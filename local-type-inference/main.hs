import Control.Monad (when, zipWithM)
import Control.Monad.Except (throwError)
import Data.List ((\\), intersect, union, groupBy, intercalate)
import Debug.Trace

data Type
  = TVar String
  | TTop
  | TBot
  | TFun [String] [Type] Type
  deriving (Eq, Show)

data Term
  = Var String
  | Fun [String] [(String, Type)] Term
  | App Term [Type] [Term]
  deriving (Eq, Show)

data Bind
  = BVar Type
  | BTVar
  deriving (Eq, Show)

type Context = [(String, Bind)]

-- Free Type Variables
fv :: Type -> [String]
fv TTop = []
fv TBot = []
fv (TVar x) = [x]
fv (TFun x s r) =
  (foldl union [] (map fv s) `union` fv r) \\ x

bind_vars :: Context -> [(String, Type)] -> Context
bind_vars ctx ps =
  foldl aux ctx ps
    where aux ctx (x, t) = (x, BVar t) : ctx

bind_tvars :: Context -> [String] -> Context
bind_tvars ctx ps =
  foldl aux ctx ps
    where aux ctx x = (x, BTVar) : ctx

class Subst t where
  subst' :: [(String, Type)] -> t -> t

instance Subst Type where
  subst' s (TVar y) =
    case lookup y s of
      Just t -> t
      Nothing -> TVar y

  subst' s (TFun x p r) =
    let s' = filter (\(y, _) -> y `notElem` x) s in
    let p' = map (subst' s') p in
    let r' = subst' s' r in
    TFun x p' r'

  subst' s t = t

instance (Subst t) => Subst [t] where
  subst' s ts = map (subst' s) ts

subst :: Subst t => [Type] -> [String] -> t -> t
subst t x s = subst' (zip x t) s

(<:) :: Type -> Type -> Bool

-- S-Refl
t <: u | t == u = True

-- S-Top
_ <: TTop = True

-- S-Bot
TBot <: _ = True

-- S-Fun
(TFun v1 p1 t1) <: (TFun v2 p2 t2) =
  trace (show t1  ++ " <: " ++ show t2) $
  v1 == v2 && all (uncurry (<:)) (zip p2 p1) && t1 <: t2

_ <: _ = False

-- Least Upper Bound
(\/) :: Type -> Type -> Type

s \/ t | s <: t = t
s \/ t | t <: s = s
(TFun x v p) \/ (TFun x' w q) | x == x' =
  TFun x (zipWith (/\) v w) (p \/ q)
_ \/ _ = TTop

-- Greatest Lower Bound
(/\) :: Type -> Type -> Type
s /\ t | s <: t = s
s /\ t | t <: s = t
(TFun x v p) /\ (TFun x' w q) | x == x' =
  TFun x (zipWith (\/) v w) (p /\ q)
_ /\ _ = TBot

-- Infer
type Result = Either String
infer :: Context -> Term -> Result Type

-- Var
infer ctx (Var x) =
  case lookup x ctx of
    Just (BVar t) -> return t
    _ -> throwError ("Unknown variable: " ++ x)

-- Abs
infer ctx (Fun v p t) = do
  let ctx' = bind_tvars ctx v
  let ctx'' = bind_vars ctx' p
  t' <- infer ctx'' t
  return $ TFun v (map snd p) t'

infer ctx (App f t e) = do
  f' <- infer ctx f
  case (t, f') of
    -- App-InfAlg
    ([], TFun x@(_:_) t r) -> do
      s <- mapM (infer ctx) e
      d <- zipWithM (constraintGen [] x) t s
      let c = foldl meet [] d
      trace (show c) (return ())
      s <- mapM (getSubst r) c
      return $ subst' s r

    -- App
    (_, TFun x s r) -> do
      let s' = subst t x s
      e' <- mapM (infer ctx) e
      when (not $ all (uncurry (<:)) (zip e' s')) (throwError "Type Error")
      return (subst t x r)

    -- App-Bot
    (_, TBot) ->
      mapM_ (infer ctx) e >> return TBot

    _ -> throwError "Type Error"

-- Variable Elimination

-- S ⇑V T
elimU :: [String] -> Type -> Type

-- VU-Top
elimU _ TTop = TTop

-- VU-Bot
elimU _ TBot = TBot

elimU v (TVar x)
  -- VU-Var-1
  | x `elem` v = TTop
  -- VU-Var-2
  | otherwise = (TVar x)

-- VU-Fun
elimU v (TFun x s t) =
  let u = map (elimD v) u in
  let r = elimU v t in
  TFun x u r

-- S ⇓V T
elimD :: [String] -> Type -> Type
-- VD-Top
elimD _ TTop = TTop

-- VD-Bot
elimD _ TBot = TBot

elimD v (TVar x)
  -- VD-Var-1
  | x `elem` v = TBot
  -- VD-Var-2
  | otherwise = TVar x

-- VD-Fun
elimD v (TFun x s t) =
  let u = map (elimU v) s in
  let r = elimD v t in
  TFun x u r

-- Constraint Generation
data Constraint
  = Constraint Type String Type
  deriving (Eq, Show)

constraintGen :: [String] -> [String] -> Type -> Type -> Result [Constraint]

-- CG-Top
constraintGen _ _ _ TTop = return []

-- CG-Bot
constraintGen _ _ TBot _ = return []

-- CG-Upper
constraintGen v x (TVar y) s | y `elem` x && fv s `intersect` x == [] =
  let t = elimD v s in
  return [Constraint TBot y t]

-- CG-Lower
constraintGen v x s (TVar y) | y `elem` x && fv s `intersect` x == [] =
  let t = elimU v s in
    return [Constraint t y TTop]

-- CG-Refl
constraintGen v x (TVar y) (TVar y') | y == y' && y `notElem` x =
  return []

-- CG-Fun
constraintGen v x (TFun y r s) (TFun y' t u)
  | y == y' && y `intersect` (v `union` x) == [] = do
    c <- zipWithM (constraintGen (v `union` y) x) t r
    d <- constraintGen (v `union` y) x s u
    return $ foldl meet [] c `meet` d

constraintGen v x s t =
   throwError $ "constraintGen: failed to generate constraints for {" ++ intercalate ", " v ++ "} ⊢_{" ++ intercalate ", " x ++ "} " ++ show s ++ " <: " ++ show t

-- The meet of two X/V-constraints C and D, written C /\ D, is defined as follows:
meet :: [Constraint] -> [Constraint] -> [Constraint]
meet c [] = c
meet [] d = d
meet c d =
  map merge cs
    where
      cs = groupBy prj (c `union` d)
      prj (Constraint _ t _) (Constraint _ u _) = t == u
      merge (c:cs) = foldl mergeC c cs
      mergeC (Constraint s x t) (Constraint u _ v) =
        Constraint (s \/ u) x (t /\ v)

-- Calculating Type Arguments

--- Calculate Variance
data Variance
  = Constant
  | Covariant
  | Contravariant
  | Invariant
  deriving (Eq, Show)

variance :: String -> Type -> Variance
variance _ TTop = Constant
variance _ TBot = Constant
variance v (TVar x)
  | v == x = Covariant
  | otherwise = Constant
variance v (TFun x t r)
  | v `elem` x = Constant
  | otherwise =
    let t' = map (invertVariance . variance v) t in
    (foldl joinVariance Constant t') `joinVariance` variance v r

invertVariance :: Variance -> Variance
invertVariance Covariant = Contravariant
invertVariance Contravariant = Covariant
invertVariance c = c

joinVariance :: Variance -> Variance -> Variance
joinVariance Constant d = d
joinVariance c Constant = c
joinVariance c d | c == d = c
joinVariance _ _ = Invariant

-- Create Substitution
type Substitution = (String, Type)

getSubst :: Type -> Constraint -> Result Substitution
getSubst r (Constraint s x t) =
  let m = (variance x r) in
  trace (show m ++ " " ++ show x ++ " " ++ show r) $
  case m of
    Constant -> return (x, s)
    Covariant -> return (x, s)
    Contravariant -> return (x, t)
    Invariant | s == t -> return (x, s)
    _ -> throwError "Cannot infer type argument"

-- Examples
id = Fun ["X"] [("x", TVar "X")] (Var "x")
id2 = Fun ["Y"] [("x", TVar "Y")] (Var "x")
const = Fun ["X", "Y"] [("x", TVar "X"), ("y", TVar "Y")] (Var "x")
app = App Main.id [] [Main.id2]

main = do
  print (infer [] Main.id)
  print (infer [] Main.id2)
  print (infer [] Main.const)
  print (infer [] Main.app)
