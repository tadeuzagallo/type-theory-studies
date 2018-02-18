module Untyped where

import System.IO.Unsafe (unsafePerformIO)
import Debug.Trace (trace)

newtype Var = Var String
  deriving Eq

instance Show Var where
  show (Var x) = x

newtype ContVar = ContVar String
  deriving Eq

instance Show ContVar where
  show (ContVar k) = k

data Term
  = LetVal Var Value Term
  | LetCont ContVar Var Term Term
  | LetProj Var Int Var Term
  | AppCont ContVar Var
  | App Var ContVar Var
  | Case Var ContVar ContVar

instance Show Term where
  show (LetVal x v t) =
    "letval " ++ show x ++ " = " ++ show v ++ " in " ++ show t
  show (LetCont k x t u) =
    "letcont " ++ show k ++ " " ++ show x ++ " = " ++ show t ++ " in " ++ show u
  show (LetProj x i y t) =
    "let " ++ show x ++ " = π" ++ show i ++ " " ++ show y ++ " in " ++ show t
  show (AppCont k x) =
    show k ++ " " ++ show x
  show (App f k x) =
    show f ++ " " ++ show k ++ " " ++ show x
  show (Case x k1 k2) =
    "case " ++ show x ++ " of " ++ show k1 ++ " ▯ " ++ show k2

data Lambda = Lambda ContVar Var Term

instance Show Lambda where
  show (Lambda k x t) =
    "λ " ++ show k ++ " " ++ show x ++ ". " ++ show t

data Value
  = Unit
  | Pair Var Var
  | In Int Var
  | Lam Lambda

instance Show Value where
  show Unit = "()"
  show (Pair x y) = "(" ++ show x ++ ", " ++ show y ++ ")"
  show (In i x) = "in" ++ show i ++ " " ++ show x
  show (Lam f) = show f

data RtValue
  = RVUnit
  | RVPair RtValue RtValue
  | RVIn Int RtValue
  | RVClo (Env, Lambda)
  deriving (Show)

data ContValue
  = Cont (Env, (Var, Term))
  | Halt
  deriving (Show)

data Env
  = Empty
  | ValueBind Var RtValue Env
  | ContBind ContVar ContValue Env
  deriving (Show)

lookupVal :: Env -> Var -> RtValue
lookupVal Empty x =
  trace (show x) undefined
lookupVal (ContBind _ _ tail) x = lookupVal tail x
lookupVal (ValueBind y v tail) x
  | x == y = v
  | otherwise = lookupVal tail x

lookupCont :: Env -> ContVar -> ContValue
lookupCont Empty x =
  trace (show x) undefined
lookupCont (ValueBind _ _ tail) k = lookupCont tail k
lookupCont (ContBind k v tail) l
  | k == l = v
  | otherwise = lookupCont tail k

addVal :: Env -> (Var, RtValue) -> Env
addVal env (x, v) = ValueBind x v env

addCont :: Env -> (ContVar, ContValue) -> Env
addCont env (k, v) = ContBind k v env

evalValue :: Env -> Value -> RtValue
evalValue _ Unit =
  RVUnit

evalValue env (Pair x y) =
  RVPair (lookupVal env x) (lookupVal env y)

evalValue env (In i x) =
  RVIn i (lookupVal env x)

evalValue env (Lam f) =
  RVClo (env, f)

eval :: Env -> Term -> ()
eval env (LetVal x v k) =
  let v' = evalValue env v
      env' = addVal env (x, v')
   in eval env' k

eval env (LetCont k x t l) =
  let cont = Cont (env, (x, t))
      env' = addCont env (k, cont)
   in eval env' l

eval env (LetProj x i y k) =
  let RVPair r1 r2 = lookupVal env y
      ri = case i of { 1 -> r1; 2 -> r2 }
      env' = addVal env (x, ri)
   in eval env' k

eval env (Case x k1 k2) =
  let RVIn i r = lookupVal env x
      ki = case i of { 1 -> k1; 2 -> k2 }
      Cont (env', (y, t)) = lookupCont env ki
      env'' = addVal env' (y, r)
   in eval env'' t

eval env (App f k x) =
  let RVClo (env', Lambda j y t) = lookupVal env f
      env'' = addCont env' (j, lookupCont env k)
      env''' = addVal env'' (y, lookupVal env x)
   in eval env''' t

eval env (AppCont k x) =
  let cont = lookupCont env k
   in case cont of
        Halt ->
          unsafePerformIO (print $ lookupVal env x)
        Cont (env', (y, t)) ->
          let env'' = addVal env' (y, lookupVal env x)
           in eval env'' t

eval' :: Monad m => Term -> m ()
eval' t =
  let halt = ContVar "halt"
      env = ContBind halt Halt Empty
   in case eval env t of () -> return ()

main :: IO ()
main =
  let f = Var "f"
      g = Var "g"
      x = Var "x"
      y = Var "y"

      k = ContVar "k"
      l = ContVar "l"

      halt = ContVar "halt"

      t = LetVal x Unit (AppCont halt x)
      t' = (LetVal f (Lam (Lambda k x (AppCont k x)))
           (LetVal x Unit
           (LetVal y (Pair x x)
           (App f halt y))))
  in eval' t'
