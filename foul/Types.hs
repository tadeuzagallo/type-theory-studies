module Types where
import Basic
import Control.Monad

data Error a = Ok a | Error String
	       deriving Show

instance Functor Error where
  fmap f (Ok a) = Ok (f a)
  fmap f (Error str) = Error str

instance Applicative Error where
  pure = return
  (<*>) = ap

instance Monad Error where
    return a = Ok a

    (Ok a) >>= f = f a
    (Error msg) >>= f = Error msg
    fail msg = Error msg

type Tid = String -- Type identifier

newtype Data = Data [ (Cid,[Tid]) ]

instance Show Data where
    show (Data alts) =
	showSeq "|" (map (\ (c,ts) -> showSeq " " (c:ts)) alts)

newtype TEnv = TEnv [ (Tid,Data) ]

instance Show TEnv where
    show (TEnv ds) =
        showSeq "\n" (map (\ (t,d) -> "data "++t++" = "++(show d)) ds)

newtype Ctxt = Ctxt [(Vid,Tid)]

newtype Arity = Arity ([Tid],Tid)

instance Show Arity where
    show (Arity (ss,t)) =
	showSeq "->" (ss++[t])

newtype Sig = Sig [(Fid,Arity)]
    
instance Show Sig where
    show (Sig fas) =
	showSeq "\n" (map (\ (f,a) -> f++" :: "++(show a)) fas)

newtype Module a = Module (TEnv,Sig,Prog a)

instance ShowFun a => Show (Module a) where
    show (Module (ds,sig,prog)) =
	  (show ds)++"\n"++(show sig)++"\n"++(show prog)

allok :: ( a -> Error () ) -> [a] -> Error ()
allok p [] = return ()
allok p (a:as) = 
    do () <- p a
       allok p as
       
ensure :: Bool -> String -> Error ()
ensure True _ = return ()
ensure False msg = fail msg

elookup :: (Eq a,Show a) => a -> [(a,b)] -> Error b
elookup a abs =
    case lookup a abs of
      Just b -> Ok b
      Nothing -> Error ((show a)++" undefined")

class CheckFun a where
    checkFun :: (Module a) -> (Fid,a) -> Error ()

check :: (CheckFun a) => (Module a) -> Error () 
check mod@(Module (TEnv ds,Sig sig,Prog prog)) = 
    allok (checkFun mod) prog

checkExpr :: (Module a) -> Ctxt -> Tid -> Expr -> Error () 
checkExpr mod@(Module (TEnv ds,Sig sig,Prog prog)) g t (ECon c es) =
    do Data d <- elookup t ds
       ts <- elookup c d
       checkExprs mod g ts es
checkExpr mod@(Module (TEnv ds,Sig sig,Prog prog)) g t e =
    do t' <- inferExpr mod g e
       ensure (t==t') ("Expected: "++t++" found: "++t')

inferExpr :: (Module a) -> Ctxt -> Expr -> Error Tid 
inferExpr mod@(Module (TEnv ds,Sig sig,Prog prog)) (Ctxt vts) (EVar v) =
    elookup v vts
inferExpr mod@(Module (TEnv ds,Sig sig,Prog prog)) g (EApp f es) =
    do Arity (ss,t) <- elookup f sig
       checkExprs mod g ss es
       return t
inferExpr mod@(Module (TEnv ds,Sig sig,Prog prog)) g _ =
    Error "Cannot infer"

checkExprs :: (Module a) -> Ctxt -> [Tid] -> [Expr] -> Error ()
checkExprs mod g [] [] = return ()
checkExprs mod g (t:ts) (e:es) = 
    do checkExpr mod g t e
       checkExprs mod g ts es
checkExprs mod g _ _ = fail "Arity doesn't match"

-- example

nat :: (Tid,Data)
nat = ("Nat",Data [("Ze",[]),("Su",["Nat"])])

addSig :: Sig
addSig = Sig [("add",Arity (["Nat","Nat"],"Nat"))]

natTE = TEnv [nat]
