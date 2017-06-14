module Basic where

type Cid = String -- Constructor names
type Vid = String -- Variable names
type Fid = String -- Function names

showSeq sep [] = ""
showSeq sep [s] = s
showSeq sep (s:ss) = s++sep++(showSeq sep ss)

data Val = VCon Cid [Val]

instance Show Val where
    show (VCon c es) = "("++(showSeq " " (c:(map show es)))++")"

data Expr = ECon Cid [Expr] | EVar Vid | EApp Fid [Expr]

instance Show Expr where
    show (EVar v) = v
    show (ECon c es) = "("++(showSeq " " (c:(map show es)))++")"
    show (EApp f es) = "("++(showSeq " " (f:(map show es)))++")"

class ShowFun a where
    showFun :: String -> a -> String

newtype Env = Env [(Vid,Val)]

newtype Prog a = Prog [(Fid,a)]

instance Functor Prog where
    fmap f (Prog xas) = Prog (map (\ (x,a) -> (x,f a)) xas)

instance (ShowFun a) => Show (Prog a) where
    show (Prog funs) =
	showSeq "\n" (map (\ (f,fun) -> showFun f fun) funs)

class ApplyFun a where
    apply :: (Prog a) -> a -> [Val] -> Val

eval :: (ApplyFun a) => (Prog a) -> Env -> Expr -> Val
eval prog env (ECon c es) = VCon c (map (eval prog env) es)
eval prog (Env xvs) (EVar x) = v
    where Just v = lookup x xvs
eval (prog@(Prog fds)) env (EApp f es) = apply prog fun (map (eval prog env) es)
    where Just fun = lookup f fds

-- example

num :: Int -> Expr
num 0 = ECon "Ze" []
num (n+1) = ECon "Su" [num n]

