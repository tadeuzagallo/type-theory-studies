module HOBasic where

type Cid = String -- Constructor names
type Vid = String -- Variable names

showSeq sep [] = ""
showSeq sep [s] = s
showSeq sep (s:ss) = s++sep++(showSeq sep ss)

data Head a = HCon Cid | HFun a
	      deriving Show

data Val a = VApp (Head a) [Val a]
	     deriving Show

data Expr = ECon Cid | EVar Vid | EApp Expr Expr 
	 deriving Show

--class ShowFun a where
--    showFun :: String -> a -> String

newtype Env a = Env [(Vid,Val a)]

appendEnv :: (Env a) -> (Env a) -> (Env a)
appendEnv (Env es) (Env es') = Env (es ++ es')


-- instance (ShowFun a) => Show (Prog a) where
--     show (Prog funs) =
-- 	showSeq "\n" (map (\ (f,fun) -> showFun f fun) funs)

class ApplyFun a where
    apply :: (Env a) -> a -> [Val a] -> (Val a)

eval :: (ApplyFun a) => (Env a) -> Expr -> (Val a)
eval env (ECon c) = VApp (HCon c) []
eval (Env xvs) (EVar x) = v
    where Just v = lookup x xvs
eval env (EApp e1 e2) = 
    let v = eval env e2
	(VApp h vs) = eval env e1
	vs' = v:vs
    in case h of
         HCon _ -> VApp h vs'
	 HFun f -> apply env f vs'

-- example

mkFun :: a -> Val a
mkFun f = VApp (HFun f) []

num :: Int -> Expr
num 0 = ECon "Ze" 
num (n+1) = EApp (ECon "Su") (num n)

