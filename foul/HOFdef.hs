module HOFdef where
import HOBasic

data Pat = PCon Cid [Pat] | 
	   PVar Vid

instance Show Pat where
    show (PVar v) = v
    show (PCon c es) = "("++(showSeq " " (c:(map show es)))++")"

newtype Line = Line ([Pat],Expr)
    deriving Show


--showLine :: Fid -> Line -> String
--showLine f (Line (ps,e)) = (showSeq " " (f:(map show ps)))++" = "++(show e)

newtype Fdef = Fdef [ Line ]
	    deriving Show
-- instance ShowFun Fdef where 
--     showFun f (Fdef lines) = showSeq "\n" (map (showLine f) lines)

instance ApplyFun Fdef where 
    apply env (f @ (Fdef ((Line (ps,e)):fun))) vs = 
	if (length vs) < (length ps) 
	then VApp (HFun f) vs
	else case matches ps vs of
		       Just env' -> eval (appendEnv env' env) e
		       Nothing -> apply env (Fdef fun) vs


matches :: [Pat] -> [Val a] -> Maybe (Env a)
matches [] [] = return (Env [])
matches (p:ps) (v:vs) = 
    do Env e1 <- match p v
       Env e2 <- matches ps vs
       return (Env (e1++e2))
matches _ _ = Nothing

match :: Pat -> (Val a) -> Maybe (Env a)
match (PVar x) v = return (Env [(x,v)])
match (PCon c ps) (VApp (HCon c') vs) 
    | c==c' = matches ps vs
    | otherwise = Nothing


--- example

mkFun' :: Fdef -> Val Fdef
mkFun' f = VApp (HFun f) []

add' = Fdef [Line ([PCon "Ze" [],PVar "m"],EVar "m"),
 	     Line ([PCon "Su" [PVar "n"],PVar "m"],
		   (EApp (ECon "Su") (EApp (EApp (EVar "add") (EVar "n")) (EVar "m"))))]

add :: (Vid,Val Fdef )
add = ("add",mkFun' add')
run_add = eval (Env [add])

test_add m n = run_add (EApp (EApp (EVar "add") (num m)) (num n))

-- badd :: (Fid,Fdef)
-- badd = ("add",Fdef [Line ([PCon "Ze" [],PVar "m"],EVar "m"),
-- 	          Line ([PCon "Su" [PVar "n"],PVar "m"],ECon "Su" [EApp "add" [EVar "m"]])])

-- pbadd = Prog [badd]

-- eq :: (Fid,Fdef)
-- eq = ("eq",Fdef [Line ([PCon "Ze" [],PCon "Ze" []],ECon "True" []),
-- 		 Line ([PCon "Ze" [],PCon "Su" [PVar "n"]],ECon "False" []),
-- 		 Line ([PCon "Su" [PVar "m"],PCon "Ze" []],ECon "False" []),
-- 		 Line ([PCon "Su" [PVar "m"],PCon "Su" [PVar "n"]],EApp "eq" [EVar "m",EVar "n"])])

-- peq = Prog [eq]

-- run_eq = eval peq (Env [])
		 
