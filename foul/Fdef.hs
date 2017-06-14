module Fdef where
import Basic

data Pat = PCon Cid [Pat] | 
	   PVar Vid

instance Show Pat where
    show (PVar v) = v
    show (PCon c es) = "("++(showSeq " " (c:(map show es)))++")"

newtype Line = Line ([Pat],Expr)

showLine :: Fid -> Line -> String
showLine f (Line (ps,e)) = (showSeq " " (f:(map show ps)))++" = "++(show e)

newtype Fdef = Fdef [ Line ]

instance ShowFun Fdef where 
    showFun f (Fdef lines) = showSeq "\n" (map (showLine f) lines)

instance ApplyFun Fdef where 
    apply prog (Fdef ((Line (ps,e)):fun)) vs = 
	      case matches ps vs of
	         Just env -> eval prog env e
		 Nothing -> apply prog (Fdef fun) vs

matches :: [Pat] -> [Val] -> Maybe Env 
matches [] [] = return (Env [])
matches (p:ps) (v:vs) = 
    do Env e1 <- match p v
       Env e2 <- matches ps vs
       return (Env (e1++e2))

match :: Pat -> Val -> Maybe Env
match (PVar x) v = return (Env [(x,v)])
match (PCon c ps) (VCon c' vs) 
    | c==c' = matches ps vs
    | otherwise = Nothing


--- example

add :: (Fid,Fdef)
add = ("add",Fdef [Line ([PCon "Ze" [],PVar "m"],EVar "m"),
	          Line ([PCon "Su" [PVar "n"],PVar "m"],ECon "Su" [EApp "add" [EVar "n",EVar "m"]])])

padd = Prog [add]

run_add = eval padd (Env [])

test_add m n = run_add (EApp "add" [num m,num n])

badd :: (Fid,Fdef)
badd = ("add",Fdef [Line ([PCon "Ze" [],PVar "m"],EVar "m"),
	          Line ([PCon "Su" [PVar "n"],PVar "m"],ECon "Su" [EApp "add" [EVar "m"]])])

pbadd = Prog [badd]

eq :: (Fid,Fdef)
eq = ("eq",Fdef [Line ([PCon "Ze" [],PCon "Ze" []],ECon "True" []),
		 Line ([PCon "Ze" [],PCon "Su" [PVar "n"]],ECon "False" []),
		 Line ([PCon "Su" [PVar "m"],PCon "Ze" []],ECon "False" []),
		 Line ([PCon "Su" [PVar "m"],PCon "Su" [PVar "n"]],EApp "eq" [EVar "m",EVar "n"])])

peq = Prog [eq]

run_eq = eval peq (Env [])
		 
