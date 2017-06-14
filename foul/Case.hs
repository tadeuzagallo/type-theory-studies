module Case where
import Basic

data Case = CExpr Expr
	  | Case Vid [(Cid,([Vid],Case))]

instance Show Case where
    show (CExpr e) = "("++(show e)++")"
    show (Case x alts) = 
	"case "++x++" of "++(showSeq "|" (map ( \ (c,(vs,ce)) ->  "("++(showSeq " " (c:vs))++") -> "++(show ce)) alts))

newtype Fcase = Fcase ([Vid],Case)

instance ShowFun Fcase where 
    showFun f (Fcase (xs,ce)) = (showSeq " " (f:xs))++" = "++(show ce)

instance ApplyFun Fcase where
    apply prog (Fcase (xs,ce)) vs =
        evalCase prog (Env (zip xs vs)) ce

evalCase :: (Prog Fcase) -> Env -> Case -> Val
evalCase prog env (CExpr e) = eval prog env e
evalCase prog env@(Env xvs) (Case x alts) = 
    evalCase prog (Env ((zip xs vs)++xvs)) ce
    where Just (VCon c vs) = lookup x xvs
	  Just (xs,ce) = lookup c alts

-- examples

cadd :: (Fid,Fcase)
cadd = ("add",Fcase (["n","m"],
		    Case "n" [("Ze",([],CExpr (EVar "m"))),
			      ("Su",(["n"],CExpr (ECon "Su" [EApp "add" [EVar "n",EVar "m"]])))]))

pcadd = Prog [cadd]

run_cadd = eval pcadd (Env [])

test_cadd m n = run_cadd (EApp "add" [num m,num n])


cbadd :: (Fid,Fcase)
cbadd = ("add",Fcase (["n","m"],
		     Case "n" [("Ze",([],CExpr (EVar "m")))]))

pcbadd = Prog [cbadd]

run_cbadd = eval pcbadd (Env [])

test_cbadd m n = run_cbadd (EApp "add" [num m,num n])


