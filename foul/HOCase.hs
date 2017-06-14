module HOCase where
import HOBasic

data Case = CExpr Expr
	  | Case Vid [(Cid,([Vid],Case)) ]
	  deriving Show

-- instance Show Case Where
--     Show (Cexpr E) = "("++(Show E)++")"
--     Show (Case X Alts) = 
-- 	"Case "++X++" Of "++(Showseq "|" (Map ( \ (C,(Vs,Ce)) ->  "("++(Showseq " " (C:Vs))++") -> "++(Show Ce)) Alts))

newtype Fcase = Fcase ([Vid],Case)
    deriving Show

-- instance ShowFun Fcase where 
--     showFun f (Fcase (xs,ce)) = (showSeq " " (f:xs))++" = "++(show ce)

instance ApplyFun Fcase where
    apply env (f @ (Fcase (xs,ce))) vs =
	if (length vs) < (length xs)
	then VApp (HFun f) vs
        else evalCase (appendEnv (Env (zip xs vs)) env) ce

evalCase :: (Env Fcase) -> Case -> (Val Fcase)
evalCase env (CExpr e) = eval env e
evalCase env@(Env xvs) (Case x alts) = 
    evalCase (Env ((zip xs vs)++xvs)) ce
    where Just (VApp (HCon c) vs) = lookup x xvs
	  Just (xs,ce) = lookup c alts

-- examples

cadd :: (Vid,Val Fcase)
cadd = ("add",mkFun (Fcase (["n","m"],
			    Case "n" [("Ze",([],CExpr (EVar "m"))),
				      ("Su",(["n"],CExpr (EApp (ECon "Su") (EApp (EApp (EVar "add") (EVar "n")) (EVar "m")))))])))

run_cadd = eval (Env [cadd])

test_cadd m n = run_cadd (EApp (EApp (EVar "add") (num m)) (num n))



-- cbadd :: (Fid,Fcase)
-- cbadd = ("add",Fcase (["n","m"],
-- 		     Case "n" [("Ze",([],CExpr (EVar "m")))]))

-- pcbadd = Prog [cbadd]

-- run_cbadd = eval pcbadd (Env [])

-- test_cbadd m n = run_cbadd (EApp "add" [num m,num n])


