module CheckCase where
import Basic
import Types
import Case

instance CheckFun Fcase where
    checkFun mod@(Module (TEnv ds,Sig sig,Prog prog)) (f,Fcase (xs,ce)) =
	do Arity (ss,t) <- elookup f sig
	   ensure ((length ss)==(length xs)) (f++" wrong arity")
	   checkCe (Ctxt (zip xs ss)) t ce
	where
	checkCe :: Ctxt -> Tid -> Case  -> Error ()
	checkCe g t (CExpr e) = checkExpr mod g t e
	checkCe (Ctxt xts) t (Case x alts) =
	    do t' <- elookup x xts
               Data dalts <- elookup t' ds
	       checkAlts alts dalts
	       where checkAlts :: [((Cid,[Vid]),Case) ] -> [ (Cid,[Tid]) ] -> Error ()
		     checkAlts [] [] = return ()
		     checkAlts (((c,xs),ce):alts) ((c',ts):dalts) =
			 do ensure (c==c') ("expected "++c'++" found "++c)
			    ensure ((length xs)==(length ts)) (c++" wrong arity")
			    checkCe (Ctxt ((zip xs ts)++xts)) t ce
			    checkAlts alts dalts
		     checkAlts [] _ = fail "Incomplete pattern"
		     checkAlts _ [] = fail "Redundant cases"

-- example

mcadd = Module (natTE,addSig,pcadd)

check_add = check mcadd

mcbadd = Module (natTE,addSig,pcbadd)

check_badd = check mcbadd