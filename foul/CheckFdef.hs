module CheckFdef where
import Basic
import Types
import Fdef

instance CheckFun Fdef where
    checkFun mod@(Module (TEnv ds,Sig sig,Prog prog)) (f,Fdef lines) =
	do a <- elookup f sig
	   allok (checkLine a) lines
	where
	  checkLine :: Arity -> Line -> Error ()
	  checkLine (Arity (ss,t)) (Line (ps,e)) =
	      do g <- checkPats ss ps (Ctxt [])
		 checkExpr mod g t e 
          checkPats :: [Tid] -> [Pat] -> Ctxt -> Error Ctxt
	  checkPats [] [] g = return g
	  checkPats (t:ts) (p:ps) g0 = 
	      do g1 <- checkPat t p g0
		 checkPats ts ps g1
	  checkPat :: Tid -> Pat -> Ctxt -> Error Ctxt
	  checkPat t (PVar v) (Ctxt vts) = 
	      case lookup v vts of
	        Nothing -> return (Ctxt ((v,t):vts))
		Just _ -> fail ("Pattern variable "++v++" used more than once")
	  checkPat t (PCon c ps) g =
	      do Data d <- elookup t ds
		 ts <- elookup c d
		 checkPats ts ps g



-- example

madd = Module (natTE,addSig,padd)

check_add = check madd

mbadd = Module (natTE,addSig,pbadd)

check_badd = check mbadd