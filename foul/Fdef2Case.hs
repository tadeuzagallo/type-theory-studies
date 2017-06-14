module Fdef2Case where
import Basic
import Case
import Fdef


addPat :: Vid -> Pat -> (Maybe Case) -> Case -> (Maybe Case,Case)


addPat :: Vid -> Pat -> (Maybe Case,Case) -> (Maybe Case,Case)
addPat x (PCon c ps) (Nothing,ce) = 
    let zs = genVars (length ps)
	(old,new) = addPats zs (Nothing,ce)
    in (old,Case x [(c,(zs,new))])
addPat x (PCon c ps) (Just (Case y alts),ce) = 
    | x==y = 
	case lookup c alts of
	  Nothing -> let zs = genVars (length ps)
			      (old,new) = addPats zs (Nothing,ce)
	             in (old,Case x [(c,(zs,new))]) 
	  Just (zs,ce') -> let (old,new) = addPats zs ps (Just ce',ce) 


addPats :: [Vid] -> [Pat] -> (Maybe Case,Case) -> (Maybe Case,Case)
addPats [] [] old_new = old_new
addPats (x:xs) (p:ps) old_new = addPats xs ps (addPat x p old_new)



-- fdef2case :: Fdef -> Fcase

-- addLine :: [Vid] -> [Pat] -> Expr -> (Maybe Fcase) -> (Maybe Fcase)
-- addLine [] [] e Nothing = Just (CExpr e)
-- addLine (x:xs) (p:ps) e ce = 

addPat :: Vid -> Pat -> (Maybe Case) -> Expr -> Case
addPat x (PCon c ps) Nothing e = Case x [(c,(zs,addPats zs ps Nothing e))]
addPat x (PVar y) Nothing e = CExpr (renameExpr y x e)
addPat x p@(PCon c ps) (Just (Case y alts)) e
    | x == y = Case y
	       (case lookup c alts of
	        Nothing -> let zs = genVars (length ps)
		           in alts++[(c,(zs,addPats zs ps Nothing e))]
		Just (zs,ce) -> update c (zs,addPats zs ps (Just e))))
    | otherwise = Just (Case y [(c,(xs,addPat ce)) | 

 

let addPatAlts [] = [(c,(zs,addPats zs ps Nothing))]
		   addPatAlts (


-- addPat x (PVar y) ce = 
-- addPat x (Case y alts) (PCon c ps) = 
--     Case y (addPat' alts)
--     where addPat' [] = 
       