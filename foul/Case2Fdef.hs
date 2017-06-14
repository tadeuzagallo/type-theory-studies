module Case2Fdef where
import Basic
import Case
import Fdef

case2fdef :: Fcase -> Fdef
case2fdef (Fcase (xs,ce)) = Fdef (splitLines (map PVar xs) ce)

splitLines :: [Pat] -> Case -> [Line]
splitLines ps (CExpr e) = [Line (ps,e)]
splitLines ps (Case x alts) = 
    do (c,(xs,ce)) <- alts
       fmap (\ (Line (ps,e)) -> Line (ps,exprSubst x (ECon c (map EVar xs)) e))
	    (splitLines (map (patSubst x (PCon c (map PVar xs))) ps) ce)
 
patSubst :: Vid -> Pat -> Pat -> Pat
patSubst x q p@(PVar y)
	     | x==y = q
	     | otherwise = p
patSubst x q (PCon c ps) = PCon c (map (patSubst x q) ps)

exprSubst :: Vid -> Expr -> Expr -> Expr
exprSubst x f e@(EVar y)
	     | x==y = f
	     | otherwise = e
exprSubst x f (ECon c es) = ECon c (map (exprSubst x f) es)
exprSubst x f (EApp g es) = EApp g (map (exprSubst x f) es)


case2fdefp :: Prog Fcase -> Prog Fdef
case2fdefp = fmap case2fdef   

-- example

padd' = case2fdefp pcadd
