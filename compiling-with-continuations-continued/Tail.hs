module Naive where

import qualified ML
import qualified Untyped
import Control.Monad.State (State, evalState, gets, modify)

data NaiveState = NaiveState { contCount :: Int, varCount :: Int }

initialState :: NaiveState
initialState = NaiveState
  { contCount = 0
  , varCount = 0
  }

type T = State NaiveState

contVar :: T Untyped.ContVar
contVar = do
  count <- gets contCount
  modify $ \s -> s { contCount = count + 1 }
  return $ Untyped.ContVar ("#k" ++ show count)

var :: T Untyped.Var
var = do
  count <- gets varCount
  modify $ \s -> s { varCount = count + 1 }
  return $ Untyped.Var ("#x" ++ show count)

transform :: ML.Term -> (Untyped.Var -> T Untyped.Term) -> T Untyped.Term
transform (ML.Var x) k =
  k (Untyped.Var x)

transform ML.Unit k = do
  x <- var
  kx <- k x
  return $ Untyped.LetVal x Untyped.Unit kx

transform (ML.App e1 e2) k = do
  l <- contVar
  x <- var
  transform e1 $ \z1 ->
    transform e2 $ \z2 ->
      k x >>= \kx ->
        return $ Untyped.LetCont l x kx (Untyped.App z1 l z2)

transform (ML.Pair (e1, e2)) k = do
  x <- var
  transform e1 $ \z1 ->
    transform e2 $ \z2 ->
      k x >>= \kx ->
        return $ Untyped.LetVal x (Untyped.Pair z1 z2) kx

transform (ML.In i e) k = do
  x <- var
  transform e $ \z ->
    k x >>= \kx ->
      return $ Untyped.LetVal x (Untyped.In i z) kx

transform (ML.Proj i e) k = do
  x <- var
  transform e $ \z ->
    k x >>= \kx ->
      return $ Untyped.LetProj x i z kx

transform (ML.Fun x e) k = do
  f <- var
  l <- contVar
  kf <- k f
  e' <- transform' e l
  return $ Untyped.LetVal
    f
    (Untyped.Lam (Untyped.Lambda l (Untyped.Var x) e'))
    kf

transform (ML.Let x e1 e2) k = do
  j <- contVar
  e2' <- transform e2 k
  e1' <- transform' e1 j
  return $ Untyped.LetCont j (Untyped.Var x) e2' e1'

transform (ML.Case e (x1, e1) (x2, e2)) k = do
  j <- contVar
  k1 <- contVar
  k2 <- contVar
  x <- var
  x1 <- var
  x2 <- var
  kx <- k x
  e1' <- transform' e1 j
  e2' <- transform' e2 j
  transform e $ \z ->
    return $
      Untyped.LetCont j x kx $
        Untyped.LetCont k1 x1 e1' $
          Untyped.LetCont k2 x2 e2' $
            Untyped.Case z k1 k2

transform' :: ML.Term -> Untyped.ContVar -> T Untyped.Term
transform' (ML.Var x) k =
  return $ Untyped.AppCont k (Untyped.Var x)

transform' ML.Unit k = do
  x <- var
  return $ Untyped.LetVal x Untyped.Unit (Untyped.AppCont k x)

transform' (ML.App e1 e2) k = do
  l <- contVar
  x <- var
  transform e1 $ \z1 ->
    transform e2 $ \z2 ->
        return $ Untyped.App z1 k z2

transform' (ML.Pair (e1, e2)) k = do
  x <- var
  transform e1 $ \z1 ->
    transform e2 $ \z2 ->
      return $ Untyped.LetVal x (Untyped.Pair z1 z2) (Untyped.AppCont k x)

transform' (ML.In i e) k = do
  x <- var
  transform e $ \z ->
    return $ Untyped.LetVal x (Untyped.In i z) (Untyped.AppCont k x)

transform' (ML.Proj i e) k = do
  x <- var
  transform e $ \z ->
    return $ Untyped.LetProj x i z (Untyped.AppCont k x)

transform' (ML.Fun x e) k = do
  f <- var
  j <- contVar
  e' <- transform' e j
  return $ Untyped.LetVal
    f
    (Untyped.Lam (Untyped.Lambda j (Untyped.Var x) e'))
    (Untyped.AppCont k f)

transform' (ML.Let x e1 e2) k = do
  j <- contVar
  e2' <- transform' e2 k
  e1' <- transform' e1 j
  return $ Untyped.LetCont j (Untyped.Var x) e2' e1'

transform' (ML.Case e (x1, e1) (x2, e2)) k = do
  k1 <- contVar
  k2 <- contVar
  x1 <- var
  x2 <- var
  e1' <- transform' e1 k
  e2' <- transform' e2 k
  transform e $ \z ->
    return $
        Untyped.LetCont k1 x1 e1' $
          Untyped.LetCont k2 x2 e2' $
            Untyped.Case z k1 k2

runTransform :: T Untyped.Term -> Untyped.Term
runTransform t = evalState t initialState

trans :: ML.Term -> Untyped.Term
trans t =
  let k z = return (Untyped.AppCont (Untyped.ContVar "halt") z)
   in runTransform $ transform t k

main :: IO ()
main =
  let t = ML.Fun "x" (ML.App (ML.Var "f") (ML.Pair (ML.Var "x", ML.Var "y")))
      untyped = trans t
   in print untyped >> Untyped.eval' untyped
