module Basic where

open import Agda.Builtin.Bool
open import Data.List using (List; _∷_; []; map)
open import Agda.Builtin.Nat
open import Agda.Builtin.String
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)

Cid = String -- Constructor names

Vid = String -- Variable names

Fid = String -- Function names

infixl 4 _++_
_++_ : String -> String -> String
s1 ++ s2 = primStringAppend s1 s2

if_then_else_ : {A : Set} -> Bool -> A -> A -> A
if true then x else _ = x
if false then _ else y = y

lookup : {A : Set} -> String -> List (String × A) -> Maybe A
lookup _ [] = nothing
lookup x ((a , b) ∷ rest) =
  if primStringEquality x a
  then just b
  else lookup a rest

showSeq : String -> List String -> String
showSeq sep [] = ""
showSeq sep (s ∷ []) = s
showSeq sep (s ∷ ss) = s ++ sep ++ (showSeq sep ss)

data Val : Set where
  VCon : Cid -> List Val -> Val

{-instance Show Val where-}
  {-show (VCon c es) = "(" ++ (showSeq " " (c : (map show es))) ++ ")"-}

data Expr : Set where
  ECon : Cid -> List Expr -> Expr
  EVar : Vid -> Expr
  EApp : Fid -> List Expr -> Expr

{-instance Show Expr where-}
  {-show (EVar v) = v-}
  {-show (ECon c es) = "(" ++ (showSeq " " (c : (map show es))) ++ ")"-}
  {-show (EApp f es) = "(" ++ (showSeq " " (f : (map show es))) ++ ")"-}

{-class ShowFun a where-}
  {-showFun :: String -> a -> String-}

data Env : Set where
  MkEnv : List (Vid × Val) -> Env

data Prog : Set -> Set where
  MkProg : {A : Set} -> List (Fid × A) -> Prog A

{-instance Functor Prog where-}
  {-fmap f (Prog xas) = Prog (map (\(x, a) -> (x, f a)) xas)-}

{-instance (ShowFun a) => Show (Prog a) where-}
  {-show (Prog funs) = showSeq "\n" (map (\(f, fun) -> showFun f fun) funs)-}

record ApplyFun (A : Set) : Set where
  field
    apply : (Prog A) -> A -> List Val -> Val

open ApplyFun {{...}} public

{-class ApplyFun a where-}
  {-apply :: (Prog a) -> a -> [Val] -> Val-}

eval : {a : Set} {{_ : ApplyFun a}} -> (Prog a) -> Env -> Expr -> Maybe Val

eval prog env (ECon c es) =
  just (VCon c (map (eval prog env) es))

eval prog (MkEnv xvs) (EVar x) =
  lookup x xvs

eval (prog@(MkProg fds)) env (EApp f es) with lookup f fds
... | nothing = nothing
... | just fun = just (apply prog fun (map (eval prog env) es))

-- example
num : Nat -> Expr
num zero = ECon "Ze" []
num (suc n) = ECon "Su" (num n ∷ [])
