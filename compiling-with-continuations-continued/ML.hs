module ML where

data Term
  = Var String
  | App Term Term
  | Fun String Term
  | Pair (Term, Term)
  | Proj Int Term
  | Unit
  | In Int Term
  | Let String Term Term
  | Case Term (String, Term) (String, Term)
