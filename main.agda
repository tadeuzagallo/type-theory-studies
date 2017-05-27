open import Agda.Builtin.Int
open import Agda.Builtin.Nat hiding(_+_; _-_)
open import Agda.Builtin.String
open import Agda.Builtin.Unit

open import Data.Product
open import Data.Sum
open import Data.Maybe
open import Data.Fin
open import Data.List

open import Function
open import Category.Monad
open import Category.Monad.Identity

_>>=_ : {A : Set} -> {B : Set} -> A ⊎ B -> (B -> A ⊎ B) -> A ⊎ B
_>>=_ m f = [ inj₁ , f ]′ m

_!!!_ : ∀ {a} {A : Set a} → (l : List A) → Fin (length l) → A
[] !!! ()
(x ∷ xs) !!! n with n
... | zero = x
... | suc m = xs !!! m


data ITerm : Set
data CTerm : Set
data Name : Set
data Value : Set
data Neutral : Set

data ITerm where
  Star : ITerm
  Bound : Int -> ITerm
  Ann : CTerm -> CTerm -> ITerm
  Pi : CTerm -> CTerm -> ITerm
  Free : Name -> ITerm
  _:$:_ : ITerm -> CTerm -> ITerm
  
data CTerm where
  Inf : ITerm -> CTerm
  Lam : CTerm -> CTerm

data Name where
  Global : String -> Name
  Local : Int -> Name
  Quote : Int -> Name
  
data Value where
  VLam : (Value -> Value) -> Value
  VNeutral : Neutral -> Value
  VStar : Value
  VPi : Value -> (Value -> Value) -> Value

data Neutral where
  NFree : Name -> Neutral
  NApp : Neutral -> Value -> Neutral

Result : Set -> Set

Type = Value
Context = List (Name × Value)
Result a = String ⊎ a

vfree : Name -> Value
iEval : ITerm → List Value → Value
vapp : Value → Value → Value
cEval : CTerm → List Value → Value
iType : (ctx : Context) → Fin (length ctx) → ITerm → Result Type
iType0 : Context → ITerm → Result Type
cType : Int -> Context -> CTerm -> Type -> Result ⊤
iSubst : Int → ITerm → ITerm → ITerm
cSubst : Int → ITerm → CTerm → CTerm
quote0 : Value → CTerm
quoteN : Int → Value → CTerm
neutralQuote : Int → Neutral → ITerm
boundFree : Int → Name → ITerm

vfree n = VNeutral (NFree n)

iEval (Ann e _) d = cEval e d
iEval (Free x) d = vfree x
iEval (Bound i) d = d !!! i
iEval (e :$: e') d = vapp (iEval e d) (cEval e' d)
iEval Star d = VStar
iEval (Pi t t') d = VPi (cEval t d) (\x -> cEval t' (x ∷ d))

vapp (VLam f) v = f v
vapp (VNeutral n) v = VNeutral (NApp n v)

cEval (Inf i) d = iEval i d
cEval (Lam e) d = VLam (\x → cEval e (x ∷ d))

return : {A : Set} → {B : Set} → (b : B) → A ⊎ B
return t = inj₂ t

throwError : {B : Set} → (a : String) → String ⊎ B
throwError str = inj₁ str

unless : {A : Set} → {B : Set} → A ⊎ B → (a : A) -> A ⊎ B
unless (inj₁ _) a = inj₁ a
unless b _ = b

lookup : {A : Set} -> {B : Set} -> (a : A) -> List (A × B) -> Maybe B
lookup a ((a' , b) :: rest) with a == a'
... | true = just b
... | false = lookup a rest
lookup a [] = nothing

iType0 = iType 0

iType i g (Ann e t) =
  cType i g t VStar
  let t' = cEval t [] in
  cType i g e t'
  return t'

iType i g Star = return VStar

iType i g (Pi t t') =
  cType i g t VStar
  let p = cEval t [] in
  cType (Data.Fin._+_ i 1) ((Local i , p) ∷ g) (cSubst 0 (Free (Local i)) t') VStar
  return VStar

iType i g (Free x) =
  maybe return (inj₂ "unknown identifier") (lookup x g)

iType i g (e :$: e') =
  iType i g e >>= λ s → f s
  where
    f : Value -> Result Type
    f (VPi t t') =
          cType i g e' t
          return (t' (cEval e' []))
    f _ = throwError "illegal application"

cType i g (Inf e) t =
  iType i g e >>= λ t' →
    unless (quote0 t == quote0 t') (throwError "type mismatch")

cType i g (Lam e) (VPi t t')
  = cType (Data.Fin._+_ i 1) ((Local i , t) ∷ g) (cSubst 0 (Free (Local i)) e) (t' (vfree (Local i)))

cType i g _ _
  = throwError "type mismatch"

iSubst i r (Ann e t) = Ann (cSubst i r e) (cSubst i r t)
iSubst i r (Bound j) with i == j
... | true = r
... | false = Bound j
iSubst i r (Free y) = Free y
iSubst i r (e :$: e') = iSubst i r e :$: cSubst i r e'
iSubst i r Star = Star
iSubst i r (Pi t t') = Pi (cSubst i r t) (cSubst (Data.Fin._+_ i 1) r t')

cSubst i r (Inf e) = Inf (iSubst i r e)
cSubst i r (Lam e) = Lam (cSubst (Data.Fin._+_ i 1) r e)

quote0 = quoteN 0

quoteN i (VLam f) = Lam (quoteN (Data.Fin._+_ i 1) (f (vfree (Quote i))))
quoteN i (VNeutral n) = Inf (neutralQuote i n)
quoteN i VStar = Inf Star
quoteN i (VPi v f) = Inf (Pi (quoteN i v) (quoteN (Data.Fin._+_ i 1) (f . vfree $ Quote i)))

neutralQuote i (NFree x) = boundFree i x
neutralQuote i (NApp n v) = neutralQuote i n :$: quote i v

boundFree i (Quote k) = Bound (i - k - 1)
boundFree i x = Free x
