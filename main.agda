open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import Agda.Builtin.String
open import Agda.Builtin.Unit

open import Data.Bool
open import Data.List
open import Data.Maybe
open import Data.Product
open import Data.Sum

open import Function
open import Category.Monad
open import Category.Monad.Identity

-- Helpers
Result : Set → Set
Result a = String ⊎ a

return : {A : Set} → {B : Set} → (b : B) → A ⊎ B
return t = inj₂ t

throwError : {B : Set} → (a : String) → String ⊎ B
throwError str = inj₁ str

unless : {A : Set} → Bool -> A ⊎ ⊤ → A ⊎ ⊤
unless true _ = return tt
unless false err = err

lookup : {A : Set} → {B : Set} → (A → A → Bool) → (a : A) → List (A × B) → Maybe B
lookup f a ((a' , b) ∷ rest) with f a a'
... | true = just b
... | false = lookup f a rest
lookup _ _ [] = nothing

_>>=_ : {A : Set} → {B : Set} → {C : Set} → A ⊎ B → (B → A ⊎ C) → A ⊎ C
_>>=_ m f = [ inj₁ , f ]′ m

_>>_ : {A : Set} → {B : Set} → {C : Set} → A ⊎ B → A ⊎ C → A ⊎ C
_>>_ m v = m >>= λ _ -> v

_!!!_ : ∀ {A : Set} → (l : List A) → Nat → Result A
[] !!! _ = throwError "unbound variable"
(x ∷ xs) !!! n with n
... | zero = return x
... | suc m = xs !!! m


data ITerm : Set
data CTerm : Set
data Name : Set
data Value : Set
data Neutral : Set

data ITerm where
  Star : ITerm
  Bound : Nat → ITerm
  Ann : CTerm → CTerm → ITerm
  Pi : CTerm → CTerm → ITerm
  Free : Name → ITerm
  _:$:_ : ITerm → CTerm → ITerm

data CTerm where
  Inf : ITerm → CTerm
  Lam : CTerm → CTerm

data Name where
  Global : String → Name
  Local : Nat → Name
  Quote : Nat → Name

data Value where
  VLam : (Value → Result Value) → Value
  VNeutral : Neutral → Value
  VStar : Value
  VPi : Value → (Value → Result Value) → Value

data Neutral where
  NFree : Name → Neutral
  NApp : Neutral → Value → Neutral

Type = Value
Context = List (Name × Value)

vfree : Name → Value
iEval : ITerm → List Value → Result Value
vapp : Value → Value → Result Value
cEval : CTerm → List Value → Result Value
iType : Nat → Context → ITerm → Result Type
iType0 : Context → ITerm → Result Type
cType : Nat → Context → CTerm → Type → Result ⊤
iSubst : Nat → ITerm → ITerm → ITerm
cSubst : Nat → ITerm → CTerm → CTerm
quote0 : Value → Result CTerm
quoteN : Nat → Value → Result CTerm
neutralQuote : Nat → Neutral → Result ITerm
boundFree : Nat → Name → ITerm
eqName : Name → Name → Bool
eqCTerm : CTerm → CTerm → Bool
eqITerm : ITerm → ITerm → Bool

eqName (Global n) (Global n') = primStringEquality n n'
eqName (Local i) (Local i') = i == i'
eqName (Quote i) (Quote i') = i == i'
eqName _ _ = false

eqITerm Star Star = true
eqITerm (Bound i) (Bound i') = i == i'
eqITerm (Ann v t) (Ann v' t') = (eqCTerm v v') ∧ (eqCTerm t t')
eqITerm (Pi v t) (Pi v' t') = (eqCTerm v v') ∧ (eqCTerm t t')
eqITerm (Free n) (Free n') = eqName n n'
eqITerm (v1 :$: v2) (v1' :$: v2') = (eqITerm v1 v1') ∧ (eqCTerm v2 v2')
eqITerm _ _ = false

eqCTerm (Inf i) (Inf i') = eqITerm i i'
eqCTerm (Lam l) (Lam l') = eqCTerm l l'
eqCTerm _ _ = false

vfree n = VNeutral (NFree n)

iEval (Ann e _) d = cEval e d
iEval (Free x) d = return (vfree x)
iEval (Bound i) d = d !!! i
iEval (e :$: e') d =
  iEval e d >>= λ v →
  cEval e' d >>= λ v' →
  vapp v v'
iEval Star d = return VStar
iEval (Pi t t') d =
  cEval t d >>= λ v →
  return (VPi v (\x → cEval t' (x ∷ d)))

vapp (VLam f) v = f v
vapp (VNeutral n) v = return (VNeutral (NApp n v))
vapp VStar _ = throwError "invalid application"
vapp (VPi _ _) _ = throwError "invalid application"

cEval (Inf i) d = iEval i d
cEval (Lam e) d = return (VLam (\x → cEval e (x ∷ d)))

iType0 = iType 0

iType i g (Ann e t) =
  (cType i g t VStar) >>
  ((cEval t []) >>= λ t' →
  (cType i g e t') >>
  (return t'))

iType i g Star = return VStar

iType i g (Pi t t') =
  cType i g t VStar >>
  (cEval t [] >>= λ p →
  cType (i + 1) ((Local i , p) ∷ g) (cSubst 0 (Free (Local i)) t') VStar >>
  return VStar)

iType i g (Free x) =
  maybe return (throwError "unknown identifier") (lookup eqName x g)

iType i g (e :$: e') =
  iType i g e >>= λ s → f s
  where
    f : Value → Result Type
    f (VPi t t') =
      cType i g e' t >>
      (cEval e' [] >>= λ v → t' v)
    f _ = throwError "illegal application"

iType _ _ (Bound _) = throwError "invalid type"

cType i g (Inf e) t =
  iType i g e >>= λ t' →
  quote0 t >>= λ t →
  quote0 t' >>= λ t' →
  unless (eqCTerm t t') (throwError "type mismatch")

cType i g (Lam e) (VPi t t') =
  t' (vfree (Local i)) >>= λ v →
  cType (i + 1) ((Local i , t) ∷ g) (cSubst 0 (Free (Local i)) e) v

cType i g _ _
  = throwError "type mismatch"

iSubst i r (Ann e t) = Ann (cSubst i r e) (cSubst i r t)
iSubst i r (Bound j) with i == j
... | true = r
... | false = Bound j
iSubst i r (Free y) = Free y
iSubst i r (e :$: e') = iSubst i r e :$: cSubst i r e'
iSubst i r Star = Star
iSubst i r (Pi t t') = Pi (cSubst i r t) (cSubst (i + 1) r t')

cSubst i r (Inf e) = Inf (iSubst i r e)
cSubst i r (Lam e) = Lam (cSubst (i + 1) r e)

quote0 = quoteN 0

quoteN i (VLam f) =
  f (vfree (Quote i)) >>= λ v →
  quoteN (i + 1) v >>= λ v' →
  return (Lam v')

quoteN i (VNeutral n) =
  neutralQuote i n >>= λ n' →
  return (Inf n')

quoteN i VStar = return (Inf Star)

quoteN i (VPi v f) =
  quoteN i v >>= λ v' →
  f (vfree (Quote i)) >>= λ i' →
  quoteN (i + 1) i' >>= λ f' →
  return (Inf (Pi v' f'))

neutralQuote i (NFree x) = return (boundFree i x)

neutralQuote i (NApp n v) =
  neutralQuote i n >>= λ n' →
  quoteN i v >>= λ v' →
  return (n' :$: v')

boundFree i (Quote k) = Bound (i - k - 1)
boundFree i x = Free x
