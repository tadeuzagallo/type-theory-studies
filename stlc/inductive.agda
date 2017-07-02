module Inductive where

open import Data.Nat using (ℕ; _+_; suc; zero)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (Dec; yes; no)
-- Types

infixr 30 _⇒_

data Type : Set where
  nat : Type
  _⇒_ : Type → Type → Type

-- Syntax

infixl 80 _•_
data Syntax : Set where
  var : ℕ → Syntax
  lit : ℕ → Syntax
  _⊕_ : Syntax → Syntax → Syntax
  _•_ : Syntax → Syntax → Syntax
  lam : Type → Syntax → Syntax

-- Type Checked Terms

data Ctx : Set where
  ε : Ctx
  _,_ : Ctx -> Type -> Ctx

data Var : Ctx → Type → Set where
  zero : {Γ : Ctx} {σ : Type} -> Var (Γ , σ) σ
  succ : {Γ : Ctx} {σ τ : Type} -> Var Γ σ → Var (Γ , τ) σ

data Term (Γ : Ctx) : Type → Set where
  var : {σ : Type} -> Var Γ σ -> Term Γ σ
  lit : ℕ → Term Γ nat
  _⊕_ : Term Γ nat → Term Γ nat → Term Γ nat
  _•_ : ∀ {σ τ} → Term Γ (σ ⇒ τ) → Term Γ σ → Term Γ τ
  lam : ∀ σ {τ} → Term (Γ , σ) τ → Term Γ (σ ⇒ τ)

-- Closed Terms

Closed : Type → Set
Closed = Term ε

toℕ : {Γ : Ctx} {τ : Type} -> Var Γ τ -> ℕ
toℕ zero = zero
toℕ (succ x) = suc (toℕ x)

len : Ctx -> ℕ
len ε  = zero
len (Γ , _) = suc (len Γ)

-- Type Erasure

erase : ∀ {Γ : Ctx} {τ} → Term Γ τ → Syntax
erase (var v) = var (toℕ v)
erase (lit n) = lit n
erase (x ⊕ y) = erase x ⊕ erase y
erase (x • y) = erase x • erase y
erase (lam σ τ) = lam σ (erase τ)

-- Type Equality

≡⇒₁ : ∀ {σ σ' τ τ'} → σ ⇒ τ ≡ σ' ⇒ τ' → σ ≡ σ'
≡⇒₁ refl = refl

≡⇒₂ : ∀ {σ σ' τ τ'} → σ ⇒ τ ≡ σ' ⇒ τ' → τ ≡ τ'
≡⇒₂ refl = refl


_≟_ : (τ σ : Type)  → Dec (τ ≡ σ)

nat ≟ nat = yes refl
nat ≟ _ ⇒ _ = no λ()
_ ⇒ _ ≟ nat = no λ()

σ ⇒ τ ≟ σ' ⇒ τ' with σ ≟ σ' | τ ≟ τ'
σ ⇒ τ ≟ .σ ⇒ .τ | yes refl | yes refl = yes refl
σ ⇒ τ ≟ σ' ⇒ τ' | no σ≢σ' | _ = no (σ≢σ' ∘ ≡⇒₁)
σ ⇒ τ ≟ σ' ⇒ τ' | _ | no τ≢τ' = no (τ≢τ' ∘ ≡⇒₂)

-- From ℕ to Fin

data ToVar : Ctx -> ℕ -> Set where
  yes : {Γ : Ctx} (σ : Type) -> (v : Var Γ σ) -> ToVar Γ (toℕ v)
  no : {Γ : Ctx} {v : ℕ} -> ToVar Γ v

lookup : (n : ℕ) -> (Γ : Ctx) -> ToVar Γ n
lookup _ ε = no
lookup zero (Γ , σ) = yes σ zero
lookup (suc n) (Γ , σ) = f σ (lookup n Γ)
  where
    f : {Γ : Ctx} {n : ℕ} (σ : Type) -> ToVar Γ n -> ToVar (Γ , σ) (suc n)
    f _ no = no
    f {Γ} σ (yes τ v) = yes {Γ , σ} τ (succ v)

-- Type Checking

data Check (Γ : Ctx) : Syntax → Set where
  yes : (τ : Type) (t : Term Γ τ) → Check Γ (erase t)
  no : {e : Syntax} → Check Γ e


check : ∀ (Γ : Ctx) (t : Syntax) → Check Γ t

check Γ (var v) with lookup v Γ
check Γ (var _) | no = no
check Γ (var .(toℕ v)) | yes τ v = yes τ (var v)

check Γ (lit n) = yes nat (lit n)

check Γ (t ⊕ u) with check Γ t | check Γ u
check Γ (.(erase t) ⊕ .(erase u)) | yes nat t | yes nat u = yes nat (t ⊕ u)
check Γ (_ ⊕ _) | _ | _ = no

check Γ (t • u) with check Γ t | check Γ u
check Γ (.(erase t) • .(erase u)) | yes (σ ⇒ τ) t | yes σ' u with σ ≟ σ'
check Γ (.(erase t) • .(erase u)) | yes (σ ⇒ τ) t | yes .σ u | yes refl = yes τ (t • u)
check Γ (.(erase t) • .(erase u)) | yes (σ ⇒ τ) t | yes σ' u | no _ = no
check Γ (t • u) | _ | _ = no

check Γ (lam σ t) with check (Γ , σ) t
check Γ (lam σ .(erase t)) | yes τ t = yes (σ ⇒ τ) (lam σ t)
check Γ (lam σ t) | no = no

-- Evaluation

⟦_⟧ : Type → Set
⟦ nat ⟧ = ℕ
⟦ σ ⇒ τ ⟧ = ⟦ σ ⟧ → ⟦ τ ⟧

data Env : Ctx → Set where
  ε : Env ε
  _,_ : {Γ : Ctx} {τ : Type} → Env Γ → ⟦ τ ⟧ → Env (Γ , τ)

evalVar : {Γ : Ctx} {τ : Type} -> Env Γ -> Var Γ τ -> ⟦ τ ⟧
evalVar {Γ} (Δ , x) zero = x
evalVar {Γ} (Δ , _) (succ x) = evalVar Δ x

_[_] : {Γ : Ctx} {τ : Type} → Env Γ → Term Γ τ → ⟦ τ ⟧
env [ var v ] = evalVar env v
env [ lit n ] = n
env [ t ⊕ u ] = env [ t ] + env [ u ]
env [ t • u ] = (env [ t ]) (env [ u ])
env [ lam _ t ] = λ x → (env , x) [ t ]

double : Closed (nat ⇒ nat)
double = lam nat (var zero ⊕ var zero)

double' : ⟦ nat ⇒ nat ⟧
double' = ε [ double ] -- A closed term, in an empty environment

doubleTest : double' 3 ≡ 6
doubleTest = refl

add : Closed (nat ⇒ nat ⇒ nat)
add = lam nat (lam nat (var zero ⊕ var (succ zero)))

add' : ⟦ nat ⇒ nat ⇒ nat ⟧
add' = ε [ add ] -- A closed term, in an empty environment

addTest : add' 2 3 ≡ 5
addTest = refl
