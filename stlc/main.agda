open import Data.Nat using (ℕ; _+_; suc; zero)
open import Data.Vec using (Vec; lookup; _∷_; [])
open import Data.Fin using (Fin; suc; toℕ; zero)
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

-- Type Checking Context

Ctx : ℕ → Set
Ctx = Vec Type

-- Type Checked Terms

data Term {n} (Γ : Ctx n) : Type → Set where
  var : ∀ {τ} (v : Fin n) → τ ≡ lookup v Γ → Term Γ τ
  lit : ℕ → Term Γ nat
  _⊕_ : Term Γ nat → Term Γ nat → Term Γ nat
  _•_ : ∀ {σ τ} → Term Γ (σ ⇒ τ) → Term Γ σ → Term Γ τ
  lam : ∀ σ {τ} → Term (σ ∷ Γ) τ → Term Γ (σ ⇒ τ)

-- Closed Terms

Closed : Type → Set
Closed = Term []

-- Type Erasure

erase : ∀ {n} {Γ : Ctx n} {τ} → Term Γ τ → Syntax
erase (var v _) = var (toℕ v)
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

data Fromℕ (n : ℕ) : ℕ → Set where
  yes : (m : Fin n) → Fromℕ n (toℕ m)
  no : (m : ℕ) → Fromℕ n (n + m)

fromℕ : ∀ (n m : ℕ) → Fromℕ n m
fromℕ zero m = no m
fromℕ (suc n) zero = yes zero
fromℕ (suc n) (suc m) with fromℕ n m
fromℕ (suc n) (suc .(toℕ m)) | yes m = yes (suc m)
fromℕ (suc n) (suc .(n + m)) | no m = no m

-- Type Checking

data Check {n} (Γ : Ctx n) : Syntax → Set where
  yes : (τ : Type) (t : Term Γ τ) → Check Γ (erase t)
  no : {e : Syntax} → Check Γ e


check : ∀ {n} (Γ : Ctx n) (t : Syntax) → Check Γ t

check {n} Γ (var v) with fromℕ n v
check {n} Γ (var .(toℕ v)) | yes v = yes (lookup v Γ) (var v refl)
check {n} Γ (var .(n + m)) | no m = no

check Γ (lit n) = yes nat (lit n)

check Γ (t ⊕ u) with check Γ t | check Γ u
check Γ (.(erase t) ⊕ .(erase u)) | yes nat t | yes nat u = yes nat (t ⊕ u)
check Γ (_ ⊕ _) | _ | _ = no

check Γ (t • u) with check Γ t | check Γ u
check Γ (.(erase t) • .(erase u)) | yes (σ ⇒ τ) t | yes σ' u with σ ≟ σ'
check Γ (.(erase t) • .(erase u)) | yes (σ ⇒ τ) t | yes .σ u | yes refl = yes τ (t • u)
check Γ (.(erase t) • .(erase u)) | yes (σ ⇒ τ) t | yes σ' u | no _ = no
check Γ (t • u) | _ | _ = no

check Γ (lam σ t) with check (σ ∷ Γ) t
check Γ (lam σ .(erase t)) | yes τ t = yes (σ ⇒ τ) (lam σ t)
check Γ (lam σ t) | no = no

-- Evaluation

⟦_⟧ : Type → Set
⟦ nat ⟧ = ℕ
⟦ σ ⇒ τ ⟧ = ⟦ σ ⟧ → ⟦ τ ⟧

infixr 5 _∷_
data Env : ∀ {n} → Ctx n → Set where
  [] : Env []
  _∷_ : ∀ {n} {Γ : Ctx n} {τ} → ⟦ τ ⟧ → Env Γ → Env (τ ∷ Γ)

lookupEnv : ∀ {n} {Γ : Ctx n} → (m : Fin n) → Env Γ → ⟦ lookup m Γ ⟧
lookupEnv zero (x ∷ _) = x
lookupEnv (suc n) (_ ∷ env) = lookupEnv n env

_[_] : ∀ {n} {Γ : Ctx n} {τ} → Env Γ → Term Γ τ → ⟦ τ ⟧
env [ var v refl ] = lookupEnv v env
env [ lit n ] = n
env [ t ⊕ u ] = env [ t ] + env [ u ]
env [ t • u ] = (env [ t ]) (env [ u ])
env [ lam _ t ] = λ x → (x ∷ env) [ t ]
