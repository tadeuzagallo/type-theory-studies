open import Relation.Binary.PropositionalEquality using (_≡_)

data Con : Set
data Ty : Con → Set

data Con where
  • : Con
  _,_ : (Γ : Con) → Ty Γ → Con

data Ty where
  U : ∀ {Γ} → Ty Γ
  Π : ∀ {Γ} (A : Ty Γ) (B : Ty (Γ , A)) → Ty Γ

module RecConTy where
  record Motives : Set₁ where
    field
      ConM : Set
      TyM : ConM → Set

  record Methods (M : Motives) : Set₁ where
    open Motives M
    field
      •M : ConM
      _,CM_ : (ΓM : ConM) → TyM ΓM → ConM
      UM : {ΓM : ConM} → TyM ΓM
      ΠM : {ΓM : ConM} (AM : TyM ΓM) (BM : TyM (ΓM ,CM AM)) → TyM ΓM

  module rec (M : Motives) (m : Methods M) where
    open Motives M
    open Methods m
    RecCon : Con → ConM
    RecTy : {Γ : Con} (A : Ty Γ) → TyM (RecCon Γ)
    RecCon • = •M
    RecCon (Γ , A) = RecCon Γ ,CM RecTy A
    RecTy U = UM
    RecTy (Π A B) = ΠM (RecTy A) (RecTy B)

module ElimConTy where
  record Motives : Set1 where
    field
      ConM : Con → Set
      TyM : {Γ : Con} → ConM Γ → Ty Γ → Set

  record Methods (M : Motives) : Set1 where
    open Motives M
    field
      •M : ConM •
      _,CM_ : {Γ : Con} (ΓM : ConM Γ) {A : Ty Γ} (AM : TyM ΓM A) → ConM (Γ , A)
      UM : {Γ : Con} {ΓM : ConM Γ} → TyM ΓM U
      ΠM : {Γ : Con} {ΓM : ConM Γ}
           {A : Ty Γ} (AM : TyM ΓM A)
           {B : Ty (Γ , A)} (BM : TyM (ΓM ,CM AM) B) → TyM ΓM (Π A B)

  module elim (M : Motives) (m : Methods M) where
    open Motives M
    open Methods m
    ElimCon : (Γ : Con) → ConM Γ
    ElimTy : {Γ : Con} (A : Ty Γ) → TyM (ElimCon Γ) A
    ElimCon • = •M
    ElimCon (Γ , A) = ElimCon Γ ,CM ElimTy A
    ElimTy U = UM
    ElimTy (Π A B) = ΠM (ElimTy A) (ElimTy B)

data _/_ (A : Set) (R : A → A → Set) : Set where
  [_] : A → A / R

postulate
  [_]≡ : ∀ {A} {R : A → A → Set} {a b : A}
       → R a b → [ a ] ≡ [ b ]

postulate
  _≡[_]≡_ : {A : Set} {B : Set} (a : A) → A ≡ B → (b : B) → a ≡ b

module Elim_/_
  (A : Set) (R : A → A → Set)
  (QM : A / R → Set)
  ([_]M : (a : A) → QM [ a ])
  ([_]≡M : {a b : A} (r : R a b)
  → [ a ]M ≡[ ap QM [ r ]≡ ]≡ [ b ]M)
  where
    Elim : (x : A / R) → QM x
    Elim [ x ] = [ x ]M
