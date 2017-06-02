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
