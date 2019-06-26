open import etlc
open import itlc renaming (Expr to Term ; Ctx to Gam)
open import common

open import Data.List
open import Data.List.All hiding (map ; zip)
open import Data.List.Any renaming (here to Here ; there to There) hiding (map ; index)
open import Data.List.Membership.Propositional
open import Data.Nat
open import Data.Product hiding (map ; zip)
open import Relation.Binary.PropositionalEquality

open import Data.List

module diagram where

  elabVar : ∀ {Γ : Ctx}{x τ} → Γ ∋ x ∶ τ → τ ∈ (map proj₂ Γ)
  elabVar here = Here refl
  elabVar (there x prf) = There (elabVar prf)

  elab : ∀ {Γ : Ctx}{e τ} → Γ ⊢ e ∶ τ → Term (map proj₂ Γ) τ
  elab T-True = true
  elab T-False = false
  elab (T-Var v) = Var (elabVar v)
  elab (T-Lam {τ₁ = τ₁} prf) = Lam τ₁ (elab prf)
  elab (T-App prf prf') = App (elab prf) (elab prf')

  index : ∀ {Γ : Gam}{τ} → τ ∈ Γ → ℕ
  index (Here px) = 0
  index (There prf) = suc (index prf)

  erase : ∀ {Γ : Gam}{τ} → Term Γ τ → Expr
  erase true = true
  erase false = false
  erase (Var x) = Var (index x)
  erase (Lam σ e) = Lam 0 (erase e)
  erase (App e e') = App (erase e) (erase e')

  data _≈_ : Expr -> Expr -> Set where
    ≈-True : true ≈ true
    ≈-False : false ≈ false
    ≈-var : ∀ {x x'} → (Var x) ≈ (Var x')

  gamma : Gam → Ctx
  gamma G = zip (vals G 0) G
     where
        vals : Gam -> ℕ -> List ℕ
        vals [] _ = []
        vals (t ∷ G) n = n ∷ (vals G (n + 1))

  postulate
    elab-erase-var : ∀ {Γ x τ}(t : gamma Γ ∋ x ∶ τ) → index (elabVar t) ≡ x
  
  elab-erase : ∀ {Γ : Gam}{e τ}(t : gamma Γ ⊢ e ∶ τ) → erase (elab t) ≡ e
  elab-erase T-True = refl
  elab-erase T-False = refl
  elab-erase (T-Var x) = cong Var (elab-erase-var x)
  elab-erase (T-Lam t) = {!!}
  elab-erase (T-App t t')
    = cong₂ App (elab-erase t) (elab-erase t')
