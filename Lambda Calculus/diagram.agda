open import etlc
open import itlc renaming (Expr to Term ; Ctx to Gam ; _=>_ to )

open import Data.List
open import Data.Product hiding (map)

module diagram where


  ty2Type : Ty -> Type
  ty2Type bool = ?
  ty2Type (t ⇒ t') = ?

  --elab : ∀ {Γ : Ctx}{e τ} → Γ ⊢ e ∶ τ → Term (map proj₂ Γ) τ
  --elab prf = 
