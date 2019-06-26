open import etlc
open import itlc renaming (Expr to Term)

module diagram where


  elab : ∀ {Γ e τ} → Γ ⊢ e ∶ τ → Term Γ τ
  elab prf = ?
