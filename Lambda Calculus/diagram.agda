open import etlc
open import itlc renaming (Expr to Term)

open import Data.List

module diagram where

{-
  elab : ∀ {Γ e τ} → Γ ⊢ e ∶ τ → Term Γ τ
  elab prf = ?
-}

evalVal : ∀ {v τ} → [] ⊢ v ∶ τ → Val v → Value τ
