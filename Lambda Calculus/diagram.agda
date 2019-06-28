open import etlc
open import itlc renaming (Expr to Term)
open import common

open import Data.List
open import Data.List.All hiding (map ; zip)
open import Data.Nat
open import Data.Product hiding (map ; zip)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open import Data.List
open import Data.Bool using (true ; false)
open import Function

module diagram where

  -----------------------------------
  -- Elaborating ETLC to ITLC Expr --
  -----------------------------------

  elab-var : ∀ {Γ x τ} → Γ ∋ x ∶ τ → (x , τ) ∈ Γ
  elab-var here = here 
  elab-var (there x p) = there x (elab-var p)

  elab : ∀ {Γ e τ} → Γ ⊢ e ∶ τ → Term Γ τ
  elab T-True = true
  elab T-False = false
  elab (T-Var x) = Var (elab-var x)
  elab (T-Lam {x = x} p) = Lam x (elab p)
  elab (T-App p p₁) = App (elab p) (elab p₁)

  postulate
    ∋-First : ∀ {Γ x τ₁ τ₂} → ((x , τ₁) ∷ Γ) ∋ x ∶ τ₂ → τ₁ ≡ τ₂

  -----------------------------------
  -- Elaborating ITLC to ETLC Expr --
  -----------------------------------

  erase-var : ∀ {Γ x τ} → (x , τ) ∈ Γ → Γ ∋ x ∶ τ
  erase-var here = here
  erase-var (there x i) = there x (erase-var i)

  erase : ∀ {Γ τ} → Term Γ τ → ∃ (λ e → Γ ⊢ e ∶ τ)
  erase true = true , T-True
  erase false = false , T-False
  erase (Var {x = x} v) = Var x , T-Var (erase-var v)
  erase (Lam x p) with erase p
  ...| e , p' = Lam x e , T-Lam p'
  erase (App p p₁) with erase p | erase p₁
  ...| e , p1 | e' , p1' = App e e' , T-App p1 p1'

  ------------------------------
  -- Proving equivalence Expr --
  ------------------------------

  erase-elab-var : ∀ {Γ x τ} → (t : (x , τ) ∈ Γ) → elab-var (erase-var t) ≡ t
  erase-elab-var here = refl
  erase-elab-var (there p i) = cong (there p) (erase-elab-var i)

  erase-elab : ∀ {Γ τ}(t : Term Γ τ) → elab (proj₂ (erase t)) ≡ t
  erase-elab true = refl
  erase-elab false = refl
  erase-elab (Var x) = cong Var (erase-elab-var x)
  erase-elab (Lam x t) with erase-elab t
  ...| p = cong (Lam x) p
  erase-elab (App t t₁) with erase-elab t | erase-elab t₁
  ...| p | p' = cong₂ App p p'

  ------------------------------------
  -- Elaborating ETLC to ITLC Value --
  ------------------------------------

  elabVal : ∀ {Γ v τ} → Γ ⊢ v ∶ τ → Val v → Value τ
  elabVal T-True v = true
  elabVal T-False v = false
  elabVal (T-Lam t) v = λ x → {!!}

  ------------------------------------
  -- Elaborating ITLC to ETLC Value --
  ------------------------------------

  eraseVal : ∀ {τ v} → Value τ → Val v
  eraseVal {bool} v = {!V-False!}
  eraseVal {τ ⇒ τ₁} v = {!!}

