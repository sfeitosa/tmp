module etlc where

open import Data.Nat 
open import Data.Product
open import Data.List
open import Data.List.All
open import Data.List.Any
open import Relation.Nullary

-- Syntax

data Expr : Set where
  true  : Expr
  false : Expr
  Var   : (x : ℕ) → Expr
  Lam   : (x : ℕ) → Expr → Expr
  App   : Expr → Expr → Expr

-- Substitution

subs : Expr → ℕ → Expr → Expr
subs e' x true = true
subs e' x false = false
subs e' y (Var x) with y ≟ x
... | yes _ = e'
... | no _ = Var x
subs e' x (Lam x₁ e) = Lam x₁ (subs e' x e)
subs e' x (App e₁ e₂) = App (subs e' x e₁) (subs e' x e₂)

-- Small step relation

data Step : Expr → Expr → Set where
  R-App₁ : ∀ {e₁ e₂ e₁'}
        → Step e₁ e₁'
        → Step (App e₁ e₂) (App e₁' e₂)
  R-App₂ : ∀ {e₁ e₂ e₂'}
        → Step e₂ e₂'
        → Step (App e₁ e₂) (App e₁ e₂')
  R-App  : ∀ {x e e'}
        → Step (App (Lam x e) e') (subs e' x e)

-- Type and context definitions

infix 3 _⇒_
data Type : Set where
  bool : Type
  _⇒_ : Type → Type → Type

Ctx : Set
Ctx = List (ℕ × Type)

-- Context lookup

data _∋_∶_ : List (ℕ × Type) → (x : ℕ) → (τ : Type) → Set where
  here  : ∀ {Γ x τ}
       → ((x , τ) ∷ Γ) ∋ x ∶ τ
  there : ∀ {Γ x₁ τ₁ x₂ τ₂}
       → Γ ∋ x₁ ∶ τ₁
       → ((x₂ , τ₂) ∷ Γ) ∋ x₁ ∶ τ₁

-- Type system

data Infer : Ctx → Expr → Type → Set where
  T-Var   : ∀ {Γ x τ}
         → Γ ∋ x ∶ τ
         → Infer Γ (Var x) τ
  T-Lam   : ∀ {Γ x e τ₁ τ₂}
         → Infer ((x , τ₁) ∷ Γ) e τ₂
         → Infer Γ (Lam x e) (τ₁ ⇒ τ₂)
  T-App   : ∀ {Γ e₁ e₂ τ₁ τ₂}
         → Infer Γ e₁ (τ₁ ⇒ τ₂)
         → Infer Γ e₂ τ₁
         → Infer Γ (App e₁ e₂) τ₂
  T-True  : ∀ {Γ}
         → Infer Γ true bool
  T-False : ∀ {Γ}
         → Infer Γ false bool

-- Definition of values

data Value : Expr → Set where
  V-True  : Value true
  V-False : Value false
  V-Lam   : ∀ {x e} → Value (Lam x e)

-- Properties

-- Canonical forms

data Canonical : Expr → Type → Set where
  C-Lam   : ∀ {x τ₁ e τ₂}
         → Infer [(x , τ₁)] e τ₂
         → Canonical (Lam x e) (τ₁ ⇒ τ₂)
  C-True  : Canonical true bool
  C-False : Canonical false bool
  
canonical : ∀ {v τ} → Infer [] v τ → Value v → Canonical v τ
canonical (T-Var ()) 
canonical (T-Lam inf) V-Lam = C-Lam inf
canonical (T-App _ _) ()
canonical T-True _ = C-True
canonical T-False _ = C-False

-- Progress 

data Progress (e : Expr) : Set where
  step : ∀ {e'}
      → Step e e'
      → Progress e
  done : Value e
      → Progress e

progress : ∀ {e τ} → Infer [] e τ → Progress e 
progress (T-Var ())
progress (T-Lam _) = done V-Lam
progress (T-App e₁ e₂) with progress e₁
... | step stp₁ = step (R-App₁ stp₁)
... | done stp₁ with progress e₂
...   | step stp₂ = step (R-App₂ stp₂)
...   | done stp₂ with canonical e₁ stp₁
...     | C-Lam inf = step R-App
progress T-True = done V-True
progress T-False = done V-False

-- Substitution lemma

subst : ∀ {Γ x e v τ₁ τ₂} → Infer [] v τ₁ → Infer ((x , τ₁) ∷ Γ) e τ₂ → Infer Γ (subs v x e) τ₂
subst inf₁ (T-Var x) = {!!}
subst inf₁ (T-Lam inf₂) = T-Lam {!!}
subst inf₁ (T-App inf₂ inf₃) = T-App (subst inf₁ inf₂) (subst inf₁ inf₃)
subst _ T-True = T-True
subst _ T-False = T-False

-- Preservation

preservation : ∀ {e₁ e₂ τ} → Infer [] e₁ τ → Step e₁ e₂ → Infer [] e₂ τ
preservation (T-Var ()) 
preservation (T-Lam _) ()
preservation (T-App inf inf₁) (R-App₁ stp) = T-App (preservation inf stp) inf₁
preservation (T-App inf inf₁) (R-App₂ stp) = T-App inf (preservation inf₁ stp)
preservation (T-App (T-Lam inf) inf₁) R-App = subst inf₁ inf
preservation T-True ()
preservation T-False ()
