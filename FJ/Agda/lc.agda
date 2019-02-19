module lc where

open import Data.Bool
open import Data.List
open import Data.List.All
open import Data.List.Any
open import Relation.Binary.PropositionalEquality

-- Type and context definitions

infix 3 _⇒_
data Type : Set where
  bool : Type
  _⇒_ : Type → Type → Type
  
Ctx : Set
Ctx = List Type

-- Membership definitions

_∈_ : {A : Set} (x : A) → List A → Set
x ∈ xs = Any (λ y → x ≡ y) xs

-- Syntax and Types

data Expr (Γ : Ctx) : Type → Set where
  true  : Expr Γ bool
  false : Expr Γ bool
  Var   : ∀ {x} → x ∈ Γ → Expr Γ x
  Lam   : ∀ σ {τ} → Expr (σ ∷ Γ) τ  → Expr Γ (σ ⇒ τ)
  App   : ∀ {σ τ} → Expr Γ (σ ⇒ τ) → Expr Γ σ → Expr Γ τ
  
-- Definition of values and environments

Value : Type → Set
Value bool = Bool
Value (σ ⇒ τ) = Value (σ) → Value (τ)

Env : Ctx → Set
Env Γ = All Value Γ

-- Evaluation

eval : ∀ {Γ τ} → Env Γ → Expr Γ τ → Value τ
eval env true = true
eval env false = false
eval env (Var x) = Data.List.All.lookup env x
eval env (Lam σ e) = λ x → (eval (x ∷ env) e)
eval env (App e e₁) = eval env e (eval env e₁)

-- Examples

Γ : Ctx
Γ = bool ∷ (bool ⇒ bool) ∷ []

env : Env Γ
env = false ∷ (λ x → x) ∷ []

expr : Expr Γ bool
expr = Var (here refl)
