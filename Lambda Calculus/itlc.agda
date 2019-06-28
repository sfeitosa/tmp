module itlc where

open import Data.Nat
open import Data.Bool
open import Data.Product
open import Data.List
open import Data.List.All
--open import Data.List.Any
--open import Data.List.Membership.Propositional
open import Relation.Binary.PropositionalEquality

open import common

-- Type and context definitions

{-
infix 3 _⇒
_
data Type : Set where
  bool : Type
  _⇒_ : Type → Type → Type
-}

{-
Ctx : Set
Ctx = List Ty
-}

infix 3 _∈_
data _∈_ (x : ℕ × Ty) : List (ℕ × Ty) → Set where
  here : ∀ {xs} → x ∈ x ∷ xs
  there : ∀ {y xs} → proj₁ x ≢ proj₁ y → x ∈ xs → x ∈ y ∷ xs

lookup∈ : {P : (ℕ × Ty) → Set} {x : ℕ × Ty} {xs : List (ℕ × Ty)}
       → All P xs → x ∈ xs → P x
lookup∈ (p ∷ ps) here = p
lookup∈ (p ∷ ps) (there x i) = lookup∈ ps i

-- Syntax and Types

data Expr (Γ : Ctx) : Ty → Set where
  true  : Expr Γ bool
  false : Expr Γ bool
  Var   : ∀ {x τ} → (x , τ) ∈ Γ → Expr Γ τ
  Lam   : ∀ {τ σ} (x : ℕ) → Expr ((x , σ) ∷ Γ) τ  → Expr Γ (σ ⇒ τ)
  App   : ∀ {σ τ} → Expr Γ (σ ⇒ τ) → Expr Γ σ → Expr Γ τ
  
-- Definition of values and environments

Value : Ty → Set
Value bool = Bool
Value (σ ⇒ τ) = Value (σ) → Value (τ)

data Val : Ty → Set 
Env' : Ctx → Set

data Val where
  V-Bool : Val bool
  V-Lam  : ∀ {Γ σ τ} → Expr (σ ∷ Γ) τ → Env' Γ → Val (proj₂ σ ⇒ τ)

Env' Γ = All (λ x → Val (proj₂ x)) Γ

Env : Ctx → Set
Env Γ = All (λ x → Value (proj₂ x)) Γ


{-# NON_TERMINATING #-}
eval' : ∀ {Γ τ} → Env' Γ → Expr Γ τ → Val τ --∃ (λ Δ → Val Δ τ)
eval' env true = V-Bool
eval' env false = V-Bool
eval' env (Var x) = lookup∈ env x
eval' env (Lam x e) = V-Lam e env
eval' env (App e e₁) with eval' env e
eval' env (App e e₁) | V-Lam e' env' with eval' env e₁
... | v = eval' (v ∷ env') e'
{-
eval' {Γ} env true = Γ , V-Bool
eval' {Γ} env false = Γ , V-Bool
eval' {Γ} env (Var x) = Γ , lookup∈ env x
eval' {Γ} env (Lam x e) = Γ , V-Lam e
eval' {Γ} env (App e e₁) with eval' env e
eval' {Γ} env (App e e₁) | Γ' , V-Lam e' with eval' env e₁
eval' {Γ} env (App e e₁) | Γ' , V-Lam e' | Γ'' , v
  = eval' {!!} e'
-}
{-
eval' env true = V-Bool
eval' env false = V-Bool
eval' env (Var x) = lookup∈ env x
eval' env (Lam x e) = V-Lam e
eval' env (App e e₁) with eval' env e
eval' env (App e e₁) | V-Lam e' with eval' env e₁
... | v = eval' env {!e'!}
-}

--with eval' env e₁
--... | v = eval' (v ∷ env) {!e!}

--eval' {!!} {!!}

--with eval' env e
--... | V-Lam {σ} {τ} = ?

-- Evaluation

eval : ∀ {Γ τ} → Env Γ → Expr Γ τ → Value τ
eval env true = true
eval env false = false
eval env (Var x) = lookup∈ env x
eval env (Lam σ e) = λ x → (eval (x ∷ env) e)
eval env (App e e₁) = {!!} --eval env e (eval env e₁)

-- Examples

{-
Γ : Ctx
Γ = bool ∷ (bool ⇒ bool) ∷ []

env : Env Γ
env = false ∷ (λ x → x) ∷ []

expr : Expr Γ bool
expr = Var (here refl)
-}
