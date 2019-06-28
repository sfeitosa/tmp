module itlc where

open import Data.Nat
open import Data.Bool
open import Data.Maybe
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

-- Value : Ty → Set
-- Value bool = Bool
-- Value (σ ⇒ τ) = Value (σ) → Value (τ)

data Val : Ty → Set 
Env' : Ctx → Set

data Val where
  V-True : Val bool
  V-False : Val bool
  V-Lam  : ∀ {Γ σ τ} → Expr (σ ∷ Γ) τ → Env' Γ → Val (proj₂ σ ⇒ τ)

Env' Γ = All (λ x → Val (proj₂ x)) Γ

-- Env : Ctx → Set
-- Env Γ = All (λ x → Value (proj₂ x)) Γ


M : Ctx -> Set -> Set
M G A = Env' G -> Maybe A 

return : ∀ {Γ A} -> A -> M Γ A
return x _ = just x

_>>=_ : ∀ {Γ A B} → M Γ A -> (A → M Γ B) -> M Γ B
(f >>= c) env with f env
...| just x = c x env
...| nothing = nothing

getEnv : ∀ {Γ} -> M Γ (Env' Γ)
getEnv env = just env

usingEnv : ∀ {Γ Γ' A} → Env' Γ -> M Γ A -> M Γ' A
usingEnv env f _ = f env

timeout : ∀ {Γ A} → M Γ A
timeout _ = nothing

eval' : ∀ {Γ τ} → ℕ → Expr Γ τ → M Γ (Val τ)
eval' zero e = timeout
eval' (suc n) true = return V-True
eval' (suc n) false = return V-False
eval' (suc n) (Var x)
  = getEnv >>= λ env -> return (lookup∈ env x) 
eval' (suc n) (Lam x e)
  = getEnv >>= λ env -> return (V-Lam e env)
eval' (suc n) (App e e')
  = eval' n e >>=
       λ { (V-Lam e1 env) ->
           eval' n e' >>= λ v -> usingEnv (v ∷ env) (eval' n e1) }

-- Examples

{-
Γ : Ctx
Γ = bool ∷ (bool ⇒ bool) ∷ []

env : Env Γ
env = false ∷ (λ x → x) ∷ []

expr : Expr Γ bool
expr = Var (here refl)
-}
