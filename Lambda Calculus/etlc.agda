module etlc where

open import Data.Nat
open import Data.List using (List; _∷_; [_]; [])
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import common

-- Syntax

data Expr : Set where
  true  : Expr
  false : Expr
  Var   : ℕ → Expr
  Lam   : ℕ → Expr → Expr
  App   : Expr → Expr → Expr

-- Substitution

subs : Expr → ℕ → Expr → Expr
subs true y v = true
subs false y v = false
subs (Var x) y v with x ≟ y
... | yes refl = v
... | no _ = Var x
subs (Lam x e) y v with x ≟ y
... | yes refl = Lam x e
... | no _ = Lam x (subs e y v)
subs (App e₁ e₂) y v = App (subs e₁ y v) (subs e₂ y v)

-- Values

data Val : Expr → Set where
  V-True  : Val true
  V-False : Val false
  V-Lam   : ∀ {x e} → Val (Lam x e)

-- Small step relation

infix 4 _⟶_
data _⟶_ : Expr → Expr → Set where
  R-App₁ : ∀ {e₁ e₂ e₁'}
        → e₁ ⟶ e₁'
        → App e₁ e₂ ⟶ App e₁' e₂
  R-App₂ : ∀ {v₁ e₂ e₂'}
        → Val v₁
        → e₂ ⟶ e₂'
        → App v₁ e₂ ⟶ App v₁ e₂'
  R-App  : ∀ {x e v₁}
        → Val v₁
        → App (Lam x e) v₁ ⟶ (subs e x v₁)

-- Type and context definition

{-
infix 7 _⇒_
data Ty : Set where
  bool : Ty
  _⇒_ : Ty → Ty → Ty
-}

-- Contex_ t lookup

data _∋_∶_ : List (ℕ × Ty) → ℕ → Ty → Set where
  here  : ∀ {Γ x τ} → ((x , τ) ∷ Γ) ∋ x ∶ τ
  there : ∀ {Γ x y τ₁ τ₂} → x ≢ y → Γ ∋ x ∶ τ₁ → ((y , τ₂) ∷ Γ) ∋ x ∶ τ₁

-- Type system

infix 4 _⊢_∶_
data _⊢_∶_ : Ctx → Expr → Ty → Set where
  T-True  : ∀ {Γ}
         → Γ ⊢ true ∶ bool
  T-False : ∀ {Γ}
         → Γ ⊢ false ∶ bool
  T-Var   : ∀ {Γ x τ}
         → Γ ∋ x ∶ τ
         → Γ ⊢ (Var x) ∶ τ
  T-Lam   : ∀ {Γ x e τ₁ τ₂}
         → ((x , τ₁) ∷ Γ) ⊢ e ∶ τ₂
         → Γ ⊢ (Lam x e) ∶ (τ₁ ⇒ τ₂)
  T-App   : ∀ {Γ e₁ e₂ τ₁ τ₂}
         → Γ ⊢ e₁ ∶ (τ₁ ⇒ τ₂)
         → Γ ⊢ e₂ ∶ τ₁
         → Γ ⊢ (App e₁ e₂) ∶ τ₂

-- Properties

-- Canonical forms

data Canonical : Expr → Ty → Set where
  C-Lam   : ∀ {x τ₁ e τ₂}
         → [(x , τ₁)] ⊢ e ∶ τ₂
         → Canonical (Lam x e) (τ₁ ⇒ τ₂)
  C-True  : Canonical true bool
  C-False : Canonical false bool

canonical : ∀ {v τ} → [] ⊢ v ∶ τ → Val v → Canonical v τ
canonical T-True _ = C-True
canonical T-False _ = C-False
canonical (T-Var ())
canonical (T-Lam r) V-Lam = C-Lam r
canonical (T-App _ _) ()

-- Progress

data Progress (e : Expr) : Set where
  Step : ∀ {e'}
      → e ⟶ e'
      → Progress e
  Done : Val e
      → Progress e

progress : ∀ {e τ} → [] ⊢ e ∶ τ → Progress e
progress T-True = Done V-True
progress T-False = Done V-False
progress (T-Var ())
progress (T-Lam _) = Done V-Lam
progress (T-App e₁ e₂) with progress e₁
... | Step stp₁ = Step (R-App₁ stp₁)
... | Done v₁ with progress e₂
...   | Step stp₂ = Step (R-App₂ v₁ stp₂)
...   | Done v₂ with canonical e₁ v₁
...     | C-Lam stp = Step (R-App v₂)

-- Prelude to Preservation

ext : ∀ {Γ₁ Γ₂}
   → (∀ {x τ₁} → Γ₁ ∋ x ∶ τ₁ → Γ₂ ∋ x ∶ τ₁)
   → (∀ {x y τ₁ τ₂} → ((y , τ₂) ∷ Γ₁) ∋ x ∶ τ₁ → ((y , τ₂) ∷ Γ₂) ∋ x ∶ τ₁)
ext p₁ here = here
ext p₁ (there x₁ p₂) = there x₁ (p₁ p₂)

rename : ∀ {Γ₁ Γ₂}
      → (∀ {x τ₁} → Γ₁ ∋ x ∶ τ₁ → Γ₂ ∋ x ∶ τ₁)
      → (∀ {e τ} → Γ₁ ⊢ e ∶ τ → Γ₂ ⊢ e ∶ τ)
rename p₁ T-True = T-True
rename p₁ T-False = T-False
rename p₁ (T-Var x) = T-Var (p₁ x)
rename p₁ (T-Lam t) = T-Lam (rename (ext p₁) t)
rename p₁ (T-App f a) = T-App (rename p₁ f) (rename p₁ a)

weaken : ∀ {Γ e τ} → [] ⊢ e ∶ τ → Γ ⊢ e ∶ τ
weaken e = rename (λ ()) e

drop : ∀ {Γ x e τ₁ τ₂ τ₃} → (x , τ₂) ∷ (x , τ₁) ∷ Γ ⊢ e ∶ τ₃ → (x , τ₂) ∷ Γ ⊢ e ∶ τ₃
drop {Γ} {x} {e} {τ₁} {τ₂} {τ₃} e₁ = rename drop-shadow e₁
  where
    drop-shadow : ∀ {e' τ'} → ((x , τ₂) ∷ (x , τ₁) ∷ Γ) ∋ e' ∶ τ' → ((x , τ₂) ∷ Γ) ∋ e' ∶ τ'
    drop-shadow here = here
    drop-shadow (there p here) = ⊥-elim (p refl)
    drop-shadow (there p (there _ i)) = there p i

swap : ∀ {Γ x y e τ₁ τ₂ τ₃} → x ≢ y → (x , τ₁) ∷ (y , τ₂) ∷ Γ ⊢ e ∶ τ₃ → (y , τ₂) ∷ (x , τ₁) ∷ Γ ⊢ e ∶ τ₃
swap {Γ} {x} {y} {e} {τ₁} {τ₂} {τ₃} p e₁ = rename swap-ctx e₁
  where
    swap-ctx : ∀ {e' τ'} → ((x , τ₁) ∷ (y , τ₂) ∷ Γ) ∋ e' ∶ τ' → ((y , τ₂) ∷ (x , τ₁) ∷ Γ) ∋ e' ∶ τ'
    swap-ctx here = there p here
    swap-ctx (there p here) = here
    swap-ctx (there p (there p₁ i)) = there p₁ (there p i)

-- Substitution lemma

subst : ∀ {Γ x e v τ₁ τ₂} → [] ⊢ v ∶ τ₁
                          → (x , τ₁) ∷ Γ ⊢ e ∶ τ₂
                          → Γ ⊢ (subs e x v) ∶ τ₂
subst v T-True = T-True
subst v T-False = T-False
subst {x = y} v (T-Var {x = x} here) with x ≟ y
... | yes refl = weaken v
... | no p = ⊥-elim (p refl)
subst {x = y} v (T-Var {x = x} (there p e)) with x ≟ y
... | yes refl = ⊥-elim (p refl)
... | no _ = T-Var e
subst {x = y} v (T-Lam {x = x} e) with x ≟ y
... | yes refl = T-Lam (drop e)
... | no p = T-Lam (subst v (swap p e))
subst v (T-App e₁ e₂) = T-App (subst v e₁) (subst v e₂)

-- Preservation

preservation : ∀ {e e' τ} → [] ⊢ e ∶ τ → e ⟶ e' → [] ⊢ e' ∶ τ
preservation T-True ()
preservation T-False ()
preservation (T-Var ()) 
preservation (T-Lam _) ()
preservation (T-App r₁ r₂) (R-App₁ s) = T-App (preservation r₁ s) r₂
preservation (T-App r₁ r₂) (R-App₂ v₁ s) = T-App r₁ (preservation r₂ s)
preservation (T-App (T-Lam r₁) r₂) (R-App v₁) = subst r₂ r₁

