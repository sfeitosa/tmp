module telescope where

open import Data.Nat
open import Data.List
open import Data.List.All

data CT  : Set
data Idx : CT → Set

Ctx : CT → Set
Ctx Δ = List (Idx Δ)

record Method (Δ : CT) : Set
record Class (Δ : CT)  : Set

data Expr (Δ : CT) (Γ : Ctx Δ) : Idx Δ → Set

record Method (Δ : CT) where
  inductive
  constructor mkMethod
  field
    ret    : Idx Δ
    params : Ctx Δ 
    expr   : Expr Δ params ret

open Method

record Class (Δ : CT) where
  inductive
  constructor mkClass
  field
    fields  : List (Idx Δ)
    methods : List (Method Δ)

open Class

infixl 5 _,_

data CT where
  ∅  : CT
  _,_ : (Δ : CT) → Class Δ → CT

data Idx where
  zero : ∀ {Δ C} → Idx (Δ , C)
  suc  : ∀ {Δ C} → Idx Δ → Idx (Δ , C)
  
infix 3 _⊆_ 
data _⊆_ : (Δ₁ : CT) → (Δ₂ : CT) → Set where
  equal : ∀ {Δ₁} → Δ₁ ⊆ Δ₁
  more  : ∀ {Δ₁ Δ₂ C} → Δ₁ ⊆ Δ₂ → Δ₁ ⊆ (Δ₂ , C)

record WkClass (Δ : CT) : Set where
  constructor wkClass
  field
    {Δ₁}  : CT
    def   : Class Δ₁
    proof : Δ₁ ⊆ Δ

infix 3 _∋_

_∋_ : (Δ : CT) → Idx Δ → WkClass Δ
(Δ₁ , C) ∋ zero = wkClass C (more equal)
(Δ₁ , C) ∋ (suc n) with (Δ₁ ∋ n)
... | wkClass C₁ p = wkClass C₁ (more p)

infix 3 _∈_
data _∈_ {A : Set} (x : A) : List A → Set where
  zero : ∀ {xs} → x ∈ x ∷ xs
  suc  : ∀ {y xs} → x ∈ xs → x ∈ y ∷ xs

lift : ∀ {Δ Δ₁} → Δ₁ ⊆ Δ → Idx Δ₁ → Idx Δ
lift equal idx = idx
lift (more p) idx = suc (lift p idx)
 
data Expr (Δ : CT) (Γ : Ctx Δ) where
  Var   : ∀ {idx}    → idx ∈ Γ → Expr Δ Γ idx
  Field : ∀ {idx f}  → Expr Δ Γ idx → f ∈ fields (WkClass.def (Δ ∋ idx)) → Expr Δ Γ (lift (WkClass.proof (Δ ∋ idx)) f)
  Invk  : ∀ {idx m}  → Expr Δ Γ idx → m ∈ methods (WkClass.def (Δ ∋ idx))
                      → All (Expr Δ Γ) (Data.List.map (lift (WkClass.proof (Δ ∋ idx))) (params m))
                      → Expr Δ Γ (lift (WkClass.proof (Δ ∋ idx)) (ret m))
  New   : (C : Idx Δ) → All (Expr Δ Γ) (Data.List.map (lift (WkClass.proof (Δ ∋ C))) (fields (WkClass.def (Δ ∋ C)))) → Expr Δ Γ C
