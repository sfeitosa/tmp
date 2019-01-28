module telescope where

open import Data.Nat
open import Data.List
open import Data.List.All
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

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
  New   : (C : Idx Δ) → All (Expr Δ Γ) (Data.List.map (lift (WkClass.proof (Δ ∋ C))) (fields (WkClass.def (Δ ∋ C))))
                      → Expr Δ Γ C

-- Evaluation

Value : (Δ : CT) → (Γ : Ctx Δ) → Idx Δ → Set
Value Δ Γ idx = Expr Δ Γ idx

Env : (Δ : CT) → Ctx Δ → Set
Env Δ Γ = All (Value Δ Γ) Γ

lookup∈ : ∀ {A} {P : A → Set} {x xs} → All P xs → x ∈ xs → P x
lookup∈ (p ∷ ps) zero = p
lookup∈ (p ∷ ps) (suc i) = lookup∈ ps i

lookupDB : ∀ {A x} → (xs : List A) → x ∈ xs → A
lookupDB (x ∷ xs) zero = x
lookupDB (x ∷ xs) (suc i) = lookupDB xs i

-- Same as above
lkp : ∀ {Δ Γ t ts} → All (Expr Δ Γ) ts → t ∈ ts → Expr Δ Γ t
lkp (x ∷ xs) zero = x
lkp (x ∷ xs) (suc i) = lkp xs i 

{-# NON_TERMINATING #-}

eval : (Δ : CT) → ∀ {Γ C} → Env Δ Γ → Expr Δ Γ C → Value Δ Γ C
eval Δ env (Var idx) = lookup∈ env idx
eval Δ env (Field {f = k} e f) with eval Δ env e
... | (New C cp) with fields (WkClass.def (Δ ∋ C))
... | flds with Data.List.map (lift (WkClass.proof (Δ ∋ C))) flds
... | flds' with lift (WkClass.proof (Δ ∋ C)) k
... | k' = {!!}
eval Δ env (Invk {m = md} e m mp) with eval Δ env e
... | (New C cp)  with methods (WkClass.def (Δ ∋ C))
... | ms with Data.List.All.map (eval Δ env) mp
... | mp' with expr md
... | mb = eval Δ env {!!}
eval Δ env (New C cp) = let cp' = Data.List.All.map (eval Δ env) cp
                          in New C cp'
