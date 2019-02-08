module telescope-val where

open import Data.Nat
open import Data.List
open import Data.List.All
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

-- Main definitions

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
    params : List (Idx Δ)
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

-- Auxiliary functions and definitions

infix 3 _⊆_ 
data _⊆_ : (Δ₁ : CT) → (Δ₂ : CT) → Set where
  equal : ∀ {Δ₁} → Δ₁ ⊆ Δ₁
  more  : ∀ {Δ₁ Δ₂ C} → Δ₁ ⊆ Δ₂ → Δ₁ ⊆ (Δ₂ , C)

-- Transitivity of ⊆
⊆-trans : ∀ {Δ Δ₁ Δ₂} → Δ₂ ⊆ Δ₁ → Δ₁ ⊆ Δ → Δ₂ ⊆ Δ
⊆-trans p equal = p
⊆-trans p (more p') = more (⊆-trans p p')

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

-- Inherently typed syntax

data Expr (Δ : CT) (Γ : Ctx Δ) where
  Var   : ∀ {idx}    → idx ∈ Γ → Expr Δ Γ idx
  Field : ∀ {idx f}  → Expr Δ Γ idx → f ∈ fields (WkClass.def (Δ ∋ idx)) → Expr Δ Γ (lift (WkClass.proof (Δ ∋ idx)) f)
  Invk  : ∀ {idx m}  → Expr Δ Γ idx → m ∈ methods (WkClass.def (Δ ∋ idx))
                      → All (Expr Δ Γ) (Data.List.map (lift (WkClass.proof (Δ ∋ idx))) (params m))
                      → Expr Δ Γ (lift (WkClass.proof (Δ ∋ idx)) (ret m))
  New   : (C : Idx Δ) → All (Expr Δ Γ) (Data.List.map (lift (WkClass.proof (Δ ∋ C))) (fields (WkClass.def (Δ ∋ C))))
                      → Expr Δ Γ C

-- Evaluation 

data Value (Δ : CT) : Idx Δ → Set where
  VNew : (C : Idx Δ) → All (Value Δ) (Data.List.map (lift (WkClass.proof (Δ ∋ C))) (fields (WkClass.def (Δ ∋ C)))) → Value Δ C

Env : (Δ : CT) → Ctx Δ → Set
Env Δ Γ = All (Value Δ) Γ

lookup∈ : ∀ {A} {P : A → Set} {x xs} → All P xs → x ∈ xs → P x
lookup∈ (p ∷ ps) zero = p
lookup∈ (p ∷ ps) (suc i) = lookup∈ ps i

lookupMap : ∀ {Δ Δ₁} {t : Idx Δ₁} {ts : List (Idx Δ₁)} {fun : Idx Δ₁ → Idx Δ}
   → All (Value Δ) (Data.List.map fun ts) → t ∈ ts → Value Δ (fun t)
lookupMap (x ∷ _) zero = x
lookupMap (_ ∷ xs) (suc i) = lookupMap xs i

{-
liftCtx : ∀ {Δ Δ₁} → Δ₁ ⊆ Δ → Ctx Δ₁ → Ctx Δ
liftCtx p [] = []
liftCtx p (x ∷ xs) = lift p x ∷ liftCtx p xs 

liftVar : ∀ {Δ₁} {C : Idx Δ₁} {Δ} {Γ : List (Idx Δ₁)}
            (prf' : Δ₁ ⊆ Δ) →
          C ∈ Γ → lift prf' C ∈ liftCtx prf' Γ
liftVar p zero = zero
liftVar p (suc idx) = suc (liftVar p idx)

liftExpr : ∀ {Δ Δ₁ Γ C} → {prf : Δ₁ ⊆ Δ} → Expr Δ₁ Γ C → Expr Δ (liftCtx prf Γ) (lift prf C)
liftExpr {prf = prf'} (Var x) = Var (liftVar prf' x) 
liftExpr {prf = prf'} (Field e f) = Field {!liftExpr e!} {!!}
liftExpr {prf = prf'} (Invk e m mp) = Invk {!!} {!!} {!!}
liftExpr {prf = prf'} (New C cp) = New (lift prf' C) {!!}
-}

liftExpr : ∀ {Δ} {C : Idx Δ} {md : Method (WkClass.Δ₁ (Δ ∋ C))}
           {ret' : Idx (WkClass.Δ₁ (Δ ∋ C))}
           {params' : List (Idx (WkClass.Δ₁ (Δ ∋ C)))} →
           Expr (WkClass.Δ₁ (Δ ∋ C)) params' ret' →
           Expr Δ (Data.List.map (lift (WkClass.proof (Δ ∋ C))) params')
           (lift (WkClass.proof (Δ ∋ C)) ret')
liftExpr (Var x) = {!!}
liftExpr (Field e x) = {!!}
liftExpr (Invk e x x₁) = {!!}
liftExpr (New C x) = {!!}


{-# NON_TERMINATING #-}

eval : (Δ : CT) → ∀ {Γ C} → Env Δ Γ → Expr Δ Γ C → Value Δ C
eval Δ env (Var x) = lookup∈ env x 
eval Δ env (Field e f) with eval Δ env e -- RC-Field
... | VNew C cp = lookupMap cp f -- R-Field
eval Δ env (Invk {m = md} e m mp) with eval Δ env e -- RC-Invk-Recv
... | VNew C cp with Data.List.All.map (eval Δ env) mp -- RC-Invk-Args
... | mp' with (expr md)
... | mb = eval Δ mp' (liftExpr mb) -- R-Invk
eval Δ env (New C cp) with Data.List.All.map (eval Δ env) cp -- RC-New-Arg
... | cp' = VNew C cp'

