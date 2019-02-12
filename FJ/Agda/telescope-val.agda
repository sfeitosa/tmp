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

-- Lifting

liftCtx : ∀ {Δ Δ₁} → (prf : Δ₁ ⊆ Δ) → List (Idx Δ₁) → List (Idx Δ)
liftExpr' : ∀ {Δ Δ₁ Γ₁} {C₁ : Idx Δ₁} → {prf : Δ₁ ⊆ Δ} → Expr Δ₁ Γ₁ C₁ → Expr Δ (liftCtx prf Γ₁) (lift prf C₁)

liftCtx p l = {!!}
--liftCtx p [] = []
--liftCtx p (i ∷ is) = lift p i ∷ liftCtx p is

liftVar : ∀ {Δ Δ₁} {prf : Δ₁ ⊆ Δ} {C₁ : Idx Δ₁} {Γ₁ : Ctx Δ₁} → C₁ ∈ Γ₁ → lift prf C₁ ∈ liftCtx prf Γ₁
liftVar zero = zero
liftVar (suc idx) = suc (liftVar idx)

liftField : ∀ {Δ Δ₁} {prf : Δ₁ ⊆ Δ} {f : Idx Δ₁} {flds : List (Idx Δ₁)} → f ∈ flds → lift prf f ∈ liftCtx prf flds
liftField zero = zero
liftField (suc idx) = suc (liftField idx)

liftMethod : ∀ {Δ Δ₁} → (prf : Δ₁ ⊆ Δ) → Method Δ₁ → Method Δ
liftMethod p (mkMethod ret params expr) = mkMethod (lift p ret) (liftCtx p params) (liftExpr' expr)

liftMethods : ∀ {Δ Δ₁} → (prf : Δ₁ ⊆ Δ) → List (Method Δ₁) → List (Method Δ)
liftMethods p [] = []
liftMethods p (m ∷ ms) = liftMethod p m ∷ liftMethods p ms

liftMethodIdx : ∀ {Δ Δ₁} {prf : Δ₁ ⊆ Δ} {m : Method Δ₁} {meths : List (Method Δ₁)}
             → m ∈ meths → liftMethod prf m ∈ liftMethods prf meths
liftMethodIdx zero = zero
liftMethodIdx (suc idx) = suc (liftMethodIdx idx)

liftParams : ∀ {Δ Δ₁} {prf : Δ₁ ⊆ Δ} {Γ₁ : Ctx Δ₁} {p : List (Idx Δ₁)}
          → All (Expr Δ₁ Γ₁) p → All (Expr Δ (liftCtx prf Γ₁)) (liftCtx prf p)
liftParams [] = []
liftParams (p ∷ ps) = liftExpr' p ∷ liftParams ps

liftExpr' (Var x) = Var (liftVar x)
liftExpr' (Field e f) = Field (liftExpr' e) (liftField f)
liftExpr' (Invk e m mp) = Invk (liftExpr' e) (liftMethodIdx m) (liftParams mp)
liftExpr' {prf = p} (New C cp) = New (lift p C) (liftParams cp)

{-
mapLiftEqId : ∀ {Δ} {Γ₁ : List (Idx Δ)} → Data.List.map (lift equal) Γ₁ ≡ Γ₁
mapLiftEqId {Γ₁ = []} = refl
mapLiftEqId {Γ₁ = x ∷ Γ₁} = cong (∷ x) mapLiftEqId

liftVar : ∀ {Δ Δ₁} {C₁ : Idx Δ₁} {Γ₁ : List (Idx Δ₁)} → (prf : Δ₁ ⊆ Δ) → C₁ ∈ Γ₁ → lift prf C₁ ∈ Data.List.map (lift prf) Γ₁
liftVar equal zero = zero
liftVar equal (suc idx) = suc (liftVar equal idx)
liftVar (more p) zero = zero
liftVar (more p) (suc idx) = suc (liftVar (more p) idx)
-}

evalL : (Δ : CT) → ∀ {Γ es} → Env Δ Γ → All (Expr Δ Γ) es → All (Value Δ) es
eval : (Δ : CT) → ∀ {Γ C} → Env Δ Γ → Expr Δ Γ C → Value Δ C

evalL Δ env [] = []
evalL Δ env (e ∷ es) = eval Δ env e ∷ evalL Δ env es

-- {-# NON_TERMINATING #-}

eval Δ env (Var x) = lookup∈ env x 
eval Δ env (Field e f) with eval Δ env e -- RC-Field
... | VNew C cp = lookupMap cp f -- R-Field
eval Δ env (Invk {m = md} e m mp) with eval Δ env e -- RC-Invk-Recv
... | VNew C cp = let mp' = (evalL Δ env mp)
                    in eval Δ mp' (liftExpr' (expr md))
eval Δ env (New C cp) = VNew C (evalL Δ env cp) 

