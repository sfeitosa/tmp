module fjhybrid where

open import Data.Nat
open import Data.List
open import Data.Product
open import Data.Vec hiding (_∈_)
open import Data.Fin
open import Data.List.All
open import Data.List.Any
open import Relation.Binary.PropositionalEquality

record MSign (n : ℕ) : Set where
  inductive
  constructor mkMSign
  field
    ret    : Fin n
    params : List (Fin n)

open MSign

record CSign (n : ℕ) : Set where
  inductive 
  constructor mkCSig
  field
    flds   : List (Fin n)
    msigns : List (MSign n)

open CSign

CTSig : (n : ℕ) → Set
CTSig n = Vec (CSign n) n

Ctx : (n : ℕ) → Set
Ctx n = List (Fin n)

data Expr {n : ℕ} (ct : CTSig n) (Γ : Ctx n) : Fin n → Set

record MImpl {n : ℕ} (ct : CTSig n) (s : MSign n) : Set where
  inductive
  constructor mkMImpl
  field
    expr : Expr ct (params s) (ret s)

open MImpl

record CImpl {n : ℕ} (ct : CTSig n) (c : Fin n) : Set where
  inductive
  constructor mkCImpl
  field
    methods : All (MImpl ct) (msigns (Data.Vec.lookup c ct))

open CImpl

CTImpl : (n : ℕ) → CTSig n → Set
CTImpl n ct = All (CImpl ct) {!!}

_∈_ : {A : Set} (x : A) → List A → Set
x ∈ xs = Any (λ y → x ≡ y) xs

-- Intrinsically typed syntax

-- data Expr {n : ℕ} (ct : CTSig n) (Γ : Ctx n) : Fin n → Set
data Expr {n : ℕ} (ct : CTSig n) (Γ : Ctx n) where
  Var   : ∀ {x} → x ∈ Γ → Expr ct Γ x
  Field : ∀ {idx f} → Expr ct Γ idx → f ∈ flds (Data.Vec.lookup idx ct) → Expr ct Γ f
  Invk  : ∀ {idx m} → Expr ct Γ idx → m ∈ msigns (Data.Vec.lookup idx ct) → All (Expr ct Γ) (params m) → Expr ct Γ (ret m)
  New   : ∀ idx → All (Expr ct Γ) (flds (Data.Vec.lookup idx ct)) → Expr ct Γ idx

-- Definition of Values

data Value {n : ℕ} (ct : CTSig n) : Fin n → Set where
  VNew : ∀ idx → All (Value ct) (flds (Data.Vec.lookup idx ct)) → Value ct idx

Env : {n : ℕ} (ct : CTSig n) → Ctx n → Set
Env ct Γ = All (Value ct) Γ

-- Evaluation

getMethodImpl : ∀ {n} {ct : CTSig n} {m : MSign n} →
                CTImpl n ct →
                (idx : Fin n) →
                m ∈ (msigns (Data.Vec.lookup idx ct)) →
                Expr ct (params m) (ret m)
getMethodImpl cti ci mi = {!!}

{-# NON_TERMINATING #-}

eval : ∀ {n idx} {ct : CTSig n} {Γ : Ctx n} (impl : CTImpl n ct) → Env ct Γ → Expr ct Γ idx → Value ct idx
evalL : ∀ {n is} {ct : CTSig n} {Γ : Ctx n} (impl : CTImpl n ct) → Env ct Γ → All (Expr ct Γ) is → All (Value ct) is

eval cti env (Var x) = Data.List.All.lookup env x
eval cti env (Field e f) with eval cti env e
... | VNew idx cp = Data.List.All.lookup cp f
eval cti env (Invk e m mp) with eval cti env e
... | VNew idx cp with evalL cti env mp
... | vmp = eval cti vmp (getMethodImpl cti idx m)
eval cti env (New idx cp) = VNew idx (evalL cti env cp)

evalL cti env [] = []
evalL cti env (i ∷ is) = eval cti env i ∷ evalL cti env is
