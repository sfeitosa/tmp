module fjhybrid3 where

open import Data.Nat
open import Data.List
open import Data.Product
open import Data.Vec hiding (_∈_)
open import Data.Fin
open import Data.List.All
open import Data.List.Any
open import Relation.Binary.PropositionalEquality
open import Data.Vec.All

_∈_ : {A : Set} (x : A) → List A → Set
x ∈ xs = Any (λ y → x ≡ y) xs

record Ty (n : ℕ) : Set where
  inductive
  field
    class : Fin n

open Ty

record CSig (n : ℕ) : Set where
  field
    flds  : List (Ty n)
    signs : List (List (Ty n) × Ty n)

open CSig

CTSig : ℕ → Set
CTSig n = Vec (CSig n) n

Ctx : ℕ → Set
Ctx n = List (Ty n)

data Expr {n : ℕ} (cts : CTSig n) (Γ : Ctx n) : Ty n → Set where
  Var   : ∀ {x}   → x ∈ Γ → Expr cts Γ x
  Field : ∀ {c f} → Expr cts Γ c → f ∈ flds (Data.Vec.lookup (class c) cts) → Expr cts Γ f
  Invk  : ∀ {c m} → Expr cts Γ c → m ∈ signs (Data.Vec.lookup (class c) cts)
                   → Data.List.All.All (Expr cts Γ) (proj₁ m) → Expr cts Γ (proj₂ m)
  New   : ∀ c     → Data.List.All.All (Expr cts Γ) (flds (Data.Vec.lookup (class c) cts)) → Expr cts Γ c


data Val {n : ℕ} (cts : CTSig n) : Ty n → Set where
  VNew : ∀ c → Data.List.All.All (Val cts) (flds (Data.Vec.lookup (class c) cts)) → Val cts c

Env : {n : ℕ} → CTSig n → Ctx n → Set
Env cts Γ = Data.List.All.All (Val cts) Γ

CImp : {n : ℕ} → CTSig n → CSig n → Set
CImp cts sig = Data.List.All.All (λ s → Expr cts (proj₁ s) (proj₂ s)) (signs sig)

CTImp : {n : ℕ} → CTSig n → Set
CTImp cts = Data.Vec.All.All (CImp cts) cts


-- ######################## Helper Functions #########################

getMethodImp : {n : ℕ} {cts : CTSig n} {cs : CSig n} → ∀ {m}  → CImp cts cs → m ∈ signs cs → Expr cts (proj₁ m) (proj₂ m)
getMethodImp imp i = Data.List.All.lookup imp i

getClassImp : {n : ℕ} {cts : CTSig n} → CTImp cts → (c : Ty n) → CImp cts (Data.Vec.lookup (class c) cts)
getClassImp cti i = Data.Vec.All.lookup (class i) cti

-- ###################################################################

{-# NON_TERMINATING #-}

eval  : {n : ℕ} {c : Ty n} {cts : CTSig n} {Γ : Ctx n}
     → (cti : CTImp cts) → Env cts Γ → Expr cts Γ c → Val cts c
evalL : {n : ℕ} {cs : List (Ty n)} {cts : CTSig n} {Γ : Ctx n}
     → (cti : CTImp cts) → Env cts Γ → Data.List.All.All (Expr cts Γ) cs → Data.List.All.All (Val cts) cs

eval cti env (Var x) = Data.List.All.lookup env x
eval cti env (Field e f) with eval cti env e
... | VNew c vcp = Data.List.All.lookup vcp f
eval {n} {cts = cts} cti env (Invk {m = md} e m mp) with evalL cti env mp
... | vmp with eval cti env e
... | VNew c vcp = eval cti vmp (getMethodImp {n} {cts} {Data.Vec.lookup (class c) cts} {md} (getClassImp cti c) m)
eval cti env (New c cp) = VNew c (evalL cti env cp)

evalL cti env [] = []
evalL cti env (x ∷ xs) = eval cti env x ∷ evalL cti env xs

