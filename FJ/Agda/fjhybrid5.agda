module fjhybrid5 where

open import Data.Nat
open import Data.List
open import Data.Product
open import Data.Vec hiding (_∈_ ; _++_)
open import Data.Fin
open import Data.List.All
open import Data.List.Any
open import Relation.Binary.PropositionalEquality
open import Data.Vec.All
open import Data.Maybe hiding (Any)

_∈_ : {A : Set} (x : A) → List A → Set
x ∈ xs = Any (λ y → x ≡ y) xs

record Ty (n : ℕ) : Set where
  field
    class : Fin n

open Ty

record CSig (n : ℕ) : Set where
  field
    super : Ty n
    flds  : List (Ty n)
    signs : List (List (Ty n) × Ty n)

open CSig

CTSig : ℕ → Set
CTSig n = Vec (CSig n) n

Ctx : ℕ → Set
Ctx n = List (Ty n)

-- Obtaining fields from a class, assuming the inheritance relation is finite and acyclic

{-# NON_TERMINATING #-}

fields : {n : ℕ} → CTSig n → Ty n → List (Ty n)
fields cts c = fields cts (super (Data.Vec.lookup (class c) cts)) ++ flds (Data.Vec.lookup (class c) cts)

-- Obtaining methods from a class, assuming the inheritance relation is finite and acyclic

{-# NON_TERMINATING #-}

msigns : {n : ℕ} → CTSig n → CSig n → List (List (Ty n) × Ty n)
msigns cts c = msigns cts (Data.Vec.lookup (class (super c)) cts) ++ signs c

data Expr {n : ℕ} (cts : CTSig n) (Γ : Ctx n) : Maybe (Ty n) → Ty n → Set where
  This  : ∀ {C}       → Expr cts Γ (just C) C
  Var   : ∀ {x ths}   → x ∈ Γ → Expr cts Γ ths x
  Field : ∀ {c f ths} → Expr cts Γ ths c → f ∈ fields cts c → Expr cts Γ ths f  
  Invk  : ∀ {c m ths} → Expr cts Γ ths c → m ∈ msigns cts (Data.Vec.lookup (class c) cts)
                       → Data.List.All.All (Expr cts Γ ths) (proj₁ m) → Expr cts Γ ths (proj₂ m)
  New   : ∀ {ths} c   → Data.List.All.All (Expr cts Γ ths) (fields cts c) → Expr cts Γ ths c

data Val {n : ℕ} (cts : CTSig n) : Ty n → Set where
  VNew : ∀ c → Data.List.All.All (Val cts) (fields cts c) → Val cts c

Env : {n : ℕ} → CTSig n → Ctx n → Set
Env cts Γ = Data.List.All.All (Val cts) Γ

CImp : {n : ℕ} → (cts : CTSig n) → Ty n → CSig n → Set
CImp cts ths sig = Data.List.All.All (λ s → Expr cts (proj₁ s) (just ths) (proj₂ s)) (msigns cts sig)

CTImp : {n : ℕ} → CTSig n → Ty n → Set
CTImp cts ths = Data.Vec.All.All (CImp cts ths) cts

-- ######################## Helper Functions #########################

getMethodImp : {n : ℕ} {τ : Ty n} {cts : CTSig n} {cs : CSig n} → ∀ {m}
            → Val cts τ  → CImp cts τ cs → m ∈ msigns cts cs → Expr cts (proj₁ m) (just τ) (proj₂ m)
getMethodImp ths imp i = Data.List.All.lookup imp i

getClassImp : {n : ℕ} {τ : Ty n} {cts : CTSig n} → Val cts τ → CTImp cts τ → (c : Ty n) → CImp cts τ (Data.Vec.lookup (class c) cts)
getClassImp ths cti i = Data.Vec.All.lookup (class i) cti

-- ###################################################################

{-# NON_TERMINATING #-}

eval  : {n : ℕ} {c : Ty n} {τ : Ty n} {cts : CTSig n} {Γ : Ctx n}
     → Val cts τ → CTImp cts τ → Env cts Γ → Expr cts Γ (just τ) c → Val cts c
evalL : {n : ℕ} {τ : Ty n} {cs : List (Ty n)} {cts : CTSig n} {Γ : Ctx n}
     → Val cts τ → CTImp cts τ → Env cts Γ → Data.List.All.All (Expr cts Γ (just τ)) cs → Data.List.All.All (Val cts) cs

eval ths cti env This = ths
eval ths cti env (Var x) = Data.List.All.lookup env x
eval ths cti env (Field e f) with eval ths cti env e
... | VNew c vcp = Data.List.All.lookup vcp f
eval {n} {τ = τ} {cts = cts} ths cti env (Invk {m = md} e m mp) with evalL ths cti env mp
... | vmp with eval ths cti env e
... | ths@(VNew c vcp) = eval ths cti vmp (getMethodImp {n} {τ} {cts} {Data.Vec.lookup (class c) cts} ths (getClassImp ths cti c) m) 
eval ths cti env (New c cp) = VNew c (evalL ths cti env cp)

evalL ths cti env [] = []
evalL ths cti env (x ∷ xs) = eval ths cti env x ∷ evalL ths cti env xs
