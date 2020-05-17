module TeBPF where

open import Data.List
--open import Data.List.All
open import Data.Fin hiding (_-_)
open import Data.Product
open import Data.List.Membership.Propositional
open import Relation.Binary.PropositionalEquality

-- temporary
open import Data.Nat
open import Data.Bool

-- Fixed set of registers Register = {r0, ..., r10, data_start, data_end}
--data Reg : Set where
--  r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 data-start data-end : Reg

-- sz is either one, two, four, or eight bytes
data sz : Set where
  one two four eight : sz

-- 𝓡 contains the numerical tag (num), invalid tag (inv),
-- private region identifiers (ctx, stk, pkt), and shared
-- region identifiers from the unbounded set Shared.
data 𝓡 : Set where
  num inv ctx stk pkt : 𝓡
  shared : 𝓡

-- Values are either numbers and pointers. Pointers are offsets from the
-- beggining of the region they point to.
TV = (𝓡 × ℕ)

-- a ∈ Address = {0, ..., 511}
Address = Fin 512

-- An environment e maps register names to their contents.
-- e ∈ Env = Register → (𝓡 × ℤ)
Env = List TV
--Env = List (Reg × TV)

-- A memory cell is a subsegment of the stack region identified by their
-- start address a and their size sz
-- c ∈ Cell - Address × Size
Cell = List (Address × sz)

-- A memory μ maps memory cells to their contents
-- μ ∈ Mem = Cell → (R × ℤ)
MemTy = List 𝓡
Mem = List (Cell × TV)

-- ζ is a set of addresses in the stack that hold a number or part of it,
-- but not a pointer, or parts of which
-- ζ ∈ Format = 2^Address -- @TODO: o que isso significa?
Format = List (Address)


-- Machine state: σ = (e, μ, ζ)
record State : Set where
  constructor
    state
  field
    env     : Env
    memty   : MemTy
    format  : Format

open State

infix 1 _∣_∣_
pattern _∣_∣_ e m f = state e m f

data Expr (sig : State) : Set where
  Number   : ℕ → Expr sig
  Register : ∀ {τ} → τ ∈ (env sig) → Expr sig
  PlusL    : ∀ {τ n} → (num , n) ∈ (env sig) → τ ∈ (env sig) → Expr sig
  PlusR    : ∀ {τ n} → τ ∈ (env sig) → (num , n) ∈ (env sig) → Expr sig
  MinusR   : ∀ {τ n} → τ ∈ (env sig) → (num , n) ∈ (env sig) → Expr sig
  Minus    : ∀ {τ n₁ n₂} → (τ , n₁) ∈ (env sig) → (τ , n₂) ∈ (env sig) → Expr sig

data Condition (sig : State) : Set where
  Eq   : ∀ {τ n₁ n₂} → (τ , n₁) ∈ (env sig) → (τ , n₂) ∈ (env sig) → Condition sig
  EqL  : ∀ {τ} → (num , 0) ∈ (env sig) → τ ∈ (env sig) → Condition sig
  EqR  : ∀ {τ} → τ ∈ (env sig) → (num , 0) ∈ (env sig) → Condition sig
  Neq  : ∀ {τ n₁ n₂} → (τ , n₁) ∈ (env sig) → (τ , n₂) ∈ (env sig) → Condition sig
  NeqL : ∀ {τ} → (num , 0) ∈ (env sig) → τ ∈ (env sig) → Condition sig
  NeqR : ∀ {τ} → τ ∈ (env sig) → (num , 0) ∈ (env sig) → Condition sig
  Leq  : ∀ {τ n₁ n₂} → (τ , n₁) ∈ (env sig) → (τ , n₂) ∈ (env sig) → Condition sig

postulate
  bounds : 𝓡 → sz → ℕ

data Command (sig : State) : Set where
  Assign   : ∀ {τ} → τ ∈ (env sig) → Expr sig → Command sig
  LoadPkt  : ∀ {τ n} → (τ , n) ∈ (env sig) → (s : sz) → Fin (bounds τ s) → Command sig
  Load     : ∀ {τ n} → (τ , n) ∈ (env sig) → (s : sz) → Fin (bounds τ s) → Command sig
  StorePkt : ∀ {τ n s} → Fin (bounds τ s) → (s : sz) → (τ , n) ∈ (env sig) → Command sig
  Store    : ∀ {τ n s} → Fin (bounds τ s) → (s : sz) → (τ , n) ∈ (env sig) → Command sig
  Assume   : Condition sig → Command sig
  Shared   : ∀ {τ} → τ ∈ (env sig) → ℕ → Command sig


-- ReadRegs(cmd) denotes the set of registers whose values are read in cmd.
{-
ReadRegsExp : Expr → List Reg
ReadRegsExp (Number n) = []
ReadRegsExp (Register r) = r ∷ []
ReadRegsExp (Plus r₁ r₂) = r₁ ∷ r₂ ∷ [] 
ReadRegsExp (Minus r₁ r₂) = r₁ ∷ r₂ ∷ []

ReadRegsCond : Condition → List Reg
ReadRegsCond (Eq r₁ r₂) = r₁ ∷ r₂ ∷ [] 
ReadRegsCond (Neq r₁ r₂) = r₁ ∷ r₂ ∷ [] 
ReadRegsCond (Leq r₁ r₂) = r₁ ∷ r₂ ∷ [] 

ReadRegs : Command → List Reg
ReadRegs (Assign r e) = r ∷ ReadRegsExp e
ReadRegs (Load r s a) = r ∷ []
ReadRegs (Store a s r) = r ∷ []
ReadRegs (Assume c) = ReadRegsCond c
ReadRegs (Shared r n) = r ∷ []

Safe : Command → Snapshot → Bool
Safe (Assign r (Number n)) s = true
Safe (Assign r (Register r₁)) s = true
Safe (Assign r (Plus r₁ r₂)) s = {!!} 
Safe (Assign r (Minus r₁ r₂)) s = {!!}
Safe (Load x x₁ x₂) s = {!!}
Safe (Store x x₁ x₂) s = {!!}
Safe (Assume x) s = {!!}
Safe (Shared x x₁) s = {!!}
-}

-- Program is list of commands?
--Program = List Command


-- Initial state
--σ-initial : Snapshot
--σ-initial = snapshot ((r10 , (stk , 512)) ∷ (data-start , (pkt , 0)) ∷ (data-end , (pkt , {!!})) ∷ (r1 , (ctx , 0)) ∷ []) [] []

--Dump = List Snapshot

{-
record eBPF : Set where
  field
    current : Snapshot
    dump    : Dump
-}

postulate
  updateEnv : ∀ {r} (c : Env) → r ∈ c → TV → Env

eval : (Δ : State) → Command Δ → State
eval (e ∣ μ ∣ ζ) (Assign r (Number n)) = updateEnv e r (num , n) ∣ μ ∣ ζ
eval (e ∣ μ ∣ ζ) (Assign r₁ (Register r₂)) = updateEnv e r₁ {!!} ∣ μ ∣ ζ
eval (e ∣ μ ∣ ζ) (Assign r (PlusL r₁ r₂)) = updateEnv e r {!!} ∣ μ ∣ ζ
eval (e ∣ μ ∣ ζ) (Assign r (PlusR x x₁)) = {!!}
eval (e ∣ μ ∣ ζ) (Assign r (MinusR x x₁)) = {!!}
eval (e ∣ μ ∣ ζ) (Assign r (Minus x x₁)) = {!!}
eval (e ∣ μ ∣ ζ) (LoadPkt x s x₁) = {!!}
eval (e ∣ μ ∣ ζ) (Load x s x₁) = {!!}
eval (e ∣ μ ∣ ζ) (StorePkt x s x₁) = {!!}
eval (e ∣ μ ∣ ζ) (Store x s x₁) = {!!}
eval (e ∣ μ ∣ ζ) (Assume x) = {!!}
eval (e ∣ μ ∣ ζ) (Shared x x₁) = {!!}
