module eBPF where

open import Data.List
open import Data.List.All
open import Data.Fin
open import Data.Product
open import Data.List.Membership.Propositional

-- temporary
open import Data.Nat

-- Fixed set of registers Register = {r0, ..., r10, data_start, data_end}
data Reg : Set where
  r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 data-start data-end : Reg

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
TaggedValue = (𝓡 × ℕ)

-- a ∈ Address = {0, ..., 511}
Address = Fin 512

-- An environment e maps register names to their contents.
-- e ∈ Env = Register → (𝓡 × ℤ)
Env = List (Reg × TaggedValue)

-- A memory cell is a subsegment of the stack region identified by their
-- start address a and their size sz
-- c ∈ Cell - Address × Size
Cell = List (Address × sz)

-- A memory μ maps memory cells to their contents
-- μ ∈ Mem = Cell → (R × ℤ)
Mem = List (Cell × TaggedValue)

-- ζ is a set of addresses in the stack that hold a number or part of it,
-- but not a pointer, or parts of which
-- ζ ∈ Format = 2^Address -- @TODO: o que isso significa?
Format = List (Address)

data Expr : Set where
  Number   : ℕ → Expr
  Register : Reg → Expr
  Plus     : Reg → Reg → Expr
  Minus    : Reg → Reg → Expr

data Condition : Set where
  Eq  : Reg → Reg → Condition
  Neq : Reg → Reg → Condition
  Leq : Reg → Reg → Condition

data Command : Set where
  Assign : Reg → Expr → Command
  Load   : Reg → sz → Address → Command
  Store  : Address → sz → Reg → Command
  Assume : Condition → Command
  Shared : Reg → ℕ → Command
  
-- Machine state: σ = (e, μ, ζ)
record Snapshot : Set where
  constructor
    snapshot
  field
    environment : Env
    memory      : Mem 
    format      : Format 

-- Program is list of commands?
Program = List Command

-- Initial state
σ-initial : Snapshot
σ-initial = snapshot ((r10 , (stk , 512)) ∷ (data-start , (pkt , 0)) ∷ (data-end , (pkt , {!!})) ∷ (r1 , (ctx , 0)) ∷ []) [] []

Dump = List Snapshot

record eBPF : Set where
  field
    current : Snapshot
    dump    : Dump

