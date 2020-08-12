open import Agda.Builtin.Nat using (_+_ ; _-_ ; _*_ ; _==_ ; _<_)
open import Data.Bool hiding (_<_)
open import Data.Fin as Fin hiding (_+_ ; _-_ ; _<_)
open import Data.List
open import Data.Maybe
open import Data.Nat hiding (_<_)
open import Data.Product

open import Data.Vec hiding (_[_]≔_)

open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All as All

module Instr (n : ℕ) where

Label : Set
Label = Fin n

-- Types

data Ty : Set where
  Num     : Ty
  Boolean : Ty

Ctx = List Ty

-- Syntax

Const : Ty → Set
Const Num = ℕ
Const Boolean = Bool
  
data Op (Γ : Ctx) : Ty → Set where
  var : ∀ {x} → x ∈ Γ → Op Γ x
  cst : ∀ {τ} → Const τ → Op Γ τ

data Instr (Γ : Ctx) : Ty → Ty → Set where
  LD   : ∀ {τ τ′} → Op Γ τ′ → Instr Γ τ τ′
  ST   : ∀ {τ} → τ ∈ Γ → Instr Γ τ τ
  SR   : Boolean ∈ Γ → Instr Γ Boolean Boolean
  RS   : Boolean ∈ Γ → Instr Γ Boolean Boolean
  AND  : Op Γ Boolean → Instr Γ Boolean Boolean
  OR   : Op Γ Boolean → Instr Γ Boolean Boolean
  XOR  : Op Γ Boolean → Instr Γ Boolean Boolean
  ADD  : Op Γ Num → Instr Γ Num Num
  SUB  : Op Γ Num → Instr Γ Num Num
  MUL  : Op Γ Num → Instr Γ Num Num
  EQ   : Op Γ Num → Instr Γ Num Boolean
  GT   : Op Γ Num → Instr Γ Num Boolean
  LT   : Op Γ Num → Instr Γ Num Boolean
  NOT  : Instr Γ Boolean Boolean
  JMPC : Label → Instr Γ Boolean Boolean

data Block (Γ : Ctx) (τ : Ty) : Ty → Set where
  SEQ  : ∀ {τ′ τ″} → Instr Γ τ τ′ → Block Γ τ′ τ″ → Block Γ τ τ″
  JMP  : Label → Block Γ τ τ
  RET  : Block Γ τ τ

Program : Ctx → Set
Program Γ = ∀ {τ τ′} → Vec (Block Γ τ τ′) n

-- Evaluation

Env : Ctx → Set
Env Γ = All Const Γ

Fuel = ℕ

eval-op : ∀ {Γ τ} → Env Γ → Op Γ τ → Const τ
eval-op e (var x) = All.lookup e x
eval-op e (cst x) = x

eval : ∀ {Γ τ τ′} → Fuel → Env Γ → Program Γ → Const τ → Block Γ τ τ′ → Maybe (Env Γ)
eval zero e p cr b = nothing
eval (suc f) e p cr (SEQ (LD x) b) = eval f e p (eval-op e x) b
eval (suc f) e p cr (SEQ (ST v) b) = eval f (e [ v ]≔ cr) p cr b
eval (suc f) e p cr (SEQ (SR v) b) = eval f (e [ v ]≔ (All.lookup e v ∨ cr)) p cr b
eval (suc f) e p cr (SEQ (RS v) b) = eval f (e [ v ]≔ (All.lookup e v ∧ not cr)) p cr b
eval (suc f) e p cr (SEQ (AND x) b) = eval f e p (eval-op e x ∧ cr) b
eval (suc f) e p cr (SEQ (OR x) b) = eval f e p (eval-op e x ∨ cr) b
eval (suc f) e p cr (SEQ (XOR x) b) = eval f e p (eval-op e x xor cr) b
eval (suc f) e p cr (SEQ (ADD x) b) = eval f e p (eval-op e x + cr) b
eval (suc f) e p cr (SEQ (SUB x) b) = eval f e p (eval-op e x - cr) b
eval (suc f) e p cr (SEQ (MUL x) b) = eval f e p (eval-op e x * cr) b
eval (suc f) e p cr (SEQ (EQ x) b) = eval f e p (eval-op e x == cr) b
eval (suc f) e p cr (SEQ (GT x) b) = eval f e p (eval-op e x < cr) b
eval (suc f) e p cr (SEQ (LT x) b) = eval f e p (cr < eval-op e x) b
eval (suc f) e p cr (SEQ NOT b) = eval f e p (not cr) b
eval (suc f) e p false (SEQ (JMPC l) b) = eval f e p false b
eval {Γ} {τ} (suc f) e p true (SEQ (JMPC l) b) = eval {Γ} {τ} {τ} f e p true (Data.Vec.lookup p l)
eval {Γ} {τ} (suc f) e p cr (JMP l) = eval {Γ} {τ} {τ} f e p cr (Data.Vec.lookup p l)
eval (suc f) e p cr RET = just e

