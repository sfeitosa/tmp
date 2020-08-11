open import Data.Bool
open import Data.Fin
open import Data.List
open import Data.Maybe
open import Data.Nat
open import Data.Product
open import Data.String
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

data Const : Ty → Set where
  num  : ℕ → Const Num
  bool : Bool → Const Boolean
  
data Op (Γ : Ctx) : Ty → Set where
  var : ∀ {x} → x ∈ Γ → Op Γ x
  cst : ∀ {τ} → Const τ → Op Γ τ

data Instr (Γ : Ctx) (τ : Ty) : Ty → Set where
  LD  : ∀ {τ′} → Op Γ τ′ → Instr Γ τ τ′
  ST  : τ ∈ Γ → Instr Γ τ τ
  AND : Op Γ Boolean → Instr Γ τ τ
  OR  : Op Γ Boolean → Instr Γ τ τ
  XOR : Op Γ Boolean → Instr Γ τ τ
  ADD : Op Γ Num → Instr Γ τ τ
  SUB : Op Γ Num → Instr Γ τ τ
  MUL : Op Γ Num → Instr Γ τ τ
  EQ  : Op Γ Boolean → Instr Γ τ τ
  GT  : Op Γ Boolean → Instr Γ τ τ
  GE  : Op Γ Boolean → Instr Γ τ τ
  NOT : Op Γ Boolean → Instr Γ τ τ

data Block (Γ : Ctx) (τ : Ty) : Ty → Set where
  SEQ : ∀ {τ′} → Instr Γ τ τ′ → Block Γ τ τ′ → Block Γ τ τ′
  JMP : ∀ {τ′} → Label → Block Γ τ τ′
  RET : ∀ {τ′} → Block Γ τ τ′

Program : Ctx → Ty → Set
Program Γ τ = ∀ {τ′} → Vec (Block Γ τ τ′) n

-- Evaluation

Env : Ctx → Set
Env Γ = All Const Γ

Fuel = ℕ

eval-op : ∀ {Γ τ} → Env Γ → Op Γ τ → Const τ
eval-op e (var x) = All.lookup e x
eval-op e (cst x) = x

eval : ∀ {Γ τ τ′} → Fuel → Env Γ → Program Γ τ → Const τ′ → Block Γ τ τ′ → Maybe (Env Γ)
eval zero e p cr b = nothing
eval (suc f) e p cr (SEQ (LD x) b) = eval f e p (eval-op e x) b
eval (suc f) e p cr (SEQ (ST v) b) = eval f (e [ v ]≔ cr) p cr b
eval (suc f) e p cr (SEQ (AND x) b) = {!!}
eval (suc f) e p cr (SEQ (OR x) b) = {!!}
eval (suc f) e p cr (SEQ (XOR x) b) = {!!}
eval (suc f) e p cr (SEQ (ADD x) b) = {!!}
eval (suc f) e p cr (SEQ (SUB x) b) = {!!}
eval (suc f) e p cr (SEQ (MUL x) b) = {!!}
eval (suc f) e p cr (SEQ (EQ x) b) = {!!}
eval (suc f) e p cr (SEQ (GT x) b) = {!!}
eval (suc f) e p cr (SEQ (GE x) b) = {!!}
eval (suc f) e p cr (SEQ (NOT x) b) = {!!}
eval (suc f) e p cr (JMP l) = eval f e p cr (Data.Vec.lookup p l)
eval (suc f) e p cr RET = just e

