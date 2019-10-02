------------------------------------------
-- Evaluation of FJ expressions in Agda --
-- Author: Samuel da Silva Feitosa      --
--         Alejandro Serrano Mena       --
-- Date: Between Feb and Apr / 2019     --
------------------------------------------
import ClassTable as CT

module Eval {c i} (Δ : CT.WFCT c i) where

open import Data.Nat
open import Data.List.All
open import Data.Product
open import Data.Maybe
open import Data.Vec.All renaming (All to AllV ; lookup to lookupV)
open import Syntax Δ
open import Implementation Δ

open CT c i
open CSig
open CImpl

-- Values associated to their types on a given context
------------------------------------------------------

Env : Ctx → Set
Env Γ = All Val Γ

-- The fuel is represented as a natural number
----------------------------------------------

Fuel = ℕ

-- Mutual recursive evaluation functions definition
---------------------------------------------------

eval      : ∀ {Γ τ c}  → Fuel → (m : Maybe (Val (class τ))) → CTImpl → Env Γ
                       → Expr Γ (maybe (λ x → just τ) nothing m) c → Maybe (Val c)
eval-list : ∀ {Γ τ cs} → Fuel → (m : Maybe (Val (class τ))) → CTImpl → Env Γ
                       → All (Expr Γ (maybe (λ x → just τ) nothing m)) cs → Maybe (All Val cs)

-- Fuel based evaluation for a single expression
------------------------------------------------

eval zero _ _ _ _ = nothing
-- Expressions with This
eval (suc fuel) (just τ) δ γ This = just τ
-- R-Var
eval (suc fuel) (just τ) δ γ (Var x) = just (lookup γ x)
-- RC-Field and R-Field
eval (suc fuel) (just τ) δ γ (Field e f) with eval fuel (just τ) δ γ e
... | nothing = nothing
... | just (VNew p cp) = just (lookup cp (∈-lift p cp f))
-- RC-Invk-Recv, RC-Invk-Arg, and R-Invk
eval (suc fuel) (just τ) δ γ (Invk e m mp) with eval-list fuel (just τ) δ γ mp
... | nothing = nothing
... | just mp' with eval fuel (just τ) δ γ e
...   | nothing = nothing
...   | just v@(VNew {C} {D} p cp) =
          let mi = lookup (implementations D δ) m
            in eval fuel (just v) δ mp' mi
-- RC-New-Arg
eval (suc fuel) (just τ) δ γ (New c cp) with eval-list fuel (just τ) δ γ cp
... | nothing = nothing
... | just cp' = just (VNew refl cp')
-- R-Cast
eval (suc fuel) (just τ) δ γ (UCast p e) with eval fuel (just τ) δ γ e
... | nothing = nothing
... | just (VNew p' cp) = just (VNew (<:-trans p' p) cp)
-- Main expression or lambda term
-- R-Var
eval (suc fuel) nothing δ γ (Var x) = just (lookup γ x)
-- RC-Field and R-Field
eval {Γ} {τ} (suc fuel) nothing δ γ (Field e f) with eval {Γ} {τ} fuel nothing δ γ e
... | nothing = nothing
... | just (VNew p cp) = just (lookup cp (∈-lift p cp f))
-- RC-Invk-Recv, RC-Invk-Arg, and R-Invk
eval {Γ} {τ} (suc fuel) nothing δ γ (Invk e m mp) with eval-list {Γ} {τ} fuel nothing δ γ mp
... | nothing = nothing
... | just mp' with eval {Γ} {τ} fuel nothing δ γ e
...   | nothing = nothing
...   | just v@(VNew {C} {D} p cp) =
          let mi = lookup (implementations D δ) m
            in eval fuel (just v) δ mp' mi
-- RC-New-Arg
eval {Γ} {τ} (suc fuel) nothing δ γ (New c cp) with eval-list {Γ} {τ} fuel nothing δ γ cp
... | nothing = nothing
... | just cp' = just (VNew refl cp')
-- R-Cast
eval {Γ} {τ} (suc fuel) nothing δ γ (UCast p e) with eval {Γ} {τ} fuel nothing δ γ e
... | nothing = nothing
... | just (VNew p' cp) = just (VNew (<:-trans p' p) cp)
-- R-Lam
eval (suc fuel) nothing δ γ (Lam i e) = just (VLam e)
-- R-Lam-Arg and R-Invk-Lam
eval {Γ} {τ} (suc fuel) nothing δ γ (InvkL e lp) with eval-list {Γ} {τ} fuel nothing δ γ lp
... | nothing = nothing
... | just lp' with eval {Γ} {τ} fuel nothing δ γ e
...   | nothing = nothing
...   | just (VLam b) = eval {τ = τ} fuel nothing δ lp' b

-- Fuel based evaluation for a list of expressions
--------------------------------------------------

-- Out of fuel
eval-list zero _ _ _ _ = nothing
-- Empty list
eval-list (suc fuel) τ δ γ [] = just []
-- Recursive definition
eval-list (suc fuel) τ δ γ (p ∷ ps) with eval fuel τ δ γ p
... | nothing = nothing 
... | just v with eval-list fuel τ δ γ ps
...   | nothing = nothing
...   | just vs = just (v ∷ vs)
