module common where

open import Data.List
open import Data.Nat
open import Data.Product

infix 7 _⇒_
data Ty : Set where
  bool : Ty
  _⇒_ : Ty → Ty → Ty

Ctx : Set
Ctx = List (ℕ × Ty)
