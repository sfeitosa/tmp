import ClassTable as CT

module Auxiliary {n} (Δ : CT.CTSig n) where

open import Data.Product
open import Data.List hiding (lookup)
open import Data.Vec hiding (_++_)
open import Data.Vec.All hiding (lookup)

open CT n
open Ty
open CSig

fields : Ty → List Ty
fields τ =
  concatMap (λ τ₁ → flds (c τ₁)) (supers (c τ)) ++ flds (c τ)
  where
    c : Ty → CSig
    c σ = lookup (class σ) Δ

signatures : Ty → List (List Ty × Ty)
signatures τ =
  concatMap (λ τ₁ → signs (c τ₁)) (supers (c τ)) ++ signs (c τ)
  where
    c : Ty → CSig
    c σ = lookup (class σ) Δ

