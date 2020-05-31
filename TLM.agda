module TLM where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.List using (List ; [] ; _∷_)
open import Data.Vec using (Vec ;  _[_]=_) renaming (_∷_ to _∷v_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here ; there)
open import Relation.Binary.PropositionalEquality

data Ty : Set where
  nil      : Ty
  list     : Ty → Ty
  listcons : Ty → Ty

Ctx = List Ty
LblCtx = Vec Ctx 2

data _⊂_ : Ty → Ty → Set where
  refl     : ∀ {τ} → τ ⊂ τ
  nil      : ∀ {τ} → nil ⊂ list τ
  lst      : ∀ {τ τ′}
          → τ ⊂ τ′
          → list τ ⊂ list τ′
  lstcons  : ∀ {τ τ′}
          → τ ⊂ τ′
          → listcons τ ⊂ list τ′
  lstmixed : ∀ {τ τ′}
          → τ ⊂ τ′
          → listcons τ ⊂ listcons τ′

data _≺_ : Ctx → Ctx → Set where
  env-sub1 : ∀ {Γ Γ′ Γ″ τ τ′} → Γ ≡ (τ′ ∷ Γ″) → τ′ ⊂ τ → Γ″ ≺ Γ′ → Γ ≺ (τ ∷ Γ′)
  env-sub2 : ∀ {Γ} → Γ ≺ []

data _⊓_≈_ : Ty → Ty → Ty → Set where
  lub-0  : ∀ {τ} → τ ⊓ τ ≈ τ
  lub-1  : ∀ {τ} → list τ ⊓ nil ≈ list τ
  lub-2  : ∀ {τ₁ τ₂ τ₃} → list τ₁ ⊓ list τ₂ ≈ τ₃ → list τ₁ ⊓ listcons τ₂ ≈ τ₃
  lub-2b : ∀ {τ₁ τ₂ τ₃} → list τ₁ ⊓ list τ₂ ≈ τ₃ → listcons τ₁ ⊓ list τ₂ ≈ τ₃
  lub-3  : ∀ {τ₁ τ₂ τ₃} → τ₁ ⊓ τ₂ ≈ τ₃ → list τ₁ ⊓ list τ₂ ≈ list τ₃
  lub-4  : ∀ {τ} → nil ⊓ list τ ≈ list τ
  lub-5  : ∀ {τ} → listcons τ ⊓ nil ≈ list τ
  lub-6  : ∀ {τ} → nil ⊓ listcons τ ≈ list τ
  lub-7  : ∀ {τ₁ τ₂ τ₃} → τ₁ ⊓ τ₂ ≈ τ₃ → listcons τ₁ ⊓ listcons τ₂ ≈ listcons τ₃

data Val : Set where
  nil  : Val
  cons : Val → Val → Val

data Instr (Δ : LblCtx) (Γ : Ctx) : Ctx → Set where
  instr-seq             : ∀ {Γ′ Γ″} → Instr Δ Γ Γ′ → Instr Δ Γ′ Γ″ → Instr Δ Γ Γ″
  instr-branch-list     : ∀ {τ l Γ₁} → (list τ) ∈ Γ → Δ [ l ]= Γ₁ → (nil ∷ Γ) ≺ Γ₁ → Instr Δ Γ (nil ∷ Γ)
  instr-branch-listcons : ∀ {τ l Γ₁} → (listcons τ) ∈ Γ → Δ [ l ]= Γ₁ → (nil ∷ Γ) ≺ Γ₁ → Instr Δ Γ Γ
  instr-branch-nil      : ∀ {Γ₁ l} → nil ∈ Γ → Δ [ l ]= Γ₁ → Γ ≺ Γ₁ → Instr Δ Γ Γ
  instr-fetch-0         : ∀ {τ} → (listcons τ) ∈ Γ → Instr Δ Γ (τ ∷ Γ)
  instr-fetch-1         : ∀ {τ} → (listcons τ) ∈ Γ → Instr Δ Γ (list τ ∷ Γ)
  instr-cons            : ∀ {τ τ₀ τ₁} → τ₀ ∈ Γ → τ₁ ∈ Γ → list τ₀ ⊓ τ₁ ≈ list τ → Instr Δ Γ (listcons τ ∷ Γ)

data Block (Δ : LblCtx) (Γ : Ctx) : Set where
  block-halt            : Block Δ Γ
  block-seq             : ∀ {Γ′} → Instr Δ Γ Γ′ → Block Δ Γ′ → Block Δ Γ
  block-jump            : ∀ {l Γ₁} → Δ [ l ]= Γ₁ → Γ ≺ Γ₁ → Block Δ Γ

data Program (Δ : LblCtx) : Set where
  blocks-label : ∀ {l Γ} → Δ [ l ]= Γ → Block Δ Γ → Program Δ → Program Δ
  blocks-empty : Program Δ

-- Examples

Γ = (listcons nil) ∷ []

Δ : LblCtx
Δ = [] ∷v [] ∷v Vec.[]

i₁ : Instr Δ Γ (nil ∷ Γ)
i₁ = instr-fetch-0 (here refl)

i₂ : Instr Δ (nil ∷ Γ) (list nil ∷ nil ∷ Γ)
i₂ = instr-fetch-1 (there (here refl))

i₃ : Instr Δ (nil ∷ nil ∷ []) (listcons nil ∷ nil ∷ nil ∷ [])
i₃ = instr-cons (here refl) (there (here refl)) lub-1

i₄ : Instr Δ Γ (list nil ∷ nil ∷ Γ)
i₄ = instr-seq i₁ i₂

-- Fazer exemplos com outros construtores
