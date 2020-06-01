module TLM where

open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Fin using (Fin)
open import Data.List using (List ; [] ; _∷_)
open import Data.List.All using (All)
open import Data.Maybe using (Maybe ; just ; nothing)
open import Data.Product using (_×_ ; _,_)
open import Data.Vec using (Vec ;  _[_]=_ ; here ; there)renaming (_∷_ to _∷v_)
open import Data.Vec.All using () renaming (All to Allv)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here ; there ; _∷=_)
open import Relation.Binary.PropositionalEquality

data Ty : Set where
  nil      : Ty
  list     : Ty → Ty
  listcons : Ty → Ty

LCtx = List Ty
GCtx = Vec LCtx 3

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

data _≺_ : LCtx → LCtx → Set where
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

data Instr (Δ : GCtx) (Γ : LCtx) : LCtx → Set where
  instr-seq             : ∀ {Γ′ Γ″} → Instr Δ Γ Γ′ → Instr Δ Γ′ Γ″ → Instr Δ Γ Γ″
  instr-branch-list     : ∀ {τ l Γ₁} → (idx : (list τ) ∈ Γ) → Δ [ l ]= Γ₁ → (idx ∷= nil) ≺ Γ₁ → Instr Δ Γ (idx ∷= nil)
  instr-branch-listcons : ∀ {τ l Γ₁} → (idx : (listcons τ) ∈ Γ) → Δ [ l ]= Γ₁ → (idx ∷= nil) ≺ Γ₁ → Instr Δ Γ Γ
  instr-branch-nil      : ∀ {Γ₁ l} → nil ∈ Γ → Δ [ l ]= Γ₁ → Γ ≺ Γ₁ → Instr Δ Γ Γ
  instr-fetch-0-new     : ∀ {τ} → (listcons τ) ∈ Γ → Instr Δ Γ (τ ∷ Γ)
  instr-fetch-0-upd     : ∀ {τ τ′} → (listcons τ) ∈ Γ → (idx : τ′ ∈ Γ) → Instr Δ Γ (idx ∷= list τ)
  instr-fetch-1-new     : ∀ {τ} → (listcons τ) ∈ Γ → Instr Δ Γ (list τ ∷ Γ)
  instr-fetch-1-upd     : ∀ {τ τ′} → (listcons τ) ∈ Γ → (idx : τ′ ∈ Γ) → Instr Δ Γ (idx ∷= list τ)
  instr-cons-new        : ∀ {τ τ₀ τ₁} → τ₀ ∈ Γ → τ₁ ∈ Γ → list τ₀ ⊓ τ₁ ≈ list τ → Instr Δ Γ (listcons τ ∷ Γ)
  instr-cons-upd        : ∀ {τ τ₀ τ₁ τ₂} → τ₀ ∈ Γ → τ₁ ∈ Γ → (idx : τ₂ ∈ Γ) → list τ₀ ⊓ τ₁ ≈ list τ → Instr Δ Γ (idx ∷= listcons τ)

data Block (Δ : GCtx) (Γ : LCtx) : Set where
  block-halt            : Block Δ Γ
  block-seq             : ∀ {Γ′} → Instr Δ Γ Γ′ → Block Δ Γ′ → Block Δ Γ
  block-jump            : ∀ {l Γ₁} → Δ [ l ]= Γ₁ → Γ ≺ Γ₁ → Block Δ Γ


data Program (Δ : GCtx) : Set where
  blocks-label : ∀ {l Γ} → Δ [ l ]= Γ → Block Δ Γ → Program Δ → Program Δ
  blocks-empty : Program Δ

-- Examples

Γ₀ : LCtx
Γ₀ = nil ∷ []

Γ₁ : LCtx
Γ₁ = nil ∷ list nil ∷ []

Γ₂ : LCtx
Γ₂ = []

Δ : GCtx
Δ = Γ₀ ∷v Γ₁ ∷v Γ₂ ∷v Vec.[]


sample : Program Δ
sample = blocks-label here (block-seq
                             (instr-seq (instr-cons-new (here refl) (here refl) lub-1)
                                                        (instr-seq (instr-cons-upd (there (here refl)) (here refl) (here refl) (lub-2 lub-0))
                                                     (instr-cons-upd (there (here refl)) (here refl) (here refl) (lub-2 lub-0))))
                           (block-jump (there here) {!!})) -- L0
        (blocks-label (there here) (block-seq {!!} {!!}) -- L1
        (blocks-label (there (there here)) block-halt -- L2
         blocks-empty)) 


{-
i₀ : Instr Δ Γ₀ (listcons nil ∷ Γ₀)
i₀ = instr-cons (here refl) (here refl) lub-1

i₁ : Instr Δ (listcons nil ∷ Γ₀) (listcons nil ∷ listcons nil ∷ Γ₀)
i₁ = instr-cons (there (here refl)) (here refl) (lub-2 lub-0)

i₂ : Instr Δ (listcons nil ∷ listcons nil ∷ Γ₀) (listcons nil ∷ listcons nil ∷ listcons nil ∷ Γ₀)
i₂ = instr-cons (there (there (here refl))) (here refl) (lub-2 lub-0)

-- i₁ : Instr Δ Γ (nil ∷ Γ)
-- i₁ = instr-fetch-0 (here refl)

-- i₂ : Instr Δ (nil ∷ Γ) (list nil ∷ nil ∷ Γ)
-- i₂ = instr-fetch-1 (there (here refl))

i₃ : Instr Δ (nil ∷ nil ∷ []) (listcons nil ∷ nil ∷ nil ∷ [])
i₃ = instr-cons (here refl) (there (here refl)) lub-1

-- i₄ : Instr Δ Γ (list nil ∷ nil ∷ Γ)
-- i₄ = instr-seq i₁ i₂

-}

-- Fazer exemplos com outros construtores

-- Evaluation

data Val : Ty → Set where
  nil  : Val nil
  cons : ∀ {τ} → Val τ → Val (list τ) → Val (listcons τ)
  

LEnv : LCtx → Set
LEnv Γ = All Val Γ

GEnv : GCtx → Set
GEnv Δ = Allv LEnv Δ

-- Initial context type
Γᵢ : LCtx
Γᵢ = nil ∷ []

-- Initial environment
γᵢ : LEnv Γᵢ
γᵢ = nil All.∷ All.[]

Fuel = ℕ

{-
step : ∀ {Γ Γ′ Δ τ} → (LEnv Γ × Instr Δ Γ τ) → (LEnv Γ′ × Instr Δ Γ′ τ)
step (γ , instr-seq i₁ i₂) = {!!}
step (γ , instr-branch-list x x₁ x₂) = {!!}
step (γ , instr-branch-listcons x x₁ x₂) = {!!}
step (γ , instr-branch-nil x x₁ x₂) = {!!}
step (γ , instr-fetch-0 x) = {!!}
step (γ , instr-fetch-1 x) = {!!}
step (γ , instr-cons x x₁ x₂) = {!!}
-}

