module TLM where

open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Fin using (Fin)
open import Data.List using (List ; [] ; _∷_)
open import Data.List.All using (All ; lookup ; _[_]≔_)
open import Data.Maybe using (Maybe ; just ; nothing)
open import Data.Product using (_×_ ; _,_)
open import Data.Vec using (Vec ;  _[_]=_ ; here ; there)renaming (_∷_ to _∷v_)
open import Data.Vec.All using () renaming (All to Allv ; lookup to lookupv)
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
  instr-branch-list     : ∀ {τ l Γ₁} → (idx : (list τ) ∈ Γ) → Δ [ l ]= Γ₁ → (idx ∷= nil) ≺ Γ₁ → Instr Δ Γ (idx ∷= listcons τ)
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
Γ₁ = list nil ∷ nil ∷ []

Γ₂ : LCtx
Γ₂ = []

Δ : GCtx
Δ = Γ₀ ∷v Γ₁ ∷v Γ₂ ∷v Vec.[]

sample : Program Δ
sample = blocks-label here (block-seq
                             (instr-seq (instr-cons-new (here refl) (here refl) lub-1)
                                        (instr-seq
                                          (instr-cons-upd (there (here refl)) (here refl) (here refl) (lub-2 lub-0))
                                          (instr-cons-upd (there (here refl)) (here refl) (here refl) (lub-2 lub-0))))
                           (block-jump (there here) (env-sub1 refl (lstcons refl) (env-sub1 refl refl env-sub2)))) -- L0
        (blocks-label (there here) (block-seq
                                     (instr-seq (instr-branch-list (here refl) (there (there here)) env-sub2)
                                                (instr-seq
                                                  (instr-fetch-1-upd (here refl) (here refl))
                                                  (instr-branch-nil (there (here refl)) (there here) (env-sub1 refl refl (env-sub1 refl refl env-sub2)))))
                           (block-jump (there (there here)) env-sub2)) -- L1
        (blocks-label (there (there here)) block-halt -- L2
         blocks-empty)) 

-- Evaluation: daqui para baixo não entendi direito

data Val : Ty → Set where
  nil  : Val nil
  cons : ∀ {τ τ₁ τ₂} → Val τ₁ → Val τ₂ → Val (listcons τ)

LEnv : LCtx → Set
LEnv Γ = All Val Γ

Prog : GCtx → Set
Prog Δ = Allv (λ Γ → Block Δ Γ) Δ

{-# NON_TERMINATING #-}
run-step : ∀ {Δ Γ Γ′} → Prog Δ → LEnv Γ → Block Δ Γ → (LEnv Γ′ × Block Δ Γ′)
run-step p r block-halt = {!!} , block-halt
run-step p r (block-seq (instr-seq i₁ i₂) b) = run-step p r (block-seq i₁ (block-seq i₂ b))
run-step p r (block-seq (instr-branch-list idx x x₁) b) = {!!}
run-step p r (block-seq (instr-branch-listcons idx x x₁) b) = {!!}
run-step p r (block-seq (instr-branch-nil x x₁ x₂) b) = {!!}
run-step p r (block-seq (instr-fetch-0-new x) b) = {!!}
run-step p r (block-seq (instr-fetch-0-upd x idx) b) = {!!}
run-step p r (block-seq (instr-fetch-1-new x) b) = {!!}
run-step p r (block-seq (instr-fetch-1-upd x idx) b) = {!!}
run-step p r (block-seq (instr-cons-new v₀ v₁ s) b) = run-step p {!!} b
run-step p r (block-seq (instr-cons-upd v₀ v₁ v′ s) b) = run-step p ({!!} [ {!v′!} ]≔ cons (lookup r v₀) (lookup r v₁)) b
run-step p r (block-jump {i} l s) = {!!} , lookupv i {!!}

{-

-- Initial context type
Γᵢ : LCtx
Γᵢ = nil ∷ []

-- Initial environment
γᵢ : LEnv Γᵢ
γᵢ = nil All.∷ All.[]

Fuel = ℕ

step-block : ∀ {Δ Γ Γ′} → GEnv Δ → LEnv Γ → Block Δ Γ → Block Δ Γ′
step-block δ γ block-halt = block-halt
step-block δ γ (block-seq x b) = {!!}
step-block δ γ (block-jump l s) = {!!}

eval-instr : ∀ {Δ Γ Γ′} → GEnv Δ → LEnv Γ → Instr Δ Γ Γ′ → (LEnv Γ′ × Instr Δ Γ Γ′)
eval-instr δ γ (instr-seq i₁ i₂) = {!!}
eval-instr δ γ (instr-branch-list idx x x₁) = {!!}
eval-instr δ γ (instr-branch-listcons idx x x₁) = {!!}
eval-instr δ γ (instr-branch-nil x x₁ x₂) = {!!}
eval-instr δ γ (instr-fetch-0-new x) = {!!}
eval-instr δ γ (instr-fetch-0-upd x idx) = {!!}
eval-instr δ γ (instr-fetch-1-new x) = {!!}
eval-instr δ γ (instr-fetch-1-upd x idx) = {!!}
eval-instr δ γ i@(instr-cons-new v₀ v₁ s) = cons (lookup γ v₀) (lookup γ v₁) All.∷ γ , i
eval-instr δ γ i@(instr-cons-upd v₀ v₁ v′ s) = {!!} [ {!v′ !} ]≔ cons (lookup γ v₀) (lookup γ v₁) , i

eval : ∀ {Δ Γ Γ′} → GEnv Δ → LEnv Γ → Block Δ Γ → Block Δ Γ′
eval δ γ block-halt = {!!}
eval δ γ (block-seq i b) = {!!}
eval δ γ (block-jump l p) = {!!}

eval-prog : ∀ {Δ} → GEnv Δ → Program Δ → {!!}
eval-prog δ (blocks-label x x₁ p) = {!!}
eval-prog δ blocks-empty = {!!}

-}
