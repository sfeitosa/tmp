module TLM where

open import Data.Bool
open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Fin using (Fin)
open import Data.List using (List ; [] ; _∷_ ; _[_]∷=_)
open import Data.List.All using (All ; lookup ; _[_]≔_)
open import Data.Maybe using (Maybe ; just ; nothing)
open import Data.Product using (_×_ ; _,_ ; ∃)
open import Data.Vec using (Vec ;  _[_]=_ ; here ; there)renaming (_∷_ to _∷v_)
open import Data.Vec.Properties using ([]=⇒lookup)
open import Data.Vec.All using () renaming (All to Allv ; lookup to lookupv)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here ; there ; _∷=_ ; index)
open import Relation.Binary.PropositionalEquality
open import Data.List.Relation.Unary.All.Properties

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

list-⊂-inv : ∀ {τ τ′} → list τ ⊂ list τ′ → τ ⊂ τ′
list-⊂-inv refl = refl
list-⊂-inv (lst p) = p

⊂-trans : ∀ {t1 t2 t3} → t1 ⊂ t2 → t2 ⊂ t3 → t1 ⊂ t3
⊂-trans refl refl = refl
⊂-trans refl nil = nil
⊂-trans refl (lst p₂) = lst p₂
⊂-trans refl (lstcons p₂) = lstcons p₂
⊂-trans refl (lstmixed p₂) = lstmixed p₂
⊂-trans nil refl = nil
⊂-trans nil (lst p₂) = nil
⊂-trans (lst p₁) refl = lst p₁
⊂-trans (lst p₁) (lst p₂) = lst (⊂-trans p₁ p₂)
⊂-trans (lstcons p₁) refl = lstcons p₁
⊂-trans (lstcons p₁) (lst p₂) = lstcons (⊂-trans p₁ p₂)
⊂-trans (lstmixed p₁) refl = lstmixed p₁
⊂-trans (lstmixed p₁) (lstcons p₂) = lstcons (⊂-trans p₁ p₂)
⊂-trans (lstmixed p₁) (lstmixed p₂) = lstmixed (⊂-trans p₁ p₂)

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

-- Lemmas about least-common-supertype

-- calculating the least subtype

lub : (t1 t2 : Ty) → ∃ (λ t → t1 ⊓ t2 ≈ t)
lub nil nil = nil , lub-0
lub nil (list t2) = list t2 , lub-4
lub nil (listcons t2) = list t2 , lub-6
lub (list t1) nil = list t1 , lub-1
lub (list t1) (list t2) with lub t1 t2
...| t3 , p = list t3 , lub-3 p 
lub (list t1) (listcons t2) with lub t1 t2
...| t3 , p = list t3 , lub-2 (lub-3 p)
lub (listcons t1) nil = list t1 , lub-5
lub (listcons t1) (list t2) with lub t1 t2
...| t3 , p = list t3 , lub-2b (lub-3 p)
lub (listcons t1) (listcons t2) with lub t1 t2
...| t3 , p = listcons t3 , lub-7 p

lub-comm : ∀ {τ₁ τ₂ τ₃} → τ₁ ⊓ τ₂ ≈ τ₃ → τ₂ ⊓ τ₁ ≈ τ₃
lub-comm lub-0 = lub-0
lub-comm lub-1 = lub-4
lub-comm lub-4 = lub-1
lub-comm (lub-2 p) = lub-2b (lub-comm p)
lub-comm (lub-2b p) = lub-2 (lub-comm p)
lub-comm (lub-3 p) = lub-3 (lub-comm p)
lub-comm lub-5 = lub-6
lub-comm lub-6 = lub-5
lub-comm (lub-7 p) = lub-7 (lub-comm p)

lub-subtype-left  : ∀ {τ₁ τ₂ τ₃} → τ₁ ⊓ τ₂ ≈ τ₃ → τ₁ ⊂ τ₃
lub-subtype-left lub-0 = refl
lub-subtype-left lub-1 = refl
lub-subtype-left (lub-2 p) = lub-subtype-left p
lub-subtype-left (lub-2b p) with lub-subtype-left p
...| p′ = ⊂-trans (lstcons refl) p′
lub-subtype-left (lub-3 p) = lst (lub-subtype-left p)
lub-subtype-left lub-4 = nil
lub-subtype-left lub-5 = lstcons refl
lub-subtype-left lub-6 = nil
lub-subtype-left (lub-7 p) = lstmixed (lub-subtype-left p)

lub-subtype-right : ∀ {τ₁ τ₂ τ₃} → τ₁ ⊓ τ₂ ≈ τ₃ → τ₂ ⊂ τ₃
lub-subtype-right lub-0 = refl
lub-subtype-right lub-1 = nil
lub-subtype-right (lub-2 p) with lub-subtype-right p
... | p′ = ⊂-trans (lstcons refl) p′
lub-subtype-right (lub-2b p) = lub-subtype-right p
lub-subtype-right (lub-3 p) = lst (lub-subtype-right p)
lub-subtype-right lub-4 = refl
lub-subtype-right lub-5 = nil
lub-subtype-right lub-6 = lstcons refl
lub-subtype-right (lub-7 p) = lstmixed (lub-subtype-right p)

lub-of-subtype : ∀ {τ₁ τ₂} → τ₁ ⊂ τ₂ → τ₁ ⊓ τ₂ ≈ τ₂
lub-of-subtype refl = lub-0
lub-of-subtype nil = lub-4
lub-of-subtype (lst p) = lub-3 (lub-of-subtype p)
lub-of-subtype (lstcons p) = lub-2b (lub-3 (lub-of-subtype p))
lub-of-subtype (lstmixed p) = lub-7 (lub-of-subtype p)

data Instr (Δ : GCtx) (Γ : LCtx) : LCtx → Set where
  instr-seq             : ∀ {Γ′ Γ″} → Instr Δ Γ Γ′ → Instr Δ Γ′ Γ″ → Instr Δ Γ Γ″
  instr-branch-list     : ∀ {τ l Γ₁} → (idx : (list τ) ∈ Γ) → Δ [ l ]= Γ₁ → (idx ∷= nil) ≺ Γ₁ → Instr Δ Γ (idx ∷= listcons τ)
  instr-branch-listcons : ∀ {τ l Γ₁} → (idx : (listcons τ) ∈ Γ) → Δ [ l ]= Γ₁ → (idx ∷= nil) ≺ Γ₁ → Instr Δ Γ Γ
  instr-branch-nil      : ∀ {l Γ₁} → nil ∈ Γ → Δ [ l ]= Γ₁ → Γ ≺ Γ₁ → Instr Δ Γ Γ
  instr-fetch-0-new     : ∀ {τ} → (listcons τ) ∈ Γ → Instr Δ Γ (τ ∷ Γ)
  instr-fetch-0-upd     : ∀ {τ} → (listcons τ) ∈ Γ → (idx : τ ∈ Γ) → Instr Δ Γ (idx ∷= τ)
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
        (blocks-label (there (there here)) {!!} -- L2
         blocks-empty)) 

-- Evaluation

data Val : Ty → Set where
  nil    : Val nil
  nil-l  : ∀ {τ} → Val (list τ)
  cons   : ∀ {τ} → Val τ → Val (list τ) → Val (listcons τ)
  cons-l : ∀ {τ} → Val τ → Val (list τ) → Val (list τ)


LEnv : LCtx → Set
LEnv Γ = All Val Γ

Prog : GCtx → Set
Prog Δ = Allv (λ Γ → Block Δ Γ) Δ

subsumption : ∀ {τ₁ τ₂} → τ₁ ⊂ τ₂ → Val τ₁ → Val τ₂
subsumption refl nil = nil
subsumption refl nil-l = nil-l
subsumption refl (cons v v₁) = cons v v₁
subsumption refl (cons-l v v₁) = v₁
subsumption nil nil = nil-l
subsumption (lst p) nil-l = nil-l
subsumption (lst p) (cons-l v v₁) = nil-l
subsumption (lstcons p) (cons v v₁) = nil-l
subsumption (lstmixed p) (cons v v₁) = cons (subsumption p v) nil-l

  
subsumption-env : ∀ {Γ₁ Γ₂} → Γ₁ ≺ Γ₂ → LEnv Γ₁ → LEnv Γ₂
subsumption-env (env-sub1 refl x₁ p) (x All.∷ xs) = subsumption x₁ x All.∷ subsumption-env p xs
subsumption-env env-sub2 r = All.[]

update-env : ∀ {τ τ′ Γ} → LEnv Γ → (i : τ′ ∈ Γ) → Val τ → LEnv (i ∷= τ)
update-env (x All.∷ xs) (here px₁) v = v All.∷ xs
update-env (x All.∷ xs) (there i) v = x All.∷ update-env xs i v


Fuel = ℕ

run-step : ∀ {Δ Γ Γ′} → Fuel → Prog Δ → LEnv Γ → Block Δ Γ → Maybe (LEnv Γ′)
run-step zero p r b = nothing
run-step (suc f) p r block-halt = just {!!}
run-step (suc f) p r (block-seq (instr-seq i₁ i₂) b) = run-step f p r (block-seq i₁ (block-seq i₂ b))
run-step (suc f) p r (block-seq (instr-branch-list {τ} v l s) b) with lookup r v
... | nil-l = nothing -- type error (aqui é o problema, após adicionar o "nil-l : ∀ {τ} → Val (list τ)" no Val)
... | cons-l v₁ v₂ = run-step f p (update-env r v (cons v₁ v₂)) b
run-step (suc f) p r (block-seq (instr-branch-listcons v l s) b) = run-step f p r b
run-step (suc f) p r (block-seq (instr-branch-nil {i} v l s) b) rewrite sym ([]=⇒lookup l) =
  run-step f p (subsumption-env s r) (lookupv i p)
run-step (suc f) p r (block-seq (instr-fetch-0-new v) b) with lookup r v
... | (cons v₁ v₂) = run-step f p (v₁ All.∷ r) b
run-step (suc f) p r (block-seq (instr-fetch-0-upd {τ} v v′) b) with lookup r v
... | (cons v₁ v₂) = run-step f p (update-env r v′ v₁) b
run-step (suc f) p r (block-seq (instr-fetch-1-new v) b) with lookup r v
... | (cons v₁ v₂) = run-step f p (v₂ All.∷ r) b
run-step (suc f) p r (block-seq (instr-fetch-1-upd {τ} v v′) b) with lookup r v
... | (cons v₁ v₂) = run-step f p (update-env r v′ v₂) b
run-step (suc f) p r (block-seq (instr-cons-new v₀ v₁ s) b) =
  run-step f p (cons (subsumption (list-⊂-inv (lub-subtype-left (lub-of-subtype (lub-subtype-left s)))) (lookup r v₀))
                     (subsumption (lub-subtype-right s) (lookup r v₁)) All.∷ r) b
run-step (suc f) p r (block-seq (instr-cons-upd {τ} v₀ v₁ v′ s) b) = run-step f p (update-env r v′
  (cons (subsumption (list-⊂-inv (lub-subtype-left (lub-of-subtype (lub-subtype-left s)))) (lookup r v₀))
        (subsumption (lub-subtype-right s) (lookup r v₁)))) b
run-step (suc f) p r (block-jump {i} l s) rewrite sym ([]=⇒lookup l) = run-step f p (subsumption-env s r) (lookupv i p)
