module etfj where

open import Data.Nat
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; _∷_; []; zip; unzip; _++_)
open import Data.List.All using (All; _∷_; [])
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃)
--open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
--open import Data.List.Membership.Setoid using (_∈_)

-- Expression syntax

data Expr : Set where
  Var   : ℕ → Expr
  Field : Expr → ℕ → Expr
  Invk  : Expr → ℕ → List Expr → Expr
  New   : ℕ → List Expr → Expr

-- Method syntax

record Method : Set where
  field
    ret    : ℕ
    params : List (ℕ × ℕ)
    body   : Expr
    
-- Class syntax

record Class : Set where
  field
    name  : ℕ
    ext   : ℕ
    -- List of field names and types
    flds  : List (ℕ × ℕ)
    -- List of method names with its ret, params, and body
    meths : List (ℕ × Method) --(ℕ × (ℕ × List (ℕ × ℕ) × Expr))

-- Substitution

get : {A : Set} → ℕ → List (ℕ × A) → Maybe A
get x [] = nothing
get x ((y , v) ∷ l) with x ≟ y
... | yes refl = just v
... | no _ = get x l

subs : Expr → List (ℕ × Expr) → Expr
subs-list : List Expr → List (ℕ × Expr) → List Expr

subs (Var x) l with get x l
... | just e = e
... | nothing = Var x
subs (Field e f) l = Field (subs e l) f
subs (Invk e m mp) l = Invk (subs e l) m (subs-list mp l)
subs (New c cp) l = New c (subs-list cp l)

subs-list [] l = []
subs-list (e ∷ el) l = subs e l ∷ subs-list el l

-- Class table: name × class

CT : Set
CT = List (ℕ × Class)

data _∋_∶_ {A : Set} : List (ℕ × A) → ℕ → A → Set where
  here  : ∀ {Δ x d} → ((x , d) ∷ Δ) ∋ x ∶ d
  there : ∀ {Δ x y d₁ d₂} → Δ ∋ x ∶ d₁ → ((y , d₂) ∷ Δ) ∋ x ∶ d₁

data _∈_ : ℕ → List ℕ → Set where
  here  : ∀ {x xs} → x ∈ (x ∷ xs)
  there : ∀ {x y xs} → x ∈ xs → x ∈ (y ∷ xs)

data env-zip {A : Set} {B : Set} : List (ℕ × A) → List B → List (ℕ × B) → Set where
  here  : env-zip [] [] [] 
  there : ∀ {x a b aenv bs benv}
       → env-zip aenv bs benv
       → env-zip ((x , a) ∷ aenv) (b ∷ bs) ((x , b) ∷ benv)

variable
  ths    : ℕ
  Object : ℕ
  ct     : CT

data fields : ℕ → List (ℕ × ℕ) → Set where
  obj   : fields Object []
  other : ∀ {C CD}
       → ct ∋ C ∶ CD
       → fields C (Class.flds CD)

data method : ℕ → ℕ → Method → Set where
  this : ∀ {C CD m mdecl}
      → ct ∋ C ∶ CD
      → (Class.meths CD) ∋ m ∶ mdecl
      → method C m mdecl 

-- Small step relation

infix 4 _⟶_
infix 4 _↦_

data _⟶_ : Expr → Expr → Set 
data _↦_ : List Expr → List Expr → Set 

data _⟶_ where
  R-Field     : ∀ {C cp flds f fi fes}
             → fields C flds
             → env-zip flds cp fes
             → fes ∋ f ∶ fi
             → Field (New C cp) f ⟶ fi
  RC-Field    : ∀ {e e' f}
             → e ⟶ e'
             → Field e f ⟶ Field e' f
  R-Invk      : ∀ {C cp m MD ap ep}
             → method C m MD -- (r , fp , e₀)
             → env-zip (Method.params MD) ap ep
             → Invk (New C cp) m ap ⟶ subs (Method.body MD) ep
--             → Invk (New C cp) m ap ⟶ subs e₀ ((ths , (New C cp)) ∷ ep)
  RC-InvkRecv : ∀ {e e' m mp}
             → e ⟶ e'
             → Invk e m mp ⟶ Invk e' m mp
  RC-InvkArg  : ∀ {e m mp mp'}
             → mp ↦ mp'
             → Invk e m mp ⟶ Invk e m mp'
  RC-NewArg   : ∀ {C cp cp'}
             → cp ↦ cp'
             → New C cp ⟶ New C cp'

data _↦_ where
  here  : ∀ {e e' l} → e ⟶ e' → e ∷ l ↦ e' ∷ l
  there : ∀ {e l l'} → l ↦ l' → e ∷ l ↦ e ∷ l'

-- Context: name × type

Ctx : Set
Ctx = List (ℕ × ℕ)

-- Type system

infix 4 _⊢_∶_
infix 4 _⊧_∶_
data _⊢_∶_ : Ctx → Expr → ℕ → Set
data _⊧_∶_ : Ctx → List Expr → List ℕ → Set

data _⊢_∶_ where
  T-Var   : ∀ {Γ x C}
         → Γ ∋ x ∶ C
         → Γ ⊢ (Var x) ∶ C
  T-Field : ∀ {Γ C Ci e f flds}
         → Γ ⊢ e ∶ C
         → fields C flds
         → flds ∋ f ∶ Ci
         → Γ ⊢ (Field e f) ∶ Ci
  T-Invk  : ∀ {Γ C e m MD mp}
         → Γ ⊢ e ∶ C
         → method C m MD
         → Γ ⊧ mp ∶ proj₂ (unzip (Method.params MD))
         → Γ ⊢ (Invk e m mp) ∶ (Method.ret MD)
  T-New   : ∀ {Γ C cp flds}
         → fields C flds
         → Γ ⊧ cp ∶ proj₂ (unzip flds)
         → Γ ⊢ (New C cp) ∶ C

data _⊧_∶_ where
  here  : ∀ {Γ}
       → Γ ⊧ [] ∶ []
  there : ∀ {Γ e C l Cl}
       → Γ ⊢ e ∶ C
       → Γ ⊧ l ∶ Cl
       → Γ ⊧ e ∷ l ∶ C ∷ Cl

-- Values

data Val : Expr → Set where
  V-New  : ∀ {c cp} → All Val cp → Val (New c cp)

-- Properties

-- Auxiliary lemmas for Progress

postulate 
  eqFields : ∀ {c fs fs'} → fields c fs → fields c fs' → fs ≡ fs'

postulate 
  ⊧-zip : ∀ {Δ₁ Δ₂ vl} → Δ₁ ⊧ vl ∶ (proj₂ (unzip Δ₂)) → (∃ λ zp → env-zip Δ₂ vl zp)

postulate
  ∋-zip : ∀ {E0 E ds Eds v t}
       → E0 ⊧ ds ∶ (proj₂ (unzip E))
       → env-zip E ds Eds
       → E ∋ v ∶ t
       → (∃ λ e → Eds ∋ v ∶ e)

-- Progress

data Progress (e : Expr) : Set where
  Step : ∀ {e'}
      → e ⟶ e'
      → Progress e
  Done : Val e
      → Progress e

data ProgressList (el : List Expr) : Set where
  Step : ∀ {el'}
      → el ↦ el'
      → ProgressList el
  Done : All Val el
      → ProgressList el

-- Progress proof

progress : ∀ {e τ} → [] ⊢ e ∶ τ → Progress e
progress-list : ∀ {el tl} → [] ⊧ el ∶ tl → ProgressList el

progress (T-Var ()) -- this is not necessary anymore
progress (T-Field tp fls bnd) with progress tp
progress (T-Field tp fls bnd) | Step ev = Step (RC-Field ev)
progress (T-Field (T-New flds fts) fls bnd) | Done ev rewrite eqFields flds fls =
  Step (R-Field fls (proj₂ (⊧-zip fts)) (proj₂ (∋-zip fts (proj₂ (⊧-zip fts)) bnd)))
progress (T-Invk tp mt tpl) with progress tp
progress (T-Invk tp mt tpl) | Step ev = Step (RC-InvkRecv ev)
progress (T-Invk tp mt tpl) | Done ev with progress-list tpl
progress (T-Invk tp mt tpl) | Done ev | Step evl = Step (RC-InvkArg evl) 
progress (T-Invk (T-New flds fts) mt tpl) | Done ev | Done evl = Step (R-Invk mt (proj₂ (⊧-zip tpl)))
progress (T-New fls tpl) with progress-list tpl
progress (T-New fls tpl) | Step evl = Step (RC-NewArg evl)
progress (T-New fls tpl) | Done evl = Done (V-New evl)

progress-list here = Done []
progress-list (there tp tpl) with progress tp
... | Step ev = Step (here ev)
... | Done ev with progress-list tpl
...   | Step evl = Step (there evl)
...   | Done evl = Done (ev ∷ evl)

-- Auxiliary lemmas for Preservation

postulate
  ∋-In : ∀ {Δ x} {τ : ℕ} → Δ ∋ x ∶ τ → x ∈ (proj₁ (unzip Δ))

postulate
  ∋-Eq : ∀ {Δ x} {a b : Expr} → Δ ∋ x ∶ a → Δ ∋ x ∶ b → a ≡ b

postulate
  ⊢-Method : ∀ {Γ C m MD} → method C m MD
                          → Γ ⊢ (Method.body MD) ∶ (Method.ret MD)

postulate
  eqMethod : ∀ {c m md md'} → method c m md → method c m md' → md ≡ md'

-- Substitution

postulate
  subst : ∀ {Γ Γ₁ e pe C el} → Γ₁ ⊢ e ∶ C
                             → Γ ⊧ el ∶ proj₂ (unzip Γ₁)
                             → env-zip Γ₁ el pe
                             → Γ ⊢ (subs e pe) ∶ C

postulate
  helper : ∀ {Δ Γ f e τ l w}
        → Δ ∋ f ∶ e
        → w ∋ f ∶ τ
        → env-zip w l Δ 
        → Γ ⊢ e ∶ τ
                   

-- Preservation proof

preservation : ∀ {Γ e e' τ} → Γ ⊢ e ∶ τ → e ⟶ e' → Γ ⊢ e' ∶ τ
preservation-list : ∀ {Γ el el' τl} → Γ ⊧ el ∶ τl → el ↦ el' → Γ ⊧ el' ∶ τl

preservation (T-Var x) () -- Not necessary anymore
preservation (T-Field tp fls bnd) (RC-Field ev) = T-Field (preservation tp ev) fls bnd
preservation (T-Field (T-New x x₁) fls bnd) (R-Field flds zp bnde) rewrite eqFields fls flds | eqFields flds x | ∋-Eq (proj₂ (∋-zip x₁ zp bnd)) bnde = helper bnde bnd zp -- See if it will it be provable
preservation (T-Invk tp tmt tpl) (RC-InvkRecv ev) = T-Invk (preservation tp ev) tmt tpl
preservation (T-Invk tp tmt tpl) (RC-InvkArg evl) = T-Invk tp tmt (preservation-list tpl evl)
preservation (T-Invk (T-New x x₁) tmt tpl) (R-Invk rmt zp) rewrite eqMethod rmt tmt = subst (⊢-Method tmt) tpl zp
preservation (T-New fls tpl) (RC-NewArg evl) = T-New fls (preservation-list tpl evl)

preservation-list here () -- Not necessary anymore
preservation-list (there tp tpl) (here ev) = there (preservation tp ev) tpl
preservation-list (there tp tpl) (there evl) = there tp (preservation-list tpl evl)
