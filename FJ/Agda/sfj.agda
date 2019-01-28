module sfj where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Data.Nat
open import Data.Product
open import Data.List
open import Data.List.All
open import Relation.Nullary using (Dec; yes; no; ¬_)

Name : Set
Name = ℕ

--------------------------------------------------------------------------------
------------------------ SYNTACTIC DEFINITIONS ---------------------------------
--------------------------------------------------------------------------------

data Expr : Set where
  Var : Name → Expr
  Field : Expr → Name → Expr
  Invk : Expr → Name → List Expr → Expr
  New : Name → List Expr → Expr

record ConstrDef : Set where
  constructor Constr
  field
    class  : Name
    params : List (Name × Name)
    init   : List (Name × Name)

record MethodDef : Set where
  constructor Method
  field
    returns : Name
    name    : Name
    params  : List (Name × Name) 
    expr    : Expr

record ClassDef : Set where
  constructor Class
  field
    name    : Name
    fields  : List (Name × Name)
    constr  : ConstrDef
    methods : List MethodDef

-- Value definition

data Value : Expr → Set where
  VNew : ∀ {c pc} → All Value pc → Value (New c pc)

-- Class table

CT : Set
CT = List (Name × ClassDef)

-- Class table lookup

data InCT : CT → Name → ClassDef → Set where
  CTBase : ∀ {C CD L}      
     → InCT ((C , CD) ∷ L) C CD
  CTStep : ∀ {C C' CD CD' L}
     → InCT L C CD
       ------------------
     → InCT ((C' , CD') ∷ L) C CD

--------------------------------------------------------------------------------
----------------------- AUXILIARY DEFINITIONS ----------------------------------
--------------------------------------------------------------------------------

-- Get a field type from a field list

data InFields : List (Name × Name) → Name → Name → Set where
  IFBase : ∀ {f t flds}
     → InFields ((t , f) ∷ flds) f t
  IFStep : ∀ {f f' t t' flds}
     → InFields flds f t
       ------------------
     → InFields ((t' , f') ∷ flds) f t

data InFExprs : List (Name × Expr) → Name → Expr → Set where
  IEBase : ∀ {f e fes}
    → InFExprs ((f , e) ∷ fes) f e
  IEStep : ∀ {f f' e e' fes}
    → InFExprs fes f e
    → InFExprs ((f' , e') ∷ fes) f e

-- Field lookup

data fields : CT → Name → List (Name × Name) → Set where
  FObject : ∀ {CT}
         → fields CT 0 []
  FClass : ∀ {CT C CD}
         → InCT CT C CD
         → fields CT C (ClassDef.fields CD)

-- Get a method from a method list

data InMethods : List MethodDef → Name → MethodDef → Set where
  IMBase : ∀ {m mn meths}
     → MethodDef.name m ≡ mn
     → InMethods (m ∷ meths) mn m
  IMStep : ∀ {m mn meths m'}
     → InMethods meths mn m
       ------------------
     → InMethods (m' ∷ meths) mn m

-- Method type lookup

data mtype : CT → Name → Name → (List Name × Name) → Set where
  MTClass : ∀ {CT C m CD MD}
          → InCT CT C CD
          → InMethods (ClassDef.methods CD) m MD
          → mtype CT C m (Σ.proj₁ (unzip (MethodDef.params MD)) , MethodDef.returns MD)


-- Method body lookup

data mbody : CT → Name → Name → (List Name × Expr) → Set where
  MBClass : ∀ {CT C m CD MD}
          → InCT CT C CD
          → InMethods (ClassDef.methods CD) m MD
          → mbody CT C m (Σ.proj₂ (unzip (MethodDef.params MD)) , MethodDef.expr MD)

--------------------------------------------------------------------------------
-------------------------- EVALUATION DEFINITIONS ------------------------------
--------------------------------------------------------------------------------

-- Substitution of a variable from lists of names and expressions

substV : List Name → List Expr → Name → Expr
substV [] _ x = (Var x)
substV _ [] x = (Var x)
substV (x ∷ xs) (y ∷ ys) v with x ≟ v
... | yes _ = y
... | no _ = substV xs ys v

-- Definitions for mutual recursion

subst : List Name → List Expr → Expr → Expr
substL : List Name → List Expr → List Expr → List Expr

-- Substitution

subst p v (Var x) = substV p v x
subst p v (Field e f) = Field (subst p v e) f
subst p v (Invk e m ap) = Invk (subst p v e) m (substL p v ap)
subst p v (New c ap) = New c (substL p v ap)

-- Substitution on a list

substL p v [] = []
substL p v (x ∷ xs) = subst p v x ∷ substL p v xs

-- Get the expression according to its position in the constructor parameters

{-
data PickField : List (Name × Name) → List Expr → Name → Expr → Set where
  PFBase : ∀ {e es n ns t}
         → PickField ((t , n) ∷ ns) (e ∷ es) n e
  PFStep : ∀ {e e' es n n' ns}
         → PickField ns es n e
         → PickField (n' ∷ ns) (e' ∷ es) n e
-}

data ZipFlds : List (Name × Name) → List Expr → List (Name × Expr) → Set where
  ZFNil  : ZipFlds [] [] []
  ZFCons : ∀ {flds es fes t f e}
    → ZipFlds flds es fes
    → ZipFlds ((t , f) ∷ flds) (e ∷ es) ((f , e) ∷ fes)

-- Definitions for mutual recursion

data step : CT → Expr → Expr → Set
data StepL : CT → List Expr → List Expr → Set

-- Evaluation

data step where
  RCField : ∀ {CT e e' f}
          → step CT e e'
            --------------
          → step CT (Field e f) (Field e' f)
  RField : ∀ {CT C fi flds ap ei fes}
         → fields CT C flds
         → ZipFlds flds ap fes
         → InFExprs fes fi ei
           -----------------
         → step CT (Field (New C ap) fi) ei
  RInvk : ∀ {CT C e m pc pm pn}
        → mbody CT C m (pn , e)
           ----------------------
        → step CT (Invk (New C pc) m pm) (subst (0 ∷ pn) ((New C pc) ∷ pm) e)
  RCInvkRecv : ∀ {CT e e' m pm}
             → step CT e e'
               -----------------
             → step CT (Invk e m pm) (Invk e' m pm)
  RCInvkArg : ∀ {CT e m pm pm'}
              → StepL CT pm pm'
              ----------------
              → step CT (Invk e m pm) (Invk e m pm')
  RCNewArg : ∀ {CT C pc pc'}
           → StepL CT pc pc'
             ----------------
           → step CT (New C pc) (New C pc')

data StepL where
  SLHere : ∀ {CT e e' l}
             → step CT e e'
             → StepL CT (e ∷ l) (e' ∷ l)
  SLThere : ∀ {CT e l l'}
              → StepL CT l l'
              → StepL CT (e ∷ l) (e ∷ l')
             

--------------------------------------------------------------------------------
--------------------------- TYPING DEFINITIONS ---------------------------------
--------------------------------------------------------------------------------

-- Gamma context

Context : Set
Context = List (Name × Name)

-- Context lookup

data InContext : Context → Name → Name → Set where
  ICBase : ∀ {G x C}
         → InContext ((x , C) ∷ G) x C
  ICStep : ∀ {G x y C D}
         → InContext G x C
         → InContext ((y , D) ∷ G) x C

-- Definitions for mutual recursion

data infer : CT → Context → Expr → Name → Set
data inferL : CT → Context → List Expr → List Name → Set

-- Typing

data infer where
  TVar : ∀ {CT G x C}
       → InContext G x C
         -----------------
       → infer CT G (Var x) C
  TField : ∀ {CT G C Ci e f flds}
         → infer CT G e C
         → fields CT C flds
         → InFields flds f Ci
           ------------------------
         → infer CT G (Field e f) Ci
  TInvk : ∀ {CT G C e m mt pm pm'}
        → infer CT G e C
        → mtype CT C m mt
        → inferL CT G pm pm'
        → pm' ≡ Σ.proj₁ mt
          -----------------------------
        → infer CT G (Invk e m pm) (Σ.proj₂ mt)
  TNew : ∀ {CT G C flds pc pc'}
       → fields CT C flds
       → inferL CT G pc pc'
       → pc' ≡ Σ.proj₁ (unzip flds)
         ----------------------------
       → infer CT G (New C pc) C

-- Typing a list

data inferL where
  ILBase : ∀ {CT G}
             → inferL CT G [] []
  ILStep : ∀ {CT G e e' l l'}
            → inferL CT G l l'
            → infer CT G e e'
            → inferL CT G (e ∷ l) (e' ∷ l')

-- Method typing

data MethodOk : CT → ClassDef → MethodDef → Set where
  MOkClass : ∀ {CT CD MD G Gf Gs}
           → Gf ≡ Σ.proj₂ (unzip (MethodDef.params MD))
           → Gs ≡ (Σ.proj₁ (unzip (MethodDef.params MD)))
           → G ≡ (0 , (ClassDef.name CD)) ∷ (Data.List.zip Gf Gs)
           → infer CT G (MethodDef.expr MD) (MethodDef.returns MD)
           → MethodOk CT CD MD

-- Class typing

data ClassOk : CT → ClassDef → Set where
  COk : ∀ {CT CD K}
      → ConstrDef.params K ≡ ClassDef.fields CD
      → ConstrDef.init K ≡ Data.List.zip (Σ.proj₂ (unzip (ClassDef.fields CD))) (Σ.proj₂ (unzip (ClassDef.fields CD)))
      → All (MethodOk CT CD) (ClassDef.methods CD)
      → ClassOk CT CD

--------------------------------------------------------------------------------
---------------------------------- PROOFS --------------------------------------
--------------------------------------------------------------------------------

-- Progress definition
data Progress (e : Expr) : Set where
  Step : ∀ {CT e'}
       → step CT e e'
       → Progress e
  Done : Value e
       → Progress e

data ProgressL (el : List Expr) : Set where
  Step : ∀ {CT el'}
      → StepL CT el el'
      → ProgressL el
  Done : All Value el
      → ProgressL el
  
-- Theorem: progress
progress  : ∀ {CT e C} → infer CT [] e C → Progress e
progressL : ∀ {CT el el'} → inferL CT [] el el' → ProgressL el

---- Var
progress (TVar ())
---- Field
progress (TField tyof flds inflds) with progress tyof
progress (TField tyof flds inflds) | Step stp = Step (RCField stp)
progress (TField {flds = fs} (TNew x₁ x₂ x₃) flds inflds) | Done (VNew x) = Step (RField flds {!!} {!!})
---- Invk
progress (TInvk tyof mty infl pm) with progress tyof
progress (TInvk tyof mty infl pm) | Step stp = Step (RCInvkRecv stp)
progress (TInvk tyof mty infl pm) | Done val with progressL infl
progress (TInvk tyof mty infl pm) | Done val | Step x = Step (RCInvkArg x)
progress (TInvk (TNew x₁ x₂ x₃) (MTClass x₄ x₅) infl refl) | Done (VNew x) | Done valL = Step (RInvk (MBClass x₄ x₅))
---- New
progress (TNew flds infl pc) with progressL infl
progress (TNew flds infl pc) | Step x = Step (RCNewArg x)
progress (TNew flds infl pc) | Done x = Done (VNew x)

progressL ILBase = Done []
progressL (ILStep x x₁) with progressL x
progressL (ILStep x x₁) | Step x₂ = Step (SLThere x₂)
progressL (ILStep infL inf) | Done valL with progress inf
progressL (ILStep infL inf) | Done valL | Step x = Step (SLHere x)
progressL (ILStep infL inf) | Done valL | Done x = Done (x ∷ valL)
