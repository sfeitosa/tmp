module fj where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Data.String using (String; _≟_)
open import Data.Product
open import Data.List
open import Data.List.All
open import Relation.Nullary using (Dec; yes; no; ¬_)

IdName : Set
IdName = String

TypeName : Set
TypeName = String

--------------------------------------------------------------------------------
------------------------ SYNTACTIC DEFINITIONS ---------------------------------
--------------------------------------------------------------------------------

data Expr : Set where
  Var : IdName → Expr
  Field : Expr → IdName → Expr
  Invk : Expr → IdName → List Expr → Expr
  New : TypeName → List Expr → Expr

record ConstrDef : Set where
  constructor Constr
  field
    class : TypeName
    params : List (TypeName × IdName)
    super : List IdName
    init : List (IdName × IdName)

record MethodDef : Set where
  constructor Method
  field
    returns : TypeName
    name : IdName
    params : List (TypeName × IdName) 
    expr : Expr

record ClassDef : Set where
  constructor Class
  field
    name : TypeName
    extends : TypeName
    fields : List (TypeName × IdName)
    constr : ConstrDef
    methods : List MethodDef

-- Value definition

data Value : Expr → Set where
  V_New : ∀ {c pc} -> All Value pc -> Value (New c pc)

-- Class table

CT : Set
CT = List (IdName × ClassDef)

-- Class table lookup

data InCT : CT → IdName → ClassDef → Set where
  CTBase : ∀ {C CD L}      
     → InCT ((C , CD) ∷ L) C CD
  CTStep : ∀ {C C' CD CD' L}
     → InCT L C CD
       ------------------
     → InCT ((C' , CD') ∷ L) C CD

--------------------------------------------------------------------------------
----------------------- AUXILIARY DEFINITIONS ----------------------------------
--------------------------------------------------------------------------------

data subtyping : CT → TypeName → TypeName → Set 
data subtypingL : CT → List TypeName → List TypeName → Set 

-- Subtyping relation

data subtyping where
  SRefl : ∀ {CT C}
         ----------
        → subtyping CT C C
  STrans : ∀ {CT C D E}
         → subtyping CT C D
         → subtyping CT D E
           -------------
         → subtyping CT C E
  SStep : ∀ {CT C CD}
        → InCT CT C CD
          --------------------
        → subtyping CT C (ClassDef.extends CD)

-- Checking subtyping for a list of types

data subtypingL where
  subtypingl_base : ∀ {CT}
             → subtypingL CT [] []
  subtypingl_step : ∀ {CT e e' l l'}
            → subtypingL CT l l'
            → subtyping CT e e'
            → subtypingL CT (e ∷ l) (e' ∷ l')

-- Get a field type from a field list

data InFields : List (TypeName × IdName) → IdName → TypeName → Set where
  IFBase : ∀ {f t flds}
     → InFields ((t , f) ∷ flds) f t
  IFStep : ∀ {f f' t t' flds}
     → InFields flds f t
       ------------------
     → InFields ((t' , f') ∷ flds) f t

-- Field lookup

data fields : CT → TypeName → List (TypeName × IdName) → Set where
  FObject : ∀ {CT}
         → fields CT "Object" []
  FClass : ∀ {CT C CD fd}
         → InCT CT C CD
         → fields CT (ClassDef.extends CD) fd
         → fields CT C (fd ++ (ClassDef.fields CD))

-- Get a method from a method list

data InMethods : List MethodDef → IdName → MethodDef → Set where
  IMBase : ∀ {m mn meths}
     → MethodDef.name m ≡ mn
     → InMethods (m ∷ meths) mn m
  IMStep : ∀ {m mn meths m'}
     → InMethods meths mn m
       ------------------
     → InMethods (m' ∷ meths) mn m

-- Check if a method 'm' is not in a method list

data NotInMethods : List MethodDef → IdName → Set where
  NIMBase : ∀ {mn}
     → NotInMethods [] mn
  NIMStep : ∀ {m mn meths}
     → MethodDef.name m ≢ mn
     → NotInMethods meths mn
     → NotInMethods (m ∷ meths) mn

-- Method type lookup

data mtype : CT → TypeName → IdName → (List TypeName × TypeName) → Set where
  MTClass : ∀ {CT C m CD MD}
          → InCT CT C CD
          → InMethods (ClassDef.methods CD) m MD
          → mtype CT C m (Σ.proj₁ (unzip (MethodDef.params MD)) , MethodDef.returns MD)
  MTSuper : ∀ {CT C m CD MT}
          → InCT CT C CD
          → NotInMethods (ClassDef.methods CD) m
          → mtype CT (ClassDef.extends CD) m MT
            ---------------------------
          → mtype CT C m MT


-- Method body lookup

data mbody : CT → TypeName → IdName → (List IdName × Expr) → Set where
  MBClass : ∀ {CT C m CD MD}
          → InCT CT C CD
          → InMethods (ClassDef.methods CD) m MD
          → mbody CT C m (Σ.proj₂ (unzip (MethodDef.params MD)) , MethodDef.expr MD)
  MBSuper : ∀ {CT C m CD MT}
          → InCT CT C CD
          → NotInMethods (ClassDef.methods CD) m
          → mbody CT (ClassDef.extends CD) m MT
            ---------------------------
          → mbody CT C m MT

--------------------------------------------------------------------------------
-------------------------- EVALUATION DEFINITIONS ------------------------------
--------------------------------------------------------------------------------

-- Substitution of a variable from lists of names and expressions

substV : List IdName → List Expr → IdName → Expr
substV [] _ x = (Var x)
substV _ [] x = (Var x)
substV (x ∷ xs) (y ∷ ys) v with x ≟ v
... | yes _ = y
... | no _ = substV xs ys v

-- Definitions for mutual recursion

subst : List IdName → List Expr → Expr → Expr
substL : List IdName → List Expr → List Expr → List Expr

-- Substitution

subst p v (Var x) = substV p v x
subst p v (Field e f) = Field (subst p v e) f
subst p v (Invk e m ap) = Invk (subst p v e) m (substL p v ap)
subst p v (New c ap) = New c (substL p v ap)

-- Substitution on a list

substL p v [] = []
substL p v (x ∷ xs) = subst p v x ∷ substL p v xs

-- Get the expression according to its position in the constructor parameters

data PickField : List IdName → List Expr → IdName → Expr → Set where
  PFBase : ∀ {e es n ns}
         → PickField (n ∷ ns) (e ∷ es) n e
  PFStep : ∀ {e e' es n n' ns}
         → PickField ns es n e
         → PickField (n' ∷ ns) (e' ∷ es) n e

-- Definitions for mutual recursion

data step : CT → Expr → Expr → Set
data StepL : CT → List Expr → List Expr → Set

-- Evaluation

data step where
  RCField : ∀ {CT e e' f}
          → step CT e e'
            --------------
          → step CT (Field e f) (Field e' f)
  RField : ∀ {CT C f flds ap fi}
         → fields CT C flds
         → PickField (Σ.proj₂ (unzip flds)) ap f fi
           -----------------
         → step CT (Field (New C ap) f) fi
  RInvk : ∀ {CT C e m pc pm pn}
        → mbody CT C m (pn , e)
           ----------------------
        → step CT (Invk (New C pc) m pm) (subst ("this" ∷ pn) ((New C pc) ∷ pm) e)
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

-- Steping each element of a list

data StepL where
  stepl_base : ∀ {CT}
             → StepL CT [] []
  stepl_step : ∀ {CT e e' l l'}
            → StepL CT l l'
            → step CT e e'
            → StepL CT (e ∷ l) (e' ∷ l')

--------------------------------------------------------------------------------
--------------------------- TYPING DEFINITIONS ---------------------------------
--------------------------------------------------------------------------------

-- Syntax of Types

data Type : Set where
  TypeClass : TypeName → Type

-- Gamma context

Context : Set
Context = List (IdName × Type)

-- Context lookup

data InContext : Context → IdName → Type → Set where
  ICBase : ∀ {G x C}
         → InContext ((x , C) ∷ G) x C
  ICStep : ∀ {G x y C D}
         → InContext G x C
         → InContext ((y , D) ∷ G) x C

-- Definitions for mutual recursion

data infer : CT → Context → Expr → Type → Set
data inferL : CT → Context → List Expr → List Type → Set

-- Typing

data infer where
  TVar : ∀ {CT G x C}
       → InContext G x C
         -----------------
       → infer CT G (Var x) C
  TField : ∀ {CT G C Ci e f flds}
         → infer CT G e (TypeClass C)
         → fields CT C flds
         → InFields flds f Ci
           ------------------------
         → infer CT G (Field e f) (TypeClass Ci)
  TInvk : ∀ {CT G C e m mt pm pm'}
        → infer CT G e (TypeClass C)
        → mtype CT C m mt
        → inferL CT G pm pm'
        → subtypingL CT (Data.List.map (λ { (TypeClass t) → t}) pm') (Σ.proj₁ mt)
          -----------------------------
        → infer CT G (Invk e m pm) (TypeClass (Σ.proj₂ mt))
  TNew : ∀ {CT G C flds pc pc'}
       → fields CT C flds
       → inferL CT G pc pc'
       → subtypingL CT (Data.List.map (λ { (TypeClass t) → t }) pc') (Σ.proj₁ (unzip flds))
         ----------------------------
       → infer CT G (New C pc) (TypeClass C)

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
  MOkClass : ∀ {CT CD DD MD E G Gf Gs}
           → Gf ≡ Σ.proj₂ (unzip (MethodDef.params MD))
           → Gs ≡ Data.List.map (λ x → TypeClass x) (Σ.proj₁ (unzip (MethodDef.params MD)))
           → G ≡ ("this", TypeClass (ClassDef.name CD)) ∷ (Data.List.zip Gf Gs)
           → infer CT G (MethodDef.expr MD) (TypeClass E)
           → subtyping CT E (MethodDef.returns MD)
           → InCT CT (ClassDef.extends CD) DD
           → NotInMethods (ClassDef.methods DD) (MethodDef.name MD)
           → MethodOk CT CD MD
  MOkSuper : ∀ {CT CD MD E G Gf Gs m}
           → Gf ≡ Σ.proj₂ (unzip (MethodDef.params MD))
           → Gs ≡ Data.List.map (λ x → TypeClass x) (Σ.proj₁ (unzip (MethodDef.params MD)))
           → G ≡ ("this", TypeClass (ClassDef.name CD)) ∷ (Data.List.zip Gf Gs)
           → infer CT G (MethodDef.expr MD) (TypeClass E)
           → subtyping CT E (MethodDef.returns MD)
           → mtype CT (ClassDef.extends CD) m (Σ.proj₁ (unzip (MethodDef.params MD)), MethodDef.returns MD)
           → MethodOk CT CD MD

-- Class typing

data ClassOk : CT → ClassDef → Set where
  COk : ∀ {CT CD fD K}
      → fields CT (ClassDef.extends CD) fD
      → ConstrDef.params K ≡ fD ++ (ClassDef.fields CD)
      → ConstrDef.super K ≡ Σ.proj₂ (unzip fD)
      → ConstrDef.init K ≡ Data.List.zip (Σ.proj₂ (unzip (ClassDef.fields CD))) (Σ.proj₂ (unzip (ClassDef.fields CD)))
      → All (MethodOk CT CD) (ClassDef.methods CD)
      → ClassOk CT CD

