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

data CT : Set where
  CTEmpty : CT
  CTContent : CT → IdName → ClassDef → CT

-- Class table lookup

data InCT : CT → IdName → ClassDef → Set where
  CTZ : ∀ {ct cn cd}
        -------------
      → InCT (CTContent ct cn cd) cn cd
  CTS : ∀ {ct cn cd cn' cd'}
      → cn ≢ cn'
      → InCT ct cn cd
        ---------------------
      → InCT (CTContent ct cn' cd') cn cd

--------------------------------------------------------------------------------
----------------------- AUXILIARY DEFINITIONS ----------------------------------
--------------------------------------------------------------------------------

data subtyping : CT → TypeName → TypeName → Set 
data subtypingL : CT → List TypeName → List TypeName → Set 

-- Subtyping relation

data subtyping where
  SRefl : ∀ {ct c}
         ----------
        → subtyping ct c c
  STrans : ∀ {ct c d e}
         → subtyping ct c d
         → subtyping ct d e
           -------------
         → subtyping ct c e
  SStep : ∀ {ct c d cd f k m}
        → InCT ct c cd
        → cd ≡ Class c d f k m
          --------------------
        → subtyping ct c d

-- Checking subtyping for a list of types

data subtypingL where
  subtypingl_base : ∀ {ct}
             → subtypingL ct [] []
  subtypingl_step : ∀ {ct e e' l l'}
            → subtypingL ct l l'
            → subtyping ct e e'
            → subtypingL ct (e ∷ l) (e' ∷ l')

-- Field lookup

data fields : CT → TypeName → List (TypeName × IdName) → Set where
  FObject : ∀ {ct}
         → fields ct "Object" []
  FClass : ∀ {c cd ct}
         → InCT ct c cd
         → fields ct c (ClassDef.fields cd)

-- Get a field type from a field list

data InFields : List (TypeName × IdName) → IdName → TypeName → Set where
  FZ : ∀ {tflds f t}
       -----------
     → InFields ((t , f) ∷ tflds) f t
  FS : ∀ {flds f t f' t'}
     → f ≢ f'
     → InFields flds f t
       ------------------
     → InFields ((t' , f') ∷ flds) f t

-- Get a method from a method list

data InMethods : List MethodDef → IdName → MethodDef → Set where
  MZ : ∀ {m mn meths r p e}
     → m ≡ Method r mn p e
       -----------
     → InMethods (m ∷ meths) mn m
  MS : ∀ {m mn m' meths}
     → m ≢ m'
     → InMethods meths mn m
       ------------------
     → InMethods (m' ∷ meths) mn m

-- Method type lookup

data mtype : CT → TypeName → IdName → (List TypeName × TypeName) → Set where
  MTClass : ∀ {ct c m md ml cn ce f k}
          → InCT ct c (Class cn ce f k ml)
          → InMethods ml m md
          → mtype ct c m (Σ.proj₁ (unzip (MethodDef.params md)) , MethodDef.returns md)
  MTSuper : ∀ {ct c cn ce f k m ml mt}
          → InCT ct c (Class cn ce f k ml)
          -- Method 'm' is not in class 'c' ?
          → mtype ct ce m mt
            ---------------------------
          → mtype ct c m mt


-- Method body lookup

data mbody : CT → TypeName → IdName → (List IdName × Expr) → Set where
  MBClass : ∀ {ct c m md ml cn ce f k}
          → InCT ct c (Class cn ce f k ml)
          → InMethods ml m md
          → mbody ct c m (Σ.proj₂ (unzip (MethodDef.params md)) , MethodDef.expr md)
  MBSuper : ∀ {ct c cn ce f k m ml mb}
          → InCT ct c (Class cn ce f k ml)
          -- Method 'm' is not in class 'c' ?
          → mbody ct ce m mb
            ---------------------------
          → mbody ct c m mb

--------------------------------------------------------------------------------
-------------------------- EVALUATION DEFINITIONS ------------------------------
--------------------------------------------------------------------------------

-- Definitions for mutual recursion

subst : List IdName → List Expr → Expr → Expr
substL : List IdName → List Expr → List Expr → List Expr

-- Substitution of a variable from lists of names and expressions

substV : List IdName → List Expr → IdName → Expr
substV [] _ x = (Var x)
substV _ [] x = (Var x)
substV (x ∷ xs) (y ∷ ys) v with x ≟ v
... | yes _ = y
... | no _ = substV xs ys v

-- Substitution

subst p v (Var x) = substV p v x
subst p v (Field e f) = Field (subst p v e) f
subst p v (Invk e m ap) = Invk (subst p v e) m (substL p v ap)
subst p v (New c ap) = New c (substL p v ap)

-- Substitution on a list

substL p v [] = []
substL p v (x ∷ xs) = subst p v x ∷ substL p v xs

-- Definitions for mutual recursion

data step : CT → Expr → Expr → Set
data StepL : CT → List Expr → List Expr → Set

-- Get the expression according to its position in the constructor parameters

data rfield : List IdName → List Expr → IdName → Expr → Set where
  rfield_base : ∀ {e es n ns}
              → rfield (n ∷ ns) (e ∷ es) n e
  rfield_step : ∀ {e e' es n n' ns}
              → rfield ns es n e
              → rfield (n' ∷ ns) (e' ∷ es) n e

-- Evaluation

data step where
  RC_Field : ∀ {ct e e' f}
           → step ct e e'
             --------------
           → step ct (Field e f) (Field e' f)
  R_Field : ∀ {ct c flds f fi p}
          → fields ct c flds
          → rfield (Σ.proj₂ (unzip flds)) p f fi
            -----------------
          → step ct (Field (New c p) f) fi
  R_Invk : ∀ {ct c e m pc pm pn}
         → mbody ct c m (pn , e)
           ----------------------
         → step ct (Invk (New c pc) m pm) (subst ("this" ∷ pn) ((New c pc) ∷ pm) e)
  RC_Invk_Recv : ∀ {ct e e' m pm}
               → step ct e e'
                 -----------------
               → step ct (Invk e m pm) (Invk e' m pm)
  RC_Invk_Arg : ∀ {ct e m pm pm'}
              → StepL ct pm pm'
                ----------------
              → step ct (Invk e m pm) (Invk e m pm')
  RC_New_Arg : ∀ {ct c pc pc'}
             → StepL ct pc pc'
               ----------------
             → step ct (New c pc) (New c pc')

-- Steping each element of a list

data StepL where
  stepl_base : ∀ {ct}
             → StepL ct [] []
  stepl_step : ∀ {ct e e' l l'}
            → StepL ct l l'
            → step ct e e'
            → StepL ct (e ∷ l) (e' ∷ l')

--------------------------------------------------------------------------------
--------------------------- TYPING DEFINITIONS ---------------------------------
--------------------------------------------------------------------------------

-- Syntax of Types

data Type : Set where
  TypeClass : TypeName → Type

-- Gamma context

data Context : Set where
  CEmpty : Context
  CGamma : Context → IdName → Type → Context

-- Context lookup

data InContext : Context → IdName → Type → Set where
  CZ : ∀ {Gamma x A}
      --------------------
    → InContext (CGamma Gamma x A) x A
  CS : ∀ {Gamma x y A B}
    → x ≢ y
    → InContext Gamma x A
      --------------------
    → InContext (CGamma Gamma y B) x A

-- Definitions for mutual recursion

data has_type : CT → Context → Expr → Type → Set
data has_typeL : CT → Context → List Expr → List Type → Set

-- Typing

data has_type where
  TVar : ∀ {ct Gamma x t}
       → InContext Gamma x t
         -----------------
       → has_type ct Gamma (Var x) t
  TField : ∀ {ct Gamma e c f t flds}
         → has_type ct Gamma e (TypeClass c)
         → fields ct c flds
         → InFields flds f t
           ------------------------
         → has_type ct Gamma (Field e f) (TypeClass t)
  TInvk : ∀ {ct Gamma e c m mt pm pm'}
        → has_type ct Gamma e (TypeClass c)
        → mtype ct c m mt
        → has_typeL ct Gamma pm pm'
        → subtypingL ct (Data.List.map (λ { (TypeClass t) → t}) pm') (Σ.proj₁ mt)
          -----------------------------
        → has_type ct Gamma (Invk e m pm) (TypeClass (Σ.proj₂ mt))
  TNew : ∀ {ct Gamma c flds pc pc'}
       → fields ct c flds
       → has_typeL ct Gamma pc pc'
       → subtypingL ct (Data.List.map (λ { (TypeClass t) → t }) pc') (Σ.proj₁ (unzip flds))
         ----------------------------
       → has_type ct Gamma (New c pc) (TypeClass c)

-- Typing a list

data has_typeL where
  has_typel_base : ∀ {ct gamma}
             → has_typeL ct gamma [] []
  has_typel_step : ∀ {ct gamma e e' l l'}
            → has_typeL ct gamma l l'
            → has_type ct gamma e e'
            → has_typeL ct gamma (e ∷ l) (e' ∷ l')

