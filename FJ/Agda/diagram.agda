open import Data.Nat
open import Data.Fin
open import Data.List using (List ; map; unzip; []; _∷_; length)
open import Data.List.All using (All; []; _∷_)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Any using (here ; there)
open import Relation.Binary.PropositionalEquality using (refl; _≡_; sym; cong; subst)

import etfj
import itfj renaming (Ctx to ICtx)

module diagram where

-- Object is represented by 0
module FJ = etfj 0

open FJ 
open FJ.ClassTable

-- We assume a CT

postulate
  Δ : CT

-- We have (length Δ) classes for our intrinsically-typed FJ

module IFJ = itfj (length Δ)

open IFJ
open IFJ.ClassTable

-- We assume a function from Ty to Name and vice-versa

postulate 
  Ty⇒Name : Ty → Name
  Name⇒Ty : Name → Ty

Meth⇒MSig : Meth → MSig
Meth⇒MSig MD = mkSig (Name⇒Ty (Meth.ret MD)) (map (λ p → Name⇒Ty (proj₂ p)) (Meth.params MD))

-- Elaborating context

elabCtx : Ctx → ICtx
elabCtx Γ = map (λ v → Name⇒Ty (proj₂ v)) Γ

postulate
  elabCT : (ct : CT) → Vec CSig (length ct)

open FJ.Syntax
open FJ.Typing Δ
open FJ.Auxiliary Δ
open IFJ.Syntax (elabCT Δ) renaming (Expr to IExpr)
open IFJ.Auxiliary (elabCT Δ) renaming (fields to ifields)

-- Assuming some valid equalities

postulate 
  eq-fields : ∀ {c flds} → fields c flds
    → map Name⇒Ty (proj₂ (unzip flds)) ≡ ifields (Name⇒Ty c)
  eq-fields₂ : ∀ {c flds} → fields c flds
    → ifields (Name⇒Ty c) ≡ map (λ f → Name⇒Ty (proj₂ f)) flds
  eq-meth : ∀ {C m MD meths} → method C m MD → meths ∋ m ∶ MD → signatures (Name⇒Ty C) ≡ map (λ m' → Meth⇒MSig (proj₂ m')) meths
  eq-mparams : ∀ {C m MD} → method C m MD
    → map Name⇒Ty (proj₂ (unzip (Meth.params MD))) ≡ map (λ p → Name⇒Ty (proj₂ p)) (Meth.params MD)

--  eq-methods : ∀ {C m MD} → method C m MD → signatures (Name⇒Ty C) ≡ 

-- Elaborating 'Var' index

elabVar : ∀ {Γ x c} → Γ ∋ x ∶ c → Name⇒Ty c ∈ elabCtx Γ
elabVar here = here refl
elabVar (there wtv) = there (elabVar wtv)

-- Elaborating 'Field' index

elabFieldList : ∀ {f τ} → (flds : List (Name × Name)) → flds ∋ f ∶ τ
             → Name⇒Ty τ ∈ map (λ f → Name⇒Ty (proj₂ f)) flds
elabFieldList .((_ , _) ∷ _) here = here refl
elabFieldList (f ∷ fs) (there wtf) = there (elabFieldList fs wtf)

elabField : ∀ {flds f τ C} → fields C flds → flds ∋ f ∶ τ
          → Name⇒Ty τ ∈ ifields (Name⇒Ty C)
elabField {flds} fls wtf rewrite eq-fields₂ fls = elabFieldList flds wtf

-- Elaborating 'Method' index (I'll need to think about it)

elabMethList : ∀ {m MD} → (meths : List (Name × Meth)) → meths ∋ m ∶ MD → Meth⇒MSig MD ∈ map (λ m' → Meth⇒MSig (proj₂ m') ) meths
elabMethList .((_ , _) ∷ _) here = here refl
elabMethList (m ∷ ms) (there wtm) = there (elabMethList ms wtm)

elabMeth : ∀ {C m MD} → method C m MD
        → Meth⇒MSig MD ∈ signatures (Name⇒Ty C)
elabMeth m@(this {cd = record { cname = cname ; flds = _ ; meths = meths }} wtc wtm) rewrite eq-meth m wtm = elabMethList meths wtm

-- Mutually recursive definitions

elabExpr : ∀ {Γ e τ} → Γ ⊢ e ∶ τ → IExpr (elabCtx Γ) (Name⇒Ty τ)
elabExprs : ∀ {Γ es τs} → Γ ⊧ es ∶ τs → All (IExpr (elabCtx Γ)) (map Name⇒Ty τs)

elabExpr (T-Var x) = Var (elabVar x)
elabExpr (T-Field wte fls wtf) = Field (elabExpr wte) (elabField fls wtf)
elabExpr (T-Invk {Γ = Γ} wte wtm wtmp) = Invk (elabExpr wte) (elabMeth wtm) (subst (All (IExpr (elabCtx Γ))) (eq-mparams wtm) (elabExprs wtmp))
elabExpr (T-New {Γ = Γ} {C = C} flds wtcp) = New (Name⇒Ty C) (subst (All (IExpr (elabCtx Γ))) (eq-fields flds) (elabExprs wtcp))

elabExprs here = []
elabExprs (there wte wtl) = elabExpr wte ∷ elabExprs wtl
