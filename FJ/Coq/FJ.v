Require Import
        List
        String.

Open Scope string_scope.

Definition TypeName := string.
Definition IdName := string.

(* ============================================================== *)
(*                    Syntactic definitions                       *)
(* ============================================================== *)

(* Expressions *)

Inductive Expr : Type := 
  | Var : IdName -> Expr (* Variables *)
  | Field : Expr -> IdName -> Expr (* Field access *)
  | Invk : Expr -> IdName -> list Expr -> Expr (* Method inv *)
  | New : TypeName -> list Expr -> Expr (* Object instatiation *)
  .

(* Constructor *)
  
Record ConstrDef : Type := Constr {
  kclass : IdName;
  kparams : list (TypeName * IdName);
  ksuper : list IdName;
  kinit : list (IdName * IdName);
}.

(* Method definition *)
  
Record MethodDef : Type := Method {
  mreturns : TypeName;
  mname : IdName;
  mparams : list (TypeName * IdName);
  mexpr : Expr;                                           
}.

(* Class definition *)

Record ClassDef : Type := Class {
  cname : TypeName;
  cextends : TypeName;
  cfields : list (TypeName * IdName);
  cconstr : ConstrDef;
  cmethods : list MethodDef;                              
}.

(* Value definition *)

Inductive Value : Expr -> Prop :=
  | V_New : forall c pc, Forall Value pc -> Value (New c pc).

(* Class table definition *)

Inductive CT : Type := 
  | CTEmpty : CT
  | CTContent : CT -> IdName -> ClassDef -> CT
  .

(* Class table lookup *)
  
Inductive InCT : CT -> IdName -> ClassDef -> Prop :=
  | CTBase : forall CT CD c,
               InCT (CTContent CT c CD) c CD
  | CTStep : forall CT CD CD' c c',
               InCT CT c CD
            -> InCT (CTContent CT c' CD') c CD
  .
  
(* ============================================================== *)
(*                    Auxiliary definitions                       *)
(* ============================================================== *)

(* Subtyping *)
  
Inductive subtyping : CT -> TypeName -> TypeName -> Prop :=
  | SRefl : forall CT C,
         subtyping CT C C
  | STrans : forall CT C D E,
         subtyping CT C D
      -> subtyping CT D E
      -> subtyping CT C E
  | SStep : forall CT C CD,
         InCT CT C CD
      -> subtyping CT C (cextends CD)
  .

(* Get the field type from a field list *)

Inductive InFields : list (TypeName * IdName) -> IdName -> TypeName -> Prop :=
  | IFBase : forall f t flds,
        InFields ((t , f) :: flds) f t
  | IFStep : forall f f' t t' flds,
        InFields flds f t   
     -> InFields ((t' , f') :: flds) f t
  .
  
(* Field lookup *)
  
Inductive fields : CT -> TypeName -> list (TypeName * IdName) -> Prop :=
  | FObject : forall CT,
        fields CT "Object" nil
  | FClass : forall CT C CD,
        InCT CT C CD
     -> fields CT C (cfields CD)
  .

(* Get a method from a method list by its name *)
  
Inductive InMethods : list MethodDef -> IdName -> MethodDef -> Prop :=
  | IMBase : forall m mn meths,
        mname m = mn   
     -> InMethods (m :: meths) mn m
  | IMStep : forall m mn meths m',
        InMethods meths mn m
     -> InMethods (m' :: meths) mn m           
  .  

(* Method type lookup *)

Inductive mtype : CT -> TypeName -> IdName -> (list TypeName * TypeName) -> Prop :=
  | MTClass : forall CT C m CD MD,
        InCT CT C CD
     -> InMethods (cmethods CD) m MD
     -> mtype CT C m (fst (split (mparams MD)) , mreturns MD)
  | MTSuper : forall CT C m CD MT,
        InCT CT C CD
        (* Method 'm' is not in class 'C'? *)   
     -> mtype CT (cextends CD) m MT
     -> mtype CT C m MT
  .

(* Method body lookup *)
  
Inductive mbody : CT -> TypeName -> IdName -> (list IdName * Expr) -> Prop :=
  | MBClass : forall CT C m CD MD,
        InCT CT C CD
     -> InMethods (cmethods CD) m MD      
     -> mbody CT C m (snd (split (mparams MD)) , mexpr MD)
  | MBSuper : forall CT C m CD MT,
        InCT CT C CD
        (* Method 'm' is not in class 'C'? *)
     -> mbody CT (cextends CD) m MT
     -> mbody CT C m MT
  .

              
(* ============================================================== *)
(*                    Evaluation definitions                      *)
(* ============================================================== *)

(* Substituting a variable from a list of parameters *)
  
Fixpoint substV (p: list IdName) (v: list Expr) (n: IdName) : Expr :=
  match p, v with
  | nil , _ => (Var n)
  | _ , nil => (Var n)
  | (x :: xs) , (y :: ys) => if string_dec x n then
                               y
                             else
                               substV xs ys n
  end.
  
(* Substitution *)
  
Fixpoint subst (p: list IdName) (v: list Expr) (e: Expr) : Expr :=
  match e with
  | (Var x) => substV p v x
  | (Field e f) => Field (subst p v e) f
  | (Invk e m ap) => Invk (subst p v e) m (map (subst p v) ap)
  | (New c ap) => New c (map (subst p v) ap) (* recursive call *)
  end.

(* Get the expression according to its position in the constructor parameters *)

Inductive PickField : list IdName -> list Expr -> IdName -> Expr -> Prop :=
  | PFBase : forall e es n ns,
        PickField (n :: ns) (e :: es) n e
  | PFStep : forall e e' es n n' ns,
        PickField ns es n e    
     -> PickField (n' :: ns) (e' :: es) n e
  .

Check Forall2.

(* Evaluation *)
  
Inductive step : CT -> Expr -> Expr -> Prop :=
  | RCField : forall CT e e' f,
        step CT e e'  
     -> step CT (Field e f) (Field e' f)
  | RField : forall CT C f flds ap fi,
        fields CT C flds
     -> PickField (fst (split flds)) ap f fi
     -> step CT (Field (New C ap) f) fi
  | RInvk : forall CT C e m pc pm pn,
        mbody CT C m (pn, e)
     -> step CT (Invk (New C pc) m pm) (subst ("this" :: pn) ((New C pc) :: pm) e)
  | RCInvkRecv : forall CT e e' m pm,
        step CT e e'
     -> step CT (Invk e m pm) (Invk e' m pm)
  | RCInvkArg : forall CT e m pm pm',
        Forall2 (step CT) pm pm'
        -> step CT (Invk e m pm) (Invk e m pm')
  | RCNewArg : forall CT C pc pc',
        Forall2 (step CT) pc pc'
     -> step CT (New C pc) (New C pc')
  .

(* ============================================================== *)
(*                      Typing definitions                        *)
(* ============================================================== *)

(* Syntax of types *)

Record FJType : Type := TypeClass {
  tname : TypeName;
}.

(* Gamma context *)
  
Inductive Context : Type :=
  | CEmpty : Context
  | CGamma : Context -> IdName -> FJType -> Context
  .

(* Context lookup *)

Inductive InContext : Context -> IdName -> FJType -> Prop :=
  | ICBase : forall G x C,
        InContext (CGamma G x C) x C
  | ICStep : forall G x y C D,
        InContext G x C
     -> InContext (CGamma G y D) x C
  .

(* Typing *)

Inductive infer : CT -> Context -> Expr -> FJType -> Prop :=
  | TVar : forall CT G x C,
        InContext G x C
     -> infer CT G (Var x) C
  | TField : forall CT G C Ci e f flds,
        infer CT G e (TypeClass C)
     -> fields CT C flds
     -> InFields flds f Ci
     -> infer CT G (Field e f) (TypeClass Ci)
  | TInvk : forall CT G C e m mt pm pm',
        infer CT G e (TypeClass C)
     -> mtype CT C m mt
     -> Forall2 (infer CT G) pm pm'
     -> Forall2 (subtyping CT) (map (fun t => tname t) pm') (fst mt)
     -> infer CT G (Invk e m pm) (TypeClass (snd mt))
  | TNew : forall CT G C flds pc pc',
        fields CT C flds
     -> Forall2 (infer CT G) pc pc'
     -> Forall2 (subtyping CT) (map (fun t => tname t) pc') (fst (split flds))
     -> infer CT G (New C pc) (TypeClass C)
  .
