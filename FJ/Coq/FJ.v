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

Definition CT := list (TypeName * ClassDef).

(* Class table lookup *)
  
Inductive InCT : CT -> IdName -> ClassDef -> Prop :=
  | CTBase : forall C CD L,
        InCT ((C, CD) :: L) C CD
  | CTStep : forall C C' CD CD' L,
        InCT L C CD
     -> InCT ((C', CD') :: L) C CD
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
  | FClass : forall CT C CD fd,
        InCT CT C CD
     -> fields CT (cextends CD) fd
     -> fields CT C (fd ++ (cfields CD))
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

(* Check if a method 'm' is in a method list *)

Inductive NotInMethods : list MethodDef -> IdName -> Prop :=
  | NIMBase : forall mn,
        NotInMethods nil mn
  | NIMStep : forall m mn meths,
        mname m <> mn
     -> NotInMethods meths mn
     -> NotInMethods (m :: meths) mn
  .
  

(* Method type lookup *)

Inductive mtype : CT -> TypeName -> IdName -> (list TypeName * TypeName) -> Prop :=
  | MTClass : forall CT C m CD MD,
        InCT CT C CD
     -> InMethods (cmethods CD) m MD
     -> mtype CT C m (fst (split (mparams MD)) , mreturns MD)
  | MTSuper : forall CT C m CD MT,
        InCT CT C CD
     -> NotInMethods (cmethods CD) m
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
     -> NotInMethods (cmethods CD) m
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

Definition Context := (list (IdName * FJType)).

(* Context lookup *)

Inductive InContext : Context -> IdName -> FJType -> Prop :=
  | ICBase : forall G x C,
        InContext ((x, C) :: G) x C  
  | ICStep : forall G x y C D,
        InContext G x C
     -> InContext ((y, D) :: G) x C
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
  
(* Method typing *)
  
Inductive MethodOk : CT -> ClassDef -> MethodDef -> Prop :=
  | MOkClass : forall CT CD DD MD E G Gf Gs,
          Gf = snd (split (mparams MD))
       -> Gs = map (fun x => TypeClass x) (fst (split (mparams MD)))
       -> G = ("this", TypeClass (cname CD)) :: (combine Gf Gs)
       -> infer CT G (mexpr MD) E
       -> subtyping CT (tname E) (mreturns MD)
       -> InCT CT (cextends CD) DD
       -> NotInMethods (cmethods DD) (mname MD)
       -> MethodOk CT CD MD
  | MOkSuper : forall CT CD MD E G Gf Gs m,
          Gf = snd (split (mparams MD))
       -> Gs = map (fun x => TypeClass x) (fst (split (mparams MD)))
       -> G = ("this", TypeClass (cname CD)) :: (combine Gf Gs)
       -> infer CT G (mexpr MD) E
       -> subtyping CT (tname E) (mreturns MD)
       -> mtype CT (cextends CD) m (fst (split (mparams MD)), mreturns MD)
       -> MethodOk CT CD MD
  .
  
(* Class typing *)
  
Inductive ClassOk : CT -> ClassDef -> Prop := 
  | COk : forall CT CD fD K,
        fields CT (cextends CD) fD 
     -> kparams K = app fD (cfields CD)
     -> ksuper K = snd (split fD)
     -> kinit K = combine (snd (split (cfields CD))) (snd (split (cfields CD)))
     -> Forall (MethodOk CT CD) (cmethods CD)
     -> ClassOk CT CD
  .

