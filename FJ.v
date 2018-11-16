(* 
  * Coq version for FJ semantics 
  * Author: Samuel da Silva Feitosa
  * Started on: November 2018
*)

Require Import
        List
        FMapAVL
        FMapFacts
        OrderedTypeEx. 

(* Syntactic definitions *)
Definition ClassName := nat.
Definition VarName := nat.
Definition FieldName := nat.
Definition MethName := nat.

Inductive expr : Type := 
  | Var : VarName -> expr (* Variables *)
  | Field : expr -> FieldName -> expr (* Field access *)
  | Invk : expr -> MethName -> list expr -> expr (* Method invocation *)
  | New : ClassName -> list expr -> expr (* Object instatiation *)
  .

Inductive constr : Type :=
| Constr : ClassName -> list (ClassName * VarName)
           -> list VarName -> list (VarName * VarName) -> constr.

Inductive method : Type :=
| Method : ClassName -> MethName -> list (ClassName * VarName)
           -> expr -> method.

Inductive class : Type :=
| Class : ClassName -> ClassName -> list (ClassName * FieldName)
          -> constr -> list method -> class.

(* Examples *)

(* Definition Object := 0. *)
Definition A := 1.
Definition x := 1.
Definition y := 2.

Definition classA := Class A 0 (0, x)::nil nil nil.

(* Definition of values *)
Inductive Value : expr -> Prop :=
  | V_New : forall c pc, Forall Value pc -> Value (New c pc).

(* Class table definition *) 

Module M := FMapAVL.Make(Nat_as_OT).
Definition ClassTable: Type := M.t class.
Variable CT : ClassTable.

Parameter Object : ClassName.
Parameter this : VarName.

(* Auxiliary definitions *)

(* fields as a function *)
Definition fields' (c: ClassName) (ct: ClassTable) : 
	     list (ClassName * FieldName) :=
  match c with
  | 0 => nil (* Object *)
  | _ => match (M.find c CT) with
         | None => nil
	 | Some (Class _ _ f _ _) => f
         end.
  end.

Eval compute in fields' 1 (M.add A classA (M.empty class)).

(* @TODO: Ideia para tratar metodos --> Ver como fazer isso.

InMethods : MethodName -> [Method] -> Type
  InHead : forall m, ... InMethods m (Method ... m ...)
  InTail : forall n m : InMethod n m -> InMethods m (m:ms) ???

*)

(* fields as a relation *)
Inductive fields : ClassName -> list (ClassName * FieldName) -> Prop := 
  | F_Object : fields Object nil
  | F_Class : forall C CD D fc fd k m,
	  M.MapsTo C (Class C D fc k m) CT ->
	  fields D fd ->
	  fields C (fd ++ fc).

Hint Constructors fields.

Example fields_ex1 : (fields Object nil).
Proof. auto. Qed.

(* @TODO: mtype as a function *)
Definition mtype (m: MethName) (c: ClassName) :
  list (list ClassName * ClassName) :=
  match c with
  | Object => nil
  end.

(* mtype as a relation *)
Inductive mtype : MethName -> ClassName -> (list ClassName, ClassName) -> Prop := 
  | MT_class : forall C CD D f k m ml r mn mp mb,
	M.MapsTo C (Class C D f k ml) CT -> 
	(* how to obtain method from method list? *) ->
        MD = Method r mn mp mb -> 
	mtype m C (mp, r).
  | MT_base : forall C CD D f k m ml mt,
	M.MapsTo C (Class C D f k ml) CT ->
	(* check if m is not in ml *) ->
	mtype m D mt -> 
	mtype m C mt.

(* @TODO: mbody as a function *)
Definition mbody (m: MethName) (c: ClassName) :
  list (list VarName * expr) :=
  match c with
  | Object => nil
  end.

(* mbody as a relation *) 
Inductive mbody : MethName -> ClassName -> (list VarName, expr) -> Prop := 
  | MT_class : forall C CD D f k m ml r mn mp mb,
	M.MapsTo C (Class C D f k ml) CT ->
	(* how to obtain method from method list? *) -> 
	MD = Method r mn mp mb -> 
	mbody m C (mp, mb).
  | MT_base : forall C CD D f k m ml,
	M.MapsTo C (Class C D f k ml) CT -> 
	(* check if m is not in ml *) -> 
	mbody m D mb -> 
	mbody m C mb.
	  
(* Semantic definitions *)

Reserved Notation " t '==>' t' " (at level 40).

(* @TODO *)
Fixpoint subst (p: list VarName) (v: list expr) (b: expr) : expr
  match b with
  | Var x => (* @TODO *)
  | Field e f => let e' = subst p v e
                   in Field e' f
  | Invk e m pm => let pm' = map (subst p v) pm in 
                   let e' = subst p v e in 
		     Invk e' m pm'
  | New c pc => let pc' = map (subst p v) pc in 
                  New c pc'
  end.

(* Daqui para baixo não pensei direito como fazer ainda... 
 * Quero acertar a primeira parte primeiro.
 *) 

Inductive step : Expr -> Expr -> Prop := 
  | R_Field : forall c e fi ei xl,
      fields c = ??? (* @TODO *)
      New c e fi ==> ei
  | RC_Field : forall e0 e0',
      e0 ==> e0' -> 
      Field e0 f -> Field e0' f
  | R_Invk : forall c m p p' e0
      mbody m c (xl, e0) ->
      New c p m p' ==> subst xl p' e0 (* @TODO: add this *)
  | RC_InvkRecv : forall e0 e0' m p,
      e0 ==> e0' -> 
      Invk e0 m p ==> Invk e0' m p
  | RC_InvkArg : forall e0 m p p',
      p ==> p' ->
      Invk e0 m p ==> Invk e0 m p'
  | RC_NewArg : forall c p p',
      p ==> p' ->
      New c p ==> New c p'
  where " t '==>' t' " := (step t t').


(* Typing definitions *)

Definition context := partial_map type.

Reserved Notation "Gamma '|-' t '\in' T" (at level 40).

Inductive has_type : context -> expr -> type -> Prop :=
  | T_Var : forall Gamma x T,
              Gamma x = Some T -> 
	      Gamma |- Var x \in T
  | T_Field: forall Gamma e0 fi C C0 Ci,
	       Gamma |- e0 \in C0 -> 
	       fields C0 = (* @TODO *) ->
	       Gamma |- Field e0 fi \in Ci
  | T_Invk: forall Gamma e0 m pm C C0 ->
	      Gamma |- e0 \in C0 ->
	      mtype m C0 = (* @TODO *) ->
	      Gamma |- (* @TODO for params *) ->
	      (* @TODO subtyping *) ->
	      Gamma |- Invk e0 m pm \in C
  | T_New: forall Gamma c pc C,
	     fields c = (* @TODO *) ->
	     Gamma |- (* @TODO for params *) ->
	     (* @TODO subtyping *) ->
	     Gamma |- New c pc \in C
  where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

Hint constructor has_type.

