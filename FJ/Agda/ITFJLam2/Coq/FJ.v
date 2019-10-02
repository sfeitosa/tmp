
Require Import
        Arith_base
        List
        Utf8.

Import ListNotations.

From Equations Require Import Equations.

(** finite types and vector definitons *)

Section BASICS.
  Inductive fin : nat -> Type :=
  | FZero : forall n, fin (S n)
  | FSucc : forall n, fin n -> fin (S n).

  Derive Signature for fin.

  Arguments FZero {n}.
  Arguments FSucc {n}.

  Inductive vec (A : Type) : nat -> Type :=
  | VNil  : vec A 0
  | VCons : forall n, A -> vec A n -> vec A (S n).

  Derive Signature for vec.

  Arguments VNil {_}.
  Arguments VCons {_}{n}.

  Equations vlookup {A}{n}(i : fin n) (v : vec A n) : A :=
    vlookup  FZero (VCons x _) := x ;
    vlookup  (FSucc ix) (VCons _ xs) := vlookup ix xs.

  Inductive In {A : Type}(x : A) : list A -> Type :=
  | IHere  : forall xs, In x (x :: xs)
  | IThere : forall ys y, In x ys -> In x (y :: ys).

  Derive Signature for In.

  (** sadly Forall from Coq library uses P : A -> Prop... *)

  Inductive forallT {A : Type}(P : A -> Type) : list A -> Type :=
  | FTNil  : forallT P []
  | FTCons : forall x xs, P x -> forallT P xs -> forallT P (x :: xs).


  Derive Signature for forallT.

  Equations forallT_lookup
             {A : Type}
             {P : A -> Type}
             {x : A}
             {xs : list A} : In x xs -> forallT P xs -> P x :=
    forallT_lookup IHere (FTCons _ p _) := p ;
    forallT_lookup (IThere _ ix) (FTCons _ _ ps) := forallT_lookup ix ps.
   

  Inductive vforall {A : Type}(P : A -> Type) : forall n, vec A n -> Type :=
  | VFNil  : vforall P _ VNil
  | VFCons : forall n x xs,
      P x -> vforall P n xs -> vforall P (S n) (VCons x xs).

  Derive Signature for vforall.

  Arguments vforall {_}(P){n}.

  Equations(noind) vforall_lookup
            {n}
            {A : Type}
            {P : A -> Type}
            {xs : vec A n}
            (idx : fin n) :
            vforall P xs -> P (vlookup idx xs) :=
    vforall_lookup FZero (VFCons _ _ pf _) := pf ;
    vforall_lookup (FSucc ix) (VFCons _ _ _ ps) := vforall_lookup ix ps.
End BASICS.

(** starting the real thing. Type definition *)

Definition ty := fin.    

(** signatures *)

Definition msig n := ((list (ty n)) * (ty n))%type.

Record csig (n : nat) : Type :=
  MkSig {
    Fields : list (ty n)
  ; Signs  : list (msig n)
  }.

Arguments Fields {n}.
Arguments Signs {n}.

Definition ctsig n := vec (csig n) n.

Definition ctx n := list (ty n).


Inductive exp {n : nat}(cts : ctsig n)(G : ctx n) : ty n -> Set :=
| Var   : forall v, In v G -> exp cts G v
| Field : forall c f, exp cts G c -> In f (Fields (vlookup c cts)) -> exp cts G f
| Invk  : forall c m1 m2, exp cts G c ->
                 In (m1,m2) (Signs (vlookup c cts)) ->
                 forallT (exp cts G) m1  ->
                 exp cts G m2
| New   : forall c, forallT (exp cts G) (Fields (vlookup c cts)) -> exp cts G c. 

Inductive val {n : nat}(cts : ctsig n) : ty n -> Set :=
| VNew : forall c, forallT (val cts) (Fields (vlookup c cts)) -> val cts c.

Equations env {n} : ctsig n -> ctx n -> Type :=
  env cts G := forallT (val cts) G.

Equations cimp {n} : ctsig n -> csig n -> Type :=
  cimp cts sig := forallT (fun s => exp cts (fst s) (snd s)) (Signs sig).

Equations ctimp {n} : ctsig n -> Type :=
  ctimp cts := vforall (cimp cts) n cts.

Equations get_method : forall {n}{cts : ctsig n}{cs : csig n}{m1 m2},
    cimp cts cs -> In (m1,m2) (Signs cs) -> exp cts m1 m2 :=
  get_method imp i := forallT_lookup i imp.

Equations get_class
  : forall {n}{cts : ctsig n}, ctimp cts -> forall (c : ty n), cimp cts (vlookup c cts) :=
  get_class cti i := vforall_lookup i cti.

Equations (noind) eval
  : forall {n}{c : ty n}{cts : ctsig n}{G : ctx n}(fuel : nat),
    ctimp cts -> env cts G -> exp cts G c -> option (val cts c) :=
  eval 0 _ _ _ := None ;
  eval (S _) ctimp G (Var _ _ _ idx)
      := Some (forallT_lookup idx G) ;
  eval (S fuel) ctimp G (New _ _ c cp) with eval_list fuel ctimp G cp => {
         | None => None ;
         | Some vp => Some (VNew _ _ vp) 
       } ;        
  eval (S fuel) ctimp G (Field _ _ _ _ e1 f) with eval fuel ctimp G e1 => {
         | None => None ;
         | Some (VNew _ _ fts) => Some (forallT_lookup f fts) 
  } ; 
  eval (S fuel) ctimp G (Invk _ _ e m mps) with eval_list fuel ctimp G mps => {
         | None => None ;
         | Some vmp with eval fuel ctimp G e => {
             | None => None ; 
             | Some (VNew _ c fts) =>
               eval fuel ctimp vmp (get_method (get_class ctimp c) m)
         } 
  }
  where
  eval_list {n : nat}{cs : list (ty n)}{cts : ctsig n}{G : ctx n}
            (fuel : nat)(cti : ctimp cts)(eG : env cts G) : 
    forallT (exp cts G) cs -> option (forallT (val cts) cs) := 
    eval_list 0 _ _ _ := None ; 
    eval_list n cit G (FTNil _) := Some (FTNil _) ;
    eval_list (S fuel) cti G (FTCons _ x xs) with eval fuel cti G x => {
                                   | None => None ;
                                   | Some v with eval_list fuel cti G xs => {
                                     | None => None ;
                                     | Some vs => Some (FTCons _ _ _ v vs)
                                     } 
    }.