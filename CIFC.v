Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.

Require Import Label.



(* class name *)
Inductive cn : Type :=
  | className : string -> cn.

(* identifiers *)
Inductive id : Type :=
  | Id : string -> id.

(* comparison of identifiers *)
Definition beq_id x y :=
  match x,y with
    | Id n1, Id n2 => if string_dec n1 n2 then true else false
  end.

Inductive field : Type :=
  | fd : cn -> id  -> field.

(* expression *)
Inductive exp : Type :=
  | Tvar : id -> exp
  | null : exp
  | FieldAccess : exp -> id -> exp
  | MethodCall : exp -> id -> exp -> exp
  | NewExp : cn -> exp
  | this : exp
(* label expressions *)  
  | l : Label -> exp
  | labelData : exp -> exp -> exp
  | unlabel : exp -> exp
  | lablOf : exp -> exp
  | unlabelOpaque : exp -> exp
  | opaqueCall : exp -> id -> exp -> exp.

Inductive stmt : Type :=
  | Skip : stmt
  | Assignment : id -> exp -> stmt
  | FieldWrite : exp -> id -> exp -> stmt
  | If : id -> id -> stmt -> stmt -> stmt
  | methodCallStmt : exp -> id -> exp -> stmt
  | Sequence : stmt -> stmt -> stmt.


Inductive methodDel : Type :=
  | method_def : cn -> id -> cn -> stmt -> id -> methodDel.

Inductive oid : Type := 
  | OID : nat -> oid.

Inductive tm : Type :=
  | Exp : exp -> tm
  | Stmt : stmt -> tm
  | ObjId: oid -> tm
  | NPE : tm.


Inductive value : tm -> Prop :=
  (* contants are values or normal form *)
  | v_oid :
      forall o, value (ObjId o)
  | v_none : 
      value (Stmt Skip)
  | v_null :
      value (Exp null)
  | v_label :
      forall lb, value (Exp (l lb))
  | v_exception :
      value NPE.


Notation "( x , y )" := (pair x y).

(* stack frame *)
Definition stack_frame : Type := id -> (option tm).

Inductive labeled_stack_frame : Type := 
  | Labeled_frame : Label -> stack_frame -> labeled_stack_frame.

Definition get_stack_label (lsf : labeled_stack_frame) : Label :=
  match lsf with 
    | Labeled_frame lb sf => lb
  end. 
  
Definition get_stack_frame (lsf : labeled_stack_frame) : stack_frame :=
  match lsf with 
    | Labeled_frame lb sf => sf
  end. 


Definition sf_update (sf : stack_frame) (x : id) (v : tm) :=
  fun x' => if beq_id x x' then (Some v) else sf x'.


Definition labeled_frame_update (lsf : labeled_stack_frame) (x : id) (v : tm) :=
  match lsf with
    |  Labeled_frame lb sf  =>  Labeled_frame lb (fun x' => if beq_id x x' then (Some v) else sf x')
  end.

Check sf_update.



(* unrestricted access L *)
Definition L_Label := LB nil.

Definition empty_stack_frame : stack_frame := fun _ => None.
Definition empty_labeled_stack_frame : labeled_stack_frame := (Labeled_frame L_Label empty_stack_frame).

Definition main_frame : labeled_stack_frame := empty_labeled_stack_frame.

Definition stack :Type := list (option labeled_stack_frame).

Check stack. 

Check labeled_frame_update.

Definition stack_push (s : stack) (lsf : labeled_stack_frame) := 
  cons (Some lsf) s. 

Fixpoint update_stack_top (s : stack) (x : id) (v : tm) := 
match s with 
  | cons (Some lsf) s' => cons (Some (labeled_frame_update lsf x v)) s'
  | nil => nil
  | cons None s' => update_stack_top s' x v
end.

Definition stack_pop (s : stack) : (option labeled_stack_frame) := 
match s with
  | h :: t => h
  | nil => None
end.

Definition variableLookup (s : stack) (x : id) : (option tm)  :=
match s with 
  | (Some lsf) :: t => (get_stack_frame lsf)(x)
  | nil => None
  | None :: lsf => None
end. 

Definition get_current_label (s : stack) : Label :=
match s with
  | (Some lsf) :: t => (get_stack_label lsf)
  | nil => L_Label
  | None :: lsf => L_Label
end.


(* Definitions for Heap related*)
Definition FieldMap : Type := id -> (option tm).

Definition fields_update (F : FieldMap) (x : id) (v : tm) :=
  fun x' => if beq_id x x' then (Some v) else F x'.

Inductive heapObj : Type :=
  | Heap_OBJ : cn -> FieldMap -> Label -> heapObj.

Definition heap : Type := oid -> (option heapObj).

(* change notation *)
Notation "< cn , F , l >" := (Heap_OBJ cn F l).

Definition get_obj_label (h : heap) (o : oid) : Label :=
  match h(o) with
  | Some (Heap_OBJ id F lb) => lb
  | None => L_Label
  end. 

(* comparison of identifiers *)
Definition beq_oid x y :=
  match x,y with
    | OID n1, OID n2 => if beq_nat n1 n2 then true else false
  end.

Definition add_heap_obj (h : heap) (o : oid) (ho : heapObj) :=
  fun x' => if beq_oid o x' then (Some ho) else h x'.

Inductive Sigma := 
  | SIGMA : stack -> heap -> Sigma.

Definition Config := pair Sigma tm. 

Check Config.

Inductive ty : Type :=
  | cnTy : ty 
  | LabelTy : ty
  | LabelelTy : ty -> ty
  | OpaqueLabeledTy : ty -> ty.


(* typing environment *)
Definition context := id -> (option ty).

Definition get_stack (sgm : Sigma) : stack :=
  match sgm with
   | SIGMA s h => s
  end.

Definition get_heap (sgm : Sigma) : heap :=
  match sgm with
   | SIGMA s h => h
  end.


Reserved Notation "Gamma '|-' t '\in' T" (at level 40).
Reserved Notation "c1 '/' st '==>' c1' '/' st'"
  (at level 40, st at level 39, c1' at level 39).

Definition isDefined (h : heap) (o : oid):=
  match h(o) with 
    | None => false
    | Some v => true
  end. 

Inductive step : tm -> Sigma -> tm -> Sigma -> Prop :=
  | ST_var : forall id sigma,
      Exp (Tvar id) / sigma ==> (match (variableLookup (get_stack sigma) id) with
                                  | None => NPE
                                  | Some v  => v
                                end) / sigma

  | ST_fieldRead1 : forall sigma sigma' e e' f,
      (Exp e) / sigma ==> (Exp e') / sigma' -> 
      Exp (FieldAccess e f) / sigma ==> Exp (FieldAccess e' f) / sigma'
  | ST_fieldRead2 : forall sigma sigma' o f lx l 

where "c1 '/' st '==>' c1' '/' st'" := (step c1 st c1' st').







(*
Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T,
      Gamma x = Some T ->
      Gamma |- tvar x \in T
  | T_Abs : forall Gamma x T11 T12 t12,
      update Gamma x T11 |- t12 \in T12 ->
      Gamma |- tabs x T11 t12 \in TArrow T11 T12
  | T_App : forall T11 T12 Gamma t1 t2,
      Gamma |- t1 \in TArrow T11 T12 ->
      Gamma |- t2 \in T11 ->
      Gamma |- tapp t1 t2 \in T12
  | T_True : forall Gamma,
       Gamma |- ttrue \in (TermTy (mBool, rNone))
  | T_False : forall Gamma,
       Gamma |- tfalse \in (TermTy (mBool, rNone))
  | T_If : forall t1 t2 t3 T Gamma,
       Gamma |- t1 \in (TermTy (mBool, rNone)) ->
       Gamma |- t2 \in T ->
       Gamma |- t3 \in T ->
       Gamma |- tif t1 t2 t3 \in T

where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

Hint Constructors has_type.
*)









