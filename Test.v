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
  | fd : cn -> id -> field.

(*
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

*)


Inductive oid : Type := 
  | OID : nat -> oid.

Inductive tm : Type :=
  | Tvar : id -> tm
  | null : tm
  | FieldAccess : tm -> id -> tm
  | MethodCall : tm -> id -> tm -> tm
  | NewExp : cn -> tm
  | this : tm
(* label related *)
  | l : Label -> tm
  | labelData : tm -> tm -> tm
  | unlabel : tm -> tm
  | labelOf : tm -> tm
  | unlabelOpaque : tm -> tm
  | opaqueCall : tm -> tm

(* statements *)
  | Skip : tm
  | Assignment : id -> tm -> tm
  | FieldWrite : tm -> id -> tm -> tm
  | If : tm -> tm -> tm -> tm -> tm 
  | Sequence : tm -> tm -> tm
  | Return : tm -> tm

(* special terms *)
  | ObjId: oid -> tm
  | NPE : tm
  (* runtime labeled date*)
  | v_l : tm -> Label -> tm
  | v_opa_l : tm -> Label -> tm.

Inductive method_def : Type :=
  | m_def : cn -> id -> cn -> id -> tm -> method_def.

Inductive value : tm -> Prop :=
  (* contants are values or normal form *)
  | v_oid :
      forall o, value (ObjId o)
  | v_none : 
      value Skip
  | v_label :
      forall lb, value (l lb)
  | v_exception :
      value NPE.

(*  | v_labeled :
      forall t lb, value (v_l t lb).
*)

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

Definition heap := oid -> (option heapObj).

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

Definition current_label (sigma : Sigma) : Label :=
  get_current_label (get_stack sigma).

Fixpoint update_current_label (s : stack) (lb : Label) := 
match s with 
  | cons (Some lsf) s' => match lsf with
                            | Labeled_frame lb' sf => cons (Some (Labeled_frame lb sf)) s'
                          end 
  | nil => nil
  | cons None s' => update_current_label s' lb
end.


Definition P := cn -> ((list id) * option (list method_def)). 

Check P.

(* variable declaration *)
Inductive vd : Type :=
  | var_def : cn -> id -> vd.

Check snd.

Definition findmbody (cls : cn) (m : id) (p : P) := 
  match snd (p(cls)) with
    | Some nil => None
    | Some (h :: t) => match h with 
                  | m_def cls m cls_a arg_id body => Some ((var_def cls_a arg_id), body)
                end
    | None => None
  end.


Definition find_fields (cls : cn) (p : P) :=
  fst (p(cls)).

Check find_fields.


Definition empty_field_map : FieldMap := fun _ => None.

Fixpoint init_field_map (fields : list id) (fm : FieldMap) :=
  match fields with 
    | nil => fm
    | h :: t => init_field_map t (fun x' => if beq_id h x' then Some null else fm h)
  end.

Check init_field_map.



Inductive step : tm -> Sigma -> tm -> Sigma -> Prop :=
(* variabel access *)
  | ST_var : forall id sigma s h lb sf lsf v s',
      sigma = SIGMA s h ->
      s = cons lsf s' ->
      lsf = Some (Labeled_frame lb sf) ->
      Some v = sf(id) ->
      (Tvar id) / sigma ==> v / sigma

(* field read *)
  (* context rule *)
  | ST_fieldRead1 : forall sigma sigma' e e' f,
       e / sigma ==>  e' / sigma' -> 
      (FieldAccess e f) / sigma ==> (FieldAccess e' f) / sigma'
  (* normal field access *)
  | ST_fieldRead2 : forall sigma sigma' o s h fname lb cls fields v l' Delta Delta',
      sigma = SIGMA s h ->
      Some (Heap_OBJ cls fields lb) = h(o) -> 
      Some v = fields(fname) -> 
      l' = join_label lb (current_label sigma) ->
      Delta' = update_current_label Delta l'-> 
      sigma' = SIGMA Delta' (get_heap sigma) ->
      (FieldAccess (ObjId o) fname) / sigma ==> v / sigma'
  (* null pointer exception for field access *)
  | ST_fieldReadException : forall sigma f ,
      (FieldAccess null f) / sigma ==> NPE / sigma

(* method call *)
  (* context rule: evaluate object target *)
  | ST_MethodCall1 : forall sigma sigma' e e' id,
       e / sigma ==>  e' / sigma' -> 
      (MethodCall e id e) / sigma ==> (MethodCall e' id e) / sigma'
  (* context rule: evaluate arguments *)
  | ST_MethodCall2 : forall sigma sigma' e e' id t,
      e <> unlabelOpaque t ->
       e / sigma ==>  e' / sigma' -> 
      (MethodCall e id e) / sigma ==> (MethodCall e id e') / sigma'
  (* normal method call *)
  | ST_MethodCall3 : forall sigma sigma' o s h cls fields v lx l theta Delta' sf lsf arg_id cls_a body meth p ,
      sigma = SIGMA s h ->
      Some (Heap_OBJ cls fields lx) = h(o) -> 
      sf = sf_update (sf_update empty_stack_frame (Id "this") (ObjId o)) arg_id v ->
      l = (current_label sigma) ->
      lsf = Labeled_frame l sf ->
      theta = Some lsf -> 
      Delta' = cons theta s ->
      Some ((var_def cls_a arg_id), body) = findmbody cls meth p -> 
      sigma' = SIGMA Delta' (get_heap sigma) ->
      MethodCall (ObjId o) meth v / sigma ==> body / sigma'
  (* null pointer exception for method call *)
  | ST_MethodCallException : forall sigma v meth, 
      MethodCall null meth v / sigma ==> NPE / sigma

(* new expression *)
  | ST_NewExp : forall sigma sigma' P F o h cls h' s lb,
      sigma = SIGMA s h->
      h(o) = None -> 
      F =  (init_field_map (find_fields cls P) empty_field_map) ->
      lb = (current_label sigma) -> 
      h' = add_heap_obj h o (Heap_OBJ cls F lb) ->
      sigma' = SIGMA s h' ->
      NewExp cls / sigma ==> ObjId o / sigma'

(* this expression *)
  | ST_this : forall sigma o s h, 
      sigma = SIGMA s h ->
      Some o = variableLookup s (Id "this") ->
      this / sigma ==>  o / sigma

(* label data express *)
  (* context rule *)
  | ST_LabelData1 : forall sigma sigma' e e' lb,
       e / sigma ==>  e' / sigma' -> 
      (labelData e lb) / sigma ==> (labelData e' lb) / sigma'
  (* label data *)
  | ST_LabelData2 : forall sigma v_l v lb,
      (labelData v lb) / sigma ==> (v_l v lb) / sigma
  (* label data exception *)
  | ST_LabelDataException : forall sigma lb,
      (labelData null lb) / sigma ==> NPE / sigma

(* unlabel *)
  (* context rule *)
  | ST_unlabel1 : forall sigma sigma' e e',
       e / sigma ==>  e' / sigma' -> 
      (unlabel e) / sigma ==> (unlabel e') / sigma'
  (* unlabel *)
  | ST_unlabel : forall sigma v_l v lb l' sigma' s h,
      sigma = SIGMA s h ->
      l' = join_label lb (current_label sigma) ->
      (unlabel ((v_l v lb))) / sigma ==> v / sigma'

(* Label of *)
  (* context rule *)
  | ST_labelof1 : forall sigma sigma' e e',
       e / sigma ==>  e' / sigma' -> 
       (labelOf e) / sigma ==> (labelOf e') / sigma'
  (* label of  *)
  | ST_labelof2 : forall sigma v lb,
      (labelOf (v_l v lb)) / sigma ==> (l lb) / sigma

(* unlabel opaque*)
  (* context rule *)
  | ST_unlabel_opaque1 : forall sigma sigma' e e',
       e / sigma ==>  e' / sigma' -> 
      (unlabelOpaque e) / sigma ==> (unlabelOpaque e') / sigma'
  (* unlabel opaque *)
  | ST_unlabel_opaque2 : forall sigma v lb l' sigma' s h,
      sigma = SIGMA s h ->
      l' = join_label lb (current_label sigma) ->
      (unlabelOpaque ((v_opa_l v lb))) / sigma ==> v / sigma'

(* Opaque call *)
  (* context rule *)
  | ST_opaquecall1 : forall sigma sigma' e e' t,
       e <> Return t ->
       e / sigma ==>  e' / sigma' -> 
      (opaqueCall e) / sigma ==> (opaqueCall e') / sigma'
  (* return context rule*)
  | ST_opaquecall_return1 : forall sigma sigma' e e',
       e / sigma ==>  e' / sigma' -> 
      (opaqueCall (Return e)) / sigma ==> (opaqueCall (Return e')) / sigma'
  (* opaque call with value, without method call inside*)
  | ST_opaquecall_val2 : forall sigma v,
      (opaqueCall v) / sigma ==> v / sigma
  (* opaque call with return statement *)
  | ST_opaquecall_return2 : forall sigma sigma' s h lb s' lsf v,
      sigma = SIGMA s h->
      s = cons lsf s' ->
      lb = (current_label sigma) ->
      sigma' = SIGMA s' h->
      (opaqueCall (Return v)) / sigma ==> v_opa_l v lb / sigma'

(* method call with unlabel opaque *)
  | ST_MethodCall_unlableOpaque : forall sigma sigma' o s h cls fields v lx l lb theta Delta' sf lsf arg_id cls_a body meth p ,
      sigma = SIGMA s h ->
      Some (Heap_OBJ cls fields lx) = h(o) -> 
      sf = sf_update (sf_update empty_stack_frame (Id "this") (ObjId o)) arg_id v ->
      l = join_label lb (current_label sigma) ->
      lsf = Labeled_frame l sf ->
      theta = Some lsf -> 
      Delta' = cons theta s ->
      Some ((var_def cls_a arg_id), body) = findmbody cls meth p -> 
      sigma' = SIGMA Delta' (get_heap sigma) ->
      MethodCall (ObjId o) meth (unlabelOpaque ((v_opa_l v lb))) / sigma ==> body / sigma'

(* assignment *)
  (* context rule *)
  | ST_assignment1 : forall sigma sigma' e e' id,
       e / sigma ==>  e' / sigma' -> 
       Assignment id e / sigma ==> Assignment id e' / sigma'
  (* assignment *)
  | ST_assignment2 : forall sigma sigma' id v s' s h,
       sigma = SIGMA s h ->
       s' = update_stack_top s id v->
       sigma' = SIGMA s' h ->
       Assignment id v / sigma ==> Skip / sigma'

(* Field Write *)
  (* context rule 1 *)
  | ST_fieldWrite1 : forall sigma sigma' f e1 e1' e2,
       e1 / sigma ==>  e1' / sigma' -> 
       FieldWrite e1 f e2 / sigma ==> FieldWrite e1' f e2/ sigma'

  (* context rule 2 *)
  | ST_fieldWrite2 : forall sigma sigma' f e1 e2 e2' t,
       e2 <> unlabelOpaque t ->
       e2 / sigma ==>  e2' / sigma' -> 
       FieldWrite e1 f e2 / sigma ==> FieldWrite e1 f e2'/ sigma'

  (* field write normal *)
  | ST_fieldWrite3 : forall sigma sigma' o s h h' f lb cls F F' v l',
      sigma = SIGMA s h ->
      Some (Heap_OBJ cls F lb) = h(o) -> 
      F' = fields_update F f v ->
      l' = join_label lb (current_label sigma) ->
      h' = add_heap_obj h o (Heap_OBJ cls F' l') ->
      sigma' = SIGMA s h' ->
      (FieldWrite (ObjId o) f v) / sigma ==> Skip / sigma'
  (* null pointer exception for field write *)
  | ST_fieldWriteException : forall sigma f v o, 
      (FieldWrite (ObjId o) f v) / sigma ==> NPE / sigma
  (* field write normal *)
  | ST_fieldWrite_opaque : forall sigma sigma' o s h h' f lo cls F F' v l' lb e2,
      e2 = unlabelOpaque ((v_opa_l v lb)) ->
      sigma = SIGMA s h ->
      Some (Heap_OBJ cls F lo) = h(o) -> 
      F' = fields_update F f v ->
      l' = join_label lo lb ->
      h' = add_heap_obj h o (Heap_OBJ cls F' l') ->
      sigma' = SIGMA s h' ->
      (FieldWrite (ObjId o) f e2) / sigma ==> Skip / sigma'

(* return statement *)
  (* context rule*)
  | ST_return1 : forall sigma sigma' e e',
       e / sigma ==>  e' / sigma' -> 
        Return e / sigma ==> Return e' / sigma'
  (* return val *)
  | ST_return2 : forall sigma sigma' v s s' s'' h lsf l', 
      sigma = SIGMA s h ->
      s = cons lsf s' ->
      l' = join_label (get_current_label s) (get_current_label s') ->
      s'' = update_current_label s' l' ->
      sigma' = SIGMA s'' h ->
       Return v / sigma ==> v / sigma'
(* if statement *)
   (* context rule 1 *)
  | ST_if1 : forall sigma sigma' s1 s2 e1' e1 e2, 
       e1 / sigma ==>  e1' / sigma' -> 
       If e1 e2 s1 s2 / sigma ==> If e1' e2 s1 s2 / sigma'
   (* context rule 2 *)
  | ST_if2 : forall sigma sigma' s1 s2 e2' e2 v, 
       e2 / sigma ==>  e2' / sigma' -> 
       If v e2 s1 s2 / sigma ==> If v e2' s1 s2 / sigma'
  | ST_if_b1 : forall sigma s1 s2 v1 v2, 
       v1 = v2 ->
       If v1 v2 s1 s2 / sigma ==>  s1 / sigma
  | ST_if_b2 : forall sigma s1 s2 v1 v2, 
       v1 <> v2 ->
       If v1 v2 s1 s2 / sigma ==>  s2 / sigma
(* sequence *)
   (* context rule *)
  | ST_seq1 : forall sigma s1 s2 s1', 
    Sequence s1 s2 / sigma ==> Sequence s1' s2 / sigma
   (* sequence rule *)
  | ST_seq2 : forall sigma v s , 
    Sequence v s / sigma ==> s / sigma

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









