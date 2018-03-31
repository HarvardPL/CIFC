Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.

Require Import Label.


(* identifiers *)
Inductive id : Type :=
  | Id : string -> id.

(* class name *)
Inductive cn : Type :=
  | class_name : string -> cn.

Inductive field : Type :=
  | fd : cn -> id -> field.





(* comparison of identifiers *)
Definition beq_id x y :=
  match x,y with
    | Id n1, Id n2 => if string_dec n1 n2 then true else false
  end.



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
  | v_l : tm -> tm -> tm
  | v_opa_l : tm -> tm -> tm.

Inductive method_def : Type :=
  | m_def : cn -> id -> cn -> id -> tm -> method_def.


Inductive CLASS : Type :=
  | class_def : cn -> (list field) -> (list method_def) -> CLASS. 



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


(* stack *)
Definition stack :Type := list labeled_stack_frame.

Check stack. 

Check labeled_frame_update.

Fixpoint update_stack_top (s : stack) (x : id) (v : tm) := 
match s with 
  | cons lsf s' => cons (labeled_frame_update lsf x v) s'
  | nil => nil
end.

Definition variableLookup (s : stack) (x : id) : (option tm)  :=
match s with 
  | (lsf) :: t => (get_stack_frame lsf)(x)
  | nil => None
end. 

Definition get_current_label (s : stack) : Label :=
match s with
  | lsf :: t => (get_stack_label lsf)
  | nil => L_Label
end.

(* Definitions for Heap related*)
Definition FieldMap : Type := id -> (option tm).

Definition fields_update (F : FieldMap) (x : id) (v : tm) :=
  fun x' => if beq_id x x' then (Some v) else F x'.

Inductive heapObj : Type :=
  | Heap_OBJ : CLASS -> FieldMap -> Label -> heapObj.

Definition heap := oid -> (option heapObj).

Definition get_obj_label (h : heap) (o : oid) : Label :=
  match h(o) with
  | Some (Heap_OBJ c F lb) => lb
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




Definition get_stack (sgm : Sigma) : stack :=
  match sgm with
   | SIGMA s h => s
  end.

Definition get_heap (sgm : Sigma) : heap :=
  match sgm with
   | SIGMA s h => h
  end.

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
  | cons lsf s' => match lsf with
                            | Labeled_frame lb' sf => cons (Labeled_frame lb sf) s'
                          end 
  | nil => nil
end.


(* variable declaration *)
Inductive vd : Type :=
  | var_def : cn -> id -> vd.



Fixpoint find_method_body (methods : list method_def) (m : id) :=
  match methods with
    | nil => None
    | h :: t =>  match h with 
                  | m_def cls m' cls_a arg_id body => if beq_id m m' then Some (m_def cls m' cls_a arg_id body) else find_method_body t m
                 end
  end.

Definition find_method (cls : CLASS) (m : id) := 
  match cls with
    | class_def c_name fields methods => find_method_body methods m
  end.




Definition find_fields (cls : CLASS) := 
  match cls with
    | class_def c_name fields methods => fields
  end.

Fixpoint type_of_field (fields : list field) (f : id) : option cn :=
  match fields with
     | nil => None
     | (fd cls h) :: t => if beq_id h f then Some cls else (type_of_field t f)
  end.

Definition empty_field_map : FieldMap := fun _ => None.

Fixpoint init_field_map (fields : list field) (fm : FieldMap) :=
  match fields with 
    | nil => fm
    | (fd cls h) :: t => init_field_map t (fun x' => if beq_id h x' then Some null else fm h)
  end.

Check init_field_map.



Inductive step : tm -> Sigma -> tm -> Sigma -> Prop :=
(* variabel access *)
  | ST_var : forall id sigma s h lb sf lsf v s',
      sigma = SIGMA s h ->
      s = cons lsf s' ->
      lsf = Labeled_frame lb sf ->
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
  | ST_MethodCall3 : forall sigma sigma' o s h cls fields v lx l theta Delta' sf lsf arg_id cls_a body meth returnT,
      sigma = SIGMA s h ->
      Some (Heap_OBJ cls fields lx) = h(o) -> 
      Some (m_def returnT meth cls_a arg_id body) = find_method cls meth -> 
      sf = sf_update (sf_update empty_stack_frame (Id "this") (ObjId o)) arg_id v ->
      l = (current_label sigma) ->
      lsf = Labeled_frame l sf ->
      theta = lsf -> 
      Delta' = cons theta s ->
      sigma' = SIGMA Delta' (get_heap sigma) ->
      MethodCall (ObjId o) meth v / sigma ==> body / sigma'
  (* null pointer exception for method call *)
  | ST_MethodCallException : forall sigma v meth, 
      MethodCall null meth v / sigma ==> NPE / sigma

(* new expression *)
  | ST_NewExp : forall sigma sigma' F o h cls h' s lb cn f_def m_def,
      sigma = SIGMA s h->
      h(o) = None -> 
      F =  (init_field_map (find_fields cls) empty_field_map) ->
      lb = (current_label sigma) -> 
      cls = class_def cn f_def m_def->
      h' = add_heap_obj h o (Heap_OBJ cls F lb) ->
      sigma' = SIGMA s h' ->
      NewExp cn / sigma ==> ObjId o / sigma'

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
      (labelOf (v_l v lb)) / sigma ==> (lb) / sigma

(* unlabel opaque*)
  (* context rule *)
  | ST_unlabel_opaque1 : forall sigma sigma' e e',
       e / sigma ==>  e' / sigma' -> 
      (unlabelOpaque e) / sigma ==> (unlabelOpaque e') / sigma'
  (* unlabel opaque *)
  | ST_unlabel_opaque2 : forall sigma v lb l' sigma' s h,
      sigma = SIGMA s h ->
      l' = join_label lb (current_label sigma) ->
      (unlabelOpaque ((v_opa_l v (l lb)))) / sigma ==> v / sigma'

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
      (opaqueCall (Return v)) / sigma ==> v_opa_l v (l lb) / sigma'

(* method call with unlabel opaque *)
  | ST_MethodCall_unlableOpaque : forall sigma sigma' o s h cls fields v lx l' lb theta Delta' sf lsf arg_id cls_a body meth returnT,
      sigma = SIGMA s h ->
      Some (Heap_OBJ cls fields lx) = h(o) -> 
      sf = sf_update (sf_update empty_stack_frame (Id "this") (ObjId o)) arg_id v ->
      l' = join_label lb (current_label sigma) ->
      lsf = Labeled_frame l' sf ->
      theta = lsf -> 
      Delta' = cons theta s ->
      Some (m_def returnT meth cls_a arg_id body) = find_method cls meth ->
      sigma' = SIGMA Delta' (get_heap sigma) ->
      MethodCall (ObjId o) meth (unlabelOpaque ((v_opa_l v (l lb)))) / sigma ==> body / sigma'

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
      e2 = unlabelOpaque ((v_opa_l v (l lb))) ->
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

Inductive ty : Type :=
  | classTy : cn -> ty 
  | LabelTy : ty
  | LabelelTy : ty -> ty
  | OpaqueLabeledTy : ty -> ty
  | voidTy : ty.

Definition typing_context := id -> (option ty).
Definition empty_context : typing_context := fun _ => None.

(*
(* typing environment *)
Reserved Notation "Gamma '|-' t '\in' T" (at level 40).

Inductive has_type : typing_context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T,
      Gamma x = Some T ->
      Gamma |- Tvar x \in T
  | T_null : forall Gamma T,
      Gamma |- null \in T
where "Gamma '|-' t '\in' T" := (has_type Gamma t T).
*)

Reserved Notation "CT ; Gamma '|-' t '\in' T" (at level 0).

Definition Class_table := cn -> CLASS.

Check find_method.

Inductive has_type : Class_table -> typing_context -> tm -> ty -> Prop :=
(*variable *)
  | T_Var : forall Gamma x T CT, 
      Gamma x = Some T ->
      CT ; Gamma |- Tvar x \in T
(* null *)
  | T_null : forall Gamma T CT, 
      CT ; Gamma |- null \in T
(* Field read *)
  | T_FieldAccess : forall Gamma e f cls_def CT clsT cls',
      CT ; Gamma |- e \in (classTy clsT) ->
      cls_def = CT(clsT) ->
      type_of_field (find_fields cls_def) f = Some cls' ->
      CT ; Gamma |- (FieldAccess e f) \in (classTy cls')
(* method call *)
  | T_MethodCall : forall Gamma e meth argu CT T returnT cls_def body arg_id arguT para_T cls_a,
      CT ; Gamma |- e \in (classTy T) ->
      CT ; Gamma |- argu \in arguT ->
      cls_def = CT(T) ->
      find_method cls_def meth = Some (m_def returnT meth cls_a arg_id body)  ->
      arguT = para_T ->
      CT ; Gamma |- MethodCall e meth argu \in (classTy returnT)
(* new exp *)
  | T_NewExp : forall Gamma cn CT,
      CT ; Gamma |- NewExp cn \in (classTy cn)
(* this *)
  | T_this : forall Gamma T CT,
      CT ; Gamma |- this \in T
(* label *)
  | T_label : forall Gamma lb CT,
      CT ; Gamma |- l lb \in LabelTy
(* label data *)
  | T_labelData : forall Gamma lb CT e T,
      CT ; Gamma |- lb \in LabelTy ->
      CT ; Gamma |- e \in T ->
      CT ; Gamma |- labelData e lb \in (LabelelTy T)
(* unlabel *)
  | T_unlabel : forall Gamma CT e T,
      CT ; Gamma |- e \in (LabelelTy T) ->
      CT ; Gamma |- unlabel e \in T
(* labelOf *)
  | T_labelOf : forall Gamma CT e T,
      CT ; Gamma |- e \in (LabelelTy T) ->
      CT ; Gamma |- labelOf e \in LabelTy
(* unlabel opaque *)
  | T_unlabelOpaque : forall Gamma CT e T,
      CT ; Gamma |- e \in (LabelelTy T) -> 
      CT ; Gamma |- unlabelOpaque e \in T
(* opaque call *)
  | T_opaqueCall : forall Gamma CT e T,
      CT ; Gamma |- e \in T ->
      CT ; Gamma |- opaqueCall e \in (OpaqueLabeledTy T)
(* Skip *)
  | T_skip : forall Gamma CT T,
      CT ; Gamma |- Skip \in T
(* assignment *)
  | T_assignment : forall Gamma CT e T x,
      Gamma x = Some T ->
      CT ; Gamma |- e \in T ->
      CT ; Gamma |- Assignment x e \in T
(* Field Write *)
  | T_FieldWrite : forall Gamma x f cls_def CT clsT cls' e,
      CT ; Gamma |- x \in (classTy clsT) ->
      CT ; Gamma |- e \in (classTy cls') ->
      cls_def = CT(clsT) ->
      type_of_field (find_fields cls_def) f = Some cls' ->
      CT ; Gamma |- (FieldWrite x f e) \in (classTy cls')
(* if *)
  | T_if : forall Gamma CT e e1 e2 e3 T T',
      CT ; Gamma |- e \in T ->
      CT ; Gamma |- e1 \in T ->
      CT ; Gamma |- e2 \in T' ->
      CT ; Gamma |- e3 \in T' ->
      CT ; Gamma |- If e e1 e2 e3 \in T'
(* sequence *)
  | T_sequence : forall Gamma CT e1 e2 T T',
      CT ; Gamma |- e1 \in T ->
      CT ; Gamma |- e2 \in T' ->
      CT ; Gamma |- Sequence e1 e2 \in T'
(* return *)
  | T_return : forall Gamma CT e T,
      CT ; Gamma |- e \in T ->
      CT ; Gamma |- Return e \in T
(* ObjId *)
  | T_ObjId : forall Gamma CT o T,
      CT ; Gamma |- ObjId o \in T
(* NPE *)
  | T_NPE : forall Gamma CT T,
      CT ; Gamma |- NPE \in T
(* runtime labeled data *)
  | T_v_l : forall Gamma lb CT v T,
      CT ; Gamma |- lb \in LabelTy ->
      CT ; Gamma |- v \in T ->
      CT ; Gamma |- v_l v lb \in (LabelelTy T)
(* runtime labeled data *)
  | T_v_opa_l : forall Gamma lb CT v T,
      CT ; Gamma |- lb \in LabelTy ->
      CT ; Gamma |- v \in T ->
      CT ; Gamma |- v_opa_l v lb \in (OpaqueLabeledTy T)



where "CT ; Gamma '|-' t '\in' T" := (has_type CT Gamma t T).

Definition empty_heap : heap := fun _ => None.

Inductive wfe_heap : Class_table -> typing_context -> heap -> Prop :=
  | empty_heap_wfe : forall ct ctx, wfe_heap ct ctx empty_heap
  | heap_wfe : forall h o cls F lo cn field_defs method_defs ct ctx,
        h(o) = None ->
        cls = class_def cn field_defs method_defs->
        wfe_heap ct ctx h -> 
        wfe_heap ct ctx (add_heap_obj h o (Heap_OBJ cls F lo)).


Check Heap_OBJ.

(*define the well-formed environment as a prop *)Inductive wfe : CT -> Gamma -> Sigma -> Prop :=
  


lemma 

Theorem progress : forall t T sigma gamma CT, 
  CT ; gamma |- t \in T -> value t \/ exists t' sigma', t / sigma ==> t' / sigma'.
Proof.
  intros t T sigma gamma CT H.
  induction H. 
  - right. exists t'.

Admitted.

  | NPE : tm
  (* runtime labeled date*)
  | v_l : tm -> Label -> tm
  | v_opa_l : tm -> Label -> tm.

Theorem preservation : forall t t' T sigma sigma', 
    gamma |- t \in T ->
    t / st ==> t' / st' ->
    gamma |- t' \in T.

Proof



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









