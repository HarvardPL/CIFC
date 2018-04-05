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

Inductive oid : Type := 
  | OID : nat -> oid.

Inductive tm : Type :=
  | Tvar : id -> tm
  | null : tm
  | FieldAccess : tm -> id -> tm
  | MethodCall : tm -> id -> tm -> tm
  | NewExp : cn -> tm
(* label related *)
  | l : Label -> tm
  | labelData : tm -> Label -> tm
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


Inductive CLASS : Type :=
  | class_def : cn -> (list field) -> (list method_def) -> CLASS. 



Inductive value : tm -> Prop :=
  (* contants are values or normal form *)
  | v_oid :
      forall o, value (ObjId o)
(* skip is not a terminal
  | v_none : 
      value Skip *)
  | v_null :
      value null
  | v_label :
      forall lb, value (l lb)
  | v_labeled : forall v lb,
      value v ->
      value (v_l v lb)
  | v_opa_labeled : forall v lb,
      value v ->
      value (v_opa_l v lb).

Inductive Exception : tm -> Prop :=
  | exception : Exception NPE.

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


Definition add_heap_obj (h : heap) (o : oid) (ho : heapObj) :=
  fun x' => if beq_oid o x' then (Some ho) else h x'.

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
  | ST_fieldRead2 : forall sigma sigma' o s h fname lb cls fields v l' s',
      sigma = SIGMA s h ->
      Some (Heap_OBJ cls fields lb) = h(o) -> 
      Some v = fields(fname) -> 
      l' = join_label lb (current_label sigma) ->
      s' = update_current_label s l'-> 
      sigma' = SIGMA s' (get_heap sigma) ->
      (FieldAccess (ObjId o) fname) / sigma ==> v / sigma'
  (* null pointer exception for field access *)
  | ST_fieldReadException : forall sigma f ,
      (FieldAccess null f) / sigma ==> NPE / sigma

(* method call *)
  (* context rule: evaluate object target *)
  | ST_MethodCall1 : forall sigma sigma' e e' e2 id,
       e / sigma ==>  e' / sigma' -> 
      (MethodCall e id e2) / sigma ==> (MethodCall e' id e2) / sigma'
  (* context rule: evaluate arguments *)
  | ST_MethodCall2 : forall sigma sigma' v e e' id,
      (forall t, value t -> t<> null -> e <> unlabelOpaque t) ->
      e / sigma ==>  e' / sigma' -> 
      value v ->
      (MethodCall v id e) / sigma ==> (MethodCall v id e') / sigma'
  (* normal method call *)
  | ST_MethodCall3 : forall sigma sigma' o s h cls fields v lx l theta s' sf lsf arg_id cls_a body meth returnT,
      sigma = SIGMA s h ->
      Some (Heap_OBJ cls fields lx) = h(o) -> 
      Some (m_def returnT meth cls_a arg_id body) = find_method cls meth -> 
      value v ->
      sf = sf_update (sf_update empty_stack_frame (Id "this") (ObjId o)) arg_id v ->
      l = (current_label sigma) ->
      lsf = Labeled_frame l sf ->
      theta = lsf -> 
      s' = cons theta s ->
      sigma' = SIGMA s' (get_heap sigma) ->
      MethodCall (ObjId o) meth v / sigma ==> body / sigma'
  (* null pointer exception for method call *)
  | ST_MethodCallException : forall sigma v meth, 
      MethodCall null meth v / sigma ==> NPE / sigma

(* method call with unlabel opaque *)
  | ST_MethodCall_unlableOpaque : forall sigma sigma' o s h cls fields v lx l' lb s' sf lsf arg_id cls_a body meth returnT,
      sigma = SIGMA s h ->
      Some (Heap_OBJ cls fields lx) = h(o) -> 
      sf = sf_update (sf_update empty_stack_frame (Id "this") (ObjId o)) arg_id v ->
      l' = join_label lb (current_label sigma) ->
      lsf = Labeled_frame l' sf ->
      s' = cons lsf s ->
      Some (m_def returnT meth cls_a arg_id body) = find_method cls meth ->
      sigma' = SIGMA s' (get_heap sigma) ->
      MethodCall (ObjId o) meth (unlabelOpaque (v_opa_l v lb)) / sigma ==> body / sigma'

  (* null pointer exception for method call with unlabel opaque of null data*)
  | ST_MethodCallOpaqueDataException : forall sigma o meth, 
      MethodCall (ObjId o) meth (unlabelOpaque null) / sigma ==> NPE / sigma

(* new expression *)
  | ST_NewExp : forall sigma sigma' F o h cls h' s lb cn,
      sigma = SIGMA s h->
      h(o) = None -> 
      F =  (init_field_map (find_fields cls) empty_field_map) ->
      lb = (current_label sigma) -> 

      h' = add_heap_obj h o (Heap_OBJ cls F lb) ->
      sigma' = SIGMA s h' ->
      NewExp cn / sigma ==> ObjId o / sigma'


(* label data express *)
  (* context rule *)
  | ST_LabelData1 : forall sigma sigma' e e' lb,
       e / sigma ==>  e' / sigma' -> 
      (labelData e lb) / sigma ==> (labelData e' lb) / sigma'
  (* label data *)
  | ST_LabelData2 : forall sigma v lb,
      value v ->
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
  | ST_unlabel2 : forall sigma v lb l' sigma' s h s',
      value v ->
      sigma = SIGMA s h ->
      l' = join_label lb (current_label sigma) ->
      s' = update_current_label s l'-> 
      sigma' = SIGMA s' (get_heap sigma) ->
      (unlabel (v_l v lb)) / sigma ==> v / sigma'
  (* unlabel data exception *)
  | ST_unlabelDataException : forall sigma,
      (unlabel null) / sigma ==> NPE / sigma

(* Label of *)
  (* context rule *)
  | ST_labelof1 : forall sigma sigma' e e',
       e / sigma ==>  e' / sigma' -> 
       (labelOf e) / sigma ==> (labelOf e') / sigma'
  (* label of  *)
  | ST_labelof2 : forall sigma v lb,
      (labelOf (v_l v lb)) / sigma ==> l lb / sigma
  | ST_labelOfDataException : forall sigma, 
      labelOf null / sigma ==> NPE / sigma


(* unlabel opaque*)
  (* context rule *)
  | ST_unlabel_opaque1 : forall sigma sigma' e e',
       e / sigma ==>  e' / sigma' -> 
      (unlabelOpaque e) / sigma ==> (unlabelOpaque e') / sigma'
  (* unlabel opaque *)
  | ST_unlabel_opaque2 : forall sigma v lb l' sigma' s h s',
      sigma = SIGMA s h ->
      l' = join_label lb (current_label sigma) ->
      s' = update_current_label s l'-> 
      sigma' = SIGMA s' (get_heap sigma) ->
      (unlabelOpaque (v_opa_l v lb)) / sigma ==> v / sigma'
  | ST_unlabel_opaqueDataException : forall sigma, 
      unlabelOpaque null / sigma ==> NPE / sigma

(* Opaque call *)
  (* context rule *)
  | ST_opaquecall1 : forall sigma sigma' e e',
       (forall v, value v -> e <> Return v) ->
       e / sigma ==>  e' / sigma' -> 
      (opaqueCall e) / sigma ==> (opaqueCall e') / sigma'
  (* return context rule*)
  | ST_opaquecall_return1 : forall sigma sigma' e e',
       e / sigma ==>  e' / sigma' -> 
      (opaqueCall (Return e)) / sigma ==> (opaqueCall (Return e')) / sigma'
  (* opaque call with value, without method call inside*)
  | ST_opaquecall_val2 : forall sigma v,
      (value v) ->
      (opaqueCall v) / sigma ==> v / sigma
  (* opaque call with return statement *)
  | ST_opaquecall_return2 : forall sigma sigma' s h lb s' lsf v,
      sigma = SIGMA s h->
      s = cons lsf s' ->
      lb = (current_label sigma) ->
      sigma' = SIGMA s' h->
      value v ->
      (opaqueCall (Return v)) / sigma ==> v_opa_l v lb / sigma'
  | ST_opaquecall_return3 : forall sigma,
      opaqueCall (Return null) / sigma ==> NPE / sigma


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
  | ST_fieldWrite2 : forall sigma sigma' f v e2 e2' t,
       value v ->
       e2 <> unlabelOpaque t ->
       e2 / sigma ==>  e2' / sigma' -> 
       FieldWrite v f e2 / sigma ==> FieldWrite v f e2'/ sigma'

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
      e2 = unlabelOpaque (v_opa_l v lb) ->
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
      value v ->
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
       value v ->
       If v e2 s1 s2 / sigma ==> If v e2' s1 s2 / sigma'
  | ST_if_b1 : forall sigma s1 s2 v1 v2, 
       v1 = v2 ->
       value v1 ->
       value v2 ->
       If v1 v2 s1 s2 / sigma ==>  s1 / sigma
  | ST_if_b2 : forall sigma s1 s2 v1 v2, 
       v1 <> v2 ->
       value v1 ->
       value v2 ->
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

Definition Class_table := cn -> option CLASS.



Inductive has_type : Class_table -> typing_context -> heap -> tm -> ty -> Prop :=
(*variable *)
  | T_Var : forall Gamma x T CT h, 
      Gamma x = Some (classTy T) ->
      has_type CT Gamma h (Tvar x) (classTy T)
(* null *)
  | T_null : forall Gamma h T CT, 
      has_type CT Gamma h null T
(* Field read *)
  | T_FieldAccess : forall Gamma e f cls_def CT clsT cls' h fields_def,
      has_type CT Gamma h e (classTy clsT) ->       
      Some cls_def = CT(clsT) ->
      fields_def = (find_fields cls_def) ->
      type_of_field fields_def f = Some cls' ->
      has_type CT Gamma h (FieldAccess e f) (classTy cls')
(* method call *)
  | T_MethodCall : forall Gamma e meth argu CT h T returnT cls_def body arg_id arguT para_T cls_a,
      has_type CT Gamma h e (classTy T) ->
      has_type CT Gamma h argu arguT ->
      Some cls_def = CT(T) ->
      find_method cls_def meth = Some (m_def returnT meth cls_a arg_id body)  ->
      arguT = para_T ->
      has_type CT Gamma h (MethodCall e meth argu) (classTy returnT)
(* new exp *)
  | T_NewExp : forall h Gamma cn CT cls_def,
      Some cls_def = CT(cn) ->
      has_type CT Gamma h (NewExp cn) (classTy cn)
(* label *)
  | T_label : forall h Gamma lb CT,
      has_type CT Gamma h (l lb) LabelTy
(* label data *)
  | T_labelData : forall h Gamma lb CT e T,
      has_type CT Gamma h (l lb) LabelTy ->
      has_type CT Gamma h e T ->
      has_type CT Gamma h (labelData e lb) (LabelelTy T)
(* unlabel *)
  | T_unlabel : forall h Gamma CT e T,
      has_type CT Gamma h e (LabelelTy T) ->
      has_type CT Gamma h (unlabel e) T
(* labelOf *)
  | T_labelOf : forall h Gamma CT e T,
      has_type CT Gamma h e (LabelelTy T) ->
      has_type CT Gamma h (labelOf e) LabelTy
(* unlabel opaque *)
  | T_unlabelOpaque : forall h Gamma CT e T,
      has_type CT Gamma h e (OpaqueLabeledTy T) -> 
      has_type CT Gamma h (unlabelOpaque e) T
(* opaque call *)
  | T_opaqueCall : forall h Gamma CT e T,
      has_type CT Gamma h e T ->
      has_type CT Gamma h (opaqueCall e) (OpaqueLabeledTy T)
(* Skip *)
  | T_skip : forall h Gamma CT T,
      has_type CT Gamma h Skip T
(* assignment *)
  | T_assignment : forall h Gamma CT e T x,
      Gamma x = Some T ->
      has_type CT Gamma h e T ->
      has_type CT Gamma h (Assignment x e) T
(* Field Write *)
  | T_FieldWrite : forall h Gamma x f cls_def CT clsT cls' e,
      has_type CT Gamma h x (classTy clsT) ->
      has_type CT Gamma h e (classTy cls') ->
      Some cls_def = CT(clsT) ->
      type_of_field (find_fields cls_def) f = Some cls' ->
      has_type CT Gamma h (FieldWrite x f e) (classTy cls')
(* if *)
  | T_if : forall Gamma h CT e e1 e2 e3 T T',
      has_type CT Gamma h e T ->
      has_type CT Gamma h e1 T ->
      has_type CT Gamma h e2 T' ->
      has_type CT Gamma h e3 T' ->
      has_type CT Gamma h (If e e1 e2 e3) T'
(* sequence *)
  | T_sequence : forall h Gamma CT e1 e2 T T',
      has_type CT Gamma h e1 T ->
      has_type CT Gamma h e2 T' ->
      has_type CT Gamma h (Sequence e1 e2) T'
(* return *)
  | T_return : forall h Gamma CT e T,
      has_type CT Gamma h e T ->
      has_type CT Gamma h (Return e) T
(* ObjId *)
  | T_ObjId : forall h Gamma CT o cls_name F lo cls_def,
      Some cls_def = CT(cls_name) ->
      h(o) = Some (Heap_OBJ cls_def F lo) ->
      has_type CT Gamma h (ObjId o) (classTy cls_name)
(* NPE *)
  | T_NPE : forall h Gamma CT T,
      has_type CT Gamma h NPE T
(* runtime labeled data *)
  | T_v_l : forall h Gamma lb CT v T,
      has_type CT Gamma h (l lb)  LabelTy ->
      has_type CT Gamma h v  T ->
      has_type CT Gamma h (v_l v lb) (LabelelTy T)
(* runtime labeled data *)
  | T_v_opa_l : forall h Gamma lb CT v T,
      has_type CT Gamma h (l lb)  LabelTy ->
      has_type CT Gamma h v  T ->
      has_type CT Gamma h (v_opa_l v lb) (OpaqueLabeledTy T).


Definition empty_heap : heap := fun _ => None.

Fixpoint field_lookup (f : id) (fields : list field) :=
  match fields with 
    | nil => false
    | (fd cn h :: t) => if beq_id h f then true else field_lookup f t
  end. 
   
Inductive wfe_fields : (list field) -> FieldMap -> Prop  :=
  | empty_fields_wfe : wfe_fields nil empty_field_map 
  | fields_wfe : forall fm v h t cn x,
      wfe_fields t fm -> 
      h = fd cn x ->
      fm(x) = Some v ->
      wfe_fields (cons h t) fm.


(*
Inductive wfe_heap : Class_table -> typing_context -> heap -> Prop :=
  | empty_heap_wfe : forall ct ctx, wfe_heap ct ctx empty_heap
  | heap_wfe : forall h h' cls_def F cn ct gamma fields newHo o lo,
        (wfe_heap ct gamma h /\ h(o) = None)
        -> newHo = Some (Heap_OBJ cls_def F lo)
        -> Some cls_def  = ct cn
        -> fields = (find_fields cls_def)
        -> (forall f cls', type_of_field fields f = Some cls' -> exists v, F(f) = Some v )
        -> h' = (fun x' => if beq_oid o x' then newHo else h x')
        -> wfe_heap ct gamma h'.
*)

Inductive wfe_heap : Class_table -> typing_context -> heap -> Prop :=
  | empty_heap_wfe : forall ct ctx, wfe_heap ct ctx empty_heap
  | heap_wfe : forall h h' o cls_def F cn ct gamma fields ho lo,
        h(o) = None ->
        wfe_heap ct gamma h ->
        ho = Some (Heap_OBJ cls_def F lo) ->
        h' = (fun x' => if beq_oid o x' then ho else (h x')) ->
        (* cls = class_def cn field_defs method_defs-> *)
        Some cls_def  = ct cn ->
        fields = (find_fields cls_def) ->
        (forall f cls', type_of_field fields f = Some cls' -> exists v, F(f) = Some v)->
        (exists o', h' o' = None) ->
        wfe_heap ct gamma h'.


Lemma some_eq : forall cls_def F lo cls_def' F' lo',
  Some (Heap_OBJ cls_def F lo) = Some (Heap_OBJ cls_def' F' lo') ->
  cls_def = cls_def' /\ F = F'.
Proof with auto. 
  intros. inversion H. auto. 
Qed.  


Lemma field_val_of_heap_obj : forall h o gamma CT cls_def F lo cls' fields,
  wfe_heap CT gamma h -> 
  h(o) = Some (Heap_OBJ cls_def F lo) ->
  fields = (find_fields cls_def) ->
  forall f, type_of_field fields f = Some cls' -> exists v, F(f) = Some v.
  (*(type_of_field fields_def fname) = Some f_def->*)

Proof with auto.
  intros. induction H. inversion H0. case_eq (beq_oid o0 o). intro.
  rewrite -> H5 in H0. rewrite -> H10 in H0. subst. inversion H0. subst.
  apply H8 with (f:=f) (cls':=cls'). assumption.
  intros. rewrite -> H5 in H0. rewrite -> H10 in H0. apply IHwfe_heap. assumption.

Qed.

(*
Inductive wfe_heap : Class_table -> typing_context -> heap -> Prop :=
  | empty_heap_wfe : forall ct ctx, wfe_heap ct ctx empty_heap
  | heap_wfe : forall h o cls F cn field_defs method_defs ct ctx h' lo,
      h(o) = Heap_OBJ cls F lo ->
      cls = class_def cn field_defs method_defs->
      Some cls  = ct cn ->
      F (x) ->
      h' = (add_heap_obj h o (Heap_OBJ cls F lo)) ->
      wfe_heap ct ctx h'.
*)


Lemma empty_heap_empty :
  ~ exists x cls F lo, empty_heap x = Some (Heap_OBJ cls F lo).
Proof with auto.
  intros contra.
  inversion contra.
  auto. destruct H. destruct H. destruct H. inversion H.
Qed.

Lemma heap_consist_ct : forall h o ct ctx cls F lo, 
  wfe_heap ct ctx h -> 
  h(o) = Some (Heap_OBJ cls F lo) ->
  exists cn cls_def, ct cn = Some (cls_def).
Proof with auto.
  intros. inversion H.  
  - subst. inversion H0. 
  - subst. exists cn0. exists cls_def. auto.
Qed.

Lemma ct_consist_heap : forall h o ct ctx cls F lo, 
  wfe_heap ct ctx h -> 
  
  h(o) = Some (Heap_OBJ cls F lo) ->
  exists cn field_defs method_defs, ct cn = Some (class_def cn field_defs method_defs).

Fixpoint variable_exists (s : stack) (x : id) :=
  match s with 
    | nil => false
    | cons (Labeled_frame lb sf) s' => match (sf x) with 
                                        | None => variable_exists s' x
                                        | Some v => true
                                        end
  end.

Inductive wfe_stack_frame : heap -> labeled_stack_frame -> Prop :=
  | stack_frame_wfe : forall h lsf sf x v o lb cls_def F lo,
        lsf = Labeled_frame lb sf ->
        sf x = Some v ->
        v = null \/ ((v = ObjId o) -> h(o) = Some (Heap_OBJ cls_def F lo)) \/ v = l lb ->
        wfe_stack_frame h lsf. 


Inductive wfe_stack : Class_table -> typing_context -> heap -> stack -> Prop :=
  | empty_stack_wfe : forall ct gamma h,
        wfe_heap ct gamma h -> 
        h = empty_heap ->
        gamma = empty_context -> 
        wfe_stack ct gamma h nil
  | stack_wfe : forall s ct h gamma x T s' lb sf cls_def gamma' v v', 
        s = cons (Labeled_frame lb sf) s'->
        wfe_stack ct gamma h s' ->
        wfe_heap ct gamma h ->
        wfe_stack_frame h ((Labeled_frame lb sf)) ->
        gamma x = None ->
        variable_exists s' x = false ->
        sf x = Some v ->
        sf (Id "this") = Some v' ->
        gamma'= (fun x' => if beq_id x x' then (Some (classTy T)) else (gamma x)) ->
        ct T = Some cls_def -> 
        wfe_stack ct gamma' h s.

Inductive wfe : Class_table -> typing_context -> Sigma -> Prop :=
  | wfe_sigma : forall sigma s h ct gamma ,
                sigma = SIGMA s h ->
                wfe_heap ct gamma h ->
                wfe_stack ct gamma h s -> 
                wfe ct gamma sigma.

Lemma wfe_sigma_s_h : forall sigma s h ct gamma, 
  sigma = SIGMA s h ->  wfe ct gamma sigma 
      -> wfe_stack ct gamma h s /\ wfe_heap ct gamma h.
Proof with auto. 
  intros. inversion H0. subst. inversion H1. subst. split; auto.
Qed.


Lemma string_eq : forall n1 n2, n1 = n2 -> Id n1 = Id n2.
Proof with eauto.
  intros. rewrite -> H. auto.
Qed. 

Check f_equal.

Lemma beq_equal : forall x x', beq_id x x' = true -> x' = x.
Proof.
   intros. unfold beq_id in H. 
  destruct x. destruct x'.  f_equal.
 case_eq (string_dec s s0). 
  - intros. rewrite -> e. auto.
  - intro. intro. rewrite -> H0 in H. inversion H. 
Qed.

Lemma Typed_variable : forall sigma s h ct gamma x T lb sf s',
  sigma = SIGMA s h ->
  wfe_stack ct gamma h s ->
   gamma x = Some T -> 
   s = cons (Labeled_frame lb sf) s' -> 
   exists v, sf x = Some v.
Proof with eauto.
  intros. inversion H0.
  + subst. inversion H9.
  + subst. case_eq (beq_id x0 x). intros. rewrite -> H in H1. inversion H1. subst. - exists v. rewrite <- H9. 
        inversion H3. subst. f_equal. apply beq_equal. assumption.
 - intros. rewrite -> H in H1. rewrite -> H7 in H1. inversion H1.  
Qed.


Lemma wfe_oid : forall o ct gamma s h sigma cls_def cn, 
  sigma = SIGMA s h ->
  wfe_stack ct gamma h s ->
  (has_type ct gamma h (ObjId o) (classTy cn)) -> ct cn = Some cls_def 
    -> exists fieldsMap lb, h(o) = Some (Heap_OBJ cls_def fieldsMap lb).
Proof with auto. 
  intros. inversion H0. 
    - inversion H1. subst. inversion H16.
    - inversion H1. subst. exists F. rewrite <- H22 in H2. inversion H2. exists lo. rewrite -> H3 in H23. assumption.  
Qed.

Definition val_option_type (input : option tm) : tm :=
  match input with 
    | Some v => v
    | None => null
  end.

Lemma excluded_middle_opaqueLabel : forall e, (exists t, e = unlabelOpaque t) \/ (forall t, ~ (e = unlabelOpaque t)).
Proof with eauto.
  intros. case e. 
right. intro.  intros contra. inversion contra.
right. intro.  intros contra. inversion contra.
right. intro.  intros contra. inversion contra.
right. intro.  intros contra. inversion contra.
right. intro.  intros contra. inversion contra.
right. intro.  intros contra. inversion contra.
right. intro.  intros contra. inversion contra.
right. intro.  intros contra. inversion contra.
right. intro.  intros contra. inversion contra.

left. exists t. auto. 
right. intro.  intros contra. inversion contra.
right. intro.  intros contra. inversion contra.
right. intro.  intros contra. inversion contra.
right. intro.  intros contra. inversion contra.
right. intro.  intros contra. inversion contra.
right. intro.  intros contra. inversion contra.
right. intro.  intros contra. inversion contra.
right. intro.  intros contra. inversion contra.
right. intro.  intros contra. inversion contra.
right. intro.  intros contra. inversion contra.
right. intro.  intros contra. inversion contra.
Qed.

Lemma excluded_middle_returnT : forall e, (exists t, e = Return t) \/ (forall t, ~ (e = Return t)).
Proof with eauto.
  intros. case e. 
right. intro.  intros contra. inversion contra.
right. intro.  intros contra. inversion contra.
right. intro.  intros contra. inversion contra.
right. intro.  intros contra. inversion contra.
right. intro.  intros contra. inversion contra.
right. intro.  intros contra. inversion contra.
right. intro.  intros contra. inversion contra.
right. intro.  intros contra. inversion contra.
right. intro.  intros contra. inversion contra.
right. intro.  intros contra. inversion contra.
right. intro.  intros contra. inversion contra.
right. intro.  intros contra. inversion contra.
right. intro.  intros contra. inversion contra.
right. intro.  intros contra. inversion contra.
right. intro.  intros contra. inversion contra.
right. intro.  intros contra. inversion contra.
left. exists t.  auto. 
right. intro.  intros contra. inversion contra.
right. intro.  intros contra. inversion contra.
right. intro.  intros contra. inversion contra.
right. intro.  intros contra. inversion contra.
Qed.


Theorem progress : forall t T sigma gamma CT s h, 
  sigma = SIGMA s h ->  wfe_heap CT gamma h -> wfe_stack CT gamma h s -> 
  has_type CT gamma h t T -> value t \/ exists t' sigma', t / sigma ==> t' / sigma'.
Proof with auto.
  intros t T sigma gamma CT s h.
  intros. 

  induction H2. 
(* TVar *)
- right. 
      inversion H1. + subst. inversion H2.
                    + subst. exists v. exists (SIGMA (Labeled_frame lb sf :: s') h).

      apply ST_var with 
      (id:=x) (lb:=lb) (sf:=sf) (lsf:=Labeled_frame lb sf) (v:=v) 
      (sigma:=(SIGMA (Labeled_frame lb sf :: s') h)) (s':=s') (s:=(Labeled_frame lb sf :: s')) (h:=h).
      auto. auto. auto. 
      case_eq (beq_id x0 x). intro. apply beq_equal with (x:=x0) (x':=x) in H. subst. auto.
      intro. rewrite -> H in H2. rewrite -> H7 in H2. inversion H2.   
(* null *)
-  left. apply v_null.
(* field access *)
- right. 
    destruct IHhas_type. auto. auto. apply H1. 
    + inversion H6. rewrite <- H7 in H2. 
      assert (exists F lb, h(o) = Some (Heap_OBJ cls_def F lb)).
       apply wfe_oid with (o:=o) (ct:=CT) (gamma:=Gamma) (s:=s) (h:=h) 
                          (sigma:=sigma) (cls_def:=cls_def) (cn:=clsT). auto. auto. auto. auto. 
       destruct H8 as [F]. destruct H8 as [lb].
      assert (exists v, F(f) = Some v).
      apply field_val_of_heap_obj with (h:=h) (o:=o) (gamma:=Gamma) (CT:=CT) 
                              (cls_def:=cls_def) (F:=F) (lo:=lb) (cls':=cls') (fields:=fields_def).
      auto. auto. auto. auto. auto. 
      destruct H9 as [v].
      remember (join_label lb (current_label sigma)) as l'.
      remember (update_current_label s l') as s'.
      remember (SIGMA s' (get_heap sigma)) as sigma'.
            exists v. exists sigma'. apply ST_fieldRead2 with 
            (sigma:=sigma) (sigma':=sigma') (o:=o) (s:=s) (h:=h) (fname:=f) (lb:=lb) 
            (cls:=cls_def) (fields:=F) (v:=v) (l':=l') (s':=s'). 
            auto. auto. auto.            auto. auto. auto. 
    (* call field access on null point object *)
    exists NPE. exists sigma. apply ST_fieldReadException.
    (* label is primitive: calling field access is not valid *)
    rewrite <- H7 in H2. inversion H2.
   
     (* call field access on labeled value*)
    {rewrite <- H8  in H2. inversion H2. }
    
     (* call field access on opaque label value*)
    {rewrite <- H8  in H2. inversion H2. }

     (* context rule *)
    + { destruct H6 as [e']. destruct H6 as [sigma'].
    exists (FieldAccess e' f). exists sigma'.
    apply ST_fieldRead1 with (sigma:=sigma) (sigma':=sigma') (e:=e) (e':=e') (f:=f). assumption. }

(* method call *)
- right.
   destruct IHhas_type1. auto. auto. auto. 
       + inversion H5. rewrite <- H6 in H2_. inversion H2_.
          (* case analysis for argument: if the argument is a value *)
             destruct IHhas_type2. auto. auto. auto. subst. 
            remember (sf_update (sf_update empty_stack_frame (Id "this") (ObjId o)) arg_id argu) as sf. 
            remember (SIGMA s h ) as sigma.
            remember (current_label sigma) as l.
            remember (Labeled_frame l sf) as lsf. 
            remember (cons lsf s) as s'.
            remember (SIGMA s' (get_heap sigma)) as sigma'.
            exists body. exists sigma'.
            apply ST_MethodCall3 with (sigma:=sigma) (sigma':=sigma') (o:=o) (s:=s) (h:=h) (cls:=cls_def) (fields:=F) 
                                       (v:=argu) (lx:=lo) (l:=l) 
                                       (theta:=lsf) (s':=s') (sf:=sf) (lsf:=lsf) (arg_id:=arg_id) 
                                        (cls_a:=cls_a) (body:=body) (meth:=meth) (returnT:=returnT); auto.
            rewrite <- H12 in H2. inversion H2. rewrite <- H13; auto. 
          (* case analysis for argument, if the argument is not a value *)
            subst. 
                destruct H14 as [t']. destruct H as [sigma'].
                pose proof (excluded_middle_opaqueLabel argu).
                destruct H4.
                  (* case for argu = unlabelOpaque t *)
                  destruct H4 as [t]. 
                  rewrite -> H4 in H. inversion H. subst. 
                  exists (MethodCall (ObjId o) meth (unlabelOpaque e')).
                  exists (sigma').
                  apply ST_MethodCall2 with (sigma:=(SIGMA s h)) (sigma':=sigma') 
                                            (v:=(ObjId o)) (e:=unlabelOpaque t) (e':=unlabelOpaque e') (id:=meth).
                  intros. subst. intro contra. inversion contra. rewrite -> H9 in H. inversion H4.
                      rewrite <- H8 in H; subst; inversion H7. auto.  subst. inversion H7.  subst.
                      inversion H7. subst. inversion H7.   
                      assumption. apply v_oid. 
                      subst. 
                      remember (SIGMA s h ) as sigma.
                      remember (sf_update (sf_update empty_stack_frame (Id "this") (ObjId o)) arg_id t') as sf.
                      remember (join_label lb (current_label sigma)) as l'. 
                      remember (Labeled_frame l' sf) as lsf. 
                      remember (cons lsf s) as s'.
                      remember (SIGMA s' (get_heap sigma)) as sigma''.
                      exists body. exists sigma''. 
                      apply ST_MethodCall_unlableOpaque with (sigma:=sigma) (sigma':=sigma'') (o:=o) (s:=s) (h:=h) 
                                            (cls:=cls_def0) (fields:=F) (v:=t') (lx:=lo) (l':=l') (lb:=lb) (s':=s')
                                           (sf:=sf) (lsf:=lsf) (arg_id:=arg_id) (cls_a:=cls_a) (body:=body) 
                                           (meth:=meth) (returnT:=returnT).
                      auto. auto. auto. auto. auto. auto. subst. 
                      rewrite <- H12 in H2. inversion H2. rewrite <- H6. rewrite -> H3; auto. 
                      auto.
                  (*exception case *)
                  subst. exists NPE. exists (SIGMA s h).
                  apply ST_MethodCallOpaqueDataException with (sigma:=(SIGMA s h)) (o:=o).  

                  (* case for argu <> unlabelOpaque t *)
                  exists (MethodCall (ObjId o) meth t'). exists sigma'. 
                  apply ST_MethodCall2 with (sigma:=(SIGMA s h)) (sigma':=sigma') (v:=((ObjId o))) 
                                            (e:=argu) (e':=t') (id:=meth).
                  intro. intro. intro. 

                  assert (argu <> unlabelOpaque t).  apply (H4 t). apply (H4 t). auto. apply v_oid.
                  (* case for argu <> unlabelOpaque t exception *)
                  subst. exists NPE. exists (SIGMA s h). 
              apply ST_MethodCallException with (sigma:=(SIGMA s h)) (v:=argu) (meth:=meth).

                  subst. inversion H2_.
                rewrite <- H7 in H2_. inversion H2_.                 rewrite <- H7 in H2_. inversion H2_. 
      +  destruct H5 as [t']. destruct H5 as [sigma']. exists (MethodCall t' meth argu). exists (sigma').   
                  apply ST_MethodCall1 with (sigma:=sigma) (sigma':=sigma') (e2:=argu) (e:=e) (e':=t') (id:=meth). apply H5.

(* new expression *)
- right. inversion H0. 
    assert (exists o, empty_heap o = None). 
      unfold empty_heap. auto. exists (OID 0). auto. 
      destruct H6 as [o]. 

      remember (init_field_map (find_fields cls_def) empty_field_map) as F.
      remember (current_label sigma) as lb. 
      remember  (add_heap_obj h o (Heap_OBJ cls_def F lb)) as h'.
      remember (SIGMA s h') as sigma'.
      exists (ObjId o). exists sigma'. apply ST_NewExp with (sigma:=sigma) (sigma':=sigma') (F:=F) (o:=o) (h:=h) (cls:=cls_def)
                                                                                (h':=h') (s:=s) (lb:=lb) (cn:=cn0).
      subst; auto. rewrite <- H5.  auto.  auto. auto. auto.  auto. 
      
      remember (current_label sigma) as lb. 
      destruct H10. 
      remember (init_field_map (find_fields cls_def) empty_field_map) as F'.
      remember (add_heap_obj h x (Heap_OBJ cls_def F' lb)) as h''.
      remember (SIGMA s h'') as sigma''.
      exists (ObjId x). exists sigma''. 

      apply ST_NewExp with (sigma:=sigma) (sigma':=sigma'') (F:=F') (o:=x) (h:=h) (cls:=cls_def)
                                                                                (h':=h'') (s:=s) (lb:=lb) (cn:=cn0).
      auto. auto.  auto.  auto. auto. auto. 

(* label *)
- left. apply  v_label.


(* label Data *)
- right. destruct IHhas_type2. auto. auto. auto. 
            destruct IHhas_type1. auto. auto. auto. 
            
            (* subgoal #1 *)
           exists  (v_l e lb). exists sigma.
                apply ST_LabelData2 with (sigma:=sigma) (lb:=lb) (v:=e). subst. auto.  auto.

            (*
                  inversion H2. 
                 (*subsubgoal #1*)
                exists  (v_l (ObjId o) lb). exists sigma.
                apply ST_LabelData3 with (sigma:=sigma) (lb:=lb) (v:=(ObjId o)). subst. auto.  auto.
                 (*subsubgoal #2*)
                exists NPE. exists sigma. apply ST_LabelDataException with (sigma:=sigma) (lb:=lb).
                 (*subsubgoal #3*)
                exists  (v_l (l lb0) lb). exists sigma.
                apply ST_LabelData3 with (sigma:=sigma) (lb:=lb) (v:=(l lb0)). subst. auto.  auto.
                 (*subsubgoal #4*)
            *)

            (* subgoal #2 *)  
                destruct H3 as [t']. destruct H3 as [sigma']. inversion H3. 

            (* subgoal #3 *)
            destruct IHhas_type1. auto. auto. auto. 
                   (* subgoal #4 *)
                    destruct H2 as [t']. destruct H2 as [sigma'].
                    exists (labelData t' lb). exists sigma'. 
                    apply ST_LabelData1 with (sigma:=sigma) (sigma':=sigma') (e:=e) (e':=t') (lb:=lb).
                    auto. 
                   (* subgoal #5 *)
                    destruct H2 as [t']. destruct H2 as [sigma']. 
                    exists (labelData t' lb). exists sigma'.
                    apply ST_LabelData1 with (sigma:=sigma) (sigma':=sigma') (e:=e) (e':=t') (lb:=lb).
                    auto.

(* unlabel : *)
- right. 
            destruct IHhas_type. auto. auto. auto. 
             (* subgoal #1 *)
                + inversion H3. rewrite <- H4 in H2. inversion H2. 
                    exists NPE. exists sigma.  apply ST_unlabelDataException with (sigma:=sigma).
                    rewrite <- H4 in H2.  inversion H2. 

             (* subgoal #2 *)
                remember ( join_label lb (current_label sigma)) as l'.
                remember (update_current_label s l') as s'.
                remember (SIGMA s' (get_heap sigma)) as sigma'.
                exists v. exists sigma'. 
                apply ST_unlabel2 with (sigma:=sigma) (s':=s') (sigma':=sigma') (l':=l') (s:=s) (h:=h) (lb:=lb) (v:=v). 
                auto. auto. auto. auto. auto.

            (* subgoal #3 *)
                rewrite <- H5 in H2.  inversion H2. 

             (* subgoal #4 *)
                + destruct H3 as [t']. destruct H3 as [sigma']. 
                    exists  (unlabel t'). exists sigma'. apply ST_unlabel1 with (sigma:=sigma) (sigma':=sigma') (e:=e) (e':=t'). auto. 
          
(* label Of *)
(* same issue as above, we may need to add (v_l v lb) as a value*)
- right. 
         destruct IHhas_type. auto. auto. auto. 
            (* subgoal #1 *)
                + inversion H3. rewrite <- H4 in H2. inversion H2. 
                    exists NPE. exists sigma.  apply ST_labelOfDataException with (sigma:=sigma).
                    rewrite <- H4 in H2.  inversion H2.
                    
                   exists (l lb). exists (sigma). apply ST_labelof2 with (v:=v) (lb:=lb).

                    rewrite <- H5 in H2. inversion H2. 
             (* subgoal #2 *)
                + destruct H3 as [t']. destruct H3 as [sigma']. 
                    exists  (labelOf t'). exists sigma'. apply ST_labelof1 with (sigma:=sigma) (sigma':=sigma') (e:=e) (e':=t'). auto. 

(* unlabel opaque *)
- right. 
         destruct IHhas_type. auto. auto. auto. 
            (* subgoal #1 *)
                + inversion H3. rewrite <- H4 in H2. inversion H2. 
                    exists NPE. exists sigma.  apply ST_unlabel_opaqueDataException with (sigma:=sigma).
                    rewrite <- H4 in H2.  inversion H2.
              
                     rewrite <- H5 in H2. inversion H2. 
 
                remember ( join_label lb (current_label sigma)) as l'.
                remember (update_current_label s l') as s'.
                remember (SIGMA s' (get_heap sigma)) as sigma'.
                exists v. exists sigma'. 
                apply ST_unlabel_opaque2 with (sigma:=sigma) (s':=s') (sigma':=sigma') (l':=l') (s:=s) (h:=h) (lb:=lb) (v:=v). 
                auto. auto. auto. auto. 

             (* subgoal #2 *)
                + destruct H3 as [t']. destruct H3 as [sigma']. 
                    exists  (unlabelOpaque t'). exists sigma'. apply ST_unlabel_opaque1 with (sigma:=sigma) (sigma':=sigma') (e:=e) (e':=t'). auto. 

(* opaque call *)
- right.  destruct IHhas_type. auto. auto. auto.    
            exists e. exists sigma. apply ST_opaquecall_val2 with (v:=e) (sigma:=sigma). auto.

            subst. destruct H3 as [t']. destruct H as [sigma'].
                pose proof (excluded_middle_returnT e).
                destruct H3.
                  (* case for argu = return t *)
                  destruct H3 as [t].
                  destruct t.
                  rewrite -> H3 in H. 
                  inversion H.  subst. 
                  exists (opaqueCall(Return e')). exists sigma'.
                  apply ST_opaquecall_return1 with (sigma:=(SIGMA s h)) (sigma':=sigma') (e:= (Tvar i)) (e':= e').
                  auto. 

                  rewrite <- H11 in H. inversion H5. 

                  (* subgoal *)
                  subst. exists NPE. exists (SIGMA s h). 
                  apply ST_opaquecall_return3 with (sigma:=(SIGMA s h)).
                  (* subgoal field access*)
                  subst. 
                  exists (opaqueCall(t') ). exists sigma'.
                  apply ST_opaquecall1 with (sigma:=(SIGMA s h)) (sigma':=sigma') (e:= Return (FieldAccess t i) ) (e':= t').
                  intros. intro contra. inversion contra. rewrite <- H5 in H3.  inversion H3.         auto.
                  (* method call *)
                  subst. 
                  exists (opaqueCall(t') ). exists sigma'.
                  apply ST_opaquecall1 with (sigma:=(SIGMA s h)) (sigma':=sigma') (e:= Return (MethodCall t1 i t2) ) (e':= t').
                  intros. intro contra. inversion contra. rewrite <- H5 in H3.  inversion H3.         auto.
                  (* new expression *)
                  subst. 
                  exists (opaqueCall(t') ). exists sigma'.
                  apply ST_opaquecall1 with (sigma:=(SIGMA s h)) (sigma':=sigma') (e:= Return (NewExp c) ) (e':= t').
                  intros. intro contra. inversion contra. rewrite <- H5 in H3.  inversion H3.         auto.
                  (* return label *)
                  subst. 
                  exists (opaqueCall(t') ). exists sigma'.
                  apply ST_opaquecall1 with (sigma:=(SIGMA s h)) (sigma':=sigma') (e:= Return (NewExp c) ) (e':= t').
                  intros. intro contra. inversion contra. rewrite <- H5 in H3.  inversion H3.         auto.


    destruct H3 as [t].
                  destruct t.
                  rewrite -> H3 in H. 
                  inversion H.  subst. 
                  exists (opaqueCall(Return e')). exists sigma'.
                  apply ST_opaquecall_return1 with (sigma:=(SIGMA s h)) (sigma':=sigma') (e:= (Tvar i)) (e':= e').
                  auto. 





                  apply ST_var with (id:=i) (sigma:=sigma) (s:=s) (h:=h) (lb) sf lsf v s',

                  rewrite -> H3 in H.
                  case (value t).
                  inversion t. 
 
 inversion H. subst. 
                  exists (opaqueCall(Return e')).
                  exists (sigma').
                  apply ST_opaquecall_return1 with (sigma:=(SIGMA s h)) (sigma':=sigma') 
                                            (e:=t) (e':=e'). auto.
      
                  subst. 
 
                  intros. subst. intro contra. inversion contra. rewrite -> H9 in H. inversion H4.
                      rewrite <- H8 in H; subst; inversion H7. auto.  subst. inversion H7.  subst.
                      inversion H7. subst. inversion H7.   
                      assumption. apply v_oid. 
                      subst. 
                      remember (SIGMA s h ) as sigma.
                      remember (sf_update (sf_update empty_stack_frame (Id "this") (ObjId o)) arg_id t') as sf.
                      remember (join_label lb (current_label sigma)) as l'. 
                      remember (Labeled_frame l' sf) as lsf. 
                      remember (cons lsf s) as s'.
                      remember (SIGMA s' (get_heap sigma)) as sigma''.
                      exists body. exists sigma''. 
                      apply ST_MethodCall_unlableOpaque with (sigma:=sigma) (sigma':=sigma'') (o:=o) (s:=s) (h:=h) 
                                            (cls:=cls_def0) (fields:=F) (v:=t') (lx:=lo) (l':=l') (lb:=lb) (s':=s')
                                           (sf:=sf) (lsf:=lsf) (arg_id:=arg_id) (cls_a:=cls_a) (body:=body) 
                                           (meth:=meth) (returnT:=returnT).
                      auto. auto. auto. auto. auto. auto. subst. 
                      rewrite <- H12 in H2. inversion H2. rewrite <- H6. rewrite -> H3; auto. 
                      auto.
                  (*exception case *)
                  subst. exists NPE. exists (SIGMA s h).
                  apply ST_MethodCallOpaqueDataException with (sigma:=(SIGMA s h)) (o:=o).  

                  (* case for argu <> unlabelOpaque t *)
                  exists (MethodCall (ObjId o) meth t'). exists sigma'. 
                  apply ST_MethodCall2 with (sigma:=(SIGMA s h)) (sigma':=sigma') (v:=((ObjId o))) 
                                            (e:=argu) (e':=t') (id:=meth).
                  intro. intro. intro. 

                  assert (argu <> unlabelOpaque t).  apply (H4 t). apply (H4 t). auto. apply v_oid.
                  (* case for argu <> unlabelOpaque t exception *)
                  subst. exists NPE. exists (SIGMA s h). 
              apply ST_MethodCallException with (sigma:=(SIGMA s h)) (v:=argu) (meth:=meth).

                  subst. inversion H2_.
                rewrite <- H7 in H2_. inversion H2_.                 rewrite <- H7 in H2_. inversion H2_. 
            



(*

(* unlabel opaque*)
  (* context rule *)
  | ST_unlabel_opaque1 : forall sigma sigma' e e',
       e / sigma ==>  e' / sigma' -> 
      (unlabelOpaque e) / sigma ==> (unlabelOpaque e') / sigma'
  (* unlabel opaque *)
  | ST_unlabel_opaque2 : forall sigma v lb l' sigma' s h,
      sigma = SIGMA s h ->
      l' = join_label lb (current_label sigma) ->
      value (v_opa_l v (l lb)) ->
      (unlabelOpaque ((v_opa_l v (l lb)))) / sigma ==> v / sigma'
*)

Theorem preservation : forall t t' T sigma sigma', 
    gamma |- t \in T ->
    t / st ==> t' / st' ->
    gamma |- t' \in T.


Proof.
Qed.




