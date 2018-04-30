Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.

Add LoadPath "/Users/llama_jian/Develop/HarvardPLCIFC".

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
  | If : id -> id -> tm -> tm -> tm 
  | Sequence : tm -> tm -> tm
  | Return : tm -> tm

(* special terms *)
  | ObjId: oid -> tm
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
(* skip is not a terminal *)
  | v_none : 
      value Skip
  | v_null :
      value null
  | v_label :
      forall lb, value (l lb)
  | v_labeled : forall v lb,
     (* value v ->*)
      value (v_l v lb)
  | v_opa_labeled : forall v lb,
     (* value v ->*)
      value (v_opa_l v lb).

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
Definition main_labeled_stack_frame : labeled_stack_frame := (Labeled_frame L_Label empty_stack_frame).

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

(*Definition heap := oid -> (option heapObj).*)

Inductive Heap_entry : Type := 
  | heap_entry : oid -> heapObj -> Heap_entry. 
  
Notation "( oid , obj )" := (heap_entry oid obj).

Definition heap := list Heap_entry.

(* comparison of identifiers *)
Definition beq_oid x y :=
  match x,y with
    | OID n1, OID n2 => if beq_nat n1 n2 then true else false
  end.

Fixpoint update_heap_obj (h : heap) (o : oid) (ho : heapObj) :=
   match h with 
      | nil => nil
      | head :: t => match head with 
                            | ( o0 , heap_obj ) => if beq_oid o o0 then cons (o , ho) t
                                                                  else head :: update_heap_obj t o ho
                      end
   end. 

Fixpoint lookup_heap_obj (h : heap) (o : oid) : option heapObj :=
   match h with 
      | nil => None
      | h :: t => match h with 
                            | ( o0 , ho ) => if beq_oid o o0 then Some ho
                                                                  else lookup_heap_obj t o
                      end
   end. 

Definition get_fresh_oid (h:heap) :=
    match h with 
     | nil => (OID 1)
     | h0 :: t0 => match h0 with 
                        | ((OID n) , _) => (OID (n+1)) 
                          end
    end.


Definition add_heap_obj (h: heap) (o:oid) (ho : heapObj) :=
  cons (o, ho) h.

Inductive Sigma := 
  | SIGMA : stack -> heap -> Sigma.

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

Definition current_label (sigma : Sigma) : Label :=
  get_current_label (get_stack sigma).

Definition update_current_label (s : stack) (lb : Label) := 
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
                  | m_def cls m' cls_a arg_id body => if beq_id m m' then Some (m_def cls m' cls_a arg_id  (Return body)) else find_method_body t m
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
    | (fd cls h) :: t =>  (fun x' => if beq_id h x' then Some null else (init_field_map t fm) x')
  end.

Check init_field_map.

Lemma empty_fields : forall fields F cls', 
  F = init_field_map fields empty_field_map ->
  (forall f, type_of_field fields f = Some cls' ->
  F f = Some null).
Proof.
  intro. intro. intro. intro. generalize dependent F.  
  induction fields. 
  - intros.   inversion H0.
  - intro F. intro Hy. 
     induction a. intro f. intro. rewrite Hy.
     case_eq (beq_id i f). intro.
     unfold init_field_map. rewrite H0. auto. 
     intro. unfold init_field_map. rewrite H0. fold init_field_map. 
     apply IHfields with (F:=(init_field_map fields empty_field_map))(f:=f).
     auto.   unfold type_of_field in H. rewrite H0 in H. fold type_of_field in H.
    auto.  
Qed.  


Inductive config := 
  | Config : tm -> Sigma -> config
  | Error_state : config
  | Terminal : config. 
Hint Constructors config.

Reserved Notation "c '==>' c'"
  (at level 40, c' at level 39).





Inductive reduction : config -> config -> Prop :=
(* variabel access *)
  | ST_var : forall id sigma s h lb sf lsf v s',
      sigma = SIGMA s h ->
      s = cons lsf s' ->
      lsf = Labeled_frame lb sf ->
      Some v = sf(id) ->
      Config (Tvar id) sigma ==> Config v sigma

(* field read *)
  (* context rule *)
  | ST_fieldRead1 : forall sigma sigma' e e' f,
      Config e sigma ==>  Config e' sigma' -> 
      Config (FieldAccess e f) sigma ==> Config (FieldAccess e' f) sigma'
  (* normal field access *)
  | ST_fieldRead2 : forall sigma sigma' o s h fname lb cls fields v l' s',
      sigma = SIGMA s h ->
      Some (Heap_OBJ cls fields lb) = lookup_heap_obj h o -> 
      Some v = fields(fname) -> 
      l' = join_label lb (current_label sigma) ->
      s' = update_current_label s l'-> 
      sigma' = SIGMA s' h ->
      Config (FieldAccess (ObjId o) fname) sigma ==> Config v sigma'
  (* null pointer exception for field access *)
  | ST_fieldReadException : forall sigma f ,
      Config (FieldAccess null f) sigma ==> Error_state
  | ST_fieldRead3 : forall sigma e f,
      Config e sigma ==>  Error_state -> 
      Config (FieldAccess e f) sigma ==> Error_state



(* method call *)
  (* context rule: evaluate object target *)
  | ST_MethodCall1 : forall sigma sigma' e e' e2 id,
       Config e sigma ==>  Config e' sigma' -> 
      Config (MethodCall e id e2) sigma ==> Config (MethodCall e' id e2)  sigma'
  (* context rule: evaluate arguments *)
  | ST_MethodCall2 : forall sigma sigma' v e e' id,
      (forall t, value t -> t<> null -> e <> unlabelOpaque t) ->
      Config e sigma ==>  Config e' sigma' -> 
      value v ->
      Config (MethodCall v id e) sigma ==> Config (MethodCall v id e') sigma'
  (* normal method call *)
  | ST_MethodCall3 : forall sigma sigma' o s h cls fields v lx l theta s' sf lsf arg_id cls_a body meth returnT,
      sigma = SIGMA s h ->
      Some (Heap_OBJ cls fields lx) = lookup_heap_obj h o -> 
      Some (m_def returnT meth cls_a arg_id (Return body)) = find_method cls meth -> 
      value v ->
      sf = sf_update empty_stack_frame arg_id v ->
      l = (current_label sigma) ->
      lsf = Labeled_frame l sf ->
      theta = lsf -> 
      s' = cons theta s ->
      sigma' = SIGMA s' (get_heap sigma) ->
      Config (MethodCall (ObjId o) meth v) sigma ==>  Config (Return body) sigma'
  (* null pointer exception for method call *)
  | ST_MethodCallException : forall sigma v meth, 
      Config (MethodCall null meth v) sigma ==> Error_state
  (* context rule error 1*)
  | ST_MethodCall4 : forall sigma e e2 id,
       Config e sigma ==>  Error_state -> 
      Config (MethodCall e id e2) sigma ==> Error_state
  (* context rule error 2*)
  | ST_MethodCall5 : forall sigma v e id,
      (forall t, value t -> t<> null -> e <> unlabelOpaque t) ->
      Config e sigma ==>  Error_state -> 
      value v ->
      Config (MethodCall v id e) sigma ==> Error_state


(* method call with unlabel opaque *)
  | ST_MethodCall_unlableOpaque : forall sigma sigma' o s h cls fields v lx l' lb s' sf lsf arg_id cls_a body meth returnT,
      sigma = SIGMA s h ->
      Some (Heap_OBJ cls fields lx) =lookup_heap_obj h o -> 
      sf = sf_update empty_stack_frame arg_id v ->
      l' = join_label lb (current_label sigma) ->
      lsf = Labeled_frame l' sf ->
      s' = cons lsf s ->
      value v ->
      Some (m_def returnT meth cls_a arg_id  (Return body)) = find_method cls meth ->
      sigma' = SIGMA s' (get_heap sigma) ->
      Config (MethodCall (ObjId o) meth (unlabelOpaque (v_opa_l v lb)))  sigma ==>Config (Return body) sigma'

  (* null pointer exception for method call with unlabel opaque of null data*)
  | ST_MethodCallOpaqueDataException : forall sigma o meth, 
      Config (MethodCall (ObjId o) meth (unlabelOpaque null)) sigma ==> Error_state

(* new expression *)
  | ST_NewExp : forall sigma sigma' h h' s o lb cls_name field_defs method_defs cls F,
      sigma = SIGMA s h->
      lb = (current_label sigma) -> 
      o = get_fresh_oid h ->
      cls = (class_def cls_name field_defs method_defs) ->
      F =  (init_field_map (find_fields cls) empty_field_map) ->
      h' = add_heap_obj h o (Heap_OBJ cls F lb) ->
      sigma' = SIGMA s h' ->
      Config (NewExp cls_name) sigma ==> Config (ObjId o) sigma'


(* label data express *)
  (* context rule *)
  | ST_LabelData1 : forall sigma sigma' e e' lb,
      Config e sigma ==>  Config e' sigma' -> 
      Config (labelData e lb) sigma ==> Config (labelData e' lb) sigma'
  (* label data *)
  | ST_LabelData2 : forall sigma v lb,
      value v ->
      Config (labelData v lb) sigma ==>  Config (v_l v lb)  sigma
  (* label data exception *)
  | ST_LabelDataException : forall sigma lb,
      Config (labelData null lb) sigma ==> Error_state
  (* context rule error*)
  | ST_LabelDataError : forall sigma e lb,
      Config e sigma ==>  Error_state -> 
      Config (labelData e lb) sigma ==> Error_state




(* unlabel *)
  (* context rule *)
  | ST_unlabel1 : forall sigma sigma' e e',
      Config e sigma ==>  Config e' sigma' -> 
      Config  (unlabel e) sigma ==> Config (unlabel e') sigma'
  (* unlabel *)
  | ST_unlabel2 : forall sigma v lb l' sigma' s h s',
      sigma = SIGMA s h ->
      l' = join_label lb (current_label sigma) ->
      s' = update_current_label s l'-> 
      sigma' = SIGMA s' (get_heap sigma) ->
      value v ->
      Config (unlabel (v_l v lb)) sigma ==> Config v sigma'
  (* unlabel data exception *)
  | ST_unlabelDataException : forall sigma,
      Config (unlabel null) sigma ==> Error_state
  (* context rule error*)
  | ST_unlabelContextError : forall sigma  e,
      Config e sigma ==>  Error_state -> 
      Config  (unlabel e) sigma ==> Error_state


(* Label of *)
  (* context rule *)
  | ST_labelof1 : forall sigma sigma' e e',
       Config e sigma ==>  Config e' sigma' -> 
       Config (labelOf e) sigma ==> Config (labelOf e') sigma'
  (* label of  *)
  | ST_labelof2 : forall sigma v lb,
      Config (labelOf (v_l v lb)) sigma ==> Config (l lb) sigma
  | ST_labelOfDataException : forall sigma, 
      Config (labelOf null) sigma ==> Error_state
  (* context rule error*)
  | ST_labelofCtxError : forall sigma e,
       Config e sigma ==>  Error_state -> 
       Config (labelOf e) sigma ==> Error_state

(* unlabel opaque*)
  (* context rule *)
  | ST_unlabel_opaque1 : forall sigma sigma' e e',
      Config e sigma ==>  Config e' sigma' -> 
     Config (unlabelOpaque e) sigma ==>  Config (unlabelOpaque e') sigma'
  (* context rule error*)
  | ST_unlabel_opaque_ctx_error : forall sigma e,
      Config e sigma ==>  Error_state -> 
     Config (unlabelOpaque e) sigma ==>  Error_state
  (* unlabel opaque *)
  | ST_unlabel_opaque2 : forall sigma v lb l' sigma' s h s',
      sigma = SIGMA s h ->
      l' = join_label lb (current_label sigma) ->
      s' = update_current_label s l'-> 
      sigma' = SIGMA s' (get_heap sigma) ->
      Config (unlabelOpaque (v_opa_l v lb)) sigma ==> Config v sigma'
  | ST_unlabel_opaqueDataException : forall sigma, 
      Config (unlabelOpaque null) sigma ==> Error_state

(* Opaque call *)
  (* context rule *)
  | ST_opaquecall1 : forall sigma sigma' e e',
       (forall v, value v -> e <> Return v) ->
       Config e sigma ==>  Config e' sigma' -> 
      Config (opaqueCall e) sigma ==> Config (opaqueCall e') sigma'
  (* context rule error*)
  | ST_opaquecall_ctx_error : forall sigma e,
      Config e sigma ==>  Error_state -> 
     Config  (opaqueCall e) sigma  ==>  Error_state
  (* return context rule*)
  | ST_opaquecall_return1 : forall sigma sigma' e e',
       Config e sigma ==> Config  e' sigma' -> 
      Config (opaqueCall (Return e)) sigma ==> Config (opaqueCall (Return e')) sigma'
  (* return context rule error*)
  | ST_opaquecall_return_error : forall sigma e,
       Config e sigma ==> Error_state -> 
      Config (opaqueCall (Return e)) sigma ==> Error_state


  (* opaque call with value, without method call inside *)
  | ST_opaquecall_val2 : forall sigma v lb,
      (value v) ->
      lb = (current_label sigma) ->
      Config (opaqueCall v) sigma ==>  Config (v_opa_l v lb) sigma  
  (* opaque call with return statement *)
  | ST_opaquecall_return2 : forall sigma sigma' s h lb s' lsf v,
      sigma = SIGMA s h->
      s = cons lsf s' ->
      s' <> nil ->
      lb = (current_label sigma) ->
      sigma' = SIGMA s' h->
      value v ->
      Config (opaqueCall (Return v)) sigma ==> Config (v_opa_l v lb) sigma'
  | ST_opaquecall_return3 : forall sigma,
      Config (opaqueCall (Return null)) sigma ==> Error_state


(* assignment *)
  (* context rule *)
  | ST_assignment1 : forall sigma sigma' e e' id,
       Config e sigma ==> Config e' sigma' -> 
       Config (Assignment id e) sigma ==> Config (Assignment id e') sigma'
  (* context rule error*)
  | ST_assignment_ctx_error : forall sigma e id,
      Config e sigma ==>  Error_state -> 
     Config  (Assignment id e) sigma  ==>  Error_state
  (* assignment *)
  | ST_assignment2 : forall sigma sigma' id v s' s h,
       value v ->
       sigma = SIGMA s h ->
       s' = update_stack_top s id v->
       sigma' = SIGMA s' h ->
       Config (Assignment id v) sigma ==> Config Skip sigma'

(* Field Write *)
  (* context rule 1 *)
  | ST_fieldWrite1 : forall sigma sigma' f e1 e1' e2,
       Config e1 sigma ==> Config e1' sigma' -> 
       Config (FieldWrite e1 f e2) sigma ==> Config (FieldWrite e1' f e2) sigma'
  (* context rule error 1 *)
  | ST_fieldWrite_ctx_error1 : forall sigma f e1 e2,
       Config e1 sigma ==> Error_state -> 
       Config (FieldWrite e1 f e2) sigma ==> Error_state
  (* context rule 2 *)
  | ST_fieldWrite2 : forall sigma sigma' f v e2 e2',
       (forall t, value t -> t<> null -> e2 <> unlabelOpaque t) ->
       value v ->
       Config e2 sigma ==> Config e2' sigma' -> 
       Config (FieldWrite v f e2) sigma ==> Config (FieldWrite v f e2') sigma'
  (* context rule error 2 *)
  | ST_fieldWrite_ctx_error2 : forall sigma f v e2,
       (forall t, value t -> t<> null -> e2 <> unlabelOpaque t) ->
       value v ->
       Config e2 sigma ==> Error_state -> 
       Config (FieldWrite v f e2) sigma ==> Error_state
  (* field write normal *)
  | ST_fieldWrite3 : forall sigma sigma' o s h h' f lb cls F F' v l',
      sigma = SIGMA s h ->
      Some (Heap_OBJ cls F lb) = lookup_heap_obj h o -> 
      F' = fields_update F f v ->
      l' = join_label lb (current_label sigma) ->
      h' = update_heap_obj h o (Heap_OBJ cls F' l') ->
      sigma' = SIGMA s h' ->
      value v->
      Config (FieldWrite (ObjId o) f v) sigma ==> Config Skip sigma'
  (* null pointer exception for field write *)
  | ST_fieldWriteException : forall sigma f v, 
      Config (FieldWrite null f v) sigma ==> Error_state
  (* field write normal *)
  | ST_fieldWrite_opaque : forall sigma sigma' o s h h' f lo cls F F' v l' lb e2,
      e2 = unlabelOpaque (v_opa_l v lb) ->
      sigma = SIGMA s h ->
      Some (Heap_OBJ cls F lo) = lookup_heap_obj h o-> 
      F' = fields_update F f v ->
      l' = join_label lo lb ->
      h' = update_heap_obj h o (Heap_OBJ cls F' l') ->
      sigma' = SIGMA s h' ->
      Config (FieldWrite (ObjId o) f e2) sigma ==> Config Skip sigma'
  | ST_FieldWriteOpaqueDataException : forall sigma o f, 
      Config (FieldWrite (ObjId o) f (unlabelOpaque null)) sigma ==> Error_state

(* return statement *)
  (* context rule*)
  | ST_return1 : forall sigma sigma' e e',
        Config e sigma ==> Config e' sigma' -> 
        Config (Return e) sigma ==> Config (Return e') sigma'
  (* context rule error*)
  | ST_return_ctx_error : forall sigma e,
        Config e sigma ==> Error_state -> 
        Config (Return e) sigma ==> Error_state
  (* return val *)
  | ST_return2 : forall sigma sigma' v s s' s'' h lsf l', 
      value v ->
      sigma = SIGMA s h ->
      s = cons lsf s' ->
      s' <> nil ->
      l' = join_label (get_current_label s) (get_current_label s') ->
      s'' = update_current_label s' l' ->
      sigma' = SIGMA s'' h ->
      Config (Return v) sigma ==> Config v sigma'
  | ST_return_terminal : forall sigma v s h lsf, 
      value v ->
      sigma = SIGMA s h ->
      s = cons lsf nil ->
      Config (Return v) sigma ==> Terminal

(* if statement *)
  | ST_if_b1 : forall sigma s1 s2 s h lsf s' lb sf id1 id2, 
       sigma = SIGMA s h ->
       s = cons lsf s' ->
       lsf = Labeled_frame lb sf ->
       sf(id1) = sf(id2) ->
       Config (If id1 id2 s1 s2) sigma ==> Config s1 sigma
  | ST_if_b2 : forall sigma s1 s2 s h lsf s' lb sf id1 id2, 
       sigma = SIGMA s h ->
       s = cons lsf s' ->
       lsf = Labeled_frame lb sf ->
       sf(id1) <> sf(id2) ->
       Config (If id1 id2 s1 s2) sigma ==> Config s2 sigma
(* sequence *)
   (* context rule *)
  | ST_seq1 : forall sigma s1 s2 s1' sigma', 
    Config s1 sigma ==> Config s1' sigma' -> 
    Config (Sequence s1 s2) sigma ==> Config (Sequence s1' s2) sigma'
  (* context rule error *)   
  | ST_seq_ctx_error : forall sigma s1 s2, 
    Config s1 sigma ==> Error_state -> 
    Config (Sequence s1 s2) sigma ==> Error_state
   (* sequence rule *)
  | ST_seq2 : forall sigma v s , 
    value v->
    Config (Sequence v s) sigma ==> Config s sigma

where "c '==>' c'" := (reduction c c').


Inductive ty : Type :=
  | classTy : cn -> ty 
  | LabelTy : ty
  | LabelelTy : ty -> ty
  | OpaqueLabeledTy : ty -> ty
  | voidTy : ty. 

Definition typing_context := id -> (option ty).
Definition empty_context : typing_context := fun _ => None.

Definition Class_table := cn -> option CLASS.

Definition update_typing (gamma : typing_context) (x:id) (T : ty) : typing_context :=
      fun x' => if beq_id x x' then (Some T) else gamma x. 

Inductive has_type : Class_table -> typing_context -> stack -> heap -> tm -> ty -> Prop :=
(*variable *)
  | T_Var : forall Gamma x T CT s h lsf s' lb sf, 
      s = cons lsf s' ->
      lsf = Labeled_frame lb sf ->
      (exists v, Some v = sf(x)) ->
      Gamma x = Some (classTy T) ->
      has_type CT Gamma s h (Tvar x) (classTy T)
(* null *)
  | T_null : forall Gamma s h T CT, 
      has_type CT Gamma s h null T
(* Field read *)
  | T_FieldAccess : forall Gamma e f cls_def CT clsT cls' h fields_def s,
      has_type CT Gamma s h e (classTy clsT) ->       
      Some cls_def = CT(clsT) ->
      fields_def = (find_fields cls_def) ->
      type_of_field fields_def f = Some cls' ->
      has_type CT Gamma s h (FieldAccess e f) (classTy cls')
(* method call *)
  | T_MethodCall : forall Gamma e meth argu CT s h T returnT cls_def body arg_id arguT para_T cls_a,
      has_type CT Gamma s h e (classTy T) ->
      has_type CT Gamma s h argu arguT ->
      Some cls_def = CT(T) ->
      find_method cls_def meth = Some (m_def returnT meth cls_a arg_id (Return body))  ->
      arguT = para_T ->
      (Gamma arg_id = Some arguT) ->
      has_type CT Gamma s h (body) (classTy returnT) ->
      has_type CT Gamma s h (MethodCall e meth argu) (classTy returnT)
(* new exp *)
  | T_NewExp : forall s h Gamma cls_name CT, 
      (forall field_defs method_defs cls_def, 
      cls_def = class_def cls_name field_defs method_defs  -> 
      CT(cls_name) = Some cls_def )->
      has_type CT Gamma s h (NewExp cls_name) (classTy cls_name)
(* label *)
  | T_label : forall s h Gamma lb CT,
      has_type CT Gamma s h (l lb) LabelTy
(* label data *)
  | T_labelData : forall s h Gamma lb CT e T,
      has_type CT Gamma s h (l lb) LabelTy ->
      has_type CT Gamma s h e T ->
      has_type CT Gamma s h (labelData e lb) (LabelelTy T)
(* unlabel *)
  | T_unlabel : forall s h Gamma CT e T,
      has_type CT Gamma s h e (LabelelTy T) ->
      has_type CT Gamma s h (unlabel e) T
(* labelOf *)
  | T_labelOf : forall s h Gamma CT e T,
      has_type CT Gamma s h e (LabelelTy T) ->
      has_type CT Gamma s h (labelOf e) LabelTy
(* unlabel opaque *)
  | T_unlabelOpaque : forall s h Gamma CT e T,
      has_type CT Gamma s h e (OpaqueLabeledTy T) -> 
      has_type CT Gamma s h (unlabelOpaque e) T
(* opaque call *)
  | T_opaqueCall : forall s h Gamma CT e T,
      has_type CT Gamma s h e T ->
      has_type CT Gamma s h (opaqueCall e) (OpaqueLabeledTy T)
(* Skip *)
  | T_skip : forall s h Gamma CT,
      has_type CT Gamma s h Skip voidTy
(* assignment *)
  | T_assignment : forall s h Gamma CT e T x lsf lb sf s', 
      s = cons lsf s' ->
      lsf = Labeled_frame lb sf ->
      (exists v, Some v = sf(x)) ->
      Gamma x = Some T ->
      has_type CT Gamma s h e T ->
      has_type CT Gamma s h (Assignment x e) voidTy
(* Field Write *)
  | T_FieldWrite : forall s h Gamma x f cls_def CT clsT cls' e,
      has_type CT Gamma s h x (classTy clsT) ->
      has_type CT Gamma s h e (classTy cls') ->
      Some cls_def = CT(clsT) ->
      type_of_field (find_fields cls_def) f = Some cls' ->
      has_type CT Gamma s h (FieldWrite x f e) voidTy
(* if *)
  | T_if : forall Gamma s h CT id1 id2 s1 s2 T T' ,
      has_type CT Gamma s h (Tvar id1) (classTy T) ->
      has_type CT Gamma s h (Tvar id2) (classTy T) ->
      has_type CT Gamma s h s1 T' ->
      has_type CT Gamma s h s2 T' ->
      has_type CT Gamma s h (If id1 id2 s1 s2) T'
(* sequence *)
  | T_sequence : forall s h Gamma CT e1 e2 T T',
      has_type CT Gamma s h e1 T ->
      has_type CT Gamma s h e2 T' ->
      has_type CT Gamma s h (Sequence e1 e2) T'
(* return *)
  | T_return : forall s h Gamma CT e T,
      has_type CT Gamma s h e T ->
      T <> voidTy ->
      has_type CT Gamma s h (Return e) T
(* ObjId *)
  | T_ObjId : forall s h Gamma CT o cls_name cls_def,
      Some cls_def = CT(cls_name) ->
      (exists F lo, lookup_heap_obj h o = Some (Heap_OBJ cls_def F lo)) ->
      (exists field_defs method_defs, cls_def = (class_def cls_name field_defs method_defs)) ->
      has_type CT Gamma s h (ObjId o) (classTy cls_name)
(* runtime labeled data *)
  | T_v_l : forall s h Gamma lb CT v T,
      has_type CT Gamma s h (l lb)  LabelTy ->
      has_type CT Gamma s h v  T ->
      has_type CT Gamma s h (v_l v lb) (LabelelTy T)
(* runtime labeled data *)
  | T_v_opa_l : forall s h Gamma lb CT v T,
      has_type CT Gamma s h (l lb)  LabelTy ->
      has_type CT Gamma s h v  T ->
      has_type CT Gamma s h (v_opa_l v lb) (OpaqueLabeledTy T).

Definition empty_heap : heap := nil.

Definition compare_oid (o1 : oid) (o2 : oid) :=
  match o1, o2 with 
      | OID n1, OID n2 => if (gt_dec n1  n2) then true else false
  end.

Inductive wfe_heap : Class_table -> typing_context -> heap -> Prop :=
  | empty_heap_wfe : forall ct ctx, 
        wfe_heap ct ctx empty_heap
  | heap_wfe : forall h h' o cls_def F ct gamma cn ho lo method_defs field_defs ,
        h' = (o , ho) :: h ->
        (h = nil \/ (exists o' ho' h'', h = (o' , ho') :: h'' /\ compare_oid o o' = true) ) ->
        wfe_heap ct gamma h ->
        ho = (Heap_OBJ cls_def F lo) ->
        Some cls_def  = ct cn ->
        cls_def = class_def cn field_defs method_defs ->
        (forall f cls', type_of_field field_defs f = Some cls' -> 
                exists v, F(f) = Some v
                 /\ (v= null  \/ 
                          ( exists o' F' lx field_defs0 method_defs0, v = ObjId o' 
                                  /\ lookup_heap_obj h' o' = Some (Heap_OBJ (class_def cls' field_defs0 method_defs0) F' lx)
                                    /\ ct cls' = Some (class_def cls' field_defs0 method_defs0)
                          ) ) 
        )->
        wfe_heap ct gamma h'.

Theorem beq_nat_true: forall n m,
  beq_nat n m = true -> n = m.
Proof.
  intros n. induction n.
    intros. destruct m. 
      reflexivity.  inversion H.
    intros. destruct m. 
      inversion H. simpl in H. apply f_equal. apply IHn in H. apply H.
Qed. 

Lemma beq_oid_equal : forall x x', beq_oid x x' = true -> x = x'.
Proof.
   intros. unfold beq_oid in H.
   destruct x. destruct x'. f_equal. 
   case_eq (n =? n0). intro. 
   apply beq_nat_true with (n:=n) (m:=n0). auto. 

   intro. rewrite H0 in H. inversion H.
Qed.

Lemma beq_oid_same : forall o, beq_oid o o = true. 
Proof with auto. 
  intro o. unfold beq_oid. destruct o. induction n. reflexivity.
  simpl. auto. 
Qed. 

Lemma beq_equal_oid : forall x x', x = x' -> beq_oid x x' = true.
Proof.
   intros. 
   destruct x. destruct x'. rewrite H.
  apply beq_oid_same.
Qed.

Lemma beq_equal : forall x x', beq_id x x' = true -> x' = x.
Proof.
   intros. unfold beq_id in H. 
  destruct x. destruct x'.  f_equal.
 case_eq (string_dec s s0). 
  - intros. rewrite -> e. auto.
  - intro. intro. rewrite -> H0 in H. inversion H. 
Qed.

Lemma beq_OID_not_equal : forall n n1, n <> n1 -> beq_oid (OID n) (OID n1) = false.
Proof. 
  intro n.   unfold beq_oid. 
    induction n. destruct n1. 
    - intuition. 
    - intuition.
    - intros. destruct n1. intuition. 
       simpl in H. simpl. apply IHn. 
       intro contra.  rewrite contra in H. intuition. 
Qed. 

Lemma beq_oid_not_equal : forall o o', o <> o' -> beq_oid o o' = false.
  Proof. 
      intros. destruct o. destruct o'.
      assert (n <> n0). intro contra. 
      rewrite contra in H. intuition. 
      apply beq_OID_not_equal.
      auto. 
  Qed.  


Lemma fresh_heap_nil : forall h CT gamma h' n0 ho0, 
    wfe_heap CT gamma h ->
    h = ((OID n0) , ho0) :: h' ->
    h' = nil ->
    forall n, n > n0 -> lookup_heap_obj h (OID n) = None.
Proof.
   intros. unfold  lookup_heap_obj. rewrite H0. 
     assert (beq_oid (OID n) (OID n0) = false).
    apply beq_OID_not_equal with (n:=n) (n1:=n0) .
    intro contra.  rewrite contra in H2. intuition. rewrite H1.  rewrite H3. auto.  
Qed. 

Lemma nat_compare_oid : forall n1 n2, 
  n1 > n2 -> compare_oid (OID n1) (OID n2) = true.
Proof. 
  intros. unfold compare_oid.
  destruct n1. destruct n2. 
  - inversion H.
  - inversion H. 
  - case_eq (gt_dec (S n1) n2 ).
      + intros. auto. 
      + intros. intuition.
Qed. 

Lemma compare_oid_nat : forall n1 n2, 
  compare_oid (OID n1) (OID n2) = true ->
  n1 > n2.
Proof. 
    intros. unfold compare_oid in H.
  destruct n1. destruct n2. 
  - inversion H.
  - inversion H. 
  - case_eq (gt_dec (S n1) n2 ).
      + intros. auto. 
      + intros. rewrite H0 in H. inversion H.
Qed. 

Lemma gt_trans : forall n1 n2 n3, 
  n1 > n2 ->
  n2 > n3 ->
  n1 > n3. 
Proof. 
  intros. intuition.
Qed.  

Lemma oid_trans : forall n1 n2 n3, 
  n1 > n2 ->
  compare_oid (OID n2) (OID n3) = true -> 
  n1 > n3. 
Proof. 
  intros. apply compare_oid_nat in H0. intuition. 
Qed. 

Lemma fresh_heap : forall h h' CT gamma  n0 ho0, 
    wfe_heap CT gamma h ->
    h = ((OID n0) , ho0) :: h' ->
    (forall n, n > n0 -> lookup_heap_obj h (OID n) = None).
  Proof.
    intros. generalize dependent h'. generalize dependent n.  
        generalize dependent n0.     generalize dependent ho0.
    induction h. intros.  inversion H0.
    intros. inversion H. inversion H0. 
    unfold  lookup_heap_obj. 
     assert (beq_oid (OID n) (OID n0) = false).
    apply beq_OID_not_equal with (n:=n) (n1:=n0) .
    intro contra.  rewrite contra in H1. intuition. rewrite H12.
    fold lookup_heap_obj. rewrite <- H14. 
    destruct H3. inversion H2. rewrite H3. auto.
    destruct H3 as [o']. destruct H3 as [ho']. destruct H3 as [h''].
   induction o'.
    apply IHh with (ho0:=ho') (n0:=n1) (h':=h''). inversion H2. apply H4. auto.
    inversion H2. rewrite H13 in H16. inversion H16. destruct H3. 
    rewrite <- H18 in H15. 
    apply oid_trans with (n1:=n) (n2:=n0) (n3:=n1). auto. auto. auto.
    destruct H3. inversion H2. auto.
Qed. 


Lemma fresh_oid_heap : forall h CT gamma o,
    wfe_heap CT gamma h ->
    o = (get_fresh_oid h) -> 
    lookup_heap_obj h o = None.
Proof. intros. generalize dependent h. induction h. 
           - unfold get_fresh_oid. auto.
           - intros. unfold get_fresh_oid in H0. 
              induction a. induction o0.   
              rewrite H0.
              apply fresh_heap with (h:=((OID n, h0) :: h)) (h':=h) (CT:=CT)
                                   (gamma:=gamma)  (n0:=n) (ho0:=h0).
              auto. auto. intuition. 
Qed. 


Lemma some_eq : forall cls_def F lo cls_def' F' lo',
  Some (Heap_OBJ cls_def F lo) = Some (Heap_OBJ cls_def' F' lo') ->
  cls_def = cls_def' /\ F = F'.
Proof with auto. 
  intros. inversion H. auto. 
Qed.  


Lemma field_val_of_heap_obj : forall h o gamma CT cls_def F lo cls' fields,
  wfe_heap CT gamma h -> 
  lookup_heap_obj h o  = Some (Heap_OBJ cls_def F lo) ->
  fields = (find_fields cls_def) ->
  forall f, type_of_field fields f = Some cls' -> exists v, F(f) = Some v.
  (*(type_of_field fields_def fname) = Some f_def->*)

Proof with auto.
  intros. induction H. inversion H0.
  unfold lookup_heap_obj in H0.
  rewrite H in H0. 
  case_eq (beq_oid o o0). intro.   rewrite H9 in H0. inversion H0.
  destruct H8 with   (f:=f) (cls':=cls'). 
  rewrite H11 in H5. inversion H5. 
  rewrite H12 in H1.  rewrite H7 in H1. unfold find_fields in H1.
  rewrite <- H1. auto. rewrite H5 in H11. inversion H11. destruct H10.
  rewrite <- H14. exists x. auto.
  intro. rewrite H9 in H0.
  fold lookup_heap_obj in H0.
  apply IHwfe_heap. auto. 
Qed.

Lemma heap_consist_ct : forall h o ct ctx cls F lo ,
  wfe_heap ct ctx h -> 
  lookup_heap_obj h o = Some (Heap_OBJ cls F lo) ->
  exists cn field_defs method_defs, ct cn = Some cls /\ cls = (class_def cn field_defs method_defs).
Proof with auto.
  intros. induction H. 
  - inversion H0.
  - unfold lookup_heap_obj in H0.
     case_eq (beq_oid o o0).   intros. rewrite H in H0.  rewrite H7 in H0. inversion H0. 
      rewrite -> H9 in H3. inversion H3.   
      exists cn0. exists  field_defs. exists method_defs. 
      split. auto. auto. intro. rewrite H in H0. rewrite H7 in H0.
      fold lookup_heap_obj in H0. apply IHwfe_heap. auto. 
Qed.

Fixpoint variable_exists (s : stack) (x : id) :=
  match s with 
    | nil => false
    | cons (Labeled_frame lb sf) s' => match (sf x) with 
                                        | None => variable_exists s' x
                                        | Some v => true
                                        end
  end.

Inductive wfe_stack_frame : Class_table -> typing_context -> heap -> labeled_stack_frame -> Prop :=
  | stack_frame_wfe : forall h lsf sf lb ct gamma,
        lsf = Labeled_frame lb sf ->
(*        (forall cls_name x, gamma x = Some (classTy cls_name) 
        -> *)
         (forall x v cls_name, sf x = Some v  
          ->  gamma x = Some (classTy cls_name) 
          ->    (
               v = null \/ 
                 ( exists o, v = ObjId o 
                              /\ (exists F lo field_defs method_defs , lookup_heap_obj h o = Some (Heap_OBJ (class_def cls_name field_defs method_defs) F lo)
                                      /\ (ct cls_name = Some (class_def cls_name field_defs method_defs))
                                   ) 
                  )    )  ) ->
        wfe_stack_frame ct gamma h lsf. 


Inductive wfe_stack : Class_table -> typing_context -> heap -> stack -> Prop :=
  | main_stack_wfe : forall ct gamma s h lb,
        wfe_heap ct gamma h -> 
       (* h = empty_heap ->*)
        s = cons (Labeled_frame lb empty_stack_frame) nil ->
        gamma = empty_context -> 
        forall lb, wfe_stack ct gamma h (cons (Labeled_frame lb empty_stack_frame) nil)
  | stack_wfe : forall s ct gamma s' lb sf h, 
        s = cons (Labeled_frame lb sf) s'->
        wfe_stack ct gamma h s' ->
        wfe_heap ct gamma h ->
        (forall x, (exists v, sf x = Some v) -> (exists T, gamma x = Some T)) -> 
        wfe_stack_frame ct gamma h (Labeled_frame lb sf) ->
        wfe_stack ct gamma h s.



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

Lemma wfe_oid : forall o ct gamma s h sigma cls_def cn, 
  sigma = SIGMA s h ->
  wfe_stack ct gamma h s ->
  (has_type ct gamma s h (ObjId o) (classTy cn)) -> ct cn = Some cls_def 
    -> exists fieldsMap lb, lookup_heap_obj h o = Some (Heap_OBJ cls_def fieldsMap lb).
Proof with auto. 
  intros. inversion H1. rewrite H2 in H5. inversion H5. 
  rewrite <- H13. auto.
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
Qed.


Lemma stack_not_nil : forall sigma gamma CT s h, 
  sigma = SIGMA s h ->  wfe_heap CT gamma h -> wfe_stack CT gamma h s -> exists lsf s', s = cons lsf s'.
Proof with auto.
  intros. inversion H1. exists (Labeled_frame lb0 empty_stack_frame). exists nil. auto. 
  exists (Labeled_frame lb sf). exists s'. auto. 
Qed.

(* every value in the stack should be well-formed, which means that all values should point to null or valid Obj Id*)
Lemma wfe_stack_value : forall gamma CT s h sigma v clsT, 
    sigma = SIGMA s h ->  wfe_heap CT gamma h -> wfe_stack CT gamma h s 
      -> (has_type CT gamma s h v (classTy clsT))
      -> value v -> (v = null \/ 
                 ( exists o, v = ObjId o 
                              /\ (exists F lo field_defs method_defs , 
                                      lookup_heap_obj h o = Some (Heap_OBJ (class_def clsT field_defs method_defs) F lo)
                                      /\ (CT clsT = Some (class_def clsT field_defs method_defs))
                                   )
                  )    ).
Proof. 
    intros gamma CT s h sigma v clsT. intro. intro. intro.  intro. intro. 
    induction H3. right. exists o. split. auto. inversion H2. 
    destruct H10 as [F].     destruct H10 as [lo].    
    destruct H11 as [field_defs].    destruct H11 as [method_defs]. 
    exists F. exists lo. exists field_defs. exists method_defs.  
    split. rewrite <- H11. auto. rewrite H11 in H5. auto.
    
    inversion H2. 

    left. auto. 
    inversion H2. inversion H2.  inversion H2. 
Qed.   

Check update_current_label.

Lemma change_label_preserve_wfe : forall gamma CT s h lb,
    wfe_heap CT gamma h -> wfe_stack CT gamma h s ->
    wfe_stack CT gamma h (update_current_label s lb).
Proof. 
   intros. inversion H0. 
    - unfold update_current_label. apply main_stack_wfe with (s:=s) (lb:=lb1); auto.
    - subst.  unfold update_current_label. apply stack_wfe with (s':=s') (lb:=lb) (sf:=sf); auto.
        inversion H5.  apply stack_frame_wfe with (sf:=sf) (lb:=lb); auto. inversion H1. auto.
Qed.




Lemma extend_heap_preserve_heap_wfe : forall gamma CT h h' o c field_defs method_defs lb,
    wfe_heap CT gamma h -> 
    o = get_fresh_oid h ->
    lookup_heap_obj h o = None -> 
    Some (class_def c field_defs method_defs) = CT c ->  
     h' = add_heap_obj h o (Heap_OBJ (class_def c field_defs method_defs)
          (init_field_map field_defs empty_field_map)
          lb) -> wfe_heap CT gamma h'.
  Proof. 
    intros. 
    remember (class_def c field_defs method_defs) as cls_def.
    remember  (init_field_map field_defs empty_field_map) as F.
    apply heap_wfe with (h:=h) (o:=o) 
        (cls_def:=cls_def) (F:=F) (cn0:=c) (ho:=(Heap_OBJ cls_def F lb))
        (lo:=lb) (method_defs:=method_defs) (field_defs:=field_defs) ;auto.
        intros. induction h. left. auto. right.
        unfold  get_fresh_oid in H0. 
        induction a. induction o0. 
        exists (OID n). exists h0. exists h. 
        rewrite H0. split. auto. apply nat_compare_oid. intuition. 
 exists null. split. 
        apply empty_fields with (fields:=field_defs) (cls':=cls'). auto. auto. 
        left.  auto.  
Qed.


Lemma extend_heap_preserve_stack_wfe : forall gamma CT s h h' o heap_obj,
    wfe_heap CT gamma h -> 
    wfe_stack CT gamma h s ->
    o = get_fresh_oid h ->
    h' = add_heap_obj h o heap_obj -> 
    wfe_heap CT gamma h' -> 
    wfe_stack CT gamma h' s.
Proof. 
  intros. induction H0.

  apply main_stack_wfe with (s:=s) (lb:=lb). 
  auto.  auto. auto. auto.
  apply stack_wfe with (s:=s) (ct:=ct) (gamma:=gamma) 
                  (s':=s') (lb:=lb) (sf:=sf) (h:=h').
  auto. auto. auto. auto.
  apply stack_frame_wfe with (sf:=sf) (lb:=lb). 
  inversion H7. auto. inversion H7. auto. inversion H8.
  intros. destruct H9 with (x:=x) (v:=v) (cls_name:=cls_name).
  auto. auto. left. auto. right. destruct H18 as [o']. destruct H18.
  destruct H19 as [F].   destruct H19 as [lo]. 
  destruct H19 as [field_defs].     destruct H19 as [method_defs].
  destruct H19.
  exists o'. split. auto. 
  exists F. exists lo. exists field_defs. exists method_defs.
  split. 

  rewrite H2. unfold add_heap_obj. 
  assert (o' <> o). intro contra. 
  rewrite contra in H19. rewrite H1 in H19. 
  assert (lookup_heap_obj h (get_fresh_oid h) = None).
  apply fresh_oid_heap with (CT:=ct) (gamma:=gamma). 
  auto. auto.  rewrite H21 in H19. inversion H19.
  assert (beq_oid o' o = false).  apply beq_oid_not_equal.
  auto. unfold lookup_heap_obj. rewrite H22. 
  fold lookup_heap_obj. auto. auto. 
Qed. 

(*change the values residing on the top of the stack does preserves the well-formness of stack*)
Lemma update_stack_preserve_wfe : forall gamma CT s s' h i v T, 
    wfe_stack CT gamma h s ->
    s' =  update_stack_top s i v -> 
    value v ->
   has_type CT gamma s h v T ->
    gamma i = Some T ->
    wfe_stack CT gamma h s'.
Proof.
   intros gamma CT s s' h i v T. intro. intro. intro Hv. intro typing. intro.

  inversion H. rewrite H4 in H1. inversion H1.
  rewrite H2 in H0.    unfold update_stack_top in H0. 

   unfold labeled_frame_update in H0. 
  remember (fun x' : id => if beq_id i x' then Some v else sf x') as sf'.

   apply stack_wfe with (s:=s') (ct:=CT) (gamma:=gamma) (s':=s'0) 
                      (lb:=lb) (sf:=sf') (h:=h); auto.  

   rewrite Heqsf'. intro. intro t. destruct t as [v0].
   case_eq (beq_id i x). intro. rewrite H12 in H11. 
  inversion H11. 
  apply beq_equal in H12. rewrite H12.  exists T. auto. 
  intro. destruct H5 with x. rewrite H12 in H11. 
  exists v0. auto. exists x0. auto. 

  inversion H6. 
  apply stack_frame_wfe with (sf:=sf') (lb:=lb). auto. 

  intros. rewrite Heqsf' in H17. 
  case_eq (beq_id i x). intro. rewrite H19 in H17.   inversion H17.
   apply beq_equal in H19. rewrite  H19 in H18. 
  rewrite H1 in H18. 

  rewrite <- H21. inversion Hv. right. exists o. split; auto.
  rewrite <- H20 in typing. inversion typing.
  destruct H24 as [F].   destruct H24 as [lo].  
  destruct H29 as [field_defs].   destruct H29 as [method_defs].
  exists F. exists lo. exists field_defs. exists method_defs.
  split.  rewrite H29 in H24. 
  rewrite <- H30 in H18. inversion H18. 
  rewrite <- H32. auto.  
  rewrite <- H30 in H18. inversion H18. 
  rewrite H32 in H23. rewrite <- H23. f_equal. rewrite H32 in H29.
  auto. 
  inversion H18. rewrite H23 in typing. rewrite <- H20 in typing.
  inversion typing. 

  left. auto. 
  inversion H18. rewrite H23 in typing. rewrite <- H20 in typing.
  inversion typing.
  inversion H18. rewrite H23 in typing. rewrite <- H20 in typing.
  inversion typing.
  inversion H18. rewrite H23 in typing. rewrite <- H20 in typing.
  inversion typing.
  intro. rewrite H19 in H17.  inversion H11. rewrite <- H22 in H12.
  apply H12 with (x:=x) (v:=v0) (cls_name:=cls_name). 
  auto. auto. 
Qed. 

Inductive wfe_heap_obj : heapObj -> Class_table -> heap -> Prop :=
  | field_wfe : forall h ho o f cls' ct cls_name cls_def method_defs field_defs F lo, 
    ct cls_name =  Some cls_def ->
    Some ho = lookup_heap_obj h o -> 
    ho = (Heap_OBJ cls_def F lo) ->
    type_of_field field_defs f = Some cls' -> 
    cls_def = class_def cls_name field_defs method_defs ->
           (forall f,  exists v0, F(f) = Some v0
             /\ (v0= null  \/ 
                      ( exists o' F' lx field_defs0 method_defs0, v0 = ObjId o' 
                              /\ lookup_heap_obj h o' = Some (Heap_OBJ (class_def cls' field_defs0 method_defs0) F' lx)
                                /\ ct cls' = Some (class_def cls' field_defs0 method_defs0)
                      ) ) ) ->
    wfe_heap_obj ho ct h. 

Lemma nil_heap_no_obj : forall ho h o,
  nil = update_heap_obj h o ho ->
  h = nil.
Proof.
  intros. induction h. auto. inversion H. 
  case a in H1. 
  case_eq (beq_oid o o0).  intro.  rewrite H0 in H1. inversion H1. 
   intro.  rewrite H0 in H1. inversion H1. 
Qed. 


Lemma  lookup_updated : forall o ho h h' ho',
    h' = update_heap_obj h o ho ->
    Some ho' = lookup_heap_obj h o ->
    Some ho = lookup_heap_obj h' o. 
  Proof. 
    intros. generalize dependent h. induction h'.
   - intros. apply nil_heap_no_obj in H. rewrite H in H0. inversion H0.
   - intro h. intro.  intro. induction a.
      destruct h. inversion H0. 
      induction h. 
      case_eq (beq_oid o o1).  intro.  
      unfold  update_heap_obj in H. rewrite H1 in H. inversion H.
      unfold lookup_heap_obj.       
      assert (beq_oid o o=true). apply beq_oid_same. rewrite H2.  auto.

      intro. unfold  update_heap_obj in H. rewrite H1 in H. fold update_heap_obj in H.  
      inversion H. 
      unfold lookup_heap_obj.        rewrite H1.  fold lookup_heap_obj.
      rewrite <- H5.  apply IHh' with (h:=h1). auto. 
      unfold lookup_heap_obj in H0.        rewrite H1 in H0.  fold lookup_heap_obj in H0. auto.
Qed. 

Lemma update_preserve_obj_typing :
  forall CT o gamma s h h' i F cls_def cls' cls lb lb' v clsT field_defs method_defs,
  wfe_heap CT gamma h ->
(*  wfe_stack CT gamma h s -> *)
  value v ->
  Some (Heap_OBJ cls F lb) = lookup_heap_obj h o ->
  type_of_field (find_fields cls_def) i = Some cls' ->
  cls_def = class_def clsT field_defs method_defs ->
  has_type CT gamma s h v (classTy cls') ->
(*  has_type CT gamma s h (ObjId o) (classTy clsT) ->*)
  Some cls_def = CT clsT ->
  h' = (update_heap_obj h o
           (Heap_OBJ cls (fields_update F i v) lb')) ->
has_type CT gamma s h' v (classTy cls').
Proof.
  intros CT o gamma s h h' i F cls_def cls' cls lb lb' v clsT field_defs method_defs. 
  intro H_wfe_h.
  intro H_v.  intro H_o. intro H_i. intro H_cls_def. intro H_typing_v. (*intro H_typing_o. *)intro H_clsT.
  intro H_h'.
  inversion H_v.  rewrite <- H in H_typing_v. inversion H_typing_v.
  apply T_ObjId with (cls_def:=cls_def0). auto.
   generalize dependent h.  
  induction h'.
  intros.  
  apply nil_heap_no_obj in H_h'. rewrite H_h' in H_o. inversion H_o.
  intro h. intros. 
  
  induction a.  destruct h. 
   inversion H_o.  induction h.
(*
  case_eq (beq_oid o o3). intro.
  unfold   update_heap_obj in H_h'. rewrite H9 in H_h'.
  inversion H_h'.
  apply beq_oid_equal in H9.
  destruct H7 as [F0]. destruct H7 as [lo0].
  
  
  assert ( Some  (Heap_OBJ cls (fields_update F i v) lb') = lookup_heap_obj h' o0).
  apply lookup_updated with (o:=o0) (ho:=(Heap_OBJ cls (fields_update F i v) lb'))
                         (h:=h1) (h':=h') (ho':=(Heap_OBJ cls_def0 F0 lo0)).
  rewrite H9. auto. auto. exists (fields_update F i v). exists lb'. 
  rewrite H9 in H7. rewrite H7 in H_o. inversion H_o. 
  rewrite <- H12. rewrite <- H13.
  auto. 
  
  intro. induction h'.  
  apply nil_heap_no_obj in H_h'. rewrite H_h' in H_o. inversion H_o.
  *)
Admitted. 

Lemma update_obj_preserve_heap_wfe : 
  forall ct o gamma h h' F cls_def cls lb clsT field_defs method_defs ho, 
  wfe_heap ct gamma h ->
  Some (Heap_OBJ cls F lb) = lookup_heap_obj h o ->
  cls_def = class_def clsT field_defs method_defs ->
  ct clsT = Some cls_def ->
  wfe_heap_obj ho ct h' -> 
  h' = (update_heap_obj h o ho) ->
  wfe_heap ct gamma h'.
Proof. 
  intros ct o gamma h h' F cls_def cls lb clsT field_defs method_defs ho.
  intro wfe_h. intro H_o. intro H_cls_def.  intro H_clsT. intro H_wfe_ho.
  intro H_h'. generalize dependent h. induction h'.
  - intro. admit. 
  - intro h. intro. intro. intro. 
    induction a.  inversion wfe_h. rewrite <- H1 in H_o. inversion H_o.

    destruct h. inversion H_o. induction h.

apply heap_wfe with (h:=h') (o:=o0) (cls_def:=cls_def0) (F:=F0) (cn0:=cn0) (ho:=h0)
(lo:=lo) (method_defs:=method_defs0) (field_defs:=field_defs0). auto.

(*o = o2*)
case_eq (beq_oid o o2). intro. 
unfold update_heap_obj in H_h'. rewrite H9 in H_h'. inversion H_h'.
inversion H.  apply beq_oid_equal in H9.  rewrite H9. rewrite H14. auto.

 (*o <> o2*)
intro. unfold update_heap_obj in H_h'. rewrite H9 in H_h'. fold update_heap_obj in H_h'. 
inversion H_h'. inversion H.
destruct H0. rewrite H0. left. auto.

right. admit. 

inversion H1. admit.

case_eq (beq_oid o o2). intro. 
unfold update_heap_obj in H_h'. rewrite H19 in H_h'. inversion H_h'. 
inversion H. auto.

intro. unfold update_heap_obj in H_h'. rewrite H19 in H_h'. 
fold update_heap_obj in H_h'. inversion H_h'. 

rewrite <- H23. apply IHh' with (h:=h1).



wfe_heap_obj ho ct ((o0, h0) :: h')







  admit. 

Admitted.  







(* reduction preserve well-form of stack and heap *)
Theorem reduction_preserve_wfe : forall gamma CT s s' h h' sigma sigma',
    sigma = SIGMA s h ->  wfe_heap CT gamma h -> wfe_stack CT gamma h s ->
     sigma' = SIGMA s' h' -> 
    forall t T, has_type CT gamma s h t T -> 
     forall t',  Config t sigma ==> Config t' sigma' ->
    wfe_heap CT gamma h' /\ wfe_stack CT gamma h' s'.
Proof. 
    intros gamma CT s s' h h' sigma sigma'. 
    intro. intro. intro. intro. 
    induction t. (*induction on the terms *)
  (* (Tvar i) *)
  + intro T. intro typing. intro t'.  intro step. inversion step.
      rewrite H in H6. rewrite H2 in H6. inversion H6. 
      rewrite <- H12. rewrite <- H13.
      split. auto. auto.

  (* null *)
  + intro T. intro typing. intro t'.  intro step. inversion step.
  (* field access *)
  + intro T. intro typing. intro t'.  intro step. 
      inversion step.  inversion typing.
      apply IHt with (T:=(classTy clsT)) (t':=e'). auto. auto.
      (*subgoal#2 *)      
      inversion typing. subst. inversion H13. inversion H8. 
      split.       rewrite <- H5. auto.
      rewrite <- H5. rewrite <- H4. 
      remember (join_label lb (current_label (SIGMA s h))) as lb'.
      unfold update_current_label.
      inversion H1. apply main_stack_wfe with (s:=s1) (lb:=lb0). auto. auto. auto. auto.  
      rewrite H. 

      apply stack_wfe with (gamma:=gamma) (s':=s'0) 
                                                      (lb:=lb') (sf:=sf); auto.
      inversion H12. apply stack_frame_wfe with (lb:=lb') (sf:=sf); auto.
      inversion H20. apply H21. 

  (* method call *)
  + intro T. intro typing. intro t'.  intro step. 
      inversion step.  
      (*subgoal 1*)
      inversion typing. apply IHt1 with (T:=(classTy T0)) (t':=e'); auto.
     
      (*subgoal 2*)
      inversion typing. apply IHt2 with (T:=arguT) (t':=e'); auto.
      (*subgoal 3*)
      subst. inversion H18. split. auto.
      inversion H9. rewrite <- H4. rewrite <- H5.
      inversion H1. rewrite <- H5 in H10.
      inversion typing. rewrite H7 in H30. inversion H30. 

      (*rewrite H5 in H10. inversion H10.*)
      remember (sf_update empty_stack_frame arg_id t2) as sf'.
      remember (Labeled_frame (current_label (SIGMA s h)) sf')  as lsf' .

      apply stack_wfe with (gamma:=gamma) (s':=s) 
                                                      (lb:=(current_label (SIGMA s h))) (sf:=sf') ; auto.
      rewrite Heqlsf'. auto.
      rewrite Heqsf'. unfold sf_update.
      intro x.  intro. 
      case_eq (beq_id arg_id x). intro.
      inversion typing.
      inversion H24.  rewrite <- H37 in H26. inversion H26. 
      destruct H43 as [F]. destruct H43 as [lo].
      rewrite <- H5 in H10. rewrite H43 in H10.  inversion H10. 
      rewrite <- H37 in H38. rewrite <- H38 in H46. inversion H46. 
      rewrite H47 in H11. rewrite <- H50 in H11. rewrite H27 in H11. 
      inversion H11. rewrite <- H53 in H34. 
      assert (x=arg_id). apply beq_equal. auto. 
      rewrite H45. exists arguT. auto. 
      
      intro. destruct H19. rewrite H20 in H19. inversion H19.

 
      apply stack_frame_wfe with (lb:=(current_label (SIGMA s h))) (sf:=sf').
      auto. intros x v cls_name.  intro. intro.
      inversion typing.
      inversion H24.  rewrite <- H37 in H26. inversion H26. 
      destruct H43 as [F]. destruct H43 as [lo].
      rewrite <- H5 in H10. rewrite H43 in H10.  inversion H10. 
      rewrite <- H37 in H38. rewrite <- H38 in H46. inversion H46. 
      rewrite H47 in H11. rewrite <- H50 in H11. rewrite H27 in H11. 
      inversion H11. 
     (*case arg_id= x*)
      case_eq (beq_id arg_id x). intro. 
      assert (x =arg_id).  apply beq_equal. auto. 
      rewrite Heqsf' in H19. unfold sf_update in H19. rewrite H45 in H19.
      inversion H19. rewrite H57 in H12.

      rewrite <- H53 in H34.  rewrite <- H55 in H34. 
      rewrite H34 in H20. inversion H20. rewrite H58 in H25.
      remember (SIGMA s h) as sigma.
      apply wfe_stack_value with (gamma:=gamma) (CT:=CT) (s:=s) (h:=h) 
                            (sigma:=sigma) (v:=v) (clsT:=cls_name). 
      auto. auto. auto.  rewrite <- H57. auto. auto.
     (*case arg_id != x*)
      intro. rewrite Heqsf' in H19. unfold sf_update in H19. rewrite H45 in H19.
      inversion H19.

      
     (*subgoal 4 *)

    subst. inversion H17. split. auto.
      inversion H9. rewrite <- H4. rewrite <- H5.
      inversion H1. rewrite <- H5 in H10.
      inversion typing. rewrite H7 in H30. inversion H30. 
      remember (sf_update empty_stack_frame arg_id v) as sf'.
      remember (Labeled_frame (join_label lb (current_label (SIGMA s h))) sf')  as lsf' .

      apply stack_wfe with (gamma:=gamma) (s':=s) 
                                                      (lb:=(join_label lb (current_label (SIGMA s h)))) (sf:=sf') ; auto.
      rewrite Heqlsf'. auto.
      rewrite Heqsf'. unfold sf_update.
      intro x.  intro. 
      case_eq (beq_id arg_id x). intro.
      inversion typing.
      inversion H24.  rewrite <- H37 in H26. inversion H26. 
      destruct H43 as [F]. destruct H43 as [lo].
      rewrite <- H5 in H10. rewrite H43 in H10.  inversion H10. 
      rewrite <- H37 in H38. rewrite <- H38 in H46. inversion H46. 
      rewrite H47 in H16. rewrite <- H50 in H16. rewrite H27 in H16. 
      inversion H16. rewrite <- H53 in H34. 
      assert (x=arg_id). apply beq_equal. auto. 
      rewrite H45. exists arguT. auto. 
      
      intro. destruct H19. rewrite H20 in H19. inversion H19.

 
      apply stack_frame_wfe with (lb:=(join_label lb (current_label (SIGMA s h)))) (sf:=sf').
      auto. intros x v' cls_name.  intro. intro.
      inversion typing.
      inversion H24.  rewrite <- H37 in H26. inversion H26. 
      destruct H43 as [F]. destruct H43 as [lo].
      rewrite <- H5 in H10. rewrite H43 in H10.  inversion H10. 
      rewrite <- H37 in H38. rewrite <- H38 in H46. inversion H46. 
      rewrite H47 in H16. rewrite <- H50 in H16. rewrite H27 in H16. 
      inversion H16. 
     (*case arg_id= x*)
      case_eq (beq_id arg_id x). intro. 
      assert (x =arg_id).  apply beq_equal. auto. 
      rewrite Heqsf' in H19. unfold sf_update in H19. rewrite H45 in H19.
      inversion H19. rewrite H57 in H15.

      rewrite <- H53 in H34.  rewrite <- H55 in H34. 
      rewrite H34 in H20. inversion H20. rewrite H58 in H25.
      remember (SIGMA s h) as sigma. rewrite <- H57.
      apply wfe_stack_value with (gamma:=gamma) (CT:=CT) (s:=s) (h:=h) 
                            (sigma:=sigma) (v:=v) (clsT:=cls_name). 
      auto. auto. auto. inversion H25. inversion H63.  auto. auto. 
      rewrite <- H57 in H15. auto. 
     (*case arg_id != x*)
      intro. rewrite Heqsf' in H19. unfold sf_update in H19. rewrite H45 in H19.
      inversion H19.

(* new expression *)
+ intro T. intro typing. intro t'.  intro step. inversion step. 
    subst. inversion typing. 
    remember (class_def c field_defs method_defs) as cls_def.
    assert (CT c = Some cls_def).
    apply H6 with (field_defs:=field_defs) (method_defs:=method_defs) (cls_def:=cls_def).
    auto. 

    inversion H7. inversion H13.
    rewrite <- H15. split.  
    remember (current_label (SIGMA s h)) as lb. 
    apply extend_heap_preserve_heap_wfe with (h:=h) (o:=(get_fresh_oid h0))
                          (c:=c) (field_defs:=field_defs)
                          (method_defs:=method_defs) (lb:=lb).
   auto.  rewrite H12. auto. apply fresh_oid_heap with (CT:=CT) (gamma:=gamma).
   auto. rewrite H12. auto. rewrite <- Heqcls_def. auto. auto.
   rewrite  H12. auto. rewrite  Heqcls_def in H15. auto.
   (* extend heap with new object preserve wfe *) 
    rewrite <- H11.
    remember (Heap_OBJ cls_def
           (init_field_map (find_fields cls_def) empty_field_map)
           (current_label (SIGMA s h))) as heap_obj.
    apply extend_heap_preserve_stack_wfe with (h:=h0) (o:= (get_fresh_oid h0))
                         (heap_obj:=heap_obj).
     rewrite <- H12.  auto.       rewrite <- H12.  auto.  auto. auto. 
     
     apply extend_heap_preserve_heap_wfe with (h:=h0) (o:=(get_fresh_oid h0)) 
                (c:=c) (field_defs:=field_defs) (method_defs:=method_defs) (lb:=(current_label (SIGMA s h))).
     rewrite <- H12.  auto.       rewrite <- H12.  auto.
     apply fresh_oid_heap with (CT:=CT) (gamma:=gamma).  
     rewrite <- H12.  auto.       rewrite <- H12.  auto.
     destruct H6 with (field_defs:=field_defs) (method_defs:=method_defs) (cls_def:= (class_def c field_defs method_defs)).
     auto. auto. rewrite Heqheap_obj in H15. 
     rewrite <- Heqcls_def. auto. rewrite Heqcls_def in H15. unfold find_fields in H15.
     rewrite Heqcls_def. auto. 

(* label value*)
+ intro T. intro typing. intro t'.  intro step. inversion step. 

(* label data *)
+ intro T. intro typing. intro t'.  intro step. 
    inversion step. inversion typing.
    apply IHt with (T:=T0) (t':=e'); auto.

    subst. inversion H8. rewrite <- H2. rewrite <- H3.
    intuition.

(* unlabel *)
+ intro T. intro typing. intro t'.  intro step. 
    inversion step. inversion typing.
    apply IHt with (T:=(LabelelTy T)) (t':=e'); auto.

    subst. inversion H10. split. auto. 
    inversion H7. rewrite <- H4. rewrite <- H5. 
    apply change_label_preserve_wfe; auto.

(* label of *)
+ intro T. intro typing. intro t'.  intro step. 
    inversion step. inversion typing.
    apply IHt with (T:=(LabelelTy T0)) (t':=e'); auto.

    subst. inversion H7. rewrite <- H2. rewrite <- H3. 
    split; auto.

(* unlabelopaque *)
+ intro T. intro typing. intro t'.  intro step. 
    inversion step. inversion typing.
    apply IHt with (T:=(OpaqueLabeledTy T)) (t':=e'); auto.

    rewrite H in H10. rewrite H2 in H10. unfold get_heap in H10.
    inversion H10. split. auto.
    rewrite H9.
    rewrite H in H7. inversion H7. rewrite <- H14. rewrite <- H15.
    apply change_label_preserve_wfe; auto.

(* opaque call *)
+ intro T. intro typing. intro t'.  intro step. 
    inversion step. 
    (*subgoal 1*)
    inversion typing. apply IHt with (T:=T0) (t':=e'); auto.
     
    (*subgoal 2*)
    inversion typing. apply ST_return1 in H4. 
    apply IHt with (T:=T0) (t':=Return e'); auto.
    rewrite <- H3. auto. 
     (*subgoal 3*)
      rewrite H in H7. rewrite H2 in H7.  inversion H7.
      rewrite <- H10 . rewrite <- H11. auto. 
     (*subgoal 4*)
     rewrite H2 in H11. inversion H11. rewrite H in H7. 
     inversion H7. rewrite <- H17. split. auto. 
     rewrite H16 in H1. inversion H1. 
     rewrite <- H23 in H8.  inversion H8. rewrite H26 in H9. intuition. 
     
     rewrite H8 in H13. inversion H13. auto. 
    
(* skip *)
+ intro T. intro typing. intro t'.  intro step. 
    inversion step.

(* assignment *)
+ intro T. intro typing. intro t'.  intro step. 
    inversion step. inversion typing.
    apply IHt with (T:=T0) (t':=e'). auto. auto.

   rewrite H in H9. rewrite H2 in H11.  inversion H9. inversion H11. 
    rewrite <- H14. split. auto. 
    rewrite H13 in H1.    inversion typing. 
    apply update_stack_preserve_wfe with (s:=s0) (i:=i) (v:=t) (T:=T0).
    auto. auto. auto. rewrite <- H13. auto. auto. 

(* field write *)
+ intro T. intro typing. intro t'.  intro step. 
    inversion step. 
     (*subgoal 1*)
    inversion typing.    apply IHt1 with (T:=(classTy clsT)) (t':=e1'); auto.
    (*subgoal 2*)
    inversion typing.    apply IHt2 with (T:=(classTy cls')) (t':=e2'); auto.  
    (*subgoal 3*)
    inversion typing. rewrite <- H3 in H19. inversion H19. subst.  
    inversion H19. 






    
      inversion H0.

      intro. admit. induction a. 

      case_eq (beq_oid o o1). intro. unfold  update_heap_obj in H.
      rewrite H2 in H. inversion H. unfold lookup_heap_obj.
      assert (beq_oid o o=true). apply beq_oid_same. rewrite H3.  auto.
      
      intro. unfold update_heap_obj in H. rewrite H2 in H. fold update_heap_obj in H.

      unfold lookup_heap_obj. rewrite  H1.  

      unfold update_heap_obj in H. 


apply beq_oid_equal in H1.        rewrite H1 in H. 
    apply IHh'. induction h. admit.
    induction a. induction a0.
    case_eq (beq_oid o1 o).
    intro. 
                  
      

admit. -
 induction H. 
    - apply nil_heap_no_obj in H. rewrite H in H0. inversion H0.
    - induction a. case_eq (beq_oid o o0).  
      intro.  apply beq_oid_equal in H1. rewrite H1.
      unfold update_heap_obj.  assert (beq_oid o0 o0= true). apply beq_oid_same.
      unfold lookup_heap_obj.  rewrite H2. auto.
      intro.       unfold update_heap_obj.  rewrite H1. fold update_heap_obj.
      unfold lookup_heap_obj. rewrite H1. fold lookup_heap_obj.
      apply IHh. unfold update_heap_obj in H.  rewrite H1 in H. fold update_heap_obj in H.
lookup_heap_obj
  Qed. 

  rewrite H_h'. unfold lookup_heap_obj. 
  case_eq (beq )

Qed. 


Lemma update_field_preserve_heap_wfe : 
  forall CT o gamma s h h' i F cls_def cls' cls lb lb' v clsT field_defs method_defs,
  wfe_heap CT gamma h ->
(*  wfe_stack CT gamma h s -> *)
  value v ->
  Some (Heap_OBJ cls F lb) = lookup_heap_obj h o ->
  type_of_field (find_fields cls_def) i = Some cls' ->
  cls_def = class_def clsT field_defs method_defs ->
  has_type CT gamma s h v (classTy cls') ->
  has_type CT gamma s h (ObjId o) (classTy clsT) ->
  Some cls_def = CT clsT ->
  h' = (update_heap_obj h o
           (Heap_OBJ cls (fields_update F i v) lb')) ->
  wfe_heap CT gamma h'.
Proof with auto. 
  intros CT o gamma s h h' i F cls_def cls' cls lb lb' v clsT field_defs method_defs.
  intro wfe_h. (*intro wfe_s. *) intro Hv. intro Ho. intro Htyf. intro Hcls_def. intro typing_v. 
  intro typing_o. intro Hct.
  intro Hy. 
  induction h. 
- inversion Ho.

- 
(* beq_oid o o0 = true *)
  induction a.  
  case_eq (beq_oid o o0). 
 (*
  intro. rewrite H5 in Hy.
  apply beq_oid_equal in H5.
  rewrite <- H5 in H0. 
  unfold fields_update in Hy.
  remember (fun x' : id => if beq_id i x' then Some v else F x') as F'. 
  inversion typing_o. destruct H13 as [F1]. destruct H13 as [lo1].
  rewrite H13 in Ho. inversion Ho. rewrite <- Hct in H8. inversion H8.
  rewrite H19 in H16. 
  apply heap_wfe with (h:=h) (o:=o) (cls_def:=cls) (F:=F') 
            (cn0:=clsT) (ho:=(Heap_OBJ cls F' lb')) 
            (lo:=lb') (method_defs:=method_defs)  (field_defs:=field_defs); auto.
  rewrite <- H16 in Hct. auto. rewrite H16. auto.  
  rewrite H in H13.  unfold lookup_heap_obj in H13. 
  rewrite <- H5 in H13. 
  assert (beq_oid o o = true). apply beq_oid_same. rewrite H15 in H13. 
  rewrite H1 in H13.  inversion H13. 
  rewrite <- H22 in H17.  rewrite <- H17 in H4.

  intro f.  intro cls_name'. rewrite HeqF'.
  case_eq (beq_id i f). intro.
  apply beq_equal in H20. 
  rewrite Hcls_def in Htyf. unfold find_fields in Htyf. 
   intro. rewrite H20 in H24. rewrite Htyf in H24.
  inversion H24. 
  exists v.  rewrite <- H26. split. auto.
  inversion Hv.  right. 
  rewrite <- H25 in typing_v. inversion typing_v. 
  rewrite Hy.
  destruct H34 as [F2]. destruct H34 as [lo2].
  destruct H35 as [field_defs2]. destruct H35 as [method_defs2]. 
  rewrite H in H34. 
  (* beq_oid o2 o = true; the field is pointing to an object of the same type as the current object*)
  case_eq (beq_oid o2 o). intro. 
  exists o2. exists F'. exists lb'. exists field_defs2. exists method_defs2. 
  split; auto. 
   unfold lookup_heap_obj. rewrite H36. 
  apply beq_oid_equal in H36.  rewrite H5 in H36. 
  rewrite H36 in H34 . unfold lookup_heap_obj in H34. 
  assert (beq_oid o0 o0 = true). apply beq_oid_same. rewrite H37 in H34. 
  rewrite H1 in H34.  inversion H34. 
  split.  rewrite <- H39 in H35. rewrite H21 in H35. rewrite H19 in H35. 
  rewrite <- H16 in H35. rewrite H35. auto. 
  rewrite H35 in H29. auto. 

  (* beq_oid o2 o = false*)
  intro. exists o2. exists F2. exists lo2. exists field_defs2. exists method_defs2. 
   split. auto. split. rewrite <- H5 in H34. 
    unfold lookup_heap_obj.     unfold lookup_heap_obj in H34. 
   rewrite H36. rewrite H36 in H34. fold lookup_heap_obj. fold lookup_heap_obj in H34.
   rewrite H34. rewrite H35. auto. rewrite H35 in H29. auto. 
  
  (*other possible values do not fit the typing*)
  rewrite <- H25 in typing_v. inversion typing_v. 
  left. auto. 
  rewrite <- H25 in typing_v. inversion typing_v. 
  rewrite <- H25 in typing_v. inversion typing_v. 
  rewrite <- H25 in typing_v. inversion typing_v.

  (*beq_id i f = false*)
  intro. rewrite H21 in H3. rewrite H19 in H3. rewrite Hcls_def in H3. inversion H3. 
  intro. 
  destruct H4 with (f:=f) (cls':=cls_name'). auto. 
  destruct H28. exists x.  split. auto. 
  destruct H29. left. auto.
  right. destruct H29 as [o']. destruct H29 as [F2]. destruct H29 as [lo2]. destruct H29 as [field_defs2].
  destruct H29 as [method_defs2]. destruct H29.  rewrite H in H30.
  rewrite Hy. rewrite <- H5 in H30.
  exists o'.
  (* o = o' *) 
  case_eq (beq_oid o' o). intro. 
  unfold lookup_heap_obj. rewrite H31. exists F'. exists lb'.
  destruct H30.  exists field_defs2. exists method_defs2. 
  unfold lookup_heap_obj in H30. rewrite H31 in H30. rewrite H1 in H30.
  inversion H30. rewrite H21 in H34. rewrite H19 in H34. rewrite <- H16 in H34.
  split. auto. split. rewrite H34. auto. auto. 

   (* o <> o' *) 
  intro. 
      unfold lookup_heap_obj.     unfold lookup_heap_obj in H30.
      rewrite H31. rewrite H31 in H30.  
      fold lookup_heap_obj.     fold lookup_heap_obj in H30.
      exists F2. exists lo2. exists field_defs2. exists method_defs2. auto.
*)
admit.
(* beq_oid o o0 = false *)
  
  

  induction h'. admit.


  intro. apply IHh.  admit. admit.
  inversion Hv. rewrite <- H0 in typing_v. inversion typing_v.
  apply T_ObjId with (cls_def:=cls_def0). auto.
  unfold lookup_heap_obj in H8. rewrite H in H8.

 

 rewrite H in Hy. fold update_heap_obj in Hy. 
  rewrite H in Ho. unfold lookup_heap_obj in Ho. rewrite H5 in Ho.
  fold lookup_heap_obj in Ho.
  
  apply IHwfe_h. auto. 
  inversion Hv. rewrite <- H6 in typing_v. inversion typing_v.
  apply T_ObjId with (cls_def:=cls_def1). auto.
  rewrite H in H14.
  subst. ` 


  rewrite H in H14. rewrite H5 in Hy. 
  fold lookup_heap_obj in Hy. fold update_heap_obj in Hy.



   forall (f : id) (cls' : cn),
     type_of_field field_defs0 f = Some cls' ->
     exists v : tm,
       F f = Some v /\
       (v = null \/
        (exists
           (o' : oid) (F' : FieldMap) (lx : Label) (field_defs0 : list field) 
         (method_defs0 : list method_def),
           v = ObjId o' /\
           lookup_heap_obj h'0 o' =
           Some (Heap_OBJ (class_def cls' field_defs0 method_defs0) F' lx) /\
           ct cls' = Some (class_def cls' field_defs0 method_defs0)))
  
  



 split; auto.
  
  

  
   
 rewrite H in Hy.
Qed.. 
  
  


(* if *)
+ intro T.. intro typing. intro t'.  intro step. 
    inversion step. rewrite H in H10. rewrite H2 in H10.
    inversion H10. rewrite <- H15. rewrite <- H16.
    split; auto.
    rewrite H in H10. rewrite H2 in H10.
    inversion H10. rewrite <- H15. rewrite <- H16.
    split; auto. 

(* sequence *)
+ intro T. intro typing. intro t'.  intro step. 
    inversion step. inversion typing.
    apply IHt1 with (T:=T0) (t':=s1'); auto.

    rewrite H in H8. rewrite H2 in H8. inversion H8.
    rewrite <- H10. rewrite <- H11.
    split;auto.

(* return *)
+ intro T. intro typing. intro t'.  intro step. 
    inversion step. inversion typing.
    apply IHt with (T:=T) (t':=e'); auto.
    subst. inversion H8. inversion H13.
    rewrite <- H3. split. auto.
    remember (join_label (get_stack_label lsf) (get_current_label s'0)) as lb'.

    inversion H1. rewrite <- H15 in H2.  
    inversion H2. rewrite H18 in H10.
    intuition.

    subst. inversion H. 
    apply change_label_preserve_wfe; auto.

(* obj id *)
+ intro T. intro typing. intro t'.  intro step. 
    inversion step.

(* runtime labeled *)
+ intro T. intro typing. intro t'.  intro step. 
    inversion step. 

(* runtime opaque labeled *)
+ intro T. intro typing. intro t'.  intro step. 
    inversion step. 

Admitted. 

Theorem progress : forall t T sigma gamma CT s h, 
  sigma = SIGMA s h ->  wfe_heap CT gamma h -> wfe_stack CT gamma h s -> 
  has_type CT gamma s h t T -> value t \/ (exists config', Config t sigma ==> config').
Proof with auto.
  intros t T sigma gamma CT s h.
  intros. 

  induction H2. 
(* TVar *)
- right. 
      inversion H1. 
          + subst. inversion H5.
          + subst. destruct H4 as [v].  
          remember (Labeled_frame lb sf) as lsf. 
           exists (Config v (SIGMA (lsf :: s') h)). 
            apply ST_var with 
                (id:=x) (lb:=lb) (sf:=sf) (lsf:=lsf) (v:=v) 
                (sigma:=(SIGMA (lsf :: s') h)) (s':=s') (s:=(lsf :: s')) (h:=h).
                auto. auto. auto. auto.  

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
      remember (SIGMA s' h) as sigma'.
            exists (Config v sigma'). apply ST_fieldRead2 with 
            (sigma:=sigma) (sigma':=sigma') (o:=o) (s:=s) (h:=h) (fname:=f) (lb:=lb) 
            (cls:=cls_def) (fields:=F) (v:=v) (l':=l') (s':=s'). 
            auto. auto. auto.            auto. auto. auto. 
    (* skip *)
    rewrite <- H7 in H2. inversion H2. 
    (* call field access on null point object *)
    exists Error_state. apply ST_fieldReadException.
    (* label is primitive: calling field access is not valid *)
    rewrite <- H7 in H2. inversion H2.
   
     (* call field access on labeled value*)
    {rewrite <- H7  in H2. inversion H2. }
    
     (* call field access on opaque label value*)
    {rewrite <- H7  in H2. inversion H2. }

     (* context rule *)
    + destruct H6. destruct x. 
    exists (Config (FieldAccess t f) s0).
    apply ST_fieldRead1 with (sigma:=sigma) (sigma':=s0) (e:=e) (e':=t) (f:=f). assumption.

    exists Error_state. apply ST_fieldRead3. auto. 
    

(* method call *)
- right.
   destruct IHhas_type1. auto. auto. auto. 
       + inversion H6. rewrite <- H7 in H2_. inversion H2_.
          (* case analysis for argument: if the argument is a value *)
             destruct IHhas_type2. auto. auto. auto. subst. 
            remember (sf_update empty_stack_frame arg_id argu) as sf. 
            remember (SIGMA s h ) as sigma.
            remember (current_label sigma) as l.
            remember (Labeled_frame l sf) as lsf. 
            remember (cons lsf s) as s'.
            remember (SIGMA s' (get_heap sigma)) as sigma'.
            exists (Config ((Return body)) sigma').
            destruct H15 as [F]. destruct H as [lo].
            apply ST_MethodCall3 with (sigma:=sigma) (sigma':=sigma') (o:=o) (s:=s) (h:=h) (cls:=cls_def) (fields:=F) 
                                       (v:=argu) (lx:=lo) (l:=l) 
                                       (theta:=lsf) (s':=s') (sf:=sf) (lsf:=lsf) (arg_id:=arg_id) 
                                        (cls_a:=cls_a) (body:=body) (meth:=meth) (returnT:=returnT) ;auto.
            rewrite <- H10 in H2. inversion H2.  auto. 
          (* case analysis for argument, if the argument is not a value *)
            subst.
                destruct H17 as [config']. destruct config' as [t' | sigma']. 
                pose proof (excluded_middle_opaqueLabel argu).
                destruct H4.
                  (* case for argu = unlabelOpaque t *)
                  destruct H4 as [t]. 
                  rewrite -> H4 in H. inversion H. subst. 
                  exists (Config (MethodCall (ObjId o) meth (unlabelOpaque e')) s0).
                  apply ST_MethodCall2 with (sigma:=(SIGMA s h)) (sigma':=s0) 
                                            (v:=(ObjId o)) (e:=unlabelOpaque t) (e':=unlabelOpaque e') (id:=meth).
                  intros. subst. intro contra. inversion contra. rewrite -> H11 in H. inversion H4.
                      rewrite <- H9 in H; subst; inversion H8. auto.  subst. inversion H8.  subst.
                      inversion H8. subst. inversion H8. subst. inversion H8. subst. inversion H8.
                      assumption. apply v_oid. 
                      subst. 
                      remember (SIGMA s h ) as sigma.
                      remember (sf_update empty_stack_frame arg_id t') as sf.
                      remember (join_label lb (current_label sigma)) as l'. 
                      remember (Labeled_frame l' sf) as lsf. 
                      remember (cons lsf s) as s'.
                      remember (SIGMA s' (get_heap sigma)) as sigma''.
                      exists (Config (Return body) sigma'').  
                      destruct H15 as [F]. destruct H4 as [lo].
                      apply ST_MethodCall_unlableOpaque with (sigma:=sigma) (sigma':=sigma'') (o:=o) (s:=s) (h:=h) 
                                            (cls:=cls_def0) (fields:=F) (v:=t') (lx:=lo) (l':=l') (lb:=lb) (s':=s')
                                           (sf:=sf) (lsf:=lsf) (arg_id:=arg_id) (cls_a:=cls_a) (body:=body) 
                                           (meth:=meth) (returnT:=returnT) .
                      auto. auto. auto. auto. auto. auto. subst. 
                      rewrite <- H10 in H2. inversion H2. rewrite <- H8. auto. 
                      auto.
                  (*exception case
                  subst. exists NPE. exists (SIGMA s h).
                  apply ST_MethodCallOpaqueDataException with (sigma:=(SIGMA s h)) (o:=o).   *)

                  (* case for argu <> unlabelOpaque t *)
                  exists (Config (MethodCall (ObjId o) meth t') s0). 
                  apply ST_MethodCall2 with (sigma:=(SIGMA s h)) (sigma':=s0) (v:=((ObjId o))) 
                                            (e:=argu) (e':=t') (id:=meth).
                  intro. intro. intro. 

                  assert (argu <> unlabelOpaque t).  apply (H4 t). apply (H4 t). auto. apply v_oid.
                   
                  exists Error_state. 
                   apply ST_MethodCall5 with (sigma:=(SIGMA s h)) (v:=(ObjId o)) (e:=argu) (id:=meth).
                  intros. intro contra. rewrite contra in H. inversion H. inversion H4. 
                  rewrite <- H12 in H9. inversion H9.                    rewrite <- H12 in H9. inversion H9.
                  rewrite <- H12 in H9. inversion H9.                    rewrite <- H12 in H9. inversion H9.
                  rewrite <- H12 in H9. inversion H9.                    rewrite <- H12 in H9. inversion H9.
                  rewrite <- H9 in H7. auto. auto. auto. subst. inversion H2_. 

                   exists Error_state. 
                  apply ST_MethodCallException with (sigma:=sigma) (v:=argu) (meth:=meth). 

                  rewrite <- H7 in H2_. inversion H2_. 
                rewrite <- H7 in H2_. inversion H2_.                 
                 rewrite <- H7 in H2_. inversion H2_. 
      +  destruct H6 as [config']. destruct config'. 

            exists (Config (MethodCall t meth argu) (s0)).
                  apply ST_MethodCall1 with (sigma:=sigma) (sigma':=s0) (e2:=argu) (e:=e) (e':=t) (id:=meth). apply H6.

            exists Error_state. apply ST_MethodCall4 with (sigma:=sigma) (e:=e) (e2:=argu) (id:=meth). auto. 

(* new expression *)
- right. inversion H0. 
    assert (exists o, empty_heap o = None). 
      unfold empty_heap. auto. exists (OID 0). auto. 
      destruct H7 as [o]. 

      remember (init_field_map (find_fields cls_def) empty_field_map) as F.
      remember (current_label sigma) as lb. 
      remember  (add_heap_obj h o (Heap_OBJ cls_def F lb)) as h'.
      remember (SIGMA s h') as sigma'.
      exists (Config (ObjId o) sigma').
       
      destruct H3 as [field_defs]. destruct H3 as [method_defs].
      apply ST_NewExp with (sigma:=sigma) (sigma':=sigma') (F:=F) (o:=o) (h:=h) (cls:=cls_def)
                  (h':=h') (s:=s) (lb:=lb) (cls_name:=cls_name) 
                  (field_defs:= field_defs) (method_defs:=method_defs).

      subst; auto. rewrite <- H6.  auto.  auto. auto. auto.  auto. auto.  
      
      remember (current_label sigma) as lb. 
      destruct H11.
      remember (init_field_map (find_fields cls_def) empty_field_map) as F'.
      remember (add_heap_obj h x (Heap_OBJ cls_def F' lb)) as h''.
      remember (SIGMA s h'') as sigma''.
      exists (Config (ObjId x) sigma''). 
      destruct H3 as [field_defs']. destruct H3 as [method_defs'].

      apply ST_NewExp with (sigma:=sigma) (sigma':=sigma'') 
                                          (F:=F') (o:=x) (h:=h) (cls:=cls_def)
                                          (h':=h'') (s:=s) (lb:=lb) (cls_name:=cls_name)
                                          (field_defs:=field_defs') (method_defs:=method_defs').
      auto. auto.  auto.  auto. auto. auto.  auto.

(* label *)
- left. apply  v_label.


(* label Data *)
- right. destruct IHhas_type2. auto. auto. auto. 
            destruct IHhas_type1. auto. auto. auto. 
            
            (* subgoal #1 *)
           exists (Config (v_l e lb)sigma).
                apply ST_LabelData2 with (sigma:=sigma) (lb:=lb) (v:=e). subst. auto.  auto.

            (* subgoal #2 *)  
                destruct H3 as [config']. inversion H3.  

            (* subgoal #3 *)
                destruct H2 as [config']. destruct config'. 
                    exists (Config (labelData t lb) s0).
                    apply ST_LabelData1 with (sigma:=sigma) (sigma':=s0) (e:=e) (e':=t) (lb:=lb).
                    auto.

           (* subgoal #4*)
               exists Error_state. 
                  apply ST_LabelDataError with (e:=e) (sigma:=sigma) (lb:=lb). auto. 

(* unlabel : *)
- right.
 
            destruct IHhas_type. auto. auto. auto. 
             (* subgoal #1 *)
                + inversion H3. 
                     rewrite <- H4 in H2. inversion H2. 
                     rewrite <- H4 in H2.  inversion H2. 
                    exists Error_state.  apply ST_unlabelDataException with (sigma:=sigma).
                    rewrite <- H4 in H2.  inversion H2.

             (* subgoal #2 *)
                remember ( join_label lb (current_label sigma)) as l'.
                remember (update_current_label s l') as s'.
                remember (SIGMA s' (get_heap sigma)) as sigma'.
                exists (Config v sigma'). 
                apply ST_unlabel2 with (sigma:=sigma) (s':=s') (sigma':=sigma') (l':=l') (s:=s) (h:=h) (lb:=lb) (v:=v). 
                auto. auto. auto. auto. auto.

            (* subgoal #3 *)
                rewrite <- H4 in H2.  inversion H2. 

              + destruct H3 as [config']. 
                 destruct config'. 
                 exists (Config (unlabel t) s0). 
                 apply ST_unlabel1 with (sigma:=sigma) (sigma':=s0) (e:=e) (e':=t). auto. 
                 exists Error_state. apply ST_unlabelContextError with (sigma:=sigma) (e:=e). auto. 
  


(* label Of *)
(* same issue as above, we may need to add (v_l v lb) as a value*)
- right. 
         destruct IHhas_type. auto. auto. auto. 
            (* subgoal #1 *)
                + inversion H3. rewrite <- H4 in H2. inversion H2. 
                    rewrite <- H4 in H2. inversion H2. 
                    exists Error_state.  apply ST_labelOfDataException with (sigma:=sigma).
                    rewrite <- H4 in H2.  inversion H2.
                    
                   exists (Config (l lb) (sigma)). apply ST_labelof2 with (v:=v) (lb:=lb).

                    rewrite <- H4 in H2. inversion H2. 
             (* subgoal #2 *)
                + destruct H3 as [config']. destruct config'. 
                    exists (Config (labelOf t) s0). apply ST_labelof1 with (sigma:=sigma) (sigma':=s0) (e:=e) (e':=t). auto.
    
             (*error state *)
                 exists Error_state. apply ST_labelofCtxError with (e:=e) (sigma:=sigma). auto. 

(* unlabel opaque *)
- right. 
         destruct IHhas_type. auto. auto. auto. 
            (* subgoal #1 *)
                + inversion H3. rewrite <- H4 in H2. inversion H2. 
                    rewrite <- H4 in H2. inversion H2. 
                    exists Error_state.  apply ST_unlabel_opaqueDataException with (sigma:=sigma).
                    rewrite <- H4 in H2.  inversion H2.
              
                     rewrite <- H4 in H2. inversion H2. 
 
                remember ( join_label lb (current_label sigma)) as l'.
                remember (update_current_label s l') as s'.
                remember (SIGMA s' (get_heap sigma)) as sigma'.
                exists (Config v sigma'). 
                apply ST_unlabel_opaque2 with (sigma:=sigma) (s':=s') (sigma':=sigma') (l':=l') (s:=s) (h:=h) (lb:=lb) (v:=v). 
                auto. auto. auto. auto. 

             (* subgoal #2 *)
                + destruct H3 as [config']. destruct config'. 
                    exists (Config (unlabelOpaque t) s0). apply ST_unlabel_opaque1 with (sigma:=sigma) (sigma':=s0) (e:=e) (e':=t). auto.

                exists Error_state. apply ST_unlabel_opaque_ctx_error with (sigma:=sigma) (e:=e).  auto. 

(* opaque call *)
- right.  destruct IHhas_type. auto. auto. auto.
            (* opaquecall won't be applied on values  *)

            remember (current_label sigma) as lb. 
            exists (Config (v_opa_l e lb)  sigma). 
            apply ST_opaquecall_val2 with (v:=e) (sigma:=sigma) (lb:=lb). auto. auto. 

            subst. destruct H3 as [config'].
                pose proof (excluded_middle_returnT e).
                destruct H3.
                  (* case for e = return t *)
                  destruct H3 as [t].
                  rewrite -> H3 in H. 
                  inversion H.  subst. 
                  exists (Config (opaqueCall(Return e')) sigma').
                  apply ST_opaquecall_return1 with (sigma:=(SIGMA s h)) (sigma':=sigma') (e:= t) (e':=e').
                  auto.

                  exists Error_state. rewrite H3.  apply ST_opaquecall_return_error with (sigma:=(SIGMA s h)) (e:=t).
                  auto. 

                  destruct config'.
                  remember  (current_label sigma) as lb. 
                  exists (Config (v_opa_l t lb) (SIGMA s' h)).
                  rewrite H3. 
                  apply ST_opaquecall_return2 with (sigma:=(SIGMA s h) ) (sigma':=(SIGMA s' h)) (s:=s) (h:=h) 
                                            (lb:=lb) (s':=s') (lsf:=lsf) (v:=t).
                  auto. inversion H7.  auto. rewrite <- H5.  auto. auto. auto.

                  inversion H11. 

                    (* case for e <> return t *)

                  destruct config'. 
                  exists (Config (opaqueCall t) s0). 
                  apply ST_opaquecall1 with  (sigma:=(SIGMA s h) ) (sigma':=(s0)) (e:=e) (e':=t). 

                  intros. apply H3. auto. 

                  exists Error_state. apply ST_opaquecall_ctx_error with (sigma:=(SIGMA s h)) (e:=e). auto. 

(* Skip *)
  - left. apply v_none. 

(* assignment *)
- right. destruct IHhas_type. auto. auto. auto.
                  remember (update_stack_top s x e) as s0.
                  remember (SIGMA s0 h) as sigma'.
                  exists (Config Skip sigma').
                  apply ST_assignment2 with (sigma:=sigma) (sigma':=sigma') (id:=x) (v:=e) (s':=s0) (s:=s) (h:=h).
                  auto. auto. auto. auto.

                  destruct H7 as [config']. destruct config'. 
                  exists (Config (Assignment x t) s0). 
                  apply ST_assignment1 with (sigma:=sigma) (sigma':=s0) (e:=e) (e':=t) (id:=x).
                  auto.

                  exists Error_state. 
                  apply ST_assignment_ctx_error with (sigma:=sigma) (e:=e) (id:=x). auto.  

(* FieldWrite *)
-right. 
      destruct IHhas_type1. auto. auto. auto. 
       + inversion H4. 
          (* case analysis for argument: if the argument is a value *)
             destruct IHhas_type2. auto. auto. auto. subst. 
            assert (exists fieldsMap lb, h(o) = Some (Heap_OBJ cls_def fieldsMap lb)).
            remember (SIGMA s h ) as sigma.
            apply wfe_oid with (o:=o) (ct:=CT) (gamma:=Gamma) (s:=s) (h:=h) 
                          (sigma:=sigma) (cls_def:=cls_def) (cn:=clsT). auto. auto. auto. auto.
            destruct H as [F]. destruct H as [lb]. 
            remember (SIGMA s h ) as sigma.
            remember (join_label lb (current_label sigma)) as l'. 
            remember (fields_update F f e) as F'. 
            remember (add_heap_obj h o (Heap_OBJ cls_def F' l')) as h'.
            remember (SIGMA s h') as sigma'.
            exists (Config Skip sigma').
            apply ST_fieldWrite3 with (sigma:=sigma) (sigma':=sigma') (o:=o) (s:=s) (h:=h) (h':=h') (f:=f) 
                                                      (lb:=lb) (cls:=cls_def) (F:=F) (F':=F') (v:=e) (l':=l').
            auto. auto. auto. auto. auto. auto.  auto.
            
          (* case analysis for argument, if the argument is not a value *)
            subst. 
                destruct H6 as [config'].
                pose proof (excluded_middle_opaqueLabel e).
                destruct H5.
                  (* case for e = unlabelOpaque t *)
                  destruct H5 as [t]. 
                  rewrite -> H5 in H. inversion H. subst. 
                  exists (Config (FieldWrite (ObjId o) f (unlabelOpaque e')) sigma').
                  apply ST_fieldWrite2 with (sigma:=(SIGMA s h)) (sigma':=sigma') 
                                            (v:=(ObjId o)) (e2:=unlabelOpaque t) (e2':=unlabelOpaque e') (f:=f).
                  intros. subst. intro contra. inversion contra. rewrite H8 in H9. 
                  inversion H5. 
                  rewrite <- H7 in H9.  inversion H9.                   rewrite <- H7 in H9.  inversion H9. 
                  rewrite <- H7 in H9.  inversion H9.                   rewrite <- H7 in H9.  inversion H9. 
                  rewrite <- H7 in H9.  inversion H9.                   rewrite <- H7 in H9.  inversion H9. 
                  auto. auto. 

                  exists Error_state. subst. apply ST_fieldWrite_ctx_error2 
                        with (sigma:=(SIGMA s h)) (f:=f) (v:=(ObjId o)) (e2:=(unlabelOpaque t)).

                  intros. intro contra. inversion contra. rewrite H8 in H9. inversion H5. 
                  rewrite <- H7 in H9.  inversion H9.                   rewrite <- H7 in H9.  inversion H9. 
                  rewrite <- H7 in H9.  inversion H9.                   rewrite <- H7 in H9.  inversion H9. 
                  rewrite <- H7 in H9.  inversion H9.                   rewrite <- H7 in H9.  inversion H9. 
                  auto. auto. 

                  assert (exists fieldsMap lb, h(o) = Some (Heap_OBJ cls_def fieldsMap lb)).
                      apply wfe_oid with (o:=o) (ct:=CT) (gamma:=Gamma) (s:=s) (h:=h) 
                                    (sigma:=sigma) (cls_def:=cls_def) (cn:=clsT). auto. auto. auto. auto.
                      destruct H13 as [F]. destruct H13 as [lo]. 
                      remember (fields_update F f v) as F'. 
                      remember (join_label lo lb) as l''. 
                      remember (add_heap_obj h o (Heap_OBJ cls_def F' l'')) as h'.
                      remember (SIGMA s h') as sigma''.

                      exists (Config Skip sigma'').
                      apply ST_fieldWrite_opaque with (sigma:=(SIGMA s h)) (sigma':=sigma'') (o:=o) (s:=s) (h:=h) (h':=h') (f:=f) 
                                                      (lb:=lb) (lo:=lo) (cls:=cls_def) (F:=F) (F':=F') (v:=v) (l':=l'') (e2:=e).
                      rewrite <- H6 in H5. auto. auto. auto. auto. auto. auto.  auto.

                      exists Error_state. 

                      apply ST_fieldWrite_ctx_error2 with (sigma:=(SIGMA s h)) (f:=f) (v:=(ObjId o)) (e2:=e).
                       intros. rewrite H5. intro contra. inversion contra. rewrite <- H12 in H10.
                      rewrite H7 in H10. auto. auto. subst. auto.   

                  (* case for argu <> unlabelOpaque t *)
                  destruct config'. 
                  exists (Config (FieldWrite (ObjId o) f t) s0). 
                  apply ST_fieldWrite2 with (sigma:=(SIGMA s h)) (sigma':=s0) (v:=((ObjId o))) 
                                            (e2:=e) (e2':=t) (f:=f).
                  intros. apply H5. apply v_oid. assumption.

                  exists Error_state. 
                      apply ST_fieldWrite_ctx_error2 with (sigma:=(SIGMA s h)) (f:=f) (v:=(ObjId o)) (e2:=e).
                       intros. apply H5.  auto. auto. 
     
                  destruct  IHhas_type2.  auto. auto. auto. 
                  rewrite <- H5 in H2_. inversion H2_.                   rewrite <- H5 in H2_. inversion H2_.
  
                  exists Error_state.
                  apply ST_fieldWriteException with (sigma:=sigma) (f:=f) (v:=e). 

                  rewrite <- H5 in H2_. inversion H2_.                   rewrite <- H5 in H2_. inversion H2_.
                  rewrite <- H5 in H2_. inversion H2_.       


          +    destruct H4 as [config'].
                 destruct config'. 
                  exists (Config (FieldWrite t f e) (s0)). 
                  apply ST_fieldWrite1 with (sigma:=sigma) (sigma':=s0) (f:=f) (e1:=x) (e1':=t) (e2:=e).
                  auto. 
        
              exists Error_state. 
              apply ST_fieldWrite_ctx_error1 with (sigma:=sigma) (f:=f) (e1:=x) (e2:=e). auto. 

(* if *)
- destruct IHhas_type1. auto. auto. auto. inversion H2. destruct H2. inversion H2. subst. 
   destruct IHhas_type2. auto. auto. auto. inversion H. destruct H. inversion H. subst. 
    rewrite H6 in H5. inversion H5. subst. 
    inversion H1. 
    rewrite <- H14 in H6. inversion H6. rewrite <- H17 in H11.  inversion H11. 

    inversion H10. 
    
    rewrite H16 in H3. rewrite H3 in H6. inversion H6. 
    destruct H17 with id1 v. rewrite H24. auto. 
    destruct H17 with id2 v0. rewrite H24. auto. 
    (* v= null and v0 =null*)
    rewrite <- H26. 
    remember (SIGMA s h) as sigma.
    right. exists (Config s1 sigma).
          apply ST_if_b1 with (sigma:=sigma) (s1:=s1) (s2:=s2) 
                                (s:=s) (h:=h) (lsf:=lsf) (s':=s') (lb:=lb) (sf:=sf) (id1:=id1) (id2:=id2).
    auto. 
    rewrite H21. rewrite H16. rewrite <- H25.  auto. 
    rewrite <- H23. rewrite <-H24. rewrite <- H16. auto. 
    rewrite <- H9. rewrite <- H11. rewrite H22. rewrite H27. auto. 
    (* v= ObjId o and v0 =null*)
    destruct H27 as [o]. destruct H27 as [cls_name]. destruct H27. 
    remember (SIGMA s h) as sigma. 
    right. exists (Config s2 sigma). rewrite <- H26. rewrite <- Heqsigma.
    apply ST_if_b2 with (sigma:=sigma) (s1:=s1) (s2:=s2)
                                (s:=s) (h:=h) (lsf:=lsf) (s':=s') (lb:=lb) (sf:=sf) (id1:=id1) (id2:=id2). 
    auto.
    rewrite H21. rewrite H16. rewrite <- H25.  auto. 
    rewrite <- H23. rewrite <-H24. rewrite <- H16. auto.
    intro contra. rewrite <- H9 in contra. rewrite <- H11 in contra.
    rewrite H22 in contra. rewrite H27 in contra.  inversion contra.

    (* v= null and v0 =ObjId o*)
    destruct H17 with id2 v0. rewrite H24. auto. 
    rewrite <- H26.   
    remember (SIGMA s h) as sigma.
    right. 
    destruct H22 as [o]. destruct H22 as [cls_name]. destruct H22.
    exists (Config s2 sigma). 
    apply ST_if_b2 with (sigma:=sigma) (s1:=s1) (s2:=s2)
                                (s:=s) (h:=h) (lsf:=lsf) (s':=s') (lb:=lb) (sf:=sf) (id1:=id1) (id2:=id2). 
    auto.
    rewrite H21. rewrite H16. rewrite <- H25.  auto. 
    rewrite <- H23. rewrite <-H24. rewrite <- H16. auto.
    intro contra. rewrite <- H9 in contra. rewrite <- H11 in contra.
    rewrite H22 in contra. rewrite H27 in contra.  inversion contra.

    (* v= ObjId o1 and v0 =ObjId o2*)  
          (*case analysis v = v0*)
          destruct H22 as [o]. destruct H27 as [o'].   
          destruct H22 as [cls_name]. destruct H27 as [cls_name']. 
          case_eq (beq_oid o o'). intro. 
          assert (o=o').
          apply beq_oid_equal with (x:=o) (x':=o'). auto. 
          destruct H22. destruct H27. rewrite <- H29 in H27. rewrite <- H27 in H22.
          rewrite H22 in H9. rewrite H9 in H11. 
  
          rewrite <- H26. 
          remember (SIGMA s h) as sigma.
          right. exists (Config s1 sigma ).
          apply ST_if_b1 with (sigma:=sigma) (s1:=s1) (s2:=s2)
                                (s:=s ) (h:=h) (lsf:=lsf) (s':=s') (lb:=lb) (sf:=sf) (id1:=id1) (id2:=id2). 
          auto. rewrite H21. rewrite H16. rewrite <- H25.  auto.
          inversion H6. rewrite <- H33. rewrite <- H34. rewrite <- H16. auto. auto. 
          (*case analysis v != v0*)
          intro. destruct H22. destruct H27.
          assert (Some v0 <> Some v).  intro contra. inversion contra.  
          rewrite H32 in H27. rewrite H27 in H22. inversion H22. 
          rewrite H33 in H28. assert (beq_oid o o = true). apply beq_oid_same.
          rewrite H31 in H28. inversion H28. 

          right. remember (SIGMA s h) as sigma. rewrite <- H26. 
          exists (Config s2 sigma ). rewrite <- Heqsigma.
          apply ST_if_b2 with (sigma:=sigma) (s1:=s1) (s2:=s2)
                                (s:=s ) (h:=h) (lsf:=lsf) (s':=s') (lb:=lb) (sf:=sf) (id1:=id1) (id2:=id2). 
          auto.  rewrite H21. rewrite H16. rewrite <- H25.  auto.
          inversion H6. rewrite <- H33. rewrite <- H34. rewrite <- H16. auto. 
          rewrite H9 in H31. rewrite H11 in H31.  auto. 
          

(* sequence *)
- right. destruct IHhas_type1. auto. auto. auto.
    exists (Config e2 sigma).
   
   apply ST_seq2 with (sigma:=sigma) (v:=e1) (s:=e2); auto.
  
  destruct H2 as [config'].
  destruct config'.
  exists (Config (Sequence t e2) s0). 
   apply ST_seq1 with (sigma:=sigma) (s1:=e1) (s2:=e2) (s1':=t); auto.

  exists Error_state. apply ST_seq_ctx_error with (sigma:=sigma) (s1:=e1) (s2:=e2).
  auto. 

(* return e *)
- right. destruct IHhas_type. auto. auto. auto. 
  assert (exists lsf s', s = cons lsf s'). 
  apply stack_not_nil with (sigma:=sigma) (gamma:=Gamma) (CT:=CT) (s:=s) (h:=h).
  auto. auto. auto.
  destruct H5 as [lsf]. destruct H5 as [s'].
  remember (join_label (get_current_label s) (get_current_label s')) as l'.
  remember (update_current_label s' l' ) as s''.
  remember (SIGMA s'' h) as sigma'.
  exists (Config e sigma').
  apply ST_return2 with (sigma:=sigma) (sigma':=sigma') (v:=e)
                                    (s:=s) (s':=s') (s'':=s'') (h:=h) (lsf:=lsf) (l':=l').
  auto. auto. auto. auto. auto. auto. 

  destruct H4 as [config'].
  destruct config'. 
  exists (Config (Return t) s0). 
  apply ST_return1 with (sigma:=sigma) (sigma':=s0) (e:=e) (e':=t). auto.

  exists Error_state. apply ST_return_ctx_error with (sigma:=sigma) (e:=e). auto. 

(* ObjId o *)
- left. apply v_oid. 

(* v_l *)
- left. apply v_labeled. 

(* v_opl_l *)
- left. apply v_opa_labeled.
Qed.




(* types of variable in stack are consistent with the object identifiers that they are pointing to.  *)
Lemma stack_frame_preserve_typing : forall sigma gamma CT s h x o s' cls_name  cls_name' method_defs field_defs lb sf cls_def F, 
    sigma = SIGMA s h ->  wfe_heap CT gamma h -> wfe_stack CT gamma h s -> 
    (s = cons (Labeled_frame lb sf) s') ->
    (sf x = Some (ObjId o)) -> 
    h(o) = Some (Heap_OBJ cls_def F lb) -> 
    cls_def = class_def cls_name' field_defs method_defs ->
    gamma x = Some (classTy cls_name) -> cls_name' = cls_name.
Proof.
    intros. inversion H1. rewrite H8 in H4.  inversion H4.
    subst.  inversion H11. destruct H2 with cls_name x. auto. destruct H15. 
      destruct H16. subst. inversion H7. inversion H. subst. rewrite H3 in H15. inversion H15. 

    destruct H16. destruct H16. destruct H17 as [F0]. 
         destruct H17 as [lx]. destruct H17 as [field_defs0]. destruct H17 as [method_defs0]. 
    destruct H17. subst. inversion H7. inversion H. subst. rewrite H3 in H15.  inversion H15.
    rewrite <- H12 in H17. rewrite H4 in H17. inversion H17. auto. 
Qed.

Lemma field_consist_typing : forall CT gamma v h o cls_def F f lb field_cls_name cls_name field_defs method_defs,
  wfe_heap CT gamma h -> 
  h(o) = Some (Heap_OBJ cls_def F lb) -> 
  cls_def = class_def cls_name field_defs method_defs ->
  type_of_field field_defs f = Some field_cls_name ->
  F f = Some v ->
     ( v = null \/ 
          ( exists o' field_defs0 method_defs0 field_cls_def F' lo, 
           v = (ObjId o') 
          /\ field_cls_def = (class_def field_cls_name field_defs0 method_defs0) 
          /\ h(o') = Some (Heap_OBJ field_cls_def F' lo) 
          /\ CT field_cls_name = Some field_cls_def 
          )
      ).
Proof with auto. 
  intros. induction H. inversion H0.
  case_eq (beq_oid o0 o). intro. rewrite H6 in H0. rewrite H11 in H0. 
  rewrite H0 in H5.  inversion H5. rewrite <- H13 in H8.
rewrite H1 in H8. inversion H8. 
  destruct H9 with  f field_cls_name. rewrite <- H17. auto. 
  rewrite <- H14 in H12.  destruct H12. rewrite H3 in H12.  inversion H12. 
  destruct H19. 

  left. auto.
  right. destruct H19 as [o']. destruct H19 as [F']. destruct H19 as [lx].
     destruct H19 as [field_defs']. destruct H19 as [method_defs'].
     exists o'. exists  field_defs'. exists method_defs'. 
     exists (class_def field_cls_name field_defs' method_defs'). 
     exists F'. exists lx. 

    destruct H19.     destruct H20. 
    split. auto. split. auto. auto. 


    intro.  
    assert (
             v = null \/
             (exists
                (o' : oid) (field_defs0 : list field) (method_defs0 : 
                                                       list method_def) 
              (field_cls_def : CLASS) (F' : FieldMap) (lo : Label),
                v = ObjId o' /\
                field_cls_def =
                class_def field_cls_name field_defs0 method_defs0 /\
                h o' = Some (Heap_OBJ field_cls_def F' lo) /\
                ct field_cls_name = Some field_cls_def)).
 apply  IHwfe_heap. auto.
rewrite H6 in  H0. rewrite H11 in H0. auto. auto. 


 destruct H12. left. auto. 

  right.

 destruct H12 as [o']. destruct H12 as [field_defs']. 
destruct H12 as [method_defs'].
destruct H12 as [field_cls_def'].
destruct H12 as [F']. destruct H12 as [lx].
destruct H12. destruct H13. destruct H14. 

 case_eq  (beq_oid o0 o'). intro. 
exists o0. exists field_defs. exists method_defs. 
exists field_cls_def'. exists F. exists lb. 


assert (o0=o').
 apply beq_oid_equal with (x:=o0) (x':=o'). auto. rewrite H17. 
rewrite <- H17 in H14. rewrite  H in H14. inversion H14.


intro.  
     exists o'. exists  field_defs'. exists method_defs'.
     exists (class_def field_cls_name field_defs' method_defs'). 
     exists F'. exists lx.
split. auto. split. auto. split.  rewrite H6. rewrite H16.  rewrite H13 in H14. auto. rewrite H13 in H15. auto.  
Qed. 




Lemma heap_preserve_typing : forall h h' t T CT gamma,
(forall o cls_def F lo, h o = Some  (Heap_OBJ cls_def F lo) 
                              -> exists F' lo', h' o = Some  (Heap_OBJ cls_def F' lo') )
 -> has_type CT gamma h t T -> has_type CT gamma h' t T.
Proof. 
  intros h h' t T CT gamma. 
  intro Hyh.
  intro Hy.  
  induction Hy. 
  + apply T_Var. auto. 
  + apply T_null.
  + apply T_FieldAccess with (cls_def:=cls_def) (clsT:=clsT) 
            (fields_def:=fields_def); auto. 
  + apply T_MethodCall with (T:=T) (cls_def:=cls_def) (body:=body) (arg_id:=arg_id)
        (arguT:=arguT) (para_T:=para_T) (cls_a:=cls_a); auto.
  + apply T_NewExp with (cls_def:=cls_def). auto. apply H0.
  + apply T_label.
  + apply T_labelData; auto.
  + apply T_unlabel; auto.
  + apply T_labelOf with (T:=T); auto. 
  + apply T_unlabelOpaque. auto.
  + apply T_opaqueCall. auto.
  + apply T_skip.
  + apply T_assignment with (T:=T); auto. 
  + apply T_FieldWrite with (cls_def:=cls_def) (clsT:=clsT) (cls':=cls'); auto. 
  + apply T_if with (T:=T); auto.
  + apply T_sequence with (T:=T); auto.
  + apply T_return; auto. 
  + apply T_ObjId with (cls_def:=cls_def). 
    auto. destruct H0 as [F]. destruct H0 as [lo].
    
    destruct Hyh with (o:=o) (cls_def:=cls_def) (F:=F) (lo:=lo).
    auto. destruct H2 as [lx]. exists x. exists lx. auto. auto. 
  + apply T_v_l; auto.
  + apply T_v_opa_l; auto.
Qed. 



Lemma reduction_preserve_heap_pointer : forall t s s' h h', 
     forall CT gamma T, has_type CT gamma h t T ->
     forall t', reduction (Config t (SIGMA s h)) (Config t' (SIGMA s' h')) -> 
     (forall o cls_def F lo, h o = Some  (Heap_OBJ cls_def F lo) 
                              -> exists F' lo', h' o = Some  (Heap_OBJ cls_def F' lo') ).
Proof.
     intros  t s s' h h'.
     intros CT gamma. 
     induction t; intro T; intro typing; intro t'; intro step; inversion step; inversion typing. 
     + intuition. exists F. exists lo. auto.  
     + apply IHt with  (classTy clsT) e'; auto.
     + inversion H9. auto. 
          inversion H4. auto.  intuition. exists F. exists lo. auto. 
     + apply IHt1 with (classTy T0) e'; auto.
     + apply IHt2 with arguT e'; auto.
     + inversion H14. auto.  intuition. exists F. exists lo. auto.  
     + inversion H12. auto.   intuition. exists F. exists lo. auto.  
     + unfold add_heap_obj in H7. inversion H9. rewrite H8. 
        intuition.
        case_eq (beq_oid o o0). intro.  auto.  inversion H3. rewrite H23 in H17. 
        apply beq_oid_equal with (x:=o) (x':=o0) in H20. 
        rewrite H20 in H4. rewrite H4 in H17. inversion H17.
 
        intro. inversion H3.  auto.  intuition. exists F0. exists lo. auto. 
        rewrite H23 in H17. unfold add_heap_obj. rewrite H20. auto.

     + apply IHt with T0 e'; auto. 
     + auto.  intuition. exists F. exists lo. auto.  
     + apply IHt with (LabelelTy T) e'; auto. 
     + inversion H6. auto.  intuition. exists F. exists lo. auto.   
     + apply IHt with (LabelelTy T0) e'; auto. 
     + auto.  intuition. exists F. exists lo. auto.  
     + apply IHt with (OpaqueLabeledTy T) e'; auto. 
     + inversion H6. auto.  intuition. exists F. exists lo. auto.   
     + apply IHt with T0 e'; auto. 
     + subst.  apply IHt with T0 (Return e'). auto. apply ST_return1. auto.
     + auto.  intuition. exists F. exists lo. auto.  
     + subst. inversion H3. inversion H6. auto.  intuition. exists F. exists lo. auto.   
     + apply IHt with T0 e'; auto. 
     + inversion H5. inversion H7. auto.  intuition. exists F. exists lo. auto.   
     + apply IHt1 with (classTy clsT) e1'; auto.
     + apply IHt2 with  (classTy cls') e2'; auto.
     + inversion H10. rewrite H9.  unfold add_heap_obj. inversion H5. 
        intros o0 cls_def0 F0 lx. 
        case_eq (beq_oid o o0). intro. 
        apply beq_oid_equal with (x:=o) (x':=o0) in H23. 
        intro. rewrite <- H23 in H28. rewrite <- H6 in H28. inversion H28. 
        exists F'. exists l'. auto. 

        intro. intro. exists F0. exists lx. auto.  
     + inversion H11. rewrite H10.  unfold add_heap_obj. inversion H6. 
        intros o0 cls_def0 F0 lx. 
        case_eq (beq_oid o o0). intro. 
        apply beq_oid_equal with (x:=o) (x':=o0) in H23. 
        intro. rewrite <- H23 in H28. rewrite <- H7 in H28. inversion H28. 
        exists F'. exists l'. auto. 

        intro. intro. exists F0. exists lx. auto.  

     + intuition. exists F. exists lo. auto. 
     + intuition. exists F. exists lo. auto.
     + apply IHt1 with T0 s1'; auto.
     + intuition. exists F. exists lo. auto. 
     + apply IHt with T e'; auto.
     + intuition. exists F. exists lo. inversion H8. inversion H4. rewrite <-H21. auto. 
Qed.

Theorem preservation : forall gamma CT s s' h h' sigma sigma',
    sigma = SIGMA s h ->  wfe_heap CT gamma h -> wfe_stack CT gamma h s -> sigma' = SIGMA s' h' -> 
    forall t T, has_type CT gamma h t T -> 
     forall t',  Config t sigma ==> Config t' sigma' ->
     ( has_type CT gamma h' t' T) .
Proof with auto.
   intros gamma CT s s' h h' sigma sigma'. 
  intro. intro. intro. intro. 
  induction t. (*induction on the terms *)
  (* (Tvar i) *)
  + intro T. intro typing. intro t'.  intro step.
        inversion step.   inversion typing. subst. 
        assert ( ( t' = null \/ 
                 ( exists o, t' = ObjId o 
                              /\ gamma i = Some (classTy T0)
                              /\ (exists F lo field_defs method_defs , h(o) = Some (Heap_OBJ (class_def T0 field_defs method_defs) F lo)
                                      /\ (CT T0 = Some (class_def T0 field_defs method_defs))
                                   ) 
                  )    ) ).
      inversion H6. inversion H1.   rewrite H5 in H15. inversion H15.
      inversion H9. destruct H17 with T0 i. auto. subst. destruct H22. 
      inversion H7. inversion H16. rewrite <- H19 in H.  rewrite H12 in H.
      rewrite H in H10. inversion H10. auto.  destruct H2.  intuition. destruct H2.
      right. exists x0. destruct H2. split; auto. split. auto. 

      destruct H3 as [F]. destruct H3 as [lo]. 
      destruct H3 as [field_defs]. destruct H3 as [method_defs]. destruct H3. 
      exists F. exists lo. exists  field_defs. exists method_defs. auto. split.
      rewrite <- H14. auto. auto.

      destruct H. rewrite H. apply T_null with (Gamma:=gamma) (h:=h') (T:=(classTy T0)) (CT:=CT).

      destruct H.  destruct H. destruct H2. destruct H3 as [F]. destruct H3 as [lo]. 
      destruct H3 as [field_defs]. destruct H3 as [method_defs]. destruct H3. rewrite H.  
      apply T_ObjId with (h:=h') (Gamma:=gamma) (CT:=CT) (o:=x) (cls_name:=T0)
                       (cls_def:=(class_def T0 field_defs method_defs)). auto. 
      auto. exists F. exists lo. auto.  inversion H6. rewrite <- H9. auto. 
      exists  field_defs. exists method_defs. auto. 
  (* null *)
  + intro T. intro typing. intro t'.  intro step.
        inversion step.  

  (* field access *)
  + intro T'. intro typing. intro t'. inversion typing. intro step. 
     inversion step. subst. apply T_FieldAccess with (Gamma:=gamma) (e:=e') (f:=i) 
            (cls_def:=cls_def) (CT:=CT) (clsT:=clsT) (cls':=cls') (h:=h') 
            (fields_def:=(find_fields cls_def)). apply IHt. 
             auto. auto. auto. auto. auto.

   assert (wfe_heap CT gamma h' /\ wfe_stack CT gamma h' s').
   apply reduction_preserve_wfe with (t:=(FieldAccess t i)) (t':=t') (T:=T')  (sigma:=sigma) (sigma':=sigma') (gamma:=gamma) (CT:=CT) (s:=s) (s':=s') (h:=h) (h':=h').
   auto. auto. auto. auto. auto. auto.   

   rewrite <- H13 in H5. inversion H5. 

   destruct H32 as [field_defs]. destruct H32 as [method_defs].
      assert (v = null \/
             (exists
                (o' : oid) (field_defs0 : list field) (method_defs0 : 
                                                       list method_def) 
              (field_cls_def : CLASS) (F' : FieldMap) (lo : Label),
                v = ObjId o' /\
                field_cls_def =
                class_def cls' field_defs0 method_defs0 /\
                h' o' = Some (Heap_OBJ field_cls_def F' lo) /\
                CT cls' = Some field_cls_def)
      ).

    apply field_consist_typing with (CT:=CT) (gamma:=gamma) (v:=v) (h:=h') (o:=o) (cls_def:=cls)
             (F:=fields) (f:=i) (lb:=lb) (field_cls_name:=cls') (cls_name:=cls_name) 
             (field_defs:=field_defs) (method_defs:=method_defs).
    apply H24. rewrite H2 in H23. inversion H23. auto. subst. 
    inversion H18. rewrite <- H3 in H19. rewrite <- H19 in H31.
    inversion H31. auto. rewrite <- H6 in H27. inversion H27.
    destruct H31 as [F]. destruct H as [lx]. inversion H.  auto. 
    rewrite <- H6 in H27. inversion H27. rewrite <- H34 in H10.
    rewrite H32 in H10. unfold find_fields in H10.
    rewrite H10 in H12. auto. subst. auto. 

    destruct H33. 
    subst. apply T_null with (Gamma:=gamma) (h:=h') (T:=(classTy cls')) (CT:=CT). 

    destruct H33 as [o']. destruct H33 as [field_defs0]. destruct H33 as [method_defs0]. 
    destruct H33 as [field_cls_def]. destruct H33 as [F']. destruct H33 as [lx]. 
    destruct H33. subst. destruct H34. destruct H2. 


    apply T_ObjId with (h:=h') (Gamma:=gamma) (CT:=CT) (cls_name:=cls') 
                                  (cls_def:=field_cls_def) (o:=o').

     auto. auto.  exists  F'. exists lx. auto. 

     exists field_defs0. exists method_defs0. auto. 

  (* MethodCall  *)
    + intro T'. intro typing. intro t'. inversion typing. intro step. 
        inversion step. 
      (* reduction on the object  *)
        - apply T_MethodCall with (Gamma:=gamma) (e:=e') (meth:=i) (argu:=t2)
                            ( CT:=CT) (h:=h') (T:=T) (returnT:=returnT) (cls_def:=cls_def)
                            (body:=body) (arg_id:=arg_id) (arguT:=arguT) (para_T:=para_T)
                          (cls_a:=cls_a) .

      apply IHt1; auto. 

      apply heap_preserve_typing with (h:=h).
      intros o cls_def0 F lo. intro.  

      apply reduction_preserve_heap_pointer with (t:=t1) (s:=s) (s':=s') (h:=h) (h':=h')
                             (CT:=CT) (gamma:=gamma) (T:=(classTy T))
                              (t':=e') (F:=F) (lo:=lo); auto. 
      rewrite <- H. rewrite <- H2.  auto.  auto. auto. auto. auto. auto. 
      apply heap_preserve_typing with (h:=h).
      intros o cls_def0 F lo. intro.  
      apply reduction_preserve_heap_pointer with (t:=t1) (s:=s) (s':=s') (h:=h) (h':=h')
                             (CT:=CT) (gamma:=gamma) (T:=(classTy T))
                              (t':=e') (F:=F) (lo:=lo); auto. 
      rewrite <- H. rewrite <- H2.  auto.  auto. 
      (* reduction on the argument  *)
        -  apply T_MethodCall with (Gamma:=gamma) (e:=t1) (meth:=i) (argu:=e')
                    ( CT:=CT) (h:=h') (T:=T) (returnT:=returnT) (cls_def:=cls_def)
                            (body:=body) (arg_id:=arg_id) (arguT:=arguT) (para_T:=para_T)
                          (cls_a:=cls_a).
          apply heap_preserve_typing with (h:=h).
          intros o cls_def0 F lo. intro. 

          apply reduction_preserve_heap_pointer with (t:=t2) (s:=s) (s':=s') (h:=h) (h':=h')
                                 (CT:=CT) (gamma:=gamma) (T:=arguT)
                                  (t':=e') (F:=F) (lo:=lo); auto. 
          rewrite <- H. rewrite <- H2.  auto.  auto. auto. auto. auto. auto. 

          apply heap_preserve_typing with (h:=h).
          intros o cls_def0 F lo. intro. 

          apply reduction_preserve_heap_pointer with (t:=t2) (s:=s) (s':=s') (h:=h) (h':=h')
                                 (CT:=CT) (gamma:=gamma) (T:=arguT)
                                  (t':=e') (F:=F) (lo:=lo); auto. 
          rewrite <- H. rewrite <- H2.  auto.  auto. 
      (* normal return  *)
          -  apply heap_preserve_typing with (h:=h).
          intros o0 cls_def0 F0 lo0. intro. 

          apply reduction_preserve_heap_pointer with (t:=(MethodCall t1 i t2)) (s:=s) (s':=s') (h:=h) (h':=h')
                                 (CT:=CT) (gamma:=gamma) (T:=T')
                                  (t':=t') (F:=F0) (lo:=lo0); auto. 
          rewrite <- H. rewrite <- H2.  auto. subst.  auto.

          inversion H6. inversion H22. destruct H10 as [F']. destruct H10 as [lo'].
         rewrite H16 in H10. rewrite H10 in H23. inversion H23. rewrite <- H17 in H3. 
          rewrite <- H3 in H8. inversion H8. rewrite <- H20 in H24. rewrite H12 in H24. 
          inversion H24. rewrite <- H16. apply T_return. auto. intuition. inversion H13.   
      (* opaque return  *)
      - subst. apply heap_preserve_typing with (h:=h).
          intros o0 cls_def0 F0 lo0. intro. 

          apply reduction_preserve_heap_pointer with 
                    (t:=(MethodCall (ObjId o) i (unlabelOpaque (v_opa_l v lb))))
                     (s:=s) (s':=s') (h:=h) (h':=h')
                                 (CT:=CT) (gamma:=gamma) (T:= (classTy returnT))
                                  (t':=(Return body0)) (F:=F0) (lo:=lo0); auto. 

          inversion H6. inversion H22. destruct H10 as [F']. destruct H10 as [lo'].
         rewrite H16 in H10. rewrite H10 in H23. inversion H23. rewrite <- H17 in H3. 
         rewrite <- H3 in H8. inversion H8. rewrite H20 in H12.  rewrite H12 in H28. 
         inversion H28. rewrite <- H16.  apply T_return. auto. intuition. inversion H13.   

(* new expression  *)
    + intro T. intro typing. intro t'.  intro step. 
   assert (wfe_heap CT gamma h' /\ wfe_stack CT gamma h' s').
   apply reduction_preserve_wfe with (t:=(NewExp c)) (t':=t') (T:=T)  (sigma:=sigma)
           (sigma':=sigma') (gamma:=gamma) (CT:=CT) (s:=s) (s':=s') (h:=h) (h':=h').
   auto. auto. auto. auto. auto. auto.   
      inversion step. inversion typing. 
      apply T_ObjId with (h:=h') (Gamma:=gamma) (CT:=CT) (o:=o)
                (cls_name:=c) (cls_def:=cls). 
      assert (h' o = Some (Heap_OBJ cls F lb)).
      rewrite H2 in H14.       inversion H14.  rewrite H13.       unfold add_heap_obj. 
      assert (beq_oid o o = true). apply beq_oid_same. rewrite H22. auto.
      assert (exists cls_name field_defs method_defs, 
                CT cls_name = Some cls /\ cls = (class_def cls_name field_defs method_defs)).
      apply heap_consist_ct with (h:=h') (o:=o) (ctx:=gamma) (F:=F) (lo:=lb).
      apply H3. auto. destruct H23 as [cls_name'].
      destruct H23 as [field_defs'].       destruct H23 as [method_defs']. destruct H23. 
      rewrite H10 in H24. inversion H24.  auto. exists F. exists lb.  

      rewrite H2 in H14.       inversion H14.  rewrite H13.       unfold add_heap_obj. 
      assert (beq_oid o o = true). apply beq_oid_same. rewrite H22. auto.
      exists field_defs. exists method_defs. auto.

(* Label  *)
    + intro T. intro typing. intro t'.  intro step. 
       inversion step. 
 
(* label data *)
    + intro T. intro typing. intro t'.  intro step.
        inversion step.   inversion typing.
        apply T_labelData with (h:=h') (Gamma:=gamma) (lb:=l0) (CT:=CT) (e:=e') (T:=T0).
        apply T_label. apply IHt; auto. inversion typing.
        apply T_v_l with (h:=h') (Gamma:=gamma) (lb:=l0) (CT:=CT) (v:=t) (T:=T0).
        apply T_label. 
        apply heap_preserve_typing with (h:=h).
          intros o0 cls_def0 F0 lo0. intro. 
        apply reduction_preserve_heap_pointer with 
                    (t:=(labelData t l0))
                     (s:=s) (s':=s') (h:=h) (h':=h')
                                 (CT:=CT) (gamma:=gamma) (T:= T)
                                  (t':=t') (F:=F0) (lo:=lo0); auto.
        rewrite <- H.         rewrite <- H2. auto. auto.

(* unlabel *)
    + intro T. intro typing. intro t'.  intro step.
        inversion step.   inversion typing.
        apply T_unlabel. apply IHt. auto. auto.
        inversion typing. rewrite <- H3 in H15. inversion H15. 
        apply heap_preserve_typing with (h:=h).
          intros o0 cls_def0 F0 lo0. intro. 
        apply reduction_preserve_heap_pointer with 
                    (t:=(unlabel t) )
                     (s:=s) (s':=s') (h:=h) (h':=h')
                                 (CT:=CT) (gamma:=gamma) (T:= T)
                                  (t':=t') (F:=F0) (lo:=lo0); auto.
        rewrite <- H.         rewrite <- H2. auto. rewrite <- H5. auto. 

(* Label of  *)
   + intro T. intro typing. intro t'.  intro step.
        inversion step.   inversion typing.
        apply T_labelOf with (T:=T0).  apply IHt. auto. auto. 
        inversion typing. apply T_label.

(* unlabelopaque  *)
   + intro T. intro typing. intro t'.  intro step.
        inversion step.   inversion typing.
        apply T_unlabelOpaque. apply IHt. auto. auto.
        inversion typing. rewrite <- H3 in H15. inversion H15. rewrite <- H5.  
        apply heap_preserve_typing with (h:=h).
          intros o0 cls_def0 F0 lo0. intro. 
        apply reduction_preserve_heap_pointer with 
                    (t:=(unlabelOpaque t) )
                     (s:=s) (s':=s') (h:=h) (h':=h')
                                 (CT:=CT) (gamma:=gamma) (T:= T)
                                  (t':=t') (F:=F0) (lo:=lo0); auto.
        rewrite <- H.         rewrite <- H2. auto. auto. 

(* opaque call  *)
   + intro T. intro typing. intro t'.  intro step.
        inversion step.   inversion typing.
        apply T_opaqueCall. apply IHt. auto. auto.
        inversion typing. 
              apply T_opaqueCall. apply IHt. auto. rewrite <- H3.
        apply ST_return1. auto.
        inversion typing.  apply T_v_opa_l. apply T_label.
        apply heap_preserve_typing with (h:=h).
          intros o0 cls_def0 F0 lo0. intro. 
        apply reduction_preserve_heap_pointer with 
                    (t:=(opaqueCall t) )
                     (s:=s) (s':=s') (h:=h) (h':=h')
                                 (CT:=CT) (gamma:=gamma) (T:= T)
                                  (t':=t') (F:=F0) (lo:=lo0); auto.
        rewrite <- H.         rewrite <- H2. auto. auto. 

        inversion typing.  apply T_v_opa_l. apply T_label.
        apply heap_preserve_typing with (h:=h).
          intros o0 cls_def0 F0 lo0. intro. 
        apply reduction_preserve_heap_pointer with 
                    (t:=(opaqueCall t) )
                     (s:=s) (s':=s') (h:=h) (h':=h')
                                 (CT:=CT) (gamma:=gamma) (T:= T)
                                  (t':=t') (F:=F0) (lo:=lo0); auto.
        rewrite <- H.         rewrite <- H2. auto. 
        rewrite <- H3 in H16. inversion H16. auto. 

(* skip  *)
   + intro T. intro typing. intro t'.  intro step.
        inversion step.  

(* assignment  *)
   + intro T. intro typing. intro t'.  intro step.
        inversion step.    inversion typing.
        apply T_assignment with (T:=T0). auto. 
        apply IHt. auto. auto. 
        inversion typing. apply T_skip.

(* field write  *)
   + intro T. intro typing. intro t'.  intro step.
        inversion step.    inversion typing.
        apply T_FieldWrite with (cls_def:=cls_def) (clsT:=clsT) (cls':=cls'). 
        apply IHt1. auto. auto.  
        apply heap_preserve_typing with (h:=h).
          intros o0 cls_def0 F0 lo0. intro. 
        apply reduction_preserve_heap_pointer with 
                    (t:=(FieldWrite t1 i t2) )
                     (s:=s) (s':=s') (h:=h) (h':=h')
                                 (CT:=CT) (gamma:=gamma) (T:= T)
                                  (t':=t') (F:=F0) (lo:=lo0); auto.
        rewrite <- H.         rewrite <- H2. auto. auto.  auto. auto. 
        
        inversion typing. 
        apply T_FieldWrite with (cls_def:=cls_def) (clsT:=clsT) (cls':=cls'). 
        
        apply heap_preserve_typing with (h:=h).
          intros o0 cls_def0 F0 lo0. intro. 
        apply reduction_preserve_heap_pointer with 
                    (t:=(FieldWrite t1 i t2) )
                     (s:=s) (s':=s') (h:=h) (h':=h')
                                 (CT:=CT) (gamma:=gamma) (T:= T)
                                  (t':=t') (F:=F0) (lo:=lo0); auto.
        rewrite <- H.  rewrite <- H2. auto. auto.  auto. auto. auto.  

        inversion typing. apply T_skip.         inversion typing. apply T_skip.

(* if statement  *)
   + intro T. intro typing. intro t'.  intro step.
        inversion step. 
        inversion typing. subst.  inversion H10. rewrite <- H3. auto.
         inversion typing. subst. inversion H10. rewrite <- H3. auto.

(* sequence *)
   + intro T. intro typing. intro t'.  intro step.
        inversion step. 
        inversion typing. 
        apply T_sequence with (T:=T0) (T':=T). 
        apply IHt1. auto. auto.
        apply heap_preserve_typing with (h:=h).
          intros o0 cls_def0 F0 lo0. intro. 
        apply reduction_preserve_heap_pointer with 
                    (t:=(Sequence t1 t2)  )
                     (s:=s) (s':=s') (h:=h) (h':=h')
                                 (CT:=CT) (gamma:=gamma) (T:= T)
                                  (t':=t') (F:=F0) (lo:=lo0); auto.
        rewrite <- H.  rewrite <- H2. auto. auto.

        inversion typing. rewrite <- H7.  
        apply heap_preserve_typing with (h:=h).
          intros o0 cls_def0 F0 lo0. intro. 
        apply reduction_preserve_heap_pointer with 
                    (t:=(Sequence t1 t2)  )
                     (s:=s) (s':=s') (h:=h) (h':=h')
                                 (CT:=CT) (gamma:=gamma) (T:= T)
                                  (t':=t') (F:=F0) (lo:=lo0); auto.
        rewrite <- H.  rewrite <- H2. auto. auto.

(* return   *)
   + intro T. intro typing. intro t'.  intro step.
        inversion step. 
        inversion typing. 
        apply T_return. apply IHt.  auto. auto.  auto. 
        
        inversion typing. rewrite <- H5. 
        apply heap_preserve_typing with (h:=h).
          intros o0 cls_def0 F0 lo0. intro. 
        apply reduction_preserve_heap_pointer with 
                    (t:=(Return t) )
                     (s:=s) (s':=s') (h:=h) (h':=h')
                                 (CT:=CT) (gamma:=gamma) (T:= T)
                                  (t':=t') (F:=F0) (lo:=lo0); auto.
        rewrite <- H.  rewrite <- H2. auto. auto.

(* objId *)
     + intro T. intro typing. intro t'.  intro step.
        inversion step. 

(* runtime labeled data *)
     + intro T. intro typing. intro t'.  intro step.
        inversion step. 
(* runtime opaque labeled data *)
     + intro T. intro typing. intro t'.  intro step.
        inversion step. 
Qed. 

Inductive multi_step_reduction : config -> config -> Prop := 
  | multi_reduction_refl : forall config , multi_step_reduction config config
  | multi_reduction_step : forall c1 c2 c3, 
                    reduction c1 c2 ->
                    multi_step_reduction c2 c3 ->
                    multi_step_reduction c1 c3.

Inductive multi_step : tm -> Sigma -> tm -> Sigma -> Prop := 
  | multi_refl : forall t sigma , multi_step t sigma t sigma
  | multi_reduction : forall t1 t2 t3 sigma1 sigma2 sigma3, 
                    reduction (Config t1 sigma1) (Config t2 sigma2) ->
                    multi_step t2 sigma2 t3 sigma3 ->
                    multi_step t1 sigma1 t3 sigma3.

Notation "c1 '==>*' c2" := (multi_step_reduction c1 c2) (at level 40).


Theorem soundness : forall gamma CT,
    forall sigma s h, sigma = SIGMA s h ->  wfe_heap CT gamma h -> wfe_stack CT gamma h s -> 
    forall t s' h' t',  multi_step t sigma t' (SIGMA s' h')  ->
    forall T, has_type CT gamma h t T -> 
     value t' \/ (exists config', Config t' (SIGMA s' h') ==> config').
Proof with auto. 
  intros  gamma CT sigma s h.  intro. intro. intro. intros t s' h' t'.
  intro multiH. 

generalize dependent s.  generalize dependent h. 
  induction multiH.
  + intro h. intro well_heap. intro s. intro sigmaH. intro well_stack. intro T. 
     intro typing. apply progress with  (T:=T) (gamma:=gamma) (CT:=CT)  (s:=s) (h:=h); auto.
  + intro h1. intro well_heap. intro s1. intro. intro well_stack. intro T. intro typing. 
      induction sigma2.  
      assert (wfe_heap CT gamma h /\ wfe_stack CT gamma h s).
      apply reduction_preserve_wfe with (t:=t1) (t':=t2) 
              (sigma:=sigma1) (sigma':=(SIGMA s h)) (gamma:=gamma) (CT:=CT)
              (s:=s1) (s':=s) (h:=h1) (h':=h) (T:=T).
      auto. auto.       auto. auto.       auto. auto. 
      destruct IHmultiH with (h0:=h) (s0:=s) (T:=T).
      apply H1. auto. apply H1.
      apply preservation with (gamma:=gamma) (CT:=CT) (s:=s1) (s':=s) 
                    (h:=h1) (h':=h) (sigma:=sigma1) (sigma':= (SIGMA s h)) (t:=t1).
      auto.       auto.       auto.       auto.       auto.       auto. 
      left. auto. right. auto.
Qed.

Theorem deterministic: forall t sigma t1 sigma1 t2 sigma2, 
     reduction (Config t sigma) (Config t1 sigma1) ->
     reduction (Config t sigma) (Config t2 sigma2) -> 
      t1 = t2 /\ sigma1 = sigma2. 
Proof.
     intros t sigma t1 sigma1 t2 sigma2 Hy1 Hy2.

     remember (Config t1 sigma1) as _t1_config. 
     generalize dependent t2.
     induction Hy1; intros t2 Hy2. 
      (*Tvar *)
     + inversion Hy2. subst. inversion H6. rewrite <- H1 in H10. rewrite <- H2 in H10.
        inversion H10. inversion  Heq_t1_config.
          split. auto. auto. 
     (*field access*)
    + inversion Hy2. inversion Heq_t1_config. subst. 
      
Admitted. 