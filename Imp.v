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
      value v ->
      value (v_l v lb)
  | v_opa_labeled : forall v lb,
      value v->
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


Definition Class_table := cn -> option CLASS.
Inductive config := 
  | Config : Class_table -> tm -> Sigma -> config
  | Error_state : config.
Hint Constructors config.

Reserved Notation "c '==>' c'"
  (at level 40, c' at level 39).





Inductive reduction : config -> config -> Prop :=
(* variabel access *)
  | ST_var : forall id sigma s h lb sf lsf v s' ct,
      sigma = SIGMA s h ->
      s = cons lsf s' ->
      lsf = Labeled_frame lb sf ->
      Some v = sf(id) ->
      Config ct (Tvar id) sigma ==> Config ct v sigma

(* field read *)
  (* context rule *)
  | ST_fieldRead1 : forall sigma sigma' e e' f ct,
      Config ct e sigma ==>  Config ct e' sigma' -> 
      Config ct (FieldAccess e f) sigma ==> Config ct (FieldAccess e' f) sigma'
  (* normal field access *)
  | ST_fieldRead2 : forall sigma sigma' o s h fname lb cls fields v l' s' ct,
      sigma = SIGMA s h ->
      Some (Heap_OBJ cls fields lb) = lookup_heap_obj h o -> 
      Some v = fields(fname) -> 
      l' = join_label lb (current_label sigma) ->
      s' = update_current_label s l'-> 
      sigma' = SIGMA s' h ->
      Config ct (FieldAccess (ObjId o) fname) sigma ==> Config ct v sigma'
  (* null pointer exception for field access *)
  | ST_fieldReadException : forall sigma f ct,
      Config ct (FieldAccess null f) sigma ==> Error_state
  | ST_fieldRead3 : forall sigma e f ct,
      Config ct e sigma ==>  Error_state -> 
      Config ct (FieldAccess e f) sigma ==> Error_state



(* method call *)
  (* context rule: evaluate object target *)
  | ST_MethodCall1 : forall sigma sigma' e e' e2 id ct,
       Config ct e sigma ==>  Config ct e' sigma' -> 
      Config ct (MethodCall e id e2) sigma ==> Config ct (MethodCall e' id e2)  sigma'
  (* context rule: evaluate arguments *)
  | ST_MethodCall2 : forall sigma sigma' v e e' id ct,
      (forall t, value t -> t<> null -> e <> unlabelOpaque t) ->
      Config ct e sigma ==>  Config ct e' sigma' -> 
      value v ->
      Config ct (MethodCall v id e) sigma ==> Config ct (MethodCall v id e') sigma'
  (* normal method call *)
  | ST_MethodCall3 : forall sigma sigma' o s h cls fields v lx l theta s' sf lsf arg_id cls_a body meth returnT ct,
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
      Config ct (MethodCall (ObjId o) meth v) sigma ==>  Config ct (Return body) sigma'
  (* null pointer exception for method call *)
  | ST_MethodCallException : forall sigma v meth ct, 
      Config ct (MethodCall null meth v) sigma ==> Error_state
  (* context rule error 1*)
  | ST_MethodCall4 : forall sigma e e2 id ct,
       Config ct e sigma ==>  Error_state -> 
      Config ct (MethodCall e id e2) sigma ==> Error_state
  (* context rule error 2*)
  | ST_MethodCall5 : forall sigma v e id ct,
      (forall t, value t -> t<> null -> e <> unlabelOpaque t) ->
      Config ct e sigma ==>  Error_state -> 
      value v ->
      Config ct (MethodCall v id e) sigma ==> Error_state


(* method call with unlabel opaque *)
  | ST_MethodCall_unlableOpaque : forall sigma sigma' o s h cls fields v lx l' lb s' sf lsf arg_id cls_a body meth returnT ct,
      sigma = SIGMA s h ->
      Some (Heap_OBJ cls fields lx) =lookup_heap_obj h o -> 
      sf = sf_update empty_stack_frame arg_id v ->
      l' = join_label lb (current_label sigma) ->
      lsf = Labeled_frame l' sf ->
      s' = cons lsf s ->
      value v ->
      Some (m_def returnT meth cls_a arg_id  (Return body)) = find_method cls meth ->
      sigma' = SIGMA s' (get_heap sigma) ->
      Config ct (MethodCall (ObjId o) meth (unlabelOpaque (v_opa_l v lb)))  sigma ==>Config ct (Return body) sigma'

  (* null pointer exception for method call with unlabel opaque of null data*)
  | ST_MethodCallOpaqueDataException : forall sigma o meth ct, 
      Config ct (MethodCall (ObjId o) meth (unlabelOpaque null)) sigma ==> Error_state

(* new expression *)
  | ST_NewExp : forall sigma sigma' h h' s o lb cls_name field_defs method_defs cls F ct,
      ct cls_name = Some cls ->
      sigma = SIGMA s h->
      lb = (current_label sigma) -> 
      o = get_fresh_oid h ->
      cls = (class_def cls_name field_defs method_defs) ->
      F =  (init_field_map (find_fields cls) empty_field_map) ->
      h' = add_heap_obj h o (Heap_OBJ cls F lb) ->
      sigma' = SIGMA s h' ->
      Config ct (NewExp cls_name) sigma ==> Config ct (ObjId o) sigma'


(* label data express *)
  (* context rule *)
  | ST_LabelData1 : forall sigma sigma' e e' lb ct,
      Config ct e sigma ==>  Config ct e' sigma' -> 
      Config ct (labelData e lb) sigma ==> Config ct (labelData e' lb) sigma'
  (* label data *)
  | ST_LabelData2 : forall sigma v lb ct,
      value v ->
      Config ct (labelData v lb) sigma ==>  Config ct (v_l v lb)  sigma
  (* label data exception *)
  | ST_LabelDataException : forall sigma lb ct,
      Config ct (labelData null lb) sigma ==> Error_state
  (* context rule error*)
  | ST_LabelDataError : forall sigma e lb ct,
      Config ct e sigma ==>  Error_state -> 
      Config ct (labelData e lb) sigma ==> Error_state




(* unlabel *)
  (* context rule *)
  | ST_unlabel1 : forall sigma sigma' e e' ct,
      Config ct e sigma ==>  Config ct e' sigma' -> 
      Config ct  (unlabel e) sigma ==> Config ct (unlabel e') sigma'
  (* unlabel *)
  | ST_unlabel2 : forall sigma v lb l' sigma' s h s' ct,
      sigma = SIGMA s h ->
      l' = join_label lb (current_label sigma) ->
      s' = update_current_label s l'-> 
      sigma' = SIGMA s' (get_heap sigma) ->
      value v ->
      Config ct (unlabel (v_l v lb)) sigma ==> Config ct v sigma'
  (* unlabel data exception *)
  | ST_unlabelDataException : forall sigma ct,
      Config ct (unlabel null) sigma ==> Error_state
  (* context rule error*)
  | ST_unlabelContextError : forall sigma  e ct,
      Config ct e sigma ==>  Error_state -> 
      Config ct  (unlabel e) sigma ==> Error_state


(* Label of *)
  (* context rule *)
  | ST_labelof1 : forall sigma sigma' e e' ct,
       Config ct e sigma ==>  Config ct e' sigma' -> 
       Config ct (labelOf e) sigma ==> Config ct (labelOf e') sigma'
  (* label of  *)
  | ST_labelof2 : forall sigma v lb ct,
      Config ct (labelOf (v_l v lb)) sigma ==> Config ct (l lb) sigma
  | ST_labelOfDataException : forall sigma ct, 
      Config ct (labelOf null) sigma ==> Error_state
  (* context rule error*)
  | ST_labelofCtxError : forall sigma e ct,
       Config ct e sigma ==>  Error_state -> 
       Config ct (labelOf e) sigma ==> Error_state

(* unlabel opaque*)
  (* context rule *)
  | ST_unlabel_opaque1 : forall sigma sigma' e e' ct,
      Config ct e sigma ==>  Config ct e' sigma' -> 
     Config ct (unlabelOpaque e) sigma ==>  Config ct (unlabelOpaque e') sigma'
  (* context rule error*)
  | ST_unlabel_opaque_ctx_error : forall sigma e ct,
      Config ct e sigma ==>  Error_state -> 
     Config ct (unlabelOpaque e) sigma ==>  Error_state
  (* unlabel opaque *)
  | ST_unlabel_opaque2 : forall sigma v lb l' sigma' s h s'  ct,
      sigma = SIGMA s h ->
      l' = join_label lb (current_label sigma) ->
      s' = update_current_label s l'-> 
      sigma' = SIGMA s' (get_heap sigma) ->
      Config ct (unlabelOpaque (v_opa_l v lb)) sigma ==> Config ct v sigma'
  | ST_unlabel_opaqueDataException : forall sigma ct, 
      Config ct (unlabelOpaque null) sigma ==> Error_state

(* Opaque call *)
  (* context rule *)
  | ST_opaquecall1 : forall sigma sigma' e e' ct,
       (forall v, value v -> e <> Return v) ->
       Config ct e sigma ==>  Config ct e' sigma' -> 
      Config ct (opaqueCall e) sigma ==> Config ct (opaqueCall e') sigma'
  (* context rule error*)
  | ST_opaquecall_ctx_error : forall sigma e ct,
      Config ct e sigma ==>  Error_state -> 
     Config ct (opaqueCall e) sigma  ==>  Error_state
  (* return context rule*)
  | ST_opaquecall_return1 : forall sigma sigma' e e' ct,
       Config ct e sigma ==> Config ct e' sigma' -> 
      Config ct (opaqueCall (Return e)) sigma ==> Config ct (opaqueCall (Return e')) sigma'
  (* return context rule error*)
  | ST_opaquecall_return_error : forall sigma e ct,
       Config ct e sigma ==> Error_state -> 
      Config ct (opaqueCall (Return e)) sigma ==> Error_state


  (* opaque call with value, without method call inside *)
  | ST_opaquecall_val2 : forall sigma v lb ct,
      (value v) ->
      lb = (current_label sigma) ->
      Config ct (opaqueCall v) sigma ==>  Config ct (v_opa_l v lb) sigma  
  (* opaque call with return statement *)
  | ST_opaquecall_return2 : forall sigma sigma' s h lb s' lsf v ct,
      sigma = SIGMA s h->
      s = cons lsf s' ->
      s' <> nil ->
      lb = (current_label sigma) ->
      sigma' = SIGMA s' h->
      value v ->
      Config ct (opaqueCall (Return v)) sigma ==> Config ct  (v_opa_l v lb) sigma'
  | ST_opaquecall_return3 : forall sigma ct,
      Config ct (opaqueCall (Return null)) sigma ==> Error_state
  | ST_opaquecall_return4 : forall sigma v s h lsf ct, 
      value v ->
      sigma = SIGMA s h ->
      s = cons lsf nil ->
      Config ct (opaqueCall (Return v)) sigma ==> Error_state


(* assignment *)
  (* context rule *)
  | ST_assignment1 : forall sigma sigma' e e' id ct,
       Config ct e sigma ==> Config ct e' sigma' -> 
       Config ct (Assignment id e) sigma ==> Config ct (Assignment id e') sigma'
  (* context rule error*)
  | ST_assignment_ctx_error : forall sigma e id ct,
      Config ct e sigma ==>  Error_state -> 
     Config ct  (Assignment id e) sigma  ==>  Error_state
  (* assignment *)
  | ST_assignment2 : forall sigma sigma' id v s' s h ct,
       value v ->
       sigma = SIGMA s h ->
       s' = update_stack_top s id v->
       sigma' = SIGMA s' h ->
       Config ct (Assignment id v) sigma ==> Config ct Skip sigma'

(* Field Write *)
  (* context rule 1 *)
  | ST_fieldWrite1 : forall sigma sigma' f e1 e1' e2 ct,
       Config ct e1 sigma ==> Config ct e1' sigma' -> 
       Config ct (FieldWrite e1 f e2) sigma ==> Config ct (FieldWrite e1' f e2) sigma'
  (* context rule error 1 *)
  | ST_fieldWrite_ctx_error1 : forall sigma f e1 e2 ct,
       Config ct e1 sigma ==> Error_state -> 
       Config ct (FieldWrite e1 f e2) sigma ==> Error_state
  (* context rule 2 *)
  | ST_fieldWrite2 : forall sigma sigma' f v e2 e2' ct,
       (forall t, value t -> t<> null -> e2 <> unlabelOpaque t) ->
       value v ->
       Config ct e2 sigma ==> Config ct e2' sigma' -> 
       Config ct (FieldWrite v f e2) sigma ==> Config ct (FieldWrite v f e2') sigma'
  (* context rule error 2 *)
  | ST_fieldWrite_ctx_error2 : forall sigma f v e2 ct,
       (forall t, value t -> t<> null -> e2 <> unlabelOpaque t) ->
       value v ->
       Config ct e2 sigma ==> Error_state -> 
       Config ct (FieldWrite v f e2) sigma ==> Error_state
  (* field write normal *)
  | ST_fieldWrite3 : forall sigma sigma' o s h h' f lb cls F F' v l' ct,
      sigma = SIGMA s h ->
      Some (Heap_OBJ cls F lb) = lookup_heap_obj h o -> 
      F' = fields_update F f v ->
      l' = join_label lb (current_label sigma) ->
      h' = update_heap_obj h o (Heap_OBJ cls F' l') ->
      sigma' = SIGMA s h' ->
      value v->
      Config ct (FieldWrite (ObjId o) f v) sigma ==> Config ct Skip sigma'
  (* null pointer exception for field write *)
  | ST_fieldWriteException : forall sigma f v ct, 
      Config ct (FieldWrite null f v) sigma ==> Error_state
  (* field write normal *)
  | ST_fieldWrite_opaque : forall sigma sigma' o s h h' f lo cls F F' v l' lb e2 ct,
      e2 = unlabelOpaque (v_opa_l v lb) ->
      sigma = SIGMA s h ->
      Some (Heap_OBJ cls F lo) = lookup_heap_obj h o-> 
      F' = fields_update F f v ->
      l' = join_label lo lb ->
      h' = update_heap_obj h o (Heap_OBJ cls F' l') ->
      sigma' = SIGMA s h' ->
      value v ->
      Config ct (FieldWrite (ObjId o) f e2) sigma ==> Config ct Skip sigma'
  | ST_FieldWriteOpaqueDataException : forall sigma o f ct, 
      Config ct (FieldWrite (ObjId o) f (unlabelOpaque null)) sigma ==> Error_state

(* return statement *)
  (* context rule*)
  | ST_return1 : forall sigma sigma' e e' ct,
        Config ct e sigma ==> Config ct e' sigma' -> 
        Config ct (Return e) sigma ==> Config ct (Return e') sigma'
  (* context rule error*)
  | ST_return_ctx_error : forall sigma e ct,
        Config ct e sigma ==> Error_state -> 
        Config ct (Return e) sigma ==> Error_state
  (* return val *)
  | ST_return2 : forall sigma sigma' v s s' s'' h lsf l' ct, 
      value v ->
      sigma = SIGMA s h ->
      s = cons lsf s' ->
      s' <> nil ->
      l' = join_label (get_current_label s) (get_current_label s') ->
      s'' = update_current_label s' l' ->
      sigma' = SIGMA s'' h ->
      Config ct (Return v) sigma ==> Config ct v sigma'
  | ST_return_terminal : forall sigma v s h lsf ct, 
      value v ->
      sigma = SIGMA s h ->
      s = cons lsf nil ->
      Config ct (Return v) sigma ==> Error_state

(* if statement *)
  | ST_if_b1 : forall sigma s1 s2 s h lsf s' lb sf id1 id2 ct, 
       sigma = SIGMA s h ->
       s = cons lsf s' ->
       lsf = Labeled_frame lb sf ->
       sf(id1) = sf(id2) ->
       Config ct (If id1 id2 s1 s2) sigma ==> Config ct s1 sigma
  | ST_if_b2 : forall sigma s1 s2 s h lsf s' lb sf id1 id2 ct, 
       sigma = SIGMA s h ->
       s = cons lsf s' ->
       lsf = Labeled_frame lb sf ->
       sf(id1) <> sf(id2) ->
       Config ct (If id1 id2 s1 s2) sigma ==> Config ct s2 sigma
(* sequence *)
   (* context rule *)
  | ST_seq1 : forall sigma s1 s2 s1' sigma' ct, 
    Config ct s1 sigma ==> Config ct s1' sigma' -> 
    Config ct (Sequence s1 s2) sigma ==> Config ct (Sequence s1' s2) sigma'
  (* context rule error *)   
  | ST_seq_ctx_error : forall sigma s1 s2 ct, 
    Config ct s1 sigma ==> Error_state -> 
    Config ct (Sequence s1 s2) sigma ==> Error_state
   (* sequence rule *)
  | ST_seq2 : forall sigma v s ct, 
    value v->
    Config ct (Sequence v s) sigma ==> Config ct s sigma

where "c '==>' c'" := (reduction c c').


Inductive ty : Type :=
  | classTy : cn -> ty 
  | LabelTy : ty
  | LabelelTy : ty -> ty
  | OpaqueLabeledTy : ty -> ty
  | voidTy : ty. 

Definition typing_context := id -> (option ty).


Definition update_typing_frame (ctx : typing_context_frame) (x:id) (T : ty) : typing_context_frame :=
      fun x' => if beq_id x x' then (Some T) else ctx x. 

Inductive has_type : Class_table -> typing_context -> heap -> tm -> ty -> Prop :=
(*variable *)
  | T_Var : forall Gamma ctx Gamma' x T CT h , 
      Gamma = cons ctx Gamma' ->
      ctx x = Some (classTy T) ->
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
  | T_MethodCall : forall Gamma Gamma' ctx e meth argu CT h T returnT cls_def body arg_id arguT para_T cls_a,
      has_type CT Gamma h e (classTy T) ->
      has_type CT Gamma h argu arguT ->
      Some cls_def = CT(T) ->
      find_method cls_def meth = Some (m_def returnT meth cls_a arg_id (Return body))  ->
      arguT = para_T ->
      ctx = update_typing_frame empty_context_frame arg_id arguT ->
      Gamma' = cons ctx Gamma ->
      has_type CT Gamma' h (body) (classTy returnT) ->
      has_type CT Gamma h (Return body) (classTy returnT) ->
      has_type CT Gamma h (MethodCall e meth argu) (classTy returnT)
(* new exp *)
  | T_NewExp : forall h Gamma cls_name CT, 
      (exists cls_def field_defs method_defs, CT cls_name = Some cls_def /\
              cls_def = class_def cls_name field_defs method_defs) ->
      has_type CT Gamma h (NewExp cls_name) (classTy cls_name)
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
(* opaque call 1 *)
  | T_opaqueCall : forall h Gamma CT e T,
      has_type CT Gamma h e T ->
      has_type CT Gamma h (opaqueCall e) (OpaqueLabeledTy T)
(* Skip *)
  | T_skip : forall h Gamma CT,
      has_type CT Gamma h Skip voidTy
(* assignment *)
  | T_assignment : forall h Gamma ctx Gamma' CT e T x, 
      Gamma = cons ctx Gamma' ->
      ctx x = Some T ->
      has_type CT Gamma h e T ->
      has_type CT Gamma h (Assignment x e) voidTy
(* Field Write *)
  | T_FieldWrite : forall h Gamma x f cls_def CT clsT cls' e,
      has_type CT Gamma h x (classTy clsT) ->
      has_type CT Gamma h e (classTy cls') ->
      Some cls_def = CT(clsT) ->
      type_of_field (find_fields cls_def) f = Some cls' ->
      has_type CT Gamma h (FieldWrite x f e) voidTy
(* if *)
  | T_if : forall Gamma h CT id1 id2 s1 s2 T T' ,
      has_type CT Gamma h (Tvar id1) (classTy T) ->
      has_type CT Gamma h (Tvar id2) (classTy T) ->
      has_type CT Gamma h s1 T' ->
      has_type CT Gamma h s2 T' ->
      has_type CT Gamma h (If id1 id2 s1 s2) T'
(* sequence *)
  | T_sequence : forall h Gamma CT e1 e2 T T',
      has_type CT Gamma h e1 T ->
      has_type CT Gamma h e2 T' ->
      has_type CT Gamma h (Sequence e1 e2) T'
(* return *)
  | T_return : forall h Gamma CT e T,
      has_type CT Gamma h e T ->
      T <> voidTy ->
      has_type CT Gamma h (Return e) T
(* ObjId *)
  | T_ObjId : forall h Gamma CT o cls_name cls_def,
      Some cls_def = CT(cls_name) ->
      (exists field_defs method_defs, cls_def = (class_def cls_name field_defs method_defs)) ->
      (exists F lo, lookup_heap_obj h o = Some (Heap_OBJ cls_def F lo)) ->
      has_type CT Gamma h (ObjId o) (classTy cls_name)
(* runtime labeled data *)
  | T_v_l : forall h Gamma lb CT v T,
      has_type CT Gamma h (l lb)  LabelTy ->
      has_type CT Gamma h v  T ->
      value v ->
      has_type CT Gamma h (v_l v lb) (LabelelTy T)
(* runtime labeled data *)
  | T_v_opa_l : forall h Gamma lb CT v T,
      has_type CT Gamma h (l lb)  LabelTy ->
      has_type CT Gamma h v  T ->
      value v ->
      has_type CT Gamma h (v_opa_l v lb) (OpaqueLabeledTy T).

Definition empty_heap : heap := nil.

Definition compare_oid (o1 : oid) (o2 : oid) :=
  match o1, o2 with 
      | OID n1, OID n2 => if (gt_dec n1  n2) then true else false
  end.

Inductive wfe_heap : Class_table -> heap -> Prop :=
  | empty_heap_wfe : forall ct, 
        wfe_heap ct  empty_heap
  | heap_wfe : forall h h' o cls_def F ct cn ho lo method_defs field_defs ,
        h' = (o , ho) :: h ->
        (h = nil \/ (exists o' ho' h'', h = (o' , ho') :: h'' /\ compare_oid o o' = true) ) ->
        wfe_heap ct h ->
        ho = (Heap_OBJ cls_def F lo) ->
        Some cls_def  = ct cn ->
        cls_def = class_def cn field_defs method_defs ->
        wfe_heap ct h'.

Inductive field_wfe_heap : Class_table -> heap -> Prop :=
  | heap_wfe_fields : forall h ct, 
        (forall o cls_def F cls_name lo method_defs field_defs,
        lookup_heap_obj  h o = Some (Heap_OBJ cls_def F lo) ->
        Some cls_def  = ct cls_name ->
        cls_def = class_def cls_name field_defs method_defs ->
        (forall f cls', type_of_field field_defs f = Some cls' -> 
                exists v, F(f) = Some v
                 /\ (v= null  \/ 
                          ( exists o' F' lx field_defs0 method_defs0, v = ObjId o' 
                                  /\ lookup_heap_obj  h o' = Some (Heap_OBJ (class_def cls' field_defs0 method_defs0) F' lx)
                                    /\ ct cls' = Some (class_def cls' field_defs0 method_defs0)
                          ) ) 
        ))->
        field_wfe_heap ct h.



Inductive wfe_stack_frame : Class_table -> typing_context_frame -> heap -> labeled_stack_frame -> Prop :=
  | stack_frame_wfe : forall h lsf sf lb ct ctx,
        lsf = Labeled_frame lb sf ->
         (forall x cls_name, ctx x = Some (classTy cls_name)  ->
        exists v, sf x = Some v  
          /\    (
               v = null \/ 
                 ( exists o, v = ObjId o 
                              /\ (exists F lo field_defs method_defs , lookup_heap_obj h o = Some (Heap_OBJ (class_def cls_name field_defs method_defs) F lo)
                                      /\ (ct cls_name = Some (class_def cls_name field_defs method_defs))
                                   ) 
                  )    )  ) ->
        wfe_stack_frame ct ctx h lsf. 


Inductive wfe_stack : Class_table -> typing_context -> heap -> stack -> Prop :=
  | main_stack_wfe : forall ct gamma s h lb,
        wfe_heap ct h -> 
        s = cons (Labeled_frame lb empty_stack_frame) nil ->
        gamma = nil ->
        forall lb, wfe_stack ct gamma h (cons (Labeled_frame lb empty_stack_frame) nil)
  | stack_wfe : forall s ct gamma s' lb sf h ctx gamma', 
        s = cons (Labeled_frame lb sf) s'->
        gamma = cons ctx gamma' ->
        wfe_stack ct gamma' h s' ->
        wfe_heap ct h ->
      (*  (forall x, (exists v, sf x = Some v) -> (exists T, gamma x = Some T)) -> *)
        wfe_stack_frame ct ctx h (Labeled_frame lb sf) ->
        wfe_stack ct gamma h s.



