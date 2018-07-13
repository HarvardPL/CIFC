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
  | v_opa_l : tm -> Label -> tm
  | dot : tm.

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
      value (v_opa_l v lb)
  | v_dot : 
      value dot.  

(* stack frame *)
Definition stack_frame : Type := id -> (option tm).

Inductive labeled_stack_frame : Type := 
  | Labeled_frame : Label -> stack_frame -> labeled_stack_frame.

Definition get_stack_label (lsf : labeled_stack_frame) : Label :=
  match lsf with 
    | Labeled_frame lb sf => lb
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
(* unrestricted access L *)
Definition H_Label := LB (cons (Principal "Jian") nil).

Definition empty_stack_frame : stack_frame := fun _ => None.
Definition empty_labeled_stack_frame : labeled_stack_frame := (Labeled_frame L_Label empty_stack_frame).
Definition main_labeled_stack_frame : labeled_stack_frame := (Labeled_frame L_Label empty_stack_frame).

(* stack *)
Definition stack :Type := list labeled_stack_frame.

Fixpoint update_stack_top (s : stack) (x : id) (v : tm) := 
match s with 
  | cons lsf s' => cons (labeled_frame_update lsf x v) s'
  | nil => nil
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
  | ST_MethodCall3 : forall sigma sigma' o s h cls fields v lx l s' sf lsf arg_id cls_a body meth returnT ct,
      sigma = SIGMA s h ->
      Some (Heap_OBJ cls fields lx) = lookup_heap_obj h o -> 
      Some (m_def returnT meth cls_a arg_id (Return body)) = find_method cls meth -> 
      value v ->
      sf = sf_update empty_stack_frame arg_id v ->
      l = (current_label sigma) ->
      lsf = Labeled_frame l sf ->
      s' = cons lsf s ->
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
      flow_to (current_label sigma) lb = true ->
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


Fixpoint surface_syntax (t : tm) :=
  match t with
    | Tvar x => true
    | null => true
    | FieldAccess e f => (surface_syntax e)
    | MethodCall e1 meth e2 => if (surface_syntax e1) then (surface_syntax e2) else false
    | NewExp cls => true
(* label related *)
    | l lb => true
    | labelData e lb => (surface_syntax e)
    | unlabel e => (surface_syntax e)
    | labelOf e => (surface_syntax e)
    | unlabelOpaque e => (surface_syntax e)
    | opaqueCall e => (surface_syntax e)
(* statements *)
    | Skip => false
    | Assignment x e => (surface_syntax e)
    | FieldWrite e1 f e2 =>  if (surface_syntax e1) then (surface_syntax e2) else false
    | If id0 id1 e1 e2 =>  if (surface_syntax e1) then (surface_syntax e2) else false
    | Sequence e1 e2 =>  if (surface_syntax e1) then (surface_syntax e2) else false
    | Return e => false

(* special terms *)
    | ObjId o =>  false
  (* runtime labeled date*)
    | v_l e lb => false
    | v_opa_l e lb => false
    | dot => false
  end.

Inductive ty : Type :=
  | classTy : cn -> ty 
  | LabelTy : ty
  | LabelelTy : ty -> ty
  | OpaqueLabeledTy : ty -> ty
  | voidTy : ty. 

Definition typing_context := id -> (option ty).
Definition empty_context : typing_context := fun _ => None.

Definition update_typing (gamma : typing_context) (x:id) (T : ty) : typing_context :=
      fun x' => if beq_id x x' then (Some T) else gamma x. 

Fixpoint dot_free (t : tm) :=
  match t with
    | Tvar x => true
    | null => true
    | FieldAccess e f => (dot_free e)
    | MethodCall e1 meth e2 => if (dot_free e1) then (dot_free e2) else false
    | NewExp cls => true
(* label related *)
    | l lb => true
    | labelData e lb => (dot_free e)
    | unlabel e => (dot_free e)
    | labelOf e => (dot_free e)
    | unlabelOpaque e => (dot_free e)
    | opaqueCall e => (dot_free e)
(* statements *)
    | Skip => true
    | Assignment x e => (dot_free e)
    | FieldWrite e1 f e2 =>  if (dot_free e1) then (dot_free e2) else false
    | If id0 id1 e1 e2 =>  if (dot_free e1) then (dot_free e2) else false
    | Sequence e1 e2 =>  if (dot_free e1) then (dot_free e2) else false
    | Return e => (dot_free e)

(* special terms *)
    | ObjId o =>  true
  (* runtime labeled date*)
    | v_l e lb => (dot_free e)
    | v_opa_l e lb => (dot_free e)
    | dot => false
  end.


Inductive has_type : Class_table -> typing_context -> heap -> tm -> ty -> Prop :=
(*variable *)
  | T_Var : forall Gamma x T CT h , 
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
  | T_MethodCall : forall Gamma Gamma' e meth argu CT h T returnT cls_def body arg_id arguT,
      has_type CT Gamma h e (classTy T) ->
      has_type CT Gamma h argu (classTy arguT) ->
      Some cls_def = CT(T) ->
      find_method cls_def meth = Some (m_def returnT meth arguT arg_id (Return body))  ->
      Gamma' = update_typing empty_context arg_id (classTy arguT) ->
      has_type CT Gamma' h (body) (classTy returnT) ->
      surface_syntax body = true ->
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
  | T_assignment : forall h Gamma CT e T x, 
      Gamma x = Some T ->
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
      has_type CT Gamma h (v_opa_l v lb) (OpaqueLabeledTy T)
  | T_dot : forall h Gamma T CT,
      has_type CT Gamma h dot T. 




Inductive wfe_stack_frame : Class_table -> heap -> labeled_stack_frame -> Prop :=
  | stack_frame_wfe : forall h lsf sf lb ct,
        lsf = Labeled_frame lb sf ->
         (forall x v, sf x = Some v  ->
               (
               v = null \/ 
                 ( exists cls_name o, v = ObjId o 
                              /\ (exists F lo field_defs method_defs , lookup_heap_obj h o = Some (Heap_OBJ (class_def cls_name field_defs method_defs) F lo)
                                      /\ (ct cls_name = Some (class_def cls_name field_defs method_defs))
                                   ) 
                  )    )  ) ->
        wfe_stack_frame ct h lsf. 

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

Inductive wfe_stack : Class_table -> heap -> stack -> Prop :=
  | main_stack_wfe : forall ct s h lb,
        wfe_heap ct h -> 
        s = cons (Labeled_frame lb empty_stack_frame) nil ->
        forall lb, wfe_stack ct h (cons (Labeled_frame lb empty_stack_frame) nil)
  | stack_wfe : forall s ct s' lb sf h, 
        s = cons (Labeled_frame lb sf) s'->
        wfe_stack ct h s' ->
        wfe_heap ct h ->
        wfe_stack_frame ct h (Labeled_frame lb sf) ->
        wfe_stack ct h s.

Lemma wfe_stack_value : forall gamma CT s h sigma v clsT, 
    sigma = SIGMA s h ->  wfe_heap CT h -> wfe_stack CT h s 
      -> (has_type CT gamma h v (classTy clsT))
      -> value v -> (v = dot \/ v = null \/ 
                 ( exists o, v = ObjId o 
                              /\ (exists F lo field_defs method_defs , 
                                      lookup_heap_obj h o = Some (Heap_OBJ (class_def clsT field_defs method_defs) F lo)
                                      /\ (CT clsT = Some (class_def clsT field_defs method_defs))
                                   )
                  )    ).
Proof. 
    intros gamma CT s h sigma v clsT. intro. intro. intro.  intro. intro. 
    induction H3. right. right.  exists o. split. auto. inversion H2. 
    destruct H10 as [F].     destruct H10 as [lo].    
    destruct H9 as [field_defs].    destruct H9 as [method_defs]. 
    exists F. exists lo. exists field_defs. exists method_defs.  
    split. rewrite <-H9. rewrite <- H10. auto. rewrite <- H9. auto.
    
    inversion H2. 

    right. left. auto. 
    right. inversion H2. right.  inversion H2. right.  inversion H2. left. auto.
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

Lemma fresh_heap_nil : forall h CT h' n0 ho0, 
    wfe_heap CT h ->
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

Lemma fresh_heap : forall h h' CT  n0 ho0, 
    wfe_heap CT h ->
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
    intro contra.  rewrite contra in H1. intuition. rewrite H10.
    fold lookup_heap_obj. rewrite <- H12. 
    destruct H3. inversion H2. rewrite H3. auto.
    destruct H3 as [o']. destruct H3 as [ho']. destruct H3 as [h''].
   induction o'.
    apply IHh with (ho0:=ho') (n0:=n1) (h':=h''). inversion H2. apply H4. auto.
    inversion H2. rewrite H11 in H14. inversion H14. destruct H3. 
    rewrite <- H16 in H13. 
    apply oid_trans with (n1:=n) (n2:=n0) (n3:=n1). auto. auto. auto.
    destruct H3. inversion H2. auto.
Qed. 


Lemma fresh_oid_heap : forall h CT o,
    wfe_heap CT h ->
    o = (get_fresh_oid h) -> 
    lookup_heap_obj h o = None.
Proof. intros. generalize dependent h. induction h. 
           - unfold get_fresh_oid. auto.
           - intros. unfold get_fresh_oid in H0. 
              induction a. induction o0.   
              rewrite H0.
              apply fresh_heap with (h:=((OID n, h0) :: h)) (h':=h) (CT:=CT)
                         (n0:=n) (ho0:=h0).
              auto. auto. intuition. 
Qed. 

(* reduction preserve well-form of stack and heap *)
Theorem reduction_preserve_wfe : forall CT s s' h h' sigma sigma',
    sigma = SIGMA s h ->  wfe_heap CT h -> wfe_stack CT h s ->     field_wfe_heap CT h -> 
     sigma' = SIGMA s' h' -> 
    forall t T, has_type CT empty_context h t T -> 
     forall t',  Config CT t sigma ==> Config CT t' sigma' ->
    wfe_heap CT h' /\ wfe_stack CT h' s' /\  field_wfe_heap CT h'.
Proof with auto.

Admitted. 

Lemma excluded_middle_label : forall lb, (flow_to lb L_Label = true) \/ (flow_to lb L_Label = false).
Proof with eauto.
  intros. case lb. intro principal. induction principal. unfold L_Label. 
  unfold flow_to. left.  unfold subset. auto.
     unfold L_Label.   unfold flow_to. left. unfold subset. auto.
Qed. 

Reserved Notation "c '=e=>' c'"
  (at level 40, c' at level 39).



Fixpoint erasure_L_fun (t : tm) :=
  match t with
    | Tvar x => Tvar x
    | null => null
    | FieldAccess e f => FieldAccess (erasure_L_fun e) f
    | MethodCall e1 meth e2 => MethodCall (erasure_L_fun e1) meth (erasure_L_fun e2)
    | NewExp cls => NewExp cls
(* label related *)
    | l lb => l lb
    | labelData e lb => labelData (erasure_L_fun e) lb
    | unlabel e => unlabel (erasure_L_fun e)
    | labelOf e => labelOf (erasure_L_fun e)
    | unlabelOpaque e => unlabelOpaque (erasure_L_fun e)
    | opaqueCall e => opaqueCall (erasure_L_fun e)
(* statements *)
    | Skip => Skip
    | Assignment x e => Assignment x (erasure_L_fun e)
    | FieldWrite e1 f e2 => FieldWrite (erasure_L_fun e1) f (erasure_L_fun e2)
    | If id0 id1 e1 e2 => If id0 id1 (erasure_L_fun e1) (erasure_L_fun e2)
    | Sequence e1 e2 => Sequence (erasure_L_fun e1) (erasure_L_fun e2)
    | Return e => Return (erasure_L_fun e)

(* special terms *)
    | ObjId o =>  ObjId o
  (* runtime labeled date*)
    | v_l e lb => if (flow_to lb L_Label) then v_l (erasure_L_fun e) lb else dot 
    | v_opa_l e lb => if (flow_to lb L_Label) then v_opa_l (erasure_L_fun e) lb else dot 
    | dot => dot
  end.

(* Notes: add a reduction rule for dot.f fieldAccess, 
    so that it reduces to dot and changes the current label to high*)

Fixpoint erasure_obj_null (t: option tm) (h:heap) : (option tm) :=
  match t with 
    | Some null => Some null
    | Some (ObjId o) => match (lookup_heap_obj h o) with 
                              | Some (Heap_OBJ cls fields lb) => if (flow_to lb L_Label) then Some (ObjId o) else Some dot
                              | None => Some dot (*already deleted object*)
                          end
    | Some dot => Some dot
    | None => None
    | _ => None
  end. 


Fixpoint erasure_stack (s:stack) (h:heap): stack :=
  match s with 
    | nil => nil 
    | cons (Labeled_frame lb sf) s'=> cons (Labeled_frame lb (fun x => (erasure_obj_null (sf x) h))) s'  (*if (flow_to lb L_Label) then cons (Labeled_frame lb (fun x => (erasure_obj_null (sf x) h))) (erasure_stack s' h)
                                                                else erasure_stack s' h*)
  end. 

Fixpoint erasure_heap (h:heap) : heap := 
    match h with 
      | nil => nil
      | h1 :: t => match h1 with 
                            | ( o0 , ho ) => match ho with 
                                                       | Heap_OBJ cls F lb => if (flow_to lb L_Label) then 
                                                                              ( o0 , (Heap_OBJ cls (fun x => (erasure_obj_null (F x) h)) lb)) :: (erasure_heap t) 
                                                                              else (erasure_heap t) 
                                                      end
                      end
    end.



Reserved Notation "c '=eH=>' c'"
  (at level 40, c' at level 39).

Inductive erasure_H : config -> config -> Prop :=
(* variabel access *)
  | Er_var_H : forall id sigma ct,
      Config ct (Tvar id) sigma =eH=> Config ct dot sigma

(* field read *)
  | Er_fieldRead1 : forall sigma sigma' e e' f ct,
      Config ct e sigma =eH=>  Config ct e' sigma' -> 
      Config ct (FieldAccess e f) sigma =eH=> Config ct (FieldAccess e' f) sigma'

  | Er_fieldRead2 : forall sigma f ct,
      Config ct (FieldAccess dot f) sigma =eH=> Config ct dot sigma

(* method call *)
  | Er_MethodCall1 : forall sigma sigma' e e' e2 id ct,
       Config ct e sigma =eH=>  Config ct e' sigma' -> 
      Config ct (MethodCall e id e2) sigma =eH=> Config ct (MethodCall e' id e2)  sigma'

  | Er_MethodCall2 : forall sigma e id ct e' sigma',
      Config ct e sigma =eH=>  Config ct e' sigma' -> 
      Config ct (MethodCall dot id e) sigma =eH=> Config ct (MethodCall dot id e') sigma'

  | Er_MethodCall3 : forall sigma id ct,
      Config ct (MethodCall dot id dot) sigma  =eH=> Config ct dot sigma


(* new expression *)
  | Er_NewExp_H : forall sigma ct cls_name,
      Config ct (NewExp cls_name) sigma =eH=> Config ct dot sigma

(* label data express *)
  (* context rule *)
  | Er_LabelData1 : forall sigma sigma' e e' lb ct ,
      Config ct e sigma =eH=>  Config ct e' sigma' -> 
      Config ct (labelData e lb) sigma =eH=> Config ct (labelData e' lb) sigma' 

  | Er_LabelData_dot : forall sigma lb ct,
      Config ct (labelData dot lb) sigma =eH=> Config ct dot sigma


(* unlabel *)
  (* context rule *)
  | Er_unlabel1 : forall sigma sigma' e e' ct,
      Config ct e sigma =eH=>  Config ct e' sigma' -> 
      Config ct  (unlabel e) sigma =eH=>       Config ct (unlabel e') sigma'
  | Er_unlabel_dot : forall sigma ct,
      Config ct  (unlabel dot) sigma =eH=> Config ct dot sigma

(* Label of *)
  (* context rule *)
  | Er_labelof1 : forall sigma sigma' e e' ct,
       Config ct e sigma =eH=>  Config ct e' sigma' -> 
       Config ct (labelOf e) sigma =eH=> Config ct (labelOf e') sigma'
  | Er_labelof_dot : forall sigma ct,
       Config ct (labelOf dot) sigma =eH=> Config ct dot sigma


(* unlabel opaque*)
  (* context rule *)
  | Er_unlabel_opaque1 : forall sigma sigma' e e' ct,
      Config ct e sigma =eH=>  Config ct e' sigma' -> 
     Config ct (unlabelOpaque e) sigma =eH=>       Config ct (unlabelOpaque e') sigma'

  | Er_unlabel_opaque_dot : forall sigma ct,
      Config ct  (unlabelOpaque dot) sigma =eH=> Config ct dot sigma



(* Opaque call *)
  (* context rule *)
  | Er_opaquecall1 : forall sigma sigma' e e' ct,
      e <> Return dot ->
       Config ct e sigma =eH=>  Config ct e' sigma' -> 
      Config ct (opaqueCall e) sigma =eH=> Config ct (opaqueCall e') sigma'

  | Er_opaquecall_dot : forall sigma ct,
      Config ct (opaqueCall dot) sigma =eH=> Config ct dot sigma

  (* opaque call with return statement *)
(*
  | Er_opaquecall_return : forall sigma sigma' s h s' lsf ct lb,
      sigma = SIGMA s h->
      s = cons lsf s' ->
      s' <> nil ->
      lb = (current_label sigma) ->
      sigma' = SIGMA s' h->
      Config ct (opaqueCall (Return dot)) sigma =eH=> Config ct (v_opa_l dot lb) sigma'*)

(* assignment *)
  (* context rule *)
  | Er_assignment1 : forall sigma sigma' e e' id ct,
       Config ct e sigma =eH=> Config ct e' sigma' -> 
       Config ct (Assignment id e) sigma =eH=> Config ct (Assignment id e') sigma'

  (* assignment *)
  | Er_assignment_H : forall sigma id ct,
      Config ct (Assignment id dot) sigma =eH=> Config ct dot sigma

(* Field Write *)
  (* context rule 1 *)
  | Er_fieldWrite1 : forall sigma sigma' f e1 e1' e2 ct,
       Config ct e1 sigma =eH=> Config ct e1' sigma' -> 
       Config ct (FieldWrite e1 f e2) sigma =eH=> Config ct (FieldWrite e1' f e2) sigma'

  (* context rule 2 *)
  | Er_fieldWrite2 : forall sigma sigma' f  e2 e2' ct,
       Config ct e2 sigma =eH=> Config ct e2' sigma' -> 
       Config ct (FieldWrite dot f e2) sigma =eH=> Config ct (FieldWrite dot f e2') sigma'
  (* field write dot *)
  | Er_fieldWrite_L : forall sigma  f ct ,
      Config ct (FieldWrite dot f dot) sigma =eH=> Config ct dot sigma


(* return statement *)
  (* context rule*)
  | Er_return1 : forall sigma sigma' e e' ct,
        Config ct e sigma =eH=> Config ct e' sigma' -> 
        Config ct (Return e) sigma =eH=> Config ct (Return e') sigma'
(*
  | Er_return_H : forall sigma sigma' s s' h lsf ct, 
      sigma = SIGMA s h ->
      s = cons lsf s' ->
      s' <> nil ->
      sigma' = SIGMA s' h ->
      Config ct (Return dot) sigma =eH=> Config ct dot sigma'*)

(* if statement *)
  | Er_b1 : forall sigma s1 s1' sigma' s2 id1 id2 ct, 
      Config ct s1 sigma =eH=> Config ct s1' sigma' -> 
      Config ct (If id1 id2 s1 s2) sigma =eH=> Config ct (If id1 id2 s1' s2) sigma'
  | Er_b2 : forall sigma sigma' s2 s2' id1 id2 ct, 
      Config ct s2 sigma =eH=> Config ct s2' sigma' -> 
      Config ct (If id1 id2 dot s2) sigma =eH=> Config ct (If id1 id2 dot s2') sigma'
  | Er_b3 : forall sigma id1 id2 ct,
      Config ct (If id1 id2 dot dot) sigma =eH=> Config ct dot sigma

(* sequence *)
   (* context rule *)
  | Er_seq1 : forall sigma s1 s2 s1' sigma' ct, 
    Config ct s1 sigma =eH=> Config ct s1' sigma' -> 
    Config ct (Sequence s1 s2) sigma =eH=> Config ct (Sequence s1' s2) sigma'
   (* sequence rule *)
  | Er_seq2 : forall sigma s ct s' sigma', 
    Config ct s sigma =eH=> Config ct s' sigma' ->
    Config ct (Sequence dot s) sigma =eH=> Config ct s' sigma'

(* null *)
  | Er_null_H : forall sigma ct,
    Config ct null sigma =eH=> Config ct dot sigma

(* object o *)
  | Er_object_H : forall ct sigma o,
    Config ct (ObjId o) sigma =eH=> Config ct dot sigma

(* label l *)
  | Er_label_H : forall sigma ct lbl,
    Config ct (l lbl) sigma =eH=> Config ct dot sigma

(* v_l v lb *)
  | Er_labeled_H : forall sigma ct v lb,
    Config ct (v_l v lb) sigma =eH=> Config ct dot sigma

(* v_opa_l v lb *)
  | Er_v_opa_l_H : forall sigma ct v lb,
    Config ct (v_opa_l v lb) sigma =eH=> Config ct dot sigma

  | Er_skip : forall sigma ct, 
    Config ct Skip sigma =eH=> Config ct dot sigma

where "c '=eH=>' c'" := (erasure_H c c').

Inductive multi_step_erasure_H : config -> config -> Prop :=
  | H_erasure_single_step : forall ct  t sigma t' sigma', 
          Config ct t sigma =eH=> Config ct t' sigma' ->
          (t' = Return dot \/  ( flow_to (current_label sigma') L_Label = true)) ->
          multi_step_erasure_H (Config ct t sigma) (Config ct t' sigma' )
  | H_erasure_multi_step : forall ct  t sigma t' sigma' t'' sigma'',
         Config ct t sigma =eH=> Config ct t' sigma' ->
         ( flow_to (current_label sigma') L_Label = false) ->
          multi_step_erasure_H  (Config ct t' sigma' )  (Config ct t'' sigma'' ) ->
          multi_step_erasure_H (Config ct t sigma) (Config ct t'' sigma'' ).

Lemma heap_consist_ct : forall h o ct cls F lo ,
  wfe_heap ct h -> 
  lookup_heap_obj h o = Some (Heap_OBJ cls F lo) ->
  exists cn field_defs method_defs, ct cn = Some cls /\ cls = (class_def cn field_defs method_defs).
Proof with auto.
  intros. induction H. 
  - inversion H0.
  - unfold lookup_heap_obj in H0.
     case_eq (beq_oid o o0).   intros. rewrite H in H0.  rewrite H6 in H0. inversion H0. 
      rewrite -> H8 in H3. inversion H3.   
      exists cn0. exists  field_defs. exists method_defs. 
      split. auto. auto. intro. rewrite H in H0. rewrite H6 in H0.
      fold lookup_heap_obj in H0. apply IHwfe_heap. auto. 
Qed.

Lemma erasure_final : forall ct  t sigma t' sigma', 
  multi_step_erasure_H (Config ct t sigma) (Config ct t' sigma') ->
            (t' = Return dot \/  ( flow_to (current_label sigma') L_Label = true)).
Proof. 
  intros ct  t sigma t' sigma'.
  intro Hy. remember (Config ct t sigma)  as config. remember (Config ct t' sigma') as config'.
  generalize dependent t.   generalize dependent t'.   
  generalize dependent sigma.   generalize dependent sigma'.     
  induction Hy. 
  intros. inversion Heqconfig'. subst.  auto.
  intros.  
  inversion Heqconfig. inversion Heqconfig'. subst.
  destruct IHHy with  sigma'0 sigma' t'0 t'; auto. 
Qed. 

Lemma erasure_H_deterministic : forall ct t sigma t1 t2 sigma1 sigma2, 
    (Config ct t sigma) =eH=> (Config ct t1 sigma1 ) ->
    (Config ct t sigma)  =eH=>(Config ct t2 sigma2 ) ->
    t1 = t2 /\ sigma1 = sigma2.
Proof. 
    intros ct t sigma t1 t2 sigma1 sigma2.
intro H_erasure1.    intro H_erasure2.
   remember (Config ct t1 sigma1) as t1_config. 
     generalize dependent t2.      generalize dependent t1. 
    induction H_erasure1; intros; inversion Heqt1_config; subst; 
      try (inversion H_erasure2; subst; auto); try (inversion H0; fail);
                try (destruct  IHH_erasure1 with e' e'0; auto;  subst; auto; inversion H_erasure1; fail); 
                try (inversion H_erasure1; fail).
      - intuition. inversion H5. inversion H5.   
      - (destruct  IHH_erasure1 with e1' e1'0; auto;  subst; auto; inversion H_erasure1).
       - (destruct  IHH_erasure1 with e2' e2'0; auto;  subst; auto; inversion H_erasure1).
      - (destruct  IHH_erasure1 with s1' s1'0; auto;  subst; auto; inversion H_erasure1).
      - (destruct  IHH_erasure1 with s2' s2'0; auto;  subst; auto; inversion H_erasure1).
      - (destruct  IHH_erasure1 with s1' s1'0; auto;  subst; auto; inversion H_erasure1).
Qed. 


Lemma multi_step_erasure_H_deterministic : forall ct t sigma t1 t2 sigma1 sigma2, 
    multi_step_erasure_H (Config ct t sigma) (Config ct t1 sigma1 ) ->
    multi_step_erasure_H (Config ct t sigma) (Config ct t2 sigma2 ) ->
    t1 = t2 /\ sigma1 = sigma2.
Proof. intros  ct t sigma t1 t2 sigma1 sigma2.
   intro H_erasure1.    intro H_erasure2.
   remember (Config ct t1 sigma1) as t1_config. 
     generalize dependent t2.      generalize dependent t1. 
    induction H_erasure1. 
    intros.  inversion Heqt1_config. subst. inversion H_erasure2. subst. 
    apply erasure_H_deterministic with ct t0 sigma0; auto.
    subst.  assert (t1 = t' /\ sigma1 = sigma'). 
    apply erasure_H_deterministic with ct t0 sigma0; auto.
    destruct H1. subst.  destruct H0. 
    subst. inversion H8. inversion H2. inversion H11.  inversion H4. inversion H12. 
    rewrite H0 in H7. inversion H7.
    intros. inversion Heqt1_config. subst.  
   
    inversion H_erasure2. destruct H7. subst. 
    assert (t' = Return dot /\ sigma' = sigma2). 
    apply erasure_H_deterministic with ct t0 sigma0; auto.
   destruct H1.  subst.  inversion H_erasure1. inversion H4. inversion H10.  inversion H6. inversion H11.  
   subst. assert (t' = t2 /\ sigma' = sigma2). 
    apply erasure_H_deterministic with ct t0 sigma0; auto.
    destruct H1. subst.  rewrite H0 in H7. inversion H7. 
    subst. assert (t' = t'0 /\ sigma' = sigma'0). 
    apply erasure_H_deterministic with ct t0 sigma0; auto. 
    destruct H1. subst. 
    destruct IHH_erasure1 with t1 t2; auto.
Qed. 


Reserved Notation "c '=e=' c'"
  (at level 40, c' at level 39).


Definition erasure_sigma_fun (sigma :Sigma) : Sigma :=
    match sigma with 
     | (SIGMA s h) =>SIGMA (erasure_stack s h) (erasure_heap h)
    end. 

Inductive erasure : config -> config -> Prop :=
  | erasure_L_context : forall ct s h t s' h' t',
      flow_to (current_label (SIGMA s h)) L_Label = true ->
      t' = erasure_L_fun t ->
      (SIGMA s' h') = erasure_sigma_fun (SIGMA s h) ->
      erasure (Config ct t (SIGMA s h)) (Config ct t' (SIGMA s' h'))  
  | erasure_H_context : forall  ct s h s' h' t t' s'' h'',
      flow_to (current_label (SIGMA s h)) L_Label = false ->
      multi_step_erasure_H (Config ct t (SIGMA s h)) (Config ct t' (SIGMA s' h')) ->
      (SIGMA s'' h'') = erasure_sigma_fun (SIGMA s' h') ->
      erasure (Config ct t (SIGMA s h))  (Config ct (t') (SIGMA s'' h''))  
where "c '=e=>' c'" := (erasure c c').

Lemma erasure_deterministic : forall ct t t1 t2 sigma sigma1 sigma2, 
  (erasure (Config ct t sigma) (Config ct t1 sigma1)) ->
  (erasure (Config ct t sigma) (Config ct t2 sigma2)) ->
  t1 = t2 /\ sigma1 = sigma2. 
Proof. 
  intros ct t t1 t2 sigma sigma1 sigma2. 
  intro H_erasure1.   intro H_erasure2.
  remember (current_label sigma) as lb. 
  assert ((flow_to lb L_Label = true) \/ (flow_to lb L_Label = false)).
  apply excluded_middle_label. destruct H. subst. 
  inversion H_erasure1. inversion H_erasure2. subst. inversion H10. subst. 
  rewrite <- H15 in H7. inversion H7.  auto. subst. rewrite <- H10 in H. rewrite H in H12. inversion H12.
  subst. rewrite H in H4. inversion H4. 
   
    inversion H_erasure1. inversion H_erasure2. subst. inversion H10. subst. 
    rewrite <- H15 in H7. inversion H7.  auto. subst. rewrite H in H4. inversion H4. 
    subst.  inversion H_erasure2. subst.  rewrite H in H3. inversion H3.
    subst. 
    assert (t1 = t2 /\(SIGMA s' h') = (SIGMA s'0 h'0)). 
    apply multi_step_erasure_H_deterministic with ct t (SIGMA s h); auto. 
    destruct H0. inversion H1. subst. rewrite <- H7  in H11. inversion H11. subst.  auto. 
Qed. 


Lemma induction_multi_step_erasure_H: forall e f sigma ct e' sigma', 
    multi_step_erasure_H (Config ct (FieldAccess e f) sigma)  (Config ct e' sigma') ->
    e = Return dot \/ exists e0, multi_step_erasure_H (Config ct e sigma)  (Config ct e0 sigma').
Proof. 
    intros.  remember (Config ct (FieldAccess e f) sigma) as config. 
    remember (Config ct e' sigma') as config'. 
    generalize dependent e.     generalize dependent e'.
        generalize dependent sigma.     generalize dependent sigma'.
    induction H. 
  intros. inversion Heqconfig'. inversion Heqconfig. subst. 
  destruct H0. subst. inversion H. left. auto. 

  inversion H. subst. right. exists e'0. apply H_erasure_single_step. auto. 
  right. auto. left. auto. 

  intros. inversion Heqconfig'. inversion Heqconfig. subst. 
  
  inversion H. inversion Heqconfig'. inversion Heqconfig. subst. 
  destruct  IHmulti_step_erasure_H with sigma'0 sigma' e' e'0; auto.
  subst. right. exists dot.  apply H_erasure_single_step; auto.
  inversion H1. destruct H10. subst. inversion H5. subst. auto.
  subst. inversion H5. inversion H4. subst. rewrite H0 in H10. auto.
  subst. inversion H8. inversion H4.   subst. inversion H11. destruct H13.
  subst. inversion H5. subst. inversion H5. subst. inversion H9.
  right. destruct H2 as [e0].
  exists e0. apply H_erasure_multi_step with e'0 sigma'; auto. left. auto.
 Qed. 

Lemma multi_erasure_L_tm_equal : forall t, 
   erasure_L_fun (erasure_L_fun t) = (erasure_L_fun t).
  Proof. induction t; try (unfold erasure_L_fun; auto); try (fold erasure_L_fun; rewrite IHt; auto);
 try (fold erasure_L_fun; rewrite IHt1; rewrite IHt2; auto).
 - fold erasure_L_fun. unfold erasure_L_fun. fold erasure_L_fun. 
    case_eq (flow_to l0 L_Label ). intro. unfold erasure_L_fun. fold erasure_L_fun. rewrite H. rewrite IHt.  auto. 
    intro. unfold erasure_L_fun. auto. 
 - fold  erasure_L_fun. 
    case_eq (flow_to l0 L_Label ). intro. unfold erasure_L_fun. fold erasure_L_fun. rewrite H. rewrite IHt.  auto. 
    intro. unfold erasure_L_fun. auto.
Qed.  

Lemma lookup_erasure_heap : forall h o cls F lb, 
   lookup_heap_obj h o = Some (Heap_OBJ cls F lb) -> 
   flow_to lb L_Label = true -> 
   exists F', lookup_heap_obj (erasure_heap h) o = Some (Heap_OBJ cls F' lb) .
Proof.      intros. induction h. unfold lookup_heap_obj in H. inversion H. 
      induction a. 
      case_eq ( beq_oid o o0). unfold lookup_heap_obj.  intro. 
      unfold erasure_heap. rename h0 into ho. induction ho. unfold  lookup_heap_obj in H. rewrite H1 in H. 
      inversion H. subst. rewrite H0. rewrite H1. exists (fun x : id => erasure_obj_null (F x) ((o0, Heap_OBJ cls F lb) :: h)). auto.
      intro. unfold  lookup_heap_obj in H. rewrite H1 in H. fold  lookup_heap_obj in H. 
      unfold erasure_heap. induction h0. fold erasure_heap.  unfold lookup_heap_obj. 
      case_eq (flow_to l0 L_Label). intro. rewrite H1. fold lookup_heap_obj.  apply IHh. auto. 
      intro. fold lookup_heap_obj. apply IHh. auto. 
Qed. 

Lemma multi_erasure_heap_equal : forall h, 
   erasure_heap (erasure_heap h) = (erasure_heap h).
  Proof. intro h.  induction h.  unfold erasure_heap. auto. induction a. rename h0 into ho.  unfold erasure_heap.
  induction ho. case_eq (flow_to l0 L_Label). 
  + intro. rewrite H. fold erasure_heap. fold erasure_heap. 
  assert ((o,
Heap_OBJ c (fun x : id =>   erasure_obj_null (erasure_obj_null (f x) ((o, Heap_OBJ c f l0) :: h))
     ((o, Heap_OBJ c  (fun x0 : id => erasure_obj_null (f x0) ((o, Heap_OBJ c f l0) :: h)) l0) :: erasure_heap h)) l0) = 
        (o, Heap_OBJ c (fun x : id => erasure_obj_null (f x) ((o, Heap_OBJ c f l0) :: h))   l0) ).

  Require Import Coq.Logic.FunctionalExtensionality.
  assert (forall a, (fun x : id =>   erasure_obj_null (erasure_obj_null (f x) ((o, Heap_OBJ c f l0) :: h))
     ((o, Heap_OBJ c  (fun x0 : id => erasure_obj_null (f x0) ((o, Heap_OBJ c f l0) :: h)) l0) :: erasure_heap h)) a =  (fun x : id => erasure_obj_null (f x) ((o, Heap_OBJ c f l0) :: h)) a).
   intro x. 
   case (f x). induction t; try (unfold erasure_obj_null; auto).
   rename o0 into o'. remember ((o, Heap_OBJ c f l0) :: h) as h'. fold erasure_obj_null. 
   ++ remember (erasure_obj_null (Some (ObjId o')) h') as erased_field.
    unfold erasure_obj_null in Heqerased_field. 
    assert (forall h o, (exists cls F lb, lookup_heap_obj h o = Some (Heap_OBJ cls F lb) ) 
      \/ lookup_heap_obj h o = None).
    intro h0. induction h0.  right. unfold lookup_heap_obj. auto. 
    intro o0. induction a. case_eq ( beq_oid o0 o1). unfold lookup_heap_obj.  intro. unfold lookup_heap_obj. rewrite H0.
    rename h1 into ho. induction ho.     left. exists c0. exists f0. exists l1. auto. 
    intro. unfold lookup_heap_obj. rewrite H0. fold lookup_heap_obj. apply IHh0. 
    destruct H0 with h' o'. destruct H1 as [cls]. destruct H1 as [F]. destruct H1 as [lb]. 
    +++  rewrite H1 in Heqerased_field. rewrite H1.
      case_eq ( flow_to lb L_Label ).  
    ++++ intro. rewrite H2 in  Heqerased_field. 
      unfold erasure_obj_null. fold erasure_obj_null.  auto.
      assert (exists F', lookup_heap_obj (erasure_heap h') o' = Some (Heap_OBJ cls F' lb)).
      apply lookup_erasure_heap with F. auto. auto.  
      assert (   ((o, Heap_OBJ c (fun x1 : id => erasure_obj_null (f x1) h') l0) :: (erasure_heap h)) = (erasure_heap h')).
      remember ( erasure_heap h' ) as erasuedh. 
      unfold erasure_heap in Heqerasuedh. rewrite Heqh' in Heqerasuedh. rewrite H in Heqerasuedh. fold erasure_heap in Heqerasuedh.
      rewrite Heqerasuedh. 
      assert ((fun x1 : id => erasure_obj_null (f x1) h') = (fun x1 : id => erasure_obj_null (f x1) ((o, Heap_OBJ c f l0) :: h))). rewrite Heqh'. auto. 
      rewrite H4. auto. rewrite H4. destruct H3 as [F']. rewrite H3. rewrite H2. auto. 
    ++++ intro.  unfold erasure_obj_null. auto.
    +++ rewrite H1. unfold erasure_obj_null. auto.
    ++ unfold erasure_obj_null. auto.
    ++  fold erasure_obj_null. auto.
   apply functional_extensionality in H0. rewrite H0.  auto. 
   ++   rewrite IHh. rewrite H0. auto. 
  + intro. fold erasure_heap. auto.
Qed.  

Lemma erasure_obj_null_equal : forall h t, 
  erasure_obj_null (erasure_obj_null t h) h = (erasure_obj_null t h).
Proof. intros. induction t. induction a; try (unfold erasure_obj_null; auto). 
      assert (forall h o, (exists cls F lb, lookup_heap_obj h o = Some (Heap_OBJ cls F lb) ) 
      \/ lookup_heap_obj h o = None).
    intro h0. induction h0.  right. unfold lookup_heap_obj. auto. 
    intro o0. induction a. case_eq ( beq_oid o0 o1). unfold lookup_heap_obj.  intro. unfold lookup_heap_obj. rewrite H. 
     rename h1 into ho. induction ho.     left. exists c. exists f. exists l0. auto. 
    intro. unfold lookup_heap_obj. rewrite H. fold lookup_heap_obj. apply IHh0. 
    destruct H with h o. destruct H0 as [cls]. destruct H0 as [F]. destruct H0 as [lb]. rewrite H0.
    case_eq (flow_to lb L_Label ). intro. rewrite H0. rewrite H1. auto. 
   intro. auto. 
  rewrite H0. auto. 
  (unfold erasure_obj_null; auto).
Qed. 

Lemma multi_erasure_stack_equal : forall s h, 
   erasure_stack (erasure_stack s h) h = (erasure_stack s h).
Proof. intros.  induction s. 
  + unfold erasure_stack. auto.
  + unfold erasure_stack. induction a. 
      case_eq ( flow_to l0 L_Label). intro. rewrite H. fold erasure_stack. auto. 
      assert ( forall a,  (erasure_obj_null (erasure_obj_null (s0 a) h) h) = erasure_obj_null (s0 a) h).
      intro a. apply erasure_obj_null_equal. 
      assert ( forall x,  (fun x : id => erasure_obj_null (erasure_obj_null (s0 x) h) h) x  = (fun x : id => erasure_obj_null (s0 x) h) x).
      intro x.  apply H0. apply functional_extensionality in H1.  rewrite H1.  rewrite IHs.  auto. 
      intro. fold erasure_stack. auto. 
Qed. 

Lemma multi_erasure_sigma_helper : forall s h, 
  (erasure_stack (erasure_stack s h) (erasure_heap h)) = (erasure_stack s h).
  intros. induction s. unfold erasure_stack. auto. 
  induction a. remember (erasure_stack (Labeled_frame l0 s0 :: s) h) as Hy. 
  unfold  erasure_stack in HeqHy. case_eq (flow_to l0 L_Label). intro. rewrite H in HeqHy.
  fold erasure_stack in HeqHy. unfold erasure_stack. rewrite HeqHy.  rewrite H. fold erasure_stack.
  Lemma erasure_obj_null_equal_erasure_h : forall h t, 
    erasure_obj_null (erasure_obj_null t h) (erasure_heap h) = (erasure_obj_null t h).
    Proof. intros. induction t. induction a; try (unfold erasure_obj_null; auto). 
        assert (forall h o, (exists cls F lb, lookup_heap_obj h o = Some (Heap_OBJ cls F lb) ) 
        \/ lookup_heap_obj h o = None).
      intro h0. induction h0.  right. unfold lookup_heap_obj. auto. 
      intro o0. induction a. case_eq ( beq_oid o0 o1). unfold lookup_heap_obj.  intro. unfold lookup_heap_obj. rewrite H. 
       rename h1 into ho. induction ho.     left. exists c. exists f. exists l0. auto. 
      intro. unfold lookup_heap_obj. rewrite H. fold lookup_heap_obj. apply IHh0. 
      destruct H with h o. destruct H0 as [cls]. destruct H0 as [F]. destruct H0 as [lb]. rewrite H0.
      case_eq (flow_to lb L_Label ). intro. 
      assert (exists F', lookup_heap_obj (erasure_heap h) o = Some (Heap_OBJ cls F' lb)).
      apply lookup_erasure_heap with F. auto. auto. destruct H2 as [F']. rewrite H2. rewrite H1. auto. 
     intro. auto. 
    rewrite H0. auto. 
    (unfold erasure_obj_null; auto).
  Qed. 
  assert (forall a,  (fun x : id =>
   erasure_obj_null (erasure_obj_null (s0 x) h) (erasure_heap h)) a = (fun x : id => erasure_obj_null (s0 x) h) a).
  intro a. apply erasure_obj_null_equal_erasure_h. apply functional_extensionality in H0. rewrite H0. 
  rewrite IHs . auto. 
  intro. rewrite H in HeqHy. fold erasure_stack in HeqHy. rewrite HeqHy. auto. 
Qed. 



Lemma multi_erasure_sigma_equal : forall s h, 
   erasure_sigma_fun (erasure_sigma_fun (SIGMA s h)) = (erasure_sigma_fun (SIGMA s h)).
  Proof. 
  intros s h. unfold erasure_sigma_fun. assert (erasure_heap (erasure_heap h) = (erasure_heap h)). 
  apply multi_erasure_heap_equal. rewrite H.
  assert ((erasure_stack (erasure_stack s h) (erasure_heap h)) = (erasure_stack s h)). 
  apply multi_erasure_sigma_helper. rewrite H0. auto. 
Qed.  

(*
Lemma multi_erasure_equal : forall ct t t1 t2 sigma sigma1 sigma2, 
  (erasure (Config ct t sigma) (Config ct t1 sigma1)) ->
  (erasure (Config ct t1 sigma1) (Config ct t2 sigma2)) ->
  t1 = t2 /\ sigma1 = sigma2. 
Proof. 
 intros ct t t1 t2 sigma sigma1 sigma2. 
  intro H_erasure1.   intro H_erasure2.
  remember (current_label sigma) as lb. 
  assert ((flow_to lb L_Label = true) \/ (flow_to lb L_Label = false)).
  apply excluded_middle_label. destruct H. subst. 
  + inversion H_erasure1. 
  ++ subst. inversion H_erasure2. subst. 
  +++ split. assert (erasure_L_fun (erasure_L_fun t) = erasure_L_fun t ). apply multi_erasure_L_tm_equal. auto. 
    rewrite H10.   rewrite H7. 
    assert (erasure_sigma_fun (erasure_sigma_fun (SIGMA s h)) = (erasure_sigma_fun (SIGMA s h))).
    apply multi_erasure_sigma_equal. auto. 
  +++ subst. 
*)

Lemma field_access_context_erasure : forall e e' f sigma sigma' ct,
  Config ct (FieldAccess e f) sigma =e=>   Config ct e' sigma' ->
  flow_to (current_label sigma) L_Label = false ->
  e = dot \/ exists e0, Config ct e sigma =e=> Config ct e0 sigma'.
Proof. intros. 
  inversion H. subst. rewrite H5 in H0. inversion H0. subst. 
  assert ((e' = dot \/  ( flow_to (current_label (SIGMA s' h')) L_Label = true))).
    apply erasure_final with ct (FieldAccess e f) (SIGMA s h) . auto.
    destruct H1. subst. inversion H. subst. unfold erasure_L_fun in H12. inversion H12.
    subst. 
    inversion H12. subst. 
    inversion H3. subst. unfold erasure_L_fun in H. inversion H. subst.
    left. auto. left. auto. 
    assert (e = dot \/ exists e0, multi_step_erasure_H (Config ct e (SIGMA s h))
                                       (Config ct e0 (SIGMA s'0 h'0))  ).
    apply induction_multi_step_erasure_H with f dot. auto.  destruct H15. subst. left. auto. subst.   
    destruct H15 as [e0].
    right. exists e0. apply erasure_H_context with s'0 h'0; auto.

  assert (e = dot \/ exists e0, multi_step_erasure_H (Config ct e (SIGMA s h))  (Config ct e0 (SIGMA s' h'))).
  apply induction_multi_step_erasure_H with f e'. auto. destruct H2. subst. inversion H. left. auto. left. auto. 
  destruct H2 as [e0]. right. exists e0. apply erasure_H_context with s' h'; auto.
Qed. 


Lemma context_field_access_erasure : forall ct e f sigma sigma', 
    multi_step_erasure_H (Config ct (FieldAccess e f) sigma)
        (Config ct dot sigma') ->
    e = dot \/ multi_step_erasure_H (Config ct e sigma)
        (Config ct dot sigma').
Proof. intros.   remember (Config ct (FieldAccess e f) sigma) as config. 
    remember (Config ct dot sigma') as config'.  
    generalize dependent e. 
        generalize dependent sigma.     generalize dependent sigma'.
    induction H. intros.  inversion Heqconfig'. inversion Heqconfig. subst.
    inversion H.  subst.  left. auto. intros.  inversion Heqconfig'. inversion Heqconfig. subst.
    inversion H. subst. 
  destruct  IHmulti_step_erasure_H with sigma'0 sigma' e'; auto.
  right. subst. inversion H1. inversion H5. subst.  apply H_erasure_single_step; auto.
  subst. inversion H8. inversion H4. subst. inversion H11. inversion H5. inversion H9. 
  right. apply H_erasure_multi_step with e' sigma'; auto.
  left. auto.
Qed.
 

Lemma flow_join_label : forall lb joined_lb lb' L,
  flow_to lb L = false ->
  lb' = join_label joined_lb lb ->
  flow_to lb' L = false.
Proof. Admitted. 

Lemma erasure_sigma_fun_preserve_heap : forall h s1 h1' s2 s1' s2' h2' , 
    SIGMA s1' h1' = erasure_sigma_fun (SIGMA s1 h) ->
    SIGMA s2' h2' = erasure_sigma_fun (SIGMA s2 h) ->
    h1' = h2' .
Proof. 
  intros. unfold erasure_sigma_fun in H. unfold erasure_sigma_fun in H0. 
  inversion H. inversion H0.  auto. 
Qed. 

Lemma method_call_context_erasure2 : forall CT id0 e s h s'0 h'0, 
    multi_step_erasure_H (Config CT (MethodCall dot id0 e) (SIGMA s h))
       (Config CT dot (SIGMA s'0 h'0)) ->
    (e = dot \/ (multi_step_erasure_H (Config CT e (SIGMA s h))  (Config CT dot (SIGMA s'0 h'0))) ).
Proof. intros CT id0 e s h s'0 h'0.
    intro H_erasure. 
    remember  (Config CT (MethodCall dot id0 e) (SIGMA s h)) as config.    remember (Config CT dot (SIGMA s'0 h'0)) as config'.
   generalize dependent e. generalize dependent s. generalize dependent h. 
   generalize dependent s'0. generalize dependent h'0. induction H_erasure. 
   + intros. inversion Heqconfig'. inversion Heqconfig. subst. inversion H. subst.  left. auto. 
   + intros. inversion Heqconfig'. inversion Heqconfig. subst. inversion H. subst. ++ inversion H2. 
      ++  subst. induction sigma'. destruct IHH_erasure with h'0 s'0 h0 s0 e'; auto. 
      +++ subst.  inversion H_erasure.  subst.  inversion H4. subst. ++++  
            right.  apply  H_erasure_single_step; auto. ++++  subst. inversion H7.  
          subst. inversion H3. inversion H3. subst. inversion H10. inversion H4. inversion H8.
        +++  right. apply H_erasure_multi_step with e' (SIGMA s0 h0); auto. 
      ++ left. auto. 
Qed. 

Lemma value_erasure_to_dot : forall CT v sigma,
(*    forall T, has_type CT empty_context h e T -> *)
    value v -> v <> dot ->
    Config CT v sigma =eH=> Config CT dot sigma.
Proof. intros. induction H. + apply Er_object_H.
    + apply Er_skip. + apply Er_null_H. + apply Er_label_H. 
    + apply Er_labeled_H. + apply Er_v_opa_l_H. + intuition. Qed. 


  Lemma join_label_commutative : forall l1 l2, 
    join_label l1 l2 = join_label l2 l1. 
  Proof. Admitted. 

Lemma context_erasure_field_access : forall CT e e_r s s'0 h h'0 f, 
   multi_step_erasure_H (Config CT (FieldAccess e f) (SIGMA s h))
       (Config CT e_r (SIGMA s'0 h'0)) ->
    e = dot \/ (e_r = dot /\ multi_step_erasure_H (Config CT e (SIGMA s h))
       (Config CT dot (SIGMA s'0 h'0))) \/ (exists e0, multi_step_erasure_H (Config CT e (SIGMA s h))
       (Config CT e0 (SIGMA s'0 h'0))  /\ e_r = (FieldAccess e0 f) ).
  Proof. intros CT e e_r s s_r h h_r f. intro H_erasure.
    remember (Config CT (FieldAccess e f) (SIGMA s h)) as config.    remember (Config CT e_r (SIGMA s_r h_r)) as config_r.
    generalize dependent e. generalize dependent s. generalize dependent h. 
   generalize dependent e_r. generalize dependent s_r. generalize dependent h_r.
    induction H_erasure; intros; inversion Heqconfig; inversion Heqconfig_r; subst. 
   + destruct H0. ++ subst. inversion H. left. auto. 
    ++ subst. inversion H. 
    +++ subst. right. right. exists e'. split.  apply H_erasure_single_step; auto. auto.  
    +++ left. auto. 
   + subst. inversion H.
    ++ subst. induction sigma'. destruct IHH_erasure with h_r s_r e_r h0 s0 e'; auto.
      +++ right. subst. inversion H_erasure. ++++ subst. inversion H4. 
        +++++ subst. inversion H3.  +++++ left. auto. subst. split. auto. apply H_erasure_single_step; auto.   
        ++++ subst. inversion H7. subst. inversion H3.  subst. inversion H10.  inversion H4.  inversion H8. 
        +++ destruct H1. ++++ right. left. auto. split. destruct H1. auto. destruct H1. 
      apply H_erasure_multi_step with e' (SIGMA s0 h0); auto.   
         ++++ destruct H1 as [e0]. right. right. exists e0. auto. 
        destruct H1. split. apply  H_erasure_multi_step with e' (SIGMA s0 h0); auto. auto.
    ++ left. auto. 
Qed.  




Lemma dot_no_erasureH : forall sigma CT,
  ~ exists t sigma', (Config CT dot sigma) =eH=> (Config CT t sigma').
Proof. 
intros. intro contra. destruct contra as [t].  destruct H as [sigma']. inversion H.
Qed.

Lemma dot_no_multi_erasureH : forall sigma CT,
  ~ exists t sigma', multi_step_erasure_H (Config CT dot sigma) (Config CT t sigma').
Proof. intros. intro contra. destruct contra as [t]. destruct H as [sigma'].  inversion H. inversion H2.
inversion H4. Qed.


(*Method call context erasure*)
Lemma context_erasure_method_call_obj : forall CT e e2 id0 s s'0 h h'0 e_r, 
   multi_step_erasure_H (Config CT (MethodCall e id0 e2) (SIGMA s h))
       (Config CT e_r (SIGMA s'0 h'0)) ->
    e = dot 
    \/ (e_r = dot /\ multi_step_erasure_H (Config CT e (SIGMA s h))
       (Config CT dot (SIGMA s'0 h'0)) /\ e2 = dot) 
    \/ (exists e0, multi_step_erasure_H (Config CT e (SIGMA s h))
       (Config CT e0 (SIGMA s'0 h'0))  /\ e_r = (MethodCall e0 id0 e2))
    \/ (exists s'1 h'1, multi_step_erasure_H (Config CT e (SIGMA s h)) (Config CT dot (SIGMA s'1 h'1)) 
        /\ multi_step_erasure_H (Config CT (MethodCall dot id0 e2) (SIGMA s'1 h'1))
       (Config CT e_r (SIGMA s'0 h'0)) ).

  Proof. intros CT e e2 id0 s s_r h h_r e_r . intro H_erasure.
    remember (Config CT (MethodCall e id0 e2) (SIGMA s h)) as config.    remember (Config CT e_r (SIGMA s_r h_r))  as config_r.
    generalize dependent e. generalize dependent s. generalize dependent h. 
   generalize dependent e_r. generalize dependent s_r. generalize dependent h_r. generalize dependent e2.
    induction H_erasure; intros; inversion Heqconfig; inversion Heqconfig_r; subst. 
   + destruct H0. ++ subst. inversion H. left. auto. 
    ++ subst. inversion H. 
    +++ subst. right. right. left.  exists e'. split.  apply H_erasure_single_step; auto. auto.  
    +++ left. auto. +++ left. auto.  
   + subst. inversion H.
    ++ subst. induction sigma'. destruct IHH_erasure with e2 h_r s_r e_r h0 s0 e'; auto.
      +++ subst. inversion H_erasure. subst. ++++ destruct H9. +++++ subst.  inversion  H4. subst. 
        right. left. split; auto.  split; auto.  apply H_erasure_single_step; auto.
      +++++  subst.  right. right.  right. exists s0. exists h0. split; apply H_erasure_single_step; auto.
       ++++ subst. inversion H7. +++++ subst.  inversion H3. 
      +++++ subst. right. right.  right. exists s0. exists h0. split. apply H_erasure_single_step; auto. 
            apply H_erasure_multi_step with (MethodCall dot id0 e') sigma'; auto.
      +++++ subst. inversion H10. inversion H4. inversion H8. 
      +++ subst. destruct H1. ++++ destruct H1. destruct H3. right. subst. left. split. auto.  split; auto. 
         apply H_erasure_multi_step with e'  (SIGMA s0 h0); auto. 
      ++++ subst. destruct H1. +++++ destruct H1 as [e0]. destruct H1. subst. 
          right. right. left. exists e0.  split; auto. apply H_erasure_multi_step with e'  (SIGMA s0 h0); auto.
      +++++ destruct H1 as [s'1]. destruct H1 as [h'1].  destruct H1. subst. right. right. right. 
          exists s'1. exists h'1.  split.  apply H_erasure_multi_step with e'  (SIGMA s0 h0); auto.
          auto. 
      ++ subst. left. auto. ++ left. auto. 
Qed. 

(*Field Write context erasure*)
Lemma context_erasure_field_write_obj : forall CT e e2 f s s'0 h h'0 e_r, 
   multi_step_erasure_H (Config CT (FieldWrite e f e2) (SIGMA s h))
       (Config CT e_r (SIGMA s'0 h'0)) ->
    e = dot 
    \/ (e_r = dot /\ multi_step_erasure_H (Config CT e (SIGMA s h))
       (Config CT dot (SIGMA s'0 h'0)) /\ e2 = dot) 
    \/ (exists e0, multi_step_erasure_H (Config CT e (SIGMA s h))
       (Config CT e0 (SIGMA s'0 h'0))  
        /\ flow_to (current_label (SIGMA s'0 h'0)) L_Label = true 
        /\ e_r = (FieldWrite e0 f e2))
    \/ (exists s'1 h'1, multi_step_erasure_H (Config CT e (SIGMA s h)) (Config CT dot (SIGMA s'1 h'1)) 
        /\ flow_to (current_label (SIGMA s'1 h'1)) L_Label = false 
        /\ multi_step_erasure_H (Config CT (FieldWrite dot f e2) (SIGMA s'1 h'1))
       (Config CT e_r (SIGMA s'0 h'0)) ).

  Proof. intros CT e e2 id0 s s_r h h_r e_r . intro H_erasure.
    remember (Config CT (FieldWrite e id0 e2) (SIGMA s h)) as config.    remember (Config CT e_r (SIGMA s_r h_r))  as config_r.
    generalize dependent e. generalize dependent s. generalize dependent h. 
   generalize dependent e_r. generalize dependent s_r. generalize dependent h_r. generalize dependent e2.
    induction H_erasure; intros; inversion Heqconfig; inversion Heqconfig_r; subst. 
   + destruct H0. ++ subst. inversion H. left. auto. 
    ++ subst. inversion H. 
    +++ subst. right. right. left.  exists e1'. split.  apply H_erasure_single_step; auto. auto.  
    +++ left. auto. +++ left. auto.  
   + subst. inversion H.
    ++ subst. induction sigma'. destruct IHH_erasure with e2 h_r s_r e_r h0 s0 e1'; auto.
      +++ subst. inversion H_erasure. subst. ++++ destruct H9. +++++ subst.  inversion  H4. subst. 
        right. left. split; auto.  split; auto.  apply H_erasure_single_step; auto.
      +++++  subst.  right. right.  right. exists s0. exists h0. split.  apply H_erasure_single_step; auto.
      split. auto. apply H_erasure_single_step; auto.
       ++++ subst. inversion H7. +++++ subst.  inversion H3. 
      +++++ subst. right. right.  right. exists s0. exists h0. split. apply H_erasure_single_step; auto. 
            split. auto. apply H_erasure_multi_step with (FieldWrite dot id0 e2') sigma'; auto.
      +++++ subst. inversion H10. inversion H4. inversion H8. 
      +++ subst. destruct H1. ++++ destruct H1. destruct H3. right. subst. left. split. auto.  split; auto. 
         apply H_erasure_multi_step with e1'  (SIGMA s0 h0); auto. 
      ++++ subst. destruct H1. +++++ destruct H1 as [e0]. destruct H1. subst. 
          right. right. left. exists e0.  split; auto. apply H_erasure_multi_step with e1'  (SIGMA s0 h0); auto.
      +++++ destruct H1 as [s'1]. destruct H1 as [h'1].  destruct H1. subst. right. right. right. 
          exists s'1. exists h'1.  split.  apply H_erasure_multi_step with e1'  (SIGMA s0 h0); auto.
          auto. 
      ++ subst. left. auto. ++ left. auto. 
Qed. 

Lemma field_write_context_erasure2 : forall CT f e s h s'0 h'0, 
    multi_step_erasure_H (Config CT (FieldWrite dot f e) (SIGMA s h))
       (Config CT dot (SIGMA s'0 h'0)) ->
    (e = dot \/ (multi_step_erasure_H (Config CT e (SIGMA s h))  (Config CT dot (SIGMA s'0 h'0))) ).
Proof. intros CT id0 e s h s'0 h'0.
    intro H_erasure. 
    remember  (Config CT (FieldWrite dot id0 e) (SIGMA s h)) as config.    remember (Config CT dot (SIGMA s'0 h'0)) as config'.
   generalize dependent e. generalize dependent s. generalize dependent h. 
   generalize dependent s'0. generalize dependent h'0. induction H_erasure. 
   + intros. inversion Heqconfig'. inversion Heqconfig. subst. inversion H. subst.  left. auto. 
   + intros. inversion Heqconfig'. inversion Heqconfig. subst. inversion H. subst. ++ inversion H2. 
      ++  subst. induction sigma'. destruct IHH_erasure with h'0 s'0 h0 s0 e2'; auto. 
      +++ subst.  inversion H_erasure.  subst.  inversion H4. subst. ++++  
            right.  apply  H_erasure_single_step; auto. ++++  subst. inversion H7.  
          subst. inversion H3. inversion H3. subst. inversion H10. inversion H4. inversion H8.
        +++  right. apply H_erasure_multi_step with e2' (SIGMA s0 h0); auto. 
      ++ left. auto. 
Qed. 


(*Sequence context erasure*)
Lemma context_erasure_sequence : forall CT e e2 s s'0 h h'0 e_r, 
   multi_step_erasure_H (Config CT (Sequence e e2) (SIGMA s h))
       (Config CT e_r (SIGMA s'0 h'0)) ->
    e = dot 
    \/ (e_r = dot /\ multi_step_erasure_H (Config CT e (SIGMA s h))
       (Config CT dot (SIGMA s'0 h'0)) /\ e2 = dot) 
    \/ (exists e0, multi_step_erasure_H (Config CT e (SIGMA s h))
       (Config CT e0 (SIGMA s'0 h'0))  /\ e_r = (Sequence e0 e2))
    \/ (exists s'1 h'1, multi_step_erasure_H (Config CT e (SIGMA s h)) (Config CT dot (SIGMA s'1 h'1)) 
        /\ multi_step_erasure_H (Config CT (Sequence dot e2) (SIGMA s'1 h'1))
       (Config CT e_r (SIGMA s'0 h'0)) ).

  Proof. intros CT e e2 s s_r h h_r e_r. intro H_erasure.
    remember (Config CT (Sequence e e2) (SIGMA s h)) as config.    remember (Config CT e_r (SIGMA s_r h_r))  as config_r.
    generalize dependent e. generalize dependent s. generalize dependent h. 
   generalize dependent e_r. generalize dependent s_r. generalize dependent h_r. generalize dependent e2.
    induction H_erasure; intros; inversion Heqconfig; inversion Heqconfig_r; subst. 
   + destruct H0. ++ subst. inversion H. left. auto. 
    ++ subst. inversion H. 
    +++ subst. right. right. left.  exists s1'. split.  apply H_erasure_single_step; auto. auto.  
    +++ left. auto.
   + subst. inversion H.
    ++ subst. induction sigma'. destruct IHH_erasure with e2 h_r s_r e_r h0 s0 s1'; auto.
      +++ subst. inversion H_erasure. subst. ++++ destruct H9. +++++ subst.  inversion  H4. subst. 
        right. right.  right. exists s0. exists h0. split; auto.  apply H_erasure_single_step; auto.
      +++++  subst.  right. right.  right. exists s0. exists h0. split; apply H_erasure_single_step; auto.
       ++++ subst. inversion H7. +++++ subst.  inversion H3. 
      +++++ subst. right. right.  right. exists s0. exists h0. split. apply H_erasure_single_step; auto. 
            apply H_erasure_multi_step with t' sigma'; auto.
      +++ subst. destruct H1. ++++ destruct H1. destruct H3. right. subst. left. split. auto.  split; auto. 
         apply H_erasure_multi_step with s1'  (SIGMA s0 h0); auto. 
      ++++ subst. destruct H1. +++++ destruct H1 as [e0]. destruct H1. subst. 
          right. right. left. exists e0.  split; auto. apply H_erasure_multi_step with s1'  (SIGMA s0 h0); auto.
      +++++ destruct H1 as [s'1]. destruct H1 as [h'1].  destruct H1. subst. right. right. right. 
          exists s'1. exists h'1.  split.  apply H_erasure_multi_step with s1'  (SIGMA s0 h0); auto.
          auto. 
      ++ subst. left. auto.
Qed. 



Lemma dot_erasure_preverve_high_context : forall s h s' h' CT e e' s_r h_r ,
(*    forall T, has_type CT empty_context h e T -> *)
    Config CT e (SIGMA s h) ==> Config CT e' (SIGMA s' h') ->
    flow_to (current_label (SIGMA s h)) L_Label = false ->
    Config CT e (SIGMA s h) =e=> Config CT dot (SIGMA s_r h_r) ->
    flow_to (current_label (SIGMA s' h')) L_Label = false.
Proof. intros s h s' h' CT e e' s_r h_r . intro H_reduction.
    intro H_context. intro H_erasure. inversion H_erasure. rewrite H_context in H2. inversion H2.
    subst. remember (Config CT e (SIGMA s h)) as config.    remember (Config CT e' (SIGMA s' h')) as config'.
   generalize dependent e. generalize dependent s. generalize dependent h. 
   generalize dependent e'. generalize dependent s'. generalize dependent h'. 
  generalize dependent s_r. generalize dependent h_r. 
  generalize dependent s'0. generalize dependent h'0.  
induction H_reduction; intros; inversion Heqconfig; inversion Heqconfig'; subst; auto.
    +inversion H9. inversion H12.  subst. auto.
    + assert (e = dot \/ (dot = dot /\ multi_step_erasure_H (Config CT e (SIGMA s h))
       (Config CT dot (SIGMA s'0 h'0))) \/ (exists e0, multi_step_erasure_H (Config CT e (SIGMA s h))
       (Config CT e0 (SIGMA s'0 h'0))  /\ dot = (FieldAccess e0 f))).
       apply context_erasure_field_access; auto.  destruct H. subst.  inversion H_reduction.
        destruct H. destruct H. destruct IHH_reduction with h'0 s'0 h_r s_r h' s' e' h s e ; auto. 
      apply erasure_H_context with s'0 h'0; auto. 
      destruct H. destruct H. inversion H0.

    + (*(FieldAccess (ObjId o) fname) *) 
        subst. rewrite <- H14. inversion H11. subst. 
        (*dealing with updating labels*)
          unfold current_label in H_context. unfold get_stack in H_context.
          unfold current_label. unfold get_stack.   
          induction s0.     unfold get_current_label in H_context. unfold flow_to in H_context. unfold L_Label in H_context.
          unfold subset in H_context. inversion H_context.
          induction a. unfold update_current_label. 
          unfold get_current_label. unfold get_stack_label. 
          unfold current_label in H_context.       unfold get_current_label in H_context. 
          unfold get_stack_label in H_context.
          assert (  flow_to (join_label lb l0)  L_Label = false).
          apply flow_join_label with l0 lb; auto. auto. 
     + (* MethodCall e' id0 e2 *) assert (e = dot 
            \/ (dot = dot /\ multi_step_erasure_H (Config CT e (SIGMA s h))
               (Config CT dot (SIGMA s'0 h'0)) /\ e2 = dot) 
            \/ (exists e0, multi_step_erasure_H (Config CT e (SIGMA s h))
               (Config CT e0 (SIGMA s'0 h'0))  /\ dot = (MethodCall e0 id0 e2))
            \/ (exists s'1 h'1, multi_step_erasure_H (Config CT e (SIGMA s h)) (Config CT dot (SIGMA s'1 h'1)) 
                /\ multi_step_erasure_H (Config CT (MethodCall dot id0 e2) (SIGMA s'1 h'1))
               (Config CT dot (SIGMA s'0 h'0)) )).
        apply context_erasure_method_call_obj; auto.  
        destruct H. ++  subst. inversion H_reduction. ++ destruct H. 
        +++  destruct H. destruct H0. subst. 
        destruct IHH_reduction with h'0 s'0 h_r s_r h' s' e' h s e ; auto. 
        apply erasure_H_context with s'0 h'0; auto. 
        +++ destruct H. destruct H as [e0]. destruct H. inversion H0.
        destruct H as [s'1].         destruct H as [h'1]. destruct H.
        remember (erasure_sigma_fun (SIGMA s'1 h'1)) as sigma''. induction sigma''. 
        destruct IHH_reduction with h'1 s'1 h0 s0 h' s' e' h s e ; auto. 
        apply erasure_H_context with s'1 h'1; auto. 
     + (* MethodCall v id0 e *) 
          assert (v = dot 
            \/ (dot = dot /\ multi_step_erasure_H (Config CT v (SIGMA s h))
               (Config CT dot (SIGMA s'0 h'0)) /\ e = dot) 
            \/ (exists e0, multi_step_erasure_H (Config CT v (SIGMA s h))
               (Config CT e0 (SIGMA s'0 h'0))  /\ dot = (MethodCall e0 id0 e))
            \/ (exists s'1 h'1, multi_step_erasure_H (Config CT v (SIGMA s h)) (Config CT dot (SIGMA s'1 h'1)) 
                /\ multi_step_erasure_H (Config CT (MethodCall dot id0 e) (SIGMA s'1 h'1))
               (Config CT dot (SIGMA s'0 h'0)) )).
        apply context_erasure_method_call_obj; auto.
        destruct H1. subst. ++ inversion H_erasure. subst. unfold erasure_L_fun in H13. inversion H13. subst. 
        assert (e = dot \/ (multi_step_erasure_H (Config CT e (SIGMA s h))  (Config CT dot (SIGMA s'1 h'1))) ).
        apply method_call_context_erasure2 with id0; auto. destruct H1. subst. inversion H_reduction.
        destruct IHH_reduction with h'1 s'1 h_r s_r h' s' e' h s e ; auto. apply erasure_H_context with s'1 h'1; auto.  
         ++destruct H1.  destruct H1.  +++ destruct H3. subst. inversion H_reduction. 
          +++ destruct H1.  ++++ destruct H1 as [e0]. destruct H1. inversion H3.  
          ++++ destruct H1 as [s'1]. destruct H1 as [h'1]. destruct H1. inversion H1. subst.  
          assert (Config CT v (SIGMA s h) =eH=> Config CT dot (SIGMA s h)). apply value_erasure_to_dot; auto.
        intro contra. subst. inversion H9.  assert (dot = dot /\ (SIGMA s'1 h'1) = (SIGMA s h)). apply erasure_H_deterministic with CT v (SIGMA s h); auto.
        destruct H5. subst.  inversion H10. subst. 
        assert (e = dot \/ (multi_step_erasure_H (Config CT e (SIGMA s h))  (Config CT dot (SIGMA s'0 h'0))) ).
        apply method_call_context_erasure2 with id0; auto. destruct H11. subst. inversion H_reduction.
        destruct IHH_reduction with h'0 s'0 h_r s_r h' s' e' h s e ; auto. apply erasure_H_context with s'0 h'0; auto.
        subst.   
        assert (Config CT v (SIGMA s h) =eH=> Config CT dot (SIGMA s h)). apply value_erasure_to_dot; auto.
        intro contra. subst. inversion H11.  assert (t' = dot /\ sigma' = (SIGMA s h)). apply erasure_H_deterministic with CT v (SIGMA s h); auto.
        destruct H5. subst. inversion H14. inversion H10. inversion H15. 
      +(*  (MethodCall (ObjId o) meth v) *) 
      inversion H14.  subst. rewrite <- H17. unfold get_heap. unfold current_label. unfold get_stack.
      remember (get_current_label s0) as lbl.  unfold get_current_label.
          unfold get_stack_label. rewrite Heqlbl. unfold current_label in H_context. unfold get_stack in H_context.  auto. 

      +(* (MethodCall (ObjId o) meth (unlabelOpaque (v_opa_l v lb))) *)
      inversion H14.  subst. rewrite <- H17. unfold get_heap. unfold current_label. unfold get_stack.
      remember (get_current_label s0) as lbl.  unfold get_current_label.
          unfold get_stack_label. rewrite Heqlbl. unfold current_label in H_context. unfold get_stack in H_context.  auto. 
          apply flow_join_label with (get_current_label s0) lb; auto.

      + (* (NewExp cls_name)*) inversion H13. subst. inversion H16. subst.
         induction s'. unfold current_label in H_context. unfold get_stack in H_context. 
         unfold get_current_label in H_context. unfold flow_to in H_context. unfold L_Label in H_context.
    unfold subset in H_context. inversion H_context. 
        induction a. unfold current_label. unfold get_stack. auto.
      + (*(labelData e lb) *) inversion H_erasure. subst. rewrite H3 in H_context. inversion H_context. subst.

Lemma label_data_context_erasure_dot : forall CT e lb sigma sigma',
    multi_step_erasure_H (Config CT (labelData e lb) sigma)
        (Config CT dot sigma') ->
   e = dot \/ multi_step_erasure_H (Config CT  e sigma)
        (Config CT dot sigma').
Proof.  intros CT e lb sigma sigma'. intro H_erasure. 
  remember (Config CT (labelData e lb) sigma) as config. 
  remember (Config CT dot sigma') as config'.  
   generalize dependent e. generalize dependent sigma. generalize dependent sigma'.
  induction H_erasure.
  - intros. inversion Heqconfig. inversion Heqconfig'. subst. inversion H. subst. left. auto.
  - intros. inversion Heqconfig. inversion Heqconfig'. subst. inversion H. subst. 
     destruct IHH_erasure with sigma'0 sigma' e'; auto. subst. right. 
      apply H_erasure_single_step; auto. inversion H_erasure. subst. inversion H4. subst.
      auto. subst. inversion H7. inversion H3.  subst. inversion H10. inversion H4. 
      subst. inversion H8. right.       apply H_erasure_multi_step with e' sigma'; auto. 
      left. auto.
Qed. 
    assert (e = dot \/ multi_step_erasure_H (Config CT  e (SIGMA s h))
        (Config CT dot  (SIGMA s'1 h'1))).     
apply label_data_context_erasure_dot with lb; auto. destruct H.
++ subst. inversion H_reduction.
++ inversion H11. subst. inversion H5. subst. inversion H. inversion H6. subst. inversion H10.
      subst.
        destruct IHH_reduction with h'1 s'1 h_r s_r h' s' e' h s e ; auto. apply erasure_H_context with s'1 h'1; auto.
+ (*(v_l v lb)*) inversion H9. subst. auto.
+ (*(unlabel e) *) inversion H_erasure.  rewrite H3 in H_context. inversion H_context. subst.

Lemma unlabel_context_dot : forall CT e sigma sigma', 
    multi_step_erasure_H (Config CT (unlabel e) sigma)
        (Config CT dot sigma') ->
   e = dot \/ multi_step_erasure_H (Config CT e sigma)
        (Config CT dot sigma').
Proof.  intros CT e sigma sigma'. intro H_erasure. 
  remember (Config CT (unlabel e) sigma) as config. 
  remember (Config CT dot sigma') as config'.  
   generalize dependent e. generalize dependent sigma. generalize dependent sigma'.
  induction H_erasure.
  - intros. inversion Heqconfig. inversion Heqconfig'. subst. inversion H. subst. left. auto.
  - intros. inversion Heqconfig. inversion Heqconfig'. subst. inversion H. subst. 
     destruct IHH_erasure with sigma'0 sigma' e'; auto. subst. right. 
      apply H_erasure_single_step; auto. inversion H_erasure. subst. inversion H4. subst.
      auto. subst. inversion H7. inversion H3.  subst. inversion H10. inversion H4. 
      subst. inversion H8. right.       apply H_erasure_multi_step with e' sigma'; auto. 
      left. auto.
Qed.

    assert (e = dot \/ multi_step_erasure_H (Config CT  e (SIGMA s h))
        (Config CT dot  (SIGMA s'1 h'1))).     
apply unlabel_context_dot; auto. destruct H.
++ subst. inversion H_reduction.
++ inversion H11. subst. inversion H5. subst. inversion H. inversion H6. subst. inversion H10.
      subst.
        destruct IHH_reduction with h'1 s'1 h_r s_r h' s' e' h s e ; auto. apply erasure_H_context with s'1 h'1; auto.

+  (*(unlabel (v_l e' lb))*) inversion H10. subst. rewrite <- H13. unfold get_heap. unfold current_label. unfold get_stack.
      induction s0.  unfold current_label in H_context. unfold get_stack in H_context. 
         unfold get_current_label in H_context. unfold flow_to in H_context. unfold L_Label in H_context.
    unfold subset in H_context. inversion H_context. 
        induction a. unfold current_label. unfold get_stack. unfold update_current_label.
        remember (get_current_label (Labeled_frame l0 s :: s0)) as lbl. unfold get_current_label.
        unfold get_stack_label. apply flow_join_label with lbl lb; auto. rewrite Heqlbl. auto.

+ (*labelof *)
inversion H_erasure.  rewrite H3 in H_context. inversion H_context. subst.

Lemma labelOf_context_dot : forall CT e sigma sigma', 
    multi_step_erasure_H (Config CT (labelOf e) sigma)
        (Config CT dot sigma') ->
   e = dot \/ multi_step_erasure_H (Config CT e sigma)
        (Config CT dot sigma').
Proof.  intros CT e sigma sigma'. intro H_erasure. 
  remember (Config CT (labelOf e) sigma) as config. 
  remember (Config CT dot sigma') as config'.  
   generalize dependent e. generalize dependent sigma. generalize dependent sigma'.
  induction H_erasure.
  - intros. inversion Heqconfig. inversion Heqconfig'. subst. inversion H. subst. left. auto.
  - intros. inversion Heqconfig. inversion Heqconfig'. subst. inversion H. subst. 
     destruct IHH_erasure with sigma'0 sigma' e'; auto. subst. right. 
      apply H_erasure_single_step; auto. inversion H_erasure. subst. inversion H4. subst.
      auto. subst. inversion H7. inversion H3.  subst. inversion H10. inversion H4. 
      subst. inversion H8. right.       apply H_erasure_multi_step with e' sigma'; auto. 
      left. auto.
Qed.

    assert (e = dot \/ multi_step_erasure_H (Config CT  e (SIGMA s h))
        (Config CT dot  (SIGMA s'1 h'1))).     
apply labelOf_context_dot; auto. destruct H.
    ++ subst. inversion H_reduction.
    ++ inversion H11. subst. inversion H5. subst. inversion H. inversion H6. subst. inversion H10.
          subst.
            destruct IHH_reduction with h'1 s'1 h_r s_r h' s' e' h s e ; auto. apply erasure_H_context with s'1 h'1; auto.

+ (*(labelOf (v_l v lb)) *)inversion H6. subst. auto.

+ (*(unlabelOpaque e) *)
inversion H_erasure.  rewrite H3 in H_context. inversion H_context. subst.

Lemma unlabelOpaque_context_dot : forall CT e sigma sigma', 
    multi_step_erasure_H (Config CT (unlabelOpaque e) sigma)
        (Config CT dot sigma') ->
   e = dot \/ multi_step_erasure_H (Config CT e sigma)
        (Config CT dot sigma').
Proof.  intros CT e sigma sigma'. intro H_erasure. 
  remember (Config CT (unlabelOpaque e) sigma) as config. 
  remember (Config CT dot sigma') as config'.  
   generalize dependent e. generalize dependent sigma. generalize dependent sigma'.
  induction H_erasure.
  - intros. inversion Heqconfig. inversion Heqconfig'. subst. inversion H. subst. left. auto.
  - intros. inversion Heqconfig. inversion Heqconfig'. subst. inversion H. subst. 
     destruct IHH_erasure with sigma'0 sigma' e'; auto. subst. right. 
      apply H_erasure_single_step; auto. inversion H_erasure. subst. inversion H4. subst.
      auto. subst. inversion H7. inversion H3.  subst. inversion H10. inversion H4. 
      subst. inversion H8. right.       apply H_erasure_multi_step with e' sigma'; auto. 
      left. auto.
Qed.

    assert (e = dot \/ multi_step_erasure_H (Config CT  e (SIGMA s h))
            (Config CT dot  (SIGMA s'1 h'1))).     
    apply unlabelOpaque_context_dot; auto. destruct H.
    ++ subst. inversion H_reduction.
    ++ inversion H11. subst. inversion H5. subst. inversion H. inversion H6. subst. inversion H10.
          subst.
            destruct IHH_reduction with h'1 s'1 h_r s_r h' s' e' h s e ; auto. apply erasure_H_context with s'1 h'1; auto.

+ inversion H9. subst. rewrite <- H12. unfold get_heap. unfold current_label. unfold get_stack.
      induction s0.  unfold current_label in H_context. unfold get_stack in H_context. 
         unfold get_current_label in H_context. unfold flow_to in H_context. unfold L_Label in H_context.
    unfold subset in H_context. inversion H_context. 
        induction a. unfold current_label. unfold get_stack. unfold update_current_label.
        remember (get_current_label (Labeled_frame l0 s :: s0)) as lbl. unfold get_current_label.
        unfold get_stack_label. apply flow_join_label with lbl lb; auto. rewrite Heqlbl. auto.

+
inversion H_erasure.   rewrite H4 in H_context. inversion H_context. subst.

Lemma opaque_call_context_dot : forall CT e sigma sigma', 
    multi_step_erasure_H (Config CT (opaqueCall e) sigma)
        (Config CT dot sigma') ->
   e = dot \/ multi_step_erasure_H (Config CT e sigma)
        (Config CT dot sigma').
Proof.  intros CT e sigma sigma'. intro H_erasure. 
  remember (Config CT (opaqueCall e) sigma) as config. 
  remember (Config CT dot sigma') as config'.  
   generalize dependent e. generalize dependent sigma. generalize dependent sigma'.
  induction H_erasure.
  - intros. inversion Heqconfig. inversion Heqconfig'. subst. inversion H. subst. left. auto.
  - intros. inversion Heqconfig. inversion Heqconfig'. subst. inversion H. subst. 
     destruct IHH_erasure with sigma'0 sigma' e'; auto. subst. right. 
      apply H_erasure_single_step; auto. inversion H_erasure. subst. inversion H4. subst.
      auto. subst. inversion H7. inversion H13.  subst. inversion H11. inversion H4. 
      subst. inversion H9. right.       apply H_erasure_multi_step with e' sigma'; auto. 
      left. auto.
      subst. right. inversion H_erasure. subst. inversion H3. subst. apply H_erasure_single_step; auto.
      apply Er_return_H with (lsf :: s')  s' h lsf; auto. subst. 
      inversion H6. subst. inversion H10. inversion H3. inversion H7. 
Qed.

    assert (e = dot \/ multi_step_erasure_H (Config CT  e (SIGMA s h))
            (Config CT dot  (SIGMA s'1 h'1))).     
    apply opaque_call_context_dot; auto. destruct H0.
    ++ subst. inversion H_reduction.
    ++ inversion H12. subst. inversion H6. subst. inversion H0. inversion H9. subst. inversion H11.
          subst.
            destruct IHH_reduction with h'1 s'1 h_r s_r h' s' e' h s e ; auto. apply erasure_H_context with s'1 h'1; auto.

+ inversion H_erasure.   rewrite H3 in H_context. inversion H_context. subst.


Lemma opaque_call_context_return_dot : forall CT e sigma sigma', 
    multi_step_erasure_H (Config CT (opaqueCall (Return e)) sigma)
        (Config CT dot sigma') ->
   e= dot \/ (exists sigma0,  multi_step_erasure_H (Config CT e sigma)
        (Config CT dot sigma0) /\ multi_step_erasure_H (Config CT (opaqueCall (Return dot)) sigma0) 
        (Config CT dot sigma')).
Proof.  intros CT e sigma sigma'. intro H_erasure. 
  remember (Config CT (opaqueCall (Return e)) sigma) as config. 
  remember (Config CT dot sigma') as config'.  
   generalize dependent e. generalize dependent sigma. generalize dependent sigma'.
  induction H_erasure.
  - intros. inversion Heqconfig. inversion Heqconfig'. subst. inversion H. 
  - intros. inversion Heqconfig. inversion Heqconfig'. subst. inversion H. subst. 
      inversion H8.  subst. 
     right.  destruct IHH_erasure with sigma'0 sigma' e'0; auto.  subst. auto.
      exists sigma'. split.    apply H_erasure_single_step; auto. auto.  
     destruct H1 as [sigma''].
     exists sigma''. split.  apply H_erasure_multi_step with e'0 sigma'; auto. apply H1. apply H1.
    left. auto.  left. auto. 
Qed.

   assert (   e= dot \/ (exists sigma0,  multi_step_erasure_H (Config CT e (SIGMA s h))
        (Config CT dot sigma0) /\ multi_step_erasure_H (Config CT (opaqueCall (Return dot)) sigma0) 
        (Config CT dot (SIGMA s'1 h'1)))).
    apply opaque_call_context_return_dot; auto. destruct H.
    ++ subst. inversion H_reduction.
    ++ destruct H as [sigma0]. destruct H. 

 inversion H0. subst.  inversion H6. subst. inversion H10.  subst.  intuition. subst. 
  remember (erasure_sigma_fun (SIGMA (lsf :: s'2) h0)) as sigma''. induction sigma''.
    destruct IHH_reduction with h0 (lsf :: s'2)  h1 s0 h' s' e' h s e ; auto. apply erasure_H_context with (lsf :: s'2) h0; auto.

+ (* v_opa_l *)
   inversion H10. subst. auto. 

+ (* opaqueCall (Return v)*)
   inversion H14. inversion H11. subst. inversion H_erasure. subst. unfold  erasure_L_fun in H15. inversion H15. 
   subst. inversion H15. subst.  inversion H2. subst. inversion H9.  subst.  inversion H19. 
        assert (Config CT v (SIGMA (lsf :: s'1) h0) =eH=> Config CT dot  (SIGMA (lsf :: s'1) h0)). apply value_erasure_to_dot; auto.
        intro contra. subst. intuition.
        assert (e'0 = dot /\ sigma' = (SIGMA (lsf :: s'1) h0)). apply erasure_H_deterministic with CT v (SIGMA (lsf :: s'1) h0); auto.
        destruct H22. subst.  inversion H17. subst. inversion H10. subst. inversion H20. subst. intuition. 
        subst. inversion H22. subst. auto.
        subst.  inversion H20. subst. auto.
        subst. inversion H18. subst. auto. 

+ (*  (Assignment id0 e)  *)
inversion H_erasure.  rewrite H3 in H_context. inversion H_context. subst.
Lemma assignment_context_dot : forall CT e sigma sigma' id0, 
    multi_step_erasure_H (Config CT (Assignment id0 e)  sigma)
        (Config CT dot sigma') ->
   e = dot \/ multi_step_erasure_H (Config CT e sigma)
        (Config CT dot sigma').
Proof.  intros CT e sigma sigma' id0. intro H_erasure. 
  remember (Config CT (Assignment id0 e)  sigma) as config. 
  remember (Config CT dot sigma') as config'.  
   generalize dependent e. generalize dependent sigma. generalize dependent sigma'.
  induction H_erasure.
  - intros. inversion Heqconfig. inversion Heqconfig'. subst. inversion H. subst. left. auto.
  - intros. inversion Heqconfig. inversion Heqconfig'. subst. inversion H. subst. 
     destruct IHH_erasure with sigma'0 sigma' e'; auto. subst. right. 
      apply H_erasure_single_step; auto. inversion H_erasure. subst. inversion H4. subst.
      auto. subst. inversion H7. inversion H3.  subst. inversion H10. inversion H4. 
      subst. inversion H8. right.       apply H_erasure_multi_step with e' sigma'; auto. 
      left. auto.
Qed.

    assert (e = dot \/ multi_step_erasure_H (Config CT  e (SIGMA s h))
            (Config CT dot  (SIGMA s'1 h'1))).     
    apply assignment_context_dot with id0; auto. destruct H.
    ++ subst. inversion H_reduction.
    ++ inversion H11. subst. inversion H5. subst. inversion H. inversion H6. subst. inversion H10.
          subst.
            destruct IHH_reduction with h'1 s'1 h_r s_r h' s' e' h s e ; auto. apply erasure_H_context with s'1 h'1; auto.

+ (* Assignment id0 v *) inversion H9. rewrite <- H12.  subst. auto.
unfold get_heap. unfold current_label. unfold get_stack.
      induction s0.  unfold current_label in H_context. unfold get_stack in H_context. 
         unfold get_current_label in H_context. unfold flow_to in H_context. unfold L_Label in H_context.
    unfold subset in H_context. inversion H_context. 
        induction a. unfold current_label. unfold get_stack. unfold update_current_label.
        unfold update_stack_top.         unfold labeled_frame_update. unfold get_current_label.
        unfold get_stack_label. auto. 

+ (* FieldWrite e1 f e2 *)
     inversion H_erasure.   rewrite H3 in H_context. inversion H_context. subst. 
    assert (e1 = dot 
    \/ (dot = dot /\ multi_step_erasure_H (Config CT e1 (SIGMA s h))
       (Config CT dot (SIGMA s'0 h'0)) /\ e2 = dot) 
    \/ (exists e0, multi_step_erasure_H (Config CT e1 (SIGMA s h))
       (Config CT e0 (SIGMA s'0 h'0))  
/\ flow_to (current_label (SIGMA s'0 h'0)) L_Label = true 
/\ dot = (FieldWrite e0 f e2))
    \/ (exists s'1 h'1, multi_step_erasure_H (Config CT e1 (SIGMA s h)) (Config CT dot (SIGMA s'1 h'1)) 
        /\ flow_to (current_label (SIGMA s'1 h'1)) L_Label = false 
      /\ multi_step_erasure_H (Config CT (FieldWrite dot f e2) (SIGMA s'1 h'1))
       (Config CT dot (SIGMA s'0 h'0)) )).
        apply context_erasure_field_write_obj; auto.  
        destruct H. ++  subst. inversion H_reduction. ++ destruct H. 
        +++  destruct H. destruct H0. subst. 
        destruct IHH_reduction with h'0 s'0 h_r s_r h' s' e1' h s e1 ; auto. 
        apply erasure_H_context with s'0 h'0; auto. 
        +++ destruct H. destruct H as [e0]. destruct H. destruct H0. inversion H1.
        destruct H as [s'2].         destruct H as [h'2]. destruct H.
        remember (erasure_sigma_fun (SIGMA s'2 h'2)) as sigma''. induction sigma''. 
        destruct IHH_reduction with h'2 s'2 h0 s0 h' s' e1' h s e1 ; auto. 
        apply erasure_H_context with s'2 h'2; auto. 

+  (* FieldWrite v f e2 *) 
inversion H_erasure.   rewrite H5 in H_context. inversion H_context. subst.
    assert (v = dot 
        \/ (dot = dot /\ multi_step_erasure_H (Config CT v (SIGMA s h))
           (Config CT dot (SIGMA s'0 h'0)) /\ e2 = dot) 
        \/ (exists e0, multi_step_erasure_H (Config CT v (SIGMA s h))
           (Config CT e0 (SIGMA s'0 h'0))  
          /\ flow_to (current_label (SIGMA s'0 h'0)) L_Label = true 
          /\ dot = (FieldWrite e0 f e2))
        \/ (exists s'1 h'1, multi_step_erasure_H (Config CT v (SIGMA s h)) (Config CT dot (SIGMA s'1 h'1)) 
            /\ flow_to (current_label (SIGMA s'1 h'1)) L_Label = false 
            /\ multi_step_erasure_H (Config CT (FieldWrite dot f e2) (SIGMA s'1 h'1))
           (Config CT dot (SIGMA s'0 h'0)) )).
            apply context_erasure_field_write_obj; auto.  
        destruct H1. subst. ++ inversion H_erasure. subst. unfold erasure_L_fun in H16. inversion H16. subst. 
        assert (e2 = dot \/ (multi_step_erasure_H (Config CT e2 (SIGMA s h))  (Config CT dot (SIGMA s'1 h'1))) ).
        apply field_write_context_erasure2 with f; auto. destruct H1. subst. inversion H_reduction.
        destruct IHH_reduction with h'1 s'1 h_r s_r h' s' e2' h s e2 ; auto. apply erasure_H_context with s'1 h'1; auto.  
         ++destruct H1.  destruct H1.  +++ destruct H3. subst. inversion H_reduction. 
          +++ destruct H1.  ++++ destruct H1 as [e0]. destruct H1. destruct H3. inversion H4.
          ++++ destruct H1 as [s'2]. destruct H1 as [h'2]. destruct H1. inversion H1. subst.  
          assert (Config CT v (SIGMA s h) =eH=> Config CT dot (SIGMA s h)). apply value_erasure_to_dot; auto.
        intro contra. subst. inversion H10.  assert (dot = dot /\ (SIGMA s'2 h'2) = (SIGMA s h)). apply erasure_H_deterministic with CT v (SIGMA s h); auto.
        destruct H9. subst.  inversion H11. subst. 
        assert (e2 = dot \/ (multi_step_erasure_H (Config CT e2 (SIGMA s h))  (Config CT dot (SIGMA s'0 h'0))) ).
        apply field_write_context_erasure2 with f; auto. destruct H3. auto.  destruct H12. subst. inversion H_reduction.
        destruct IHH_reduction with h'0 s'0 h_r s_r h' s' e2' h s e2 ; auto. apply erasure_H_context with s'0 h'0; auto.
        subst.   
        assert (Config CT v (SIGMA s h) =eH=> Config CT dot (SIGMA s h)). apply value_erasure_to_dot; auto.
        intro contra. subst. inversion H12.  assert (t' = dot /\ sigma' = (SIGMA s h)). apply erasure_H_deterministic with CT v (SIGMA s h); auto.
        destruct H9. subst. inversion H17. inversion H11. inversion H18.  


+ (* FieldWrite (ObjId o) f v *)
  rewrite <- H16. 
    unfold get_heap. unfold current_label. unfold get_stack.
      induction s0.  unfold current_label in H_context. unfold get_stack in H_context. 
         unfold get_current_label in H_context. unfold flow_to in H_context. unfold L_Label in H_context.
    unfold subset in H_context. inversion H_context. 
        induction a. unfold current_label. unfold get_stack. inversion H13. subst. auto.

+ (* FieldWrite (ObjId o) f (unlabelOpaque (v_opa_l v lb)) *)
  rewrite <- H16. 
    unfold get_heap. unfold current_label. unfold get_stack.
      induction s0.  unfold current_label in H_context. unfold get_stack in H_context. 
         unfold get_current_label in H_context. unfold flow_to in H_context. unfold L_Label in H_context.
    unfold subset in H_context. inversion H_context. 
        induction a. unfold current_label. unfold get_stack. inversion H13. subst. auto.

+  (* Return e *) 
 inversion H_erasure.   rewrite H3 in H_context. inversion H_context. subst.
  Lemma return_context_return_dot : forall CT e sigma sigma', 
      multi_step_erasure_H (Config CT  (Return e) sigma)
          (Config CT dot sigma') ->
     e= dot \/ (exists sigma0,  multi_step_erasure_H (Config CT e sigma)
          (Config CT dot sigma0) /\ multi_step_erasure_H (Config CT (Return dot) sigma0) 
          (Config CT dot sigma')).
  Proof.  intros CT e sigma sigma'. intro H_erasure. 
    remember (Config CT (Return e) sigma) as config. 
    remember (Config CT dot sigma') as config'.  
     generalize dependent e. generalize dependent sigma. generalize dependent sigma'.
    induction H_erasure.
    - intros. inversion Heqconfig. inversion Heqconfig'. subst. inversion H. subst.  left. auto.  
    - intros. inversion Heqconfig. inversion Heqconfig'. subst. inversion H. subst. 
        destruct IHH_erasure with sigma'0 sigma' e'; auto.  subst. auto. right. 
        exists sigma'. split.    apply H_erasure_single_step; auto. auto.  
       destruct H1 as [sigma'']. right. 
       exists sigma''. split.  apply H_erasure_multi_step with e' sigma'; auto. apply H1. apply H1.
      left. auto.
  Qed.

   assert ( e= dot \/ (exists sigma0,  multi_step_erasure_H (Config CT e (SIGMA s h) )
          (Config CT dot sigma0) /\ multi_step_erasure_H (Config CT (Return dot) sigma0) 
          (Config CT dot (SIGMA s'0 h'0)))).
    apply return_context_return_dot; auto. destruct H.
    ++ subst. inversion H_reduction.
    ++ destruct H as [sigma0]. destruct H. 

 inversion H0. subst.  inversion H6. subst. inversion H16.  subst.  subst. 
  remember (erasure_sigma_fun (SIGMA (lsf :: s'2) h0)) as sigma''. induction sigma''.
    destruct IHH_reduction with h0 (lsf :: s'2)  h1 s0 h' s' e' h s e ; auto. apply erasure_H_context with (lsf :: s'2) h0; auto.

    subst.  inversion H10.  subst. inversion H5.  subst.
  remember (erasure_sigma_fun (SIGMA (lsf :: s'2) h0)) as sigma''. induction sigma''.
    destruct IHH_reduction with h0 (lsf :: s'2)  h1 s0 h' s' e' h s e ; auto. apply erasure_H_context with (lsf :: s'2) h0; auto.

+ (* Return v*) inversion H12. subst. rewrite <- H15.  
       unfold current_label in H_context. unfold get_stack in H_context.
          unfold current_label. unfold get_stack.   
          induction lsf. 
          unfold get_current_label in H_context. unfold current_label in H_context. unfold get_stack_label in H_context.

          induction s'. intuition.  
          remember (get_current_label (Labeled_frame l0 s :: a :: s')) as lbl. 

          induction a. unfold update_current_label. 
          unfold get_current_label. unfold get_stack_label. 
          unfold get_current_label in Heqlbl.          unfold get_stack_label in Heqlbl. subst. 
          assert (  flow_to (join_label l0 l1)  L_Label = false).
          apply flow_join_label with l0 l1; auto.            apply join_label_commutative.
          auto. 

+ (* If id1 id2 e' s2 *)
    inversion H9. inversion H12.  subst. auto. 

+ (* If id1 id2 s1 e' *)
    inversion H9. inversion H12.  subst. auto. 

+ (* (Sequence s1 s2) .  *)
    inversion H_erasure.   rewrite H3 in H_context. inversion H_context. subst. 
    assert (s1 = dot 
    \/ (dot = dot /\ multi_step_erasure_H (Config CT s1 (SIGMA s h))
       (Config CT dot (SIGMA s'0 h'0)) /\ s2 = dot) 
    \/ (exists e0, multi_step_erasure_H (Config CT s1 (SIGMA s h))
       (Config CT e0 (SIGMA s'0 h'0))  /\ dot = (Sequence e0 s2))
    \/ (exists s'1 h'1, multi_step_erasure_H (Config CT s1 (SIGMA s h)) (Config CT dot (SIGMA s'1 h'1)) 
        /\ multi_step_erasure_H (Config CT (Sequence dot s2) (SIGMA s'1 h'1))
       (Config CT dot (SIGMA s'0 h'0)) )).
        apply context_erasure_sequence; auto.  
        destruct H. ++  subst. inversion H_reduction. ++ destruct H. 
        +++  destruct H. destruct H0. subst. 
        destruct IHH_reduction with h'0 s'0 h_r s_r h' s' s1' h s s1 ; auto. 
        apply erasure_H_context with s'0 h'0; auto. 
        +++ destruct H. destruct H as [e0]. destruct H. inversion H0.
        destruct H as [s'2].         destruct H as [h'2]. destruct H.
        remember (erasure_sigma_fun (SIGMA s'2 h'2)) as sigma''. induction sigma''. 
        destruct IHH_reduction with h'2 s'2 h0 s0 h' s' s1' h s s1 ; auto. 
        apply erasure_H_context with s'2 h'2; auto. 

+ inversion H9.  subst. auto. 
Qed. 


Lemma empty_stack_cannot_H_context : forall s h,
  flow_to (current_label (SIGMA s h)) L_Label = false ->
s <> nil.
Proof. intros. intro contra.  subst. unfold current_label in H. unfold get_stack in H. 
         unfold get_current_label in H. unfold flow_to in H. unfold L_Label in H.
    unfold subset in H. inversion H.
Qed. 

 Lemma erasure_sigma_equal_after_erasure : forall ct t t' sigma sigma', 
    Config ct t sigma =eH=> Config ct t' sigma' ->
    flow_to (current_label sigma) L_Label = false ->
    erasure_sigma_fun sigma =     erasure_sigma_fun sigma'.
 Proof. 
    intros ct t t' sigma sigma'.  intro H_erasure. intro H_flow. remember (Config ct t sigma) as config.
    remember (Config ct t' sigma') as config'. generalize dependent t'. generalize dependent t. 
    generalize dependent sigma. generalize dependent sigma'. 
    induction H_erasure; try ( intros; inversion Heqconfig; inversion Heqconfig'; subst; auto);
    try (apply  IHH_erasure with e e'; auto; fail).
    - unfold erasure_sigma_fun. unfold erasure_stack. unfold current_label in H_flow. 
      unfold get_stack in H_flow.  unfold get_current_label in H_flow. induction lsf. unfold get_stack_label in H_flow.
      rewrite H_flow. fold erasure_stack. auto. 
    - try (apply  IHH_erasure with e1 e1'; auto; fail).
    - try (apply  IHH_erasure with e2 e2'; auto; fail).
    - unfold erasure_sigma_fun. unfold erasure_stack. unfold current_label in H_flow. 
      unfold get_stack in H_flow.  unfold get_current_label in H_flow. induction lsf. unfold get_stack_label in H_flow.
      rewrite H_flow. fold erasure_stack. auto. 
    - try (apply  IHH_erasure with s1 s1'; auto; fail).
    - try (apply  IHH_erasure with s2 s2'; auto; fail).
    - try (apply  IHH_erasure with s1 s1'; auto; fail).
    - try (apply  IHH_erasure with s t'; auto; fail).
Qed. 

Lemma erasure_sigma_equal_after_erasure_multistep : forall ct t t' sigma sigma', 
    multi_step_erasure_H (Config ct t sigma) (Config ct t' sigma') ->
    flow_to (current_label sigma) L_Label = false ->
    erasure_sigma_fun sigma =     erasure_sigma_fun sigma'.
Proof. 
       intros ct t t' sigma sigma'.  intro H_erasure. intro H_flow. remember (Config ct t sigma) as config.
    remember (Config ct t' sigma') as config'. generalize dependent t'. generalize dependent t. 
    generalize dependent sigma. generalize dependent sigma'. induction H_erasure.
    intros; inversion Heqconfig; inversion Heqconfig'; subst; auto.
    - apply erasure_sigma_equal_after_erasure in H. auto. auto. 
    - intros. inversion Heqconfig; inversion Heqconfig'; subst; auto. 
      apply erasure_sigma_equal_after_erasure in H. auto. auto. 
       destruct IHH_erasure with sigma'0 sigma' t' t'0; auto. auto. 
Qed.  
 

Lemma H_context_to_L_context : forall e e' s h s' h' CT s'1 h'1 s_r h_r e_r, 
    forall T, has_type CT empty_context h e T -> 
    Config CT e (SIGMA s h) ==> Config CT e' (SIGMA s' h') ->
    flow_to (current_label (SIGMA s h)) L_Label = false ->
    flow_to (current_label (SIGMA s' h')) L_Label = true ->
    Config CT e (SIGMA s h) =e=> Config CT e_r (SIGMA s_r h_r) ->
    Config CT e' (SIGMA s' h') =e=> Config CT (erasure_L_fun e') (SIGMA s'1 h'1) ->
    Config CT e_r (SIGMA s_r h_r) = Config CT (erasure_L_fun e') (SIGMA s'1 h'1).
Proof.
Admitted. 

Lemma surface_syntax_if : forall t1 t2, 
    (if surface_syntax t1 then surface_syntax t2 else false) = true -> surface_syntax t1 = true /\ surface_syntax t2 = true.
    Proof.  intros. case_eq (surface_syntax t1). intro. case_eq (surface_syntax t2). intro. auto.
      intro. rewrite H0 in H. rewrite H1 in H. intuition. intro. rewrite H0 in H. intuition.
Qed.

Lemma surface_syntax_is_dot_free : forall t, 
  surface_syntax t = true -> dot_free t = true.
Proof. intros. induction t; auto; try (apply surface_syntax_if in H; destruct H; apply IHt1 in H; apply IHt2 in H0; 
        unfold dot_free; fold dot_free); try (rewrite H); auto; try (unfold surface_syntax in H; inversion H).
Qed. 
        

Lemma dot_free_if : forall t1 t2, 
    (if dot_free t1 then dot_free t2 else false) = true -> dot_free t1 = true /\ dot_free t2 = true.
    Proof.  intros. case_eq (dot_free t1). intro. case_eq (dot_free t2). intro. auto.
      intro. rewrite H0 in H. rewrite H1 in H. intuition. intro. rewrite H0 in H. intuition.
Qed.

Lemma dot_free_preservation : forall t t' s h s' h' CT, 
  field_wfe_heap CT h -> wfe_heap CT h -> wfe_stack CT h s ->
  Config CT t (SIGMA s h) ==> Config CT t' (SIGMA s' h') ->
  dot_free t = true ->
  forall T, has_type CT empty_context h t T -> 
  dot_free t' = true.
Proof. intros  t t' s h s' h' CT. intro H_wfe_fields. 
  intro H_wfe_heap. intro H_wfe_stack. intro H_reduction. intro H_dot_free.
  intro T.  intro H_typing. 
  generalize dependent t'.  
  generalize dependent T.
    generalize dependent s'.      generalize dependent h'. 
induction t; intros; subst; try (inversion H_reduction; fail);
     try (unfold  dot_free in H_dot_free; auto; fold dot_free in H_dot_free; auto).
-  inversion H_typing. inversion H3.
- inversion H_reduction. 
 + subst.  inversion H_typing. destruct IHt with h' s' (classTy clsT) e'; auto.
 + subst.  inversion H_wfe_fields. inversion H5. subst. rename h0 into h.
    inversion H_typing. subst. inversion H2. subst. destruct H14 as [F'].  destruct H0 as [lo]. 
    destruct H12 as [field_defs0]. destruct H1 as [method_defs0]. rewrite <- H6 in H0. inversion H0.
    subst. rewrite <- H3 in H4. inversion H4.  
   assert ( exists cn field_defs method_defs, CT cn = Some cls_def
               /\ cls_def = (class_def cn field_defs method_defs)). 
    apply heap_consist_ct with h o F' lo; auto. rewrite H8 in H6. auto.
    destruct H1 as [cls_name].     destruct H1 as [field_defs].
    destruct H1 as [method_defs].     destruct H1. 
    rewrite H9 in H8. inversion H8. subst.
    destruct H with o (class_def cls_name field_defs method_defs) 
          F' cls_name lo method_defs field_defs i  cls'; auto. 
    destruct H9. destruct H11. rewrite H9 in H7. inversion H7. rewrite H11. auto.
    destruct H11 as [o'].     destruct H11 as [F_f]. destruct H11 as [lx]. 
    destruct H11 as [f_field_defs].     destruct H11 as [f_method_defs]. destruct H11. 
    rewrite H9 in H7. inversion H7. rewrite H11. auto.
- inversion H_reduction.
 + subst.  inversion H_typing. destruct IHt1 with h' s' (classTy T0) e'; auto.

  apply dot_free_if in H_dot_free. destruct H_dot_free. auto.
  unfold dot_free. fold dot_free. auto.
    case_eq (dot_free e'). intro. rewrite H15 in H_dot_free. 
    apply dot_free_if in H_dot_free. destruct H_dot_free. auto.
    intro.  auto.
+ subst.  apply dot_free_if in H_dot_free. destruct H_dot_free. auto.
  unfold dot_free. fold dot_free. inversion H_typing. destruct IHt2 with h' s'  (classTy arguT) e'; auto.
  rewrite H. case_eq (dot_free e'). intro. auto. intro. auto.
+ subst. inversion H6. subst. inversion H_typing. subst.  inversion H2. 
    destruct H16 as [F0]. destruct H16 as [lb]. rewrite H16 in H7. inversion H7. 
    rewrite <- H1 in H4. inversion H4. subst. rewrite H5 in H8. inversion H8. subst. auto.
    unfold dot_free. fold dot_free. apply surface_syntax_is_dot_free. auto.
     
+ subst. inversion H6. subst. inversion H_typing. subst.  inversion H2. 
    destruct H16 as [F0]. destruct H16 as [l0]. rewrite H16 in H7. inversion H7. 
    rewrite <- H1 in H4. inversion H4. subst. rewrite H5 in H13. inversion H13. subst. auto.
    unfold dot_free. fold dot_free. apply surface_syntax_is_dot_free. auto.
- inversion H_reduction. auto.
- inversion H_reduction. subst. inversion H_typing. destruct IHt with h' s' T0 e'; auto. subst. auto.
- inversion H_reduction. subst. inversion H_typing. destruct IHt with h' s' (LabelelTy T) e'; auto. subst. auto.
- inversion H_reduction. subst. inversion H_typing. destruct IHt with h' s' (LabelelTy T0) e'; auto. subst. auto.
- inversion H_reduction. subst. inversion H_typing. destruct IHt with h' s' (OpaqueLabeledTy T) e'; auto. subst. auto.
- inversion H_reduction. subst. inversion H_typing. destruct IHt with h' s' T0 e'; auto. 
    inversion H_typing. subst. destruct IHt with h' s' T0 (Return e'); auto. apply ST_return1. auto.
    subst. unfold dot_free. fold dot_free. auto.
    subst. unfold dot_free in H_dot_free. fold dot_free in H_dot_free. unfold dot_free. fold dot_free. auto.
- inversion H_typing. inversion H4.
- inversion H_reduction. apply dot_free_if in H_dot_free. destruct H_dot_free. auto. inversion H_typing.
  + subst. destruct IHt1 with h' s' (classTy clsT) e1'; auto.
      unfold dot_free. fold dot_free. case_eq (dot_free e1'). intro. rewrite H in H8. auto.
      intro. auto.
  +  apply dot_free_if in H_dot_free. destruct H_dot_free. auto. inversion H_typing.
      subst. destruct IHt2 with h' s' (classTy cls') e2'; auto.
      unfold dot_free. fold dot_free. case_eq (dot_free e2'). intro. rewrite H in H9. rewrite H9. auto.
      intro. rewrite H in H9. rewrite H9. auto.
  + subst. auto.
  + subst. auto.
- inversion H_reduction. apply dot_free_if in H_dot_free. destruct H_dot_free. auto. inversion H_typing.
  + subst. inversion H23. inversion H5.
  + subst. inversion H_typing. inversion H7. inversion H18.
- apply dot_free_if in H_dot_free. destruct H_dot_free. auto. inversion H_typing. inversion H_reduction. 
  + subst. destruct IHt1 with h' s' (T0) s1'; auto.
      unfold dot_free. fold dot_free. case_eq (dot_free s1'). intro. rewrite H1 in H0. auto.
      intro. auto.
  + subst. auto.
-  inversion H_typing.  inversion H_reduction.
  + subst. destruct IHt with h' s' T e'; auto.
  + subst. auto.
Qed.


Inductive valid_syntax :  tm -> Prop :=
  (*variable *)
  | Valid_var : forall x,
      valid_syntax (Tvar x)
(* null *)
  | Valid_null : 
      valid_syntax null
(* Field read *)
  | Valid_FieldAccess : forall e f,
      valid_syntax e ->
      valid_syntax (FieldAccess e f)

(* method call *)
  | Valid_MethodCall1 : forall e meth argu,
      valid_syntax e ->
      surface_syntax argu = true -> 
      valid_syntax (MethodCall e meth argu)

  | Valid_MethodCall2 : forall v meth argu,
      value v -> 
      valid_syntax argu ->
      valid_syntax (MethodCall v meth argu)

(* new exp *)
  | Valid_NewExp : forall cls_name,
      valid_syntax (NewExp cls_name)
(* label *)
  | Valid_label : forall lb,
      valid_syntax (l lb)
(* label data *)
  | Valid_labelData : forall e lb,
      valid_syntax e ->
      valid_syntax (labelData e lb)
(* unlabel *)
  | Valid_unlabel : forall e,
      valid_syntax e ->
      valid_syntax (unlabel e) 
(* labelOf *)
  | Valid_labelOf : forall e,
      valid_syntax e ->
      valid_syntax (labelOf e)
(* unlabel opaque *)
  | Valid_unlabelOpaque : forall e,
      valid_syntax e ->
      valid_syntax (unlabelOpaque e)
(* opaque call 1 *)
  | Valid_opaqueCall : forall e,
      valid_syntax e ->
      valid_syntax (opaqueCall e)
(* Skip *)
  | Valid_skip : 
      valid_syntax Skip
(* assignment *)
  | Valid_assignment : forall e x, 
      valid_syntax e ->
      valid_syntax (Assignment x e)
(* Field Write *)
  | Valid_FieldWrite1 : forall e1 f  e2,
      valid_syntax e1 ->
      surface_syntax e2 = true -> 
      valid_syntax (FieldWrite e1 f e2)

  | Valid_FieldWrite2 : forall v f  e2,
      value v -> 
      valid_syntax e2 ->
      valid_syntax (FieldWrite v f e2)
(* if *)
  | Valid_if1 : forall id1 id2 e1 e2,
      valid_syntax e1 ->
      surface_syntax e2 = true -> 
      valid_syntax (If id1 id2 e1 e2)

  | Valid_if2 : forall id1 id2 v e2,
      value v -> 
      valid_syntax e2 ->
      valid_syntax (If id1 id2 v e2)
(* sequence *)
  | Valid_sequence1 : forall e1 e2,
      valid_syntax e1 ->
      surface_syntax e2 = true -> 
      valid_syntax (Sequence e1 e2)

  | Valid_sequence2 : forall v e2,
      value v -> 
      valid_syntax e2 ->
      valid_syntax (Sequence v e2)

(* return *)
  | Valid_return : forall e,
      valid_syntax e ->
      valid_syntax (Return e)
(* ObjId *)
  | Valid_ObjId : forall o,
      valid_syntax (ObjId o)
(* runtime labeled data *)
  | Valid_v_l : forall lb v,
      value v ->
      valid_syntax (v_l v lb)
(* runtime labeled data *)
  | Valid_v_opa_l : forall lb v,
      value v ->
      valid_syntax (v_opa_l v lb)
  | Valid_dot : 
      valid_syntax dot. 





Hint Constructors valid_syntax.
Lemma value_is_valid_syntax : forall v, 
  value v -> valid_syntax v.
Proof with eauto. intros. inversion H. apply Valid_ObjId. apply Valid_skip. apply Valid_null. apply Valid_label. apply Valid_v_l.
        auto. apply Valid_v_opa_l. auto. apply Valid_dot. Qed. 

Lemma surface_syntax_is_valid_syntax : forall t,
  surface_syntax t = true -> valid_syntax t.
Proof with eauto. intros. induction t; try ( unfold  surface_syntax in H; fold  surface_syntax in H; inversion H; auto).
-  apply surface_syntax_if in H. destruct H. apply IHt1 in H. apply Valid_MethodCall1. auto. auto. 
-  apply surface_syntax_if in H. destruct H. apply Valid_FieldWrite1. apply IHt1 in H. auto. auto. 
- apply surface_syntax_if in H. destruct H.  apply Valid_if1. apply IHt1 in H. auto. auto. 
- apply surface_syntax_if in H. destruct H.  apply Valid_sequence1. apply IHt1 in H. auto. auto.
Qed.  

Lemma surface_syntax_H_erasure_dot : forall t ct sigma sigma',
surface_syntax t = true -> 
Config ct t sigma =eH=> Config ct dot sigma' ->
sigma = sigma'.
Proof. 
Proof. intros. induction t; try (inversion H0; subst; auto).
- unfold surface_syntax in H. inversion H.
- unfold surface_syntax in H. inversion H. Qed. 

Lemma surface_syntax_H_erasure : forall t t' ct sigma sigma',
surface_syntax t = true -> 
Config ct t sigma =eH=> Config ct t' sigma' ->
sigma = sigma'.
Proof. 
Proof. intros. 
remember (Config ct t sigma) as config. 
      remember (Config ct t' sigma') as config'.
    generalize dependent t.     generalize dependent sigma.     generalize dependent sigma'.
        generalize dependent t'. 
induction H0; intros; inversion Heqconfig; inversion Heqconfig'; subst; auto;
 try (destruct IHerasure_H with e' sigma'0 sigma0 e; auto);
 try (unfold surface_syntax in H; inversion H; fail); 
 try (apply surface_syntax_if in H; apply H; fail).
- unfold surface_syntax in H4. inversion H4.
- apply surface_syntax_if in H. destruct IHerasure_H with e1' sigma'0 sigma0 e1; auto. apply H.
- unfold surface_syntax in H3. inversion H3.
- apply surface_syntax_if in H. destruct IHerasure_H with s1' sigma'0 sigma0 s1; auto. apply H.
- apply surface_syntax_if in H. destruct IHerasure_H with s1' sigma'0 sigma0 s1; auto. apply H.
Qed. 


Fixpoint surface_syntax_plus_dot (t : tm) :=
  match t with
    | Tvar x => true
    | null => true
    | FieldAccess e f => (surface_syntax_plus_dot e)
    | MethodCall e1 meth e2 => if (surface_syntax_plus_dot e1) then (surface_syntax_plus_dot e2) else false
    | NewExp cls => true
(* label related *)
    | l lb => true
    | labelData e lb => (surface_syntax_plus_dot e)
    | unlabel e => (surface_syntax_plus_dot e)
    | labelOf e => (surface_syntax_plus_dot e)
    | unlabelOpaque e => (surface_syntax_plus_dot e)
    | opaqueCall e => (surface_syntax_plus_dot e)
(* statements *)
    | Skip => false
    | Assignment x e => (surface_syntax_plus_dot e)
    | FieldWrite e1 f e2 =>  if (surface_syntax_plus_dot e1) then (surface_syntax_plus_dot e2) else false
    | If id0 id1 e1 e2 =>  if (surface_syntax_plus_dot e1) then (surface_syntax_plus_dot e2) else false
    | Sequence e1 e2 =>  if (surface_syntax_plus_dot e1) then (surface_syntax_plus_dot e2) else false
    | Return e => false

(* special terms *)
    | ObjId o =>  false
  (* runtime labeled date*)
    | v_l e lb => false
    | v_opa_l e lb => false
    | dot => true
  end.

Lemma surface_syntax_plus_dot_if : forall t1 t2, 
    (if surface_syntax_plus_dot t1 then surface_syntax_plus_dot t2 else false) = true -> surface_syntax_plus_dot t1 = true /\ surface_syntax_plus_dot t2 = true.
    Proof.  intros. case_eq (surface_syntax_plus_dot t1). intro. case_eq (surface_syntax_plus_dot t2). intro. auto.
      intro. rewrite H0 in H. rewrite H1 in H. intuition. intro. rewrite H0 in H. intuition.
Qed.

Lemma surface_syntax_plus_dot_H_erasure : forall t t' ct sigma sigma',
surface_syntax_plus_dot t = true -> 
Config ct t sigma =eH=> Config ct t' sigma' ->
sigma = sigma'.
Proof. 
Proof. intros. 
remember (Config ct t sigma) as config. 
      remember (Config ct t' sigma') as config'.
    generalize dependent t.     generalize dependent sigma.     generalize dependent sigma'.
        generalize dependent t'. 
induction H0; intros; inversion Heqconfig; inversion Heqconfig'; subst; auto;
 try (destruct IHerasure_H with e' sigma'0 sigma0 e; auto);
 try (unfold surface_syntax_plus_dot in H; inversion H; fail); 
 try (apply surface_syntax_plus_dot in H; apply H; fail).
- apply surface_syntax_plus_dot_if in H. apply H.
- unfold surface_syntax_plus_dot in H4. inversion H4.
- apply surface_syntax_plus_dot_if in H. destruct IHerasure_H with e1' sigma'0 sigma0 e1; auto. apply H.
- unfold surface_syntax_plus_dot in H. fold surface_syntax_plus_dot in H. 
 destruct IHerasure_H with e2' sigma'0 sigma0 e2; auto.
-  unfold surface_syntax_plus_dot in H3. inversion H3.
- apply surface_syntax_plus_dot_if in H. destruct IHerasure_H with s1' sigma'0 sigma0 s1; auto. apply H.
- unfold surface_syntax_plus_dot in H. fold surface_syntax_plus_dot in H. 
 destruct IHerasure_H with s2' sigma'0 sigma0 s2; auto.
- apply surface_syntax_plus_dot_if in H. 
 destruct IHerasure_H with s1' sigma'0 sigma0 s1; auto. apply H.
- unfold surface_syntax_plus_dot in H. fold surface_syntax_plus_dot in H. 
 destruct IHerasure_H with t' sigma'0 sigma0 s; auto.
Qed. 

Lemma surface_syntax_plus_preservation : forall t t' ct sigma sigma',
    surface_syntax_plus_dot t = true -> 
    Config ct t sigma =eH=> Config ct t' sigma' ->
    surface_syntax_plus_dot t' = true.
Proof. intros. remember (Config ct t sigma) as config.  remember  (Config ct t' sigma') as config'.
        generalize dependent t.     generalize dependent sigma.     generalize dependent sigma'. generalize dependent t'. 
    induction H0; intros; inversion Heqconfig;  inversion Heqconfig';  subst;
     try (unfold surface_syntax_plus_dot in H; inversion H; fail); auto; 
    try (destruct IHerasure_H with e' sigma'0 sigma0 e; auto; fail); 
    try (apply surface_syntax_plus_dot_if in H; apply H; auto; fail) . 
    - apply surface_syntax_plus_dot_if in H. destruct H.  unfold surface_syntax_plus_dot.  fold surface_syntax_plus_dot.
    assert (surface_syntax_plus_dot e' = true). apply IHerasure_H with sigma'0 sigma0 e; auto. rewrite H2. rewrite H1. auto. 
    -  apply surface_syntax_plus_dot_if in H. destruct H.  unfold surface_syntax_plus_dot.  fold surface_syntax_plus_dot.
    assert (surface_syntax_plus_dot e1' = true). apply IHerasure_H with sigma'0 sigma0 e1; auto. rewrite H2. rewrite H1. auto.
    - unfold surface_syntax_plus_dot in H.  fold surface_syntax_plus_dot in H. unfold surface_syntax_plus_dot. fold surface_syntax_plus_dot. 
    apply IHerasure_H with sigma'0 sigma0 e2; auto. 
    -unfold surface_syntax_plus_dot in H.  fold surface_syntax_plus_dot in H. unfold surface_syntax_plus_dot. fold surface_syntax_plus_dot. 
    apply surface_syntax_plus_dot_if in H. destruct H.
    assert (surface_syntax_plus_dot s1' = true). apply IHerasure_H with sigma'0 sigma0 s1; auto. rewrite H2. rewrite H1. auto.
    - unfold surface_syntax_plus_dot in H.  fold surface_syntax_plus_dot in H. unfold surface_syntax_plus_dot. fold surface_syntax_plus_dot. 
    assert (surface_syntax_plus_dot s2' = true). apply IHerasure_H with sigma'0 sigma0 s2; auto. rewrite H1. auto.
    - apply surface_syntax_plus_dot_if in H. destruct H. 
       unfold surface_syntax_plus_dot. fold surface_syntax_plus_dot. 
       assert (surface_syntax_plus_dot s1' = true). apply IHerasure_H with sigma'0 sigma0 s1; auto. rewrite H2. rewrite H1. auto.
    - unfold surface_syntax_plus_dot in H.  fold surface_syntax_plus_dot in H. unfold surface_syntax_plus_dot. fold surface_syntax_plus_dot. 
    apply IHerasure_H with sigma'0 sigma0 s; auto.
Qed.

Lemma surface_syntax_plus_dot_H_multi_erasure : forall t t' ct sigma sigma',
surface_syntax_plus_dot t = true -> 
multi_step_erasure_H (Config ct t sigma) (Config ct t' sigma') ->
sigma = sigma'.
Proof. intros. 
remember (Config ct t sigma) as config. remember (Config ct t' sigma') as config'.
    generalize dependent t.     generalize dependent sigma.     generalize dependent sigma'.
        generalize dependent t'. 
induction H0; intros; inversion Heqconfig; inversion Heqconfig'; subst; auto.
- apply surface_syntax_plus_dot_H_erasure with t0 t'0 ct. auto. auto. 
- destruct IHmulti_step_erasure_H with t'0 sigma'0 sigma' t'; auto. 
   apply surface_syntax_plus_preservation with t0 ct sigma0 sigma'; auto. 
    apply surface_syntax_plus_dot_H_erasure with t0 t' ct; auto.
Qed.  




Lemma surface_syntax_plus_erasure_H_dot : forall t sigma ct t' sigma', 
  surface_syntax_plus_dot t = true -> 
flow_to (current_label sigma) L_Label = false ->
  multi_step_erasure_H (Config ct t sigma)  (Config ct t' sigma') ->
  t' = dot. 
Proof. intros.  
 remember (Config ct t sigma) as config.  remember  (Config ct t' sigma') as config'.
    generalize dependent t.     generalize dependent sigma.     generalize dependent sigma'.
induction H1; intros; inversion Heqconfig;  inversion Heqconfig';  subst.
-destruct H0. auto.  apply surface_syntax_plus_dot_H_erasure with t0 t' ct sigma0 sigma'0 in H. 
  subst.  rewrite H0 in H1. inversion H1. auto. 
- destruct IHmulti_step_erasure_H with sigma'0 sigma' t'0; auto. 
apply surface_syntax_plus_preservation with t0 ct sigma0 sigma'. auto. auto. 
Qed. 

Lemma surface_syntax_imple_plus : forall t, 
  surface_syntax t = true ->  surface_syntax_plus_dot t = true.
Proof. intros. induction t; try (unfold surface_syntax in H; inversion H; fail) ;
  try (unfold surface_syntax_plus_dot; auto; fail); 
 try (unfold surface_syntax_plus_dot; fold surface_syntax_plus_dot; apply surface_syntax_if in H; destruct H;
  apply IHt1 in H; rewrite H;   apply IHt2 in H0; rewrite H0; auto).
Qed.

Lemma surface_syntax_erasure_H_dot : forall t sigma ct t' sigma', 
  surface_syntax t = true -> 
  flow_to (current_label sigma) L_Label = false ->
  multi_step_erasure_H (Config ct t sigma)  (Config ct t' sigma') ->
  t' = dot. 
Proof. intros.  apply surface_syntax_imple_plus in H. 
  apply surface_syntax_plus_erasure_H_dot with t sigma ct sigma'; auto. Qed. 

Lemma surface_syntax_equal_after_erasure : forall t,
   surface_syntax t = true -> erasure_L_fun t = t. 
Proof. intros. induction t; try (unfold surface_syntax in H; fold surface_syntax in H; inversion H; auto); 
try (apply IHt in H; unfold erasure_L_fun; fold erasure_L_fun; rewrite H; auto);
try  (unfold erasure_L_fun; fold erasure_L_fun; apply surface_syntax_if in H; destruct H;
    apply IHt1 in H; apply IHt2 in H0; rewrite H; rewrite H0;  auto).
Qed.  

Lemma simulation_H : forall CT t t0 t' t0' s h s' h' sigma_l_e sigma_r_e,
      dot_free t = true ->
      valid_syntax t ->
      forall T, has_type CT empty_context h t T -> 
      field_wfe_heap CT h -> wfe_heap CT h -> wfe_stack CT h s ->
      flow_to (current_label (SIGMA s h)) L_Label = false ->
      Config CT t (SIGMA s h) ==> Config CT t' (SIGMA s' h') ->
      (Config CT t (SIGMA s h)) =e=> (Config CT t0 sigma_l_e) ->
      (Config CT t' (SIGMA s' h')) =e=> (Config CT t0' sigma_r_e) ->
      (Config CT t0 sigma_l_e) = (Config CT t0' sigma_r_e).
Proof. 
  intros CT t t0 t' t0' s h s' h' sigma_l_e sigma_r_e. intro H_dot_free. intro H_valid_syntax. 
  intro T. intro H_typing. intro H_wfe_fields. 
  intro H_wfe_heap. intro H_wfe_stack. 
  intro H_flow. intro H_reduction. 
  (*intro H_erasure_sigma_l.  *) intro H_erasure_l. intro H_erasure_r.   

  
generalize dependent t'. 
  generalize dependent t0.
  generalize dependent t0'.
  generalize dependent T.
    generalize dependent sigma_l_e.      generalize dependent sigma_r_e. 
    generalize dependent s.      generalize dependent h.
    generalize dependent s'.      generalize dependent h'.
induction t. 
  - intros.  admit. -intros.  admit.  - intros.  admit. 
  - intros.  admit. -intros.  admit.  - intros.  admit. 
  - intros.  admit. -intros.  admit.  - intros.  admit. 
  - intros.  admit. -intros.  admit.  - intros.  admit. 
  - intros.  admit. 

- (* (FieldWrite t1 i t2) *) intros. unfold dot_free in H_dot_free. fold dot_free in H_dot_free. auto.
  apply dot_free_if in H_dot_free. destruct H_dot_free.  inversion H_erasure_l. subst.
  + rewrite H_flow in H4. inversion H4.
  + subst. inversion H_reduction.  
  ++ subst. inversion H_erasure_r. subst.
  +++ subst.  rename i into f.  rename t1 into e. rename t2 into e2. rename t0 into e_r.
        assert (    e = dot 
    \/ (e_r = dot /\ multi_step_erasure_H (Config CT e (SIGMA s h))
       (Config CT dot (SIGMA s'0 h'0)) /\ e2 = dot) 
    \/ (exists e0, multi_step_erasure_H (Config CT e (SIGMA s h))
       (Config CT e0 (SIGMA s'0 h'0))  
        /\ flow_to (current_label (SIGMA s'0 h'0)) L_Label = true 
        /\ e_r = (FieldWrite e0 f e2))
    \/ (exists s'1 h'1, multi_step_erasure_H (Config CT e (SIGMA s h)) (Config CT dot (SIGMA s'1 h'1)) 
      /\ flow_to (current_label (SIGMA s'1 h'1)) L_Label = false 
        /\ multi_step_erasure_H (Config CT (FieldWrite dot f e2) (SIGMA s'1 h'1))
       (Config CT e_r (SIGMA s'0 h'0)) )).
        apply context_erasure_field_write_obj; auto.    destruct H1.
    ++++ subst. inversion H2. 
   ++++ destruct H1. 
    +++++ destruct H1. subst. destruct H3.  subst. 
     assert (    flow_to (current_label (SIGMA s' h')) L_Label = false).
    apply dot_erasure_preverve_high_context with s h CT e e1' s'' h''; auto.  
    apply erasure_H_context with s'0 h'0; auto. rewrite H3 in H6. inversion H6. 
    +++++ subst. destruct H1. 
    ++++++  destruct H1 as [e0]. destruct H1. subst.
      assert ((Config CT e1' (SIGMA s' h')) =e=> (Config CT (erasure_L_fun e1') (SIGMA s'1 h'1))).
      apply erasure_L_context; auto. 
      assert ((Config CT e (SIGMA s h)) =e=> (Config CT e0 (SIGMA s'' h''))).
      apply erasure_H_context with s'0 h'0; auto.
      inversion H_typing. subst. 
      unfold erasure_L_fun.        fold erasure_L_fun. 
      assert (Config CT e0 (SIGMA s'' h'') =Config CT (erasure_L_fun e1' ) (SIGMA s'1 h'1)).
      destruct  IHt1 with h' s' h s (SIGMA s'1 h'1) (SIGMA s'' h'')  (classTy clsT) (erasure_L_fun e1') e0 e1'; auto.
      inversion H_valid_syntax. subst. auto. subst. auto. apply value_is_valid_syntax. auto. assert ((erasure_L_fun e2) = e2).
      apply surface_syntax_equal_after_erasure. auto.
      inversion H_valid_syntax. subst. auto. subst. auto. 
      inversion H15; subst; inversion H2.
      inversion H10.  subst. destruct H3. subst.  rewrite H11. auto.
  ++++++ destruct H1 as [s'2]. destruct H1 as [h'2]. destruct H1. 
      assert ((Config CT e1' (SIGMA s' h')) =e=> (Config CT (erasure_L_fun e1') (SIGMA s'1 h'1))).
      apply erasure_L_context; auto.

      inversion H_valid_syntax. subst. 

Lemma field_write_context_erasure3 : forall CT f e2 e_r sigma sigma', 
    multi_step_erasure_H (Config CT (FieldWrite dot f e2) sigma)
       (Config CT e_r sigma') ->
    (e2 = dot \/ exists e0 sigma0, (multi_step_erasure_H (Config CT e2 sigma)  (Config CT e0 sigma0)) ).
Proof. intros CT f e2 e_r sigma sigma'.
    intro H_erasure. 
    remember  (Config CT (FieldWrite dot f e2) sigma) as config.    remember (Config CT e_r sigma') as config'.
   generalize dependent e2. generalize dependent sigma. 
   generalize dependent sigma'. generalize dependent e_r. induction H_erasure. 
   + intros. inversion Heqconfig'. inversion Heqconfig. subst. inversion H. ++ subst. inversion H2. 
        ++   subst. destruct H0.  inversion H0. right. exists e2'.  exists sigma'0. apply H_erasure_single_step.    auto. right. auto. 
        ++  subst. left. auto.  
   + intros. inversion Heqconfig'. inversion Heqconfig. subst. inversion H. subst. ++ inversion H2. 
      ++  subst. destruct IHH_erasure with e_r sigma'0 sigma' e2' ; auto. 
      +++ subst.  inversion H_erasure.  subst.  inversion H4. subst. ++++ inversion H3. 
           ++++ subst. inversion H3. ++++ subst. right.  exists dot. exists sigma'0. apply  H_erasure_single_step; auto. 
          ++++  subst. inversion H7.  
          subst. inversion H3. inversion H3. subst. inversion H10. inversion H4. inversion H8.
        +++  right. destruct H1 as [e3]. destruct H1 as [sigma3]. exists e3. exists sigma3.  apply H_erasure_multi_step with e2' sigma'; auto. 
      ++ left. auto. 
Qed. 

assert (e_r = dot). apply surface_syntax_plus_erasure_H_dot with (FieldWrite dot f e2) (SIGMA s'2 h'2) CT (SIGMA s'0 h'0); auto. 
  unfold surface_syntax_plus_dot. fold surface_syntax_plus_dot. apply surface_syntax_imple_plus. auto. destruct H3. auto. apply H3.
subst. destruct H3.

assert ( flow_to (current_label (SIGMA s' h')) L_Label = false).
remember (erasure_sigma_fun (SIGMA s'2 h'2)) as sigma''. induction sigma''.
apply dot_erasure_preverve_high_context with s h CT e e1' s0 h0; auto.
apply erasure_H_context with s'2 h'2; auto. 
rewrite H10 in H6. inversion H6.

subst.

assert ( flow_to (current_label (SIGMA s' h')) L_Label = false).
remember (erasure_sigma_fun (SIGMA s'2 h'2)) as sigma''. induction sigma''.
apply dot_erasure_preverve_high_context with s h CT e e1' s0 h0; auto.
apply erasure_H_context with s'2 h'2; auto. 
rewrite H7 in H6. inversion H6.

+++ subst. 
rename i into f.  rename t1 into e. rename t2 into e2. rename t0 into e_r.
        assert (    e = dot 
    \/ (e_r = dot /\ multi_step_erasure_H (Config CT e (SIGMA s h))
       (Config CT dot (SIGMA s'0 h'0)) /\ e2 = dot) 
    \/ (exists e0, multi_step_erasure_H (Config CT e (SIGMA s h))
       (Config CT e0 (SIGMA s'0 h'0))  
  /\ flow_to (current_label (SIGMA s'0 h'0)) L_Label = true 
/\ e_r = (FieldWrite e0 f e2))
    \/ (exists s'1 h'1, multi_step_erasure_H (Config CT e (SIGMA s h)) (Config CT dot (SIGMA s'1 h'1)) 
      /\ flow_to (current_label (SIGMA s'1 h'1)) L_Label = false 
        /\ multi_step_erasure_H (Config CT (FieldWrite dot f e2) (SIGMA s'1 h'1))
       (Config CT e_r (SIGMA s'0 h'0)) )).
        apply context_erasure_field_write_obj; auto.  

rename e1' into e'. rename t0' into e_r'.
        assert (    e' = dot 
    \/ (e_r' = dot /\ multi_step_erasure_H (Config CT e' (SIGMA s' h'))
       (Config CT dot (SIGMA s'1 h'1)) /\ e2 = dot) 
    \/ (exists e0', multi_step_erasure_H (Config CT e' (SIGMA s' h'))
       (Config CT e0' (SIGMA s'1 h'1))  
  /\ flow_to (current_label (SIGMA s'1 h'1)) L_Label = true 
/\ e_r' = (FieldWrite e0' f e2))
    \/ (exists s'2 h'2, multi_step_erasure_H (Config CT e' (SIGMA s' h')) (Config CT dot (SIGMA s'2 h'2)) 
      /\ flow_to (current_label (SIGMA s'2 h'2)) L_Label = false 
        /\ multi_step_erasure_H (Config CT (FieldWrite dot f e2) (SIGMA s'2 h'2))
       (Config CT e_r' (SIGMA s'1 h'1)) )).
        apply context_erasure_field_write_obj; auto.
  destruct H1. ++++ subst. unfold dot_free in H. inversion H.
++++ destruct H1. +++++ destruct H1. destruct H5. subst. unfold dot_free in H0. inversion H0. 
+++++ destruct H1.  ++++++ destruct H1 as [e0]. destruct H1. destruct H3. 
inversion H_typing.
  assert (dot_free e' = true). apply dot_free_preservation with e s h s' h' CT (classTy clsT); auto. subst. 
  unfold dot_free in H22. inversion H22. destruct H3. destruct H3. destruct H7. subst. 
  unfold dot_free in H0. inversion H0. destruct H3. 
+++++++ destruct H3 as [e0']. destruct H3. destruct H7.
inversion H_typing. subst. 
  assert (Config CT  e0 (SIGMA s'' h'') = (Config CT e0' (SIGMA s''0 h''0))).
  apply  IHt1 with h' s' h s (classTy clsT) e'; auto. 
  inversion H_valid_syntax. auto. apply value_is_valid_syntax. auto.
  apply erasure_H_context with s'0 h'0; auto.
  apply erasure_H_context with s'1 h'1; auto.
  destruct H5. subst.  inversion H10. subst. auto.
+++++++ destruct H3 as [s'2].  destruct H3 as [h'2]. subst. destruct H3. destruct H5. destruct H7.  
remember (erasure_sigma_fun (SIGMA s'2 h'2)) as sigma''. induction sigma''. 
  assert (Config CT e0 (SIGMA s'' h'') = (Config CT dot (SIGMA s0 h0))). inversion H_typing.
  apply  IHt1 with h' s' h s (classTy clsT) e'; auto. 
  inversion H_valid_syntax. auto. apply value_is_valid_syntax. auto. subst. 
  apply erasure_H_context with s'0 h'0; auto.
  apply erasure_H_context with s'2 h'2; auto.
  inversion H14. subst. 

  assert (e2 = dot \/ exists e0 sigma0, (multi_step_erasure_H (Config CT e2 (SIGMA s'2 h'2))  (Config CT e0 sigma0))).
  apply field_write_context_erasure3 with f e_r' (SIGMA s'1 h'1); auto. 
destruct H10. subst. unfold dot_free in H0. inversion H0.  
destruct H10 as [e0]. destruct H10 as [sigma0]. assert (e0 = dot). apply surface_syntax_erasure_H_dot with e2  (SIGMA s'2 h'2) CT sigma0; auto. subst.
inversion H_valid_syntax. auto.  
inversion H17; subst; inversion H2. subst. 
(*
assert (flow_to (current_label (SIGMA s'0 h'0)) L_Label = false).

Lemma field_write_context_erasure3 : forall CT f e2 e_r sigma sigma', 
    multi_step_erasure_H (Config CT (FieldWrite dot f e2) sigma)
       (Config CT e_r sigma') ->
    (e2 = dot \/ exists e0 sigma0, (multi_step_erasure_H (Config CT e2 sigma)  (Config CT e0 sigma0)) ).

assert (e_r = dot). apply surface_syntax_plus_erasure_H_dot with (FieldWrite dot f e2) (SIGMA s'2 h'2) CT (SIGMA s'0 h'0); auto. 
  unfold surface_syntax_plus_dot. fold surface_syntax_plus_dot. apply surface_syntax_imple_plus. auto. destruct H3. auto. apply H3.
subst. destruct H3.

 
  inversion H10. subst. 
 Lemma field_write_e_dot : forall e CT e2 f sigma sigma' sigma'' e_r,
valid_syntax (FieldWrite e f e2) ->
multi_step_erasure_H (Config CT (FieldWrite e f e2) sigma)
       (Config CT e_r sigma') ->
multi_step_erasure_H (Config CT e sigma)
       (Config CT dot sigma'') ->
flow_to (current_label sigma) L_Label = false ->
e_r = dot. 
Proof. intros e CT e2 f sigma sigma' sigma'' e_r. intro H_valid_syntax.   intro H_erasure. 
    remember  (Config CT (FieldWrite e f e2) sigma) as config.    remember (Config CT e_r sigma') as config'.
   generalize dependent e2. generalize dependent sigma. generalize dependent sigma''. generalize dependent e. 
   generalize dependent sigma'. generalize dependent e_r. induction H_erasure. 
   + intros. inversion Heqconfig'. inversion Heqconfig. subst. inversion H. ++ subst. inversion H1.  subst. 
        destruct H0. inversion H0. inversion H_valid_syntax. subst. 
        +++   
        ++   subst. destruct H0.  inversion H0. right. exists e2'.  exists sigma'0. apply H_erasure_single_step.    auto. right. auto. 
        ++  subst. left. auto.  
   + intros. inversion Heqconfig'. inversion Heqconfig. subst. inversion H. subst. ++ inversion H2. 
      ++  subst. destruct IHH_erasure with e_r sigma'0 sigma' e2' ; auto. 
      +++ subst.  inversion H_erasure.  subst.  inversion H4. subst. ++++ inversion H3. 
           ++++ subst. inversion H3. ++++ subst. right.  exists dot. exists sigma'0. apply  H_erasure_single_step; auto. 
          ++++  subst. inversion H7.  
          subst. inversion H3. inversion H3. subst. inversion H10. inversion H4. inversion H8.
        +++  right. destruct H1 as [e3]. destruct H1 as [sigma3]. exists e3. exists sigma3.  apply H_erasure_multi_step with e2' sigma'; auto. 
      ++ left. auto.  
*)

Admitted.






(*

Lemma dot_erasure_preverve_high_context : forall s h s' h' CT e e' s_r h_r ,
(*    forall T, has_type CT empty_context h e T -> *)
    Config CT e (SIGMA s h) ==> Config CT e' (SIGMA s' h') ->
    flow_to (current_label (SIGMA s h)) L_Label = false ->
    Config CT e (SIGMA s h) =e=> Config CT dot (SIGMA s_r h_r) ->
    flow_to (current_label (SIGMA s' h')) L_Label = false.



  admit.  - intros.  admit. 
  - intros.  admit. -intros.  admit.  - intros.  admit. 


  remember (Config CT t (SIGMA s h)) as config. 
  remember (Config CT t' (SIGMA s' h')) as config'. 
  generalize dependent t'. generalize dependent t.
  generalize dependent t0.
  generalize dependent t0'.
  generalize dependent T.
    generalize dependent sigma_l_e.      generalize dependent sigma_r_e. 
    generalize dependent s.      generalize dependent h.
    generalize dependent s'.      generalize dependent h'.


    induction H_reduction; intros; inversion Heqconfig; inversion Heqconfig'; subst.
    (*Tvar *)
    - inversion Heqconfig. inversion Heqconfig'. subst. inversion H_erasure_l. subst.
        rewrite H_flow in H3. inversion H3. subst.  admit.
    (*Field access context reduction *)
    - inversion Heqconfig. inversion Heqconfig'. subst.  inversion H_erasure_l. subst.
        + rewrite H_flow in H2. inversion H2.
        + subst. inversion H_erasure_r. subst. 
            ++ admit.
            ++ subst.    assert (e = dot \/  Config CT e (SIGMA s h) =e=> Config CT t0 (SIGMA s'' h'')). admit.
             destruct H. +++ subst. inversion H_reduction.
             +++ subst. 
              assert (e' = dot \/  Config CT e' (SIGMA s' h') =e=> Config CT t0' (SIGMA s''0 h''0)). admit.
             destruct H0. ++++ subst. admit.
              ++++ inversion H_typing.
            apply IHH_reduction with h' s' h s (classTy clsT) e e'; auto. 
    (*Field access object read *)
    - intros. inversion Heqconfig. inversion Heqconfig'.   subst.  inversion H_erasure_l. subst.
     + rewrite H_flow in H4. inversion H4.
     + subst. inversion H_erasure_r. subst.    
       ++ inversion H10. 
       +++ inversion H3. inversion H17. subst. destruct H14. 
       ++++ inversion H. ++++ subst. rewrite H4 in H. inversion H.
       +++ subst. inversion H7. inversion H2. subst. 
        assert (flow_to
         (current_label
            (SIGMA
               (update_current_label s0
                  (join_label lb (current_label (SIGMA s0 h')))) h')) L_Label = false).
                    unfold get_stack. induction s0.  unfold current_label in H4. unfold get_stack in H4. 
                        unfold get_current_label in H4. unfold L_Label in H4. unfold flow_to in H4. unfold subset in H4. 
                        inversion H4. 
        unfold current_label. unfold get_stack. induction a. unfold update_current_label. 
        unfold get_current_label. unfold get_stack_label. 
        apply flow_join_label with l0 lb; auto. rewrite H in H5. inversion H5. 
       ++ subst. rewrite H12. rewrite H15. 
assert (t0 = dot /\ s' = s0 /\ h' = h'0). admit.  destruct H. destruct H2. subst.
assert ( t' = null \/ exists o',  t' = ObjId o').    admit. destruct H. 
        +++ subst.  assert ( t0' = dot /\ s'0 =  (update_current_label s0
                 (join_label lb (current_label (SIGMA s0 h'0)))) /\ h'0 = h'1). admit. destruct H. destruct H2. subst.
              unfold erasure_sigma_fun. 
    assert (erasure_stack s0 =  erasure_stack
               (update_current_label s0 (join_label lb (current_label (SIGMA s0 h'1))))). 

      Lemma Erasure_equal_stack_join_label_H_context : forall s h lb s', 
        flow_to (current_label (SIGMA s h)) L_Label = false -> 
        s' = (update_current_label s (join_label lb (current_label (SIGMA s h)))) ->
        erasure_stack s = erasure_stack s'.
      Proof. intros.
        unfold flow_to in H. unfold  current_label in H. unfold get_stack in H.
        unfold get_current_label in H. induction s. unfold L_Label in H. unfold subset in H. inversion H.

        induction a.  rewrite H0. unfold  current_label. unfold update_current_label.
        unfold get_stack.   unfold get_current_label. unfold get_stack_label.
      unfold erasure_stack. unfold get_stack_label in H. 
        assert (flow_to l0 L_Label = false). unfold   flow_to. rewrite H. auto.
        assert (flow_to (join_label lb l0) L_Label = false). 
        apply flow_join_label with l0 lb; auto.  rewrite H1. rewrite H2.  fold erasure_stack. auto.
       Qed. 

        apply Erasure_equal_stack_join_label_H_context with (s:=s0) (h:=h'1) (lb:=lb) 
                (s':=(update_current_label s0 (join_label lb (current_label (SIGMA s0 h'1))))); auto. 
        rewrite H. auto.
      +++ destruct H as [o']. subst. 
      assert ( t0' = dot /\ s'0 =  (update_current_label s0
                 (join_label lb (current_label (SIGMA s0 h'0)))) /\ h'0 = h'1). admit. destruct H. destruct H2. subst.
              unfold erasure_sigma_fun. 
    assert (erasure_stack s0 =  erasure_stack
               (update_current_label s0 (join_label lb (current_label (SIGMA s0 h'1))))). 
        apply Erasure_equal_stack_join_label_H_context with (s:=s0) (h:=h'1) (lb:=lb) 
                (s':=(update_current_label s0 (join_label lb (current_label (SIGMA s0 h'1))))); auto. 
        rewrite H. auto.
  (*Method context call *)
  -   inversion Heqconfig. inversion Heqconfig'. subst.  inversion H_erasure_l. subst.
        + rewrite H_flow in H2. inversion H2.
        + subst. inversion H_erasure_r. subst. 
            ++ assert (Config CT e' (SIGMA s' h') =e=> Config CT (erasure_L_fun e') (SIGMA s'1 h'1)).
              apply erasure_L_context; auto. 
              assert (e = dot \/  Config CT e (SIGMA s h) =e=> Config CT t0 (SIGMA s'' h'')). admit.              
              destruct H0. admit. admit. 

++ subst. admit. 
  -  (*(MethodCall v id0 e) *) inversion Heqconfig. inversion Heqconfig'. subst.  inversion H_erasure_l. subst. 
      + rewrite H_flow in H4. inversion H4.
      + subst.  assert (t0 = dot \/ (exists t_r, t0 = (MethodCall dot id0 t_r) /\ 
                                                multi_step_erasure_H (Config CT e (SIGMA s h)) (Config CT t_r (SIGMA s'0 h'0))  )). admit. 
         destruct H1. subst. (* destruct IHH_reduction with h' s' h s (SIGMA s'1 h'1)  (SIGMA s'' h'') (classTy T0) (erasure_L_fun e') 
                                          dot e e'; auto.*)
         ++ inversion H9. subst. +++ inversion H3.  subst. inversion H_reduction. +++  subst. 
        inversion H7; subst. ++++ assert (Config CT v (SIGMA s h) =eH=> Config CT dot (SIGMA s h)). apply value_erasure_to_dot; auto.
        intro contra. subst. inversion H2.  assert (e'0 = dot /\ sigma' = (SIGMA s h)). apply erasure_H_deterministic with CT v (SIGMA s h); auto.
        destruct H3. subst. inversion H12. subst. +++++ assert (Config CT e (SIGMA s h) =e=> Config CT dot (SIGMA s'' h'')). admit. 
        inversion H_erasure_r. subst. ++++++ (* right side cannot be L label*) admit. 
        ++++++ subst. inversion H8. subst. inversion H3.  subst. admit. subst. inversion H24. inversion H14.  inversion H19.  
         
        +++++ subst.  (*H14*) admit. 
  ++++  subst.  (*H12*) admit.
  ++++ inversion H12. inversion H3.  inversion H8. 
  ++ subst.  destruct H1 as [t_r]. destruct H1. subst. admit. 

- (*  (MethodCall (ObjId o) meth v) => (Return body) *)
  admit. 


- (*  (MethodCall (ObjId o) meth (unlabelOpaque (v_opa_l v lb))) => (Return body) *)
admit. 

- (*NewExp cls_name *)
 inversion Heqconfig. inversion Heqconfig'. subst. inversion H_erasure_l. subst.
 + rewrite H_flow in H3. inversion H3.
 + subst. inversion H7.  subst. inversion H2. subst.  
  ++ inversion H_erasure_r.  subst. assert (flow_to (current_label (SIGMA s' h')) L_Label = false.)

Lemma simulation_H_stack_equal : forall CT t t0 t' t0' s s' h h' sigma_l_e sigma_r_e T,
      has_type CT empty_context h t T -> 
      field_wfe_heap CT h -> wfe_heap CT h -> wfe_stack CT h s ->
      flow_to (current_label (SIGMA s h)) L_Label = false ->
      Config CT t (SIGMA s h) ==> Config CT t' (SIGMA s' h') ->
      (erasure (Config CT t (SIGMA s h)) (Config CT t0 sigma_l_e)) ->
      (erasure (Config CT t' (SIGMA s' h')) (Config CT t0' sigma_r_e)) ->
      sigma_l_e = sigma_r_e.
Proof. 
    intros CT t t0 t' t0' s s' h h' sigma_l_e sigma_r_e T.
    intro H_typing. intro H_wfe_fields. 
  intro H_wfe_heap. intro H_wfe_stack. intro H_flow. intro H_reduction. 
intro H_erasure_l. intro H_erasure_r.  

remember (Config CT t (SIGMA s h)) as config. 
remember (Config CT t' (SIGMA s' h')) as config'. 
generalize dependent t'. generalize dependent t.
generalize dependent t0.
generalize dependent t0'.
generalize dependent T.
    generalize dependent sigma_l_e.      generalize dependent sigma_r_e. 
    generalize dependent s.      generalize dependent h.
    generalize dependent s'.      generalize dependent h'.

induction H_reduction; try (intros; inversion Heqconfig; inversion Heqconfig'; fail).
- admit.  - admit.  - admit.  
(*method call context rule 1 *)
- intros. inversion Heqconfig. inversion Heqconfig'. subst. 
    inversion H_erasure_l. subst. rewrite H_flow in H2. inversion H2. 
    subst.  
    inversion H_typing. subst. 
   rename t0 into e_r.

    assert (e = dot 
    \/ (e_r  = dot /\ multi_step_erasure_H (Config CT e (SIGMA s h))
       (Config CT dot (SIGMA s'0 h'0)) /\ e2 = dot) 
    \/ (exists e0, multi_step_erasure_H (Config CT e (SIGMA s h))
       (Config CT e0 (SIGMA s'0 h'0))  /\ e_r = (MethodCall e0 id0 e2))
    \/ (exists s'1 h'1, multi_step_erasure_H (Config CT e (SIGMA s h)) (Config CT dot (SIGMA s'1 h'1)) 
        /\ multi_step_erasure_H (Config CT (MethodCall dot id0 e2) (SIGMA s'1 h'1))
       (Config CT e_r (SIGMA s'0 h'0)) )). 
     apply context_erasure_method_call_obj; auto. 
   destruct H. 




    assert ((t0 = dot \/  ( flow_to (current_label (SIGMA s'0 h'0)) L_Label = true))).
    apply erasure_final with CT (MethodCall e id0 e2) (SIGMA s h) . auto. 
    destruct H. subst. inversion H_erasure_l. subst. rewrite H_flow in H10. inversion H10. 
    subst. 

    destruct IHH_reduction with h' s' h s (SIGMA s'1 h'1)  (SIGMA s'' h'') (classTy T0) (erasure_L_fun e') 
                                dot e e'; auto.

    assert (    e = dot \/ multi_step_erasure_H (Config CT e (SIGMA s h))
        (Config CT dot (SIGMA s'1 h'1))).
    admit. 
    destruct H0. auto.   subst.   inversion H_reduction. subst. 
    apply erasure_H_context with s'2 h'2; auto.


   assert (e = dot \/  exists e0, Config CT e (SIGMA s h) =e=> Config CT e0 (SIGMA s'' h'')).
   admit.
   
    destruct H1. subst. inversion H_reduction.
    destruct H1 as [e0].  
     destruct IHH_reduction with h' s' h s (SIGMA s'1 h'1)  (SIGMA s'' h'')  (classTy T0) (erasure_L_fun e') 
                                e0 e e'; auto.

    subst. 
   assert (e = dot \/   exists e0, Config CT e (SIGMA s h) =e=> Config CT e0 (SIGMA s'' h'')).
   admit.

   assert (e' = dot \/  exists e0, Config CT e' (SIGMA s' h') =e=> Config CT e0 (SIGMA s''0 h''0)).
   admit.
    destruct H. subst. inversion H_reduction.
    destruct H0.
    (* this part needs consideration*) 
    admit.
    destruct H as [e0].
    destruct H0 as [e'0].
    subst. destruct IHH_reduction with h' s' h s (SIGMA s''0 h''0)  (SIGMA s'' h'')  (classTy T0) e'0 
                                e0 e e'; auto.

(* MethodCall v meth e *)
- intros. inversion Heqconfig. inversion Heqconfig'. subst. 
    inversion H_erasure_l. subst. rewrite H_flow in H4. inversion H4. 
    subst.  
 inversion H_typing. subst. 
    inversion H_erasure_r. subst. 
    assert (Config CT e' (SIGMA s' h') =e=> Config CT (erasure_L_fun e') (SIGMA s'1 h'1)).
    apply erasure_L_context; auto. 
    assert ((t0 = dot \/  ( flow_to (current_label (SIGMA s'0 h'0)) L_Label = true))).
    apply erasure_final with CT (MethodCall v id0 e) (SIGMA s h) . auto. 
    destruct H2. subst.  inversion H_erasure_l. subst. unfold erasure_L_fun  in H22.  inversion H22.
   subst.  

    destruct IHH_reduction with h' s' h s (SIGMA s'1 h'1)  (SIGMA s'' h'') (classTy arguT) (erasure_L_fun e') 
                                dot e e'; auto.

    assert (    e = dot \/ multi_step_erasure_H (Config CT e (SIGMA s h))
        (Config CT dot (SIGMA s'2 h'2))).
    admit. 
    destruct H2. auto.   subst.   inversion H_reduction. subst. 
    apply erasure_H_context with s'2 h'2; auto.


   assert (e = dot \/  exists e0, Config CT e (SIGMA s h) =e=> Config CT e0 (SIGMA s'' h'')).
   admit.
   
    destruct H3. subst. inversion H_reduction.
    destruct H3 as [e0].  
     destruct IHH_reduction with h' s' h s (SIGMA s'1 h'1)  (SIGMA s'' h'')  (classTy arguT) (erasure_L_fun e') 
                                e0 e e'; auto.

    subst. 
   assert (e = dot \/   exists e0, Config CT e (SIGMA s h) =e=> Config CT e0 (SIGMA s'' h'')).
   admit.

   assert (e' = dot \/  exists e0, Config CT e' (SIGMA s' h') =e=> Config CT e0 (SIGMA s''0 h''0)).
   admit.
    destruct H1. subst. inversion H_reduction.
    destruct H2.
    (* this part needs consideration*) 
    admit.
    destruct H1 as [e0].
    destruct H2 as [e'0].
    subst. destruct IHH_reduction with h' s' h s (SIGMA s''0 h''0)  (SIGMA s'' h'')  (classTy arguT) e'0 
                                e0 e e'; auto.

- intros. inversion Heqconfig. inversion Heqconfig'. subst. 
    inversion H_erasure_l. inversion H11. subst. rewrite H_flow in H5. inversion H5.  
    inversion H11. subst.
    inversion H_typing. subst. 
    inversion H_erasure_r. subst.
    unfold  current_label in H15.     unfold  get_stack in H15. 
    unfold current_label in H_flow. unfold get_stack in H_flow.
    remember (get_current_label s0) as cur_lbl.
    unfold get_current_label in H15. unfold get_stack_label in H15.
    rewrite H_flow in H15.  inversion H15.

    subst. inversion H_erasure_l.  rewrite H16 in H_flow. inversion H_flow. 



assert (erasure_sigma_fun  (SIGMA
              (Labeled_frame (current_label (SIGMA s0 h0))
                 (sf_update empty_stack_frame arg_id v) :: s0) h0) = erasure_sigma_fun (SIGMA s'1 h'1)).

apply erasure_sigma_equal_after_erasure_multistep with CT (Return body) t0'; auto.
rewrite <- H27 in H22. rewrite H22. 
subst. assert   (erasure_sigma_fun (SIGMA s0 h0) = erasure_sigma_fun (SIGMA s'2 h'2)). 
apply erasure_sigma_equal_after_erasure_multistep with CT (MethodCall (ObjId o) meth v)  t0; auto.
rewrite <- H in H26. 
unfold erasure_sigma_fun. unfold erasure_stack. rewrite H16. fold erasure_stack. rewrite H26. auto. 

-  intros. inversion Heqconfig. inversion Heqconfig'. subst. unfold get_heap in H14. 
    inversion H11. inversion H14. subst.  
    inversion H_erasure_l. subst. rewrite H_flow in H3. inversion H3. subst.   
    inversion H_erasure_r. subst.
    unfold  current_label in H4.     unfold  get_stack in H4. 
    unfold current_label in H_flow. unfold get_stack in H_flow.
    remember (get_current_label s0) as cur_lbl.
    unfold get_current_label in H4. unfold get_stack_label in H4.
    assert (  flow_to (join_label lb cur_lbl)  L_Label = false).
    apply flow_join_label with cur_lbl lb; auto. 
    rewrite H in H4. inversion H4. 
    subst.

assert (erasure_sigma_fun (SIGMA s0 h') = erasure_sigma_fun (SIGMA s' h'0)).
apply erasure_sigma_equal_after_erasure_multistep with CT (MethodCall (ObjId o) meth (unlabelOpaque (v_opa_l v lb))) t0; auto.
rewrite <- H in H10. 

assert (erasure_sigma_fun (SIGMA
              (Labeled_frame (join_label lb (current_label (SIGMA s0 h')))
                 (sf_update empty_stack_frame arg_id v) :: s0) h') = erasure_sigma_fun (SIGMA s'0 h'1)).
apply erasure_sigma_equal_after_erasure_multistep with CT (Return body) t0'; auto.
rewrite <- H1 in H16. rewrite H16.


    remember (current_label (SIGMA s0 h')) as cur_lbl.
assert (  flow_to (join_label lb cur_lbl)  L_Label = false).
    apply flow_join_label with cur_lbl lb; auto.
unfold erasure_sigma_fun. unfold erasure_stack. rewrite H2. fold erasure_stack.
rewrite H10. unfold erasure_sigma_fun. auto. 

- intros. inversion Heqconfig. inversion Heqconfig'. subst. 
    inversion H10. inversion H13. subst.  
    inversion H_erasure_l. subst. rewrite H_flow in H3. inversion H3. subst.   
    inversion H_erasure_r. subst.
    unfold  current_label in H4.     unfold  get_stack in H4. 
    unfold current_label in H_flow. unfold get_stack in H_flow.
    rewrite H_flow in H4. inversion H4.

    subst.  

assert (erasure_sigma_fun (SIGMA s' h0) = erasure_sigma_fun (SIGMA s'0 h')).
apply erasure_sigma_equal_after_erasure_multistep with CT (NewExp cls_name) t0; auto.
rewrite <- H0 in H8. 

assert (erasure_sigma_fun 
            (SIGMA s'
              (add_heap_obj h0 (get_fresh_oid h0)
                 (Heap_OBJ (class_def cls_name field_defs method_defs)
                    (init_field_map field_defs empty_field_map)
                    (current_label (SIGMA s' h0)))))
                                 = erasure_sigma_fun (SIGMA s'1 h'0)).
apply erasure_sigma_equal_after_erasure_multistep with CT (ObjId (get_fresh_oid h0)) t0'; auto.
rewrite <- H1 in H14. rewrite H14.
rewrite H8. 

Lemma extend_heap_preserve_erasure : forall s h o h' CT cls F lb, 
  o = (get_fresh_oid h) ->field_wfe_heap CT h -> wfe_heap CT h ->  wfe_stack CT h s ->
  h' =  add_heap_obj h o (Heap_OBJ cls F lb) ->
  flow_to lb L_Label = false ->
  erasure_sigma_fun (SIGMA s h) =   erasure_sigma_fun (SIGMA s h').
Proof. 
(*
  intros  s h o h' CT cls F lb. 
  intro H_o. intro H_wfe_field. intro H_wfe_heap. intro H_wfe_stack.   intro H_h'. intro H_flow. 
  assert (erasure_heap h = erasure_heap h'). induction h. 
  unfold erasure_heap. rewrite H_h'. unfold  add_heap_obj. rewrite H_flow. auto. 
  unfold add_heap_obj in H_h'. remember (a::h) as h0. unfold erasure_heap.
  rewrite H_h'. rewrite H_flow. fold  erasure_heap. auto. 
  unfold erasure_sigma_fun. 
  assert (erasure_stack s h = erasure_stack s h').
  induction s. unfold erasure_stack. auto. unfold erasure_stack.
  induction a.   
  case (flow_to l0 L_Label).

  Require Import Coq.Logic.FunctionalExtensionality.

  assert (forall a, (fun x : id => erasure_obj_null (s0 x) h) a = (fun x : id => erasure_obj_null (s0 x) h') a).
  intro a. inversion H_wfe_stack. unfold empty_stack_frame. unfold erasure_obj_null. auto.
  inversion H3. 
  assert (forall x, s0 x = None \/ exists v, s0 x = Some v ).
  intro x. induction s0. right. exists a0. auto. left. auto. 
  destruct H12 with a. rewrite H13.   unfold erasure_obj_null. auto. 
  destruct H13 as [v]. inversion H0. inversion H7. subst. 
  destruct H8 with a v; auto. subst. 
  unfold  erasure_obj_null. rewrite H13. 
  auto. destruct H4 as [cls_name]. destruct H4 as [o'].  destruct H4. subst. 
  rewrite H13. unfold erasure_obj_null. 
destruct H5 as [Fo]. destruct H4 as [lo]. 
  destruct H4 as [field_defs].  destruct H4 as [method_defs]. destruct H4. 
assert ( lookup_heap_obj h o'  =  lookup_heap_obj (add_heap_obj h (get_fresh_oid h) (Heap_OBJ cls F lb)) o').
  assert (o' <> (get_fresh_oid h) ).
  intro contra. assert (lookup_heap_obj h (get_fresh_oid h) = None). 
  apply fresh_oid_heap with CT; auto. rewrite <- contra in H6. rewrite H6 in H4. 
  inversion H4. 
  unfold  lookup_heap_obj. unfold add_heap_obj.
  assert (beq_oid o' (get_fresh_oid h) = false).  apply beq_oid_not_equal. auto. 
  rewrite H9.  fold lookup_heap_obj. auto. rewrite <- H6. rewrite H4. auto. 

  apply functional_extensionality in H0. 

  rewrite H0. fold erasure_stack. inversion H_wfe_stack. auto. inversion H1.  
  assert (erasure_stack s h = erasure_stack s h'). apply IHs.  rewrite H11. auto.
   rewrite <- H11.  rewrite <- H8. auto. 

  fold  erasure_stack. inversion H_wfe_stack. unfold erasure_stack. auto.   
  subst. apply IHs. inversion H0. auto.  
  rewrite H. rewrite H0. auto. 
Qed. *)  Admitted.
  apply extend_heap_preserve_erasure with (get_fresh_oid h0) CT (class_def cls_name field_defs method_defs)
            (init_field_map field_defs empty_field_map) (current_label (SIGMA s' h0)); auto. 
  
- intros. inversion Heqconfig. inversion Heqconfig'. subst. 
    inversion H_erasure_l. subst. rewrite H_flow in H2. inversion H2. 
    subst.  
    inversion H_typing. subst.  
    inversion H_erasure_r. subst. 
    assert (Config CT e' (SIGMA s' h') =e=> Config CT (erasure_L_fun e') (SIGMA s'1 h'1)).
    apply erasure_L_context; auto. 
    assert ((t0 = dot \/  ( flow_to (current_label (SIGMA s'0 h'0)) L_Label = true))).
    apply erasure_final with CT (labelData e lb) (SIGMA s h) . auto. 
    destruct H0. subst.  inversion H_erasure_l. subst. unfold erasure_L_fun  in H16.  inversion H16.
   subst.  

    destruct IHH_reduction with h' s' h s (SIGMA s'1 h'1)  (SIGMA s'' h'') T0 (erasure_L_fun e') 
                                dot e e'; auto.

    assert (    e = dot \/ multi_step_erasure_H (Config CT e (SIGMA s h))
        (Config CT dot (SIGMA s'2 h'2))).
    admit. 
    destruct H0. auto.   subst.   inversion H_reduction. subst. 
    apply erasure_H_context with s'2 h'2; auto.


   assert (e = dot \/  exists e0, Config CT e (SIGMA s h) =e=> Config CT e0 (SIGMA s'' h'')).
   admit.
   
    destruct H1. subst. inversion H_reduction.
    destruct H1 as [e0].  
     destruct IHH_reduction with h' s' h s (SIGMA s'1 h'1)  (SIGMA s'' h'')  T0 (erasure_L_fun e') 
                                e0 e e'; auto.

    subst. 
   assert (e = dot \/   exists e0, Config CT e (SIGMA s h) =e=> Config CT e0 (SIGMA s'' h'')).
   admit.

   assert (e' = dot \/  exists e0, Config CT e' (SIGMA s' h') =e=> Config CT e0 (SIGMA s''0 h''0)).
   admit.

    destruct H. subst. inversion H_reduction.
    destruct H0.
    (* this part needs consideration: basically, the result of the reduction cannot be dot*) 
    admit. 
    destruct H as [e0].
    destruct H0 as [e'0].
    subst. destruct IHH_reduction with h' s' h s (SIGMA s''0 h''0)  (SIGMA s'' h'') T0 e'0 
                                e0 e e'; auto.

-  intros. inversion Heqconfig. inversion Heqconfig'. subst. inversion H6.  subst. 
    inversion H_erasure_l. subst. rewrite H_flow in H3. inversion H3. 

    inversion H_erasure_r. subst. rewrite H_flow in H14. inversion H14. 
    subst. 
    assert (erasure_sigma_fun  (SIGMA s' h') = erasure_sigma_fun (SIGMA s'0 h'0)).
apply erasure_sigma_equal_after_erasure_multistep with CT (labelData v lb) t0; auto.
rewrite <- H0 in H10. 

    assert (erasure_sigma_fun  (SIGMA s' h') = erasure_sigma_fun (SIGMA s'1 h'1)).
apply erasure_sigma_equal_after_erasure_multistep with CT (v_l v lb) t0'; auto.
rewrite <- H1 in H19. rewrite H19. rewrite H10.  auto. 
 
- intros. inversion Heqconfig. inversion Heqconfig'. subst. 
    inversion H_erasure_l. subst. rewrite H_flow in H2. inversion H2. 
    subst.  
    inversion H_typing. subst.  
    inversion H_erasure_r. subst. 
    assert (Config CT e' (SIGMA s' h') =e=> Config CT (erasure_L_fun e') (SIGMA s'1 h'1)).
    apply erasure_L_context; auto. 
    assert ((t0 = dot \/  ( flow_to (current_label (SIGMA s'0 h'0)) L_Label = true))).
    apply erasure_final with CT (unlabel e) (SIGMA s h) . auto. 
    destruct H0. subst.  inversion H_erasure_l. subst. unfold erasure_L_fun  in H15.  inversion H15.
   subst.  

    destruct IHH_reduction with h' s' h s (SIGMA s'1 h'1)  (SIGMA s'' h'') (LabelelTy T) (erasure_L_fun e') 
                                dot e e'; auto.

    assert (    e = dot \/ multi_step_erasure_H (Config CT e (SIGMA s h))
        (Config CT dot (SIGMA s'2 h'2))).
    admit. 
    destruct H0. auto.   subst.   inversion H_reduction. subst. 
    apply erasure_H_context with s'2 h'2; auto.


   assert (e = dot \/  exists e0, Config CT e (SIGMA s h) =e=> Config CT e0 (SIGMA s'' h'')).
   admit.
   
    destruct H1. subst. inversion H_reduction.
    destruct H1 as [e0].  
     destruct IHH_reduction with h' s' h s (SIGMA s'1 h'1)  (SIGMA s'' h'')  (LabelelTy T)  (erasure_L_fun e') 
                                e0 e e'; auto.

    subst. 
   assert (e = dot \/   exists e0, Config CT e (SIGMA s h) =e=> Config CT e0 (SIGMA s'' h'')).
   admit.

   assert (e' = dot \/  exists e0, Config CT e' (SIGMA s' h') =e=> Config CT e0 (SIGMA s''0 h''0)).
   admit.

    destruct H. subst. inversion H_reduction.
    destruct H0.
    (* this part needs consideration: basically, the result of the reduction cannot be dot*) 
    admit. 
    destruct H as [e0].
    destruct H0 as [e'0].
    subst. destruct IHH_reduction with h' s' h s (SIGMA s''0 h''0)  (SIGMA s'' h'') (LabelelTy T) e'0 
                                e0 e e'; auto.

-  intros. inversion Heqconfig. inversion Heqconfig'. subst. 
    unfold get_heap in H10. inversion H10. inversion H7.  subst. 
    inversion H_erasure_l. subst. rewrite H_flow in H2. inversion H2. 
    
    inversion H_erasure_r. subst. 

    induction s0. unfold current_label in H_flow. unfold get_stack in H_flow.
    unfold get_current_label in H_flow. unfold flow_to in H_flow. unfold L_Label in H_flow.
    unfold subset in H_flow. inversion H_flow.

    remember (current_label (SIGMA s0 h0)) as cur_lbl.     unfold current_label in H15.
    unfold get_stack in H15. induction a.    
unfold update_current_label in H15. unfold get_current_label in H15.
unfold get_stack_label in H15. unfold current_label in H_flow.
unfold get_stack in H_flow.
unfold get_current_label in H_flow. unfold get_stack_label in H_flow. 

assert (  flow_to (join_label lb l0)  L_Label = false).
    apply flow_join_label with l0 lb; auto.
rewrite H in H15. inversion H15.

subst.

inversion H_typing.
assert (erasure_sigma_fun (SIGMA s0 h0) = erasure_sigma_fun (SIGMA s' h')).
apply erasure_sigma_equal_after_erasure_multistep with CT (unlabel (v_l t' lb)) t0; auto.
rewrite <- H12 in H11. subst. 

assert (erasure_sigma_fun 
            (SIGMA
              (update_current_label s0
                 (join_label lb (current_label (SIGMA s0 h0)))) h0)
                                 = erasure_sigma_fun  (SIGMA s'0 h'0)).
apply erasure_sigma_equal_after_erasure_multistep with CT t' t0'; auto.
rewrite <- H in H20. rewrite H20.
rewrite H11. 

    remember (current_label (SIGMA s0 h0)) as cur_lbl.
assert (  flow_to (join_label lb cur_lbl)  L_Label = false).
    apply flow_join_label with cur_lbl lb; auto. induction s0.
    rewrite Heqcur_lbl in H_flow.
    unfold current_label in H_flow. unfold get_stack in H_flow.
    unfold get_current_label in H_flow. unfold flow_to in H_flow. unfold L_Label in H_flow.
    unfold subset in H_flow. inversion H_flow.
    
    induction a. unfold update_current_label. unfold erasure_sigma_fun. 
unfold erasure_stack. rewrite H0. fold erasure_stack.
    rewrite Heqcur_lbl in H_flow. unfold current_label in H_flow.
unfold get_stack in H_flow. unfold get_current_label in H_flow.
unfold get_stack_label in H_flow. rewrite H_flow. auto.

- intros. inversion Heqconfig. inversion Heqconfig'. subst. 
    inversion H_erasure_l. subst. rewrite H_flow in H2. inversion H2. 
    subst.  
    inversion H_typing. subst.  
    inversion H_erasure_r. subst. 
    assert (Config CT e' (SIGMA s' h') =e=> Config CT (erasure_L_fun e') (SIGMA s'1 h'1)).
    apply erasure_L_context; auto. 
    assert ((t0 = dot \/  ( flow_to (current_label (SIGMA s'0 h'0)) L_Label = true))).
    apply erasure_final with CT (labelOf e) (SIGMA s h) . auto. 
    destruct H0. subst.  inversion H_erasure_l. subst. unfold erasure_L_fun  in H15.  inversion H15.
   subst.  

    destruct IHH_reduction with h' s' h s (SIGMA s'1 h'1)  (SIGMA s'' h'') (LabelelTy T0) (erasure_L_fun e') 
                                dot e e'; auto.

    assert (    e = dot \/ multi_step_erasure_H (Config CT e (SIGMA s h))
        (Config CT dot (SIGMA s'2 h'2))).
    admit. 
    destruct H0. auto.   subst.   inversion H_reduction. subst. 
    apply erasure_H_context with s'2 h'2; auto.


   assert (e = dot \/  exists e0, Config CT e (SIGMA s h) =e=> Config CT e0 (SIGMA s'' h'')).
   admit.
   
    destruct H1. subst. inversion H_reduction.
    destruct H1 as [e0].  
     destruct IHH_reduction with h' s' h s (SIGMA s'1 h'1)  (SIGMA s'' h'')  (LabelelTy T0)  (erasure_L_fun e') 
                                e0 e e'; auto.

    subst. 
   assert (e = dot \/   exists e0, Config CT e (SIGMA s h) =e=> Config CT e0 (SIGMA s'' h'')).
   admit.

   assert (e' = dot \/  exists e0, Config CT e' (SIGMA s' h') =e=> Config CT e0 (SIGMA s''0 h''0)).
   admit.

    destruct H. subst. inversion H_reduction.
    destruct H0.
    (* this part needs consideration: basically, the result of the reduction cannot be dot*) 
    admit. 
    destruct H as [e0].
    destruct H0 as [e'0].
    subst. destruct IHH_reduction with h' s' h s (SIGMA s''0 h''0)  (SIGMA s'' h'') (LabelelTy T0) e'0 
                                e0 e e'; auto.

- intros. inversion Heqconfig. inversion Heqconfig'. subst. inversion H5. subst. 
    inversion H_erasure_l. subst. rewrite H_flow in H2. inversion H2. 
    subst.  
    inversion H_erasure_r. subst. rewrite H_flow in H4. inversion H4.  subst. 

    assert (erasure_sigma_fun (SIGMA s' h') = erasure_sigma_fun (SIGMA s'0 h'0)).
apply erasure_sigma_equal_after_erasure_multistep with CT (labelOf (v_l v lb)) t0; auto.
rewrite <- H in H9. 

    assert (erasure_sigma_fun (SIGMA s' h') = erasure_sigma_fun (SIGMA s'1 h'1)).
apply erasure_sigma_equal_after_erasure_multistep with CT (l lb) t0'; auto.
rewrite <- H0 in H12. rewrite H9. rewrite H12. auto.

-   intros. inversion Heqconfig. inversion Heqconfig'. subst. 
    inversion H_erasure_l. subst. rewrite H_flow in H2. inversion H2. 
    subst.  
    inversion H_typing. subst.  
    inversion H_erasure_r. subst. 
    assert (Config CT e' (SIGMA s' h') =e=> Config CT (erasure_L_fun e') (SIGMA s'1 h'1)).
    apply erasure_L_context; auto. 
    assert ((t0 = dot \/  ( flow_to (current_label (SIGMA s'0 h'0)) L_Label = true))).
    apply erasure_final with CT (unlabelOpaque e) (SIGMA s h) . auto. 
    destruct H0. subst.  inversion H_erasure_l. subst. unfold erasure_L_fun  in H15.  inversion H15.
   subst.  

    destruct IHH_reduction with h' s' h s (SIGMA s'1 h'1)  (SIGMA s'' h'') (OpaqueLabeledTy T) (erasure_L_fun e') 
                                dot e e'; auto.

    assert (    e = dot \/ multi_step_erasure_H (Config CT e (SIGMA s h))
        (Config CT dot (SIGMA s'2 h'2))).
    admit. 
    destruct H0. auto.   subst.   inversion H_reduction. subst. 
    apply erasure_H_context with s'2 h'2; auto.


   assert (e = dot \/  exists e0, Config CT e (SIGMA s h) =e=> Config CT e0 (SIGMA s'' h'')).
   admit.
   
    destruct H1. subst. inversion H_reduction.
    destruct H1 as [e0].  
     destruct IHH_reduction with h' s' h s (SIGMA s'1 h'1)  (SIGMA s'' h'') (OpaqueLabeledTy T) (erasure_L_fun e') 
                                e0 e e'; auto.

    subst. 
   assert (e = dot \/   exists e0, Config CT e (SIGMA s h) =e=> Config CT e0 (SIGMA s'' h'')).
   admit.

   assert (e' = dot \/  exists e0, Config CT e' (SIGMA s' h') =e=> Config CT e0 (SIGMA s''0 h''0)).
   admit.

    destruct H. subst. inversion H_reduction.
    destruct H0.
    (* this part needs consideration: basically, the result of the reduction cannot be dot*) 
    admit. 
    destruct H as [e0].
    destruct H0 as [e'0].
    subst. destruct IHH_reduction with h' s' h s (SIGMA s''0 h''0)  (SIGMA s'' h'') (OpaqueLabeledTy T) e'0 
                                e0 e e'; auto.

-  intros. inversion Heqconfig. inversion Heqconfig'. subst. 
    unfold get_heap in H9. inversion H9. inversion H6.  subst. 
    inversion H_erasure_l. subst. rewrite H_flow in H2. inversion H2. 
    
    inversion H_erasure_r. subst. 
    induction s0. unfold current_label in H_flow. unfold get_stack in H_flow.
    unfold get_current_label in H_flow. unfold flow_to in H_flow. unfold L_Label in H_flow.
    unfold subset in H_flow. inversion H_flow.

    remember (current_label (SIGMA s0 h0)) as cur_lbl.     unfold current_label in H14.
    unfold get_stack in H14. induction a.    
unfold update_current_label in H14. unfold get_current_label in H14.
unfold get_stack_label in H14. unfold current_label in H_flow.
unfold get_stack in H_flow.
unfold get_current_label in H_flow. unfold get_stack_label in H_flow. 

assert (  flow_to (join_label lb l0)  L_Label = false).
    apply flow_join_label with l0 lb; auto.
rewrite H in H14. inversion H14.

subst.
inversion H_typing.
assert (erasure_sigma_fun (SIGMA s0 h0) = erasure_sigma_fun (SIGMA s' h')).
apply erasure_sigma_equal_after_erasure_multistep with CT (unlabelOpaque (v_opa_l t' lb))  t0; auto.
rewrite <- H11 in H10. subst. 

assert (erasure_sigma_fun 
            (SIGMA
              (update_current_label s0
                 (join_label lb (current_label (SIGMA s0 h0)))) h0)
                                 = erasure_sigma_fun  (SIGMA s'0 h'0)).
apply erasure_sigma_equal_after_erasure_multistep with CT t' t0'; auto.
rewrite <- H in H19. rewrite H19.
rewrite H10. 

    remember (current_label (SIGMA s0 h0)) as cur_lbl.
assert (  flow_to (join_label lb cur_lbl)  L_Label = false).
    apply flow_join_label with cur_lbl lb; auto. induction s0.
    rewrite Heqcur_lbl in H_flow.
    unfold current_label in H_flow. unfold get_stack in H_flow.
    unfold get_current_label in H_flow. unfold flow_to in H_flow. unfold L_Label in H_flow.
    unfold subset in H_flow. inversion H_flow.
    
    induction a. unfold update_current_label. unfold erasure_sigma_fun. 
unfold erasure_stack. rewrite H0. fold erasure_stack.
    rewrite Heqcur_lbl in H_flow. unfold current_label in H_flow.
unfold get_stack in H_flow. unfold get_current_label in H_flow.
unfold get_stack_label in H_flow. rewrite H_flow. auto.

-  intros. inversion Heqconfig. inversion Heqconfig'. subst. 
    inversion H_erasure_l. subst. rewrite H_flow in H3. inversion H3. 
    subst.  
    inversion H_typing. subst.  
    inversion H_erasure_r. subst. 
    assert (Config CT e' (SIGMA s' h') =e=> Config CT (erasure_L_fun e') (SIGMA s'1 h'1)).
    apply erasure_L_context; auto. 
    assert ((t0 = dot \/  ( flow_to (current_label (SIGMA s'0 h'0)) L_Label = true))).
    apply erasure_final with CT (opaqueCall e) (SIGMA s h) . auto. 
    destruct H1. subst.  inversion H_erasure_l. subst. unfold erasure_L_fun  in H16.  inversion H16.
   subst.  

    destruct IHH_reduction with h' s' h s (SIGMA s'1 h'1)  (SIGMA s'' h'') T0 (erasure_L_fun e') 
                                dot e e'; auto.

    assert (    e = dot \/ multi_step_erasure_H (Config CT e (SIGMA s h))
        (Config CT dot (SIGMA s'2 h'2))).
    admit. 
    destruct H1. auto.   subst.   inversion H_reduction. subst. 
    apply erasure_H_context with s'2 h'2; auto.

   assert (e = dot \/  exists e0, Config CT e (SIGMA s h) =e=> Config CT e0 (SIGMA s'' h'')).
   admit.
   
    destruct H2. subst. inversion H_reduction.
    destruct H2 as [e0].  
     destruct IHH_reduction with h' s' h s (SIGMA s'1 h'1)  (SIGMA s'' h'') T0 (erasure_L_fun e') 
                                e0 e e'; auto.

    subst. 
   assert (e = dot \/   exists e0, Config CT e (SIGMA s h) =e=> Config CT e0 (SIGMA s'' h'')).
   admit.

   assert (e' = dot \/  exists e0, Config CT e' (SIGMA s' h') =e=> Config CT e0 (SIGMA s''0 h''0)).
   admit.

    destruct H0. subst. inversion H_reduction.
    destruct H1.
    (* this part needs consideration: basically, the result of the reduction cannot be dot*) 
    admit. 
    destruct H0 as [e0].
    destruct H1 as [e'0].
    subst. destruct IHH_reduction with h' s' h s (SIGMA s''0 h''0)  (SIGMA s'' h'') T0 e'0 
                                e0 e e'; auto.

- intros. inversion Heqconfig. inversion Heqconfig'. subst. 
    inversion H_erasure_l. subst. rewrite H_flow in H2. inversion H2. 
    subst.  
    inversion H_typing. subst.  
    inversion H_erasure_r. subst. 
    assert (Config CT e' (SIGMA s' h') =e=> Config CT (erasure_L_fun e') (SIGMA s'1 h'1)).
    apply erasure_L_context; auto. 
    assert ((t0 = dot \/  ( flow_to (current_label (SIGMA s'0 h'0)) L_Label = true))).
    apply erasure_final with CT (opaqueCall (Return e)) (SIGMA s h) . auto. 
    destruct H0. subst.  inversion H_erasure_l. subst. unfold erasure_L_fun  in H15.  inversion H15.
   subst.  inversion H5.

    destruct IHH_reduction with h' s' h s (SIGMA s'1 h'1)  (SIGMA s'' h'') T0 (erasure_L_fun (e')) 
                                dot e e'; auto.

    assert (    e = dot \/ multi_step_erasure_H (Config CT e (SIGMA s h))
        (Config CT dot (SIGMA s'2 h'2))).
    admit. 
    destruct H17. auto.   subst.   inversion H_reduction. subst. 
    apply erasure_H_context with s'2 h'2; auto.

   assert (e = dot \/  exists e0, Config CT e (SIGMA s h) =e=> Config CT e0 (SIGMA s'' h'')).
   admit.
   
    destruct H1. subst. inversion H_reduction.
    destruct H1 as [e0].   inversion H5.
     destruct IHH_reduction with h' s' h s (SIGMA s'1 h'1)  (SIGMA s'' h'') T0 (erasure_L_fun e') 
                                e0 e e'; auto.

    subst. 
   assert (e = dot \/   exists e0, Config CT e (SIGMA s h) =e=> Config CT e0 (SIGMA s'' h'')).
   admit.

   assert (e' = dot \/  exists e0, Config CT e' (SIGMA s' h') =e=> Config CT e0 (SIGMA s''0 h''0)).
   admit.

    destruct H. subst. inversion H_reduction.
    destruct H0.
    (* this part needs consideration: basically, the result of the reduction cannot be dot*) 
    admit. 
    destruct H as [e0].
    destruct H0 as [e'0].
    subst. destruct IHH_reduction with h' s' h s (SIGMA s''0 h''0)  (SIGMA s'' h'') T0 e'0 
                                e0 e e'; auto. inversion H5. auto.

-  intros. inversion Heqconfig. inversion Heqconfig'. subst. 
    inversion H7. subst. 
    inversion H_erasure_l. subst. rewrite H_flow in H3. inversion H3. 
    
    inversion H_erasure_r. subst. rewrite H_flow in H14. inversion H14.
    subst. 

    assert (erasure_sigma_fun (SIGMA s' h') = erasure_sigma_fun (SIGMA s'0 h'0)).
apply erasure_sigma_equal_after_erasure_multistep with CT (opaqueCall v)  t0; auto.
rewrite <- H0 in H10. subst. 

    assert (erasure_sigma_fun (SIGMA s' h') = erasure_sigma_fun (SIGMA s'1 h'1)).
apply erasure_sigma_equal_after_erasure_multistep with CT (v_opa_l v (current_label (SIGMA s' h')))  t0'; auto.
rewrite <- H1 in H19. subst. rewrite H19. rewrite H10. auto.

- intros. inversion Heqconfig. inversion Heqconfig'. subst. 
    inversion H11. subst. inversion H8. subst. 
    inversion H_erasure_l. subst. rewrite H_flow in H3. inversion H3. 
    inversion H_erasure_r. subst.
    assert (erasure_sigma_fun (SIGMA (lsf :: s'0) h0) = erasure_sigma_fun (SIGMA s' h')).
apply erasure_sigma_equal_after_erasure_multistep with CT (opaqueCall (Return v))  t0; auto.
rewrite H12. rewrite H21. rewrite <- H.

unfold erasure_sigma_fun.  unfold erasure_stack. unfold current_label in H_flow.
unfold get_stack in H_flow. unfold get_current_label in H_flow. induction lsf.
unfold get_stack_label in H_flow. rewrite H_flow. fold erasure_stack. auto.

subst.

    assert (erasure_sigma_fun (SIGMA (lsf :: s'0) h0) = erasure_sigma_fun (SIGMA s' h')).
apply erasure_sigma_equal_after_erasure_multistep with CT (opaqueCall (Return v))  t0; auto.
rewrite <- H in H12.

    assert (erasure_sigma_fun  (SIGMA s'0 h0) = erasure_sigma_fun (SIGMA s'1 h'0)).
apply erasure_sigma_equal_after_erasure_multistep with 
        CT (v_opa_l v (current_label (SIGMA (lsf :: s'0) h0)))  t0'; auto.
rewrite <- H0 in H21. rewrite H12. rewrite H21.

unfold erasure_sigma_fun.  unfold erasure_stack. unfold current_label in H_flow.
unfold get_stack in H_flow. unfold get_current_label in H_flow. induction lsf.
unfold get_stack_label in H_flow. rewrite H_flow. fold erasure_stack. auto.

-intros. inversion Heqconfig. inversion Heqconfig'. subst. 
    inversion H_erasure_l. subst. rewrite H_flow in H2. inversion H2. 
    subst.  
    inversion H_typing. subst.  
    inversion H_erasure_r. subst. 
    assert (Config CT e' (SIGMA s' h') =e=> Config CT (erasure_L_fun e') (SIGMA s'1 h'1)).
    apply erasure_L_context; auto. 
    assert ((t0 = dot \/  ( flow_to (current_label (SIGMA s'0 h'0)) L_Label = true))).
    apply erasure_final with CT  (Assignment id0 e) (SIGMA s h) . auto. 
    destruct H0. subst.  inversion H_erasure_l. subst. unfold erasure_L_fun  in H16.  inversion H16.
   subst.  inversion H6.   inversion H6. subst. inversion H6.

- intros. inversion Heqconfig. inversion Heqconfig'. subst. 
    inversion H_erasure_l. inversion H6. subst. rewrite H_flow in H3. inversion H3. 

    inversion Heqconfig'. subst.      inversion H_erasure_r. subst. 
    assert (erasure_sigma_fun  (SIGMA s h') = erasure_sigma_fun (SIGMA s' h'0)).
apply erasure_sigma_equal_after_erasure_multistep with 
        CT (Assignment id0 v)  t0; auto. rewrite H11.  rewrite <- H0. inversion H6. subst. 
        rewrite H14. induction s0. unfold update_stack_top. auto.       induction a. 
        unfold update_stack_top. unfold  labeled_frame_update.
        unfold erasure_sigma_fun. unfold erasure_stack.  unfold current_label in H_flow.
        unfold get_stack in H_flow. unfold get_current_label in H_flow.  unfold get_stack_label in H_flow.  
        rewrite H_flow.  fold erasure_stack. auto. 

    subst. 
    assert (erasure_sigma_fun  (SIGMA s h') = erasure_sigma_fun (SIGMA s' h'0)).
apply erasure_sigma_equal_after_erasure_multistep with 
        CT (Assignment id0 v)  t0; auto. rewrite H11. rewrite <- H0. 

    assert (erasure_sigma_fun (SIGMA (update_stack_top s id0 v) h') = erasure_sigma_fun (SIGMA s'0 h'1)).
apply erasure_sigma_equal_after_erasure_multistep with CT Skip  t0'; auto.
rewrite <- H1 in H14. rewrite H14. inversion H6. subst. 
    induction s0. unfold update_stack_top. auto.       induction a. 
        unfold update_stack_top. unfold  labeled_frame_update.
        unfold erasure_sigma_fun. unfold erasure_stack.  unfold current_label in H_flow.
        unfold get_stack in H_flow. unfold get_current_label in H_flow.  unfold get_stack_label in H_flow.  
        rewrite H_flow.  fold erasure_stack. auto.

- intros. inversion Heqconfig. inversion Heqconfig'. subst. 
    inversion H_erasure_l. subst. rewrite H_flow in H2. inversion H2. 
    subst.  
    inversion H_typing. subst.  
    inversion H_erasure_r. subst. 
    assert (Config CT e1' (SIGMA s' h') =e=> Config CT (erasure_L_fun e1') (SIGMA s'1 h'1)).
    apply erasure_L_context; auto. 
    assert ((t0 = dot \/  ( flow_to (current_label (SIGMA s'0 h'0)) L_Label = true))).
    apply erasure_final with CT (FieldWrite e1 f e2)  (SIGMA s h) . auto. 
    destruct H0. subst.  inversion H_erasure_l. subst. unfold erasure_L_fun  in H18.  inversion H18.
   subst. 

    destruct IHH_reduction with h' s' h s (SIGMA s'1 h'1)  (SIGMA s'' h'') (classTy clsT) (erasure_L_fun (e1')) 
                                dot e1 e1'; auto.

    assert (    e1 = dot \/ multi_step_erasure_H (Config CT e1 (SIGMA s h))
        (Config CT dot (SIGMA s'2 h'2))).
    admit. 
    destruct H0. auto.   subst.   inversion H_reduction. subst. 
    apply erasure_H_context with s'2 h'2; auto.

   assert (e1 = dot \/  exists e0, Config CT e1 (SIGMA s h) =e=> Config CT e0 (SIGMA s'' h'')).
   admit.
   
    destruct H1. subst. inversion H_reduction.
    destruct H1 as [e0]. 
     destruct IHH_reduction with h' s' h s (SIGMA s'1 h'1)  (SIGMA s'' h'') (classTy clsT) (erasure_L_fun e1') 
                                e0 e1 e1'; auto.

    subst. 
   assert (e1 = dot \/   exists e0, Config CT e1 (SIGMA s h) =e=> Config CT e0 (SIGMA s'' h'')).
   admit.

   assert (e1' = dot \/  exists e0, Config CT e1' (SIGMA s' h') =e=> Config CT e0 (SIGMA s''0 h''0)).
   admit.

    destruct H. subst. inversion H_reduction.
    destruct H0.
    (* this part needs consideration: basically, the result of the reduction cannot be dot*) 
    admit. 
    destruct H as [e0].
    destruct H0 as [e'0].
    subst. destruct IHH_reduction with h' s' h s (SIGMA s''0 h''0)  (SIGMA s'' h'') (classTy clsT)  e'0 
                                e0 e1 e1'; auto. 

- intros. inversion Heqconfig. inversion Heqconfig'. subst. 
    inversion H_erasure_l. subst. rewrite H_flow in H4. inversion H4. 
    subst.  
    inversion H_typing. subst.  
    inversion H_erasure_r. subst. 
    assert (Config CT e2' (SIGMA s' h') =e=> Config CT (erasure_L_fun e2') (SIGMA s'1 h'1)).
    apply erasure_L_context; auto. 
    assert ((t0 = dot \/  ( flow_to (current_label (SIGMA s'0 h'0)) L_Label = true))).
    apply erasure_final with CT (FieldWrite v f e2)  (SIGMA s h) . auto. 
    destruct H2. subst.  inversion H_erasure_l. subst. unfold erasure_L_fun  in H20.  inversion H20.
   subst. 

    destruct IHH_reduction with h' s' h s (SIGMA s'1 h'1)  (SIGMA s'' h'') (classTy cls') (erasure_L_fun (e2')) 
                                dot e2 e2'; auto.

    assert (    e2 = dot \/ multi_step_erasure_H (Config CT e2 (SIGMA s h))
        (Config CT dot (SIGMA s'2 h'2))).
    admit. 
    destruct H2. auto.   subst.   inversion H_reduction. subst. 
    apply erasure_H_context with s'2 h'2; auto.

   assert (e2 = dot \/  exists e0, Config CT e2 (SIGMA s h) =e=> Config CT e0 (SIGMA s'' h'')).
   admit.
   
    destruct H3. subst. inversion H_reduction.
    destruct H3 as [e0]. 
     destruct IHH_reduction with h' s' h s (SIGMA s'1 h'1)  (SIGMA s'' h'') (classTy cls') (erasure_L_fun e2') 
                                e0 e2 e2'; auto.

    subst. 
   assert (e2 = dot \/   exists e0, Config CT e2 (SIGMA s h) =e=> Config CT e0 (SIGMA s'' h'')).
   admit.

   assert (e2' = dot \/  exists e0, Config CT e2' (SIGMA s' h') =e=> Config CT e0 (SIGMA s''0 h''0)).
   admit.

    destruct H1. subst. inversion H_reduction.
    destruct H2.
    (* this part needs consideration: basically, the result of the reduction cannot be dot*) 
    admit. 
    destruct H1 as [e0].
    destruct H2 as [e'0].
    subst. destruct IHH_reduction with h' s' h s (SIGMA s''0 h''0)  (SIGMA s'' h'') (classTy cls')  e'0 
                                e0 e2 e2'; auto.

- intros. inversion Heqconfig. inversion Heqconfig'. subst.  inversion H9. subst. 
    inversion Heqconfig'. subst. 
    inversion H_erasure_l. subst. rewrite H_flow in H3. inversion H3. 
    subst.  
    inversion H_erasure_r. subst. 
inversion H8. destruct H14. subst. inversion H2. subst. admit.  (*this is the tricky one*)
   subst. inversion H2. intuition. assert (exists o0 : oid, ObjId o = ObjId o0). exists o. auto. intuition. 
   subst.  unfold current_label in H_flow. unfold get_stack in H_flow. 
   unfold current_label in H14. unfold get_stack in H14.  rewrite H_flow in H14. inversion H14.  subst. 

   inversion H7.  subst. 
   intuition. assert (exists o0 : oid, ObjId o = ObjId o0). exists o. auto. intuition. 
   subst. inversion H16. inversion H2. inversion H13.  subst. 
   inversion H14. subst. inversion H2.  subst. 
    rewrite H11. rewrite H15. 
 
   subst. inversion H7. subst. inversion H17.  inversion H2. inversion H13. 
assert (erasure_sigma_fun  (SIGMA s' h0) = erasure_sigma_fun (SIGMA s'0 h')).
apply erasure_sigma_equal_after_erasure_multistep with 
        CT (FieldWrite (ObjId o) f v) t0; auto. rewrite H11. rewrite <- H. rewrite H15. 


Admitted. 
*)


Reserved Notation "c '==l>' c'"
  (at level 40, c' at level 39).

Inductive l_reduction : config -> config -> Prop :=
    | L_reduction : forall c1 c2 c2_r, 
      c1 ==> c2 ->
      c2 =e=> c2_r ->
      l_reduction c1 c2_r
where "c '==l>' c'" := (l_reduction c c').




Inductive L_equivalence_object : oid -> heap -> oid -> heap -> Prop :=
   | object_equal_H : forall o1 o2 h1 h2 lb1 lb2 cls1 cls2 F1 F2,
        Some (Heap_OBJ cls1 F1 lb1) = lookup_heap_obj h1 o1 -> 
        Some (Heap_OBJ cls2 F2 lb2) = lookup_heap_obj h2 o2 ->
        flow_to lb1 L_Label = false ->
        flow_to lb2 L_Label = false ->
        L_equivalence_object o1 h1 o2 h2
   | object_equal_L : forall o1 o2 h1 h2 lb1 lb2 cls1 cls2 F1 F2,
        Some (Heap_OBJ cls1 F1 lb1) = lookup_heap_obj h1 o1 -> 
        Some (Heap_OBJ cls2 F2 lb2) = lookup_heap_obj h2 o2 ->
        flow_to lb1 L_Label = true ->
        flow_to lb2 L_Label = true ->
        ((cls1 = cls2) /\ (lb1 = lb2) /\ 
            (forall fname, F1 fname = Some null -> F2 fname = Some null ) /\
            (forall fname fo1 fo2, F1 fname = Some (ObjId fo1) -> F2 fname = Some (ObjId fo2) ->
              L_equivalence_object fo1 h1 fo2 h2 )
        )-> L_equivalence_object o1 h1 o2 h2.

Inductive L_equivalence_tm : tm -> heap -> tm -> heap -> Prop :=
  | L_equivalence_tm_eq_Tvar : forall id1 id2 h1 h2, 
      id1 = id2 -> L_equivalence_tm (Tvar id1) h1 (Tvar id2) h2
  | L_equivalence_tm_eq_null : forall h1 h2,  
      L_equivalence_tm null h1 null h2
  | L_equivalence_tm_eq_fieldaccess : forall e1 e2 f h1 h2,
      L_equivalence_tm e1 h1 e2 h2 ->
      L_equivalence_tm (FieldAccess e1 f) h1 (FieldAccess e2 f) h2
  | L_equivalence_tm_eq_methodcall : forall e1 e2 a1 a2 meth h1 h2,
      L_equivalence_tm e1 h1 e2 h2->
      L_equivalence_tm a1 h1 a2 h2 ->
      L_equivalence_tm (MethodCall e1 meth a1) h1 (MethodCall e1 meth a1) h2
  | L_equivalence_tm_eq_newexp : forall cls1 cls2 h1 h2,
      cls1 = cls2 ->
      L_equivalence_tm (NewExp cls1) h1 (NewExp cls2) h2
  | L_equivalence_tm_eq_label : forall l1 l2 h1 h2, 
      l1 = l2 ->
      L_equivalence_tm (l l1) h1 (l l2) h2
  | L_equivalence_tm_eq_labelData : forall e1 e2 l1 l2 h1 h2,
      L_equivalence_tm e1 h1 e2 h2->
      l1 = l2 ->
      L_equivalence_tm (labelData e1 l1) h1 (labelData e2 l2) h2
  | L_equivalence_tm_eq_unlabel : forall e1 e2 h1 h2,
      L_equivalence_tm e1 h1 e2 h2->
      L_equivalence_tm (unlabel e1) h1 (unlabel e2) h2
  | L_equivalence_tm_eq_labelOf : forall e1 e2 h1 h2,
      L_equivalence_tm e1 h1 e2 h2 ->
      L_equivalence_tm (labelOf e1) h1 (labelOf e2) h2
  | L_equivalence_tm_eq_unlabelOpaque : forall e1 e2 h1 h2,
      L_equivalence_tm e1 h1 e2 h2 ->
      L_equivalence_tm (unlabelOpaque e1) h1 (unlabelOpaque e2) h2
  | L_equivalence_tm_eq_opaqueCall : forall e1 e2 h1 h2,
      L_equivalence_tm e1 h1 e2 h2 ->
      L_equivalence_tm (opaqueCall e1) h1 (opaqueCall e2) h2
  | L_equivalence_tm_eq_skip : forall h1 h2,
      L_equivalence_tm Skip h1 Skip h2
  | L_equivalence_tm_eq_Assignment : forall e1 e2 x1 x2 h1 h2, 
      L_equivalence_tm e1 h1 e2 h2 ->
      x1 = x2->
      L_equivalence_tm (Assignment x1 e1) h1 (Assignment x2 e2) h2
  | L_equivalence_tm_eq_FieldWrite : forall e1 e2 f1 f2 e1' e2' h1 h2,
      L_equivalence_tm e1 h1 e2 h2 ->
      f1 = f2 ->
      L_equivalence_tm e1' h1 e2' h2 ->
      L_equivalence_tm (FieldWrite e1 f1 e1') h1 (FieldWrite e2 f2 e2') h2
  | L_equivalence_tm_eq_if : forall s1 s2 s1' s2' id1 id2 id1' id2' h1 h2,
      L_equivalence_tm s1 h1 s1' h2 ->
      L_equivalence_tm s2 h1 s2' h2 ->
      id1 = id1' ->
      id2 = id2' ->
      L_equivalence_tm (If id1 id2 s1 s2) h1 (If id1' id2' s1' s2') h2
  | L_equivalence_tm_eq_Sequence : forall s1 s2 s1' s2' h1 h2, 
      L_equivalence_tm s1 h1 s1' h2 ->
      L_equivalence_tm s2 h1 s2' h2->
      L_equivalence_tm (Sequence s1 s2) h1 (Sequence s1' s2') h2
  | L_equivalence_tm_eq_sequence_dot1 : forall s1 s2 h1 h2, 
      L_equivalence_tm s1 h1 s2 h2 ->
      L_equivalence_tm s1 h1 (Sequence dot s2) h2
  | L_equivalence_tm_eq_sequence_dot2 : forall s1 s2 h1 h2, 
      L_equivalence_tm s1 h1 s2 h2 ->
      L_equivalence_tm (Sequence dot s1) h1 s2 h2
  | L_equivalence_tm_eq_return : forall e1 e2 h1 h2,  
      L_equivalence_tm e1 h1 e2 h2 ->
      L_equivalence_tm (Return e1) h1 (Return e2) h2
  | L_equivalence_tm_eq_object : forall o1 o2 h1 h2, 
      L_equivalence_object o1 h1 o2 h2 ->
      L_equivalence_tm (ObjId o1) h1 (ObjId o2) h2
  | L_equivalence_tm_eq_v_l_L : forall lb e1 e2 h1 h2, 
      flow_to lb L_Label = true ->
      L_equivalence_tm e1 h1 e2 h2 ->
      L_equivalence_tm (v_l e1 lb) h1 (v_l e2 lb) h2
  | L_equivalence_tm_eq_v_l_H : forall e1 e2 l1 l2 h1 h2, 
      flow_to l1 L_Label = false ->
      flow_to l2 L_Label = false ->
      L_equivalence_tm (v_l e1 l1) h1 (v_l e2 l2) h2
  | L_equivalence_tm_eq_v_opa_l_L : forall lb e1 e2 h1 h2, 
      flow_to lb L_Label = true ->
      L_equivalence_tm e1 h1 e2 h2 ->
      L_equivalence_tm (v_opa_l e1 lb) h1 (v_opa_l e2 lb) h2
  | L_equivalence_tm_eq_v_opa_l_H : forall e1 e2 l1 l2 h1 h2, 
      flow_to l1 L_Label = false ->
      flow_to l2 L_Label = false ->
      L_equivalence_tm (v_opa_l e1 l1) h1 (v_opa_l e2 l2) h2
  | L_equivalence_tm_eq_dot : forall h1 h2,
      L_equivalence_tm (dot) h1 (dot) h2.



Inductive multi_step_reduction : config -> config -> Prop := 
  | multi_reduction_refl : forall config , multi_step_reduction config config
  | multi_reduction_step : forall c1 c2 c3, 
                    reduction c1 c2 ->
                    multi_step_reduction c2 c3 ->
                    multi_step_reduction c1 c3.

Inductive multi_step : Class_table -> tm -> Sigma -> Class_table-> tm -> Sigma -> Prop := 
  | multi_refl : forall t ct sigma , multi_step ct t sigma ct t sigma
  | multi_reduction : forall t1 t2 t3 sigma1 sigma2 sigma3 ct, 
                    reduction (Config ct t1 sigma1) (Config ct t2 sigma2) ->
                    multi_step ct t2 sigma2 ct t3 sigma3 ->
                    multi_step ct t1 sigma1 ct t3 sigma3.

Notation "c1 '==>*' c2" := (multi_step_reduction c1 c2) (at level 40).



Inductive multi_step_l_reduction : config -> config -> Prop := 
  | multi_reduction_l_refl : forall config , multi_step_l_reduction config config
  | multi_reduction_l_step : forall c1 c2 c3, 
                    l_reduction c1 c2 ->
                    multi_step_l_reduction c2 c3 ->
                    multi_step_l_reduction c1 c3.

Notation "c1 '==>L*' c2" := (multi_step_l_reduction c1 c2) (at level 40).



Theorem L_reduction_determinacy: forall ct t sigma t1 sigma1 t2 sigma2, 
     l_reduction (Config ct t sigma) (Config ct t1 sigma1) ->
     l_reduction (Config ct t sigma) (Config ct t2 sigma2) -> 
      t1 = t2 /\ sigma1 = sigma2. 
Proof.
Admitted. 

Lemma normal_form_prime : forall v sigma ct, value v->
(forall v' sigma', Config ct v sigma ==> Config ct v' sigma' -> False).
Proof. 
  intros v sigma ct. intro H_v. intros.
  inversion H_v; try (rewrite <-H0 in H; inversion H; fail); 
  try (rewrite <-H1 in H; inversion H).
Qed.

Lemma normal_form_L_reduction : forall v sigma ct, value v->
(forall v' sigma', Config ct v sigma ==l> Config ct v' sigma' -> False).
Proof. 
  intros v sigma ct. intro H_v. intros.
  induction H_v; 
  try (subst; inversion H; subst; inversion H0; fail).
Qed.

Lemma ct_consist : forall CT CT' t t' sigma sigma', 
  Config CT t sigma ==> Config CT' t' sigma' -> CT = CT'. 
 Proof.
   intros. induction t; inversion H; auto. 
  Qed. 

Lemma ct_erasure : forall CT CT' t t' sigma sigma', 
  Config CT t sigma =e=> Config CT' t' sigma' -> CT = CT'. 
Proof. intros CT CT' t t' sigma sigma'. intro H.
   inversion H. subst. auto. auto. 
Qed. 


Lemma l_reduction_ct_consist : forall CT CT' t t' sigma sigma', 
  Config CT t sigma ==l> Config CT' t' sigma' -> CT = CT'. 
 Proof.
   intros. inversion H. subst. induction c2. assert (CT = c).
   apply ct_consist with t t0 sigma s. auto. subst. apply ct_erasure with t0 t' s sigma'. auto. 
   inversion H1. 
  Qed. 

Theorem L_reduction_multistep_determinacy: forall ct t sigma v1 sigma1 v2 sigma2, 
     multi_step_l_reduction (Config ct t sigma) (Config ct v1 sigma1) ->
     multi_step_l_reduction (Config ct t sigma) (Config ct v2 sigma2) -> 
     value v1 -> value v2 ->
      v1 = v2 /\ sigma1 = sigma2. 
Proof.
  intros ct t sigma v1 sigma1 v2 sigma2 Hy1 Hy2.
  intro Hv1. intro Hv2.  
  remember (Config ct v1 sigma1) as v1_config. 
  remember (Config ct t sigma) as config. 
  generalize dependent v1.      generalize dependent v2.
  generalize dependent sigma.      generalize dependent sigma1.
  generalize dependent sigma2. generalize dependent t. 
  induction Hy1.
  - intros. subst. inversion Heqv1_config. subst. 
    inversion Hy2. auto. inversion H. subst. inversion Hv1; subst; inversion H3. 
- intros. subst.  inversion Hy2. subst. inversion H.  subst. inversion Hv2; subst; inversion H0. 
  subst.  induction c2.  induction c0. 
  assert (ct = c). apply l_reduction_ct_consist with t  t0 sigma s. auto. 
  assert (ct = c0). apply l_reduction_ct_consist with t  t1 sigma s0. auto.
  subst. assert (t0 = t1 /\ s = s0). apply L_reduction_determinacy with c0 t sigma. auto. auto. 
  destruct H2. subst. apply IHHy1 with t1 s0; auto. inversion H0. inversion H3.  inversion H. 
  inversion H3. Qed. 


Lemma simulation_L : forall CT t t0 t' t0' sigma_l sigma_r sigma_l_e sigma_r_e s h,
      sigma_l = SIGMA s h ->
      field_wfe_heap CT h -> wfe_heap CT h -> wfe_stack CT h s ->
      flow_to (current_label sigma_l) L_Label = true ->
      Config CT t sigma_l ==> Config CT t' sigma_r ->
      (erasure (Config CT t sigma_l) (Config CT t0 sigma_l_e)) ->
      (erasure (Config CT t' sigma_r) (Config CT t0' sigma_r_e)) ->
      l_reduction (Config CT t0 sigma_l_e) (Config CT t0' sigma_r_e).
Proof. 
  intros CT t t0 t' t0' sigma_l sigma_r sigma_l_e sigma_r_e s h.
  intro H_sigma. intro H_wfe_fields. 
  intro H_wfe_heap. intro H_wfe_stack. intro H_flow. intro H_reduction. 
  (*intro H_erasure_sigma_l.  *) intro H_erasure_l. intro H_erasure_r.  
    generalize dependent t0.     generalize dependent t0'. induction H_reduction; subst.
 
(*Tvar *)
  (*- admit.  inversion H_erasure_l.
      + subst. inversion H_wfe_stack. rewrite <- H4 in H3. inversion H3. 
          rewrite <- H9 in H7.  inversion H7.
        subst. inversion H2. inversion H. inversion H3. subst. destruct H4 with id0 t'. auto. 
        rewrite H5 in H_erasure_r. inversion H_erasure_r. subst. 
         apply L_ST_var with (s:= (Labeled_frame lb sf :: s')) (h:=h0) (lb:=lb) 
                (sf:=sf) (lsf:=(Labeled_frame lb sf)) (s':=s'); auto.
         subst. rewrite H6 in H13. inversion H13. 

         destruct H5 as [cls_name].          destruct H5 as [o]. destruct H5.  
         rewrite H5 in H_erasure_r. inversion H_erasure_r. subst. 
         apply L_ST_var with (s:= (Labeled_frame lb sf :: s')) (h:=h0) (lb:=lb) 
                (sf:=sf) (lsf:=(Labeled_frame lb sf)) (s':=s'); auto.
         subst. rewrite H6 in H15. inversion H15. 
    + subst. rewrite H_flow in H6. inversion H6. 

  - intro t0'. intro. intro t0. intro.    inversion H_erasure_l. 
    + subst. inversion H_erasure_r. subst. 
      *)
Admitted. 



Inductive L_equivalence_store : stack -> heap -> stack -> heap -> Prop :=
  | L_equivalence_empty : forall lb h, 
      L_equivalence_store (cons (Labeled_frame lb empty_stack_frame) nil) h
                                       (cons (Labeled_frame lb empty_stack_frame) nil) h
  | L_equivalence_equal_store : forall s h,
      L_equivalence_store s h s h
  | L_equivalence_store_L : forall s1 lb1 sf1 s0 s2 lb2 sf2 s0' h1 h2 v1 v2, 
      s1 = cons (Labeled_frame lb1 sf1) s0->
      s2 = cons (Labeled_frame lb2 sf2) s0'->
      L_equivalence_store s0 h1 s0' h2 ->
      flow_to lb1 L_Label = true ->
      flow_to lb2 L_Label = true ->
      (forall x, sf1 x = Some v1 -> sf2 x = Some v2 -> L_equivalence_tm v1 h1 v2 h2) ->
      L_equivalence_store s1 h1 s2 h2.

Lemma erasure_equal_input : forall ct t s h s' h' sigma_r sigma_r' t_r t_r', 
      L_equivalence_store s h s' h' ->
      erasure (Config ct t (SIGMA s h)) (Config ct t_r sigma_r) -> 
      erasure (Config ct t (SIGMA s' h')) (Config ct t_r' sigma_r') -> 
      (Config ct t_r sigma_r) = (Config ct t_r' sigma_r').
Proof. Admitted. 

Lemma erasue_target : forall ct t sigma, 
    exists t' sigma',  (Config ct t sigma) =e=> (Config ct t' sigma').
  Proof. intros ct t sigma. 
   induction t. 
   Admitted. 

Theorem preservation : forall CT s s' h h' sigma sigma',
    field_wfe_heap CT h -> sigma = SIGMA s h ->  
    wfe_heap CT h -> wfe_stack CT h s -> sigma' = SIGMA s' h' -> 
    forall t T, has_type CT empty_context h t T -> 
     forall t',  Config CT t sigma ==> Config CT t' sigma' ->
     ( has_type CT empty_context h' t' T) .
Proof. Admitted. 


Lemma error_state_cannot_reach_valid_state : forall ct t sigma, 
    ~ (Error_state ==>* Config ct t sigma).
Proof. 
  intros. intro contra. induction t; inversion contra; inversion H. 
Qed. 


Lemma valid_syntax_preservation : forall CT t t' sigma' s h, 
      valid_syntax t ->
      forall T, has_type CT empty_context h t T -> 
      field_wfe_heap CT h -> wfe_heap CT h -> wfe_stack CT h s ->
      Config CT t (SIGMA s h) ==> Config CT t' sigma' ->
      valid_syntax t'. 
Proof. 
 intros CT t t' sigma' s h.   intro H_valid_syntax. intro T. intro H_typing.
intro H_wfe_fields. intro H_wfe_heap. intro H_wfe_stack.
    intro H_reduction.
    remember (Config CT t (SIGMA s h)) as config. 
    remember (Config CT t' sigma') as config'. 
generalize dependent t. generalize dependent t'. 
generalize dependent s. generalize dependent h.
generalize dependent sigma'. generalize dependent T.
induction H_reduction; intros; inversion Heqconfig; inversion Heqconfig'; subst; auto.
- inversion H_wfe_fields. inversion H6. subst. rename h0 into h.
    inversion H_typing. subst. inversion H5. 
- inversion H_valid_syntax. inversion H_typing. subst. 
   destruct IHH_reduction with (classTy clsT) sigma'0 h s e' e; auto. 
-  inversion H_wfe_fields. inversion H8. subst. rename h0 into h.
    inversion H_typing. subst. inversion H4. subst. destruct H14 as [F'].  destruct H2 as [lo]. 
    destruct H12 as [field_defs0]. destruct H3 as [method_defs0]. rewrite <- H6 in H5. inversion H5.
    subst. rewrite <- H0 in H2. inversion H2. subst. 
remember (class_def clsT field_defs0 method_defs0) as cls_def.
   assert ( exists cn field_defs method_defs, CT cn = Some cls_def
               /\ cls_def = (class_def cn field_defs method_defs)). 
    apply heap_consist_ct with h o F' lo; auto. 
    destruct H3 as [cls_name].     destruct H3 as [field_defs].
    destruct H3 as [method_defs].     destruct H3. 
    rewrite Heqcls_def in H7. inversion H7. subst.
    destruct H with o (class_def cls_name field_defs method_defs) 
          F' cls_name lo method_defs field_defs fname  cls'; auto. 
    destruct H10. rewrite H10 in H1. inversion H1. destruct H11.  rewrite H11. auto.
    destruct H11 as [o'].     destruct H11 as [F_f]. destruct H11 as [lx]. 
    destruct H11 as [f_field_defs].     destruct H11 as [f_method_defs]. destruct H11. 
    rewrite H11. auto.
- inversion H_valid_syntax. inversion H_typing. subst. 
   destruct IHH_reduction with (classTy T0) sigma'0 h s e' e; auto. subst. 
   inversion H1; subst; inversion H_reduction. 
-  inversion H_valid_syntax. inversion H_typing. subst. 
    assert (valid_syntax e). apply surface_syntax_is_valid_syntax. auto. 
    apply Valid_MethodCall2; auto.
    apply   IHH_reduction with (classTy arguT) sigma'0 h s e; auto.  
    subst.     apply Valid_MethodCall2; auto.
    inversion H_typing. 
apply   IHH_reduction with (classTy arguT) sigma'0 h s e; auto.  
- inversion H_typing.  subst. inversion H11. subst. inversion H5. subst. rewrite <- H4 in H7. inversion H7. 
  destruct H16 as [F']. destruct H as [lo]. rewrite H in H0. inversion H0.  subst. 
  rewrite H8 in H1. inversion H1. subst. apply Valid_return. apply surface_syntax_is_valid_syntax. auto. 
-  inversion H_typing.  subst. inversion H11. subst. inversion H3. subst. rewrite <- H2 in H7. inversion H7. 
  destruct H16 as [F']. destruct H as [lo]. rewrite H in H0. inversion H0.  subst. 
  rewrite H8 in H6. inversion H6. subst. apply Valid_return. apply surface_syntax_is_valid_syntax. auto.
-  inversion H_valid_syntax. inversion H_typing. subst. 
   destruct IHH_reduction with T0 sigma'0 h s e' e; auto.
-  inversion H_valid_syntax. inversion H_typing. subst. 
   destruct IHH_reduction with (LabelelTy T) sigma'0 h s e' e; auto.
- inversion H_valid_syntax; auto;  inversion H0; apply value_is_valid_syntax; auto. 
- inversion H_valid_syntax. inversion H_typing. subst. 
   destruct IHH_reduction with (LabelelTy T0) sigma'0 h s e' e; auto.
- inversion H_valid_syntax. inversion H_typing. subst. 
   destruct IHH_reduction with (OpaqueLabeledTy T) sigma'0 h s e' e; auto.
- inversion H_valid_syntax; auto;  inversion H0; apply value_is_valid_syntax; auto. 
- inversion H_valid_syntax. inversion H_typing. subst. 
   destruct IHH_reduction with ( T0) sigma'0 h s e' e; auto.
- inversion H_valid_syntax. inversion H_typing. subst. 
  inversion H6.  subst. 
   destruct IHH_reduction with ( T0) sigma'0 h s e' e; auto. inversion H0. auto. 
- inversion H_typing. subst. inversion H5. 
- inversion H_valid_syntax. inversion H_typing. subst. 
   destruct IHH_reduction with (classTy clsT) sigma'0 h s e1' e1; auto. 
    inversion H1; subst; inversion H_reduction.
-  inversion H_valid_syntax. inversion H_typing. subst. 
   destruct IHH_reduction with (classTy cls') sigma'0 h s e2' e2; auto. subst. 
    apply surface_syntax_is_valid_syntax. auto.  subst.  
   apply Valid_FieldWrite2. auto. inversion H_typing. subst. 
destruct IHH_reduction with (classTy cls') sigma'0 h s e2' e2; auto.
-  inversion H_valid_syntax. inversion H_typing. subst.  
    apply Valid_return. 
   destruct IHH_reduction with T sigma'0 h s e' e; auto.
-   inversion H_valid_syntax. auto. 
- inversion H_typing. subst.  inversion H9.  inversion H5. 
- inversion H_typing. subst.  inversion H9.  inversion H5. 
- inversion H_valid_syntax. inversion H_typing. subst. 
  apply Valid_sequence1.
destruct IHH_reduction with T0 sigma'0 h s s1' s1; auto. auto. subst. 
inversion H1; subst; inversion H_reduction. 
- inversion H_valid_syntax. apply surface_syntax_is_valid_syntax. auto.  auto. 
Qed. 

Lemma simulation_H_L : forall CT t t0 t' t0' sigma_l sigma_r sigma_l_e sigma_r_e s h,
      dot_free t = true ->
      valid_syntax t ->
      sigma_l = SIGMA s h ->
      forall T, has_type CT empty_context h t T -> 
      field_wfe_heap CT h -> wfe_heap CT h -> wfe_stack CT h s ->
      flow_to (current_label sigma_l) L_Label = false ->
      flow_to (current_label sigma_r) L_Label = true ->
      Config CT t sigma_l ==> Config CT t' sigma_r ->
      (erasure (Config CT t sigma_l) (Config CT t0 sigma_l_e)) ->
      (erasure (Config CT t' sigma_r) (Config CT t0' sigma_r_e)) ->
      l_reduction (Config CT t0 sigma_l_e) (Config CT t0' sigma_r_e).
 Proof.  intros CT t t0 t' t0' sigma_l sigma_r sigma_l_e sigma_r_e s h. intro H_dot_free. intro H_valid_syntax. 
  intro H_sigma_l.  
  intro T. intro H_typing. intro H_wfe_fields. 
  intro H_wfe_heap. intro H_wfe_stack. intro H_flow_l. intro H_flow_r.  intro H_reduction. 
  (*intro H_erasure_sigma_l.  *) intro H_erasure_l. intro H_erasure_r.   

  generalize dependent t'.   
  generalize dependent t0.
  generalize dependent t0'.
  generalize dependent T.
    generalize dependent sigma_l_e.      generalize dependent sigma_r_e. 
    generalize dependent sigma_l.      generalize dependent sigma_r. 
    generalize dependent s.      generalize dependent h.
induction t. 
  - intros.  admit. -intros.  admit.  - intros.  admit. 
  - intros.  admit. -intros.  admit.  - intros.  admit. 
  - intros.  admit. -intros.  admit.  - intros.  admit. 
  - intros.  admit. -intros.  admit.  - intros.  admit. 
  - intros.  admit. 


Admitted. 

Lemma simulation_H_H : forall CT t t0 t' t0' s h s' h' sigma_l_e sigma_r_e,
      dot_free t = true ->
      valid_syntax t ->
      forall T, has_type CT empty_context h t T -> 
      field_wfe_heap CT h -> wfe_heap CT h -> wfe_stack CT h s ->
      flow_to (current_label (SIGMA s h)) L_Label = false ->
      flow_to (current_label (SIGMA s' h')) L_Label = false ->
      Config CT t (SIGMA s h) ==> Config CT t' (SIGMA s' h') ->
      (Config CT t (SIGMA s h)) =e=> (Config CT t0 sigma_l_e) ->
      (Config CT t' (SIGMA s' h')) =e=> (Config CT t0' sigma_r_e) ->
      (Config CT t0 sigma_l_e) = (Config CT t0' sigma_r_e).
Admitted.

Lemma simulation_return_v : forall CT v s h s' h' t' sigma_l_e t0 t0' sigma_r_e, 
      forall T, has_type CT empty_context h v T -> 
      flow_to (current_label (SIGMA s h)) L_Label = false ->
      dot_free v = true->
      value v->
      Config CT (Return v) (SIGMA s h) ==> Config CT t' (SIGMA s' h') ->
      (Config CT  (Return v) (SIGMA s h)) =e=> (Config CT t0 sigma_l_e) ->
      (Config CT t' (SIGMA s' h')) =e=> (Config CT t0' sigma_r_e) ->
      l_reduction (Config CT t0 sigma_l_e) (Config CT t0' sigma_r_e).
Proof. intros CT v s h s' h' t' sigma_l_e t0 t0' sigma_r_e.  intro T. intro H_typing.
      intro H_flow. intro H_dot_free.  intro H_v. intro H_reduction. intro H_erasure_l. intro H_erasure_r.
      inversion H_reduction. subst. inversion H_v; subst; inversion H0. 
       subst. inversion H5.  inversion H10. subst. rename t' into v. rename s'0 into s0.
      assert (flow_to (current_label ((SIGMA
                                     (update_current_label s0
                                        (join_label (get_stack_label lsf)
                                            (get_current_label s0))) h0))) L_Label = false). 

      induction s0.  unfold current_label in H_flow. unfold get_stack in H_flow. 
         unfold get_current_label in H_flow. unfold flow_to in H_flow. unfold L_Label in H_flow.
    unfold subset in H_flow. inversion H_flow. induction lsf. unfold get_stack_label in H_flow. induction l0. inversion H_flow.
        induction a. unfold current_label. unfold get_stack. unfold update_current_label. induction lsf. 

        remember (get_current_label (Labeled_frame l0 s :: s0)) as lbl. unfold get_current_label.
        unfold get_stack_label.  apply flow_join_label with l1 lbl; auto.  apply join_label_commutative. 

       inversion H_erasure_l. subst. rewrite H3 in H_flow. inversion H_flow. subst. 
       inversion H11. subst.  inversion H2. subst. assert (Config CT v (SIGMA (lsf :: s0) h0) =eH=> Config CT dot  (SIGMA (lsf :: s0) h0)).
       apply value_erasure_to_dot. auto. subst. intro contra. subst. 
      unfold dot_free in H_dot_free. fold dot_free in H_dot_free. inversion H_dot_free.
      assert (e' = dot /\ (SIGMA s' h') = (SIGMA (lsf :: s0) h0)).
      apply erasure_H_deterministic with CT v (SIGMA (lsf :: s0) h0); auto. destruct H6. subst.  
      inversion H8. subst. inversion H_erasure_r. subst. rewrite H15 in H. inversion H.
      subst. inversion H19. subst. 
      assert (Config CT v
        (SIGMA
           (update_current_label s0
              (join_label (get_stack_label lsf) (get_current_label s0))) h0)  =eH=> 
        Config CT dot  (SIGMA
           (update_current_label s0
              (join_label (get_stack_label lsf) (get_current_label s0))) h0) ).
       apply value_erasure_to_dot. auto. subst. intro contra. subst. 
      unfold dot_free in H_dot_free. fold dot_free in H_dot_free. inversion H_dot_free.
      assert (t0' = dot /\ (SIGMA s' h') = (SIGMA
          (update_current_label s0
             (join_label (get_stack_label lsf) (get_current_label s0))) h0)).
      apply erasure_H_deterministic with CT v (SIGMA
          (update_current_label s0
             (join_label (get_stack_label lsf) (get_current_label s0))) h0); auto. destruct H9.  inversion H16. subst.  
       apply L_reduction with . 
      



Lemma multi_step_simulation_revised : forall CT t t0 t' t0' sigma_l sigma_r sigma_l_e sigma_r_e s h,
      dot_free t = true -> valid_syntax t ->
      sigma_l = SIGMA s h ->
      field_wfe_heap CT h -> wfe_heap CT h -> wfe_stack CT h s ->
      Config CT t sigma_l ==>* Config CT t' sigma_r ->
      (Config CT t sigma_l) =e=> (Config CT t0 sigma_l_e) ->
      (Config CT t' sigma_r) =e=> (Config CT t0' sigma_r_e) ->
      forall T, has_type CT empty_context h t T -> 
      (Config CT t0 sigma_l_e) ==>L* (Config CT t0' sigma_r_e).
Proof.
    intros CT t t0 t' t0' sigma_l sigma_r sigma_l_e sigma_r_e s h.
    intro H_dot_free. intro H_valid_syntax.
    intro H_sigma_l.  intro H_wfe_field. intro H_wfe_heap. intro H_wfe_stack.
    intro H_multistep_reduction. intro H_erasure_l. intro H_erasure_r. intro T. intro H_typing. 
    remember (Config CT t sigma_l) as t_config. 
    remember (Config CT t' sigma_r) as t'_config. 

    generalize dependent t0'. generalize dependent t0. generalize dependent t. 
    generalize dependent sigma_l. generalize dependent t'. generalize dependent sigma_r.
    generalize dependent sigma_l_e. generalize dependent sigma_r_e.
    generalize dependent s. generalize dependent h.
    induction H_multistep_reduction.
    intros. 
    assert ((Config CT t0 sigma_l_e) = (Config CT t0' sigma_r_e)).
    apply erasure_equal_input with t s h s h.
    apply L_equivalence_equal_store.
    rewrite Heqt_config in H_erasure_l. 
    rewrite <- H_sigma_l.  auto.
    rewrite Heqt_config in H_erasure_r. 
    rewrite <- H_sigma_l.  auto. 
    rewrite H. apply multi_reduction_l_refl.


    intros.   induction c2. 
    assert ( exists t1_r s0_r, erasure (Config c t1 s0) (Config c t1_r s0_r)).
    apply erasue_target. destruct H0 as [t1_r]. destruct H0 as [s0_r].

    remember (current_label (SIGMA s h)) as cur_lbl.
    assert ((flow_to cur_lbl L_Label = true) \/ (flow_to cur_lbl L_Label = false)).
    apply excluded_middle_label.  destruct H1.
    apply multi_reduction_l_step with (Config c t1_r s0_r).
    assert (CT=c). apply ct_consist with t t1 sigma_l s0. 
    rewrite Heqt_config in H. auto. subst. 

    apply simulation_L with (CT:=c) (t:=t) (t0:=t0) (t':=t1) (t0':=t1_r) 
      (sigma_l:=(SIGMA s h)) (sigma_r:=s0) (sigma_l_e:=sigma_l_e) (s:=s) (h:=h); auto.
    subst. induction s0.
    assert (CT=c). apply ct_consist with t t1 (SIGMA s h) (SIGMA s0 h0); auto.  
    subst; auto.  

    assert (wfe_heap c h0 /\ wfe_stack c h0 s0 /\  field_wfe_heap c h0).
    apply reduction_preserve_wfe with s h (SIGMA s h) (SIGMA s0 h0) t
    T t1; auto. 
    destruct IHH_multistep_reduction with (h:=h0) (s:=s0) (sigma_r_e:=sigma_r_e)
           (sigma_l_e:=s0_r) (t0':=t0')
    (sigma_r0:=sigma_r) (t'0:=t') (sigma_l:=(SIGMA s0 h0)) (t:=t1) (t0:= t1_r). 
    apply H2.  apply H2. apply H2. auto. auto. auto. 
    apply dot_free_preservation with t s h s0 h0 c T; auto. 
    apply valid_syntax_preservation with c t (SIGMA s0 h0) s h T; auto. 
    auto. 
    apply preservation with s s0 h (SIGMA s h) (SIGMA s0 h0) t; auto.
    auto. auto. apply multi_reduction_l_refl. 
    apply multi_reduction_l_step with c2; auto.

    subst. induction s0.
    assert (CT=c). apply ct_consist with t t1 (SIGMA s h) (SIGMA s0 h0); auto.  
    subst; auto.  

    assert (wfe_heap c h0 /\ wfe_stack c h0 s0 /\  field_wfe_heap c h0).
    apply reduction_preserve_wfe with s h (SIGMA s h) (SIGMA s0 h0) t
    T t1; auto. 
    assert (Config c t1_r s0_r ==>L* Config c t0' sigma_r_e).
    apply IHH_multistep_reduction with (h:=h0) (s:=s0) (sigma_r_e:=sigma_r_e)
           (sigma_l_e:=s0_r) (t0':=t0')
    (sigma_r0:=sigma_r) (t'0:=t') (sigma_l:=(SIGMA s0 h0)) (t:=t1) (t0:= t1_r); auto. 
    apply H2.  apply H2. apply H2.
    apply dot_free_preservation with t s h s0 h0 c T; auto. 
    apply valid_syntax_preservation with c t (SIGMA s0 h0) s h T; auto. 
    apply preservation with s s0 h (SIGMA s h) (SIGMA s0 h0) t; auto.

    (*case for return v*)
    assert ((exists v, value v -> t = Return v) \/ (forall v, ~ value v \/ t <> Return v)).
    Lemma excluded_middle_return_v : forall t,
      (exists v, value v -> t = Return v) \/ (forall v, ~ value v \/ t <> Return v).
      Proof with eauto.
        intros. case t; try (intros; right; right ; intro contra; inversion contra; fail).
        intro t0. left. exists t0. intro. auto.  
      Qed. 
    apply excluded_middle_return_v.  destruct H4.
  apply multi_reduction_l_step with (Config c t0' sigma_r_e). 
    apply multi_reduction_l_step with c2; auto.

    (*case for opaqueCall (return v) *)


    assert ((flow_to (current_label (SIGMA s0 h0)) L_Label = true) \/ (flow_to (current_label (SIGMA s0 h0)) L_Label = false)).
    apply excluded_middle_label.  destruct H4.

    assert (Config c t0 sigma_l_e ==l> (Config c t1_r s0_r)).
    apply simulation_H_L with (CT:=c) (t:=t) (t0:=t0) (t':=t1) (t0':=t1_r) 
      (sigma_l:=(SIGMA s h)) (sigma_r:= (SIGMA s0 h0)) (sigma_l_e:=sigma_l_e) (s:=s) (h:=h) (T:=T); auto.
    apply multi_reduction_l_step with (Config c t1_r s0_r). auto. auto. 

    assert ( Config c t0 sigma_l_e = Config c t1_r s0_r).
    apply simulation_H with t t1 s h s0 h0 T; auto.
    rewrite <- H5 in H3. auto.  

    subst.  apply error_state_cannot_reach_valid_state in H_multistep_reduction. intuition. 
Qed. 



(*

Lemma multi_step_simulation : forall CT t t0 t' t0' sigma_l sigma_r sigma_l_e sigma_r_e s h,
      dot_free t = true -> valid_syntax t ->
      sigma_l = SIGMA s h ->
      field_wfe_heap CT h -> wfe_heap CT h -> wfe_stack CT h s ->
      Config CT t sigma_l ==>* Config CT t' sigma_r ->
      (Config CT t sigma_l) =e=> (Config CT t0 sigma_l_e) ->
      (Config CT t' sigma_r) =e=> (Config CT t0' sigma_r_e) ->
      forall T, has_type CT empty_context h t T -> 
      (Config CT t0 sigma_l_e) ==>L* (Config CT t0' sigma_r_e).
Proof.
    intros CT t t0 t' t0' sigma_l sigma_r sigma_l_e sigma_r_e s h.
    intro H_dot_free. intro H_valid_syntax.
    intro H_sigma_l.  intro H_wfe_field. intro H_wfe_heap. intro H_wfe_stack.
    intro H_multistep_reduction. intro H_erasure_l. intro H_erasure_r. intro T. intro H_typing. 
    remember (Config CT t sigma_l) as t_config. 
    remember (Config CT t' sigma_r) as t'_config. 

    generalize dependent t0'. generalize dependent t0. generalize dependent t. 
    generalize dependent sigma_l. generalize dependent t'. generalize dependent sigma_r.
    generalize dependent sigma_l_e. generalize dependent sigma_r_e.
    generalize dependent s. generalize dependent h.
    induction H_multistep_reduction.
    intros. 
    assert ((Config CT t0 sigma_l_e) = (Config CT t0' sigma_r_e)).
    apply erasure_equal_input with t s h s h.
    apply L_equivalence_equal_store.
    rewrite Heqt_config in H_erasure_l. 
    rewrite <- H_sigma_l.  auto.
    rewrite Heqt_config in H_erasure_r. 
    rewrite <- H_sigma_l.  auto. 
    rewrite H. apply multi_reduction_l_refl.


    intros.   induction c2. 
    assert ( exists t1_r s0_r, erasure (Config c t1 s0) (Config c t1_r s0_r)).
    apply erasue_target. destruct H0 as [t1_r]. destruct H0 as [s0_r].

    remember (current_label (SIGMA s h)) as cur_lbl.
    assert ((flow_to cur_lbl L_Label = true) \/ (flow_to cur_lbl L_Label = false)).
    apply excluded_middle_label.  destruct H1.
    apply multi_reduction_l_step with (Config c t1_r s0_r).
    assert (CT=c). apply ct_consist with t t1 sigma_l s0. 
    rewrite Heqt_config in H. auto. subst. 

    apply simulation_L with (CT:=c) (t:=t) (t0:=t0) (t':=t1) (t0':=t1_r) 
      (sigma_l:=(SIGMA s h)) (sigma_r:=s0) (sigma_l_e:=sigma_l_e) (s:=s) (h:=h); auto.
    subst. induction s0.
    assert (CT=c). apply ct_consist with t t1 (SIGMA s h) (SIGMA s0 h0); auto.  
    subst; auto.  

assert (wfe_heap c h0 /\ wfe_stack c h0 s0 /\  field_wfe_heap c h0).
apply reduction_preserve_wfe with s h (SIGMA s h) (SIGMA s0 h0) t
T t1; auto. 
destruct IHH_multistep_reduction with (h:=h0) (s:=s0) (sigma_r_e:=sigma_r_e)
       (sigma_l_e:=s0_r) (t0':=t0')
(sigma_r0:=sigma_r) (t'0:=t') (sigma_l:=(SIGMA s0 h0)) (t:=t1) (t0:= t1_r). 
apply H2.  apply H2. apply H2. auto. auto. auto. 
apply dot_free_preservation with t s h s0 h0 c T; auto. 
apply valid_syntax_preservation with c t (SIGMA s0 h0) s h T; auto. 
auto. 
apply preservation with s s0 h (SIGMA s h) (SIGMA s0 h0) t; auto.
auto. auto. apply multi_reduction_l_refl. 
apply multi_reduction_l_step with c2; auto.

subst. induction s0.
assert (CT=c). apply ct_consist with t t1 (SIGMA s h) (SIGMA s0 h0); auto.  
subst; auto.  

assert (wfe_heap c h0 /\ wfe_stack c h0 s0 /\  field_wfe_heap c h0).
apply reduction_preserve_wfe with s h (SIGMA s h) (SIGMA s0 h0) t
T t1; auto. 
assert (Config c t1_r s0_r ==>L* Config c t0' sigma_r_e).
apply IHH_multistep_reduction with (h:=h0) (s:=s0) (sigma_r_e:=sigma_r_e)
       (sigma_l_e:=s0_r) (t0':=t0')
(sigma_r0:=sigma_r) (t'0:=t') (sigma_l:=(SIGMA s0 h0)) (t:=t1) (t0:= t1_r); auto. 
apply H2.  apply H2. apply H2.
apply dot_free_preservation with t s h s0 h0 c T; auto. 
apply valid_syntax_preservation with c t (SIGMA s0 h0) s h T; auto. 
apply preservation with s s0 h (SIGMA s h) (SIGMA s0 h0) t; auto.

assert ( Config c t0 sigma_l_e = Config c t1_r s0_r).
apply simulation_H with t t1 s h s0 h0 T; auto.
rewrite <- H4 in H3. auto.  

subst.  apply error_state_cannot_reach_valid_state in H_multistep_reduction. intuition. 
Qed. 
*)

Lemma erasure_preserve_value : forall v sigma v' sigma' ct, 
  value v ->
  erasure (Config ct v sigma) (Config ct v' sigma') ->
  value v'.
Proof. 
  (*intros v sigma v' sigma' ct. intro Hv. intro Herasure.
  generalize dependent v'. induction Hv; intro v'; intro Herasure; inversion Herasure.
  apply v_oid. apply v_dot. apply v_null. apply v_dot. apply v_label. apply v_dot.
  subst. assert (value v'0). apply IHHv. auto. apply v_labeled.  auto. 
  apply v_dot.  assert (value v'0). subst. apply IHHv. auto. apply v_opa_labeled.  auto. apply v_dot.  *)
Admitted. 


Inductive L_equivalence_config : config -> config -> Prop :=
  | L_equal_config : forall s h t ct, 
      L_equivalence_config (Config ct t (SIGMA s h))  (Config ct t (SIGMA s h))
  | L_equivalence_config_L : forall s h s' h' t t' lb1 lb2 ct, 
      lb1 = current_label (SIGMA s h) ->
      lb2 = current_label (SIGMA s' h') ->
      lb1 = lb2 ->
      flow_to lb2 L_Label = true ->
      L_equivalence_tm t h t' h'->
      L_equivalence_store s h s' h' ->
      L_equivalence_config (Config ct t (SIGMA s h)) (Config ct t' (SIGMA s' h'))
  | L_equivalence_config_H : forall s h s' h' t t' lb1 lb2 ct, 
      L_equivalence_store s h s' h' ->
      lb1 = current_label (SIGMA s h) ->
      lb2 = current_label (SIGMA s' h') ->
      flow_to lb1 L_Label = false ->
      flow_to lb2 L_Label = false ->
      L_equivalence_config (Config ct t (SIGMA s h)) (Config ct t' (SIGMA s' h')).


Lemma erasure_equal_imply_L_equivalence : forall ct v1 v2 s1 s2 h1 h2 v_r s_r h_r, 
      value v1 -> value v2 ->
      (Config ct v1 (SIGMA s1 h1)) =e=> (Config ct v_r (SIGMA s_r h_r)) ->
      (Config ct v2 (SIGMA s2 h2)) =e=> (Config ct v_r (SIGMA s_r h_r)) ->
      L_equivalence_config (Config ct v1 (SIGMA s1 h1)) (Config ct v2 (SIGMA s2 h2)).
Proof.
  intros  ct v1 v2 s1 s2 h1 h2 v_r s_r h_r. intro H_v1. intro H_v2. 
  intro H_erasure1.   intro H_erasure2. 
  remember  (Config ct v1 (SIGMA s1 h1) ) as v1_config. 
  generalize dependent v2.      generalize dependent v1.
  induction H_erasure1; intros; inversion Heqv1_config; subst; try (inversion H_v1); subst.
      - unfold erasure_L_fun in H_erasure2. admit.
      - unfold erasure_L_fun in H_erasure2. 

      (*
      -  (*inversion H_erasure2; subst; auto.
        inversion H_v2. rewrite H1 in H11. admit. *) admit.
    - subst. unfold erasure_L_fun in H_erasure2. inversion H_v2. subst. inversion H_erasure2; try (subst; 
      unfold erasure_L_fun in H9; inversion H9). subst. inversion H3. subst. 
      
      try (subst; remember (current_label (SIGMA s1 h1))  as lb0; inversion H_erasure2; apply L_equivalence_config_H with lb0 lb0; auto;
          apply L_equivalence_equal_store).
    - inversion H_v2; subst;  inversion H_erasure2; 
      try (subst; remember (current_label (SIGMA s1 h1))  as lb0; inversion H_erasure2; apply L_equivalence_config_H with lb0 lb0; auto;
          apply L_equivalence_equal_store). apply L_equal_config.
    - inversion H_v2; subst;  inversion H_erasure2; 
      try (subst; remember (current_label (SIGMA s1 h1))  as lb0; inversion H_erasure2; apply L_equivalence_config_H with lb0 lb0; auto;
          apply L_equivalence_equal_store). 
    - inversion H_v2; subst;  inversion H_erasure2; 
      try (subst; remember (current_label (SIGMA s1 h1))  as lb0; inversion H_erasure2; apply L_equivalence_config_H with lb0 lb0; auto;
          apply L_equivalence_equal_store); try (apply L_equal_config).
    - inversion H_v2; subst;  inversion H_erasure2; 
      try (subst; remember (current_label (SIGMA s1 h1))  as lb0; inversion H_erasure2; apply L_equivalence_config_H with lb0 lb0; auto;
          apply L_equivalence_equal_store); try (apply L_equal_config); try (apply L_equivalence_config_H with cur_lbl cur_lbl; auto;
          apply L_equivalence_equal_store).
    - inversion H_v2; subst;  inversion H_erasure2; 
      try (subst; remember (current_label (SIGMA s1 h1))  as lb0; inversion H_erasure2; apply L_equivalence_config_H with lb0 lb0; auto;
          apply L_equivalence_equal_store); try (apply L_equal_config); try (apply L_equivalence_config_H with cur_lbl cur_lbl; auto;
          apply L_equivalence_equal_store). 
      subst. assert (L_equivalence_config (Config ct v (SIGMA s1 h1))
                 (Config ct v1 (SIGMA s1 h1))). apply IHH_erasure1 with v; auto.
      inversion H. apply L_equal_config.
      subst. remember (current_label (SIGMA s1 h1)) as cur_lb.
      apply L_equivalence_config_L with cur_lb cur_lb; auto.
      assert (flow_to lb L_Label = true \/ flow_to lb L_Label = false). 
      apply excluded_middle_label.
      destruct H2.       apply L_equivalence_tm_eq_v_l_L; auto.
      apply L_equivalence_tm_eq_v_l_H; auto.
    
      apply L_equivalence_config_H with lb1 lb2; auto.

    - inversion H_v2; subst;  inversion H_erasure2; 
      try (subst; remember (current_label (SIGMA s1 h1))  as lb0; inversion H_erasure2; apply L_equivalence_config_H with lb0 lb0; auto;
          apply L_equivalence_equal_store); try (apply L_equal_config); try (apply L_equivalence_config_H with cur_lbl cur_lbl; auto;
          apply L_equivalence_equal_store).
    - inversion H_v2; subst;  inversion H_erasure2.
      subst. assert (L_equivalence_config (Config ct v (SIGMA s1 h1))
                 (Config ct v1 (SIGMA s1 h1))). apply IHH_erasure1 with v; auto.
      inversion H. apply L_equal_config.
      subst. remember (current_label (SIGMA s1 h1)) as cur_lb.
      apply L_equivalence_config_L with cur_lb cur_lb; auto.
      assert (flow_to lb L_Label = true \/ flow_to lb L_Label = false). 
      apply excluded_middle_label.
      destruct H2.       apply L_equivalence_tm_eq_v_opa_l_L; auto.
      apply L_equivalence_tm_eq_v_opa_l_H; auto.
    
      apply L_equivalence_config_H with lb1 lb2; auto.
  -  inversion H_v2; subst;  inversion H_erasure2; 
      try (subst; remember (current_label (SIGMA s1 h1))  as lb0; inversion H_erasure2; apply L_equivalence_config_H with lb0 lb0; auto;
          apply L_equivalence_equal_store); try (apply L_equal_config); try (apply L_equivalence_config_H with cur_lbl cur_lbl; auto;
          apply L_equivalence_equal_store).
*)
Admitted. 




Theorem Non_interference : forall ct t s s' h h' sf sf' lb x s0 s1 h1 s2 h2 v1 v2 final_v1 final_v2,
      dot_free t = true -> valid_syntax t ->
      field_wfe_heap ct h -> wfe_heap ct h -> wfe_stack ct h s->
      field_wfe_heap ct h' -> wfe_heap ct h' -> wfe_stack ct h' s'->
      s = cons (Labeled_frame lb sf) s0 ->
      s' = cons (Labeled_frame lb sf') s0 ->
      sf x = Some (v_l v1 H_Label) ->
      sf' x = Some (v_l v2 H_Label) ->
      L_equivalence_store s h s' h' ->
      (Config ct t (SIGMA s h)) ==>* (Config ct final_v1 (SIGMA s1 h1)) -> 
      (Config ct t (SIGMA s' h')) ==>* (Config ct final_v2 (SIGMA s2 h2)) ->
      value final_v1-> value final_v2 -> 
      forall T, has_type ct empty_context h t T -> has_type ct empty_context h' t T ->
      L_equivalence_config (Config ct final_v1 (SIGMA s1 h1)) (Config ct final_v2 (SIGMA s2 h2)).

Proof. 
    intros ct t s s' h h' sf sf' lb x s0 s1 h1 s2 h2 v1 v2 final_v1 final_v2.
    intro H_dot_free. intro H_valid_syntax.
    intro H_wfe_field. intro H_wfe_heap. intro H_wfe_stack. 
    intro H_wfe_field'. intro H_wfe_heap'. intro H_wfe_stack'. 
    intro H_stack1. intro H_stack2. intro H_high_v1. intro H_high_v2.
    intro H_equal_start.  intro H_execution1.  intro H_execution2. intro H_final_v1. intro H_final_v2.
    intro T. intro H_typing_h. intro H_typing_h'. 
    assert (exists t_r sigma_r, erasure (Config ct t (SIGMA s h)) (Config ct t_r sigma_r)).
    apply erasue_target.
    assert (exists t_r' sigma_r', erasure (Config ct t (SIGMA s' h')) (Config ct t_r' sigma_r')).
    apply erasue_target.
    destruct H as [t_r]. destruct H as [sigma_r]. 
    destruct H0 as [t_r']. destruct H0 as [sigma_r'].
    assert  ((Config ct t_r sigma_r) = (Config ct t_r' sigma_r')).
    apply erasure_equal_input with t s h s' h'; auto.

    assert (exists final_v1_r sigma1_r, erasure (Config ct final_v1 (SIGMA s1 h1)) (Config ct final_v1_r sigma1_r)).
    apply erasue_target. destruct H2 as [final_v1_r]. destruct H2 as [sigma1_r].
    assert ((Config ct t_r sigma_r) ==>L* (Config ct final_v1_r sigma1_r)).
    apply multi_step_simulation_revised with t final_v1 (SIGMA s h) (SIGMA s1 h1) s h T; auto.

    assert (exists final_v2_r sigma2_r, erasure (Config ct final_v2 (SIGMA s2 h2)) (Config ct final_v2_r sigma2_r)).
    apply erasue_target. destruct H4 as [final_v2_r]. destruct H4 as [sigma2_r].
    assert ((Config ct t_r' sigma_r') ==>L* (Config ct final_v2_r sigma2_r)).
    apply multi_step_simulation_revised with t final_v2 (SIGMA s' h') (SIGMA s2 h2) s' h' T; auto.

    rewrite H1 in H3.

    assert (final_v1_r = final_v2_r /\ sigma1_r = sigma2_r). 
    apply  L_reduction_multistep_determinacy with ct t_r' sigma_r'; auto. 
    apply erasure_preserve_value with final_v1 (SIGMA s1 h1) sigma1_r ct; auto.

    apply erasure_preserve_value with final_v2 (SIGMA s2 h2) sigma2_r ct; auto. 
    induction sigma1_r.     induction sigma2_r.  inversion H1. subst. 
    apply erasure_equal_imply_L_equivalence with final_v1_r s3 h0; auto. 
    destruct H6. subst. inversion H7. auto.
Qed.  



