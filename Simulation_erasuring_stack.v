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
  | ST_fieldRead2 : forall sigma sigma' o s h fname lb cls fields v s' ct,
      sigma = SIGMA s h ->
      Some (Heap_OBJ cls fields lb) = lookup_heap_obj h o -> 
      Some v = fields(fname) -> 
      flow_to lb (current_label sigma) = true ->
      s' = update_current_label s lb-> 
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
      value v -> v <> null ->
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
      flow_to lb (current_label sigma) = true ->
      l' = join_label lb (current_label sigma) ->
      h' = update_heap_obj h o (Heap_OBJ cls F' lb) ->
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
      l' = join_label lo (join_label (current_label sigma) lb) ->
      flow_to lo (join_label (current_label sigma) lb)  = true ->
      h' = update_heap_obj h o (Heap_OBJ cls F' lo) ->
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
  | ST_return2 : forall sigma sigma' v s s' h lsf l' ct, 
      value v ->
      sigma = SIGMA s h ->
      s = cons lsf s' ->
      s' <> nil ->
      l' = (get_current_label s) ->
      sigma' = SIGMA s' h ->
      Config ct (Return v) sigma ==> Config ct (v_opa_l v l') sigma'
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


Fixpoint return_free (t : tm) :=
  match t with
    | Tvar x => true
    | null => true
    | FieldAccess e f => (return_free e)
    | MethodCall e1 meth e2 => if (return_free e1) then (return_free e2) else false
    | NewExp cls => true
(* label related *)
    | l lb => true
    | labelData e lb => (return_free e)
    | unlabel e => (return_free e)
    | labelOf e => (return_free e)
    | unlabelOpaque e => (return_free e)
(* statements *)
    | Skip => true
    | Assignment x e => (return_free e)
    | FieldWrite e1 f e2 =>  if (return_free e1) then (return_free e2) else false
    | If id0 id1 e1 e2 =>  if (return_free e1) then (return_free e2) else false
    | Sequence e1 e2 =>  if (return_free e1) then (return_free e2) else false
    | Return e => false

(* special terms *)
    | ObjId o =>  true 
  (* runtime labeled date*)
    | v_l e lb => (return_free e)
    | v_opa_l e lb => (return_free e)
    | dot => true
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
      has_type CT Gamma h (Return body) (OpaqueLabeledTy (classTy returnT)) ->
      has_type CT Gamma h (MethodCall e meth argu) (OpaqueLabeledTy (classTy returnT))
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
      has_type CT Gamma h (Return e) (OpaqueLabeledTy T)
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
     unfold L_Label.   unfold flow_to. right. unfold subset. auto.
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
    | v_l e lb => if (flow_to lb L_Label) then v_l (erasure_L_fun e) lb else v_l dot lb 
    | v_opa_l e lb => if (flow_to lb L_Label) then v_opa_l (erasure_L_fun e) lb else v_opa_l dot lb 
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
    | cons (Labeled_frame lb sf) s'=> if (flow_to lb L_Label) then cons (Labeled_frame lb (fun x => (erasure_obj_null (sf x) h))) (erasure_stack s' h)
                                                                else erasure_stack s' h

                (*cons (Labeled_frame lb (fun x => (erasure_obj_null (sf x) h))) s' *) 
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


Fixpoint erasure_H_fun (t: tm  ) : tm :=
match t with
    | Tvar x => dot
    | null => dot
    | FieldAccess e f => if (return_free e) then dot else FieldAccess (erasure_H_fun e) f
    | MethodCall e1 meth e2 =>  if (return_free e1) then 
                                                   ( if (return_free e2) then dot else MethodCall e1 meth (erasure_H_fun e2) )
                                                 else MethodCall (erasure_H_fun e1) meth e2
    | NewExp cls => dot
(* label related *)
    | l lb => dot
    | labelData e lb => if (return_free e) then dot else labelData (erasure_H_fun e) lb
    | unlabel e => if (return_free e) then dot else unlabel (erasure_H_fun e)
    | labelOf e => if (return_free e) then dot else labelOf (erasure_H_fun e) 
    | unlabelOpaque e => if (return_free e) then dot else unlabelOpaque (erasure_H_fun e)
(* statements *)
    | Skip => dot
    | Assignment x e => if (return_free e) then dot else Assignment x (erasure_H_fun e)
    | FieldWrite e1 f e2 => if (return_free e1) then 
                                                   ( if (return_free e2) then dot else FieldWrite e1 f (erasure_H_fun e2) )
                                                 else FieldWrite (erasure_H_fun e1) f e2
    | If id0 id1 e1 e2 => dot
    | Sequence e1 e2 => if (return_free e1) then 
                                                   ( if (return_free e2) then dot else (erasure_H_fun e2) )
                                                 else Sequence (erasure_H_fun e1) e2
    | Return e => if (return_free e) then  (v_opa_l dot H_Label) else Return (erasure_H_fun e)

(* special terms *)
    | ObjId o =>  dot
  (* runtime labeled date*)
    | v_l e lb => if (return_free e) then dot else v_l (erasure_H_fun e) lb
    | v_opa_l e lb => if (return_free e) then dot else v_opa_l (erasure_H_fun e) lb
    | dot => dot
  end.

Fixpoint erasure_H_fun_whole (t: tm) (s:stack) : tm :=
match s with 
  |  (Labeled_frame lb sf :: s') => if (flow_to lb L_Label) then t else erasure_H_fun_whole (erasure_H_fun t) s'
  | nil => t
end. 

(* test cases
Definition t := unlabelOpaque (Return (unlabelOpaque (Return (unlabelOpaque (Return (ObjId (OID 0))))))).
Definition s := (Labeled_frame H_Label empty_stack_frame ) :: (Labeled_frame H_Label empty_stack_frame ) 
                :: (Labeled_frame H_Label empty_stack_frame ) :: (Labeled_frame L_Label empty_stack_frame :: nil).

Compute (flow_to H_Label L_Label).

Compute (erasure_H_fun t ).
Compute (erasure_H_fun (erasure_H_fun t ) ).

Definition t' := unlabelOpaque (Return (unlabelOpaque (Return (unlabelOpaque (v_opa_l (ObjId (OID 0)) H_Label   ))))).
Definition s' := (Labeled_frame H_Label empty_stack_frame ) 
                :: (Labeled_frame H_Label empty_stack_frame ) :: (Labeled_frame L_Label empty_stack_frame :: nil).

Definition t0 := unlabelOpaque (Return (unlabelOpaque (Return (unlabelOpaque ( MethodCall (ObjId (OID 0)) (Id "meth") (ObjId (OID 1))   ))))).
Compute (erasure_H_fun_whole t0 s' ).
Compute (erasure_H_fun_whole t' s' ).
Compute (erasure_H_fun_whole t s ).
Print s. 
Compute (erasure_stack s nil).
*)
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
  | Valid_if : forall id1 id2 e1 e2,
      surface_syntax e1 = true ->
      surface_syntax e2 = true ->
      valid_syntax (If id1 id2 e1 e2)

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
  | erasure_H_context : forall  ct s h s' h' t t' ,
      flow_to (current_label (SIGMA s h)) L_Label = false ->
      t' = erasure_H_fun_whole t s ->
      (SIGMA s' h') = erasure_sigma_fun (SIGMA s h) ->
      erasure (Config ct t (SIGMA s h))  (Config ct (t') (SIGMA s' h'))  
where "c '=e=>' c'" := (erasure c c').

Lemma erasure_deterministic : forall ct t t1 t2 sigma sigma1 sigma2, 
  (erasure (Config ct t sigma) (Config ct t1 sigma1)) ->
  (erasure (Config ct t sigma) (Config ct t2 sigma2)) ->
  t1 = t2 /\ sigma1 = sigma2. 
Proof. 
  intros ct t t1 t2 sigma sigma1 sigma2. 
  intro H_erasure1.   intro H_erasure2.
  remember (current_label sigma) as lb.  
  inversion H_erasure1. inversion H_erasure2. subst. inversion H9. subst.
  rewrite H6. rewrite H14. auto.  subst.
   
  inversion H9. subst.  rewrite H3 in H11. inversion H11. 
inversion H_erasure2. subst. inversion H9. subst.
  rewrite H11 in H3. inversion H3. subst.  
  inversion H9. subst. rewrite H6. rewrite H14. auto.
Qed. 

Lemma multi_erasure_L_tm_equal : forall t, 
   erasure_L_fun (erasure_L_fun t) = (erasure_L_fun t).
  Proof. induction t; try (unfold erasure_L_fun; auto; fold erasure_L_fun;  rewrite IHt; auto; fail);
 try (unfold erasure_L_fun; auto; fold erasure_L_fun; rewrite IHt1; rewrite IHt2; auto).
 - fold erasure_L_fun. unfold erasure_L_fun. fold erasure_L_fun. 
    case_eq (flow_to l0 L_Label ). intro. unfold erasure_L_fun. fold erasure_L_fun. rewrite H. rewrite IHt.  auto. 
    intro. unfold erasure_L_fun. auto. rewrite H. auto.

 - fold  erasure_L_fun. 
    case_eq (flow_to l0 L_Label ). intro. unfold erasure_L_fun. fold erasure_L_fun. rewrite H.
    unfold erasure_L_fun. fold erasure_L_fun.  rewrite IHt. rewrite H.  auto. 
    intro. unfold erasure_L_fun. auto. rewrite H. rewrite H. auto. 
Qed.  

Lemma dot_free_if : forall t1 t2, 
    (if dot_free t1 then dot_free t2 else false) = true -> dot_free t1 = true /\ dot_free t2 = true.
    Proof.  intros. case_eq (dot_free t1). intro. case_eq (dot_free t2). intro. auto.
      intro. rewrite H0 in H. rewrite H1 in H. intuition. intro. rewrite H0 in H. intuition.
Qed.

Lemma return_free_if : forall t1 t2, 
    (if return_free t1 then return_free t2 else false) = true -> return_free t1 = true /\ return_free t2 = true.
    Proof.  intros. case_eq (return_free t1). intro. case_eq (return_free t2). intro. auto.
      intro. rewrite H0 in H. rewrite H1 in H. intuition. intro. rewrite H0 in H. intuition.
Qed.

Lemma return_free_if_false : forall t1 t2, 
    (if return_free t1 then return_free t2 else false) = false ->
     return_free t1 = false \/ (return_free t1 = true /\ return_free t2 = false).
    Proof.  intros. case_eq (return_free t1). intro. case_eq (return_free t2). intro. rewrite H0 in H. rewrite H1 in H. inversion H.
      intro. right. auto. intro. left. auto. 
Qed.


Lemma erasure_H_fun_preserve_return_free_true : forall t, 
  return_free t = true ->
  return_free(erasure_H_fun (t)) = true.
Proof. intros. induction t; 
    try (unfold erasure_H_fun; unfold return_free; auto; fail); 
    try (unfold return_free in H; fold return_free in H;
      unfold erasure_H_fun; rewrite H; unfold return_free; auto);
   try (unfold return_free in H; fold return_free in H; apply return_free_if in H; destruct H;
  unfold erasure_H_fun; rewrite H; rewrite H0;  unfold return_free; auto).

  unfold return_free in H. inversion H.
Qed.


Hint Constructors valid_syntax.
Lemma value_is_valid_syntax : forall v, 
  value v -> valid_syntax v.
Proof with eauto. intros. inversion H. apply Valid_ObjId. apply Valid_skip. apply Valid_null. apply Valid_label. apply Valid_v_l.
        auto. apply Valid_v_opa_l. auto. apply Valid_dot. Qed. 

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

Lemma surface_syntax_is_return_free : forall t, 
  surface_syntax t = true -> return_free t = true.
Proof. intros. induction t; auto; try (apply surface_syntax_if in H; destruct H; apply IHt1 in H; apply IHt2 in H0; 
        unfold return_free; fold return_free); try (rewrite H); auto; try (unfold surface_syntax in H; inversion H).
Qed. 

Lemma surface_syntax_is_valid_syntax : forall t,
  surface_syntax t = true -> valid_syntax t.
Proof with eauto. Admitted. 

Lemma value_is_return_free : forall v,
(*    forall T, has_type CT empty_context h e T -> *)
    value v ->
    return_free v = true.
Proof. intro v. intro H_v. induction H_v; subst; auto. Qed.  

Lemma value_erasure_to_dot : forall v,
(*    forall T, has_type CT empty_context h e T -> *)
    value v ->
    erasure_H_fun v = dot.
Proof. intros.  induction H; unfold erasure_H_fun; auto. fold erasure_H_fun.
 pose proof (value_is_return_free v).    apply H0 in H. rewrite H. auto.
 pose proof (value_is_return_free v).   apply H0 in H. rewrite H. auto.
Qed.

(*
Lemma erasure_H_fun_preserve_return_free_false : forall t, 
  valid_syntax t ->
  return_free t = false ->
  return_free(erasure_H_fun (t)) = false.
Proof. intro t.  intro H_valid_syntax. intros. induction t; 
    try (unfold erasure_H_fun; unfold return_free; auto; fail);
    try (unfold return_free in H;  fold return_free in H;
      unfold erasure_H_fun; rewrite H; fold erasure_H_fun; unfold return_free;
      fold return_free; inversion H_valid_syntax; apply IHt; auto).
    apply return_free_if_false in H. destruct H.
    unfold erasure_H_fun. rewrite H. fold erasure_H_fun. unfold return_free. fold return_free. 
    inversion H_valid_syntax. assert (return_free (erasure_H_fun t1) = false). apply IHt1; auto.
    rewrite H5.  auto. assert (return_free (erasure_H_fun t1) = false). apply IHt1; auto. apply value_is_valid_syntax. auto. 
    rewrite H5.  auto.

   destruct H. inversion H_valid_syntax. assert (valid_syntax t2). apply surface_syntax_is_valid_syntax. auto. subst. 
    unfold erasure_H_fun. rewrite H. fold erasure_H_fun. unfold return_free. fold return_free. rewrite H0.
    unfold return_free. fold return_free. rewrite H. apply IHt2; auto.  subst. 
    unfold erasure_H_fun. rewrite H. fold erasure_H_fun. unfold return_free. fold return_free. rewrite H0.
    unfold return_free. fold return_free. rewrite H. apply IHt2; auto. 

    apply return_free_if_false in H. destruct H.
    unfold erasure_H_fun. rewrite H. fold erasure_H_fun. unfold return_free. fold return_free. 
    inversion H_valid_syntax. assert (return_free (erasure_H_fun t1) = false). apply IHt1; auto.
    rewrite H5.  auto. assert (return_free (erasure_H_fun t1) = false). apply IHt1; auto. apply value_is_valid_syntax. auto. 
    rewrite H5.  auto.

   destruct H. inversion H_valid_syntax. assert (valid_syntax t2). apply surface_syntax_is_valid_syntax. auto. subst. 
    unfold erasure_H_fun. rewrite H. fold erasure_H_fun. unfold return_free. fold return_free. rewrite H0.
    unfold return_free. fold return_free. rewrite H. apply IHt2; auto.  subst. 
    unfold erasure_H_fun. rewrite H. fold erasure_H_fun. unfold return_free. fold return_free. rewrite H0.
    unfold return_free. fold return_free. rewrite H. apply IHt2; auto. 

    inversion H_valid_syntax. unfold return_free in H. fold return_free in H. apply surface_syntax_is_return_free in H2. 
    apply surface_syntax_is_return_free in H5. rewrite H2 in H. rewrite H5 in H. inversion H. 

    apply return_free_if_false in H. destruct H.
    unfold erasure_H_fun. rewrite H. fold erasure_H_fun. unfold return_free. fold return_free. 
    inversion H_valid_syntax. assert (return_free (erasure_H_fun t1) = false). apply IHt1; auto.
     rewrite H4.  auto. assert (return_free (erasure_H_fun t1) = false). apply IHt1; auto. apply value_is_valid_syntax. auto. 
    rewrite H4.  auto.
    destruct H. inversion H_valid_syntax. assert (valid_syntax t2). apply surface_syntax_is_valid_syntax. auto. subst. 
    unfold erasure_H_fun. rewrite H. fold erasure_H_fun. unfold return_free. fold return_free. rewrite H0.
    unfold return_free. fold return_free. apply surface_syntax_is_return_free in H4. rewrite H4 in H0. inversion H0. 
    unfold erasure_H_fun. rewrite H. rewrite H0. fold erasure_H_fun.
    apply IHt2; auto.  subst. 

    unfold erasure_H_fun. case (return_free t). unfold return_free. auto. 
    fold erasure_H_fun. unfold return_free. auto.  subst. 
    apply value_is_valid_syntax. auto.      apply value_is_valid_syntax. auto. 
Qed.  
*)

Lemma exclude_middle_return_t : forall t, 
    (return_free t = true \/ return_free t = false). 
Proof. intro t. induction t; unfold return_free; try (left; auto; fail);
  try (fold return_free; auto); try (destruct IHt1; rewrite H; auto). 
Qed. 


(*
Lemma multi_erasure_H_tm_equal : forall t, 
    valid_syntax t ->
   erasure_H_fun (erasure_H_fun t) = (erasure_H_fun t).
  Proof with eauto.  induction t; try (unfold erasure_H_fun; auto;fail); try (fold erasure_H_fun; rewrite IHt; auto; fail);
 try (fold erasure_H_fun; rewrite IHt1; rewrite IHt2; auto; fail).
 - assert (return_free t = true \/ return_free t = false). apply exclude_middle_return_t. destruct H.
  + unfold erasure_H_fun. rewrite H. auto. 
  +  unfold erasure_H_fun. rewrite H. fold erasure_H_fun. intro. 
      assert (return_free(erasure_H_fun (t)) = false). apply erasure_H_fun_preserve_return_free_false; auto. 
      inversion H0;  auto. rewrite H1. assert (erasure_H_fun (erasure_H_fun t) = erasure_H_fun t). apply IHt.
      inversion H0. auto. rewrite H2.  auto. 
 -  intro. unfold erasure_H_fun. fold erasure_H_fun.
    assert (return_free t1 = true \/ return_free t1= false). apply exclude_middle_return_t. destruct H0.
    rewrite H0.
    assert (return_free t2 = true \/ return_free t2= false). apply exclude_middle_return_t. destruct H1.
    rewrite H1. auto. rewrite H1. unfold erasure_H_fun.  fold erasure_H_fun. rewrite H0. 
    assert (return_free(erasure_H_fun (t2)) = false). apply erasure_H_fun_preserve_return_free_false; auto. 
    inversion H. apply surface_syntax_is_valid_syntax. auto. auto. rewrite H2.  inversion H.  
    apply  surface_syntax_is_valid_syntax in H7. apply IHt2 in H7. rewrite H7. auto. 
    apply IHt2 in H7. rewrite H7. auto. rewrite H0. 
    unfold erasure_H_fun. fold erasure_H_fun.
 
   assert (return_free(erasure_H_fun (t1)) = false). apply erasure_H_fun_preserve_return_free_false; auto. 
    inversion H. auto.  apply value_is_valid_syntax. auto.  rewrite H1. 
    inversion H. apply IHt1 in H4.  rewrite H4.  auto. apply value_is_valid_syntax in H4. 
    apply IHt1 in H4.  rewrite H4. auto.  
 - assert (return_free t = true \/ return_free t = false). apply exclude_middle_return_t. destruct H.
  + unfold erasure_H_fun. rewrite H. auto. 
  +  unfold erasure_H_fun. rewrite H. fold erasure_H_fun. intro. 
      assert (return_free(erasure_H_fun (t)) = false). apply erasure_H_fun_preserve_return_free_false; auto. 
      inversion H0;  auto. rewrite H1. assert (erasure_H_fun (erasure_H_fun t) = erasure_H_fun t). apply IHt.
      inversion H0. auto. rewrite H2.  auto. 
 - assert (return_free t = true \/ return_free t = false). apply exclude_middle_return_t. destruct H.
  + unfold erasure_H_fun. rewrite H. auto. 
  +  unfold erasure_H_fun. rewrite H. fold erasure_H_fun. intro. 
      assert (return_free(erasure_H_fun (t)) = false). apply erasure_H_fun_preserve_return_free_false; auto. 
      inversion H0;  auto. rewrite H1. assert (erasure_H_fun (erasure_H_fun t) = erasure_H_fun t). apply IHt.
      inversion H0. auto. rewrite H2.  auto. 
 - assert (return_free t = true \/ return_free t = false). apply exclude_middle_return_t. destruct H.
  + unfold erasure_H_fun. rewrite H. auto. 
  +  unfold erasure_H_fun. rewrite H. fold erasure_H_fun. intro. 
      assert (return_free(erasure_H_fun (t)) = false). apply erasure_H_fun_preserve_return_free_false; auto. 
      inversion H0;  auto. rewrite H1. assert (erasure_H_fun (erasure_H_fun t) = erasure_H_fun t). apply IHt.
      inversion H0. auto. rewrite H2.  auto. 
 - assert (return_free t = true \/ return_free t = false). apply exclude_middle_return_t. destruct H.
  unfold erasure_H_fun. rewrite H. auto.   unfold erasure_H_fun. rewrite H. fold erasure_H_fun. intro. 
      assert (return_free(erasure_H_fun (t)) = false). apply erasure_H_fun_preserve_return_free_false; auto. 
      inversion H0;  auto. rewrite H1. assert (erasure_H_fun (erasure_H_fun t) = erasure_H_fun t). apply IHt.
      inversion H0. auto. rewrite H2.  auto. 
 - assert (return_free t = true \/ return_free t = false). apply exclude_middle_return_t. destruct H.
  + unfold erasure_H_fun. rewrite H. auto. 
  +  unfold erasure_H_fun. rewrite H. fold erasure_H_fun. intro. 
      assert (return_free(erasure_H_fun (t)) = false). apply erasure_H_fun_preserve_return_free_false; auto. 
      inversion H0;  auto. rewrite H1. assert (erasure_H_fun (erasure_H_fun t) = erasure_H_fun t). apply IHt.
      inversion H0. auto. rewrite H2.  auto. 
 - assert (return_free t = true \/ return_free t = false). apply exclude_middle_return_t. destruct H.
  + unfold erasure_H_fun. rewrite H. auto. 
  +  unfold erasure_H_fun. rewrite H. fold erasure_H_fun. intro. 
      assert (return_free(erasure_H_fun (t)) = false). apply erasure_H_fun_preserve_return_free_false; auto. 
      inversion H0;  auto. rewrite H1. assert (erasure_H_fun (erasure_H_fun t) = erasure_H_fun t). apply IHt.
      inversion H0. auto. rewrite H2.  auto. 
 -  intro. unfold erasure_H_fun. fold erasure_H_fun.
    assert (return_free t1 = true \/ return_free t1= false). apply exclude_middle_return_t. destruct H0.
    rewrite H0.
    assert (return_free t2 = true \/ return_free t2= false). apply exclude_middle_return_t. destruct H1.
    rewrite H1. auto. rewrite H1. unfold erasure_H_fun.  fold erasure_H_fun. rewrite H0. 
    assert (return_free(erasure_H_fun (t2)) = false). apply erasure_H_fun_preserve_return_free_false; auto. 
    inversion H. apply surface_syntax_is_valid_syntax. auto. auto. rewrite H2.  inversion H.  
    apply  surface_syntax_is_valid_syntax in H7. apply IHt2 in H7. rewrite H7. auto. 
    apply IHt2 in H7. rewrite H7. auto. rewrite H0. 
    unfold erasure_H_fun. fold erasure_H_fun.
 
   assert (return_free(erasure_H_fun (t1)) = false). apply erasure_H_fun_preserve_return_free_false; auto. 
    inversion H. auto.  apply value_is_valid_syntax. auto.  rewrite H1. 
    inversion H. apply IHt1 in H4.  rewrite H4.  auto. apply value_is_valid_syntax in H4. 
    apply IHt1 in H4.  rewrite H4. auto.  
 -  intro. unfold erasure_H_fun. fold erasure_H_fun.
    assert (return_free t1 = true \/ return_free t1= false). apply exclude_middle_return_t. destruct H0.
    rewrite H0.
    assert (return_free t2 = true \/ return_free t2= false). apply exclude_middle_return_t. destruct H1.
    rewrite H1. auto. rewrite H1. unfold erasure_H_fun.  fold erasure_H_fun.  apply IHt2. 
    inversion H.   apply surface_syntax_is_valid_syntax. auto. auto.
rewrite H0. 
    unfold erasure_H_fun. fold erasure_H_fun.
 
   assert (return_free(erasure_H_fun (t1)) = false). apply erasure_H_fun_preserve_return_free_false; auto. 
    inversion H. auto.  apply value_is_valid_syntax. auto.  rewrite H1. 
    inversion H. apply IHt1 in H4.  rewrite H4.  auto. apply value_is_valid_syntax in H4. 
    apply IHt1 in H4.  rewrite H4. auto.
-   unfold erasure_H_fun.  fold erasure_H_fun. intro.  

assert (return_free t = true \/ return_free t = false). apply exclude_middle_return_t. destruct H0.
  + rewrite H0. unfold erasure_H_fun.  auto. 
+ rewrite H0. unfold erasure_H_fun. fold erasure_H_fun. 
      assert (return_free(erasure_H_fun (t)) = false). apply erasure_H_fun_preserve_return_free_false; auto. 
      inversion H;  auto. rewrite H1. assert (erasure_H_fun (erasure_H_fun t) = erasure_H_fun t). apply IHt. 
      inversion H. auto. rewrite H2.  auto.
 - assert (return_free t = true \/ return_free t = false). apply exclude_middle_return_t. destruct H.
  + unfold erasure_H_fun. rewrite H. auto. 
  +  unfold erasure_H_fun. rewrite H. fold erasure_H_fun. intro. 
      assert (return_free(erasure_H_fun (t)) = false). apply erasure_H_fun_preserve_return_free_false; auto. 
      inversion H0;  auto. apply value_is_valid_syntax. auto. 
      rewrite H1. assert (erasure_H_fun (erasure_H_fun t) = erasure_H_fun t). apply IHt.
      inversion H0. auto.  apply value_is_valid_syntax. auto.  rewrite H2.  auto.
  - assert (return_free t = true \/ return_free t = false). apply exclude_middle_return_t. destruct H.
  + unfold erasure_H_fun. rewrite H. auto. 
  +  unfold erasure_H_fun. rewrite H. fold erasure_H_fun. intro. 
      assert (return_free(erasure_H_fun (t)) = false). apply erasure_H_fun_preserve_return_free_false; auto. 
      inversion H0;  auto. apply value_is_valid_syntax. auto. 
      rewrite H1. assert (erasure_H_fun (erasure_H_fun t) = erasure_H_fun t). apply IHt.
      inversion H0. auto.  apply value_is_valid_syntax. auto.  rewrite H2.  auto.
Qed. 
*)

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


Lemma lookup_erasure_heap_none : forall h o, 
   lookup_heap_obj h o = None -> 
   lookup_heap_obj (erasure_heap h) o = None.
Proof. induction h. intros. auto. unfold lookup_heap_obj. unfold erasure_heap. induction a. intro o0. 
  case_eq (beq_oid o0 o). intros. inversion H0. intro. fold lookup_heap_obj. fold erasure_heap. induction h0.  
   case_eq (flow_to l0 L_Label). intro. unfold lookup_heap_obj. rewrite H. fold lookup_heap_obj. apply IHh.
  intro. apply IHh. 
Qed.  

Lemma erasure_heap_no_H_label : forall h cls F lb,
  forall o, lookup_heap_obj (erasure_heap h) o = Some (Heap_OBJ cls F lb) -> 
     flow_to lb L_Label = true.
Proof. induction h. intros. unfold  erasure_heap in H. unfold lookup_heap_obj in H. inversion H.
   induction a. intros. unfold  erasure_heap in H. unfold lookup_heap_obj in H. induction h0.  
    case_eq (flow_to l0 L_Label). intro. rewrite H0 in H. case_eq (beq_oid o0 o). intro. rewrite H1 in H. inversion H.
    rewrite H5 in H0. auto. intro. rewrite H1 in H. fold erasure_heap in H.  fold lookup_heap_obj in H.
    apply IHh with cls F o0; auto.  intro. rewrite H0 in H.  fold erasure_heap in H.  fold lookup_heap_obj in H.
    apply IHh with cls F o0; auto.
Qed. 

Lemma beq_oid_equal : forall o o0, 
      beq_oid o o0 = true -> o = o0. 
Admitted. 

Lemma heap_lookup : forall h h' CT o ho, 
    wfe_heap CT h ->
    h = (o, ho) :: h' ->
    lookup_heap_obj h' o = None.
  Proof.
    intros. induction o. inversion H. rewrite <- H2 in H0. inversion H0.
    subst.  inversion H1. subst. rename h0 into h. destruct H2. 
    rewrite H0. auto. 
    destruct H0 as [o']. destruct H0 as [ho']. destruct H0 as [h'']. destruct H0.  induction o'. 
    apply compare_oid_nat in H2. apply fresh_heap with h'' CT n0 ho'; auto. 
Qed. 

Lemma lookup_none_in_erasured_heap : forall o h, 
    lookup_heap_obj h o = None ->
    lookup_heap_obj (erasure_heap h) o = None.
Proof. induction h. unfold erasure_heap. auto.
    intro. induction a. unfold erasure_heap. induction h0.
    case_eq (flow_to l0 L_Label). intro. fold lookup_heap_obj.
    fold erasure_heap. unfold lookup_heap_obj. 
    unfold lookup_heap_obj in H. case_eq (beq_oid o o0). intro. 
    rewrite H1 in H. inversion H. intro.  rewrite H1 in H. fold lookup_heap_obj in H.
    fold lookup_heap_obj. apply IHh. auto.
    intro. fold erasure_heap. unfold lookup_heap_obj in H.
    case_eq (beq_oid o o0). intro.  rewrite H1 in H. inversion H.
    intro. rewrite H1 in H. fold lookup_heap_obj in H. apply IHh. auto.
Qed. 

Lemma lookup_erasure_heap_erasured : forall h o cls F lb CT, 
       wfe_heap CT h ->
   lookup_heap_obj h o = Some (Heap_OBJ cls F lb) -> 
   flow_to lb L_Label = false -> 
   lookup_heap_obj (erasure_heap h) o = None.
Proof. induction h. intros. unfold lookup_heap_obj in H0. inversion H0. 
      induction a. intros. 
      case_eq ( beq_oid o0 o). intro. unfold lookup_heap_obj. 
      unfold erasure_heap. rename h0 into ho. induction ho.
      case_eq (flow_to l0 L_Label). unfold lookup_heap_obj in H0.
      rewrite H2 in H0. inversion H0. subst. intro. rewrite H1 in H3. inversion H3.

      intro. assert ( lookup_heap_obj h o0 = None). 
      apply heap_lookup with ((o, Heap_OBJ c f l0) :: h) CT (Heap_OBJ c f l0); auto. 
      apply beq_oid_equal in H2.
      rewrite H2. auto.
      fold lookup_heap_obj. fold erasure_heap.  apply lookup_none_in_erasured_heap.
      auto.
     intro.  unfold lookup_heap_obj in H0. 
     rewrite H2 in H0. fold lookup_heap_obj in H0.
     unfold lookup_heap_obj. unfold erasure_heap. fold lookup_heap_obj. induction h0. 
     case_eq (flow_to l0 L_Label). unfold lookup_heap_obj. rewrite H2.  fold lookup_heap_obj.
     fold erasure_heap. intro.  apply IHh with cls F lb CT; auto.  
    inversion H. inversion H4. subst. auto.
     intro.      fold erasure_heap. apply IHh with cls F lb CT. 
    inversion H. inversion H4. subst. auto. auto. auto.  
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
  + induction a. unfold erasure_stack. unfold erasure_stack. 
      case_eq (flow_to l0 L_Label).  intro. rewrite H.  fold erasure_stack.

      assert ( forall a,  (erasure_obj_null (erasure_obj_null (s0 a) h) h) = erasure_obj_null (s0 a) h).
      intro a. apply erasure_obj_null_equal. 
      assert ( forall x,  (fun x : id => erasure_obj_null (erasure_obj_null (s0 x) h) h) x  = (fun x : id => erasure_obj_null (s0 x) h) x).
      intro x.  apply H0. apply functional_extensionality in H1.  rewrite H1. rewrite IHs.  auto.
      
      intro. fold erasure_stack. auto. 
Qed. 

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

Lemma multi_erasure_sigma_helper : forall s h, 
  (erasure_stack (erasure_stack s h) (erasure_heap h)) = (erasure_stack s h).
  intros. induction s. unfold erasure_stack. auto. 
  induction a. remember (erasure_stack (Labeled_frame l0 s0 :: s) h) as Hy. 
  unfold  erasure_stack in HeqHy. 
  unfold erasure_stack. rewrite HeqHy.   fold erasure_stack. fold erasure_stack in HeqHy.
  case_eq (flow_to l0 L_Label).  intro.  rewrite H in HeqHy.  
  unfold erasure_stack. rewrite H. fold erasure_stack. 
  

  assert (forall a,  (fun x : id =>
   erasure_obj_null (erasure_obj_null (s0 x) h) (erasure_heap h)) a = (fun x : id => erasure_obj_null (s0 x) h) a).
  intro a. apply erasure_obj_null_equal_erasure_h. apply functional_extensionality in H0. rewrite H0. rewrite IHs.  
  auto. intro. rewrite H in HeqHy.  auto. 
Qed. 

Lemma multi_erasure_sigma_equal : forall s h, 
   erasure_sigma_fun (erasure_sigma_fun (SIGMA s h)) = (erasure_sigma_fun (SIGMA s h)).
  Proof. 
  intros s h. unfold erasure_sigma_fun. assert (erasure_heap (erasure_heap h) = (erasure_heap h)). 
  apply multi_erasure_heap_equal. rewrite H.
  assert ((erasure_stack (erasure_stack s h) (erasure_heap h)) = (erasure_stack s h)). 
  apply multi_erasure_sigma_helper. rewrite H0. auto. 
Qed.  


Lemma flow_join_label : forall lb joined_lb lb' L,
  flow_to lb L = false ->
  lb' = join_label joined_lb lb ->
  flow_to lb' L = false.
Proof. Admitted. 

Lemma flow_transitive : forall lb lb',
  flow_to lb' L_Label = false ->
  flow_to lb lb' = true ->
  flow_to lb L_Label = false.
Proof. Admitted. 

Lemma flow_no_H_to_L : forall lb lb',
  flow_to lb L_Label = true ->
  flow_to lb' L_Label = false ->
  flow_to lb lb' = false.
Proof. Admitted. 

Lemma erasure_sigma_fun_preserve_heap : forall h s1 h1' s2 s1' s2' h2' , 
    SIGMA s1' h1' = erasure_sigma_fun (SIGMA s1 h) ->
    SIGMA s2' h2' = erasure_sigma_fun (SIGMA s2 h) ->
    h1' = h2' .
Proof. 
  intros. unfold erasure_sigma_fun in H. unfold erasure_sigma_fun in H0. 
  inversion H. inversion H0.  auto. 
Qed. 



Lemma join_label_commutative : forall l1 l2, 
    join_label l1 l2 = join_label l2 l1. 
Proof. Admitted. 

 Lemma erasure_sigma_equal_after_erasure : forall ct t t' sigma sigma', 
    Config ct t sigma =e=> Config ct t' sigma' ->
    erasure_sigma_fun sigma =     erasure_sigma_fun sigma'.
 Proof. 
    intros ct t t' sigma sigma'.  intro H_erasure.  inversion H_erasure; subst;  rewrite H6;
    pose proof (multi_erasure_sigma_equal s h); auto.
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
    inversion H_typing. subst. inversion H2. subst. destruct H15 as [F'].   destruct H0 as [lo]. 
    destruct H13 as [field_defs0]. destruct H1 as [method_defs0]. rewrite <- H6 in H0. inversion H0.
    subst. rewrite <- H3 in H4. inversion H4.  
   assert ( exists cn field_defs method_defs, CT cn = Some cls_def
               /\ cls_def = (class_def cn field_defs method_defs)). 
    apply heap_consist_ct with h o F' lo; auto. rewrite H9 in H6. auto.
    destruct H1 as [cls_name].     destruct H1 as [field_defs].
    destruct H1 as [method_defs].     destruct H1. 
    rewrite H11 in H9. inversion H9. subst.
    destruct H with o (class_def cls_name field_defs method_defs) 
          F' cls_name lo method_defs field_defs i  cls'; auto. 
    destruct H11. destruct H12. rewrite H11 in H7. inversion H7. rewrite H12. auto.
    destruct H12 as [o'].     destruct H12 as [F_f]. destruct H12 as [lx]. 
    destruct H12 as [f_field_defs].     destruct H12 as [f_method_defs]. destruct H12. 
    rewrite H11 in H7. inversion H7. rewrite H12. auto.
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
  + subst. destruct IHt with h' s' T0 e'; auto.
  + subst. auto.
Qed.

Lemma surface_syntax_H_erasure_dot : forall t,
surface_syntax t = true -> 
erasure_H_fun t = dot.
Proof. intro t. intro Hy. induction t; unfold surface_syntax in Hy; fold surface_syntax in Hy; inversion Hy;
try (unfold erasure_H_fun; auto; fold erasure_H_fun;
      apply surface_syntax_is_return_free in Hy; rewrite Hy; auto ;fail);
try (apply surface_syntax_if in Hy; destruct Hy; unfold erasure_H_fun; fold erasure_H_fun;
apply surface_syntax_is_return_free in H; apply surface_syntax_is_return_free in H1;
rewrite H; rewrite H1; auto).
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
    inversion H_typing. subst.  inversion H5. subst. destruct H15 as [F'].  destruct H3 as [lo]. 
    destruct H13 as [field_defs0]. destruct H4 as [method_defs0]. rewrite <- H7 in H6. inversion H6.
    subst. rewrite <- H0 in H3. inversion H3. subst. 
remember (class_def clsT field_defs0 method_defs0) as cls_def.
   assert ( exists cn field_defs method_defs, CT cn = Some cls_def
               /\ cls_def = (class_def cn field_defs method_defs)). 
    apply heap_consist_ct with h o F' lo; auto. 
    destruct H4 as [cls_name].     destruct H4 as [field_defs].
    destruct H4 as [method_defs].     destruct H4. 
    rewrite Heqcls_def in H10. inversion H10. subst.
    destruct H with o (class_def cls_name field_defs method_defs) 
          F' cls_name lo method_defs field_defs fname  cls'; auto. 
    destruct H11. rewrite H11 in H1. inversion H1. destruct H12.  rewrite H12. auto.
    destruct H12 as [o'].     destruct H12 as [F_f]. destruct H12 as [lx]. 
    destruct H12 as [f_field_defs].     destruct H12 as [f_method_defs]. destruct H12. 
    rewrite H12. auto.
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
   destruct IHH_reduction with (classTy clsT) sigma'0 h s e1' e1; auto. 
    inversion H1; subst; inversion H_reduction.
-  inversion H_valid_syntax. inversion H_typing. subst. 
   destruct IHH_reduction with (classTy cls') sigma'0 h s e2' e2; auto. subst. 
    apply surface_syntax_is_valid_syntax. auto.  subst.  
   apply Valid_FieldWrite2. auto. inversion H_typing. subst. 
destruct IHH_reduction with (classTy cls') sigma'0 h s e2' e2; auto.
-  inversion H_valid_syntax. inversion H_typing. subst.  
    apply Valid_return. 
   destruct IHH_reduction with T0 sigma'0 h s e' e; auto.
-   inversion H_valid_syntax. auto.  apply surface_syntax_is_valid_syntax. auto. 
- inversion H_typing. subst.  inversion H9.  inversion H5. 
- inversion H_valid_syntax. inversion H_typing. subst. 
  apply Valid_sequence1.
destruct IHH_reduction with T0 sigma'0 h s s1' s1; auto. auto. subst. 
inversion H1; subst; inversion H_reduction. 
- inversion H_valid_syntax. apply surface_syntax_is_valid_syntax. auto.  auto. 
Qed. 

Lemma surface_syntax_imple_plus : forall t, 
  surface_syntax t = true ->  surface_syntax_plus_dot t = true.
Proof. intros. induction t; try (unfold surface_syntax in H; inversion H; fail) ;
  try (unfold surface_syntax_plus_dot; auto; fail); 
 try (unfold surface_syntax_plus_dot; fold surface_syntax_plus_dot; apply surface_syntax_if in H; destruct H;
  apply IHt1 in H; rewrite H;   apply IHt2 in H0; rewrite H0; auto).
Qed.

Lemma surface_syntax_equal_after_erasure : forall t,
   surface_syntax t = true -> erasure_L_fun t = t. 
Proof. intros. induction t; try (unfold surface_syntax in H; fold surface_syntax in H; inversion H; auto); 
try (apply IHt in H; unfold erasure_L_fun; fold erasure_L_fun; rewrite H; auto);
try  (unfold erasure_L_fun; fold erasure_L_fun; apply surface_syntax_if in H; destruct H;
    apply IHt1 in H; apply IHt2 in H0; rewrite H; rewrite H0;  auto).
Qed.  

Lemma erasure_H_fun_imply_return_free : forall t, 
  valid_syntax t ->
  erasure_H_fun t = dot -> return_free t = true.
Proof.   intro t. intro H_valid. intro.  induction t; try (unfold  erasure_H_fun in H; inversion H; fail);
  try (unfold return_free; auto; fail);
  try (unfold return_free; fold return_free;
  unfold erasure_H_fun in H;  fold erasure_H_fun in H;
  pose proof (exclude_middle_return_t t) as Hy; destruct Hy as [H_true | H_false];
  auto; rewrite H_false in H; inversion H; fail).
  unfold return_free; fold return_free;   unfold erasure_H_fun in H;  fold erasure_H_fun in H;
pose proof (exclude_middle_return_t t1) as Hy1; destruct Hy1 as [H1_true | H1_false];
pose proof (exclude_middle_return_t t2) as Hy2; destruct Hy2 as [H2_true | H2_false].
rewrite H1_true; rewrite H2_true;  auto. rewrite H1_true in H; rewrite H2_false in H; inversion H.
rewrite H1_false in H; inversion H. rewrite H1_false in H; inversion H.
 
  unfold return_free; fold return_free;   unfold erasure_H_fun in H;  fold erasure_H_fun in H;
pose proof (exclude_middle_return_t t1) as Hy1; destruct Hy1 as [H1_true | H1_false];
pose proof (exclude_middle_return_t t2) as Hy2; destruct Hy2 as [H2_true | H2_false].
rewrite H1_true; rewrite H2_true;  auto. rewrite H1_true in H; rewrite H2_false in H; inversion H.
rewrite H1_false in H; inversion H. rewrite H1_false in H; inversion H.

  unfold return_free; fold return_free.
inversion H_valid. pose proof (surface_syntax_is_valid_syntax t1 H2). pose proof (surface_syntax_is_valid_syntax t2 H5).
apply IHt1 in H6. apply IHt2 in H7. rewrite H6. rewrite H7. auto. 
apply surface_syntax_H_erasure_dot. auto. apply surface_syntax_H_erasure_dot. auto. 
 
  unfold return_free; fold return_free;   unfold erasure_H_fun in H;  fold erasure_H_fun in H;
pose proof (exclude_middle_return_t t1) as Hy1; destruct Hy1 as [H1_true | H1_false];
pose proof (exclude_middle_return_t t2) as Hy2; destruct Hy2 as [H2_true | H2_false].
rewrite H1_true; rewrite H2_true;  auto. rewrite H1_true in H; rewrite H2_false in H.
apply IHt2 in H. rewrite H in H2_false. inversion H2_false. inversion H_valid. 
apply surface_syntax_is_valid_syntax. auto. auto. 
rewrite H1_false in H. inversion H.
rewrite H1_false in H. inversion H.

unfold erasure_H_fun in H. fold erasure_H_fun in H. case_eq ( return_free t); intro; rewrite H0 in H; inversion H.
Qed. 

Lemma return_free_imply_erasure_H_fun_dot : forall t, 
valid_syntax t ->
return_free t = false -> erasure_H_fun t <> dot. 
Proof. intro t.  intro H_valid. intros. induction t; try (unfold return_free in H; inversion H; fail);
  try (unfold return_free in H; fold return_free in H; unfold erasure_H_fun; 
       fold erasure_H_fun; rewrite H; intuition; inversion H0);
  try (unfold return_free in H; fold return_free in H; unfold erasure_H_fun;
       fold erasure_H_fun; apply  return_free_if_false in H; destruct H) ;
  try (rewrite H; intuition; inversion H0);
  try (destruct H; rewrite H; rewrite H0; intuition; inversion H1; fail).
  inversion H_valid. apply surface_syntax_is_return_free in H2. rewrite H2 in H. inversion H.
  destruct H. 
  inversion H_valid. apply surface_syntax_is_return_free in H6. rewrite H6 in H0. inversion H0.
  unfold   erasure_H_fun. destruct H. rewrite H. rewrite H0.  fold erasure_H_fun. intro contra. 
  apply erasure_H_fun_imply_return_free in contra. rewrite H0 in contra. inversion contra.  
  inversion H_valid. apply surface_syntax_is_valid_syntax. auto. auto. 
 case_eq (return_free t); intro; intro contra; inversion contra; unfold erasure_H_fun in contra;
 rewrite H0 in contra; inversion contra.  Qed. 

Lemma return_free_true_imply_erasure_H_fun_dot : forall t, 
valid_syntax t ->
return_free t = true -> erasure_H_fun t = dot. 
Proof. intro t.  intro H_valid. intros. induction t; try (unfold return_free in H; inversion H; fail);
  try (unfold return_free in H; fold return_free in H; unfold erasure_H_fun; 
       fold erasure_H_fun; rewrite H; intuition; inversion H0);
  try (unfold return_free in H; fold return_free in H; unfold erasure_H_fun;
       fold erasure_H_fun; apply  return_free_if_false in H; destruct H) ;
  try (rewrite H; intuition; inversion H0);
  try (destruct H; rewrite H; rewrite H0; intuition; inversion H1; fail);
  try (unfold erasure_H_fun; auto; fail);
  try (unfold return_free in H; fold return_free in H; apply return_free_if in H; destruct H;
  unfold  erasure_H_fun; rewrite H; rewrite H0; auto). 
Qed. 



Lemma erasure_H_fun_imply_return_free_false : forall t, 
  valid_syntax t ->
  erasure_H_fun t <> dot -> return_free t = false.
Proof.   intro t. intro H_valid. intro.
  induction t; try (unfold erasure_H_fun in H; intuition; fail); fold erasure_H_fun in H;
  try (
  unfold erasure_H_fun in H; fold erasure_H_fun in H);
  try (case_eq (return_free t ); intro; rewrite H0 in H; intuition); 
  try (unfold return_free; auto; fail).
   try (case_eq (return_free t1 ); intro; rewrite H0 in H; intuition); 
   try (case_eq (return_free t2 ); intro; rewrite H1 in H; intuition).
  unfold  return_free. fold return_free. rewrite H0. rewrite H1. auto. 
  unfold  return_free. fold return_free. rewrite H0. auto. 
   try (case_eq (return_free t1 ); intro; rewrite H0 in H; intuition); 
   try (case_eq (return_free t2 ); intro; rewrite H1 in H; intuition).
  unfold  return_free. fold return_free. rewrite H0. rewrite H1. auto. 
  unfold  return_free. fold return_free. rewrite H0. auto. 
   try (case_eq (return_free t1 ); intro; rewrite H0 in H; intuition); 
   try (case_eq (return_free t2 ); intro; rewrite H1 in H; intuition).
  unfold  return_free. fold return_free. rewrite H0. rewrite H1. auto. 
  unfold  return_free. fold return_free. rewrite H0. auto. 
Qed. 


Lemma erasure_H_fun_equal_return_free : forall t t', 
valid_syntax t -> valid_syntax t' ->
erasure_H_fun t = erasure_H_fun t' ->
return_free t = return_free t'.
Proof. 
intros. case_eq (return_free t). intro. apply return_free_true_imply_erasure_H_fun_dot in H2. 
rewrite H2 in H1. assert (erasure_H_fun t' = dot). auto.  apply erasure_H_fun_imply_return_free in H3. auto. 
auto. auto. intro.   apply return_free_imply_erasure_H_fun_dot in H2.  rewrite H1 in H2. 
apply erasure_H_fun_imply_return_free_false in H2. auto. auto. auto. 
Qed. 



Lemma lookup_update_heap : forall h o cls F lb, 
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

Lemma flow_false_trans : forall lb1 lb2, 
flow_to lb1 L_Label = false ->
flow_to lb2 lb1 = true ->
flow_to lb2 L_Label = false.
Admitted.  

Lemma exclude_middle_return : (forall t, ((exists v, t = Return v) \/ (forall v, t <> Return v))).
  Proof with eauto. intro t. induction t; try (right; intro v0; intro contra; inversion contra; fail).
  left. exists t. auto. Qed. 

      Hint Constructors value.
Lemma excluded_middle_value : forall t,
  (value t) \/ ~ value t.
  Proof with eauto.
    intros. induction t; try (left; auto; fail); try (right; intro contra; inversion contra;fail).
    destruct IHt. left; auto. right. intro contra. inversion contra. intuition. 
      destruct IHt. left; auto. right. intro contra. inversion contra. intuition. 
Qed. 

Reserved Notation "c '==l>' c'"
  (at level 40, c' at level 39).

Inductive l_reduction : config -> config -> Prop :=
    | L_reduction : forall c1 c2 c2_r, 
      c1 ==> c2 ->
      c2 =e=> c2_r ->
      l_reduction c1 c2_r
where "c '==l>' c'" := (l_reduction c c').


(* wrong lemma 
Lemma return_value_preserve_H_context : forall s h s' h' v t' CT, 
    flow_to (current_label (SIGMA s h)) L_Label = false ->
    value v->
    Config CT (Return v) (SIGMA s h) ==> Config CT t' (SIGMA s' h') ->
    flow_to (current_label (SIGMA s' h')) L_Label = false.
    Proof. intros s h s' h' v t' CT. intro H_flow. intro H_v.  intro H_reduction. 
      inversion H_v; subst; inversion H_reduction; try (inversion H0 ; subst; rewrite H10; fail); 
      try (inversion H1 ; subst; rewrite H11);
      try (inversion H5; inversion H10);       try (inversion H6; inversion H11); try (subst;  induction s'0; intuition; induction a; induction lsf; 
      unfold current_label in H_flow; unfold get_stack in H_flow; unfold get_current_label in H_flow; 
      unfold get_stack_label in H_flow;
      
      unfold update_current_label; unfold current_label; unfold get_stack;
      unfold get_current_label;       unfold get_stack; unfold get_current_label;
      unfold get_stack_label; 
      apply flow_join_label with l1 l0; auto; 
          apply join_label_commutative; auto). 
Qed.  
*) 

      Lemma multi_erasure_stack_helper : forall s h CT,
      wfe_heap CT h -> 
  (erasure_stack s h)  = (erasure_stack s (erasure_heap h)).
  Proof. intros. induction s. unfold erasure_stack. auto. 
  induction a. remember (erasure_stack (Labeled_frame l0 s0 :: s) h) as Hy. 
  unfold  erasure_stack in HeqHy. 
  unfold erasure_stack. rewrite HeqHy.   fold erasure_stack.
  
  assert (forall a,  (fun x : id => erasure_obj_null (s0 x) h) a =
               (fun x : id => erasure_obj_null (s0 x) (erasure_heap h)) a).
  intro a.
  
  Lemma erasure_obj_null_equal_erasure_h_helper : forall h t CT,
      wfe_heap CT h ->
      erasure_obj_null t h = erasure_obj_null t (erasure_heap h).
      Proof. intros. induction t. induction a; try (unfold erasure_obj_null; auto). 
          assert (forall h o, (exists cls F lb, lookup_heap_obj h o = Some (Heap_OBJ cls F lb) ) 
          \/ lookup_heap_obj h o = None).
        intro h0. induction h0.  right. unfold lookup_heap_obj. auto. 
        intro o0. induction a. case_eq ( beq_oid o0 o1). unfold lookup_heap_obj.  intro. unfold lookup_heap_obj. rewrite H0. 
         rename h1 into ho. induction ho.     left. exists c. exists f. exists l0. auto. 
        intro. unfold lookup_heap_obj. rewrite H0. fold lookup_heap_obj. apply IHh0. 
        destruct H0 with h o. destruct H1 as [cls]. destruct H1 as [F]. destruct H1 as [lb]. rewrite H1.
        case_eq (flow_to lb L_Label ). intro. 
        assert (exists F', lookup_heap_obj (erasure_heap h) o = Some (Heap_OBJ cls F' lb)).
        apply lookup_erasure_heap with F. auto. auto. destruct H3 as [F']. rewrite H3. rewrite H2. auto. 
       intro.   assert ( lookup_heap_obj (erasure_heap h) o = None).  apply lookup_erasure_heap_erasured with cls F lb CT; auto. 
        rewrite H3. auto. rewrite H1. auto. assert (lookup_heap_obj (erasure_heap h) o  = None). 
       apply lookup_none_in_erasured_heap. auto. rewrite H2. auto.
      (unfold erasure_obj_null; auto).
    Qed.
    apply erasure_obj_null_equal_erasure_h_helper with CT. auto.
     apply functional_extensionality in H0. rewrite H0. auto.
     rewrite IHs. auto. 
  Qed.

Lemma exclude_middle_unlabelOpaque : (forall t, ((exists v, value v /\ t = unlabelOpaque v) 
        \/ (forall v, t <> unlabelOpaque v) 
          \/ (exists t', t = unlabelOpaque t' /\ ~ value t'))).
  Proof with eauto. intro t. induction t; try (right; left; intro v0; intro contra; inversion contra; fail).
  pose proof (excluded_middle_value t). destruct H. left. exists t. auto.
  right. right. exists t. auto. Qed.


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

Lemma multi_step_concat : forall c c1 c2, 
 c ==>L*  c1 ->
 c1 ==>L*  c2 ->
 c ==>L*  c2.
Proof. intros c c1 c2. 
  intro Hy1.   intro Hy2.
  induction Hy1.   auto. 
  apply IHHy1 in Hy2. apply multi_reduction_l_step with c0; auto. 
Qed. 



(*
Lemma erasure_sigma_preserve_context : forall s h s' h', 
  SIGMA s' h' = erasure_sigma_fun (SIGMA s h) ->
  flow_to (current_label (SIGMA s' h')) L_Label = flow_to (current_label (SIGMA s h)) L_Label.
Proof. intros.
 unfold erasure_sigma_fun in H. unfold erasure_stack in H.  induction s. 
 inversion H. auto. 
  induction a. rewrite H. unfold current_label. unfold get_stack. unfold get_current_label.
  unfold get_stack_label. auto.  
Qed. 

Lemma erasure_preserve_context : forall s h s' h' t t' CT, 
      Config CT t (SIGMA s h) =e=> (      Config CT t' (SIGMA s' h')) ->
      (flow_to (current_label (SIGMA s' h')) L_Label = flow_to (current_label (SIGMA s h)) L_Label ).
    Proof. intros. inversion H; apply erasure_sigma_preserve_context; auto. Qed.  
*)


Lemma lookup_heap_obj_two_cases : forall h o, 
  ((exists cls F lb, lookup_heap_obj h o = Some (Heap_OBJ cls F lb) ) 
      \/ (lookup_heap_obj h o = None)).
  Proof.   intro h0. induction h0.  right. unfold lookup_heap_obj. auto. 
    intro o0. induction a. case_eq ( beq_oid o0 o). unfold lookup_heap_obj.  intro. unfold lookup_heap_obj. rewrite H.
    rename h into ho. induction ho.     left. exists c. exists f. exists l0. auto. 
    intro. unfold lookup_heap_obj. rewrite H. fold lookup_heap_obj. apply IHh0.
Qed. 


  Lemma erasure_obj_null_result : forall t h, 
    (erasure_obj_null (Some t) h = None) \/ (erasure_obj_null (Some t) h = Some null)
   \/ (exists o, erasure_obj_null (Some t) h = Some (ObjId o)) \/ (erasure_obj_null (Some t) h = Some dot).
  Proof. induction t; intros; try (left; auto; fail). right. left.  auto.  unfold erasure_obj_null. 
    pose proof (lookup_heap_obj_two_cases h o). destruct H. destruct H as [cls]. destruct H as [F]. destruct H as [lb]. rewrite H.
    case_eq (flow_to lb L_Label). intro. right. right. left.  exists o. auto.  intro. right. right. right. auto. 
    rewrite H. right. right. right.  auto. right. right. right.  auto. 
Qed. 

  Lemma erasure_obj_null_option_result : forall option_t h, 
    (erasure_obj_null (option_t) h = None) \/ (erasure_obj_null (option_t) h = Some null)
   \/ (exists o, erasure_obj_null (option_t) h = Some (ObjId o)) \/ (erasure_obj_null (option_t) h = Some dot).
  Proof.  induction option_t. intro h.  apply erasure_obj_null_result. intro h. left. auto.   Qed. 

Lemma erasure_H_fun_preserve_value : forall v, 
  value v ->
  value (erasure_H_fun v).
Proof. 
  intros. induction v; try (inversion H); try ( unfold erasure_H_fun; auto; fail).
  unfold erasure_H_fun. fold erasure_H_fun. apply value_is_return_free in H1. rewrite H1. auto.
    unfold erasure_H_fun. fold erasure_H_fun. apply value_is_return_free in H1. rewrite H1. auto.
Qed.

Lemma field_in_erasured_heap : forall h o cls fields lb t0 i, 
    Some (Heap_OBJ cls fields lb) = lookup_heap_obj (erasure_heap h) o ->
    Some t0 = fields i ->
    valid_syntax t0.
  Proof. intros.  induction h. unfold erasure_heap in H. unfold  lookup_heap_obj in H. inversion H.  
   unfold lookup_heap_obj in H. induction a. unfold erasure_heap in H. rename h0 into ho.
    induction ho. case_eq (flow_to l0 L_Label). intro. rewrite H1 in H. case_eq (beq_oid o o0). intro. 
   rewrite H2 in H.  inversion H. rewrite H5 in H0. subst.
  assert ((erasure_obj_null (f i)  ((o0, Heap_OBJ c f l0) :: h) = None) \/ (erasure_obj_null (f i)  ((o0, Heap_OBJ c f l0) :: h) = Some null)
   \/ (exists o, erasure_obj_null (f i)  ((o0, Heap_OBJ c f l0) :: h) = Some (ObjId o)) \/ (erasure_obj_null (f i)  ((o0, Heap_OBJ c f l0) :: h) = Some dot)).
  apply erasure_obj_null_option_result. destruct H3; try (rewrite H3 in H0; inversion H0). destruct H3. rewrite H3 in H0.
  inversion H0. auto. destruct H3. destruct H3 as [o']. rewrite H3 in H0. inversion H0. auto. rewrite H3 in H0. inversion H0. auto. 
  intro. rewrite H2 in H. fold lookup_heap_obj in H. fold erasure_heap in H. apply IHh in H. auto.
  intro. rewrite H1 in H. fold lookup_heap_obj in H. fold erasure_heap in H. apply IHh in H. auto.
Qed. 

Hint Constructors valid_syntax. 
Lemma valid_syntax_preservation_erasure_H : forall t, 
     valid_syntax t -> valid_syntax (erasure_H_fun t).
Proof with eauto. induction t; intro; try (unfold erasure_H_fun; auto); fold erasure_H_fun;
        try (case_eq (return_free t); auto; intro ; inversion H; auto).
    case_eq (return_free t1). auto. intro . case_eq (return_free t2). intro. auto. 
    intro. inversion H. apply surface_syntax_is_return_free in H6.  rewrite H6 in H1. inversion H1.
    apply Valid_MethodCall2. auto. auto.      
    intro. inversion H. apply Valid_MethodCall1. auto.  auto. 
    apply value_is_return_free in H3. rewrite H3 in H0. inversion H0. 

    case_eq (return_free t1). auto. intro . case_eq (return_free t2). intro. auto. 
    intro. inversion H. apply surface_syntax_is_return_free in H6.  rewrite H6 in H1. inversion H1.
    apply Valid_FieldWrite2. auto. auto.      
    intro. inversion H. apply Valid_FieldWrite1. auto.  auto. 
    apply value_is_return_free in H3. rewrite H3 in H0. inversion H0.

    case_eq (return_free t1). auto. intro . case_eq (return_free t2). intro. auto. 
    intro. inversion H. apply surface_syntax_is_return_free in H5.  rewrite H5 in H1. inversion H1. auto. 
    intro.  inversion H.  apply Valid_sequence1; auto. apply value_is_return_free in H3. rewrite H3 in H0. inversion H0.
    
   apply Valid_v_l. apply erasure_H_fun_preserve_value.  auto. 
   apply Valid_v_opa_l. apply erasure_H_fun_preserve_value.  auto.
Qed.  


Lemma valid_syntax_preservation_erasured : forall CT t t' s h sigma', 
      valid_syntax t ->
      forall T, has_type CT empty_context h t T -> 
      wfe_heap CT h -> 
      Config CT t (erasure_sigma_fun (SIGMA s h)) ==> Config CT t' sigma' ->
      valid_syntax t'. 
Proof. 
 intros CT t t' s h sigma'.   intro H_valid_syntax. intro T. intro H_typing. intro H_wfe_heap.
    intro H_reduction.
    remember (Config CT t (erasure_sigma_fun (SIGMA s h))) as config. 
    remember (Config CT t' sigma') as config'. 
generalize dependent t. generalize dependent t'. 
generalize dependent s. generalize dependent h.
generalize dependent sigma'. generalize dependent T.
induction H_reduction; intros; inversion Heqconfig; inversion Heqconfig'; subst; auto.
-  inversion H_typing. subst. inversion H4. 
- inversion H_valid_syntax. inversion H_typing. subst. 
   destruct IHH_reduction with (classTy clsT) sigma'0 h s e' e; auto. 
- inversion H8. subst. apply field_in_erasured_heap with h0 o cls fields lb fname; auto.
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
  destruct H16 as [F']. destruct H as [lo].   case_eq (flow_to lo L_Label ). intro. 
  assert (exists F', lookup_heap_obj (erasure_heap h0) o = Some (Heap_OBJ cls_def0 F' lo)).
  apply lookup_update_heap with F'; auto. destruct H10 as [F0]. rewrite H10 in H0. 
  inversion H0.  subst. 
  rewrite H8 in H1. inversion H1. subst. apply Valid_return. apply surface_syntax_is_valid_syntax. auto. 
  intro. assert (lookup_heap_obj (erasure_heap h0) o = None). 
  apply lookup_erasure_heap_erasured with cls_def0 F' lo CT; auto. 
  rewrite H10 in H0. inversion H0.  
-  inversion H_typing.  subst. inversion H11. subst. inversion H3. subst. rewrite <- H2 in H7. inversion H7. 
  destruct H16 as [F']. destruct H as [lo]. 
  case_eq (flow_to lo L_Label ). intro. 
  assert (exists F', lookup_heap_obj (erasure_heap h0) o = Some (Heap_OBJ cls_def0 F' lo)).
  apply lookup_update_heap with F'; auto. destruct H10 as [F0]. rewrite H10 in H0. inversion H0.  subst. 
  rewrite H8 in H6. inversion H6. subst. apply Valid_return. apply surface_syntax_is_valid_syntax. auto.
intro. assert (lookup_heap_obj (erasure_heap h0) o = None). 
  apply lookup_erasure_heap_erasured with cls_def0 F' lo CT; auto. 
  rewrite H10 in H0. inversion H0.  
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
   destruct IHH_reduction with (classTy clsT) sigma'0 h s e1' e1; auto. 
    inversion H1; subst; inversion H_reduction.
-  inversion H_valid_syntax. inversion H_typing. subst. 
   destruct IHH_reduction with (classTy cls') sigma'0 h s e2' e2; auto. subst. 
    apply surface_syntax_is_valid_syntax. auto.  subst.  
   apply Valid_FieldWrite2. auto. inversion H_typing. subst. 
destruct IHH_reduction with (classTy cls') sigma'0 h s e2' e2; auto.
- 
  inversion H_valid_syntax. inversion H_typing. subst.  
    apply Valid_return. 
   destruct IHH_reduction with T0 sigma'0 h s e' e; auto.
-   inversion H_valid_syntax. auto. apply surface_syntax_is_valid_syntax. auto.  
- inversion H_typing. subst.  inversion H9.  inversion H5. 
- inversion H_valid_syntax. inversion H_typing. subst. 
  apply Valid_sequence1.
destruct IHH_reduction with T0 sigma'0 h s s1' s1; auto. auto. subst. 
inversion H1; subst; inversion H_reduction. 
- inversion H_valid_syntax. apply surface_syntax_is_valid_syntax. auto.  auto. 
Qed. 


Hint Constructors has_type.
Lemma typing_preservation_erasure : forall CT h t, 
 forall T, has_type CT empty_context h t T -> has_type CT empty_context h (erasure_H_fun t) T.
Proof with eauto. induction t; intros; try (unfold  erasure_H_fun; auto; fail); 
    try (unfold  erasure_H_fun; case_eq (return_free t); intro;  auto; fold erasure_H_fun; inversion H; auto; fail).

    unfold  erasure_H_fun; case_eq (return_free t); intro;  auto. fold erasure_H_fun. inversion H. 
    apply T_FieldAccess with cls_def clsT fields_def; auto.

    unfold  erasure_H_fun; case_eq (return_free t1); intro;  auto. case_eq (return_free t2). intro. auto. 
    intro. fold erasure_H_fun. inversion H. apply T_MethodCall with Gamma' T0 cls_def body
        arg_id arguT; auto. fold erasure_H_fun. inversion H. apply T_MethodCall with Gamma' T0 cls_def body
        arg_id arguT; auto.

    unfold  erasure_H_fun; case_eq (return_free t); intro;  auto. fold erasure_H_fun. inversion H. 
    apply T_labelOf with (T0). auto.  

    inversion H. inversion H5. 
    
    unfold  erasure_H_fun; case_eq (return_free t1); intro;  auto. case_eq (return_free t2). intro. auto. 
    intro. fold erasure_H_fun. inversion H. auto.  apply T_FieldWrite with cls_def clsT cls'; auto. 
    fold erasure_H_fun. inversion H. auto.  apply T_FieldWrite with cls_def clsT cls'; auto. 

    unfold  erasure_H_fun; case_eq (return_free t1); intro;  auto. case_eq (return_free t2). intro. auto. 
    intro. fold erasure_H_fun. inversion H. auto.     fold erasure_H_fun. inversion H. apply T_sequence with T0. auto. 
    fold erasure_H_fun. inversion H. auto. 

    unfold  erasure_H_fun; case_eq (return_free t); intro;  auto. fold erasure_H_fun. inversion H. auto. 
    subst.     apply T_v_l. auto.  apply IHt.  auto.  apply erasure_H_fun_preserve_value. auto. 
    
    unfold  erasure_H_fun; case_eq (return_free t); intro;  auto. fold erasure_H_fun. inversion H. auto. 
    apply T_v_opa_l. auto. apply IHt.  auto. apply erasure_H_fun_preserve_value. auto.
Qed.  

(*
Lemma valid_syntax_erasure_reduction : forall t t0 sigma' s h CT sigma_l ,
      valid_syntax t ->  
      forall T, has_type CT empty_context h t T -> 
      flow_to (current_label (SIGMA s h)) L_Label = false ->
      field_wfe_heap CT h -> wfe_heap CT h -> wfe_stack CT h s ->
      Config CT t (SIGMA s h) =e=> Config CT  (erasure_H_fun t)  sigma' ->
      Config CT (erasure_H_fun t) sigma' ==> Config CT t0 sigma_l ->
      return_free t = false ->
      valid_syntax t0.
    Proof.  induction t. 
- intros. inversion H0. inversion H12. 
- intros. inversion H6. 
- intros. unfold erasure_H_fun in H6. fold erasure_H_fun in H6.  unfold return_free in H7. 
  fold return_free in H7. rewrite H7 in H6. inversion H6. 
++ subst. unfold erasure_H_fun in H5. 
  fold erasure_H_fun in H5. rewrite H7 in H5. inversion H5. rewrite H12 in H1. inversion H1.
  subst.   inversion H0.  
   apply Valid_FieldAccess. apply IHt with (SIGMA s' h') s h CT sigma_l (classTy clsT); auto. 
    inversion H. auto. apply erasure_H_context; auto.
++
  subst. inversion H5. rewrite H12 in H1. inversion H1. subst.  
  unfold erasure_sigma_fun in H20. inversion H20. 


apply field_in_erasured_heap with h o cls fields lb i; auto. rewrite <- H11. auto.

- intros. unfold erasure_H_fun in H6. fold erasure_H_fun in H6.  unfold return_free in H7. 
  fold return_free in H7. apply return_free_if_false in H7. destruct H7.
++ rewrite H7 in H6. inversion H6.
+++ subst.   inversion H0.  
   apply Valid_MethodCall1. subst. apply IHt1 with sigma' s h CT sigma_l (classTy T0); auto.
  inversion H. auto. apply value_is_valid_syntax. auto. inversion H5;
 apply erasure_H_context; auto.  inversion H. auto. pose proof (erasure_H_fun_preserve_value t1 H26).
  inversion H29; try (rewrite <- H31 in H9; inversion H9; fail); try (rewrite <- H30 in H9; inversion H9; fail).

+++ subst.   inversion H0.  
   apply Valid_MethodCall2. subst.  inversion H. auto. apply erasure_H_fun_preserve_value. auto.
  apply IHt2 with sigma' s h CT sigma_l (classTy arguT); auto. inversion H.   
  apply surface_syntax_is_valid_syntax; auto. auto. inversion H5;
 apply erasure_H_context; auto.  inversion H. auto. pose proof (erasure_H_fun_preserve_value t1 H26).
  inversion H29; try (rewrite <- H31 in H9; inversion H9; fail); try (rewrite <- H30 in H9; inversion H9; fail).


++ subst. unfold erasure_H_fun in H5. 
  fold erasure_H_fun in H5. rewrite H7 in H5. inversion H5. rewrite H12 in H1. inversion H1.
  subst.   inversion H0.  
   apply Valid_FieldAccess. apply IHt with (SIGMA s' h') s h CT sigma_l (classTy clsT); auto. 
    inversion H. auto. apply erasure_H_context; auto.
*)

Lemma field_value : forall h o cls F lb f t' CT cls',  
wfe_heap CT h -> field_wfe_heap CT h ->
Some (Heap_OBJ cls F lb) = lookup_heap_obj h o ->
F f = Some t' ->
has_type CT empty_context h (FieldAccess (ObjId o) f)
             (classTy cls') ->
( t' = null \/ exists o',  t' = ObjId o').
Proof. intros h o cls F lb f t' CT cls'. intro H_wfe_heap. intro H_wfe_fields. 
  intro Hy. intro Hy_Field. intro H_typing.  inversion H_typing. inversion H2. 
  subst.  destruct H16 as [F']. destruct H as [lo]. rewrite H in Hy. inversion Hy. subst.
  destruct H15 as [field_defs]. destruct H0 as [method_defs]. rewrite <- H6 in H11. inversion H11. subst. 
  inversion H_wfe_fields. subst. destruct H0 with o (class_def clsT field_defs method_defs) F' clsT lo method_defs field_defs
      f cls'; auto. destruct H1. rewrite H1 in Hy_Field. inversion Hy_Field. subst. 
  destruct H3. left. auto. 
  destruct H3 as [o']. destruct H3 as [F0]. destruct H3 as [lx]. destruct H3. destruct H3. destruct H3. right. exists o'. auto.
Qed.  

  Lemma label_equivalence : forall l l', 
    flow_to l L_Label = false -> flow_to l' L_Label = false ->
    l = l'. 
  Admitted. 

(*
Lemma erasure_value : forall v t, 
         valid_syntax t -> 
         value v -> 
         erasure_H_fun t = v -> 
         return_free t = true. 
    Proof with eauto.  induction t; intros; auto; unfold erasure_H_fun in H1; fold erasure_H_fun in H1;
    try (case_eq (return_free t ); intro; rewrite H2 in H1; unfold return_free; fold return_free; auto; subst; inversion H0 ).
        try (case_eq (return_free t1 ); intro; rewrite H2 in H1; unfold return_free; fold return_free; auto; rewrite H2; 
      case_eq (return_free t2); intro); try (auto); try (rewrite H3 in H1; rewrite <- H1 in H0; inversion H0; fail); 
        try (rewrite H2 in H1); try (rewrite H3 in H1); try (rewrite <- H1 in H0; inversion H0). 
        try (case_eq (return_free t1 ); intro; rewrite H2 in H1; unfold return_free; fold return_free; auto; rewrite H2; 
      case_eq (return_free t2); intro); try (auto); try (rewrite H3 in H1; rewrite <- H1 in H0; inversion H0; fail); 
        try (rewrite H2 in H1); try (rewrite H3 in H1); try (rewrite <- H1 in H0; inversion H0).
      inversion H. unfold return_free. fold return_free. apply surface_syntax_is_return_free in H4. 
      apply surface_syntax_is_return_free in H7. rewrite H4. rewrite H7.  auto.  
       case_eq (return_free t1); intro; rewrite H2 in H1; unfold return_free; fold return_free. rewrite H2. 
       case_eq (return_free t2). intro. auto. intro. rewrite H3 in H1. apply IHt2 in H1. rewrite H1 in H3. intuition. 
      inversion H. apply surface_syntax_is_valid_syntax. auto. auto. auto. 
      rewrite H2. rewrite <- H1 in H0. inversion H0. 
      subst. apply value_erasure_to_dot in H3.
      assert (erasure_H_fun (erasure_H_fun t)  = (erasure_H_fun t) ).
      apply multi_erasure_H_tm_equal. inversion H. apply value_is_valid_syntax. auto. 
      rewrite H1 in H3. apply erasure_H_fun_imply_return_free in H3. rewrite H3 in H2. auto. 
      inversion H. apply value_is_valid_syntax. auto. 
      subst. apply value_erasure_to_dot in H3.
      assert (erasure_H_fun (erasure_H_fun t)  = (erasure_H_fun t) ).
      apply multi_erasure_H_tm_equal. inversion H. apply value_is_valid_syntax. auto. 
      rewrite H1 in H3. apply erasure_H_fun_imply_return_free in H3. rewrite H3 in H2. auto. 
      inversion H. apply value_is_valid_syntax. auto. 
Qed. 


Lemma erasure_unlabelOpaque_return_free : forall t v, 
  valid_syntax t-> value v -> erasure_H_fun t = unlabelOpaque v ->
  return_free t = true. 
Proof with eauto. induction t; intros; auto; unfold erasure_H_fun in H1;
  fold erasure_H_fun in H1; try (case_eq (return_free t ); intro; rewrite H2 in H1; subst; inversion H1);
   try (case_eq (return_free t1 ); intro; rewrite H2 in H1); try (  case_eq (return_free t2); intro; 
  rewrite H3 in H1; inversion H1); try ( rewrite H2 in H1; inversion H1); try (inversion H1).
  assert (return_free t = true). apply erasure_value with v; auto. inversion H. auto.
  auto. 
  assert (return_free t2 = true). apply IHt2 with v; auto. inversion H. 
  apply surface_syntax_is_valid_syntax; auto. auto. rewrite H3 in H4. inversion H4. 
Qed. 
*)

Lemma flow_to_simpl : forall l0 s0 s h, 
flow_to (current_label (SIGMA (Labeled_frame l0 s0 :: s) h))
             L_Label = false -> 
flow_to l0 L_Label = false. 
Proof. intros l0 s0 s h. unfold current_label.   unfold get_stack.  
      unfold get_current_label. unfold get_stack_label. auto. Qed. 

Lemma nil_flow_to_L_Label : forall h, 
 flow_to (current_label (SIGMA nil h)) L_Label = true.
Proof.   intro h.  unfold flow_to; unfold current_label;  unfold get_stack; 
      unfold get_current_label. unfold L_Label. 
      unfold subset. auto. Qed. 


Lemma erasure_H_whole_equal_return_free : forall t t' s s', 
valid_syntax t -> valid_syntax t' ->
erasure_H_fun_whole (erasure_H_fun t) s  = erasure_H_fun_whole (erasure_H_fun t') s' ->
return_free t = return_free t'.
Proof. 
intros. unfold erasure_H_fun_whole in H1. induction s. induction s'. 
apply erasure_H_fun_equal_return_free in H1; auto. 
induction a. case_eq (flow_to l0 L_Label). intro. rewrite H2 in H1. fold erasure_H_fun_whole in H1.
apply erasure_H_fun_equal_return_free in H1; auto.
intro. rewrite H2 in H1. auto.  fold erasure_H_fun_whole in H1. fold  erasure_H_fun_whole in IHs'. 
Admitted. 
(*
rewrite H1. auto. intro. rewrite H2 in H1.  fold erasure_H_fun_whole in H1.
fold  erasure_H_fun_whole in IHs'. 
 
rewrite H2 in H1. assert (erasure_H_fun t' = dot). auto.  apply erasure_H_fun_imply_return_free in H3. auto. 
auto. auto. intro.   apply return_free_imply_erasure_H_fun_dot in H2.  rewrite H1 in H2. 
apply erasure_H_fun_imply_return_free_false in H2. auto. auto. auto. 
Qed. 
*)


 Lemma update_H_object_equal_erasure : forall h o CT cls F F' lb lb',
       wfe_heap CT h -> 
        Some (Heap_OBJ cls F lb) = lookup_heap_obj h o ->
        flow_to lb' L_Label = false ->
        flow_to lb L_Label = false ->
          erasure_heap h = erasure_heap
                                            (update_heap_obj h o
                                               (Heap_OBJ cls F' lb')).
    Proof. intros h o CT cls F F' lb lb'. intros.  induction h. unfold lookup_heap_obj in H0. inversion H0.
     induction a. case_eq (beq_oid o o0). intro. unfold update_heap_obj. rewrite H3. 

    unfold lookup_heap_obj in H0.  rewrite H3 in H0.  inversion H0. 
    unfold erasure_heap. fold erasure_heap. rewrite H2. rewrite H1.  auto. 
    intro. unfold update_heap_obj. rewrite H3.  fold update_heap_obj. 
    assert (erasure_heap h =
      erasure_heap (update_heap_obj h o (Heap_OBJ cls F' lb'))).
    apply IHh. auto.  inversion H. auto. inversion H4. subst. auto.
    unfold  lookup_heap_obj in H0. rewrite H3 in H0. fold lookup_heap_obj in H0. auto.
    unfold erasure_heap. fold erasure_heap.
    rewrite H4. auto. 

    induction h0. 
    assert ( forall a, 
     (fun x : id => erasure_obj_null (f x) ((o0, Heap_OBJ c f l0) :: h)) a
          = (fun x : id => erasure_obj_null (f x)
                     ((o0, Heap_OBJ c f l0) :: update_heap_obj h o (Heap_OBJ cls F' lb'))) a).
    Proof. intro  a. 
assert (forall h o, (exists cls F lb, lookup_heap_obj h o = Some (Heap_OBJ cls F lb) ) 
      \/ lookup_heap_obj h o = None).
    intro h1. induction h1.  right. unfold lookup_heap_obj. auto.
    intro o1.  induction a0. case_eq ( beq_oid o1 o2). unfold lookup_heap_obj.  intro. unfold lookup_heap_obj. rewrite H5.
    rename h0 into ho. induction ho.     left. exists c0. exists f0. exists l1. auto. 
    intro. unfold lookup_heap_obj. rewrite H5. fold lookup_heap_obj. apply IHh1. 
    remember ((o, Heap_OBJ c f l0) :: h) as h'. 
    case (f a). induction t; try (unfold erasure_obj_null; auto).
    

    destruct H5 with  ((o0, Heap_OBJ c f l0) :: h)  o1. 
    destruct H6 as [cls1]. destruct H6 as [F1]. destruct H6 as [lb1]. rewrite H6.

      Lemma lookup_updated_heap_equal : forall cls F lb o h cls1 F1 lb1 F' o1 lb',
          lookup_heap_obj h o = Some (Heap_OBJ cls F lb) ->
          lookup_heap_obj h o1 = Some (Heap_OBJ cls1 F1 lb1) -> 
          (lookup_heap_obj
               (update_heap_obj h o (Heap_OBJ cls F' lb')) o1  = 
                      Some (Heap_OBJ cls1 F1 lb1)) \/ 
              (lookup_heap_obj (update_heap_obj h o (Heap_OBJ cls F' lb')) o1  = 
                      Some (Heap_OBJ cls F' lb') /\ beq_oid o1 o = true).
      Proof. intros.  induction h. 
      unfold lookup_heap_obj in H0. inversion H0.  induction a.
      case_eq (beq_oid o o0). intro.

      unfold  update_heap_obj. rewrite H1.
      case_eq (beq_oid o1 o). intro.
      unfold lookup_heap_obj. rewrite H2.
      unfold lookup_heap_obj in H0. apply beq_oid_equal in H2. rewrite H2 in H0.
      rewrite H1 in H0.
      unfold lookup_heap_obj in H. rewrite H1 in H. rewrite H0 in H. inversion H. subst.  
      right. auto. 
      intro. unfold lookup_heap_obj. rewrite H2. fold lookup_heap_obj.
      unfold lookup_heap_obj in H0. apply beq_oid_equal in H1. rewrite <-H1 in H0.
      rewrite H2 in H0. fold lookup_heap_obj in H0. rewrite H0. 
      left. auto.
      intro. 
      case_eq (beq_oid o1 o0). intro.
      unfold update_heap_obj. rewrite H1. fold update_heap_obj.
       unfold lookup_heap_obj. rewrite H2.
       unfold lookup_heap_obj in H0.    rewrite H2 in H0. rewrite H0.
      left. auto. 
      intro.  unfold lookup_heap_obj in H. 
       unfold lookup_heap_obj in H0. 
      rewrite H1 in H. fold lookup_heap_obj in H.
      rewrite H2 in H0. fold lookup_heap_obj in H0.
      unfold update_heap_obj.
       unfold lookup_heap_obj.  rewrite H1. rewrite H2. 
      fold lookup_heap_obj.
       fold update_heap_obj. apply IHh; auto.
      Qed. 

      remember ((o0, Heap_OBJ c f l0) :: h) as h0.
      assert(  (lookup_heap_obj
               (update_heap_obj h0 o (Heap_OBJ cls F' lb')) o1  = 
                      Some (Heap_OBJ cls1 F1 lb1)) \/ 
              (lookup_heap_obj (update_heap_obj h0 o (Heap_OBJ cls F' lb')) o1  = 
                      Some (Heap_OBJ cls F' lb')) /\ beq_oid o1 o = true ).
      apply lookup_updated_heap_equal with F lb; auto. 
      destruct H7. unfold update_heap_obj in H7. rewrite Heqh0 in H7.  rewrite H3 in H7. 
      fold update_heap_obj in H7. rewrite H7. auto.

      unfold update_heap_obj in H7. rewrite Heqh0 in H7.  rewrite H3 in H7. 
      fold update_heap_obj in H7. destruct H7. rewrite H7. apply beq_oid_equal in H8.
      rewrite H8 in H6. rewrite H6 in H0. inversion H0. subst. rewrite H2.  rewrite H1.  auto.

      rewrite H6. 
      auto.

      Lemma lookup_updated_heap_none : forall h o1 o ho,
      o <> o1 ->
      lookup_heap_obj h o1 = None ->
      lookup_heap_obj (update_heap_obj h o ho) o1 = None.
      Proof. intros. induction h.
      unfold update_heap_obj. unfold lookup_heap_obj. auto. 
      induction a. case_eq (beq_oid o o0). intro. unfold update_heap_obj. rewrite H1. 
      unfold lookup_heap_obj in H0. apply beq_oid_equal in H1. 
      unfold lookup_heap_obj. rewrite <- H1 in H0. 
      case_eq (beq_oid o1 o). intro. rewrite H2 in H0. inversion H0.
      intro. rewrite H2 in H0. fold lookup_heap_obj. fold lookup_heap_obj in H0. auto. 
      intro. unfold update_heap_obj. rewrite H1. 
      fold update_heap_obj. unfold lookup_heap_obj in H0. 
      case_eq ( beq_oid o1 o0). intro. rewrite H2 in H0. inversion H0.
      intro.  rewrite H2 in H0. fold lookup_heap_obj in H0. apply IHh in H0. 
      unfold lookup_heap_obj.  rewrite H2. fold lookup_heap_obj. auto. 
      Qed.  

      assert (lookup_heap_obj (update_heap_obj ((o0, Heap_OBJ c f l0) :: h) o (Heap_OBJ cls F' lb')) o1 = None).
      apply lookup_updated_heap_none; auto. 
      intro contra. rewrite contra in H0. rewrite <- H0 in H6. inversion H6. 
      unfold update_heap_obj in H7. rewrite H3 in H7. fold update_heap_obj in H7. rewrite H7. auto. 
        
      auto. 
      apply functional_extensionality in H5. rewrite H5. auto.  
Qed.

Lemma value_erasure_dot : forall v lb sf s, 
  value v -> flow_to lb L_Label = false ->
  (erasure_H_fun_whole v (Labeled_frame lb sf :: s)) = dot.
  Proof. intros. unfold erasure_H_fun_whole. rewrite H0. induction s. auto.
    apply value_erasure_to_dot.  auto.
  induction a. fold erasure_H_fun_whole. fold erasure_H_fun_whole in IHs.
  case_eq (flow_to l0 L_Label).  intro. apply value_erasure_to_dot. auto.
  intro. assert (erasure_H_fun v = dot). apply value_erasure_to_dot. auto.
  rewrite H2. rewrite H2 in IHs. unfold erasure_H_fun. fold erasure_H_fun. auto. Qed.

Lemma dot_erasure_dot : forall s,
  erasure_H_fun_whole dot s = dot.
Proof.  intros. unfold erasure_H_fun_whole. induction s. auto. 
  induction a. case_eq ( flow_to l0 L_Label). intro. auto.  intro. 
    fold  erasure_H_fun_whole. fold erasure_H_fun_whole in IHs. 
  unfold erasure_H_fun. auto. Qed. 

Lemma erasure_stack_updated_heap : forall s h o cls F i v lo, 
 flow_to lo L_Label = false ->
 lookup_heap_obj h o = Some (Heap_OBJ cls F lo) ->
 (erasure_stack s h) = erasure_stack s
        (update_heap_obj h o
           (Heap_OBJ cls (fields_update F i v) lo)).
  Proof.  intros.  
(*flow_to l0 L_Label = true *)
induction s. auto. induction a. rename s0 into sf.
    unfold erasure_stack. case_eq ( flow_to l0 L_Label). intro. 
    fold erasure_stack.
    assert (forall a, (fun x : id => erasure_obj_null (sf x) h) a = (fun x : id =>
                                                                           erasure_obj_null (sf x)
                                                                             (update_heap_obj h o
                                                                                (Heap_OBJ cls (fields_update F i v) lo))) a) .
    intro a. assert (forall h o, (exists cls F lb, lookup_heap_obj h o = Some (Heap_OBJ cls F lb) ) 
      \/ lookup_heap_obj h o = None).
    intro h1. induction h1.  right. unfold lookup_heap_obj. auto.
    intro o1.  induction a0. case_eq ( beq_oid o1 o0). unfold lookup_heap_obj.  intro. unfold lookup_heap_obj. rewrite H2.
    rename h0 into ho. induction ho.     left. exists c. exists f. exists l1. auto. 
    intro. unfold lookup_heap_obj. rewrite H2. fold lookup_heap_obj. apply IHh1. 
    case (sf a). induction t; try (unfold erasure_obj_null; auto).

    destruct H2 with  h o0. 
    destruct H3 as [cls1]. destruct H3 as [F1]. destruct H3 as [lb1]. rewrite H3.
    remember  lo as lb'. 
    remember (fields_update F i v) as F'. 
    assert(  (lookup_heap_obj
               (update_heap_obj h o (Heap_OBJ cls F' lb')) o0  = 
                      Some (Heap_OBJ cls1 F1 lb1)) \/ 
              (lookup_heap_obj (update_heap_obj h o (Heap_OBJ cls F' lb')) o0  = 
                      Some (Heap_OBJ cls F' lb')) /\ beq_oid o0 o = true ).
      apply lookup_updated_heap_equal with F lo; auto. rewrite <- Heqlb'. auto.
      destruct H4. unfold update_heap_obj in H4.
      fold update_heap_obj in H4. rewrite H4. auto.

      unfold update_heap_obj in H4. 
      fold update_heap_obj in H4. destruct H4. rewrite H4. apply beq_oid_equal in H5.
      rewrite H5 in H3. rewrite H3 in H0. inversion H0. subst. 
      auto.
      rewrite H3. unfold erasure_obj_null.
      assert (lookup_heap_obj
          (update_heap_obj h o
             (Heap_OBJ cls (fields_update F i v)
                lo))    o0 = None).
      apply lookup_updated_heap_none; auto.
     intro contra. rewrite contra in H0. rewrite H0 in H3.  inversion H3. 
      rewrite H4. auto. auto. 
     apply functional_extensionality in H2.
      rewrite H2. auto. 
      rewrite IHs. auto.
(*flow_to l0 L_Label = false *)
     intro. fold   erasure_stack. auto. 
Qed. 

Lemma extend_heap_preserve_erasure : forall s h o h' CT cls F lb, 
  o = (get_fresh_oid h) ->field_wfe_heap CT h -> wfe_heap CT h ->  wfe_stack CT h s ->
  h' =  add_heap_obj h o (Heap_OBJ cls F lb) ->
  flow_to lb L_Label = false ->
  erasure_sigma_fun (SIGMA s h) =   erasure_sigma_fun (SIGMA s h').
Proof. 
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
Qed.

Lemma return_free_change_imply_method_call : forall t CT s h l0 sf s' h' e', 
     wfe_heap CT h -> 
     field_wfe_heap CT h ->
     forall T, has_type CT empty_context h t T ->
     Config CT t (SIGMA s h) ==>
     Config CT e' (SIGMA (Labeled_frame l0 sf :: s') h') ->
     return_free t = true -> return_free e' = false ->
     s = s'.
  Proof. induction t; intros CT s h lb sf s' h' e'; intro H_wfe_heap; intro H_wfe_fields; intro T; intro H_typing;
   intro H_reduction;   intro Hy1; intro Hy2; inversion H_reduction;  inversion H_typing; subst; 
    try (unfold  return_free in Hy1; fold  return_free in Hy1; 
      unfold  return_free in Hy2; fold  return_free in Hy2).
   - inversion H13.
   - apply IHt with CT h lb sf h' e'0 (classTy clsT); auto.
   - inversion H5. subst. 
        assert (( e' = null \/ exists o',  e' = ObjId o')).
  apply field_value with h0 o cls fields lb0 i CT cls'; auto.
      destruct H. subst. inversion Hy2. destruct H as [o']. subst. inversion Hy2.  
   - apply return_free_if in Hy1. destruct Hy1. auto. rewrite H1 in Hy2. 
      case_eq (return_free e'0). intro. rewrite H2 in Hy2. inversion Hy2. 
      intro. 
      apply IHt1 with CT h lb sf h' e'0 (classTy T0); auto.
   - apply return_free_if in Hy1. destruct Hy1. auto. rewrite H in Hy2. 
      case_eq (return_free e'0). intro. rewrite H1 in Hy2. inversion Hy2. 
      intro. 
      apply IHt2 with CT h lb sf h' e'0 (classTy arguT); auto.
   - inversion H14. inversion H6. auto. 
   - inversion H14. inversion H6. auto. 
   - inversion H11. inversion H5. inversion Hy2. 
   -  apply IHt with CT h lb sf h' e'0 T0; auto.
   - rewrite Hy1 in Hy2.  inversion Hy2. 
  -  apply IHt with CT h lb sf h' e'0  (LabelelTy T); auto.
   - inversion H4. inversion H7. subst.  rewrite Hy1 in Hy2.  inversion Hy2. 
   -   apply IHt with CT h lb sf h' e'0  (LabelelTy T0); auto.
   -  inversion Hy2.
  -  apply IHt with CT h lb sf h' e'0   (OpaqueLabeledTy T); auto.
  -  rewrite Hy1 in Hy2.  inversion Hy2. 
  - inversion H11. - inversion H14. 
  - apply return_free_if in Hy1. destruct Hy1. auto. rewrite H1 in Hy2. 
      case_eq (return_free e1'). intro. rewrite H2 in Hy2. inversion Hy2. 
      intro. 
      apply IHt1 with CT h lb sf h' e1' (classTy clsT); auto.
   - apply return_free_if in Hy1. destruct Hy1. auto. rewrite H in Hy2. 
      apply IHt2 with CT h lb sf h' e2' (classTy cls'); auto.
   - inversion Hy2.    - inversion Hy2. 
   - inversion H21. inversion H5.  - inversion H21. inversion H5. 
  - apply return_free_if in Hy1. destruct Hy1. auto. rewrite H1 in Hy2. 
      case_eq (return_free s1'). intro. rewrite H2 in Hy2. inversion Hy2. 
      intro. 
      apply IHt1 with CT h lb sf h' s1' T0; auto.
   - apply return_free_if in Hy1. destruct Hy1. auto. rewrite H1 in Hy2.
      inversion Hy2.  
   - inversion Hy1.
   - inversion Hy1. 
Qed.   

(*
Lemma return_free_false_imply_equal : forall t CT s h s' h' e', 
     wfe_heap CT h -> 
     field_wfe_heap CT h ->
     forall T, has_type CT empty_context h t T ->
     Config CT t (SIGMA s h) ==>
     Config CT e' (SIGMA s' h') ->
     return_free t = false -> return_free e' = false ->
     return_free (erasure_H_fun t) = true -> return_free (erasure_H_fun e') = true -> 
     s = s'.
  Proof. induction t; intros CT s h s' h' e'; intro H_wfe_heap; intro H_wfe_fields; intro T; 
   intro H_typing; intro H_reduction;   intro Hy1; intro Hy2; intro Hy3; intro Hy4; 
    inversion H_reduction;  inversion H_typing; subst; 
    try (unfold  return_free in Hy1; fold  return_free in Hy1; 
      unfold  return_free in Hy2; fold  return_free in Hy2); auto.
   - apply IHt with CT h h' e'0 (classTy clsT); auto.
      unfold erasure_H_fun in Hy3. rewrite Hy1 in Hy3. fold erasure_H_fun in Hy3.
      unfold return_free in Hy3. fold  return_free in Hy3. auto.
      unfold erasure_H_fun in Hy4. rewrite Hy2 in Hy4. fold erasure_H_fun in Hy4.
      unfold return_free in Hy4. fold  return_free in Hy4. auto.
   - inversion H5. inversion H10. auto.
   - apply return_free_if in Hy1. destruct Hy1. auto. rewrite H1 in Hy2. 
      case_eq (return_free e'0). intro. rewrite H2 in Hy2. inversion Hy2. 
      intro. 
      apply IHt1 with CT h lb sf h' e'0 (classTy T0); auto.
   - apply return_free_if in Hy1. destruct Hy1. auto. rewrite H in Hy2. 
      case_eq (return_free e'0). intro. rewrite H1 in Hy2. inversion Hy2. 
      intro. 
      apply IHt2 with CT h lb sf h' e'0 (classTy arguT); auto.
   - inversion H14. inversion H6. auto. 
   - inversion H14. inversion H6. auto. 
   - inversion H11. inversion H5. inversion Hy2. 
   -  apply IHt with CT h lb sf h' e'0 T0; auto.
   - rewrite Hy1 in Hy2.  inversion Hy2. 
  -  apply IHt with CT h lb sf h' e'0  (LabelelTy T); auto.
   - inversion H4. inversion H7. subst.  rewrite Hy1 in Hy2.  inversion Hy2. 
   -   apply IHt with CT h lb sf h' e'0  (LabelelTy T0); auto.
   -  inversion Hy2.
  -  apply IHt with CT h lb sf h' e'0   (OpaqueLabeledTy T); auto.
  -  rewrite Hy1 in Hy2.  inversion Hy2. 
  - inversion H11. - inversion H14. 
  - apply return_free_if in Hy1. destruct Hy1. auto. rewrite H1 in Hy2. 
      case_eq (return_free e1'). intro. rewrite H2 in Hy2. inversion Hy2. 
      intro. 
      apply IHt1 with CT h lb sf h' e1' (classTy clsT); auto.
   - apply return_free_if in Hy1. destruct Hy1. auto. rewrite H in Hy2. 
      apply IHt2 with CT h lb sf h' e2' (classTy cls'); auto.
   - inversion Hy2.    - inversion Hy2. 
   - inversion H21. inversion H5.  - inversion H21. inversion H5. 
  - apply return_free_if in Hy1. destruct Hy1. auto. rewrite H1 in Hy2. 
      case_eq (return_free s1'). intro. rewrite H2 in Hy2. inversion Hy2. 
      intro. 
      apply IHt1 with CT h lb sf h' s1' T0; auto.
   - apply return_free_if in Hy1. destruct Hy1. auto. rewrite H1 in Hy2.
      inversion Hy2.  
   - inversion Hy1.
   - inversion Hy1. 
Qed.   
*)


Lemma return_free_change_imply_return_free : forall t CT s h l0 sf s' h' e', 
     wfe_heap CT h -> 
     field_wfe_heap CT h ->
     forall T, has_type CT empty_context h t T ->
     Config CT t (SIGMA s h) ==>
     Config CT e' (SIGMA (Labeled_frame l0 sf :: s') h') ->
     return_free t = true -> return_free e' = false ->
     return_free (erasure_H_fun e') = true.
  Proof. induction t; intros CT s h lb sf s' h' e'; intro H_wfe_heap; intro H_wfe_fields; intro T; intro H_typing;
   intro H_reduction;   intro Hy1; intro Hy2; inversion H_reduction;  inversion H_typing; subst; 
    try (unfold  return_free in Hy1; fold  return_free in Hy1; 
      unfold  return_free in Hy2; fold  return_free in Hy2).
   - inversion H13.
   - unfold erasure_H_fun. fold erasure_H_fun. rewrite Hy2. 
      assert (return_free (erasure_H_fun e'0) = true). 
      apply IHt with CT s h lb sf s' h' (classTy clsT); auto. 
      unfold return_free. fold return_free. auto.  
   - inversion H5. subst. 
        assert (( e' = null \/ exists o',  e' = ObjId o')).
  apply field_value with h0 o cls fields lb0 i CT cls'; auto.
      destruct H. subst. unfold erasure_H_fun. auto. 
      destruct H as [o']. subst. unfold erasure_H_fun. auto. 
   - apply return_free_if in Hy1. destruct Hy1. auto. rewrite H1 in Hy2. 
      case_eq (return_free e'0). intro. rewrite H2 in Hy2. inversion Hy2. 
      intro. assert (return_free (erasure_H_fun e'0) = true). 
      apply IHt1 with CT s h lb sf s' h' (classTy T0); auto.
      unfold erasure_H_fun.  fold erasure_H_fun. rewrite H2.
      unfold return_free. fold return_free. rewrite H3. rewrite H1. auto. 
   - apply return_free_if in Hy1. destruct Hy1. auto. 
      case_eq (return_free e'0). intro. rewrite H1 in Hy2. rewrite H in Hy2. inversion Hy2. 
      intro. assert (return_free (erasure_H_fun e'0) = true). 
      apply IHt2 with CT s h lb sf s' h' (classTy arguT); auto.
      unfold erasure_H_fun.  fold erasure_H_fun. rewrite H1.
      unfold return_free. fold return_free. rewrite H.
      unfold return_free. fold return_free. rewrite H2. rewrite H. auto. 
   - inversion H6. subst. rename h0 into h. rename s0 into s. inversion H18. 
      subst. rewrite <- H1 in H20. inversion H20. destruct H10 as [F']. destruct H as [lo].
      rewrite H in H7. inversion H7. subst. rewrite H21 in H8. inversion H8. subst. 
      assert (return_free body0 = true). apply surface_syntax_is_return_free. auto. 
      unfold erasure_H_fun. fold erasure_H_fun. rewrite H0. auto. 
   - inversion H6. subst. rename h0 into h. rename s0 into s. inversion H18. 
      subst. rewrite <- H1 in H20. inversion H20. destruct H8 as [F']. destruct H as [lo].
      rewrite H in H7. inversion H7. subst. rewrite H21 in H13. inversion H13. subst. 
      assert (return_free body0 = true). apply surface_syntax_is_return_free. auto. 
      unfold erasure_H_fun. fold erasure_H_fun. rewrite H0. auto. 
   - unfold erasure_H_fun. auto. 
   - unfold erasure_H_fun. fold erasure_H_fun. rewrite Hy2. 
      assert (return_free (erasure_H_fun e'0) = true). 
      apply IHt with CT s h lb sf s' h' T0; auto. 
      unfold return_free. fold return_free. auto.  
   - unfold erasure_H_fun. fold erasure_H_fun.  rewrite Hy1.  auto. 
  -  unfold erasure_H_fun. fold erasure_H_fun. rewrite Hy2. 
      assert (return_free (erasure_H_fun e'0) = true). 
      apply IHt with CT s h lb sf s' h' (LabelelTy T); auto. 
      unfold return_free. fold return_free. auto.  
   - assert (erasure_H_fun e' = dot). apply return_free_true_imply_erasure_H_fun_dot.
      apply value_is_valid_syntax; auto. auto. rewrite H. auto. 
   - unfold erasure_H_fun. fold erasure_H_fun. rewrite Hy2. 
      assert (return_free (erasure_H_fun e'0) = true). 
      apply IHt with CT s h lb sf s' h' (LabelelTy T0); auto. 
      unfold return_free. fold return_free. auto.  
   - unfold erasure_H_fun. auto. 
   - unfold erasure_H_fun. fold erasure_H_fun. rewrite Hy2. 
      assert (return_free (erasure_H_fun e'0) = true). 
      apply IHt with CT s h lb sf s' h' (OpaqueLabeledTy T); auto. 
      unfold return_free. fold return_free. auto.
   - rewrite Hy1 in Hy2. inversion Hy2. 
  - inversion H11. 
  - inversion H14. 
  - apply return_free_if in Hy1. destruct Hy1. auto. rewrite H1 in Hy2. 
      case_eq (return_free e1'). intro. rewrite H2 in Hy2. inversion Hy2. 
      intro. assert (return_free (erasure_H_fun e1') = true). 
      apply IHt1 with CT s h lb sf s' h' (classTy clsT); auto.
      unfold erasure_H_fun.  fold erasure_H_fun. rewrite H2.
      unfold return_free. fold return_free. rewrite H3. rewrite H1. auto.
   - apply return_free_if in Hy1. destruct Hy1. auto. 
      case_eq (return_free e2'). intro. rewrite H1 in Hy2. rewrite H in Hy2. inversion Hy2. 
      intro. assert (return_free (erasure_H_fun e2') = true). 
      apply IHt2 with CT s h lb sf s' h' (classTy cls'); auto.
      unfold erasure_H_fun.  fold erasure_H_fun. rewrite H1.
      unfold return_free. fold return_free. rewrite H.
      unfold return_free. fold return_free. rewrite H3. rewrite H. auto.
   - auto. - auto. - inversion H21. inversion H5. 
    - inversion H21. inversion H5. 
  - apply return_free_if in Hy1. destruct Hy1. auto. rewrite H1 in Hy2. 
      case_eq (return_free s1'). intro. rewrite H2 in Hy2. inversion Hy2. 
      intro. assert (return_free (erasure_H_fun s1') = true). 
      apply IHt1 with CT s h lb sf s' h' T0; auto.
      unfold erasure_H_fun.  fold erasure_H_fun. rewrite H2.
      unfold return_free. fold return_free. rewrite H3. rewrite H1. auto.
   - apply return_free_if in Hy1. destruct Hy1. auto. rewrite H1 in Hy2.
      inversion Hy2.  
    - inversion Hy2. inversion Hy1. 
    - inversion Hy1. 
Qed.  

Lemma return_free_change_imply_return : forall t CT s h l0 sf s' h' e', 
     wfe_heap CT h -> 
     field_wfe_heap CT h ->
     forall T, has_type CT empty_context h t T ->
     Config CT t (SIGMA (Labeled_frame l0 sf :: s) h) ==>
     Config CT e' (SIGMA s' h') ->
     return_free t = false -> return_free e' = true ->
     s = s'.
  Proof. induction t; intros CT s h lb sf s' h' e'; intro H_wfe_heap; intro H_wfe_fields; intro T; intro H_typing;
   intro H_reduction;   intro Hy1; intro Hy2; inversion H_reduction;  inversion H_typing; subst; 
    try (unfold  return_free in Hy1; fold  return_free in Hy1; 
      unfold  return_free in Hy2; fold  return_free in Hy2); 
      try (inversion Hy1; fail); try (inversion Hy2; fail).  Admitted. 
(*
   - inversion H13.
   - apply IHt with CT h lb sf h' e'0 (classTy clsT); auto.
   - inversion H5. subst. 
        assert (( e' = null \/ exists o',  e' = ObjId o')).
  apply field_value with h0 o cls fields lb0 i CT cls'; auto.
      destruct H. subst. inversion Hy2. destruct H as [o']. subst. inversion Hy2.  
   - apply return_free_if in Hy1. destruct Hy1. auto. rewrite H1 in Hy2. 
      case_eq (return_free e'0). intro. rewrite H2 in Hy2. inversion Hy2. 
      intro. 
      apply IHt1 with CT h lb sf h' e'0 (classTy T0); auto.
   - apply return_free_if in Hy1. destruct Hy1. auto. rewrite H in Hy2. 
      case_eq (return_free e'0). intro. rewrite H1 in Hy2. inversion Hy2. 
      intro. 
      apply IHt2 with CT h lb sf h' e'0 (classTy arguT); auto.
   - inversion H14. inversion H6. auto. 
   - inversion H14. inversion H6. auto. 
   - inversion H11. inversion H5. inversion Hy2. 
   -  apply IHt with CT h lb sf h' e'0 T0; auto.
   - rewrite Hy1 in Hy2.  inversion Hy2. 
  -  apply IHt with CT h lb sf h' e'0  (LabelelTy T); auto.
   - inversion H4. inversion H7. subst.  rewrite Hy1 in Hy2.  inversion Hy2. 
   -   apply IHt with CT h lb sf h' e'0  (LabelelTy T0); auto.
   -  inversion Hy2.
  -  apply IHt with CT h lb sf h' e'0   (OpaqueLabeledTy T); auto.
  -  rewrite Hy1 in Hy2.  inversion Hy2. 
  - inversion H11. - inversion H14. 
  - apply return_free_if in Hy1. destruct Hy1. auto. rewrite H1 in Hy2. 
      case_eq (return_free e1'). intro. rewrite H2 in Hy2. inversion Hy2. 
      intro. 
      apply IHt1 with CT h lb sf h' e1' (classTy clsT); auto.
   - apply return_free_if in Hy1. destruct Hy1. auto. rewrite H in Hy2. 
      apply IHt2 with CT h lb sf h' e2' (classTy cls'); auto.
   - inversion Hy2.    - inversion Hy2. 
   - inversion H21. inversion H5.  - inversion H21. inversion H5. 
  - apply return_free_if in Hy1. destruct Hy1. auto. rewrite H1 in Hy2. 
      case_eq (return_free s1'). intro. rewrite H2 in Hy2. inversion Hy2. 
      intro. 
      apply IHt1 with CT h lb sf h' s1' T0; auto.
   - apply return_free_if in Hy1. destruct Hy1. auto. rewrite H1 in Hy2.
      inversion Hy2.  
   - inversion Hy1.
   - inversion Hy1. 
Qed.   *)

Lemma return_free_change_imply_return_free_false2true : forall t CT s h  s' h' e', 
     wfe_heap CT h -> 
     field_wfe_heap CT h ->
     forall T, has_type CT empty_context h t T ->
     Config CT t (SIGMA s h) ==>
     Config CT e' (SIGMA s' h') ->
     return_free t = false -> return_free e' = true ->
     return_free (erasure_H_fun t) = true.
  Proof. induction t; intros CT s h  s' h' e'; intro H_wfe_heap; intro H_wfe_fields; intro T; intro H_typing;
   intro H_reduction;   intro Hy1; intro Hy2; inversion H_reduction;  inversion H_typing; subst; 
    try (unfold  return_free in Hy1; fold  return_free in Hy1; 
      unfold  return_free in Hy2; fold  return_free in Hy2); auto. 
   - unfold erasure_H_fun. fold erasure_H_fun. rewrite Hy1. 
      assert (return_free (erasure_H_fun t) = true). 
      apply IHt with CT s h s' h' e'0 (classTy clsT); auto. 
      unfold return_free. fold return_free. auto.  Admitted. (*
   - inversion H5. subst. 
        assert (( e' = null \/ exists o',  e' = ObjId o')).
  apply field_value with h0 o cls fields lb0 i CT cls'; auto.
      destruct H. subst. unfold erasure_H_fun. auto. 
      destruct H as [o']. subst. unfold erasure_H_fun. auto. 
   - apply return_free_if in Hy1. destruct Hy1. auto. rewrite H1 in Hy2. 
      case_eq (return_free e'0). intro. rewrite H2 in Hy2. inversion Hy2. 
      intro. assert (return_free (erasure_H_fun e'0) = true). 
      apply IHt1 with CT s h lb sf s' h' (classTy T0); auto.
      unfold erasure_H_fun.  fold erasure_H_fun. rewrite H2.
      unfold return_free. fold return_free. rewrite H3. rewrite H1. auto. 
   - apply return_free_if in Hy1. destruct Hy1. auto. 
      case_eq (return_free e'0). intro. rewrite H1 in Hy2. rewrite H in Hy2. inversion Hy2. 
      intro. assert (return_free (erasure_H_fun e'0) = true). 
      apply IHt2 with CT s h lb sf s' h' (classTy arguT); auto.
      unfold erasure_H_fun.  fold erasure_H_fun. rewrite H1.
      unfold return_free. fold return_free. rewrite H.
      unfold return_free. fold return_free. rewrite H2. rewrite H. auto. 
   - inversion H6. subst. rename h0 into h. rename s0 into s. inversion H18. 
      subst. rewrite <- H1 in H20. inversion H20. destruct H10 as [F']. destruct H as [lo].
      rewrite H in H7. inversion H7. subst. rewrite H21 in H8. inversion H8. subst. 
      assert (return_free body0 = true). apply surface_syntax_is_return_free. auto. 
      unfold erasure_H_fun. fold erasure_H_fun. rewrite H0. auto. 
   - inversion H6. subst. rename h0 into h. rename s0 into s. inversion H18. 
      subst. rewrite <- H1 in H20. inversion H20. destruct H8 as [F']. destruct H as [lo].
      rewrite H in H7. inversion H7. subst. rewrite H21 in H13. inversion H13. subst. 
      assert (return_free body0 = true). apply surface_syntax_is_return_free. auto. 
      unfold erasure_H_fun. fold erasure_H_fun. rewrite H0. auto. 
   - unfold erasure_H_fun. auto. 
   - unfold erasure_H_fun. fold erasure_H_fun. rewrite Hy2. 
      assert (return_free (erasure_H_fun e'0) = true). 
      apply IHt with CT s h lb sf s' h' T0; auto. 
      unfold return_free. fold return_free. auto.  
   - unfold erasure_H_fun. fold erasure_H_fun.  rewrite Hy1.  auto. 
  -  unfold erasure_H_fun. fold erasure_H_fun. rewrite Hy2. 
      assert (return_free (erasure_H_fun e'0) = true). 
      apply IHt with CT s h lb sf s' h' (LabelelTy T); auto. 
      unfold return_free. fold return_free. auto.  
   - assert (erasure_H_fun e' = dot). apply return_free_true_imply_erasure_H_fun_dot.
      apply value_is_valid_syntax; auto. auto. rewrite H. auto. 
   - unfold erasure_H_fun. fold erasure_H_fun. rewrite Hy2. 
      assert (return_free (erasure_H_fun e'0) = true). 
      apply IHt with CT s h lb sf s' h' (LabelelTy T0); auto. 
      unfold return_free. fold return_free. auto.  
   - unfold erasure_H_fun. auto. 
   - unfold erasure_H_fun. fold erasure_H_fun. rewrite Hy2. 
      assert (return_free (erasure_H_fun e'0) = true). 
      apply IHt with CT s h lb sf s' h' (OpaqueLabeledTy T); auto. 
      unfold return_free. fold return_free. auto.
   - rewrite Hy1 in Hy2. inversion Hy2. 
  - inversion H11. 
  - inversion H14. 
  - apply return_free_if in Hy1. destruct Hy1. auto. rewrite H1 in Hy2. 
      case_eq (return_free e1'). intro. rewrite H2 in Hy2. inversion Hy2. 
      intro. assert (return_free (erasure_H_fun e1') = true). 
      apply IHt1 with CT s h lb sf s' h' (classTy clsT); auto.
      unfold erasure_H_fun.  fold erasure_H_fun. rewrite H2.
      unfold return_free. fold return_free. rewrite H3. rewrite H1. auto.
   - apply return_free_if in Hy1. destruct Hy1. auto. 
      case_eq (return_free e2'). intro. rewrite H1 in Hy2. rewrite H in Hy2. inversion Hy2. 
      intro. assert (return_free (erasure_H_fun e2') = true). 
      apply IHt2 with CT s h lb sf s' h' (classTy cls'); auto.
      unfold erasure_H_fun.  fold erasure_H_fun. rewrite H1.
      unfold return_free. fold return_free. rewrite H.
      unfold return_free. fold return_free. rewrite H3. rewrite H. auto.
   - inversion H21. inversion H5. 
    - inversion H21. inversion H5. 
  - apply return_free_if in Hy1. destruct Hy1. auto. rewrite H1 in Hy2. 
      case_eq (return_free s1'). intro. rewrite H2 in Hy2. inversion Hy2. 
      intro. assert (return_free (erasure_H_fun s1') = true). 
      apply IHt1 with CT s h lb sf s' h' T0; auto.
      unfold erasure_H_fun.  fold erasure_H_fun. rewrite H2.
      unfold return_free. fold return_free. rewrite H3. rewrite H1. auto.
   - apply return_free_if in Hy1. destruct Hy1. auto. rewrite H1 in Hy2.
      inversion Hy2.  
    - inversion Hy2. inversion Hy1. 
    - inversion Hy1. 
Qed.  *)


Lemma return_free_equal_stack : forall t CT s h l0 s0  l1 s1 s' h' e', 
     wfe_heap CT h -> 
     field_wfe_heap CT h ->
     forall T, has_type CT empty_context h t T ->
     Config CT t (SIGMA (Labeled_frame l0 s0 :: s) h) ==>
     Config CT e' (SIGMA (Labeled_frame l1 s1 :: s') h') ->
     return_free t = true -> return_free e' = true ->
     s = s'.
  Proof. induction t; intros CT s h lb0 s0  lb1 s1 s' h' e'; intro H_wfe_heap; intro H_wfe_fields; intro T; intro H_typing;
   intro H_reduction;   intro Hy1; intro Hy2; inversion H_reduction;  inversion H_typing; subst; 
      try (inversion Hy1; fail); try (inversion Hy2;fail); try (auto).
   - apply IHt with CT h lb0 s0 lb1 s1 h' e'0 (classTy clsT); auto.
   - inversion H5. subst. unfold  update_current_label in H10.  inversion H10. auto. 
   - apply return_free_if in Hy1. destruct Hy1. auto. 
      unfold return_free in Hy2. fold return_free in Hy2.   rewrite H1 in Hy2.  
      case_eq (return_free e'0). intro. rewrite H2 in Hy2. 
      apply IHt1 with CT h lb0 s0 lb1 s1 h' e'0 (classTy T0); auto.
      intro. rewrite H2 in Hy2.  inversion Hy2. 
   - apply return_free_if in Hy1. destruct Hy1. auto. 
      unfold return_free in Hy2. fold return_free in Hy2.   rewrite H in Hy2.  
      apply IHt2 with CT h lb0 s0 lb1 s1 h' e'0 (classTy arguT); auto.
   - inversion H5. subst. inversion H11. auto.
   - apply IHt with CT h lb0 s0 lb1 s1 h' e'0 T0; auto.
   - apply IHt with CT h lb0 s0 lb1 s1 h' e'0 (LabelelTy T); auto.
   - inversion H4. subst. inversion H7.  auto. 
   - apply IHt with CT h lb0 s0 lb1 s1 h' e'0 (LabelelTy T0); auto.
   - apply IHt with CT h lb0 s0 lb1 s1 h' e'0 (OpaqueLabeledTy T); auto.
   - inversion H4. subst. inversion H7.  auto. 
    - inversion H11. 
    - inversion H14. 
    - apply return_free_if in Hy1. destruct Hy1. 
      unfold return_free in Hy2. fold return_free in Hy2. 
      case_eq (return_free e1'). intro. rewrite H2 in Hy2. 
      auto.  apply IHt1 with CT h lb0 s0 lb1 s1 h' e1' (classTy clsT); auto.
      intro. rewrite H2 in Hy2.  inversion Hy2. 
   - apply return_free_if in Hy1. destruct Hy1. auto. 
      unfold return_free in Hy2. fold return_free in Hy2.   rewrite H in Hy2.  
      apply IHt2 with CT h lb0 s0 lb1 s1 h' e2' (classTy cls'); auto.
    - inversion H6. subst. inversion H12. subst. auto. 
    - inversion H7. subst. inversion H13. subst. auto.
    - apply return_free_if in Hy1. destruct Hy1. 
      unfold return_free in Hy2. fold return_free in Hy2. 
      case_eq (return_free s1'). intro. rewrite H2 in Hy2. 
      auto.  apply IHt1 with CT h lb0 s0 lb1 s1 h' s1' T0; auto.
      intro. rewrite H2 in Hy2.  inversion Hy2.
Qed. 

Lemma valid_syntax_after_erasure : forall t, 
  valid_syntax t ->
  valid_syntax (erasure_H_fun t).
Proof with eauto. induction t; intros; unfold  erasure_H_fun; auto; try (fold erasure_H_fun).
case_eq (return_free t ); intro; auto. apply Valid_FieldAccess. apply IHt. inversion H. auto. 
case_eq (return_free t1 ); intro; auto. Admitted. 


Lemma field_access_erasure_dot : forall t s' i,
    valid_syntax t-> 
    dot = erasure_H_fun_whole t s' -> t <> dot ->
    (erasure_H_fun_whole (FieldAccess t i) s') = dot.
   Proof with eauto. intros.  generalize dependent t. induction s'. intros.  unfold erasure_H_fun_whole.  auto. 
    intros. unfold erasure_H_fun_whole in H0. rewrite H0 in H1. intuition.  induction a. 
    case_eq ( flow_to l0 L_Label). intros. unfold erasure_H_fun_whole in H1. rewrite H in H1.
    rewrite H1 in H2. intuition. intros.  unfold erasure_H_fun_whole in H1. rewrite H in H1.
    fold erasure_H_fun_whole in H1.
    unfold erasure_H_fun_whole.
    rewrite H. fold erasure_H_fun_whole. unfold erasure_H_fun.  fold erasure_H_fun. 
    case_eq (return_free t). intro. auto. apply dot_erasure_dot. intro. 
    apply IHs'; auto. apply valid_syntax_after_erasure. auto. 
    apply return_free_imply_erasure_H_fun_dot in H3. auto. auto. Qed. 

Lemma field_access_erasure_helper : forall t e' s s' i, 
    valid_syntax t -> valid_syntax e' ->
    erasure_H_fun_whole (erasure_H_fun t) s = erasure_H_fun_whole (erasure_H_fun e') s' ->
    return_free t = false -> return_free e' = false ->
    erasure_H_fun_whole (FieldAccess (erasure_H_fun t) i) s = 
    erasure_H_fun_whole (FieldAccess (erasure_H_fun e') i) s'.
    Proof. intros. generalize dependent t. generalize dependent e'. generalize dependent s'.
    induction s.  intros. generalize dependent e'.  generalize dependent t. induction s'.

    intros. unfold erasure_H_fun_whole in H1. rewrite H1. auto.

    intros. unfold erasure_H_fun_whole in H1. induction a. case_eq (flow_to l0 L_Label). intro.
    rewrite H4 in H1. unfold erasure_H_fun_whole. rewrite H4. rewrite H1. auto.

    intros.  rewrite H4 in H1. fold erasure_H_fun_whole in H1.
    unfold erasure_H_fun_whole.  rewrite H4. fold erasure_H_fun_whole. 
    unfold erasure_H_fun. fold erasure_H_fun. 
    case_eq (return_free (erasure_H_fun e')) . intro. 
    apply return_free_true_imply_erasure_H_fun_dot in H5. rewrite H5 in H1.  
    pose proof (dot_erasure_dot s'). rewrite H6 in H1. apply erasure_H_fun_imply_return_free in H1. 
    rewrite H1 in H2. inversion H2. auto. 
    apply valid_syntax_after_erasure. auto.
    intro. apply IHs'; auto. apply valid_syntax_after_erasure. auto.

    intros.  generalize dependent e'.  generalize dependent t. induction s'.
    intros. induction a.  unfold erasure_H_fun_whole in H1. 
    case_eq (flow_to l0 L_Label).  intro.  rewrite H4 in H1. 
    
    unfold erasure_H_fun_whole. rewrite H4. rewrite H1. auto. 
    intro. rewrite H4 in H1. fold erasure_H_fun_whole in H1.
    remember (erasure_H_fun_whole (FieldAccess (erasure_H_fun e') i) nil) as tmp.  
    unfold erasure_H_fun_whole. rewrite H4.   fold erasure_H_fun_whole. rewrite Heqtmp.
    unfold erasure_H_fun. fold erasure_H_fun. 
    case_eq (return_free (erasure_H_fun t)) . intro. pose proof (dot_erasure_dot s). 
    apply return_free_true_imply_erasure_H_fun_dot in H5. rewrite H5 in H1. rewrite H6 in H1.
    assert (return_free e' = true). apply erasure_H_fun_imply_return_free. auto. auto. 
    rewrite H7 in H3. inversion H3.     apply valid_syntax_after_erasure. auto.
    intro. apply IHs; auto. apply valid_syntax_after_erasure. auto.

    intros. induction a.    case_eq (flow_to l0 L_Label).  intro. 
    assert (erasure_H_fun_whole (FieldAccess (erasure_H_fun t) i)
  (Labeled_frame l0 s0 :: s)  = (FieldAccess (erasure_H_fun t) i)). 
    unfold erasure_H_fun_whole. rewrite H4. auto. 
      
    unfold erasure_H_fun_whole in H1. rewrite H4 in H1. fold erasure_H_fun_whole in H1. 
    unfold erasure_H_fun_whole. rewrite H4.   fold erasure_H_fun_whole.
    induction a0. case_eq (flow_to l1 L_Label). intro. rewrite H6 in H1.  rewrite H1. auto .
    intro. rewrite H6 in H1. rewrite <- H5. unfold erasure_H_fun. fold erasure_H_fun. 
    case_eq (return_free (erasure_H_fun e')). intro. 
   apply return_free_true_imply_erasure_H_fun_dot in H7. rewrite H7 in H1.
    pose proof (dot_erasure_dot s'). rewrite H8 in H1. apply erasure_H_fun_imply_return_free in H1.
    rewrite H1 in H2. inversion H2. 
    auto. apply valid_syntax_after_erasure. auto. 

    intro. apply IHs'; auto. apply valid_syntax_after_erasure. auto. rewrite <- H1. 
    unfold erasure_H_fun_whole. rewrite H4. auto. 

    intro. induction a0. unfold erasure_H_fun_whole in H1. rewrite H4 in H1. fold erasure_H_fun_whole in H1. 
    unfold erasure_H_fun_whole. rewrite H4. fold erasure_H_fun_whole. 
     case_eq (flow_to l1 L_Label). intro. rewrite H5 in H1. 
    assert (erasure_H_fun_whole (FieldAccess (erasure_H_fun e') i)
                     (Labeled_frame l1 s1 :: s') = FieldAccess (erasure_H_fun e') i).
    unfold erasure_H_fun_whole. rewrite H5. auto. 
    unfold erasure_H_fun. fold erasure_H_fun. 

    case_eq (return_free (erasure_H_fun t)). intro. 
     apply return_free_true_imply_erasure_H_fun_dot in H7. rewrite H7 in H1.
    pose proof (dot_erasure_dot s). rewrite H8 in H1. assert (erasure_H_fun e' = dot). auto. 
    apply erasure_H_fun_imply_return_free in H9. rewrite H9 in H3. inversion H3. auto. 
    auto. apply valid_syntax_after_erasure. auto.

    intro. rewrite <- H6. apply IHs; auto.   apply valid_syntax_after_erasure. auto.
    rewrite H1. unfold erasure_H_fun_whole. rewrite H5. auto. 

    intro. rewrite H5 in H1. unfold erasure_H_fun. fold erasure_H_fun. 
    case_eq (return_free (erasure_H_fun t)). intro. 
    apply return_free_true_imply_erasure_H_fun_dot in H6. rewrite H6 in H1. 
    case_eq (return_free (erasure_H_fun e')). intro. 
    pose proof (dot_erasure_dot s). pose proof (dot_erasure_dot s').
    rewrite H8. rewrite H9. auto. 

    intro.  pose proof (dot_erasure_dot s). rewrite H8 in H1. rewrite H8. 
    assert (erasure_H_fun_whole (FieldAccess (erasure_H_fun (erasure_H_fun e')) i) s' = dot).
    apply field_access_erasure_dot; auto. 
    apply valid_syntax_after_erasure. apply valid_syntax_after_erasure. auto.
    intro contra. apply erasure_H_fun_imply_return_free in contra.  rewrite contra in H7. 
    inversion H7.   apply valid_syntax_after_erasure. auto. auto. 
     apply valid_syntax_after_erasure. auto.

    intro. case_eq (return_free (erasure_H_fun e')). intro. 
    pose proof (dot_erasure_dot s). pose proof (dot_erasure_dot s').
    rewrite H9. apply return_free_true_imply_erasure_H_fun_dot in H7. rewrite H7 in H1. 
    rewrite H9 in H1. 

    apply field_access_erasure_dot; auto. 
    apply valid_syntax_after_erasure. apply valid_syntax_after_erasure. auto.
    intro contra. apply erasure_H_fun_imply_return_free in contra.  rewrite contra in H6. 
    inversion H6.   apply valid_syntax_after_erasure. auto. 
    apply valid_syntax_after_erasure. auto. 

    intro.  pose proof (dot_erasure_dot s). apply IHs; auto. 
     apply valid_syntax_after_erasure. auto. 
    apply valid_syntax_after_erasure. auto. 
Qed. 


Lemma label_data_erasure_dot : forall t s' i,
        valid_syntax t-> 
        dot = erasure_H_fun_whole t s' -> t <> dot ->
        (erasure_H_fun_whole (labelData t i) s') = dot.
   Proof with eauto. intros.  generalize dependent t. induction s'. intros.  unfold erasure_H_fun_whole.  auto. 
    intros. unfold erasure_H_fun_whole in H0. rewrite H0 in H1. intuition.  induction a. 
    case_eq ( flow_to l0 L_Label). intros. unfold erasure_H_fun_whole in H1. rewrite H in H1.
    rewrite H1 in H2. intuition. intros.  unfold erasure_H_fun_whole in H1. rewrite H in H1.
    fold erasure_H_fun_whole in H1.
    unfold erasure_H_fun_whole.
    rewrite H. fold erasure_H_fun_whole. unfold erasure_H_fun.  fold erasure_H_fun. 
    case_eq (return_free t). intro. auto. apply dot_erasure_dot. intro. 
    apply IHs'; auto. apply valid_syntax_after_erasure. auto. 
    apply return_free_imply_erasure_H_fun_dot in H3. auto. auto. Qed. 

Lemma label_data_erasure_helper : forall t e' s s' i, 
    valid_syntax t -> valid_syntax e' ->
    erasure_H_fun_whole (erasure_H_fun t) s = erasure_H_fun_whole (erasure_H_fun e') s' ->
    return_free t = false -> return_free e' = false ->
    erasure_H_fun_whole (labelData (erasure_H_fun t) i) s = 
    erasure_H_fun_whole (labelData (erasure_H_fun e') i) s'.
     Proof. intros. generalize dependent t. generalize dependent e'. generalize dependent s'.
    induction s.  intros. generalize dependent e'.  generalize dependent t. induction s'.

    intros. unfold erasure_H_fun_whole in H1. rewrite H1. auto.

    intros. unfold erasure_H_fun_whole in H1. induction a. case_eq (flow_to l0 L_Label). intro.
    rewrite H4 in H1. unfold erasure_H_fun_whole. rewrite H4. rewrite H1. auto.

    intros.  rewrite H4 in H1. fold erasure_H_fun_whole in H1.
    unfold erasure_H_fun_whole.  rewrite H4. fold erasure_H_fun_whole. 
    unfold erasure_H_fun. fold erasure_H_fun. 
    case_eq (return_free (erasure_H_fun e')) . intro. 
    apply return_free_true_imply_erasure_H_fun_dot in H5. rewrite H5 in H1.  
    pose proof (dot_erasure_dot s'). rewrite H6 in H1. apply erasure_H_fun_imply_return_free in H1. 
    rewrite H1 in H2. inversion H2. auto. 
    apply valid_syntax_after_erasure. auto.
    intro. apply IHs'; auto. apply valid_syntax_after_erasure. auto.

    intros.  generalize dependent e'.  generalize dependent t. induction s'.
    intros. induction a.  unfold erasure_H_fun_whole in H1. 
    case_eq (flow_to l0 L_Label).  intro.  rewrite H4 in H1. 
    
    unfold erasure_H_fun_whole. rewrite H4. rewrite H1. auto. 
    intro. rewrite H4 in H1. fold erasure_H_fun_whole in H1.
    remember (erasure_H_fun_whole (labelData (erasure_H_fun e') i) nil) as tmp.  
    unfold erasure_H_fun_whole. rewrite H4.   fold erasure_H_fun_whole. rewrite Heqtmp.
    unfold erasure_H_fun. fold erasure_H_fun. 
    case_eq (return_free (erasure_H_fun t)) . intro. pose proof (dot_erasure_dot s). 
    apply return_free_true_imply_erasure_H_fun_dot in H5. rewrite H5 in H1. rewrite H6 in H1.
    assert (return_free e' = true). apply erasure_H_fun_imply_return_free. auto. auto. 
    rewrite H7 in H3. inversion H3.     apply valid_syntax_after_erasure. auto.
    intro. apply IHs; auto. apply valid_syntax_after_erasure. auto.

    intros. induction a.    case_eq (flow_to l0 L_Label).  intro. 
    assert (erasure_H_fun_whole (labelData (erasure_H_fun t) i)
  (Labeled_frame l0 s0 :: s)  = (labelData (erasure_H_fun t) i)). 
    unfold erasure_H_fun_whole. rewrite H4. auto. 
      
    unfold erasure_H_fun_whole in H1. rewrite H4 in H1. fold erasure_H_fun_whole in H1. 
    unfold erasure_H_fun_whole. rewrite H4.   fold erasure_H_fun_whole.
    induction a0. case_eq (flow_to l1 L_Label). intro. rewrite H6 in H1.  rewrite H1. auto .
    intro. rewrite H6 in H1. rewrite <- H5. unfold erasure_H_fun. fold erasure_H_fun. 
    case_eq (return_free (erasure_H_fun e')). intro. 
   apply return_free_true_imply_erasure_H_fun_dot in H7. rewrite H7 in H1.
    pose proof (dot_erasure_dot s'). rewrite H8 in H1. apply erasure_H_fun_imply_return_free in H1.
    rewrite H1 in H2. inversion H2. 
    auto. apply valid_syntax_after_erasure. auto. 

    intro. apply IHs'; auto. apply valid_syntax_after_erasure. auto. rewrite <- H1. 
    unfold erasure_H_fun_whole. rewrite H4. auto. 

    intro. induction a0. unfold erasure_H_fun_whole in H1. rewrite H4 in H1. fold erasure_H_fun_whole in H1. 
    unfold erasure_H_fun_whole. rewrite H4. fold erasure_H_fun_whole. 
     case_eq (flow_to l1 L_Label). intro. rewrite H5 in H1. 
    assert (erasure_H_fun_whole (labelData (erasure_H_fun e') i)
                     (Labeled_frame l1 s1 :: s') = labelData (erasure_H_fun e') i).
    unfold erasure_H_fun_whole. rewrite H5. auto. 
    unfold erasure_H_fun. fold erasure_H_fun. 

    case_eq (return_free (erasure_H_fun t)). intro. 
     apply return_free_true_imply_erasure_H_fun_dot in H7. rewrite H7 in H1.
    pose proof (dot_erasure_dot s). rewrite H8 in H1. assert (erasure_H_fun e' = dot). auto. 
    apply erasure_H_fun_imply_return_free in H9. rewrite H9 in H3. inversion H3. auto. 
    auto. apply valid_syntax_after_erasure. auto.

    intro. rewrite <- H6. apply IHs; auto.   apply valid_syntax_after_erasure. auto.
    rewrite H1. unfold erasure_H_fun_whole. rewrite H5. auto. 

    intro. rewrite H5 in H1. unfold erasure_H_fun. fold erasure_H_fun. 
    case_eq (return_free (erasure_H_fun t)). intro. 
    apply return_free_true_imply_erasure_H_fun_dot in H6. rewrite H6 in H1. 
    case_eq (return_free (erasure_H_fun e')). intro. 
    pose proof (dot_erasure_dot s). pose proof (dot_erasure_dot s').
    rewrite H8. rewrite H9. auto. 

    intro.  pose proof (dot_erasure_dot s). rewrite H8 in H1. rewrite H8. 
    assert (erasure_H_fun_whole (labelData (erasure_H_fun (erasure_H_fun e')) i) s' = dot).
    apply label_data_erasure_dot; auto. 
    apply valid_syntax_after_erasure. apply valid_syntax_after_erasure. auto.
    intro contra. apply erasure_H_fun_imply_return_free in contra.  rewrite contra in H7. 
    inversion H7.   apply valid_syntax_after_erasure. auto. auto. 
     apply valid_syntax_after_erasure. auto.

    intro. case_eq (return_free (erasure_H_fun e')). intro. 
    pose proof (dot_erasure_dot s). pose proof (dot_erasure_dot s').
    rewrite H9. apply return_free_true_imply_erasure_H_fun_dot in H7. rewrite H7 in H1. 
    rewrite H9 in H1. 

    apply label_data_erasure_dot; auto. 
    apply valid_syntax_after_erasure. apply valid_syntax_after_erasure. auto.
    intro contra. apply erasure_H_fun_imply_return_free in contra.  rewrite contra in H6. 
    inversion H6.   apply valid_syntax_after_erasure. auto. 
    apply valid_syntax_after_erasure. auto. 

    intro.  pose proof (dot_erasure_dot s). apply IHs; auto. 
     apply valid_syntax_after_erasure. auto. 
    apply valid_syntax_after_erasure. auto. 
Qed. 


Lemma labelOf_erasure_dot : forall t s',
    valid_syntax t-> 
    dot = erasure_H_fun_whole t s' -> t <> dot ->
    (erasure_H_fun_whole (labelOf t) s') = dot.
   Proof with eauto. intros.  generalize dependent t. induction s'. intros.  unfold erasure_H_fun_whole.  auto. 
    intros. unfold erasure_H_fun_whole in H0. rewrite H0 in H1. intuition.  induction a. 
    case_eq ( flow_to l0 L_Label). intros. unfold erasure_H_fun_whole in H1. rewrite H in H1.
    rewrite H1 in H2. intuition. intros.  unfold erasure_H_fun_whole in H1. rewrite H in H1.
    fold erasure_H_fun_whole in H1.
    unfold erasure_H_fun_whole.
    rewrite H. fold erasure_H_fun_whole. unfold erasure_H_fun.  fold erasure_H_fun. 
    case_eq (return_free t). intro. auto. apply dot_erasure_dot. intro. 
    apply IHs'; auto. apply valid_syntax_after_erasure. auto. 
    apply return_free_imply_erasure_H_fun_dot in H3. auto. auto. Qed. 


Lemma label_of_erasure_helper : forall t e' s s', 
    valid_syntax t -> valid_syntax e' ->
    erasure_H_fun_whole (erasure_H_fun t) s = erasure_H_fun_whole (erasure_H_fun e') s' ->
    return_free t = false -> return_free e' = false ->
    erasure_H_fun_whole (labelOf (erasure_H_fun t)) s = 
    erasure_H_fun_whole (labelOf (erasure_H_fun e')) s'.
Proof. intros. generalize dependent t. generalize dependent e'. generalize dependent s'.
    induction s.  intros. generalize dependent e'.  generalize dependent t. induction s'.

    intros. unfold erasure_H_fun_whole in H1. rewrite H1. auto.

    intros. unfold erasure_H_fun_whole in H1. induction a. case_eq (flow_to l0 L_Label). intro.
    rewrite H4 in H1. unfold erasure_H_fun_whole. rewrite H4. rewrite H1. auto.

    intros.  rewrite H4 in H1. fold erasure_H_fun_whole in H1.
    unfold erasure_H_fun_whole.  rewrite H4. fold erasure_H_fun_whole. 
    unfold erasure_H_fun. fold erasure_H_fun. 
    case_eq (return_free (erasure_H_fun e')) . intro. 
    apply return_free_true_imply_erasure_H_fun_dot in H5. rewrite H5 in H1.  
    pose proof (dot_erasure_dot s'). rewrite H6 in H1. apply erasure_H_fun_imply_return_free in H1. 
    rewrite H1 in H2. inversion H2. auto. 
    apply valid_syntax_after_erasure. auto.
    intro. apply IHs'; auto. apply valid_syntax_after_erasure. auto.

    intros.  generalize dependent e'.  generalize dependent t. induction s'.
    intros. induction a.  unfold erasure_H_fun_whole in H1. 
    case_eq (flow_to l0 L_Label).  intro.  rewrite H4 in H1. 
    
    unfold erasure_H_fun_whole. rewrite H4. rewrite H1. auto. 
    intro. rewrite H4 in H1. fold erasure_H_fun_whole in H1.
    remember (erasure_H_fun_whole (labelOf (erasure_H_fun e')) nil) as tmp.  
    unfold erasure_H_fun_whole. rewrite H4.   fold erasure_H_fun_whole. rewrite Heqtmp.
    unfold erasure_H_fun. fold erasure_H_fun. 
    case_eq (return_free (erasure_H_fun t)) . intro. pose proof (dot_erasure_dot s). 
    apply return_free_true_imply_erasure_H_fun_dot in H5. rewrite H5 in H1. rewrite H6 in H1.
    assert (return_free e' = true). apply erasure_H_fun_imply_return_free. auto. auto. 
    rewrite H7 in H3. inversion H3.     apply valid_syntax_after_erasure. auto.
    intro. apply IHs; auto. apply valid_syntax_after_erasure. auto.

    intros. induction a.    case_eq (flow_to l0 L_Label).  intro. 
    assert (erasure_H_fun_whole (labelOf (erasure_H_fun t) )
  (Labeled_frame l0 s0 :: s)  = (labelOf (erasure_H_fun t) )). 
    unfold erasure_H_fun_whole. rewrite H4. auto. 
      
    unfold erasure_H_fun_whole in H1. rewrite H4 in H1. fold erasure_H_fun_whole in H1. 
    unfold erasure_H_fun_whole. rewrite H4.   fold erasure_H_fun_whole.
    induction a0. case_eq (flow_to l1 L_Label). intro. rewrite H6 in H1.  rewrite H1. auto .
    intro. rewrite H6 in H1. rewrite <- H5. unfold erasure_H_fun. fold erasure_H_fun. 
    case_eq (return_free (erasure_H_fun e')). intro. 
   apply return_free_true_imply_erasure_H_fun_dot in H7. rewrite H7 in H1.
    pose proof (dot_erasure_dot s'). rewrite H8 in H1. apply erasure_H_fun_imply_return_free in H1.
    rewrite H1 in H2. inversion H2. 
    auto. apply valid_syntax_after_erasure. auto. 

    intro. apply IHs'; auto. apply valid_syntax_after_erasure. auto. rewrite <- H1. 
    unfold erasure_H_fun_whole. rewrite H4. auto. 

    intro. induction a0. unfold erasure_H_fun_whole in H1. rewrite H4 in H1. fold erasure_H_fun_whole in H1. 
    unfold erasure_H_fun_whole. rewrite H4. fold erasure_H_fun_whole. 
     case_eq (flow_to l1 L_Label). intro. rewrite H5 in H1. 
    assert (erasure_H_fun_whole (labelOf (erasure_H_fun e') )
                     (Labeled_frame l1 s1 :: s') = labelOf (erasure_H_fun e')).
    unfold erasure_H_fun_whole. rewrite H5. auto. 
    unfold erasure_H_fun. fold erasure_H_fun. 

    case_eq (return_free (erasure_H_fun t)). intro. 
     apply return_free_true_imply_erasure_H_fun_dot in H7. rewrite H7 in H1.
    pose proof (dot_erasure_dot s). rewrite H8 in H1. assert (erasure_H_fun e' = dot). auto. 
    apply erasure_H_fun_imply_return_free in H9. rewrite H9 in H3. inversion H3. auto. 
    auto. apply valid_syntax_after_erasure. auto.

    intro. rewrite <- H6. apply IHs; auto.   apply valid_syntax_after_erasure. auto.
    rewrite H1. unfold erasure_H_fun_whole. rewrite H5. auto. 

    intro. rewrite H5 in H1. unfold erasure_H_fun. fold erasure_H_fun. 
    case_eq (return_free (erasure_H_fun t)). intro. 
    apply return_free_true_imply_erasure_H_fun_dot in H6. rewrite H6 in H1. 
    case_eq (return_free (erasure_H_fun e')). intro. 
    pose proof (dot_erasure_dot s). pose proof (dot_erasure_dot s').
    rewrite H8. rewrite H9. auto. 

    intro.  pose proof (dot_erasure_dot s). rewrite H8 in H1. rewrite H8. 
    assert (erasure_H_fun_whole (labelOf (erasure_H_fun (erasure_H_fun e'))) s' = dot).
    apply labelOf_erasure_dot; auto. 
    apply valid_syntax_after_erasure. apply valid_syntax_after_erasure. auto.
    intro contra. apply erasure_H_fun_imply_return_free in contra.  rewrite contra in H7. 
    inversion H7.   apply valid_syntax_after_erasure. auto. auto. 
     apply valid_syntax_after_erasure. auto.

    intro. case_eq (return_free (erasure_H_fun e')). intro. 
    pose proof (dot_erasure_dot s). pose proof (dot_erasure_dot s').
    rewrite H9. apply return_free_true_imply_erasure_H_fun_dot in H7. rewrite H7 in H1. 
    rewrite H9 in H1. 

    apply labelOf_erasure_dot; auto. 
    apply valid_syntax_after_erasure. apply valid_syntax_after_erasure. auto.
    intro contra. apply erasure_H_fun_imply_return_free in contra.  rewrite contra in H6. 
    inversion H6.   apply valid_syntax_after_erasure. auto. 
    apply valid_syntax_after_erasure. auto. 

    intro.  pose proof (dot_erasure_dot s). apply IHs; auto. 
     apply valid_syntax_after_erasure. auto. 
    apply valid_syntax_after_erasure. auto. 
Qed. 

Lemma unlabelOpaque_erasure_dot : forall t s',
    valid_syntax t-> 
    dot = erasure_H_fun_whole t s' -> t <> dot ->
    (erasure_H_fun_whole (unlabelOpaque t) s') = dot.
   Proof with eauto. intros.  generalize dependent t. induction s'. intros.  unfold erasure_H_fun_whole.  auto. 
    intros. unfold erasure_H_fun_whole in H0. rewrite H0 in H1. intuition.  induction a. 
    case_eq ( flow_to l0 L_Label). intros. unfold erasure_H_fun_whole in H1. rewrite H in H1.
    rewrite H1 in H2. intuition. intros.  unfold erasure_H_fun_whole in H1. rewrite H in H1.
    fold erasure_H_fun_whole in H1.
    unfold erasure_H_fun_whole.
    rewrite H. fold erasure_H_fun_whole. unfold erasure_H_fun.  fold erasure_H_fun. 
    case_eq (return_free t). intro. auto. apply dot_erasure_dot. intro. 
    apply IHs'; auto. apply valid_syntax_after_erasure. auto. 
    apply return_free_imply_erasure_H_fun_dot in H3. auto. auto. Qed. 

Lemma unlabelOpaque_erasure_helper : forall t e' s s', 
    valid_syntax t -> valid_syntax e' ->
    erasure_H_fun_whole (erasure_H_fun t) s = erasure_H_fun_whole (erasure_H_fun e') s' ->
    return_free t = false -> return_free e' = false ->
    erasure_H_fun_whole (unlabelOpaque (erasure_H_fun t)) s = 
    erasure_H_fun_whole (unlabelOpaque (erasure_H_fun e')) s'.
Proof. intros. generalize dependent t. generalize dependent e'. generalize dependent s'.
    induction s.  intros. generalize dependent e'.  generalize dependent t. induction s'.

    intros. unfold erasure_H_fun_whole in H1. rewrite H1. auto.

    intros. unfold erasure_H_fun_whole in H1. induction a. case_eq (flow_to l0 L_Label). intro.
    rewrite H4 in H1. unfold erasure_H_fun_whole. rewrite H4. rewrite H1. auto.

    intros.  rewrite H4 in H1. fold erasure_H_fun_whole in H1.
    unfold erasure_H_fun_whole.  rewrite H4. fold erasure_H_fun_whole. 
    unfold erasure_H_fun. fold erasure_H_fun. 
    case_eq (return_free (erasure_H_fun e')) . intro. 
    apply return_free_true_imply_erasure_H_fun_dot in H5. rewrite H5 in H1.  
    pose proof (dot_erasure_dot s'). rewrite H6 in H1. apply erasure_H_fun_imply_return_free in H1. 
    rewrite H1 in H2. inversion H2. auto. 
    apply valid_syntax_after_erasure. auto.
    intro. apply IHs'; auto. apply valid_syntax_after_erasure. auto.

    intros.  generalize dependent e'.  generalize dependent t. induction s'.
    intros. induction a.  unfold erasure_H_fun_whole in H1. 
    case_eq (flow_to l0 L_Label).  intro.  rewrite H4 in H1. 
    
    unfold erasure_H_fun_whole. rewrite H4. rewrite H1. auto. 
    intro. rewrite H4 in H1. fold erasure_H_fun_whole in H1.
    remember (erasure_H_fun_whole (unlabelOpaque (erasure_H_fun e')) nil) as tmp.  
    unfold erasure_H_fun_whole. rewrite H4.   fold erasure_H_fun_whole. rewrite Heqtmp.
    unfold erasure_H_fun. fold erasure_H_fun. 
    case_eq (return_free (erasure_H_fun t)) . intro. pose proof (dot_erasure_dot s). 
    apply return_free_true_imply_erasure_H_fun_dot in H5. rewrite H5 in H1. rewrite H6 in H1.
    assert (return_free e' = true). apply erasure_H_fun_imply_return_free. auto. auto. 
    rewrite H7 in H3. inversion H3.     apply valid_syntax_after_erasure. auto.
    intro. apply IHs; auto. apply valid_syntax_after_erasure. auto.

    intros. induction a.    case_eq (flow_to l0 L_Label).  intro. 
    assert (erasure_H_fun_whole (unlabelOpaque (erasure_H_fun t) )
  (Labeled_frame l0 s0 :: s)  = (unlabelOpaque (erasure_H_fun t) )). 
    unfold erasure_H_fun_whole. rewrite H4. auto. 
      
    unfold erasure_H_fun_whole in H1. rewrite H4 in H1. fold erasure_H_fun_whole in H1. 
    unfold erasure_H_fun_whole. rewrite H4.   fold erasure_H_fun_whole.
    induction a0. case_eq (flow_to l1 L_Label). intro. rewrite H6 in H1.  rewrite H1. auto .
    intro. rewrite H6 in H1. rewrite <- H5. unfold erasure_H_fun. fold erasure_H_fun. 
    case_eq (return_free (erasure_H_fun e')). intro. 
   apply return_free_true_imply_erasure_H_fun_dot in H7. rewrite H7 in H1.
    pose proof (dot_erasure_dot s'). rewrite H8 in H1. apply erasure_H_fun_imply_return_free in H1.
    rewrite H1 in H2. inversion H2. 
    auto. apply valid_syntax_after_erasure. auto. 

    intro. apply IHs'; auto. apply valid_syntax_after_erasure. auto. rewrite <- H1. 
    unfold erasure_H_fun_whole. rewrite H4. auto. 

    intro. induction a0. unfold erasure_H_fun_whole in H1. rewrite H4 in H1. fold erasure_H_fun_whole in H1. 
    unfold erasure_H_fun_whole. rewrite H4. fold erasure_H_fun_whole. 
     case_eq (flow_to l1 L_Label). intro. rewrite H5 in H1. 
    assert (erasure_H_fun_whole (unlabelOpaque (erasure_H_fun e') )
                     (Labeled_frame l1 s1 :: s') = unlabelOpaque (erasure_H_fun e')).
    unfold erasure_H_fun_whole. rewrite H5. auto. 
    unfold erasure_H_fun. fold erasure_H_fun. 

    case_eq (return_free (erasure_H_fun t)). intro. 
     apply return_free_true_imply_erasure_H_fun_dot in H7. rewrite H7 in H1.
    pose proof (dot_erasure_dot s). rewrite H8 in H1. assert (erasure_H_fun e' = dot). auto. 
    apply erasure_H_fun_imply_return_free in H9. rewrite H9 in H3. inversion H3. auto. 
    auto. apply valid_syntax_after_erasure. auto.

    intro. rewrite <- H6. apply IHs; auto.   apply valid_syntax_after_erasure. auto.
    rewrite H1. unfold erasure_H_fun_whole. rewrite H5. auto. 

    intro. rewrite H5 in H1. unfold erasure_H_fun. fold erasure_H_fun. 
    case_eq (return_free (erasure_H_fun t)). intro. 
    apply return_free_true_imply_erasure_H_fun_dot in H6. rewrite H6 in H1. 
    case_eq (return_free (erasure_H_fun e')). intro. 
    pose proof (dot_erasure_dot s). pose proof (dot_erasure_dot s').
    rewrite H8. rewrite H9. auto. 

    intro.  pose proof (dot_erasure_dot s). rewrite H8 in H1. rewrite H8. 
    assert (erasure_H_fun_whole (unlabelOpaque (erasure_H_fun (erasure_H_fun e'))) s' = dot).
    apply unlabelOpaque_erasure_dot; auto. 
    apply valid_syntax_after_erasure. apply valid_syntax_after_erasure. auto.
    intro contra. apply erasure_H_fun_imply_return_free in contra.  rewrite contra in H7. 
    inversion H7.   apply valid_syntax_after_erasure. auto. auto. 
     apply valid_syntax_after_erasure. auto.

    intro. case_eq (return_free (erasure_H_fun e')). intro. 
    pose proof (dot_erasure_dot s). pose proof (dot_erasure_dot s').
    rewrite H9. apply return_free_true_imply_erasure_H_fun_dot in H7. rewrite H7 in H1. 
    rewrite H9 in H1. 

    apply unlabelOpaque_erasure_dot; auto. 
    apply valid_syntax_after_erasure. apply valid_syntax_after_erasure. auto.
    intro contra. apply erasure_H_fun_imply_return_free in contra.  rewrite contra in H6. 
    inversion H6.   apply valid_syntax_after_erasure. auto. 
    apply valid_syntax_after_erasure. auto. 

    intro.  pose proof (dot_erasure_dot s). apply IHs; auto. 
     apply valid_syntax_after_erasure. auto. 
    apply valid_syntax_after_erasure. auto. 
Qed. 


Lemma sequence_erasure_dot : forall t t2 s',
    valid_syntax t-> 
    return_free t2 = true ->
    dot = erasure_H_fun_whole t s' -> t <> dot ->
    (erasure_H_fun_whole (Sequence t t2) s') = dot.
   Proof with eauto. intros.  generalize dependent t. induction s'. intros.  unfold erasure_H_fun_whole.  auto. 
    intros. unfold erasure_H_fun_whole in H0. unfold erasure_H_fun_whole in H1. 
     rewrite H1 in H2. intuition.  induction a. 
    case_eq ( flow_to l0 L_Label). intros. unfold erasure_H_fun_whole in H2. rewrite H in H2.
    rewrite <- H2 in H3. intuition. 
    intros.  unfold erasure_H_fun_whole in H2. rewrite H in H2.
    fold erasure_H_fun_whole in H2.
    unfold erasure_H_fun_whole.
    rewrite H. fold erasure_H_fun_whole. unfold erasure_H_fun.  fold erasure_H_fun. 
    case_eq (return_free t). intro. auto. rewrite H0.  apply dot_erasure_dot. intro. 
    apply IHs'; auto. apply valid_syntax_after_erasure. auto. 
    apply return_free_imply_erasure_H_fun_dot in H4. auto. auto. Qed. 


 Lemma Sequence_erasure_helper : forall t1 s1' s s' t2, 
    valid_syntax t1 -> valid_syntax s1' -> return_free t2 = true ->
    erasure_H_fun_whole (erasure_H_fun t1) s = erasure_H_fun_whole (erasure_H_fun s1') s' ->
    return_free t1 = false -> return_free s1' = false ->
    erasure_H_fun_whole (Sequence (erasure_H_fun t1) t2 ) s = 
    erasure_H_fun_whole (Sequence (erasure_H_fun s1') t2) s'.
    Proof. intros. generalize dependent t1. generalize dependent s1'. generalize dependent s'.
    induction s.  intros. generalize dependent s1'.  generalize dependent t1. induction s'.

    intros. unfold erasure_H_fun_whole in H2. rewrite H2. auto.

    intros. unfold erasure_H_fun_whole in H2. induction a. case_eq (flow_to l0 L_Label). intro.
    rewrite H5 in H2. unfold erasure_H_fun_whole. rewrite H5. rewrite H2. auto.

    intros.  rewrite H5 in H2. fold erasure_H_fun_whole in H2.
    unfold erasure_H_fun_whole.  rewrite H5. fold erasure_H_fun_whole. 
    unfold erasure_H_fun. fold erasure_H_fun. 
    case_eq (return_free (erasure_H_fun s1')) . intro. 
    apply return_free_true_imply_erasure_H_fun_dot in H6. rewrite H6 in H2.  
    pose proof (dot_erasure_dot s'). rewrite H7 in H2. apply erasure_H_fun_imply_return_free in H2. 
    rewrite H2 in H3. inversion H3. auto. 
    apply valid_syntax_after_erasure. auto.
    intro. apply IHs'; auto. apply valid_syntax_after_erasure. auto.

    intros.  generalize dependent s1'.  generalize dependent t1. induction s'.
    intros. induction a.  unfold erasure_H_fun_whole in H2. 
    case_eq (flow_to l0 L_Label).  intro.  rewrite H5 in H2. 
    
    unfold erasure_H_fun_whole. rewrite H5. rewrite H2. auto. 
    intro. rewrite H5 in H2. fold erasure_H_fun_whole in H2.
    remember (erasure_H_fun_whole (Sequence (erasure_H_fun s1') t2) nil) as tmp.  
    unfold erasure_H_fun_whole. rewrite H5.   fold erasure_H_fun_whole. rewrite Heqtmp.
    unfold erasure_H_fun. fold erasure_H_fun. 
    case_eq (return_free (erasure_H_fun t1)) . intro. pose proof (dot_erasure_dot s). 
    apply return_free_true_imply_erasure_H_fun_dot in H6. rewrite H6 in H2. rewrite H7 in H2.
    assert (return_free s1' = true). apply erasure_H_fun_imply_return_free. auto. auto. 
    rewrite H8 in H4. inversion H4.     apply valid_syntax_after_erasure. auto.
    intro. apply IHs; auto. apply valid_syntax_after_erasure. auto.

    intros. induction a.    case_eq (flow_to l0 L_Label).  intro. 
    assert (erasure_H_fun_whole (Sequence (erasure_H_fun t1) t2)
  (Labeled_frame l0 s0 :: s)  = (Sequence (erasure_H_fun t1) t2 )). 
    unfold erasure_H_fun_whole. rewrite H5. auto. 
      
    unfold erasure_H_fun_whole in H2. rewrite H5 in H2. fold erasure_H_fun_whole in H2. 
    unfold erasure_H_fun_whole. rewrite H5.   fold erasure_H_fun_whole.
    induction a0. case_eq (flow_to l1 L_Label). intro. rewrite H7 in H2.  rewrite H2. auto .
    intro. rewrite H7 in H2. rewrite <- H6. unfold erasure_H_fun. fold erasure_H_fun. 
    case_eq (return_free (erasure_H_fun s1')). intro. 
   apply return_free_true_imply_erasure_H_fun_dot in H8. rewrite H8 in H2.
    pose proof (dot_erasure_dot s'). rewrite H9 in H2. apply erasure_H_fun_imply_return_free in H2.
    rewrite H2 in H3. inversion H3. 
    auto. apply valid_syntax_after_erasure. auto. 

    intro. apply IHs'; auto. apply valid_syntax_after_erasure. auto. rewrite <- H2. 
    unfold erasure_H_fun_whole. rewrite H5. auto. 

    intro. induction a0. unfold erasure_H_fun_whole in H2. rewrite H5 in H2. fold erasure_H_fun_whole in H2. 
    unfold erasure_H_fun_whole. rewrite H5. fold erasure_H_fun_whole. 
     case_eq (flow_to l1 L_Label). intro. rewrite H6 in H2. 
    assert (erasure_H_fun_whole (Sequence (erasure_H_fun s1') t2 )
                     (Labeled_frame l1 s1 :: s') = Sequence (erasure_H_fun s1') t2).
    unfold erasure_H_fun_whole. rewrite H6. auto. 
    unfold erasure_H_fun. fold erasure_H_fun. 

    case_eq (return_free (erasure_H_fun t1)). intro. 
     apply return_free_true_imply_erasure_H_fun_dot in H8. rewrite H8 in H2.
    pose proof (dot_erasure_dot s). rewrite H9 in H2. assert (erasure_H_fun s1' = dot). auto. 
    apply erasure_H_fun_imply_return_free in H10. rewrite H10 in H4. inversion H4. auto. 
    auto. apply valid_syntax_after_erasure. auto.

    intro. rewrite <- H7. apply IHs; auto.   apply valid_syntax_after_erasure. auto.
    rewrite H2. unfold erasure_H_fun_whole. rewrite H6. auto. 

    intro. rewrite H6 in H2. unfold erasure_H_fun. fold erasure_H_fun. 
    case_eq (return_free (erasure_H_fun t1)). intro. 
    apply return_free_true_imply_erasure_H_fun_dot in H7. rewrite H7 in H2. 
    case_eq (return_free (erasure_H_fun s1')). intro. 
    pose proof (dot_erasure_dot s). pose proof (dot_erasure_dot s'). rewrite H1.
    rewrite H9. rewrite H10. auto. rewrite H1.  

    intro.  pose proof (dot_erasure_dot s). rewrite H9 in H2. rewrite H9. 
    assert (erasure_H_fun_whole (Sequence (erasure_H_fun (erasure_H_fun s1')) t2) s' = dot).
    apply sequence_erasure_dot; auto. 
    apply valid_syntax_after_erasure. apply valid_syntax_after_erasure. auto.
    intro contra. apply erasure_H_fun_imply_return_free in contra.  rewrite contra in H8. 
    inversion H8.   apply valid_syntax_after_erasure. auto. auto. 
     apply valid_syntax_after_erasure. auto.

    intro. case_eq (return_free (erasure_H_fun s1')). intro. 
    pose proof (dot_erasure_dot s). pose proof (dot_erasure_dot s'). rewrite H1. 
    rewrite H10. apply return_free_true_imply_erasure_H_fun_dot in H8. rewrite H8 in H2. 
    rewrite H10 in H2. 

    apply sequence_erasure_dot; auto. 
    apply valid_syntax_after_erasure. apply valid_syntax_after_erasure. auto.
    intro contra. apply erasure_H_fun_imply_return_free in contra.  rewrite contra in H7. 
    inversion H7.   apply valid_syntax_after_erasure. auto. 
    apply valid_syntax_after_erasure. auto. 

    intro.  pose proof (dot_erasure_dot s). apply IHs; auto. 
     apply valid_syntax_after_erasure. auto. 
    apply valid_syntax_after_erasure. auto.
Qed. 

    Lemma return_erasure_dot_helper : forall e' s', 
      valid_syntax e' ->
      dot = erasure_H_fun_whole (erasure_H_fun (erasure_H_fun e')) s' ->
      return_free (erasure_H_fun e') = false -> 
      erasure_H_fun_whole (erasure_H_fun (Return (erasure_H_fun (erasure_H_fun e')))) s' = dot.
    Proof. intros. generalize dependent e'.  induction s'. intros.  unfold erasure_H_fun_whole in H.  
    assert (erasure_H_fun (erasure_H_fun e') = dot). auto. 
    apply erasure_H_fun_imply_return_free in H2. rewrite H2 in H1. inversion H1. 
    apply valid_syntax_after_erasure. auto. 
    intros. unfold erasure_H_fun_whole in H0. induction a.
    case_eq (flow_to l0 L_Label).  intro. rewrite H2 in H0. 
    assert (erasure_H_fun (erasure_H_fun e') = dot). auto.  
    apply erasure_H_fun_imply_return_free in H3. rewrite H3 in H1. inversion H1. 
    apply valid_syntax_after_erasure. auto.
    intro. rewrite H2 in H0. fold  erasure_H_fun_whole in H0. 

    case_eq (return_free (erasure_H_fun (erasure_H_fun e'))). intro. unfold erasure_H_fun_whole.
    rewrite H2. fold erasure_H_fun_whole. unfold erasure_H_fun.  
    fold erasure_H_fun. rewrite H3. auto. unfold erasure_H_fun. unfold return_free.
   apply dot_erasure_dot.  

    intro. assert ( erasure_H_fun_whole
         (erasure_H_fun (Return (erasure_H_fun (erasure_H_fun (erasure_H_fun e'))))) s' = dot) .
    apply IHs'; auto. apply valid_syntax_after_erasure. auto.
    unfold erasure_H_fun_whole. rewrite H2. fold erasure_H_fun_whole. auto. 
    unfold erasure_H_fun. fold erasure_H_fun. rewrite H3. auto. 
Qed.

Lemma return_erasure_helper : forall t e' s s' s0 s1 l0 l1, 
    valid_syntax t -> valid_syntax e' ->
    flow_to l0 L_Label = false ->    flow_to l1 L_Label = false ->
    erasure_H_fun_whole (erasure_H_fun t) s = erasure_H_fun_whole (erasure_H_fun e') s' ->
    return_free t = false -> return_free e' = false ->
    erasure_H_fun_whole (Return (erasure_H_fun t)) (Labeled_frame l0 s0 :: s) = 
    erasure_H_fun_whole (Return (erasure_H_fun e')) (Labeled_frame l1 s1 :: s').
Proof. intros. generalize dependent t. generalize dependent e'. generalize dependent s'.
    induction s.  intros. generalize dependent e'.  generalize dependent t. induction s'.

    intros. unfold erasure_H_fun_whole in H3. rewrite H3. unfold erasure_H_fun_whole. 
    fold erasure_H_fun_whole.  rewrite H1. rewrite H2. auto.

    intros. unfold erasure_H_fun_whole in H3. induction a. case_eq (flow_to l2 L_Label). intro.
    rewrite H6 in H3. unfold erasure_H_fun_whole. rewrite H6. rewrite H3. auto.
    rewrite H1. rewrite H2. auto. 

    intros.   rewrite H6 in H3. fold erasure_H_fun_whole in H3.
    unfold erasure_H_fun_whole.  rewrite H6. fold erasure_H_fun_whole. 
    unfold erasure_H_fun. fold erasure_H_fun. rewrite H1. rewrite H2.  
    case_eq (return_free (erasure_H_fun e')) . intro. 
    apply return_free_true_imply_erasure_H_fun_dot in H7. rewrite H7 in H3.  
    pose proof (dot_erasure_dot s'). rewrite H8 in H3. apply erasure_H_fun_imply_return_free in H3. 
    rewrite H3 in H4. inversion H4. auto. 
    apply valid_syntax_after_erasure. auto. 

    intro. 
    assert (erasure_H_fun_whole (Return (erasure_H_fun t))
         (Labeled_frame l0 s0 :: nil) =
               erasure_H_fun_whole (Return (erasure_H_fun (erasure_H_fun e')))
                 (Labeled_frame l1 s1 :: s')).
    apply IHs'; auto. apply valid_syntax_after_erasure. auto.
    unfold erasure_H_fun_whole in H8. rewrite H1 in H8. rewrite H2 in H8.
    fold erasure_H_fun_whole in H8. 

    case_eq (return_free (erasure_H_fun t)).  intro. rewrite <- H8. 
    unfold erasure_H_fun. fold erasure_H_fun. rewrite H9. auto. 
   intro. rewrite <- H8.  unfold erasure_H_fun. fold  erasure_H_fun. rewrite H9. auto.  

    intros.  generalize dependent e'.  generalize dependent t. induction s'.
    intros. induction a.  unfold erasure_H_fun_whole in H3. 
    case_eq (flow_to l2 L_Label).  intro.  rewrite H6 in H3.  unfold erasure_H_fun_whole. 
    fold erasure_H_fun_whole.  rewrite H1. rewrite H2. rewrite H6. rewrite H3. auto. 

    intro. rewrite H6 in H3. fold erasure_H_fun_whole in H3. 
    case_eq (return_free (erasure_H_fun t)). intro. 
    assert ((erasure_H_fun (erasure_H_fun t)) = dot). 
    apply return_free_true_imply_erasure_H_fun_dot; auto. 
    apply valid_syntax_after_erasure. auto. rewrite H8 in H3. 
    pose proof (dot_erasure_dot s). rewrite H9 in H3. 
    assert (return_free e' = true).  apply erasure_H_fun_imply_return_free ; auto.
    rewrite H10 in H5. inversion H5. 

    intro.
    assert (erasure_H_fun_whole (Return (erasure_H_fun (erasure_H_fun t)))
        (Labeled_frame l0 s0 :: s) =
      erasure_H_fun_whole (Return (erasure_H_fun e'))
        (Labeled_frame l1 s1 :: nil)).
    apply IHs; auto. apply valid_syntax_after_erasure. auto.
    rewrite <- H8. unfold  erasure_H_fun_whole. rewrite H1.  rewrite H6. 
    
    fold erasure_H_fun_whole.  remember (erasure_H_fun_whole
  (erasure_H_fun (erasure_H_fun (Return (erasure_H_fun t)))) s) as tmp. 
    unfold erasure_H_fun in Heqtmp. fold erasure_H_fun in Heqtmp. rewrite H7 in Heqtmp. auto. 

    intros.  induction a.    case_eq (flow_to l2 L_Label).  intro. 
    assert (erasure_H_fun_whole (Return (erasure_H_fun t) )
  (Labeled_frame l0 s0 :: Labeled_frame l2 s2 :: s)  = (erasure_H_fun (Return (erasure_H_fun t) ))). 
    unfold erasure_H_fun_whole.  rewrite H6. rewrite H1. auto. 
      
    unfold erasure_H_fun_whole in H3. rewrite H6 in H3. fold erasure_H_fun_whole in H3. 
    unfold erasure_H_fun_whole. rewrite H6.   fold erasure_H_fun_whole. rewrite H1. rewrite H2. 
    induction a0. case_eq (flow_to l3 L_Label). intro. rewrite H8 in H3.  rewrite H3. auto .
    intro. rewrite H8 in H3. rewrite <- H7. unfold erasure_H_fun. fold erasure_H_fun. 
    case_eq (return_free (erasure_H_fun e')). intro. 
   apply return_free_true_imply_erasure_H_fun_dot in H9. rewrite H9 in H3.
    pose proof (dot_erasure_dot s'). rewrite H10 in H3. apply erasure_H_fun_imply_return_free in H3.
    rewrite H3 in H4. inversion H4. 
    auto. apply valid_syntax_after_erasure. auto. 

    intro.  
    assert (erasure_H_fun_whole (Return (erasure_H_fun t))
         (Labeled_frame l0 s0 :: Labeled_frame l2 s2 :: s) =
       erasure_H_fun_whole (Return (erasure_H_fun (erasure_H_fun e')))
         (Labeled_frame l1 s1 :: s')). 
    apply IHs'; auto. apply valid_syntax_after_erasure. auto. rewrite <- H3. 
    unfold erasure_H_fun_whole. rewrite H6. auto. rewrite H10. 
    remember (erasure_H_fun_whole
  (erasure_H_fun (Return (erasure_H_fun (erasure_H_fun e')))) s') as tmp.
    unfold erasure_H_fun_whole. fold erasure_H_fun_whole. rewrite H2. auto. 

    intro. induction a0.
unfold erasure_H_fun_whole in H3. rewrite H6 in H3. fold erasure_H_fun_whole in H3. 
 case_eq (flow_to l3 L_Label). intro. rewrite H7 in H3.  
    case_eq (return_free (erasure_H_fun t)). intro.

     apply return_free_true_imply_erasure_H_fun_dot in H8. rewrite H8 in H3. 
    pose proof (dot_erasure_dot s). rewrite H9 in H3. assert (erasure_H_fun e' = dot). auto. 
    apply erasure_H_fun_imply_return_free in H10. rewrite H10 in H5. inversion H5. auto. 
    auto. apply valid_syntax_after_erasure. auto. 

    intro. 
      assert (
      erasure_H_fun_whole (Return (erasure_H_fun (erasure_H_fun t)))
        (Labeled_frame l0 s0 :: s) =
      erasure_H_fun_whole (Return (erasure_H_fun e'))
        (Labeled_frame l1 s1 :: Labeled_frame l3 s3 :: s')).
    apply IHs; auto. apply valid_syntax_after_erasure. auto.

    unfold erasure_H_fun_whole. rewrite H7. fold erasure_H_fun_whole. auto. 
    rewrite <- H9. 
    unfold erasure_H_fun_whole. rewrite H1. rewrite H6. fold erasure_H_fun_whole. 

    remember (erasure_H_fun_whole
  (erasure_H_fun (Return (erasure_H_fun (erasure_H_fun t)))) s) as tmp.
    unfold erasure_H_fun. fold erasure_H_fun.  rewrite H8. auto.  
 
    intro. rewrite H7 in H3. unfold  erasure_H_fun_whole.  rewrite H1. rewrite H6. 
    rewrite H7. fold erasure_H_fun_whole. rewrite H2.  

    unfold erasure_H_fun. fold erasure_H_fun. 
    case_eq (return_free (erasure_H_fun t)). intro. 
    apply return_free_true_imply_erasure_H_fun_dot in H8. rewrite H8 in H3. 
    case_eq (return_free (erasure_H_fun e')). intro. 
    pose proof (dot_erasure_dot s). pose proof (dot_erasure_dot s'). 
    unfold erasure_H_fun. unfold return_free.     rewrite H10. rewrite H11. auto. 

    intro.  pose proof (dot_erasure_dot s). rewrite H10 in H3. 
    assert (erasure_H_fun_whole
  (erasure_H_fun (Return (erasure_H_fun (erasure_H_fun e')))) s' = dot).
    apply return_erasure_dot_helper; auto. rewrite H11. 
  unfold erasure_H_fun. unfold return_free. rewrite H10. auto. 
     apply valid_syntax_after_erasure. auto.

    intro. 
    case_eq (return_free (erasure_H_fun e')). intro. 
    apply return_free_true_imply_erasure_H_fun_dot in H9. rewrite H9 in H3. 
    pose proof (dot_erasure_dot s). pose proof (dot_erasure_dot s'). rewrite H11 in H3. 

   assert (erasure_H_fun_whole (erasure_H_fun (Return (erasure_H_fun (erasure_H_fun t)))) s = dot).
   apply return_erasure_dot_helper; auto. rewrite H12. unfold erasure_H_fun. unfold return_free. 
    rewrite H11. auto.      apply valid_syntax_after_erasure. auto.
   intro. 
   assert (erasure_H_fun_whole (Return (erasure_H_fun t))
               (Labeled_frame l0 s0 :: Labeled_frame l2 s2 :: s) =
             erasure_H_fun_whole (Return (erasure_H_fun (erasure_H_fun e')))
               (Labeled_frame l1 s1 :: s')).
  apply IHs'; auto.   apply valid_syntax_after_erasure. auto. 
  unfold erasure_H_fun_whole. fold erasure_H_fun_whole.  rewrite H6.  auto. 
  unfold erasure_H_fun_whole in H10. rewrite H6 in H10. rewrite H1 in H10. 
  fold erasure_H_fun_whole in H10. rewrite H2 in H10. 
  
  case_eq (return_free (erasure_H_fun t)). intro. rewrite H11 in H8. inversion H8. 
  intro. 
  rewrite <- H10. remember (erasure_H_fun_whole
  (erasure_H_fun (Return (erasure_H_fun (erasure_H_fun t)))) s) as tmp. 
   unfold erasure_H_fun. fold erasure_H_fun. rewrite H11. auto. 
Qed.  


Lemma simulation_H : forall CT t t0 t' t0' s h s' h' sigma_l_e sigma_r_e,
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
Proof. 
  intros CT t t0 t' t0' s h s' h' sigma_l_e sigma_r_e. intro H_dot_free. intro H_valid_syntax. 
  intro T. intro H_typing. intro H_wfe_fields. 
  intro H_wfe_heap. intro H_wfe_stack. 
  intro H_flow_l.   intro H_flow_r. intro H_reduction. 
  (*intro H_erasure_sigma_l.  *) intro H_erasure_l. intro H_erasure_r.   
  
generalize dependent t'. 
  generalize dependent t0.
  generalize dependent t0'.
  generalize dependent T.
    generalize dependent sigma_l_e.      generalize dependent sigma_r_e. 
    generalize dependent s.      generalize dependent h.
    generalize dependent s'.      generalize dependent h'.
induction t; intros; try (inversion H_reduction; subst).
- (* (Tvar i) *) inversion H_typing. inversion H3. 
- (*(FieldAccess t i)*) intros. 
unfold dot_free in H_dot_free. fold dot_free in H_dot_free. auto.
inversion H_erasure_l. subst.
  + rewrite H_flow_l in H3. inversion H3.
  + subst.  inversion H_erasure_r. subst.
        rewrite H_flow_r in H4. inversion H4. subst. 
  ++  inversion H_typing. subst. 
    assert (Config CT (erasure_H_fun_whole t s) (SIGMA  s'0 h'0) = Config CT (erasure_H_fun_whole e' s')  (SIGMA s'1 h'1)).
    apply IHt with h' s' h s (classTy clsT)  e'; auto.     
    inversion H_valid_syntax. auto. 
    apply erasure_H_context; auto.     auto. apply erasure_H_context; auto.

    unfold erasure_H_fun_whole.  
    induction s. 
    pose proof (nil_flow_to_L_Label h). rewrite H1 in H_flow_l. inversion H_flow_l. 

    induction a. apply flow_to_simpl in H_flow_l. rewrite H_flow_l. fold erasure_H_fun_whole.
    fold erasure_H_fun_whole in IHs. unfold erasure_H_fun. fold erasure_H_fun. 

    unfold erasure_H_fun_whole.  
    induction s'. 
    pose proof (nil_flow_to_L_Label h'). rewrite H1 in H_flow_r. inversion H_flow_r. 

    induction a. apply flow_to_simpl in H_flow_r. rewrite H_flow_r. fold erasure_H_fun_whole.
    fold erasure_H_fun_whole in IHs'. unfold erasure_H_fun. fold erasure_H_fun. 

     unfold erasure_H_fun_whole in H. fold erasure_H_fun_whole in H. 
      rewrite H_flow_l in H. rewrite H_flow_r in H.

     inversion H. subst. auto.  
      
     case_eq (return_free t). case_eq (return_free e'). intros. 
     pose proof (dot_erasure_dot s).      pose proof (dot_erasure_dot s').
      rewrite H9. rewrite H11. auto.  
     
     intros. pose proof (dot_erasure_dot s).  rewrite H9. 
    apply return_free_true_imply_erasure_H_fun_dot in H7. 
    rewrite H7 in H6. rewrite H9 in H6. 
    assert ((Labeled_frame l0 s0 :: s)  = s').
    apply return_free_change_imply_method_call with t CT h l1 s1 h' e' (classTy clsT); auto.
    apply erasure_H_fun_imply_return_free. inversion H_valid_syntax. auto. auto. 

    assert ((erasure_H_fun_whole (FieldAccess (erasure_H_fun e') i) s') = dot).
    apply field_access_erasure_dot; auto. apply valid_syntax_after_erasure; auto. 
    inversion H_valid_syntax. 
    apply valid_syntax_preservation with CT t  (SIGMA (Labeled_frame l1 s1 :: s') h')
                  (Labeled_frame l0 s0 :: s) h (classTy clsT); auto. 
    apply return_free_imply_erasure_H_fun_dot  in H1. auto. 
    apply valid_syntax_preservation with CT t  (SIGMA (Labeled_frame l1 s1 :: s') h')
                  (Labeled_frame l0 s0 :: s) h (classTy clsT); auto.  
    inversion H_valid_syntax. auto. rewrite H12. auto. 
    inversion H_valid_syntax.  auto. 

    intro. case_eq (return_free e'). intro. 
    apply return_free_true_imply_erasure_H_fun_dot in H7. rewrite H7 in H6. 
    assert (erasure_H_fun_whole dot s' = dot). apply dot_erasure_dot. 
    rewrite H9 in H6. 
    assert ((erasure_H_fun_whole (FieldAccess (erasure_H_fun t) i) s) = dot).
    apply field_access_erasure_dot; auto. apply valid_syntax_after_erasure; auto. 
    inversion H_valid_syntax. auto. 
    apply return_free_imply_erasure_H_fun_dot in H1. auto. 
    inversion H_valid_syntax. auto. 
    rewrite H11. rewrite H9. auto. 
     apply valid_syntax_preservation with CT t  (SIGMA (Labeled_frame l1 s1 :: s') h')
                  (Labeled_frame l0 s0 :: s) h (classTy clsT); auto.   
    inversion H_valid_syntax. auto. 
    intro. 

    
    
    assert (erasure_H_fun_whole (FieldAccess (erasure_H_fun t) i) s = 
    erasure_H_fun_whole (FieldAccess (erasure_H_fun e') i) s'). 
    apply field_access_erasure_helper; auto. inversion H_valid_syntax. auto. 
    apply valid_syntax_preservation with CT t  (SIGMA (Labeled_frame l1 s1 :: s') h')
                  (Labeled_frame l0 s0 :: s) h (classTy clsT); auto.   
    inversion H_valid_syntax. auto. 
    rewrite H9. auto.  

- (*FieldAccess (ObjId o) i*)  
  intros. unfold dot_free in H_dot_free. fold dot_free in H_dot_free. auto.
  inversion H_erasure_l. subst.
  + rewrite H_flow_l in H2. inversion H2.
  + subst.  inversion H_erasure_r. subst.
        rewrite H_flow_r in H3. inversion H3. subst. 
  ++  inversion H_typing. subst. unfold erasure_H_fun_whole.
        induction s. 
        pose proof (nil_flow_to_L_Label h). rewrite H in H_flow_l. inversion H_flow_l.
    induction a. apply flow_to_simpl in H_flow_l. rewrite H_flow_l. fold erasure_H_fun_whole.
    fold erasure_H_fun_whole in IHs. unfold erasure_H_fun. fold erasure_H_fun. 
 assert (return_free (ObjId o) = true).
  auto.  rewrite H. inversion H_reduction. inversion H5. subst.   inversion H9.  subst. 
  inversion H5. inversion H18. subst. inversion H23. subst. rename h1 into h.  
  assert (( t' = null \/ exists o',  t' = ObjId o')).
  apply field_value with h o cls fields lb i CT cls'; auto. 
  assert ((erasure_H_fun_whole t' (Labeled_frame lb0 s1 :: s)) = dot). apply value_erasure_dot; auto.
  destruct H0. rewrite H0. auto. destruct H0 as [o']. rewrite H0. auto.
  rewrite H9. assert ((erasure_H_fun_whole dot s) = dot). apply dot_erasure_dot; auto.
  rewrite H11. rewrite H14. rewrite H12. 
      assert (l0 = lb0). apply label_equivalence; auto; 
      apply flow_transitive with l0; auto. rewrite H13. auto.   

- (*MethodCall t1' i t2*)  admit. 
- (*MethodCall t1 i t2'*)  admit.
- (*MethodCall o i v*) 
 inversion H_erasure_l. subst.
  + rewrite H_flow_l in H2. inversion H2.
  + subst.  inversion H_erasure_r. subst.
        rewrite H_flow_r in H3. inversion H3. subst. 
  ++  inversion H_typing. subst. inversion H6. inversion H14.  subst. 
        rewrite H11. rewrite H13. 
    induction s0. pose proof (nil_flow_to_L_Label h0). rewrite H in H_flow_l.
    inversion H_flow_l. induction a. apply flow_to_simpl in H_flow_l.
    unfold erasure_H_fun_whole. fold erasure_H_fun_whole. rewrite H_flow_l.
    unfold erasure_H_fun . fold erasure_H_fun. 
    unfold return_free. fold return_free. 
    assert (return_free t2 = true). apply value_is_return_free. auto.  
    rewrite H.  auto. rewrite H2. 

    inversion H4. subst. destruct H23 as [F']. destruct H0 as [lo']. rewrite H0 in H7. 
    inversion H7. subst. rewrite <- H15   in H10. inversion H10. subst. 
    rewrite H12 in H8. inversion H8. subst. 
    
    assert (return_free body0 = true). apply surface_syntax_is_return_free. auto. 
    rewrite H1.  

    unfold erasure_H_fun. unfold return_free. 

    unfold erasure_sigma_fun. unfold erasure_stack. rewrite H_flow_l. rewrite H2. 
    fold erasure_stack. auto. 

-  (* MethodCall (ObjId o) i (unlabelOpaque (v_opa_l v lb))  *) 
 inversion H_erasure_l. subst.
  + rewrite H_flow_l in H2. inversion H2.
  + subst.  inversion H_erasure_r. subst.
        rewrite H_flow_r in H3. inversion H3. subst. 
  ++  inversion H_typing. subst. inversion H6. inversion H14.  subst. 
        rewrite H11. rewrite H9. 
    induction s0. pose proof (nil_flow_to_L_Label h0). rewrite H in H_flow_l.
    inversion H_flow_l. induction a. apply flow_to_simpl in H_flow_l.
    unfold erasure_H_fun_whole. fold erasure_H_fun_whole. rewrite H_flow_l.
    unfold erasure_H_fun . fold erasure_H_fun. 
    unfold return_free. fold return_free. 
    assert (return_free v = true). apply value_is_return_free. inversion H5.  auto.  
    rewrite H.  auto. 

    assert (flow_to
      (join_label lb (current_label (SIGMA (Labeled_frame l0 s :: s0) h0)))
      L_Label = false). 
    apply flow_join_label with (current_label (SIGMA (Labeled_frame l0 s :: s0) h0)) lb; auto.
    rewrite H0.  

    inversion H4. subst. destruct H24 as [F']. destruct H1 as [lo']. rewrite H1 in H7. 
    inversion H7. subst. rewrite <- H16   in H8. inversion H8. subst. 
    rewrite H10 in H13. inversion H13. subst. 
    
    assert (return_free body0 = true). apply surface_syntax_is_return_free. auto. 
    rewrite H15.  

    unfold erasure_H_fun. unfold return_free. 

    unfold erasure_sigma_fun. unfold erasure_stack. rewrite H_flow_l. rewrite H0. 
    fold erasure_stack. auto. 

- (* new exp*) 
 inversion H_erasure_l. subst.
  + rewrite H_flow_l in H2. inversion H2.
  + subst.  inversion H_erasure_r. subst.
        rewrite H_flow_r in H3. inversion H3. subst. 
  ++  inversion H_typing. subst. inversion H5. inversion H11.  subst.
       rewrite H9. rewrite H12.
    remember (add_heap_obj h0 (get_fresh_oid h0)
           (Heap_OBJ (class_def c field_defs method_defs)
              (init_field_map field_defs empty_field_map)
              (current_label (SIGMA s0 h0)))) as h'.
    assert (erasure_sigma_fun (SIGMA s0 h0) =   erasure_sigma_fun (SIGMA s0 h')). 
    apply extend_heap_preserve_erasure with (get_fresh_oid h0) CT 
        (class_def c field_defs method_defs)
         (init_field_map field_defs empty_field_map)
        (current_label (SIGMA s0 h0)); auto. 
     induction s0. pose proof (nil_flow_to_L_Label h0). rewrite H0 in H_flow_l.
    inversion H_flow_l. induction a. apply flow_to_simpl in H_flow_l.
    unfold erasure_H_fun_whole. fold  erasure_H_fun_whole. rewrite H_flow_l. 
    unfold erasure_H_fun. rewrite H. auto.  
      

- (* label data *) 
 intros. 
unfold dot_free in H_dot_free. fold dot_free in H_dot_free. auto.
inversion H_valid_syntax. 
pose proof (valid_syntax_after_erasure t H1). subst.    
inversion H_erasure_l. subst.
  + rewrite H_flow_l in H5. inversion H5.
  + subst.  inversion H_erasure_r. subst.
        rewrite H_flow_r in H6. inversion H6. subst. 
  ++ inversion H_typing. subst. 
    assert (Config CT (erasure_H_fun_whole t s) (SIGMA  s'0 h'0) = Config CT (erasure_H_fun_whole e' s')  (SIGMA s'1 h'1)).
    apply IHt with h' s' h s T0 e'; auto.     
    inversion H_valid_syntax. auto. 
    apply erasure_H_context; auto.     auto. apply erasure_H_context; auto.

    unfold erasure_H_fun_whole.  
    induction s. 
    pose proof (nil_flow_to_L_Label h). rewrite H2 in H_flow_l. inversion H_flow_l. 

    induction a. apply flow_to_simpl in H_flow_l. rewrite H_flow_l. fold erasure_H_fun_whole.
    fold erasure_H_fun_whole in IHs. unfold erasure_H_fun. fold erasure_H_fun. 

    unfold erasure_H_fun_whole.  
    induction s'. 
    pose proof (nil_flow_to_L_Label h'). rewrite H2 in H_flow_r. inversion H_flow_r. 

    induction a. apply flow_to_simpl in H_flow_r. rewrite H_flow_r. fold erasure_H_fun_whole.
    fold erasure_H_fun_whole in IHs'. unfold erasure_H_fun. fold erasure_H_fun. 

     unfold erasure_H_fun_whole in H. fold erasure_H_fun_whole in H. 
      rewrite H_flow_l in H. rewrite H_flow_r in H.

     inversion H. subst. auto.  
      
     case_eq (return_free t). case_eq (return_free e'). intros. 
     pose proof (dot_erasure_dot s).      pose proof (dot_erasure_dot s').
      rewrite H8. rewrite H11. auto.  
     
     intros. pose proof (dot_erasure_dot s).  rewrite H8. 
    apply return_free_true_imply_erasure_H_fun_dot in H7. 
    rewrite H7 in H4. rewrite H8 in H4. 
   (* assert ((Labeled_frame l0 s0 :: s)  = s').
    apply return_free_change_imply_method_call with t CT h l2 s1 h' e' T0; auto.
    apply erasure_H_fun_imply_return_free. inversion H_valid_syntax. auto. auto*)

    assert ((erasure_H_fun_whole (labelData (erasure_H_fun e') l0) s') = dot).
    apply label_data_erasure_dot; auto. apply valid_syntax_after_erasure; auto. 
    apply valid_syntax_preservation with CT t  (SIGMA (Labeled_frame l2 s1 :: s') h')
                  (Labeled_frame l1 s0 :: s) h T0; auto. 
    apply return_free_imply_erasure_H_fun_dot  in H2. auto.
    apply valid_syntax_preservation with CT t  (SIGMA (Labeled_frame l2 s1 :: s') h')
                  (Labeled_frame l1 s0 :: s) h T0; auto. auto.   
    rewrite H11. auto. auto. 

    intro. case_eq (return_free e'). intro. 
    apply return_free_true_imply_erasure_H_fun_dot in H7. rewrite H7 in H4. 
    assert (erasure_H_fun_whole dot s' = dot). apply dot_erasure_dot. 
    rewrite H8 in H4. 
    assert ((erasure_H_fun_whole (labelData (erasure_H_fun t) l0) s) = dot).
    apply label_data_erasure_dot; auto.
    apply return_free_imply_erasure_H_fun_dot  in H2. auto. auto. 
    rewrite H11. rewrite H8. auto. 
    apply valid_syntax_preservation with CT t  (SIGMA (Labeled_frame l2 s1 :: s') h')
                  (Labeled_frame l1 s0 :: s) h T0; auto. auto.   
    intro. 

    assert (erasure_H_fun_whole (labelData (erasure_H_fun t) l0) s = 
    erasure_H_fun_whole (labelData (erasure_H_fun e') l0) s'). 
    apply label_data_erasure_helper; auto.
    apply valid_syntax_preservation with CT t  (SIGMA (Labeled_frame l2 s1 :: s') h')
                  (Labeled_frame l1 s0 :: s) h T0; auto. 
    rewrite H8. auto.  

- (* v_l t lb *) 
 inversion H_erasure_l. subst.
  + rewrite H_flow_l in H3. inversion H3.
  + subst.  inversion H_erasure_r. subst.
        rewrite H_flow_r in H4. inversion H4. subst. 
  ++  inversion H_typing. subst. rewrite H8. rewrite H10. 
    induction s'. pose proof (nil_flow_to_L_Label h'). rewrite H in H_flow_l.
    inversion H_flow_l. induction a. apply flow_to_simpl in H_flow_l.
    unfold erasure_H_fun_whole. fold erasure_H_fun_whole. rewrite H_flow_l.
    unfold erasure_H_fun . fold erasure_H_fun. 
    unfold return_free. fold return_free. 
    assert (return_free t = true). apply value_is_return_free. auto.  
    rewrite H.  auto. 

-  (* unlabel *) admit. 

-  (* unlabel v_l *) 
 inversion H_erasure_l. subst.
  + rewrite H_flow_l in H2. inversion H2.
  + subst.  inversion H_erasure_r. subst.
        rewrite H_flow_r in H3. inversion H3. subst. 
  ++  inversion H_typing. subst. inversion H4. inversion H7.  subst. 
        rewrite H10. rewrite H12. 
    induction s0. pose proof (nil_flow_to_L_Label h0). rewrite H in H_flow_l.
    inversion H_flow_l. induction a. apply flow_to_simpl in H_flow_l.
    unfold erasure_H_fun_whole. fold erasure_H_fun_whole. rewrite H_flow_l.
    unfold erasure_H_fun . fold erasure_H_fun. 
    unfold return_free. fold return_free. 
    assert (return_free t' = true). apply value_is_return_free. auto.  
    inversion H6. auto. rewrite H.  auto. 

    assert (erasure_H_fun_whole t'
     (update_current_label (Labeled_frame l0 s :: s0)
        (join_label lb (current_label (SIGMA (Labeled_frame l0 s :: s0) h0)))) = dot).
    apply value_erasure_dot.     inversion H6. auto.
    apply flow_join_label with (current_label (SIGMA (Labeled_frame l0 s :: s0) h0)) lb; auto. 
    subst. rewrite H17. 

    pose proof (dot_erasure_dot s0). rewrite H0. 
    unfold update_current_label. unfold erasure_sigma_fun. unfold erasure_stack. 
    rewrite H_flow_l. fold erasure_stack. 
    assert (flow_to
         (join_label lb (current_label (SIGMA (Labeled_frame l0 s :: s0) h0)))
         L_Label = false).
    apply flow_join_label with (current_label (SIGMA (Labeled_frame l0 s :: s0) h0)) lb; auto. 
    rewrite H1. auto. 

-  (* labelOf *) 

 intros. 
unfold dot_free in H_dot_free. fold dot_free in H_dot_free. auto.
inversion H_valid_syntax. 
pose proof (valid_syntax_after_erasure t H1). subst.    
inversion H_erasure_l. subst.
  + rewrite H_flow_l in H5. inversion H5.
  + subst.  inversion H_erasure_r. subst.
        rewrite H_flow_r in H6. inversion H6. subst. 
  ++  inversion H_typing. subst. 
    assert (Config CT (erasure_H_fun_whole t s) (SIGMA  s'0 h'0) = Config CT (erasure_H_fun_whole e' s')  (SIGMA s'1 h'1)).
    apply IHt with h' s' h s (LabelelTy T0)  e'; auto.     
    apply erasure_H_context; auto.     auto. apply erasure_H_context; auto.

    unfold erasure_H_fun_whole.  
    induction s. 
    pose proof (nil_flow_to_L_Label h). rewrite H3 in H_flow_l. inversion H_flow_l. 

    induction a. apply flow_to_simpl in H_flow_l. rewrite H_flow_l. fold erasure_H_fun_whole.
    fold erasure_H_fun_whole in IHs. unfold erasure_H_fun. fold erasure_H_fun. 

    unfold erasure_H_fun_whole.  
    induction s'. 
    pose proof (nil_flow_to_L_Label h'). rewrite H3 in H_flow_r. inversion H_flow_r. 

    induction a. apply flow_to_simpl in H_flow_r. rewrite H_flow_r. fold erasure_H_fun_whole.
    fold erasure_H_fun_whole in IHs'. unfold erasure_H_fun. fold erasure_H_fun. 

    unfold erasure_H_fun_whole in H. fold erasure_H_fun_whole in H. 
      rewrite H_flow_l in H. rewrite H_flow_r in H.

     inversion H. subst. auto.  

     case_eq (return_free t). case_eq (return_free e'). intros. 
     pose proof (dot_erasure_dot s).      pose proof (dot_erasure_dot s').
      rewrite H9. rewrite H11. auto.  
     
     intros. pose proof (dot_erasure_dot s).  rewrite H9. 
    apply return_free_true_imply_erasure_H_fun_dot in H7. 
    rewrite H7 in H4. rewrite H9 in H4. 

    assert ((erasure_H_fun_whole (labelOf (erasure_H_fun e')) s') = dot).
    apply labelOf_erasure_dot; auto. apply valid_syntax_after_erasure; auto.  
    apply valid_syntax_preservation with CT t  (SIGMA (Labeled_frame l1 s1 :: s') h')
                  (Labeled_frame l0 s0 :: s) h (LabelelTy T0); auto. 

    apply return_free_imply_erasure_H_fun_dot  in H3. auto. 
    apply valid_syntax_preservation with CT t  (SIGMA (Labeled_frame l1 s1 :: s') h')
                  (Labeled_frame l0 s0 :: s) h (LabelelTy T0); auto. 
    rewrite H11. auto. auto.  

    intro. case_eq (return_free e'). intro. 
    apply return_free_true_imply_erasure_H_fun_dot in H7. rewrite H7 in H4. 
    assert (erasure_H_fun_whole dot s' = dot). apply dot_erasure_dot. 
    rewrite H9 in H4.  rewrite H9. 
    assert ((erasure_H_fun_whole (labelOf (erasure_H_fun t)) s) = dot).
    apply labelOf_erasure_dot; auto.  
    apply return_free_imply_erasure_H_fun_dot in H3. auto. auto. 
    rewrite H11. auto. 
    apply valid_syntax_preservation with CT t  (SIGMA (Labeled_frame l1 s1 :: s') h')
                  (Labeled_frame l0 s0 :: s) h (LabelelTy T0); auto. 
    intro. 

    assert (erasure_H_fun_whole (labelOf (erasure_H_fun t)) s = 
    erasure_H_fun_whole (labelOf (erasure_H_fun e')) s'). 
    apply label_of_erasure_helper; auto. auto. 
    apply valid_syntax_preservation with CT t  (SIGMA (Labeled_frame l1 s1 :: s') h')
                  (Labeled_frame l0 s0 :: s) h (LabelelTy T0); auto. 
    rewrite H9. auto.  


-  (* labelOf v*) 
 inversion H_erasure_l. subst.
  + rewrite H_flow_l in H2. inversion H2.
  + subst.  inversion H_erasure_r. subst.
        rewrite H_flow_r in H3. inversion H3. subst. 
  ++  inversion H_typing. subst. rewrite H7. rewrite H9. 
    induction s'. pose proof (nil_flow_to_L_Label h'). rewrite H in H_flow_l.
    inversion H_flow_l. induction a. apply flow_to_simpl in H_flow_l.
    unfold erasure_H_fun_whole. fold erasure_H_fun_whole. rewrite H_flow_l.
    unfold erasure_H_fun . fold erasure_H_fun. 
    unfold return_free. fold return_free. 
    assert (return_free v = true). apply value_is_return_free. auto.  
    inversion H5. auto. rewrite H.  auto. 

-  (* unlabelOpaque e *)
 intros. 
unfold dot_free in H_dot_free. fold dot_free in H_dot_free. auto.
inversion H_valid_syntax. 
pose proof (valid_syntax_after_erasure t H1). subst.    
inversion H_erasure_l. subst.
  + rewrite H_flow_l in H5. inversion H5.
  + subst.  inversion H_erasure_r. subst.
        rewrite H_flow_r in H6. inversion H6. subst. 
  ++  inversion H_typing. subst. 
    assert (Config CT (erasure_H_fun_whole t s) (SIGMA  s'0 h'0) = Config CT (erasure_H_fun_whole e' s')  (SIGMA s'1 h'1)).
    apply IHt with h' s' h s (OpaqueLabeledTy T)  e'; auto.     
    apply erasure_H_context; auto.     auto. apply erasure_H_context; auto.

    unfold erasure_H_fun_whole.  
    induction s. 
    pose proof (nil_flow_to_L_Label h). rewrite H3 in H_flow_l. inversion H_flow_l. 

    induction a. apply flow_to_simpl in H_flow_l. rewrite H_flow_l. fold erasure_H_fun_whole.
    fold erasure_H_fun_whole in IHs. unfold erasure_H_fun. fold erasure_H_fun. 

    unfold erasure_H_fun_whole.  
    induction s'. 
    pose proof (nil_flow_to_L_Label h'). rewrite H3 in H_flow_r. inversion H_flow_r. 

    induction a. apply flow_to_simpl in H_flow_r. rewrite H_flow_r. fold erasure_H_fun_whole.
    fold erasure_H_fun_whole in IHs'. unfold erasure_H_fun. fold erasure_H_fun. 

    unfold erasure_H_fun_whole in H. fold erasure_H_fun_whole in H. 
      rewrite H_flow_l in H. rewrite H_flow_r in H.

     inversion H. subst. auto.  

     case_eq (return_free t). case_eq (return_free e'). intros. 
     pose proof (dot_erasure_dot s).      pose proof (dot_erasure_dot s').
      rewrite H9. rewrite H11. auto.  
     
     intros. pose proof (dot_erasure_dot s).  rewrite H9. 
    apply return_free_true_imply_erasure_H_fun_dot in H7. 
    rewrite H7 in H4. rewrite H9 in H4. 

    assert ((erasure_H_fun_whole (unlabelOpaque (erasure_H_fun e')) s') = dot).
    apply unlabelOpaque_erasure_dot; auto. apply valid_syntax_after_erasure; auto.  
    apply valid_syntax_preservation with CT t  (SIGMA (Labeled_frame l1 s1 :: s') h')
                  (Labeled_frame l0 s0 :: s) h (OpaqueLabeledTy T); auto. 

    apply return_free_imply_erasure_H_fun_dot  in H3. auto. 
    apply valid_syntax_preservation with CT t  (SIGMA (Labeled_frame l1 s1 :: s') h')
                  (Labeled_frame l0 s0 :: s) h (OpaqueLabeledTy T); auto. 
    rewrite H11. auto. auto.  

    intro. case_eq (return_free e'). intro. 
    apply return_free_true_imply_erasure_H_fun_dot in H7. rewrite H7 in H4. 
    assert (erasure_H_fun_whole dot s' = dot). apply dot_erasure_dot. 
    rewrite H9 in H4.  rewrite H9. 
    assert ((erasure_H_fun_whole (unlabelOpaque (erasure_H_fun t)) s) = dot).
    apply unlabelOpaque_erasure_dot; auto.  
    apply return_free_imply_erasure_H_fun_dot in H3. auto. auto. 
    rewrite H11. auto. 
    apply valid_syntax_preservation with CT t  (SIGMA (Labeled_frame l1 s1 :: s') h')
                  (Labeled_frame l0 s0 :: s) h (OpaqueLabeledTy T); auto. 
    intro. 
    
    assert (erasure_H_fun_whole (unlabelOpaque (erasure_H_fun t)) s = 
    erasure_H_fun_whole (unlabelOpaque (erasure_H_fun e')) s'). 
    apply unlabelOpaque_erasure_helper; auto. auto. 
    apply valid_syntax_preservation with CT t  (SIGMA (Labeled_frame l1 s1 :: s') h')
                  (Labeled_frame l0 s0 :: s) h (OpaqueLabeledTy T); auto. 
    rewrite H9. auto.  

-  (* (unlabelOpaque (v_opa_l t' lb)) *) 
 inversion H_erasure_l. subst.
  + rewrite H_flow_l in H2. inversion H2.
  + subst.  inversion H_erasure_r. subst.
        rewrite H_flow_r in H3. inversion H3. subst. 
  ++  inversion H_typing. subst. inversion H4. inversion H7.  subst. 
        rewrite H9. rewrite H11. 
    induction s0. pose proof (nil_flow_to_L_Label h0). rewrite H in H_flow_l.
    inversion H_flow_l. induction a. apply flow_to_simpl in H_flow_l.
    unfold erasure_H_fun_whole. fold erasure_H_fun_whole. rewrite H_flow_l.
    unfold erasure_H_fun . fold erasure_H_fun. 
    unfold return_free. fold return_free. 
    assert (return_free t' = true). apply value_is_return_free. auto.  
    inversion H6. auto. rewrite H.  auto. 

    assert (erasure_H_fun_whole t'
     (update_current_label (Labeled_frame l0 s :: s0)
        (join_label lb (current_label (SIGMA (Labeled_frame l0 s :: s0) h0)))) = dot).
    apply value_erasure_dot.     inversion H6. auto.
    apply flow_join_label with (current_label (SIGMA (Labeled_frame l0 s :: s0) h0)) lb; auto. 
    rewrite H0. 

    pose proof (dot_erasure_dot s0). rewrite H1. 
    unfold update_current_label. unfold erasure_sigma_fun. unfold erasure_stack. 
    rewrite H_flow_l. fold erasure_stack. 
    assert (flow_to
         (join_label lb (current_label (SIGMA (Labeled_frame l0 s :: s0) h0)))
         L_Label = false).
    apply flow_join_label with (current_label (SIGMA (Labeled_frame l0 s :: s0) h0)) lb; auto. 
    rewrite H5. auto. 

-  (*Assignment*) 
      inversion H_typing. inversion H5.
-  (* Assignment *) 
     inversion H_typing. inversion H5.
-  (* (FieldWrite t1 i t2) *) admit.
-  (* (FieldWrite t1 i t2) *) admit.
-  (* (FieldWrite t1 i t2) *) 
    inversion H_erasure_l. subst.
  + rewrite H_flow_l in H2. inversion H2.
  + subst.  inversion H_erasure_r. subst.
        rewrite H_flow_r in H3. inversion H3. subst. 
  ++  inversion H_typing. subst. inversion H6. inversion H12. subst. 
        induction s0. pose proof (nil_flow_to_L_Label h0). rewrite H in H_flow_l.
        inversion H_flow_l. induction a. apply flow_to_simpl in H_flow_l.
        unfold erasure_H_fun_whole. fold erasure_H_fun_whole. rewrite H_flow_l.
        unfold erasure_H_fun . fold erasure_H_fun.
        unfold return_free. fold return_free. assert (return_free t2 = true).
        apply value_is_return_free. auto. rewrite H. rewrite H10. rewrite H14.
        unfold erasure_sigma_fun.

       rename h0 into h.
        assert (erasure_heap h = erasure_heap
                                                    (update_heap_obj h o
                                                       (Heap_OBJ cls (fields_update F i t2) lb))).
        apply update_H_object_equal_erasure with CT F lb; auto. 
        apply flow_false_trans with ((current_label (SIGMA (Labeled_frame l0 s :: s0) h))); auto.
        apply flow_false_trans with ((current_label (SIGMA (Labeled_frame l0 s :: s0) h))); auto.
        rewrite <- H0.
        
        unfold erasure_stack. fold erasure_stack. rewrite H_flow_l.

        assert ( (erasure_stack s0 h) = erasure_stack s0
                (update_heap_obj h o
                     (Heap_OBJ cls (fields_update F i t2) lb))).
        apply erasure_stack_updated_heap; auto. 
        apply flow_false_trans with ((current_label (SIGMA (Labeled_frame l0 s :: s0) h))); auto.
  
        rewrite H1. auto. 
-  (*(FieldWrite t1 i t2 *) 
      inversion H_erasure_l. subst.
  + rewrite H_flow_l in H2. inversion H2.
  + subst.  inversion H_erasure_r. subst.
        rewrite H_flow_r in H3. inversion H3. subst. 
  ++  inversion H_typing. subst. inversion H7. inversion H13. subst. 
        induction s0. pose proof (nil_flow_to_L_Label h0). rewrite H in H_flow_l.
        inversion H_flow_l. induction a. apply flow_to_simpl in H_flow_l.
        unfold erasure_H_fun_whole. fold erasure_H_fun_whole. rewrite H_flow_l.
        unfold erasure_H_fun . fold erasure_H_fun.
        unfold return_free. fold return_free. assert (return_free v = true).
        apply value_is_return_free. auto. rewrite H. rewrite H9. rewrite H12.
        unfold erasure_sigma_fun.

       rename h0 into h.
        assert (erasure_heap h = erasure_heap
                                                    (update_heap_obj h o
                                                       (Heap_OBJ cls (fields_update F i v) lo))).
        apply update_H_object_equal_erasure with CT F lo; auto. 
        apply flow_false_trans with ((join_label (current_label (SIGMA (Labeled_frame l0 s :: s0) h)) lb)); auto.
        apply flow_join_label with (current_label (SIGMA (Labeled_frame l0 s :: s0) h)) lb; auto. 
        apply join_label_commutative; auto.
        apply flow_false_trans with ((join_label (current_label (SIGMA (Labeled_frame l0 s :: s0) h)) lb)); auto.
        apply flow_join_label with (current_label (SIGMA (Labeled_frame l0 s :: s0) h)) lb; auto. 
        apply join_label_commutative; auto.
        rewrite <- H0.
        
        unfold erasure_stack. fold erasure_stack. rewrite H_flow_l.


        assert ( (erasure_stack s0 h) = erasure_stack s0
                (update_heap_obj h o
                     (Heap_OBJ cls (fields_update F i v) lo))).
        apply erasure_stack_updated_heap; auto. 
        apply flow_false_trans with ((join_label (current_label (SIGMA (Labeled_frame l0 s :: s0) h)) lb)); auto.
        apply flow_join_label with (current_label (SIGMA (Labeled_frame l0 s :: s0) h)) lb; auto. 
        apply join_label_commutative; auto.
  
        rewrite H1. auto. 

-  (* if *) 
  inversion H_typing. inversion H7. inversion H18. 
-  (* if *) 
  inversion H_typing. inversion H7. inversion H18. 
-  (* Sequence *) 
 intros. 
unfold dot_free in H_dot_free. fold dot_free in H_dot_free. auto.
apply dot_free_if in H_dot_free. destruct H_dot_free. 
inversion H_valid_syntax. 
pose proof (valid_syntax_after_erasure t1 H4). subst.    
inversion H_erasure_l. subst.
  + rewrite H_flow_l in H8. inversion H8.
  + subst.  inversion H_erasure_r. subst.
        rewrite H_flow_r in H9. inversion H9. subst. 
  ++  inversion H_typing. subst. 
    assert (Config CT (erasure_H_fun_whole t1 s) (SIGMA  s'0 h'0) = Config CT (erasure_H_fun_whole s1' s')  (SIGMA s'1 h'1)).
    apply IHt1 with h' s' h s T0 s1'; auto.
    apply erasure_H_context; auto.     auto. apply erasure_H_context; auto.
    assert (return_free t2 = true).
    inversion H_valid_syntax. apply surface_syntax_is_return_free. auto. 
    inversion H10; subst; inversion H0.  

    unfold erasure_H_fun_whole.  
    induction s. 
    pose proof (nil_flow_to_L_Label h). rewrite H7 in H_flow_l. inversion H_flow_l. 

    induction a. apply flow_to_simpl in H_flow_l. rewrite H_flow_l. fold erasure_H_fun_whole.
    fold erasure_H_fun_whole in IHs. unfold erasure_H_fun. fold erasure_H_fun. 

    unfold erasure_H_fun_whole.  
    induction s'. 
    pose proof (nil_flow_to_L_Label h'). rewrite H7 in H_flow_r. inversion H_flow_r. 

    induction a. apply flow_to_simpl in H_flow_r. rewrite H_flow_r. fold erasure_H_fun_whole.
    fold erasure_H_fun_whole in IHs'. unfold erasure_H_fun. fold erasure_H_fun. 


    unfold erasure_H_fun_whole in H2. fold erasure_H_fun_whole in H2. 
      rewrite H_flow_l in H2. rewrite H_flow_r in H2.

     inversion H2. subst. auto.  

     case_eq (return_free t1). case_eq (return_free s1'). intros. 
     pose proof (dot_erasure_dot s).      pose proof (dot_erasure_dot s').
     rewrite H3. 
     rewrite H14. rewrite H17. auto.  
     
     intros. pose proof (dot_erasure_dot s). rewrite H3.  rewrite H14. 
    apply return_free_true_imply_erasure_H_fun_dot in H11. 
    rewrite H11 in H10. rewrite H14 in H10.

    assert ((erasure_H_fun_whole (Sequence (erasure_H_fun s1') t2) s') = dot).
    apply sequence_erasure_dot; auto. apply valid_syntax_after_erasure; auto.  
    apply valid_syntax_preservation with CT t1  (SIGMA (Labeled_frame l1 s1 :: s') h')
                  (Labeled_frame l0 s0 :: s) h T0; auto. 

    apply return_free_imply_erasure_H_fun_dot  in H7. auto. 
    apply valid_syntax_preservation with CT t1  (SIGMA (Labeled_frame l1 s1 :: s') h')
                  (Labeled_frame l0 s0 :: s) h T0; auto. 
    rewrite H17. auto. auto.  

    intro. rewrite H3.  case_eq (return_free s1'). intro. 
    apply return_free_true_imply_erasure_H_fun_dot in H11. rewrite H11 in H10. 
    assert (erasure_H_fun_whole dot s' = dot). apply dot_erasure_dot. 
    rewrite H14 in H10.  rewrite H14. 
    assert ((erasure_H_fun_whole (Sequence (erasure_H_fun t1) t2) s) = dot).
    apply sequence_erasure_dot; auto.  
    apply return_free_imply_erasure_H_fun_dot in H7. auto. auto. 
    rewrite H17. auto. 
    apply valid_syntax_preservation with CT t1  (SIGMA (Labeled_frame l1 s1 :: s') h')
                  (Labeled_frame l0 s0 :: s) h T0; auto. 
    intro. 
    
    assert (erasure_H_fun_whole (Sequence (erasure_H_fun t1) t2) s = 
    erasure_H_fun_whole (Sequence (erasure_H_fun s1') t2) s'). 
    apply Sequence_erasure_helper; auto. auto. 
    apply valid_syntax_preservation with CT t1  (SIGMA (Labeled_frame l1 s1 :: s') h')
                  (Labeled_frame l0 s0 :: s) h T0; auto. 
    rewrite H14. auto.
+  inversion H4; subst; inversion H0. 

- (*sequence *) 
    inversion H_erasure_l. subst.
  + rewrite H_flow_l in H3. inversion H3.
  + subst.  inversion H_erasure_r. subst.
        rewrite H_flow_r in H4. inversion H4. subst.
  ++ induction s'. pose proof (nil_flow_to_L_Label h'). rewrite H in H_flow_l.
        inversion H_flow_l. induction a. apply flow_to_simpl in H_flow_l.
        unfold erasure_H_fun_whole. fold erasure_H_fun_whole. rewrite H_flow_l.
        unfold erasure_H_fun. fold erasure_H_fun. assert (return_free t1 = true).
        apply value_is_return_free. auto. rewrite H. fold erasure_H_fun.
        case_eq (return_free t'). intro.  assert ( erasure_H_fun t' = dot).
        apply return_free_true_imply_erasure_H_fun_dot. auto. 
        inversion H_valid_syntax. apply surface_syntax_is_valid_syntax. auto. auto.
        auto. rewrite H2. rewrite H8. rewrite H10. auto.
        intro.  rewrite H8. rewrite H10. auto.

- (*return e*) 
 intros. 
unfold dot_free in H_dot_free. fold dot_free in H_dot_free. auto.
inversion H_valid_syntax. 
pose proof (valid_syntax_after_erasure t H1). subst.    
inversion H_erasure_l. subst.
  + rewrite H_flow_l in H5. inversion H5.
  + subst.  inversion H_erasure_r. subst.
        rewrite H_flow_r in H6. inversion H6. subst. 
  ++  inversion H_typing. subst. 
    assert (Config CT (erasure_H_fun_whole t s) (SIGMA  s'0 h'0) = Config CT (erasure_H_fun_whole e' s')  (SIGMA s'1 h'1)).
    apply IHt with h' s' h s T0  e'; auto.     
    apply erasure_H_context; auto.     auto. apply erasure_H_context; auto.  inversion H. subst.

    induction s.
    pose proof (nil_flow_to_L_Label h). rewrite H4 in H_flow_l. inversion H_flow_l. 

    induction s'.
    pose proof (nil_flow_to_L_Label h'). rewrite H4 in H_flow_r. inversion H_flow_r.
    induction a. induction a0. 

    apply flow_to_simpl in H_flow_r. apply flow_to_simpl in H_flow_l. 

    unfold erasure_H_fun_whole in H7. fold erasure_H_fun_whole in H7. 
      rewrite H_flow_l in H7. rewrite H_flow_r in H7.

    case_eq (return_free t). case_eq (return_free e'). intros. 
     pose proof (dot_erasure_dot s).      pose proof (dot_erasure_dot s').

     assert (s = s'). apply return_free_equal_stack with t CT h l0 s0 l1 s1 h' e' T0; auto. 
     rewrite H14. unfold erasure_H_fun_whole. fold erasure_H_fun_whole. 
      rewrite H_flow_l. rewrite H_flow_r. unfold erasure_H_fun.  rewrite H4. rewrite H8. auto.
    
     intros. pose proof (dot_erasure_dot s). 
     assert ( (Labeled_frame l0 s0 :: s) = s'). 
    apply return_free_change_imply_method_call with t CT h l1 s1 h' e' T0; auto.  
    apply return_free_true_imply_erasure_H_fun_dot in H8. 
    rewrite H8 in H7. rewrite <- H13 in H7.
    rewrite <- H11 in H7. unfold erasure_H_fun_whole in H7. rewrite H_flow_l in H7. 
    fold erasure_H_fun_whole in H7. rewrite H11 in H7. rewrite H11 in H7.
    unfold erasure_H_fun_whole. fold erasure_H_fun_whole. rewrite H_flow_l. 

    case_eq (return_free (erasure_H_fun e')). intro. apply return_free_true_imply_erasure_H_fun_dot in H14. 
    unfold erasure_H_fun. fold erasure_H_fun.
    apply erasure_H_fun_imply_return_free in H8. 
     rewrite H8. auto. rewrite H4. rewrite H_flow_r. rewrite <- H13. 
    unfold erasure_H_fun_whole. rewrite H_flow_l. fold erasure_H_fun_whole. 
    unfold erasure_H_fun. fold erasure_H_fun. apply erasure_H_fun_imply_return_free in H14.  rewrite H14. auto.
  apply valid_syntax_after_erasure. auto.
    apply valid_syntax_preservation with CT t  (SIGMA (Labeled_frame l1 s1 :: s') h')
                  (Labeled_frame l0 s0 :: s) h T0; auto. auto.
    apply valid_syntax_after_erasure. auto.
    apply valid_syntax_preservation with CT t  (SIGMA (Labeled_frame l1 s1 :: s') h')
                  (Labeled_frame l0 s0 :: s) h T0; auto. 

    assert (return_free (erasure_H_fun e') = true).
    apply return_free_change_imply_return_free with t CT (Labeled_frame l0 s0 :: s) h l1 s1 s' h' T0; auto.
    apply erasure_H_fun_imply_return_free in H8. auto. auto. 
     intro. rewrite H14 in H15. inversion H15. auto. 

    intro.  fold erasure_H_fun_whole. 

    case_eq (return_free e'). intros.
    apply return_free_true_imply_erasure_H_fun_dot in H8. rewrite H8 in H7. 
    pose proof (dot_erasure_dot s'). rewrite H11 in H7. 
    
    assert ((return_free (erasure_H_fun t)) = true).
    apply return_free_change_imply_return_free_false2true with CT (Labeled_frame l0 s0 :: s)
                h (Labeled_frame l1 s1 :: s') h'  e' T0; auto.  admit. 

    unfold erasure_H_fun_whole. fold erasure_H_fun_whole. rewrite H_flow_l. rewrite H_flow_r.
    unfold erasure_H_fun. fold erasure_H_fun. rewrite H4. 
    apply erasure_H_fun_imply_return_free in H8. rewrite H8. induction s. 

    unfold erasure_H_fun_whole in H7.     apply erasure_H_fun_imply_return_free in H7. 
    rewrite H7 in H4. inversion H4. 
    auto. induction a.     case_eq ( flow_to l2 L_Label). intro.
    unfold erasure_H_fun_whole in H7. fold erasure_H_fun_whole in H7.  rewrite H14 in H7. 
    apply erasure_H_fun_imply_return_free in H7.  rewrite H7 in H4. inversion H4. auto.
 
    intro. unfold erasure_H_fun_whole in H7. rewrite H14 in H7.  fold erasure_H_fun_whole in H7. 
    unfold erasure_H_fun_whole. fold erasure_H_fun_whole. rewrite H14. 
    unfold erasure_H_fun. fold erasure_H_fun. rewrite H13. 
    assert (Labeled_frame l2 s2 :: s = (Labeled_frame l1 s1 :: s')). apply return_free_change_imply_return with 
        t CT h l0 s0 h' e' T0; auto.  inversion H15. auto. 
    apply valid_syntax_preservation with CT t (SIGMA (Labeled_frame l1 s1 :: s') h')
                  (Labeled_frame l0 s0 :: s) h T0; auto.
    apply valid_syntax_preservation with CT t (SIGMA (Labeled_frame l1 s1 :: s') h')
                  (Labeled_frame l0 s0 :: s) h T0; auto. 

    intro. 
    unfold erasure_H_fun_whole. rewrite H_flow_l. rewrite H_flow_r. fold erasure_H_fun_whole.


Lemma return_erasure_helper_revised : forall t e' s s', 
    valid_syntax t -> valid_syntax e' -> s <> nil -> s' <> nil ->
    erasure_H_fun_whole (erasure_H_fun t) s = erasure_H_fun_whole (erasure_H_fun e') s' ->
    return_free t = false -> return_free e' = false ->
    (erasure_H_fun_whole (erasure_H_fun (Return t)) s)  = 
    (erasure_H_fun_whole (erasure_H_fun (Return e')) s').
  Proof. intros. generalize dependent t. generalize dependent e'. 
    induction s.  intros. intuition. 

    induction s'. intuition. 

   
    
    

Lemma return_erasure_helper_revised : forall t e' s s' l0 s0 l1 s1, 
    valid_syntax t -> valid_syntax e' ->
    flow_to l0 L_Label = false ->    flow_to l1 L_Label = false ->
    erasure_H_fun_whole (erasure_H_fun t) s = erasure_H_fun_whole (erasure_H_fun e') s' ->
    return_free t = false -> return_free e' = false ->
    erasure_H_fun_whole (Return t) (Labeled_frame l0 s0 :: s) = 
    erasure_H_fun_whole (Return e') (Labeled_frame l1 s1 :: s').
Proof. intros. generalize dependent t. generalize dependent e'. generalize dependent s'.
    induction s.  intros. generalize dependent e'.  generalize dependent t. induction s'.

    intros. admit. admit. 
    induction s'. admit.  induction a. induction a0. intros.  
    case_eq (flow_to l2 L_Label). intro. 



 unfold erasure_H_fun_whole in H3. rewrite H3. unfold erasure_H_fun_whole. 
    fold erasure_H_fun_whole.  rewrite H1. rewrite H2. auto.

    intros. unfold erasure_H_fun_whole in H3. induction a. case_eq (flow_to l2 L_Label). intro.
    rewrite H6 in H3. unfold erasure_H_fun_whole. rewrite H6. rewrite H3. auto.
    rewrite H1. rewrite H2. auto. 

    intros.   rewrite H6 in H3. fold erasure_H_fun_whole in H3.
    unfold erasure_H_fun_whole.  rewrite H6. fold erasure_H_fun_whole. 
    unfold erasure_H_fun. fold erasure_H_fun. rewrite H1. rewrite H2.  rewrite H4. rewrite H5. 
    case_eq (return_free (erasure_H_fun e')) . intro. 
    induction s'. unfold erasure_H_fun_whole in H3. rewrite <-H3 in H7. rewrite H4 in H7. inversion H7. 
    induction a. case_eq (flow_to l3 L_Label).  unfold erasure_H_fun_whole in H3. 
    intro. rewrite H8 in H3. rewrite <-H3 in H7. rewrite H4 in H7. inversion H7. 
    
    intro. unfold erasure_H_fun_whole in H3. rewrite H8 in H3. fold erasure_H_fun_whole in H3.
     apply return_free_true_imply_erasure_H_fun_dot in H7. rewrite H7 in H3.  
    pose proof (dot_erasure_dot s'). rewrite H9 in H3. rewrite H3 in H4. inversion H4. 
     apply valid_syntax_after_erasure. auto. 

    intro.
    assert (erasure_H_fun_whole (Return  t)
         (Labeled_frame l0 s0 :: nil) =
               erasure_H_fun_whole (Return (erasure_H_fun e'))
                 (Labeled_frame l1 s1 :: s')).
    apply IHs'; auto. apply valid_syntax_after_erasure. auto.
    unfold erasure_H_fun_whole in H8. rewrite H1 in H8. rewrite H2 in H8.
    fold erasure_H_fun_whole in H8. rewrite <- H8. unfold erasure_H_fun. fold erasure_H_fun. 
    rewrite H4. auto. 

    intros.  generalize dependent e'.  generalize dependent t. induction s'.
    intros. induction a.  unfold erasure_H_fun_whole in H3. 
    case_eq (flow_to l2 L_Label).  intro.  rewrite H6 in H3.  unfold erasure_H_fun_whole. 
    fold erasure_H_fun_whole.  rewrite H1. rewrite H2. rewrite H6. rewrite H3. auto. 

    intro. rewrite H6 in H3. fold erasure_H_fun_whole in H3. 

    case_eq (return_free (erasure_H_fun t)). intro. 
    assert ((erasure_H_fun (erasure_H_fun t)) = dot). 
    apply return_free_true_imply_erasure_H_fun_dot; auto. 
    apply valid_syntax_after_erasure. auto.  
    induction s. unfold erasure_H_fun_whole in H3. rewrite <-H3 in H5. 
    rewrite H7 in H5. inversion H5. 
    induction a. case_eq (flow_to l3 L_Label).  unfold erasure_H_fun_whole in H3. 
    intro. rewrite H9 in H3. rewrite <-H3 in H5.     rewrite H7 in H5. inversion H5. 
    intro.      unfold erasure_H_fun_whole in H3. rewrite H9 in H3. fold erasure_H_fun_whole in H3.
    rewrite H8 in H3. pose proof (dot_erasure_dot s). rewrite H10 in H3. rewrite <- H3 in H5. inversion H5. 

    intro. 
    assert (erasure_H_fun_whole (Return (erasure_H_fun  t))
        (Labeled_frame l0 s0 :: s) =
      erasure_H_fun_whole (Return e')
        (Labeled_frame l1 s1 :: nil)).
    apply IHs; auto. apply valid_syntax_after_erasure. auto.
    rewrite <- H8. unfold  erasure_H_fun_whole. rewrite H1.  rewrite H6. 
    
    fold erasure_H_fun_whole.  remember (erasure_H_fun_whole
  (erasure_H_fun (Return (erasure_H_fun t))) s) as tmp. 
    unfold erasure_H_fun. fold erasure_H_fun. rewrite H4.   auto. 


    intros.  induction a.    case_eq (flow_to l2 L_Label).  intro. 
    assert (erasure_H_fun_whole (Return t )
  (Labeled_frame l0 s0 :: Labeled_frame l2 s2 :: s)  = (erasure_H_fun (Return t ))). 
    unfold erasure_H_fun_whole.  rewrite H6. rewrite H1. auto. 
      
    unfold erasure_H_fun_whole in H3. rewrite H6 in H3. fold erasure_H_fun_whole in H3. 
    unfold erasure_H_fun_whole. rewrite H6.   fold erasure_H_fun_whole. rewrite H1. rewrite H2. 
    induction a0. case_eq (flow_to l3 L_Label). intro. rewrite H8 in H3.  rewrite H3. auto .
    intro. rewrite H8 in H3. rewrite <- H7. unfold erasure_H_fun. fold erasure_H_fun. 
    case_eq (return_free (erasure_H_fun e')). intro. 
   apply return_free_true_imply_erasure_H_fun_dot in H9. induction s'. 
   unfold erasure_H_fun_whole in H3. rewrite H3 in H4. apply erasure_H_fun_imply_return_free in H9.
   rewrite H9 in H4. inversion H4. apply valid_syntax_after_erasure. auto. 
   induction a. case_eq (flow_to l4 L_Label).  unfold erasure_H_fun_whole in H3. 
    intro. rewrite H10 in H3. rewrite H3 in H4.  apply erasure_H_fun_imply_return_free in H9.
   rewrite H9 in H4. inversion H4. apply valid_syntax_after_erasure. auto. 
    
    intro. unfold erasure_H_fun_whole in H3.  rewrite H10 in H3. fold erasure_H_fun_whole in H3.  
     rewrite H9 in H3. pose proof (dot_erasure_dot s'). rewrite H11 in H3. rewrite H3 in H4. 
    unfold return_free in H4. inversion H4. apply valid_syntax_after_erasure. auto. 

    intro. 
    assert (erasure_H_fun_whole (Return  t)
         (Labeled_frame l0 s0 :: Labeled_frame l2 s2 :: s) =
       erasure_H_fun_whole (Return (erasure_H_fun ( e')))
         (Labeled_frame l1 s1 :: s')).
    apply IHs'; auto. apply valid_syntax_after_erasure. auto. rewrite <- H3. 
    unfold erasure_H_fun_whole. rewrite H6. auto. 


----


rewrite H10. 
    remember (erasure_H_fun_whole
  (erasure_H_fun (Return (erasure_H_fun (erasure_H_fun e')))) s') as tmp.
    unfold erasure_H_fun_whole. fold erasure_H_fun_whole. rewrite H2. auto. 

    intro. induction a0.
unfold erasure_H_fun_whole in H3. rewrite H6 in H3. fold erasure_H_fun_whole in H3. 
 case_eq (flow_to l3 L_Label). intro. rewrite H7 in H3.  
    case_eq (return_free (erasure_H_fun t)). intro.

     apply return_free_true_imply_erasure_H_fun_dot in H8. rewrite H8 in H3. 
    pose proof (dot_erasure_dot s). rewrite H9 in H3. assert (erasure_H_fun e' = dot). auto. 
    apply erasure_H_fun_imply_return_free in H10. rewrite H10 in H5. inversion H5. auto. 
    auto. apply valid_syntax_after_erasure. auto. 

    intro. 
      assert (
      erasure_H_fun_whole (Return (erasure_H_fun (erasure_H_fun t)))
        (Labeled_frame l0 s0 :: s) =
      erasure_H_fun_whole (Return (erasure_H_fun e'))
        (Labeled_frame l1 s1 :: Labeled_frame l3 s3 :: s')).
    apply IHs; auto. apply valid_syntax_after_erasure. auto.

    unfold erasure_H_fun_whole. rewrite H7. fold erasure_H_fun_whole. auto. 
    rewrite <- H9. 
    unfold erasure_H_fun_whole. rewrite H1. rewrite H6. fold erasure_H_fun_whole. 

    remember (erasure_H_fun_whole
  (erasure_H_fun (Return (erasure_H_fun (erasure_H_fun t)))) s) as tmp.
    unfold erasure_H_fun. fold erasure_H_fun.  rewrite H8. auto.  
 
    intro. rewrite H7 in H3. unfold  erasure_H_fun_whole.  rewrite H1. rewrite H6. 
    rewrite H7. fold erasure_H_fun_whole. rewrite H2.  

    unfold erasure_H_fun. fold erasure_H_fun. 
    case_eq (return_free (erasure_H_fun t)). intro. 
    apply return_free_true_imply_erasure_H_fun_dot in H8. rewrite H8 in H3. 
    case_eq (return_free (erasure_H_fun e')). intro. 
    pose proof (dot_erasure_dot s). pose proof (dot_erasure_dot s'). 
    unfold erasure_H_fun. unfold return_free.     rewrite H10. rewrite H11. auto. 

    intro.  pose proof (dot_erasure_dot s). rewrite H10 in H3. 
    assert (erasure_H_fun_whole
  (erasure_H_fun (Return (erasure_H_fun (erasure_H_fun e')))) s' = dot).
    apply return_erasure_dot_helper; auto. rewrite H11. 
  unfold erasure_H_fun. unfold return_free. rewrite H10. auto. 
     apply valid_syntax_after_erasure. auto.

    intro. 
    case_eq (return_free (erasure_H_fun e')). intro. 
    apply return_free_true_imply_erasure_H_fun_dot in H9. rewrite H9 in H3. 
    pose proof (dot_erasure_dot s). pose proof (dot_erasure_dot s'). rewrite H11 in H3. 

   assert (erasure_H_fun_whole (erasure_H_fun (Return (erasure_H_fun (erasure_H_fun t)))) s = dot).
   apply return_erasure_dot_helper; auto. rewrite H12. unfold erasure_H_fun. unfold return_free. 
    rewrite H11. auto.      apply valid_syntax_after_erasure. auto.
   intro. 
   assert (erasure_H_fun_whole (Return (erasure_H_fun t))
               (Labeled_frame l0 s0 :: Labeled_frame l2 s2 :: s) =
             erasure_H_fun_whole (Return (erasure_H_fun (erasure_H_fun e')))
               (Labeled_frame l1 s1 :: s')).
  apply IHs'; auto.   apply valid_syntax_after_erasure. auto. 
  unfold erasure_H_fun_whole. fold erasure_H_fun_whole.  rewrite H6.  auto. 
  unfold erasure_H_fun_whole in H10. rewrite H6 in H10. rewrite H1 in H10. 
  fold erasure_H_fun_whole in H10. rewrite H2 in H10. 
  
  case_eq (return_free (erasure_H_fun t)). intro. rewrite H11 in H8. inversion H8. 
  intro. 
  rewrite <- H10. remember (erasure_H_fun_whole
  (erasure_H_fun (Return (erasure_H_fun (erasure_H_fun t)))) s) as tmp. 
   unfold erasure_H_fun. fold erasure_H_fun. rewrite H11. auto. 
Qed.  














    intro. assert ((erasure_H_fun_whole (Return (erasure_H_fun t)) (Labeled_frame l0 s0 :: s)) 
        = (erasure_H_fun_whole (Return (erasure_H_fun e'))  (Labeled_frame l1 s1 :: s'))).

    apply return_erasure_helper; auto.   
    apply valid_syntax_preservation with CT t  (SIGMA (Labeled_frame l1 s1 :: s') h')
                  (Labeled_frame l0 s0 :: s) h T0; auto. 
    rewrite H11. auto.   

    intro. assert ((erasure_H_fun_whole (Return (erasure_H_fun t)) s) 
        = (erasure_H_fun_whole (Return (erasure_H_fun e')) s')).

    apply return_erasure_helper; auto.   
    apply valid_syntax_preservation with CT t  (SIGMA (Labeled_frame l1 s1 :: s') h')
                  (Labeled_frame l0 s0 :: s) h T0; auto. 
    rewrite H13. auto.   


---------------

    unfold erasure_H_fun_whole.  
    induction s.
    pose proof (nil_flow_to_L_Label h). rewrite H4 in H_flow_l. inversion H_flow_l. 

    induction a. apply flow_to_simpl in H_flow_l. rewrite H_flow_l. fold erasure_H_fun_whole.
    fold erasure_H_fun_whole in IHs. unfold erasure_H_fun. fold erasure_H_fun. 

    unfold erasure_H_fun_whole.   
        generalize dependent e'. induction s'.
 intros.  
    pose proof (nil_flow_to_L_Label h'). rewrite H4 in H_flow_r. inversion H_flow_r. 

    induction a. apply flow_to_simpl in H_flow_r. rewrite H_flow_r. fold erasure_H_fun_whole.
    fold erasure_H_fun_whole in IHs'. unfold erasure_H_fun. fold erasure_H_fun. 

    intros. unfold erasure_H_fun_whole in H7. fold erasure_H_fun_whole in H7. 
      rewrite H_flow_l in H7. rewrite H_flow_r in H7.

     inversion H. rewrite H_flow_l in H8. rewrite H_flow_r in H8. subst. auto.  

     case_eq (return_free t). case_eq (return_free e'). intros. 
     pose proof (dot_erasure_dot s).      pose proof (dot_erasure_dot s').

     assert (s = s'). apply return_free_equal_stack with t CT h l0 s0 l1 s1 h' e' T0; auto. 
     rewrite H15. auto.  
    
     intros. pose proof (dot_erasure_dot s). 
     assert ( (Labeled_frame l0 s0 :: s) = s'). 
    apply return_free_change_imply_method_call with t CT h l1 s1 h' e' T0; auto.  
    apply return_free_true_imply_erasure_H_fun_dot in H11. 
    rewrite H11 in H8. rewrite H13 in H8.
    rewrite <- H14 in H8. unfold erasure_H_fun_whole in H8. rewrite H_flow_l in H8. 
    fold erasure_H_fun_whole in H8. rewrite <- H14. unfold erasure_H_fun_whole.
    fold erasure_H_fun_whole. rewrite H_flow_l. 

    case_eq (return_free (erasure_H_fun e')). intro. apply return_free_true_imply_erasure_H_fun_dot in H15. 
    unfold erasure_H_fun. fold erasure_H_fun. apply erasure_H_fun_imply_return_free in H15. 
     rewrite H15. auto.  apply valid_syntax_after_erasure. auto.
    apply valid_syntax_preservation with CT t  (SIGMA (Labeled_frame l1 s1 :: s') h')
                  (Labeled_frame l0 s0 :: s) h T0; auto. 
    apply valid_syntax_after_erasure. auto.
    apply valid_syntax_preservation with CT t  (SIGMA (Labeled_frame l1 s1 :: s') h')
                  (Labeled_frame l0 s0 :: s) h T0; auto. 

    assert (return_free (erasure_H_fun e') = true).
    apply return_free_change_imply_return_free with t CT (Labeled_frame l0 s0 :: s) h l1 s1 s' h' T0; auto.
    apply erasure_H_fun_imply_return_free in H11. auto. auto. 
     intro. rewrite H15 in H16. inversion H16. auto. 

    intro.  fold erasure_H_fun_whole. 

    case_eq (return_free e'). intros.
    apply return_free_true_imply_erasure_H_fun_dot in H11. rewrite H11 in H8. 
    pose proof (dot_erasure_dot s'). rewrite H13 in H8. 
    
    induction s. unfold erasure_H_fun_whole in H8. 
    apply erasure_H_fun_imply_return_free in H8.  rewrite H8 in H4. inversion H4. 
    auto. induction a. unfold erasure_H_fun_whole in H8. 
    case_eq ( flow_to l2 L_Label). intro. rewrite H14 in H8. 
    apply erasure_H_fun_imply_return_free in H8.  rewrite H8 in H4. inversion H4. auto. 
    intro. rewrite H14 in H8.  fold erasure_H_fun_whole in H8. 
    unfold erasure_H_fun_whole. fold erasure_H_fun_whole. rewrite H14. 
    unfold erasure_H_fun. fold erasure_H_fun. 
    assert ((return_free (erasure_H_fun t)) = true).
    apply return_free_change_imply_return_free_false2true with CT (Labeled_frame l0 s0 :: Labeled_frame l2 s2 :: s)
                h (Labeled_frame l1 s1 :: s') h'  e' T0; auto. 
    apply erasure_H_fun_imply_return_free in H11. auto.
    apply valid_syntax_preservation with CT t  (SIGMA (Labeled_frame l1 s1 :: s') h')
                  (Labeled_frame l0 s0 :: Labeled_frame l2 s2 :: s) h T0; auto. 
    rewrite H15. 
    assert (Labeled_frame l2 s2 :: s = (Labeled_frame l1 s1 :: s')). apply return_free_change_imply_return with 
        t CT h l0 s0 h' e' T0; auto.  
        apply erasure_H_fun_imply_return_free in H11. auto.
    apply valid_syntax_preservation with CT t  (SIGMA (Labeled_frame l1 s1 :: s') h')
                  (Labeled_frame l0 s0 :: Labeled_frame l2 s2 :: s) h T0; auto. 

     inversion H16. auto.
        apply valid_syntax_preservation with CT t  (SIGMA (Labeled_frame l1 s1 :: s') h')
                  (Labeled_frame l0 s0 :: s) h T0; auto. 

    intro. assert ((erasure_H_fun_whole (Return (erasure_H_fun t)) s) 
        = (erasure_H_fun_whole (Return (erasure_H_fun e')) s')).

    apply return_erasure_helper; auto.   
    apply valid_syntax_preservation with CT t  (SIGMA (Labeled_frame l1 s1 :: s') h')
                  (Labeled_frame l0 s0 :: s) h T0; auto. 
    rewrite H13. auto.   

- (* return v*) inversion H5. inversion H9. subst.
 intros. unfold dot_free in H_dot_free. fold dot_free in H_dot_free. 
  inversion H_erasure_l. subst.
  + rewrite H_flow_l in H2. inversion H2.
  + subst.  inversion H_erasure_r. subst.
        rewrite H_flow_r in H3. inversion H3. subst. 
  ++  inversion H_typing. subst. induction lsf. 
    apply flow_to_simpl in H_flow_l. unfold erasure_H_fun_whole. 
    rewrite H_flow_l. fold erasure_H_fun_whole.
    rewrite H13. unfold get_stack_label. unfold erasure_H_fun.
    fold erasure_H_fun. assert (return_free t = true). apply value_is_return_free. auto.
    rewrite H.
    induction s'0. intuition. induction a. unfold erasure_H_fun_whole.
    apply flow_to_simpl in H_flow_r. rewrite H_flow_r. fold  erasure_H_fun_whole.
    unfold erasure_H_fun. fold erasure_H_fun. rewrite H.
    unfold return_free. rewrite H11. unfold erasure_sigma_fun. fold erasure_sigma_fun.
    remember (Labeled_frame l1 s0 :: s'0) as s''.
    unfold erasure_stack. fold erasure_stack. rewrite H_flow_l. auto.
Qed.



Lemma simulation_H_revised : forall CT t t0 t' t0' s h s' h' sigma_l_e sigma_r_e,
      dot_free t = true ->
      valid_syntax t ->
      forall T, has_type CT empty_context h t T -> 
      field_wfe_heap CT h -> wfe_heap CT h -> wfe_stack CT h s ->
      flow_to (current_label (SIGMA s h)) L_Label = false ->
      flow_to (current_label (SIGMA s' h')) L_Label = false ->
      Config CT t (SIGMA s h) ==> Config CT t' (SIGMA s' h') ->
      (Config CT t (SIGMA s h)) =e=> (Config CT t0 sigma_l_e) ->
      (Config CT t' (SIGMA s' h')) =e=> (Config CT t0' sigma_r_e) ->
         (Config CT t0 sigma_l_e) = (Config CT t0' sigma_r_e) 
              \/ (Config CT t0 sigma_l_e) ==l> (Config CT t0' sigma_r_e).
Proof. 
  intros CT t t0 t' t0' s h s' h' sigma_l_e sigma_r_e. intro H_dot_free. intro H_valid_syntax. 
  intro T. intro H_typing. intro H_wfe_fields. 
  intro H_wfe_heap. intro H_wfe_stack. 
  intro H_flow_l.   intro H_flow_r. intro H_reduction. 
  (*intro H_erasure_sigma_l.  *) intro H_erasure_l. intro H_erasure_r.   
  
generalize dependent t'. 
  generalize dependent t0.
  generalize dependent t0'.
  generalize dependent T.
    generalize dependent sigma_l_e.      generalize dependent sigma_r_e. 
    generalize dependent s.      generalize dependent h.
    generalize dependent s'.      generalize dependent h'.
induction t; intros; try (inversion H_reduction; subst).
- (* (Tvar i) *) inversion H_typing. inversion H3. 
- (*(FieldAccess t i)*) intros. 
unfold dot_free in H_dot_free. fold dot_free in H_dot_free. auto.
inversion H_erasure_l. subst.
  + rewrite H_flow_l in H3. inversion H3.
  + subst.  inversion H_erasure_r. subst.
        rewrite H_flow_r in H4. inversion H4. subst. 
  +++  inversion H_typing. subst. 
    assert (Config CT (erasure_H_fun t) (SIGMA  s'0 h'0) = Config CT (erasure_H_fun e')  (SIGMA s'1 h'1) 
      \/ (Config CT (erasure_H_fun t) (SIGMA  s'0 h'0) ==l> Config CT (erasure_H_fun e')  (SIGMA s'1 h'1))). 
    apply IHt with h' s' h s (classTy clsT)  e'; auto.     
    inversion H_valid_syntax. auto. 
    apply erasure_H_context; auto.     auto. apply erasure_H_context; auto.

    destruct H.
    assert (return_free t= return_free e'). 
    apply erasure_H_fun_equal_return_free. inversion H_valid_syntax. auto.  
    apply valid_syntax_preservation with CT t (SIGMA s' h') s h (classTy clsT); auto. 
    inversion H_valid_syntax. auto.   inversion H. auto.
    unfold erasure_H_fun. fold erasure_H_fun. subst. 
    case_eq (return_free t). intro.  rewrite H6 in H1. rewrite <- H1. 
    left. inversion H. auto.  
    intro. rewrite H6 in H1. rewrite <- H1. inversion H. left. auto. 
     (*l reduction*)    
    inversion H. induction c2.
  ++++ assert (CT = c). apply ct_consist with (erasure_H_fun t)  t0 (SIGMA s'0 h'0) s0; auto. 
    subst. rename c into CT.    right.  unfold erasure_H_fun. fold erasure_H_fun. subst. 
    case_eq (return_free t). intro. assert ((erasure_H_fun t) = dot). 
    apply return_free_true_imply_erasure_H_fun_dot; auto. inversion H_valid_syntax; auto. 
    rewrite H9 in H1. inversion H1. 
    
    intro. case_eq (return_free e'). 
    intro.  assert (erasure_H_fun e' = dot).
    apply  return_free_true_imply_erasure_H_fun_dot; auto. 
    apply valid_syntax_preservation with CT t (SIGMA s' h') s h (classTy clsT); auto. 
    inversion H_valid_syntax. auto. rewrite H11 in H6. 
    assert (Config CT (FieldAccess (erasure_H_fun t) i) (SIGMA s'0 h'0) ==> 
            Config CT (FieldAccess t0 i)  s0 ).
    apply ST_fieldRead1; auto. induction s0. 
    assert ((flow_to (current_label ((SIGMA s'1 h'1))) L_Label = flow_to (current_label (SIGMA s0 h0)) L_Label )).
    apply erasure_preserve_context with t0 dot CT; auto. 
    assert ( flow_to (current_label (SIGMA s'1 h'1)) L_Label = flow_to (current_label (SIGMA s' h')) L_Label).
    apply erasure_sigma_preserve_context; auto. rewrite H_flow_r in H15. rewrite H15 in H14. 
    inversion H6. subst. rewrite H19 in H14. inversion H14. subst. 

    assert (Config CT (FieldAccess t0 i) (SIGMA s0 h0) =e=> Config CT dot (SIGMA s'1 h'1)).
    apply erasure_H_context; auto. unfold erasure_H_fun. fold erasure_H_fun. 
    assert (return_free t0 = true). apply  erasure_H_fun_imply_return_free; auto. 

    apply valid_syntax_preservation_erasured with CT (erasure_H_fun t) s h (SIGMA s0 h0) (classTy clsT). auto. 
    apply valid_syntax_preservation_erasure_H; inversion H_valid_syntax; auto. 
    apply typing_preservation_erasure; auto. auto.  rewrite <- H8. auto. 

    rewrite H16. auto. apply L_reduction with (Config CT (FieldAccess t0 i) (SIGMA s0 h0)); auto. 
  
    intro.  unfold erasure_H_fun. fold erasure_H_fun. subst. 
    assert (Config CT (FieldAccess (erasure_H_fun t) i) (SIGMA s'0 h'0) ==> 
            Config CT (FieldAccess t0 i)  s0 ).
    apply ST_fieldRead1; auto. induction s0. 
    assert ((flow_to (current_label ((SIGMA s'1 h'1))) L_Label = flow_to (current_label (SIGMA s0 h0)) L_Label )).
    apply erasure_preserve_context with t0 (erasure_H_fun e') CT; auto. 
    assert ( flow_to (current_label (SIGMA s'1 h'1)) L_Label = flow_to (current_label (SIGMA s' h')) L_Label).
    apply erasure_sigma_preserve_context; auto. rewrite H_flow_r in H14. rewrite H14 in H12.  
    inversion H6. subst. rewrite H18 in H12. inversion H12. subst. 

    assert (Config CT (FieldAccess t0 i) (SIGMA s0 h0) =e=> Config CT (FieldAccess (erasure_H_fun e') i)  (SIGMA s'1 h'1)).
    apply erasure_H_context; auto. unfold erasure_H_fun. fold erasure_H_fun.
    apply return_free_imply_erasure_H_fun_dot in H9. rewrite H23 in H9.  
    assert (return_free t0 = false). apply  erasure_H_fun_imply_return_free_false; auto.

    apply valid_syntax_preservation_erasured with CT (erasure_H_fun t) s h (SIGMA s0 h0) (classTy clsT). auto. 
    apply valid_syntax_preservation_erasure_H; inversion H_valid_syntax; auto. 
    apply typing_preservation_erasure; auto. auto.  rewrite <- H8. auto. 
    
    rewrite H15. rewrite H23. auto. 
    apply valid_syntax_preservation with CT t (SIGMA s' h') s h (classTy clsT); auto.
    inversion H_valid_syntax. auto. 
    apply L_reduction with (Config CT (FieldAccess t0 i) (SIGMA s0 h0)); auto. 

  ++++ inversion H6. 


- (*FieldAccess (ObjId o) i*)  
  intros. unfold dot_free in H_dot_free. fold dot_free in H_dot_free. auto.
  inversion H_erasure_l. subst.
  + rewrite H_flow_l in H2. inversion H2.
  + subst.  inversion H_erasure_r. subst.
        rewrite H_flow_r in H3. inversion H3. subst. 
  +++  inversion H_typing. subst. left. unfold erasure_H_fun. assert (return_free (ObjId o) = true).
  auto.  rewrite H. fold erasure_H_fun. inversion H5. subst. rename h0 into h.
  assert (( t' = null \/ exists o',  t' = ObjId o')).  
  apply field_value with h o cls fields lb i CT cls'; auto. rename s0 into s. 
    unfold erasure_sigma_fun; 
      induction s; 
      unfold flow_to in H_flow_l;  unfold current_label in H_flow_l;  unfold get_stack in H_flow_l; 
      unfold get_current_label in H_flow_l. unfold L_Label in H_flow_l. 
      unfold subset in H_flow_l. inversion H_flow_l.
      induction a.
      unfold update_current_label;  auto;  fold erasure_H_fun; rewrite H12; rewrite H14; rewrite H10.
      unfold update_current_label.
      assert ((erasure_H_fun t') = dot). destruct H0. subst; auto. destruct H0 as [o']. subst. auto.
      rewrite H9.   
      assert (l0 = lb). apply label_equivalence; auto; 
      apply flow_transitive with l0; auto. rewrite H11. auto.   

- (*MethodCall t1' i t2*) 
  intros. unfold dot_free in H_dot_free. fold dot_free in H_dot_free. 
  apply dot_free_if in H_dot_free. destruct H_dot_free. auto.
  inversion H_erasure_l. subst.
  + rewrite H_flow_l in H5. inversion H5.
  + subst.  inversion H_erasure_r. subst.
        rewrite H_flow_r in H6. inversion H6. subst. 
  ++  inversion H_typing. subst. 
    assert (Config CT (erasure_H_fun t1) (SIGMA  s'0 h'0) = Config CT (erasure_H_fun e')  (SIGMA s'1 h'1) 
      \/ (Config CT (erasure_H_fun t1) (SIGMA  s'0 h'0) ==l> Config CT (erasure_H_fun e')  (SIGMA s'1 h'1))). 
    apply IHt1 with h' s' h s (classTy T0)  e'; auto.   
    inversion H_valid_syntax. auto.  apply value_is_valid_syntax.  auto. 
    apply erasure_H_context; auto.     auto. apply erasure_H_context; auto.

    destruct H2.
    assert (return_free t1= return_free e'). 
    apply erasure_H_fun_equal_return_free. inversion H_valid_syntax. auto.  
    apply value_is_valid_syntax.  auto. 
    apply valid_syntax_preservation with CT t1 (SIGMA s' h') s h (classTy T0); auto. 
    inversion H_valid_syntax. auto.   auto. apply value_is_valid_syntax; auto.
    inversion H2. auto. 
    unfold erasure_H_fun. fold erasure_H_fun. subst. 
    case_eq (return_free t1). intro.  rewrite H4 in H3. rewrite <- H3. 
    left. inversion H2. subst. auto. inversion   H_valid_syntax. apply surface_syntax_is_return_free in H21.
    rewrite H21. auto.  inversion H16; subst; inversion H0. 
    intro. rewrite <- H3. rewrite H4.  inversion H2. subst. auto. 

     (*l reduction*)    
    inversion H2. induction c2.
  +++ assert (CT = c). apply ct_consist with (erasure_H_fun t1)  t (SIGMA s'0 h'0) s0; auto. 
    subst. rename c into CT.    right.  unfold erasure_H_fun. fold erasure_H_fun. subst. 
    case_eq (return_free t1). intro. assert ((erasure_H_fun t1) = dot). 
    apply return_free_true_imply_erasure_H_fun_dot; auto. inversion H_valid_syntax; auto.
    apply value_is_valid_syntax; auto.
    rewrite H14 in H3. inversion H3.   
    
    intro. case_eq (return_free e'). 
    intro.  assert (erasure_H_fun e' = dot).
    apply  return_free_true_imply_erasure_H_fun_dot; auto. 
    apply valid_syntax_preservation with CT t1 (SIGMA s' h') s h (classTy T0); auto. 
    inversion H_valid_syntax. auto. apply value_is_valid_syntax; auto.
    rewrite H15 in H4. 
    assert (Config CT (MethodCall (erasure_H_fun t1) i t2) (SIGMA s'0 h'0) ==> 
            Config CT (MethodCall t i t2)  s0 ).
    apply ST_MethodCall1; auto. induction s0.
    assert (return_free t2 = true). inversion H_valid_syntax. apply surface_syntax_is_return_free; auto.
    apply value_is_return_free in H22. rewrite H22 in H13. inversion H13. rewrite H18.  
    
    assert ((flow_to (current_label ((SIGMA s'1 h'1))) L_Label = flow_to (current_label (SIGMA s0 h0)) L_Label )).
    apply erasure_preserve_context with t dot CT; auto. 
    assert ( flow_to (current_label (SIGMA s'1 h'1)) L_Label = flow_to (current_label (SIGMA s' h')) L_Label).
    apply erasure_sigma_preserve_context; auto. rewrite H_flow_r in H22. rewrite H22 in H21. 
    inversion H4. subst. rewrite H26 in H21. inversion H21. subst. 

    assert (Config CT (MethodCall t i t2) (SIGMA s0 h0) =e=> Config CT dot (SIGMA s'1 h'1)).
    apply erasure_H_context; auto. unfold erasure_H_fun. fold erasure_H_fun. 
    assert (return_free t = true). apply  erasure_H_fun_imply_return_free; auto. 

    apply valid_syntax_preservation_erasured with CT (erasure_H_fun t1) s h (SIGMA s0 h0) (classTy T0). auto. 
    apply valid_syntax_preservation_erasure_H; inversion H_valid_syntax; auto. 
    apply value_is_valid_syntax. auto. 
    apply typing_preservation_erasure; auto. auto.  rewrite <- H10. auto. 

    rewrite H18. rewrite H23.  auto. apply L_reduction with (Config CT (MethodCall t i t2) (SIGMA s0 h0)); auto.
  
    intro.  unfold erasure_H_fun. fold erasure_H_fun. subst. 
    assert (Config CT (MethodCall (erasure_H_fun t1) i t2) (SIGMA s'0 h'0) ==> 
            Config CT (MethodCall t i t2)  s0 ).
    apply ST_MethodCall1; auto. induction s0.
    assert ((flow_to (current_label ((SIGMA s'1 h'1))) L_Label = flow_to (current_label (SIGMA s0 h0)) L_Label )).
    apply erasure_preserve_context with t (erasure_H_fun e') CT; auto. 
    assert ( flow_to (current_label (SIGMA s'1 h'1)) L_Label = flow_to (current_label (SIGMA s' h')) L_Label).
    apply erasure_sigma_preserve_context; auto. rewrite H_flow_r in H18. rewrite H18 in H16.  
    inversion H4. subst. rewrite H24 in H16. inversion H16. subst. 

    assert (Config CT (MethodCall t i t2) (SIGMA s0 h0) =e=> Config CT (MethodCall (erasure_H_fun e') i t2) (SIGMA s'1 h'1)).
    apply erasure_H_context; auto. unfold erasure_H_fun. fold erasure_H_fun.
    apply return_free_imply_erasure_H_fun_dot in H14. rewrite H29 in H14.  
    assert (return_free t = false). apply  erasure_H_fun_imply_return_free_false; auto.

    apply valid_syntax_preservation_erasured with CT (erasure_H_fun t1) s h (SIGMA s0 h0) (classTy T0). auto. 
    apply valid_syntax_preservation_erasure_H; inversion H_valid_syntax; auto.
    apply value_is_valid_syntax; auto.  
    apply typing_preservation_erasure; auto. auto.  rewrite <- H10. auto. 
    
    rewrite H21. rewrite H29. auto. 
    apply valid_syntax_preservation with CT t1 (SIGMA s' h') s h (classTy T0); auto.
    inversion H_valid_syntax. auto. apply value_is_valid_syntax; auto.  
    apply L_reduction with (Config CT (MethodCall t i t2) (SIGMA s0 h0)); auto. 

  +++ inversion H4. 

- (*MethodCall t1 i t2' *)
  intros. unfold dot_free in H_dot_free. fold dot_free in H_dot_free. 
  apply dot_free_if in H_dot_free. destruct H_dot_free. auto.
  inversion H_erasure_l. subst.
  + rewrite H_flow_l in H5. inversion H5.
  + subst.  inversion H_erasure_r. subst.
        rewrite H_flow_r in H6. inversion H6. subst. 
  ++  inversion H_typing. subst. 
    assert (Config CT (erasure_H_fun t2) (SIGMA  s'0 h'0) = Config CT (erasure_H_fun e')  (SIGMA s'1 h'1) 
      \/ (Config CT (erasure_H_fun t2) (SIGMA  s'0 h'0) ==l> Config CT (erasure_H_fun e')  (SIGMA s'1 h'1))). 
    apply IHt2 with h' s' h s (classTy arguT)  e'; auto.   
    inversion H_valid_syntax. apply surface_syntax_is_valid_syntax. auto. auto. 
    apply erasure_H_context; auto.     auto. apply erasure_H_context; auto.

    destruct H1.
    assert (return_free t2= return_free e'). 
    apply erasure_H_fun_equal_return_free. inversion H_valid_syntax. 
    apply surface_syntax_is_valid_syntax. auto. auto. 
    apply valid_syntax_preservation with CT t2 (SIGMA s' h') s h (classTy arguT); auto. 
    inversion H_valid_syntax. apply surface_syntax_is_valid_syntax. auto.   auto.
    inversion H1. auto. 
    unfold erasure_H_fun. fold erasure_H_fun. subst. 
    case_eq (return_free t1). intro. 
    left. inversion H1. subst.  rewrite H2.  auto. 
    intro. left. assert (return_free t1 = true). apply value_is_return_free. auto. 
    rewrite H4 in H16. inversion H16. 

     (*l reduction*)    
    inversion H1. induction c2.
  +++ assert (CT = c). apply ct_consist with (erasure_H_fun t2)  t (SIGMA s'0 h'0) s0; auto. 
    subst. rename c into CT.    right.  unfold erasure_H_fun. fold erasure_H_fun. subst. 
    case_eq (return_free t2). intro. assert ((erasure_H_fun t2) = dot). 
    apply return_free_true_imply_erasure_H_fun_dot; auto. inversion H_valid_syntax; auto.
    apply surface_syntax_is_valid_syntax; auto.
    rewrite H17 in H2. inversion H2.   
    
    assert (return_free t1 = true). apply value_is_return_free. auto. 

    intro. rewrite H16.  case_eq (return_free e'). 
    intro.  assert (erasure_H_fun e' = dot).
    apply  return_free_true_imply_erasure_H_fun_dot; auto. 
    apply valid_syntax_preservation with CT t2 (SIGMA s' h') s h (classTy arguT); auto. 
    inversion H_valid_syntax. auto. apply surface_syntax_is_valid_syntax; auto. auto. 

    rewrite H19 in H4.
    assert (Config CT (MethodCall t1 i (erasure_H_fun t2)) (SIGMA s'0 h'0) ==> 
            Config CT (MethodCall t1 i t)  s0 ).
    apply ST_MethodCall2; auto. induction s0. 
    intro v0. intros. intro contra. 
    apply erasure_unlabelOpaque_return_free in contra. 
    rewrite contra in H17. inversion H17. inversion H_valid_syntax.
    apply surface_syntax_is_valid_syntax. auto.  auto. auto. induction s0. 

    assert ((flow_to (current_label ((SIGMA s'1 h'1))) L_Label = flow_to (current_label (SIGMA s0 h0)) L_Label )).
    apply erasure_preserve_context with t dot CT; auto. 
    assert ( flow_to (current_label (SIGMA s'1 h'1)) L_Label = flow_to (current_label (SIGMA s' h')) L_Label).
    apply erasure_sigma_preserve_context; auto. rewrite H_flow_r in H25. rewrite H25 in H24. 
    inversion H4. subst. rewrite H29 in H24. inversion H24. subst. 

    assert (Config CT (MethodCall t1 i t) (SIGMA s0 h0) =e=> Config CT dot (SIGMA s'1 h'1)).
    apply erasure_H_context; auto. unfold erasure_H_fun. fold erasure_H_fun.  
    assert (return_free t = true). apply  erasure_H_fun_imply_return_free; auto. 

    apply valid_syntax_preservation_erasured with CT (erasure_H_fun t2) s h (SIGMA s0 h0) (classTy arguT). auto. 
    apply valid_syntax_preservation_erasure_H; inversion H_valid_syntax; auto. 
    apply surface_syntax_is_valid_syntax. auto. 
    apply typing_preservation_erasure; auto. auto.  rewrite <- H13. auto. 

    rewrite H16. rewrite H26.  auto. apply L_reduction with (Config CT (MethodCall t1 i t) (SIGMA s0 h0)); auto.
  
    intro.  unfold erasure_H_fun. fold erasure_H_fun. subst. 
    assert (Config CT (MethodCall t1 i (erasure_H_fun t2)) (SIGMA s'0 h'0) ==> 
            Config CT (MethodCall t1 i t)  s0 ).
    apply ST_MethodCall2; auto. 

    intro v0. intros. intro contra. 
    apply erasure_unlabelOpaque_return_free in contra. 
    rewrite contra in H17. inversion H17. inversion H_valid_syntax.
    apply surface_syntax_is_valid_syntax. auto.  auto. auto. induction s0. 

    assert ((flow_to (current_label ((SIGMA s'1 h'1))) L_Label = flow_to (current_label (SIGMA s0 h0)) L_Label )).
    apply erasure_preserve_context with t (erasure_H_fun e') CT; auto. 
    assert ( flow_to (current_label (SIGMA s'1 h'1)) L_Label = flow_to (current_label (SIGMA s' h')) L_Label).
    apply erasure_sigma_preserve_context; auto. rewrite H_flow_r in H24. rewrite H24 in H21.  
    inversion H4. subst. rewrite H28 in H21. inversion H21. subst. 

    assert (Config CT (MethodCall t1 i t) (SIGMA s0 h0) =e=> Config CT (MethodCall t1 i (erasure_H_fun e')) (SIGMA s'1 h'1)).
    apply erasure_H_context; auto. unfold erasure_H_fun. fold erasure_H_fun.
    apply return_free_imply_erasure_H_fun_dot in H18. rewrite H33 in H18.  
    assert (return_free t = false). apply  erasure_H_fun_imply_return_free_false; auto.

    apply valid_syntax_preservation_erasured with CT (erasure_H_fun t2) s h (SIGMA s0 h0) (classTy arguT). auto. 
    apply valid_syntax_preservation_erasure_H; inversion H_valid_syntax; auto.
    apply surface_syntax_is_valid_syntax; auto.  
    apply typing_preservation_erasure; auto. auto.  rewrite <- H13. auto. 
    
    rewrite H16. rewrite H25. rewrite H33. auto. 
    apply valid_syntax_preservation with CT t2 (SIGMA s' h') s h (classTy arguT); auto.
    inversion H_valid_syntax. auto. apply surface_syntax_is_valid_syntax; auto. auto.   
    apply L_reduction with (Config CT (MethodCall t1 i t) (SIGMA s0 h0) ); auto. 

  +++ inversion H4. 

-  (*  MethodCall (ObjId o) i v  *) 
inversion H6. subst. inversion H14. subst. rename s0 into s. rename h0 into h. 
 intros. unfold dot_free in H_dot_free. fold dot_free in H_dot_free. 
  inversion H_erasure_l. subst.
  + rewrite H_flow_l in H2. inversion H2.
  + subst.  inversion H_erasure_r. subst.
      induction s. 
      unfold flow_to in H_flow_l;  unfold current_label in H_flow_l;  unfold get_stack in H_flow_l; 
      unfold get_current_label in H_flow_l. unfold L_Label in H_flow_l. 
      unfold subset in H_flow_l. inversion H_flow_l.
      induction a.
      
      unfold current_label in H_flow_l;  unfold get_stack in H_flow_l; 
      unfold get_current_label in H_flow_l. unfold get_stack_label in H_flow_l. 
      unfold current_label in H3;  unfold get_stack in H3; 
      unfold get_current_label in H3. unfold get_stack_label in H3. rewrite H_flow_l in H3. inversion H3. 

   ++ subst. right. unfold erasure_H_fun. fold erasure_H_fun. assert (return_free (ObjId o ) = true). auto. 
      rewrite H. assert (return_free t2 = true). apply value_is_return_free; auto. rewrite H0. 
      inversion H_typing. subst. inversion H10. subst. destruct H22 as [F']. destruct H1 as [lo']. 
      rewrite H1 in H7. inversion H7. subst. rewrite <- H15 in H5. inversion H5.  subst.  
      rewrite H16 in H8. inversion H8. subst. 
  
      assert (return_free body0 = true). apply surface_syntax_is_return_free. auto. rewrite H4.  





  inversion H_erasure_l. subst.
  + rewrite H_flow_l in H2. inversion H2.
  + subst.  inversion H_erasure_r. subst.
        rewrite H_flow_r in H6. inversion H6. subst. 
  ++  inversion H_typing. subst. 


-  (* MethodCall (ObjId o) i (unlabelOpaque (v_opa_l v lb))  *)  admit.

- (* new exp*) admit. 

- (* label data *) admit. 

- (* v_l t lb *) admit. 

-  (* unlabel *) admit. 

-  (* unlabel v_l *) admit.

-  (* labelOf *) admit.


-  (* labelOf v*) admit.

-  (* unlabelOpaque e *) admit.

-  (* (unlabelOpaque (v_opa_l t' lb)) *) admit.

-  (* opaqueCall e' *) admit.

-  (* (opaqueCall (Return e')) *) admit.

-  (* (opaqueCall t) *) admit.
-  (* (opaqueCall (Return v)) *) admit.
-  (*Assignment*) 
      inversion H_typing. inversion H5.
-  (* Assignment *) 
     inversion H_typing. inversion H5.
-  (* (FieldWrite t1 i t2) *) admit.
-  (* (FieldWrite t1 i t2) *) admit.
-  (* (FieldWrite t1 i t2) *) admit.
-  (*(FieldWrite t1 i t2 *) admit.
-  (* if *) 
  inversion H_typing. inversion H7. inversion H18. 
-  (* if *) 
  inversion H_typing. inversion H7. inversion H18. 
-  (* Sequence *) 
 intros. unfold dot_free in H_dot_free. fold dot_free in H_dot_free. 
  apply dot_free_if in H_dot_free. destruct H_dot_free. auto.
  inversion H_erasure_l. subst.
  + rewrite H_flow_l in H5. inversion H5.
  + subst.  inversion H_erasure_r. subst.
        rewrite H_flow_r in H6. inversion H6. subst. 
  ++  inversion H_typing. subst. 
    assert (Config CT (erasure_H_fun t1) (SIGMA  s'0 h'0) = Config CT (erasure_H_fun s1')  (SIGMA s'1 h'1) 
      \/ (Config CT (erasure_H_fun t1) (SIGMA  s'0 h'0) ==l> Config CT (erasure_H_fun s1')  (SIGMA s'1 h'1))). 
    apply IHt1 with h' s' h s T0  s1'; auto.   
    inversion H_valid_syntax. auto.  apply value_is_valid_syntax.  auto. 
    apply erasure_H_context; auto.     auto. apply erasure_H_context; auto.

    destruct H2.
    assert (return_free t1= return_free s1'). 
    apply erasure_H_fun_equal_return_free. inversion H_valid_syntax. auto.  
    apply value_is_valid_syntax.  auto. 
    apply valid_syntax_preservation with CT t1 (SIGMA s' h') s h  T0; auto. 
    inversion H_valid_syntax. auto.   auto. apply value_is_valid_syntax; auto.
    inversion H2. auto. 
    unfold erasure_H_fun. fold erasure_H_fun. subst. 
    case_eq (return_free t1). intro.  rewrite H4 in H3. rewrite <- H3. 
    left. inversion H2. subst. auto. intro.  rewrite H4 in H3. rewrite <- H3. left. 
    inversion H2. subst. auto. auto.  

     (*l reduction*)    
    inversion H2. induction c2.
  +++ assert (CT = c). apply ct_consist with (erasure_H_fun t1)  t (SIGMA s'0 h'0) s0; auto. 
    subst. rename c into CT.    right.  unfold erasure_H_fun. fold erasure_H_fun. subst. 
    case_eq (return_free t1). intro. assert ((erasure_H_fun t1) = dot). 
    apply return_free_true_imply_erasure_H_fun_dot; auto. inversion H_valid_syntax; auto.
    apply value_is_valid_syntax; auto.
    rewrite H8 in H3. inversion H3.   
    
    intro. case_eq (return_free s1'). 
    intro.  assert (erasure_H_fun s1' = dot).
    apply  return_free_true_imply_erasure_H_fun_dot; auto. 
    apply valid_syntax_preservation with CT t1 (SIGMA s' h') s h T0; auto. 
    inversion H_valid_syntax. auto. apply value_is_valid_syntax; auto.
    rewrite H11 in H4. 
    assert (Config CT (Sequence (erasure_H_fun t1) t2) (SIGMA s'0 h'0) ==> 
            Config CT (Sequence t t2)  s0 ).
    apply ST_seq1; auto. induction s0.
    assert (return_free t2 = true). inversion H_valid_syntax. apply surface_syntax_is_return_free; auto.
    apply value_is_return_free in H17. rewrite H17 in H7. inversion H7. rewrite H15.  
    
    assert ((flow_to (current_label ((SIGMA s'1 h'1))) L_Label = flow_to (current_label (SIGMA s0 h0)) L_Label )).
    apply erasure_preserve_context with t dot CT; auto. 
    assert ( flow_to (current_label (SIGMA s'1 h'1)) L_Label = flow_to (current_label (SIGMA s' h')) L_Label).
    apply erasure_sigma_preserve_context; auto. rewrite H_flow_r in H17. rewrite H17 in H16. 
    inversion H4. subst. rewrite H21 in H16. inversion H16. subst. 

    assert (Config CT (Sequence t t2) (SIGMA s0 h0) =e=> Config CT dot (SIGMA s'1 h'1)).
    apply erasure_H_context; auto. unfold erasure_H_fun. fold erasure_H_fun. 
    assert (return_free t = true). apply  erasure_H_fun_imply_return_free; auto. 

    apply valid_syntax_preservation_erasured with CT (erasure_H_fun t1) s h (SIGMA s0 h0) T0. auto. 
    apply valid_syntax_preservation_erasure_H; inversion H_valid_syntax; auto. 
    apply value_is_valid_syntax. auto. 
    apply typing_preservation_erasure; auto. auto.  rewrite <- H10. auto. 

    rewrite H18. rewrite H15.  auto. apply L_reduction with (Config CT (Sequence t t2) (SIGMA s0 h0)); auto.
  
    intro.  unfold erasure_H_fun. fold erasure_H_fun. subst. 
    assert (Config CT (Sequence (erasure_H_fun t1) t2) (SIGMA s'0 h'0) ==> 
            Config CT (Sequence t t2)  s0 ).
    apply ST_seq1; auto. induction s0.
    assert ((flow_to (current_label ((SIGMA s'1 h'1))) L_Label = flow_to (current_label (SIGMA s0 h0)) L_Label )).
    apply erasure_preserve_context with t (erasure_H_fun s1') CT; auto. 
    assert ( flow_to (current_label (SIGMA s'1 h'1)) L_Label = flow_to (current_label (SIGMA s' h')) L_Label).
    apply erasure_sigma_preserve_context; auto. rewrite H_flow_r in H15. rewrite H15 in H14.  
    inversion H4. subst. rewrite H19 in H14. inversion H14. subst. 

    assert (Config CT (Sequence t t2) (SIGMA s0 h0) =e=> Config CT (Sequence (erasure_H_fun s1') t2) (SIGMA s'1 h'1)).
    apply erasure_H_context; auto. unfold erasure_H_fun. fold erasure_H_fun.
    apply return_free_imply_erasure_H_fun_dot in H8. rewrite H24 in H8.  
    assert (return_free t = false). apply  erasure_H_fun_imply_return_free_false; auto.

    apply valid_syntax_preservation_erasured with CT (erasure_H_fun t1) s h (SIGMA s0 h0) ( T0). auto. 
    apply valid_syntax_preservation_erasure_H; inversion H_valid_syntax; auto.
    apply value_is_valid_syntax; auto.  
    apply typing_preservation_erasure; auto. auto.  rewrite <- H10. auto. 
    
    rewrite H16. rewrite H24. auto. 
    apply valid_syntax_preservation with CT t1 (SIGMA s' h') s h T0; auto.
    inversion H_valid_syntax. auto. apply value_is_valid_syntax; auto.  
    apply L_reduction with (Config CT (Sequence t t2) (SIGMA s0 h0)); auto. 

  +++ inversion H4. 


-  (* Sequence *) 
 intros. unfold dot_free in H_dot_free. fold dot_free in H_dot_free. 
  apply dot_free_if in H_dot_free. destruct H_dot_free. auto.
  inversion H_erasure_l. subst.
  + rewrite H_flow_l in H5. inversion H5.
  + subst.  inversion H_erasure_r. subst.
        rewrite H_flow_r in H6. inversion H6. subst. 
        unfold  erasure_H_fun. fold  erasure_H_fun. 
        assert (return_free t1 = true). apply value_is_return_free. auto. rewrite H2. 
        rewrite <- H12 in H10. inversion H10. subst.  left. 
        case_eq (return_free t' ). intro.
        apply return_free_true_imply_erasure_H_fun_dot in H3. rewrite H3. auto. 
        inversion H_valid_syntax.  apply surface_syntax_is_valid_syntax. auto. auto. 
      
       intro. auto. 

-  (* Return *) 
 intros. unfold dot_free in H_dot_free. fold dot_free in H_dot_free. 
  inversion H_erasure_l. subst.
  + rewrite H_flow_l in H3. inversion H3.
  + subst.  inversion H_erasure_r. subst.
        rewrite H_flow_r in H4. inversion H4. subst. 
  ++  inversion H_typing. subst. 
    assert (Config CT (erasure_H_fun t) (SIGMA  s'0 h'0) = Config CT (erasure_H_fun e')  (SIGMA s'1 h'1) 
      \/ (Config CT (erasure_H_fun t) (SIGMA  s'0 h'0) ==l> Config CT (erasure_H_fun e')  (SIGMA s'1 h'1))). 
    apply IHt with h' s' h s T  e'; auto.   
    inversion H_valid_syntax. auto. 
    apply erasure_H_context; auto.     auto. apply erasure_H_context; auto.

    destruct H.
    assert (return_free t= return_free e'). 
    apply erasure_H_fun_equal_return_free. inversion H_valid_syntax. auto.  
    apply valid_syntax_preservation with CT t (SIGMA s' h') s h  T; auto. 
    inversion H_valid_syntax. auto. 
    inversion H. auto. 
    unfold erasure_H_fun. fold erasure_H_fun. subst. 
    case_eq (return_free t). intro.  rewrite H5 in H2. rewrite <- H2. 
    left. inversion H. subst. auto. intro.  rewrite H5 in H2. rewrite <- H2. left. 
    inversion H. subst. auto. auto.  

     (*l reduction*)    
    inversion H. induction c2.
  +++ assert (CT = c). apply ct_consist with (erasure_H_fun t)  t0 (SIGMA s'0 h'0) s0; auto. 
    subst. rename c into CT.    right.  unfold erasure_H_fun. fold erasure_H_fun. subst. 
    case_eq (return_free t). intro. assert ((erasure_H_fun t) = dot). 
    apply return_free_true_imply_erasure_H_fun_dot; auto. inversion H_valid_syntax; auto.
    rewrite H9 in H2. inversion H2.   
    
    intro. case_eq (return_free e'). 
    intro.  assert (erasure_H_fun e' = dot).
    apply  return_free_true_imply_erasure_H_fun_dot; auto. 
    apply valid_syntax_preservation with CT t (SIGMA s' h') s h T; auto. 
    inversion H_valid_syntax. auto. 
    rewrite H11 in H5. 
    assert (Config CT (Return (erasure_H_fun t)) (SIGMA s'0 h'0) ==> 
            Config CT (Return t0) s0 ).
    apply ST_return1; auto. induction s0.
    
    assert ((flow_to (current_label ((SIGMA s'1 h'1))) L_Label = flow_to (current_label (SIGMA s0 h0)) L_Label )).
    apply erasure_preserve_context with t0 dot CT; auto. 
    assert ( flow_to (current_label (SIGMA s'1 h'1)) L_Label = flow_to (current_label (SIGMA s' h')) L_Label).
    apply erasure_sigma_preserve_context; auto. rewrite H_flow_r in H14. rewrite H14 in H13. 
    inversion H5. subst. rewrite H18 in H13. inversion H13. subst. 

    assert (Config CT (Return t0) (SIGMA s0 h0) =e=> Config CT (Return dot) (SIGMA s'1 h'1)).
    apply erasure_H_context; auto. unfold erasure_H_fun. fold erasure_H_fun. 
    assert (return_free t0 = true). apply  erasure_H_fun_imply_return_free; auto. 

    apply valid_syntax_preservation_erasured with CT (erasure_H_fun t) s h (SIGMA s0 h0) T. auto. 
    apply valid_syntax_preservation_erasure_H; inversion H_valid_syntax; auto. 
    apply typing_preservation_erasure; auto. auto.  rewrite <- H8. auto. 

    rewrite H15. auto.  auto. apply L_reduction with ( Config CT (Return t0) (SIGMA s0 h0)); auto.
  
    intro.  unfold erasure_H_fun. fold erasure_H_fun. subst. 
    assert (Config CT (Return (erasure_H_fun t)) (SIGMA s'0 h'0) ==> 
            Config CT (Return t0)  s0 ).
    apply ST_return1; auto. induction s0.
    assert ((flow_to (current_label ((SIGMA s'1 h'1))) L_Label = flow_to (current_label (SIGMA s0 h0)) L_Label )).
    apply erasure_preserve_context with t0 (erasure_H_fun e') CT; auto. 
    assert ( flow_to (current_label (SIGMA s'1 h'1)) L_Label = flow_to (current_label (SIGMA s' h')) L_Label).
    apply erasure_sigma_preserve_context; auto. rewrite H_flow_r in H13. rewrite H13 in H12.  
    inversion H5. subst. rewrite H17 in H12. inversion H12. subst. 

    assert (Config CT (Return t0) (SIGMA s0 h0) =e=> Config CT (Return (erasure_H_fun e')) (SIGMA s'1 h'1)).
    apply erasure_H_context; auto. unfold erasure_H_fun. fold erasure_H_fun.
    assert (return_free t0 = false). apply  erasure_H_fun_imply_return_free_false; auto.

    apply valid_syntax_preservation_erasured with CT (erasure_H_fun t) s h (SIGMA s0 h0) T. auto. 
    apply valid_syntax_preservation_erasure_H; inversion H_valid_syntax; auto. 
    apply typing_preservation_erasure; auto. auto.  rewrite <- H8. auto. 
    apply return_free_imply_erasure_H_fun_dot in H9. rewrite H22 in H9. auto.  
    apply valid_syntax_preservation with CT t (SIGMA s' h') s h T; auto. 
    inversion H_valid_syntax. auto. rewrite H14.  rewrite H22. auto. 
    apply L_reduction with (Config CT (Return t0) (SIGMA s0 h0)); auto. 

  +++ inversion H5. 
- (* Return *) right. inversion H5. subst. 
 intros. unfold dot_free in H_dot_free. fold dot_free in H_dot_free. 
  inversion H_erasure_l. subst.
  + rewrite H_flow_l in H2. inversion H2.
  + subst.  inversion H_erasure_r. subst.
        rewrite H_flow_r in H3. inversion H3. subst. 
  ++rewrite H13. rewrite H11. assert (return_free t' = true).
       apply value_is_return_free. auto.
        assert (erasure_H_fun t' = dot). 
        apply return_free_true_imply_erasure_H_fun_dot. auto. 
       inversion H_valid_syntax. auto. auto.  
     unfold erasure_H_fun. fold erasure_H_fun.
     rewrite H0. rewrite H. unfold erasure_sigma_fun. induction lsf. 
     inversion H10. subst.  unfold erasure_stack. fold erasure_stack.
    assert (Config CT (Return dot)
         (SIGMA (Labeled_frame l0 (fun x : id => erasure_obj_null (s x) h0) :: s'0)
            (erasure_heap h0)) ==> Config CT dot (SIGMA (update_current_label s'0 (join_label l0 (get_current_label s'0)))
                                                      (erasure_heap h0)) ).
    apply ST_return2 with  (Labeled_frame l0 (fun x : id => erasure_obj_null (s x) h0) :: s'0)
                                        s'0  (update_current_label s'0 (join_label l0 (get_current_label s'0))) 
                                         (erasure_heap h0) (Labeled_frame l0 (fun x : id => erasure_obj_null (s x) h0))
                                         (join_label l0 (get_current_label s'0)); auto. 
    assert (Config CT dot (SIGMA (update_current_label s'0 (join_label l0 (get_current_label s'0)))
                                                      (erasure_heap h0)) =e=> Config CT dot
                                                                              (SIGMA
                                                                                 (erasure_stack
                                                                                    (update_current_label s'0 (join_label l0 (get_current_label s'0))) h0)
                                                                                 (erasure_heap h0))).
    apply erasure_H_context; auto. unfold erasure_sigma_fun.
    assert ( (erasure_stack
                    (update_current_label s'0 (join_label l0 (get_current_label s'0))) h0) = 
                (erasure_stack
                  (update_current_label s'0 (join_label l0 (get_current_label s'0))) (erasure_heap h0) )).
    apply multi_erasure_stack_helper with CT. auto. 
    rewrite H6. 
    assert ((erasure_heap (erasure_heap h0)) =  (erasure_heap h0)).
    apply multi_erasure_heap_equal. rewrite H8. auto.  
    apply L_reduction with (Config CT dot
                                           (SIGMA
                                              (update_current_label s'0 (join_label l0 (get_current_label s'0)))
                                              (erasure_heap h0))) ; auto. 
Admitted.


(*
Lemma simulation_H_saved : forall CT t t0 t' t0' s h s' h' sigma_l_e sigma_r_e,
      dot_free t = true ->
      valid_syntax t ->
      forall T, has_type CT empty_context h t T -> 
      field_wfe_heap CT h -> wfe_heap CT h -> wfe_stack CT h s ->
      flow_to (current_label (SIGMA s h)) L_Label = false ->
      flow_to (current_label (SIGMA s' h')) L_Label = false ->
      Config CT t (SIGMA s h) ==> Config CT t' (SIGMA s' h') ->
      (Config CT t (SIGMA s h)) =e=> (Config CT t0 sigma_l_e) ->
      (Config CT t' (SIGMA s' h')) =e=> (Config CT t0' sigma_r_e) ->
         (Config CT t0 sigma_l_e) ==>L*  (Config CT t0' sigma_r_e).
Proof. 
  intros CT t t0 t' t0' s h s' h' sigma_l_e sigma_r_e. intro H_dot_free. intro H_valid_syntax. 
  intro T. intro H_typing. intro H_wfe_fields. 
  intro H_wfe_heap. intro H_wfe_stack. 
  intro H_flow_l.   intro H_flow_r. intro H_reduction. 
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
  + rewrite H_flow_l in H4. inversion H4.
  + subst. inversion H_reduction.  
  ++ subst. inversion H_erasure_r. subst.
        rewrite H_flow_r in H6. inversion H6. subst. 
  +++  inversion H_typing. subst. 
    assert (Config CT (erasure_H_fun t1) (SIGMA  s'0 h'0) ==>L* Config CT (erasure_H_fun e1')  (SIGMA s'1 h'1)). 
    apply IHt1 with h' s' h s (classTy clsT)  e1'; auto.     
    inversion H_valid_syntax. auto. apply value_is_valid_syntax. auto. apply erasure_H_context; auto. 
    auto. apply erasure_H_context; auto. 
     inversion H1. unfold erasure_H_fun. fold erasure_H_fun. subst. rewrite H5. 
    inversion H_valid_syntax. subst. 
    assert (return_free t1= return_free e1'). 
    apply erasure_H_fun_equal_return_free. auto. 
    apply valid_syntax_preservation with CT t1 (SIGMA s' h') s h (classTy clsT); auto. auto. 
    case_eq (return_free t1). intro.  rewrite H8 in H3. rewrite <- H3.  
    pose proof (surface_syntax_H_erasure_dot t2 H14).
    apply erasure_H_fun_imply_return_free in H11. rewrite H11. auto. 
    apply surface_syntax_is_valid_syntax. auto.

    intro. rewrite H8 in H3. rewrite <- H3. auto. 
    subst. inversion H10 ; subst; inversion H2. 
   ++ subst. inversion H_erasure_r. subst.
        rewrite H_flow_r in H6. inversion H6. subst. 
  +++  inversion H_typing. subst. 
    assert (Config CT (erasure_H_fun t2) (SIGMA  s'0 h'0) = Config CT (erasure_H_fun e2')  (SIGMA s'1 h'1)). 
    apply IHt2 with h' s' h s (classTy cls')  e2'; auto.     
    inversion H_valid_syntax. apply surface_syntax_is_valid_syntax. auto.  auto. apply erasure_H_context; auto. 
    auto. apply erasure_H_context; auto. 
     inversion H1. unfold erasure_H_fun. fold erasure_H_fun. subst. rewrite H3. 
    inversion H_valid_syntax. subst. 
    assert (return_free t2= return_free e2'). 
    apply erasure_H_fun_equal_return_free. apply surface_syntax_is_valid_syntax. auto. 
    apply valid_syntax_preservation with CT t2 (SIGMA s' h') s h (classTy cls'); auto. 
    apply surface_syntax_is_valid_syntax. auto. auto.  
    case_eq (return_free t2). intro.  rewrite H8 in H2. rewrite <- H2.
    pose proof ( value_is_return_free t1 H11) . rewrite H13. auto. 
    intro. pose proof ( value_is_return_free t1 H11) . rewrite H13. auto. 
    rewrite <- H2. rewrite H8. auto. 
    subst. 
   pose proof ( value_is_return_free t1 H11) . rewrite H2.
     assert (return_free t2= return_free e2'). 
    apply erasure_H_fun_equal_return_free. auto. 
    apply valid_syntax_preservation with CT t2 (SIGMA s' h') s h (classTy cls'); auto.  auto. 
    rewrite H8.  auto. 
  ++ subst. inversion H_erasure_r. subst.
        rewrite H_flow_r in H5. inversion H5. subst.
   +++ inversion H10. subst. rename s0 into s. rename h0 into h.
    unfold erasure_H_fun. fold erasure_H_fun. unfold return_free. fold return_free. 
    pose proof (value_is_return_free t2 H17). rewrite H1. 
    rewrite H16 in H14. rewrite H9. rewrite H14. unfold erasure_sigma_fun.
   

 Lemma update_H_object_equal_erasure : forall h o CT cls F F' lb lb',
       wfe_heap CT h -> 
        Some (Heap_OBJ cls F lb) = lookup_heap_obj h o ->
        flow_to lb' L_Label = false ->
        flow_to lb L_Label = false ->
          erasure_heap h = erasure_heap
                                            (update_heap_obj h o
                                               (Heap_OBJ cls F' lb')).
    Proof. intros h o CT cls F F' lb lb'. intros.  induction h. unfold lookup_heap_obj in H0. inversion H0.
     induction a. case_eq (beq_oid o o0). intro. unfold update_heap_obj. rewrite H3. 

    unfold lookup_heap_obj in H0.  rewrite H3 in H0.  inversion H0. 
    unfold erasure_heap. fold erasure_heap. rewrite H2. rewrite H1.  auto. 
    intro. unfold update_heap_obj. rewrite H3.  fold update_heap_obj. 
    assert (erasure_heap h =
      erasure_heap (update_heap_obj h o (Heap_OBJ cls F' lb'))).
    apply IHh. auto.  inversion H. auto. inversion H4. subst. auto.
    unfold  lookup_heap_obj in H0. rewrite H3 in H0. fold lookup_heap_obj in H0. auto.
    unfold erasure_heap. fold erasure_heap.
    rewrite H4. auto. 

    induction h0. 
    assert ( forall a, 
     (fun x : id => erasure_obj_null (f x) ((o0, Heap_OBJ c f l0) :: h)) a
          = (fun x : id => erasure_obj_null (f x)
                     ((o0, Heap_OBJ c f l0) :: update_heap_obj h o (Heap_OBJ cls F' lb'))) a).
    Proof. intro  a. 
assert (forall h o, (exists cls F lb, lookup_heap_obj h o = Some (Heap_OBJ cls F lb) ) 
      \/ lookup_heap_obj h o = None).
    intro h1. induction h1.  right. unfold lookup_heap_obj. auto.
    intro o1.  induction a0. case_eq ( beq_oid o1 o2). unfold lookup_heap_obj.  intro. unfold lookup_heap_obj. rewrite H5.
    rename h0 into ho. induction ho.     left. exists c0. exists f0. exists l1. auto. 
    intro. unfold lookup_heap_obj. rewrite H5. fold lookup_heap_obj. apply IHh1. 
    remember ((o, Heap_OBJ c f l0) :: h) as h'. 
    case (f a). induction t; try (unfold erasure_obj_null; auto).
    

    destruct H5 with  ((o0, Heap_OBJ c f l0) :: h)  o1. 
    destruct H6 as [cls1]. destruct H6 as [F1]. destruct H6 as [lb1]. rewrite H6.

      Lemma lookup_updated_heap_equal : forall cls F lb o h cls1 F1 lb1 F' o1 lb',
          lookup_heap_obj h o = Some (Heap_OBJ cls F lb) ->
          lookup_heap_obj h o1 = Some (Heap_OBJ cls1 F1 lb1) -> 
          (lookup_heap_obj
               (update_heap_obj h o (Heap_OBJ cls F' lb')) o1  = 
                      Some (Heap_OBJ cls1 F1 lb1)) \/ 
              (lookup_heap_obj (update_heap_obj h o (Heap_OBJ cls F' lb')) o1  = 
                      Some (Heap_OBJ cls F' lb') /\ beq_oid o1 o = true).
      Proof. intros.  induction h. 
      unfold lookup_heap_obj in H0. inversion H0.  induction a.
      case_eq (beq_oid o o0). intro.

      unfold  update_heap_obj. rewrite H1.
      case_eq (beq_oid o1 o). intro.
      unfold lookup_heap_obj. rewrite H2.
      unfold lookup_heap_obj in H0. apply beq_oid_equal in H2. rewrite H2 in H0.
      rewrite H1 in H0.
      unfold lookup_heap_obj in H. rewrite H1 in H. rewrite H0 in H. inversion H. subst.  
      right. auto. 
      intro. unfold lookup_heap_obj. rewrite H2. fold lookup_heap_obj.
      unfold lookup_heap_obj in H0. apply beq_oid_equal in H1. rewrite <-H1 in H0.
      rewrite H2 in H0. fold lookup_heap_obj in H0. rewrite H0. 
      left. auto.
      intro. 
      case_eq (beq_oid o1 o0). intro.
      unfold update_heap_obj. rewrite H1. fold update_heap_obj.
       unfold lookup_heap_obj. rewrite H2.
       unfold lookup_heap_obj in H0.    rewrite H2 in H0. rewrite H0.
      left. auto. 
      intro.  unfold lookup_heap_obj in H. 
       unfold lookup_heap_obj in H0. 
      rewrite H1 in H. fold lookup_heap_obj in H.
      rewrite H2 in H0. fold lookup_heap_obj in H0.
      unfold update_heap_obj.
       unfold lookup_heap_obj.  rewrite H1. rewrite H2. 
      fold lookup_heap_obj.
       fold update_heap_obj. apply IHh; auto.
      Qed. 

      remember ((o0, Heap_OBJ c f l0) :: h) as h0.
      assert(  (lookup_heap_obj
               (update_heap_obj h0 o (Heap_OBJ cls F' lb')) o1  = 
                      Some (Heap_OBJ cls1 F1 lb1)) \/ 
              (lookup_heap_obj (update_heap_obj h0 o (Heap_OBJ cls F' lb')) o1  = 
                      Some (Heap_OBJ cls F' lb')) /\ beq_oid o1 o = true ).
      apply lookup_updated_heap_equal with F lb; auto. 
      destruct H7. unfold update_heap_obj in H7. rewrite Heqh0 in H7.  rewrite H3 in H7. 
      fold update_heap_obj in H7. rewrite H7. auto.

      unfold update_heap_obj in H7. rewrite Heqh0 in H7.  rewrite H3 in H7. 
      fold update_heap_obj in H7. destruct H7. rewrite H7. apply beq_oid_equal in H8.
      rewrite H8 in H6. rewrite H6 in H0. inversion H0. subst. rewrite H2.  rewrite H1.  auto.

      rewrite H6. 
      auto.

      Lemma lookup_updated_heap_none : forall h o1 o ho,
      o <> o1 ->
      lookup_heap_obj h o1 = None ->
      lookup_heap_obj (update_heap_obj h o ho) o1 = None.
      Proof. intros. induction h.
      unfold update_heap_obj. unfold lookup_heap_obj. auto. 
      induction a. case_eq (beq_oid o o0). intro. unfold update_heap_obj. rewrite H1. 
      unfold lookup_heap_obj in H0. apply beq_oid_equal in H1. 
      unfold lookup_heap_obj. rewrite <- H1 in H0. 
      case_eq (beq_oid o1 o). intro. rewrite H2 in H0. inversion H0.
      intro. rewrite H2 in H0. fold lookup_heap_obj. fold lookup_heap_obj in H0. auto. 
      intro. unfold update_heap_obj. rewrite H1. 
      fold update_heap_obj. unfold lookup_heap_obj in H0. 
      case_eq ( beq_oid o1 o0). intro. rewrite H2 in H0. inversion H0.
      intro.  rewrite H2 in H0. fold lookup_heap_obj in H0. apply IHh in H0. 
      unfold lookup_heap_obj.  rewrite H2. fold lookup_heap_obj. auto. 
      Qed.  

      assert (lookup_heap_obj (update_heap_obj ((o0, Heap_OBJ c f l0) :: h) o (Heap_OBJ cls F' lb')) o1 = None).
      apply lookup_updated_heap_none; auto. 
      intro contra. rewrite contra in H0. rewrite <- H0 in H6. inversion H6. 
      unfold update_heap_obj in H7. rewrite H3 in H7. fold update_heap_obj in H7. rewrite H7. auto. 
        
      auto. 
      apply functional_extensionality in H5. rewrite H5. auto.  
Qed. 


assert (erasure_heap h = erasure_heap
                                            (update_heap_obj h o
                                               (Heap_OBJ cls (fields_update F i t2) lb))).
apply update_H_object_equal_erasure with CT F lb; auto. 
apply flow_false_trans with (current_label (SIGMA s h)); auto.
apply flow_false_trans with (current_label (SIGMA s h)); auto.
rewrite <- H2.


assert ( (erasure_stack s h) = erasure_stack s
        (update_heap_obj h o
           (Heap_OBJ cls (fields_update F i t2) lb))).
unfold erasure_stack. induction s. auto. induction a. rename s0 into sf. 
assert (forall a, (fun x : id => erasure_obj_null (sf x) h) a = (fun x : id =>
                                                                           erasure_obj_null (sf x)
                                                                             (update_heap_obj h o
                                                                                (Heap_OBJ cls (fields_update F i t2) lb))) a) .
intro a. assert (forall h o, (exists cls F lb, lookup_heap_obj h o = Some (Heap_OBJ cls F lb) ) 
      \/ lookup_heap_obj h o = None).
    intro h1. induction h1.  right. unfold lookup_heap_obj. auto.
    intro o1.  induction a0. case_eq ( beq_oid o1 o0). unfold lookup_heap_obj.  intro. unfold lookup_heap_obj. rewrite H3.
    rename h0 into ho. induction ho.     left. exists c. exists f. exists l1. auto. 
    intro. unfold lookup_heap_obj. rewrite H3. fold lookup_heap_obj. apply IHh1. 
    case (sf a). induction t; try (unfold erasure_obj_null; auto).

    destruct H3 with  h o0. 
    destruct H6 as [cls1]. destruct H6 as [F1]. destruct H6 as [lb1]. rewrite H6.
    remember  lb as lb'. 
    remember (fields_update F i t2) as F'. 
    assert(  (lookup_heap_obj
               (update_heap_obj h o (Heap_OBJ cls F' lb')) o0  = 
                      Some (Heap_OBJ cls1 F1 lb1)) \/ 
              (lookup_heap_obj (update_heap_obj h o (Heap_OBJ cls F' lb')) o0  = 
                      Some (Heap_OBJ cls F' lb')) /\ beq_oid o0 o = true ).
      apply lookup_updated_heap_equal with F lb; auto. rewrite <- Heqlb'. auto.
      destruct H7. unfold update_heap_obj in H7.
      fold update_heap_obj in H7. rewrite H7. auto.

      unfold update_heap_obj in H7. 
      fold update_heap_obj in H7. destruct H7. rewrite H7. apply beq_oid_equal in H8.
      rewrite H8 in H6. rewrite H6 in H11. inversion H11. subst. 
      auto.
      rewrite H6. unfold erasure_obj_null.
assert (lookup_heap_obj
    (update_heap_obj h o
       (Heap_OBJ cls (fields_update F i t2)
          lb))    o0 = None).
apply lookup_updated_heap_none; auto.
intro contra. rewrite contra in H11. rewrite <- H11 in H6.  inversion H6. 
rewrite H7. auto. auto. 
apply functional_extensionality in H3.
rewrite H3. auto. 
rewrite H3. auto.

(*field write with opaquelabeled value*)
++ subst. inversion H_erasure_r. subst.
        rewrite H_flow_r in H5. inversion H5. subst.
   +++ inversion H11. subst. rename s0 into s. rename h0 into h.
    unfold erasure_H_fun. fold erasure_H_fun. unfold return_free. fold return_free. 
    pose proof (value_is_return_free v H18). rewrite H1. 
    rewrite H17 in H13. rewrite H9. rewrite H13. unfold erasure_sigma_fun.

assert (erasure_heap h = erasure_heap
                                            (update_heap_obj h o
                                               (Heap_OBJ cls (fields_update F i v) lo))).
apply update_H_object_equal_erasure with CT F lo; auto. 
apply flow_false_trans with (join_label (current_label (SIGMA s h)) lb); auto.
apply flow_join_label with (current_label (SIGMA s h)) lb; auto.
apply join_label_commutative. 

apply flow_false_trans with (join_label (current_label (SIGMA s h)) lb); auto.
apply flow_join_label with (current_label (SIGMA s h)) lb; auto.
apply join_label_commutative. 


rewrite <- H2.


assert ( (erasure_stack s h) = erasure_stack s
        (update_heap_obj h o
           (Heap_OBJ cls (fields_update F i v) lo))).
unfold erasure_stack. induction s. auto. induction a. rename s0 into sf. 
assert (forall a, (fun x : id => erasure_obj_null (sf x) h) a = (fun x : id =>
                                                                           erasure_obj_null (sf x)
                                                                             (update_heap_obj h o
                                                                                (Heap_OBJ cls (fields_update F i v) lo))) a) .
intro a. assert (forall h o, (exists cls F lb, lookup_heap_obj h o = Some (Heap_OBJ cls F lb) ) 
      \/ lookup_heap_obj h o = None).
    intro h1. induction h1.  right. unfold lookup_heap_obj. auto.
    intro o1.  induction a0. case_eq ( beq_oid o1 o0). unfold lookup_heap_obj.  intro. unfold lookup_heap_obj. rewrite H3.
    rename h0 into ho. induction ho.     left. exists c. exists f. exists l1. auto. 
    intro. unfold lookup_heap_obj. rewrite H3. fold lookup_heap_obj. apply IHh1. 
    case (sf a). induction t; try (unfold erasure_obj_null; auto).

    destruct H3 with  h o0. 
    destruct H6 as [cls1]. destruct H6 as [F1]. destruct H6 as [lb1]. rewrite H6.
    remember  lo as lb'. 
    remember (fields_update F i v) as F'. 
    assert(  (lookup_heap_obj
               (update_heap_obj h o (Heap_OBJ cls F' lb')) o0  = 
                      Some (Heap_OBJ cls1 F1 lb1)) \/ 
              (lookup_heap_obj (update_heap_obj h o (Heap_OBJ cls F' lb')) o0  = 
                      Some (Heap_OBJ cls F' lb')) /\ beq_oid o0 o = true ).
      apply lookup_updated_heap_equal with F lo; auto. rewrite <- Heqlb'. auto.
      destruct H7. unfold update_heap_obj in H7.
      fold update_heap_obj in H7. rewrite H7. auto.

      unfold update_heap_obj in H7. 
      fold update_heap_obj in H7. destruct H7. rewrite H7. apply beq_oid_equal in H8.
      rewrite H8 in H6. rewrite H6 in H12. inversion H12. subst. 
      auto.
      rewrite H6. unfold erasure_obj_null.
assert (lookup_heap_obj
    (update_heap_obj h o
       (Heap_OBJ cls (fields_update F i v)
          lo))    o0 = None).
apply lookup_updated_heap_none; auto.
intro contra. rewrite contra in H12. rewrite <- H12 in H6.  inversion H6. 
rewrite H7. auto. auto. 
apply functional_extensionality in H3.
rewrite H3. auto. 
rewrite H3. auto.

(*if *)
- intros. inversion H_typing.  inversion H6. inversion H16.

(*sequence*)
- intros.  unfold dot_free in H_dot_free. fold dot_free in H_dot_free. auto.
  apply dot_free_if in H_dot_free. destruct H_dot_free.  inversion H_erasure_l. subst.
  + rewrite H_flow_l in H4. inversion H4.
  + subst. inversion H_reduction.  
  ++ subst. inversion H_erasure_r. subst.
        rewrite H_flow_r in H6. inversion H6. subst. 
  +++  inversion H_typing. subst. 
    assert (Config CT (erasure_H_fun t1) (SIGMA  s'0 h'0) = Config CT (erasure_H_fun s1')  (SIGMA s'1 h'1)). 
    apply IHt1 with h' s' h s T0  s1'; auto.     
    inversion H_valid_syntax. auto. apply value_is_valid_syntax. auto. apply erasure_H_context; auto. 
    auto. apply erasure_H_context; auto. 
     inversion H1. unfold erasure_H_fun. fold erasure_H_fun. subst. rewrite H5. 
    inversion H_valid_syntax. subst. 
    assert (return_free t1= return_free s1'). 
    apply erasure_H_fun_equal_return_free. auto. 
    apply valid_syntax_preservation with CT t1 (SIGMA s' h') s h T0; auto. auto. 
    case_eq (return_free t1). intro.  rewrite H7 in H3. rewrite <- H3.  
    pose proof (surface_syntax_H_erasure_dot t2 H11).
    apply erasure_H_fun_imply_return_free in H14. rewrite H14. auto. 
    apply surface_syntax_is_valid_syntax. auto.

    intro. rewrite H7 in H3. rewrite <- H3. auto. 
    subst. inversion H8 ; subst; inversion H2. 
   ++ subst. inversion H_erasure_r. subst.
        rewrite H_flow_r in H6. inversion H6. subst. 
  +++  inversion H_typing. subst. 
    assert (Config CT (erasure_H_fun t') (SIGMA  s'0 h'0) = Config CT (erasure_H_fun t')  (SIGMA s'1 h'1)). 
    rewrite H9. rewrite H12.  auto. 

    unfold erasure_H_fun. assert (return_free t1 = true). apply value_is_return_free. auto.  rewrite H3. 
    fold erasure_H_fun.
    case_eq (return_free t').  intro.  apply return_free_true_imply_erasure_H_fun_dot in H5 . rewrite H5. 
    inversion H1. subst. auto.  inversion H_valid_syntax. apply surface_syntax_is_valid_syntax. auto. 
    auto.     intro. auto. 
    
(*return *)
- intros.  unfold dot_free in H_dot_free. fold dot_free in H_dot_free. auto.
   inversion H_erasure_l. subst.
  + rewrite H_flow_l in H2. inversion H2.
  + subst. inversion H_reduction.  
  ++ subst. inversion H_erasure_r. subst.
        rewrite H_flow_r in H4. inversion H4. subst. 
  +++  inversion H_typing. subst. 
    assert (Config CT (erasure_H_fun t) (SIGMA  s'0 h'0) = Config CT (erasure_H_fun e')  (SIGMA s'1 h'1)). 
    apply IHt with h' s' h s T e'; auto.     
    inversion H_valid_syntax. auto. apply erasure_H_context; auto. 
    auto. apply erasure_H_context; auto. inversion H. subst. 
    unfold  erasure_H_fun. fold erasure_H_fun. subst. rewrite H5. 
    inversion H_valid_syntax. subst. 
    assert (return_free t= return_free e'). 
    apply erasure_H_fun_equal_return_free. auto. 
    apply valid_syntax_preservation with CT t (SIGMA s' h') s h T; auto. auto. 
    case_eq (return_free t). intro.  rewrite H9 in H3. rewrite <- H3. auto.   

    intro. rewrite H9 in H3. rewrite <- H3. auto. 
   ++ subst. inversion H6. subst.  inversion H_erasure_r. subst.
        rewrite H_flow_r in H3. inversion H3. subst. 



Admitted. 
*)







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

Lemma return_free_preserve_context : forall CT t t' s h s' h',
      dot_free t = true ->
      valid_syntax t ->
      return_free t = true ->
      forall T, has_type CT empty_context h t T -> 
      field_wfe_heap CT h -> wfe_heap CT h -> wfe_stack CT h s ->
      flow_to (current_label (SIGMA s h)) L_Label = false ->
      Config CT t (SIGMA s h) ==> Config CT t' (SIGMA s' h') ->
      flow_to (current_label (SIGMA s' h')) L_Label = false.
Proof. intros CT t t' s h s' h'.       intro H_dot_free. intro H_valid_syntax. 
  intro H_return_free. 
  intro T. intro H_typing. intro H_wfe_fields. 
  intro H_wfe_heap. intro H_wfe_stack. intro H_flow. intro H_reduction. 
  generalize dependent t'. 
  generalize dependent T.
    generalize dependent s.      generalize dependent h.
    generalize dependent s'.      generalize dependent h'.
induction t; intros; try (inversion H_reduction; subst).
(*Tvar *)
  - inversion H_typing. inversion H3.

(*Field access*)
  -  inversion H_typing. apply IHt with h s (classTy clsT) e'; auto. subst. 
      inversion H_valid_syntax. auto. 
  -  inversion H5. subst. rewrite H10. rename s0 into s. induction s.  
      unfold flow_to in H_flow.  unfold current_label in H_flow.  unfold get_stack in H_flow. 
      unfold get_current_label in H_flow. unfold L_Label in H_flow. 
      unfold subset in H_flow. inversion H_flow.
      induction a.   unfold update_current_label. 
          
          unfold current_label in H_flow.       unfold get_current_label in H_flow. 
          unfold get_stack_label in H_flow. unfold get_stack in H_flow.
         unfold current_label. unfold get_current_label. unfold get_stack_label. 
        unfold get_stack.
          assert (  flow_to (join_label lb l0)  L_Label = false).
          apply flow_join_label with l0 lb; auto. auto. 
        apply flow_transitive with l0. auto.  unfold current_label in H8. 
        unfold get_current_label in H8. unfold get_stack in H8. unfold get_stack_label in H8. auto. 

(*method e1 context*)
- inversion H_typing. apply IHt1 with h s (classTy T0) e'; auto. subst. 
      inversion H_dot_free. auto. apply dot_free_if in H1. destruct H1. rewrite H. rewrite H1. auto. 
      subst.        inversion H_valid_syntax. auto. apply value_is_valid_syntax. auto. subst.  
      inversion H_return_free.  apply return_free_if in H1. destruct H1. rewrite H. rewrite H1. auto. 
(*method e2 context*)
- inversion H_typing. apply IHt2 with h s (classTy arguT) e'; auto. subst. 
      inversion H_dot_free. auto. apply dot_free_if in H0. destruct H0. rewrite H. rewrite H0. auto. 
      subst.        inversion H_valid_syntax. auto. apply surface_syntax_is_valid_syntax. auto. subst.  
      auto. subst. inversion H_return_free.  apply return_free_if in H0. destruct H0. rewrite H. rewrite H0. auto. 
(*method normal call*)
-  inversion H6. subst. rewrite H14. rename s0 into s. induction s.  
      unfold flow_to in H_flow.  unfold current_label in H_flow.  unfold get_stack in H_flow. 
      unfold get_current_label in H_flow. unfold L_Label in H_flow. 
      unfold subset in H_flow. inversion H_flow.
      induction a.   unfold update_current_label. 
          
          unfold current_label in H_flow.       unfold get_current_label in H_flow. 
          unfold get_stack_label in H_flow. unfold get_stack in H_flow.
         unfold current_label. unfold get_current_label. unfold get_stack_label. 
        unfold get_stack. auto. 
(*method opaque call*)
-  inversion H6. subst. rewrite H14. rename s0 into s. induction s.  
      unfold flow_to in H_flow.  unfold current_label in H_flow.  unfold get_stack in H_flow. 
      unfold get_current_label in H_flow. unfold L_Label in H_flow. 
      unfold subset in H_flow. inversion H_flow.
      induction a.   unfold update_current_label. 
          
          unfold current_label in H_flow.       unfold get_current_label in H_flow. 
          unfold get_stack_label in H_flow. unfold get_stack in H_flow.
         unfold current_label. unfold get_current_label. unfold get_stack_label. 
        unfold get_stack. assert (  flow_to (join_label lb l0)  L_Label = false).
          apply flow_join_label with l0 lb; auto. auto.
(*new cls()*)
- inversion H5. subst. rewrite H11.  
         unfold current_label. unfold get_stack. 
        unfold current_label in H_flow. unfold get_stack in H_flow. auto.  
(*labelData *)
  (* context rule *)
- inversion H_typing. apply IHt with h s T0 e'; auto. subst. 
      inversion H_valid_syntax. auto. 
  (* label data *)
- auto. 

(* unlabel *)
  (* context rule *)
- inversion H_typing. apply IHt with h s (LabelelTy T) e'; auto. subst. 
      inversion H_valid_syntax. auto. 

  (* unlabel *)
-  inversion H4. subst. rewrite H7. rename s0 into s. induction s.  
      unfold flow_to in H_flow.  unfold current_label in H_flow.  unfold get_stack in H_flow. 
      unfold get_current_label in H_flow. unfold L_Label in H_flow. 
      unfold subset in H_flow. inversion H_flow.
      induction a.   unfold update_current_label. 
          
          unfold current_label in H_flow.       unfold get_current_label in H_flow. 
          unfold get_stack_label in H_flow. unfold get_stack in H_flow.
         unfold current_label. unfold get_current_label. unfold get_stack_label. 
        unfold get_stack.
          assert (  flow_to (join_label lb l0)  L_Label = false).
          apply flow_join_label with l0 lb; auto. auto.

(* Label of *)
  (* context rule *)
- inversion H_typing. apply IHt with h s (LabelelTy T0) e'; auto. subst. 
      inversion H_valid_syntax. auto. 

  (* label of  *)
- auto. 

(* unlabel opaque*)
  (* context rule *)
- inversion H_typing. apply IHt with h s  (OpaqueLabeledTy T) e'; auto. subst. 
      inversion H_valid_syntax. auto. 
  (* unlabel opaque *)
-  inversion H4. subst. rewrite H7. rename s0 into s. induction s.  
      unfold flow_to in H_flow.  unfold current_label in H_flow.  unfold get_stack in H_flow. 
      unfold get_current_label in H_flow. unfold L_Label in H_flow. 
      unfold subset in H_flow. inversion H_flow.
      induction a.   unfold update_current_label. 
          
          unfold current_label in H_flow.       unfold get_current_label in H_flow. 
          unfold get_stack_label in H_flow. unfold get_stack in H_flow.
         unfold current_label. unfold get_current_label. unfold get_stack_label. 
        unfold get_stack.
          assert (  flow_to (join_label lb l0)  L_Label = false).
          apply flow_join_label with l0 lb; auto. auto.

(* Opaque call *)
  (* context rule *)
- inversion H_typing. apply IHt with h s T0 e'; auto. subst. 
      inversion H_valid_syntax. auto. 
  (* return context rule*)
- inversion H_return_free.

  (* opaque call with value, without method call inside *)
- auto.
- inversion H_return_free.

(* assignment *)
  (* context rule *)
- inversion H_typing. inversion H5.   
  (* assignment *)
- inversion H_typing. inversion H5.   

(* Field Write *)
(*context e1 *)
- inversion H_typing. apply IHt1 with h s (classTy clsT) e1'; auto. subst. 
      inversion H_dot_free. auto. apply dot_free_if in H1. destruct H1. rewrite H. rewrite H1. auto. 
      subst.        inversion H_valid_syntax. auto. apply value_is_valid_syntax. auto. subst.  
      inversion H_return_free.  apply return_free_if in H1. destruct H1. rewrite H. rewrite H1. auto. 
(*method e2 context*)
- inversion H_typing. apply IHt2 with h s (classTy cls') e2'; auto. subst. 
      inversion H_dot_free. auto. apply dot_free_if in H0. destruct H0. rewrite H. rewrite H0. auto. 
      subst.        inversion H_valid_syntax. auto. apply surface_syntax_is_valid_syntax. auto. subst.  
      auto. subst. inversion H_return_free.  apply return_free_if in H0. destruct H0. rewrite H. rewrite H0. auto. 
(*method normal call*)
-  inversion H6. subst. rewrite H12. rename s0 into s. induction s.  
      unfold flow_to in H_flow.  unfold current_label in H_flow.  unfold get_stack in H_flow. 
      unfold get_current_label in H_flow. unfold L_Label in H_flow. 
      unfold subset in H_flow. inversion H_flow.
      induction a.   unfold update_current_label. 

      unfold current_label in H_flow.       unfold get_current_label in H_flow. 
      unfold get_stack_label in H_flow. unfold get_stack in H_flow.
      unfold current_label. unfold get_current_label. unfold get_stack_label. 
      unfold get_stack. auto. 
(*method opaque call*)
-  inversion H7. subst. rewrite H13. rename s0 into s. induction s.  
      unfold flow_to in H_flow.  unfold current_label in H_flow.  unfold get_stack in H_flow. 
      unfold get_current_label in H_flow. unfold L_Label in H_flow. 
      unfold subset in H_flow. inversion H_flow.
      induction a.   unfold update_current_label. 
          
          unfold current_label in H_flow.       unfold get_current_label in H_flow. 
          unfold get_stack_label in H_flow. unfold get_stack in H_flow.
         unfold current_label. unfold get_current_label. unfold get_stack_label. 
        unfold get_stack. assert (  flow_to (join_label lb l0)  L_Label = false).
          apply flow_join_label with l0 lb; auto. auto.

(* if statement *)
- auto. 
- auto. 

(* sequence *)
   (* context rule *)
- inversion H_typing. apply IHt1 with h s T0 s1'; auto. subst. 
      inversion H_dot_free. auto. apply dot_free_if in H1. destruct H1. rewrite H. rewrite H1. auto. 
      subst.        inversion H_valid_syntax. auto. apply value_is_valid_syntax. auto. subst.  
      inversion H_return_free.  apply return_free_if in H1. destruct H1. rewrite H. rewrite H1. auto. 
- auto. 
(* return *)
- inversion H_return_free. 
- inversion H_return_free.
Qed. 


(*
Lemma erasure_v_opa_l : forall t v0 lb, 
  return_free t = false ->
  erasure_H_fun t = v_opa_l v0 lb -> value v0 ->
  t = v_opa_l v0 lb.
Proof. induction t; intros v0 lb; intro H_return_free; intros; try (unfold erasure_H_fun in H; inversion H; fail);
try (inversion H; case_eq (return_free t); intro; rewrite H1 in H2; inversion H2);
inversion H; unfold erasure_H_fun in H; fold erasure_H_fun in H;
        case_eq (return_free t1);
        intro; try (case_eq (return_free t2);  intro; rewrite H1 in H;  rewrite H3 in H; inversion H);
        try (case_eq (return_free t2);
        intro; rewrite H1 in H; inversion H).

Qed. 

Lemma erasure_value_unlabelOpaque : forall v t, 
   valid_syntax t -> 
   value v -> return_free t = false ->
   erasure_H_fun t = unlabelOpaque v ->
   t =  unlabelOpaque v.
Proof. intros v t. intro H_valid. intros.  induction t; subst;
    try (inversion H1; case_eq (return_free t); intro; rewrite H2 in H1; inversion H1);
    try (unfold erasure_H_fun in H1; fold erasure_H_fun in H1; case_eq (return_free t); intro;  rewrite H2 in H1; inversion H1);
    try (unfold erasure_H_fun in H1; fold erasure_H_fun in H1; 
        case_eq (return_free t1); 
        intro;     try (case_eq (return_free t2); 
        intro; rewrite H2 in H1; rewrite H3 in H1; inversion H1);
        try (case_eq (return_free t2); 
        intro; rewrite H2 in H1; inversion H1)).

    inversion H_valid. inversion H; try (rewrite <- H6 in H4; 
    pose proof (erasure_H_fun_preserve_return_free_false t H5 H2); rewrite H4 in H7; 
    unfold return_free in H7; fold return_free in H7; inversion H7). 
    subst. pose proof (erasure_H_fun_preserve_return_free_false t H5 H2).
    rewrite <- H7 in H3. unfold return_free in H3. fold return_free in H3. 
    pose proof (value_is_return_free v0 H6) . rewrite H4 in H3. inversion H3.
    
    subst.  assert (t = v_opa_l v0 lb). apply erasure_v_opa_l; auto. subst.
    rewrite H7. rewrite <- H7. rewrite <- H7.  auto.  
Qed. 

Lemma erasure_value : forall v t, 
   valid_syntax t -> 
   value v -> return_free t = false ->
   erasure_H_fun t = v ->
   t = v.
Proof. intros v t. intro H_valid. intros.  induction t; subst;
    try (inversion H0; case_eq (return_free t); intro; rewrite H1 in H0; inversion H0; fail);
    try (unfold erasure_H_fun in H;  fold erasure_H_fun in H; 
    unfold return_free in H0;  fold return_free in H0;  rewrite H0 in H; inversion H);
    try (unfold erasure_H_fun in H;  fold erasure_H_fun in H);
    try (unfold return_free in H0;  fold return_free in H0);
    try (apply return_free_if_false in H0; destruct H0; try (rewrite H0 in H; inversion H);
    try (destruct H0; rewrite H0 in H; rewrite H1 in H; inversion H)).
    inversion H_valid. assert (return_free t1 = true). apply surface_syntax_is_return_free. auto. 
    rewrite H7 in H0. inversion H0. 
     destruct H0.   inversion H_valid. assert (return_free t2 = true). apply surface_syntax_is_return_free. auto. 
    rewrite H8 in H1. inversion H1. 

*)




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
induction t; intros; try (inversion H_reduction; subst).
  - inversion H_typing. inversion H4. 
  (*Field access context rule*)
  - inversion H_erasure_l. 
   + rewrite  H_flow_l in H3. inversion H3. 
   + inversion H_erasure_r. 
    ++ subst. 
     unfold erasure_L_fun. unfold erasure_H_fun. subst. 
     fold erasure_L_fun. fold erasure_H_fun.
     case_eq (return_free t). 
    +++ intro H_return_free. 
     assert (return_free (FieldAccess t i) = true). unfold return_free. fold return_free. auto. 
     assert ( flow_to (current_label (SIGMA s1 h1)) L_Label = false). 
     inversion H_typing.
     apply return_free_preserve_context with CT t e' s h (classTy clsT); auto.
     inversion H_valid_syntax. auto.  rewrite H1 in H_flow_r. inversion H_flow_r.

     +++ intro. assert (Config CT (erasure_H_fun t) (SIGMA s' h') ==l>
     Config CT (erasure_L_fun e') (SIGMA s'0 h'0)). 
     inversion H_typing.
     apply IHt with h s (SIGMA s1 h1) (SIGMA s h)  (classTy clsT) e'; auto.
     inversion H_valid_syntax. auto. apply erasure_H_context; auto. 
      apply erasure_L_context; auto.
    inversion H1. induction c2. assert (CT = c). 
    apply ct_consist with (erasure_H_fun t) t0 (SIGMA s' h') s0; auto.
    subst. rename c into CT.
    assert (Config CT (FieldAccess (erasure_H_fun t) i)  (SIGMA s' h') 
                ==> Config CT (FieldAccess t0 i) s0). apply ST_fieldRead1. auto.
    apply L_reduction with ( Config CT (FieldAccess t0 i) s0); auto.
    inversion H4. subst. apply erasure_L_context; auto. rewrite H15.
     unfold erasure_L_fun. fold erasure_L_fun. auto.
    
    subst. assert (flow_to (current_label (SIGMA s'0 h'0)) L_Label = 
                  flow_to (current_label (SIGMA s2 h0)) L_Label). 
    apply erasure_sigma_preserve_context; auto. 

    subst. assert (flow_to (current_label (SIGMA s'0 h'0)) L_Label = 
                  flow_to (current_label (SIGMA s1 h1)) L_Label). 
    apply erasure_sigma_preserve_context; auto.
    rewrite H13 in H7. rewrite H11 in H6. rewrite H7 in H6. inversion H6.  
    inversion H4.
    ++ subst.     rewrite H_flow_r in H13. inversion H13.

(*field access with obj*)
-  inversion H5.  subst. rename s0 into s. rename h0 into h.
    induction s.  
      unfold flow_to in H_flow_l.  unfold current_label in H_flow_l.  unfold get_stack in H_flow_l. 
      unfold get_current_label in H_flow_l. unfold L_Label in H_flow_l. 
      unfold subset in H_flow_l. inversion H_flow_l.

      induction a. 
          unfold current_label in H_flow_l.       unfold get_current_label in H_flow_l. 
          unfold get_stack_label in H_flow_l. unfold get_stack in H_flow_l.
          unfold current_label in H_flow_r.       unfold get_current_label in H_flow_r. 
          unfold get_stack_label in H_flow_r. unfold get_stack in H_flow_r.
          unfold update_current_label in H_flow_r. 

          assert (  flow_to (join_label lb l0)  L_Label = false).
          apply flow_join_label with l0 lb; auto. auto.  
          assert (flow_to lb l0 = false). apply flow_no_H_to_L; auto.  
           unfold current_label in H8.       unfold get_current_label in H8. 
          unfold get_stack_label in H8. unfold get_stack in H8. rewrite H0 in H8. inversion H8. 

(* method call e1  *)
-  inversion H_erasure_l. 
   + rewrite  H_flow_l in H3. inversion H3. 
   + inversion H_erasure_r. 
    ++ subst. 
     unfold erasure_L_fun. unfold erasure_H_fun. subst. 
     fold erasure_L_fun. fold erasure_H_fun.
     case_eq (return_free t1). 
    +++ intro H_return_free. 
     assert ( flow_to (current_label (SIGMA s1 h1)) L_Label = false). 
     inversion H_typing.
     apply return_free_preserve_context with CT t1 e' s h (classTy T0); auto.  
     unfold dot_free in H_dot_free. fold dot_free in H_dot_free.  apply dot_free_if in H_dot_free. 
      apply H_dot_free. inversion H_valid_syntax.  auto. apply value_is_valid_syntax. auto.  
     rewrite H in H_flow_r. inversion H_flow_r.

     +++ intro. assert (Config CT (erasure_H_fun t1) (SIGMA s' h') ==l>
     Config CT (erasure_L_fun e') (SIGMA s'0 h'0)). 
     inversion H_typing.
     apply IHt1 with h s (SIGMA s1 h1) (SIGMA s h)  (classTy T0) e'; auto.
     inversion H_valid_syntax. auto.
     unfold dot_free in H_dot_free. fold dot_free in H_dot_free.  apply dot_free_if in H_dot_free. 
     apply H_dot_free. 
     unfold dot_free in H_dot_free. fold dot_free in H_dot_free.  apply dot_free_if in H_dot_free. 
     apply H_dot_free.  inversion H_valid_syntax.  auto. apply value_is_valid_syntax. auto.  

     apply erasure_H_context; auto. 
      apply erasure_L_context; auto.
    inversion H1. induction c2. assert (CT = c). 
    apply ct_consist with (erasure_H_fun t1) t (SIGMA s' h') s0; auto.
    subst. rename c into CT.
    assert (Config CT (MethodCall (erasure_H_fun t1) i t2)  (SIGMA s' h') 
                ==> Config CT (MethodCall t i t2) s0 ). apply ST_MethodCall1. auto.
    apply L_reduction with ( Config CT (MethodCall t i t2) s0); auto.
    inversion H4. subst. apply erasure_L_context; auto. rewrite H15.
     unfold erasure_L_fun. fold erasure_L_fun. auto.
    
    subst. assert (flow_to (current_label (SIGMA s'0 h'0)) L_Label = 
                  flow_to (current_label (SIGMA s2 h0)) L_Label). 
    apply erasure_sigma_preserve_context; auto. 

    subst. assert (flow_to (current_label (SIGMA s'0 h'0)) L_Label = 
                  flow_to (current_label (SIGMA s1 h1)) L_Label). 
    apply erasure_sigma_preserve_context; auto.
    rewrite H13 in H7. rewrite H11 in H6. rewrite H7 in H6. inversion H6.  
    inversion H4.
    ++ subst.     rewrite H_flow_r in H13. inversion H13.

(* method call e2*)
-  inversion H_erasure_l. 
   + rewrite  H_flow_l in H3. inversion H3. 
   + inversion H_erasure_r. 
    ++ subst. 
     unfold erasure_L_fun. unfold erasure_H_fun. subst. 
     fold erasure_L_fun. fold erasure_H_fun. pose proof (value_is_return_free t1 H8).
     case_eq (return_free t2). 
    +++ intro H_return_free. 
     assert ( flow_to (current_label (SIGMA s1 h1)) L_Label = false). 
     inversion H_typing.
     apply return_free_preserve_context with CT t2 e' s h (classTy arguT); auto.  
     unfold dot_free in H_dot_free. fold dot_free in H_dot_free.  apply dot_free_if in H_dot_free. 
      apply H_dot_free. inversion H_valid_syntax.  auto. apply surface_syntax_is_valid_syntax. auto. auto. 
     rewrite H0 in H_flow_r. inversion H_flow_r.

     +++ intro. assert (Config CT (erasure_H_fun t2) (SIGMA s' h') ==l>
     Config CT (erasure_L_fun e') (SIGMA s'0 h'0)). 
     inversion H_typing.
     apply IHt2 with h s (SIGMA s1 h1) (SIGMA s h)  (classTy arguT) e'; auto.
     inversion H_valid_syntax. auto.
     unfold dot_free in H_dot_free. fold dot_free in H_dot_free.  apply dot_free_if in H_dot_free. 
     apply H_dot_free. 
     unfold dot_free in H_dot_free. fold dot_free in H_dot_free.  apply dot_free_if in H_dot_free. 
     apply H_dot_free.  inversion H_valid_syntax.  apply surface_syntax_is_valid_syntax. auto. auto.   

     apply erasure_H_context; auto. 
      apply erasure_L_context; auto.
    inversion H1. induction c2. assert (CT = c). 
    apply ct_consist with (erasure_H_fun t2) t (SIGMA s' h') s0; auto.
    subst. rename c into CT.
    assert (Config CT (MethodCall t1 i (erasure_H_fun t2))  (SIGMA s' h') 
                ==> Config CT (MethodCall t1 i t) s0 ). apply ST_MethodCall2; auto.
    intro t0. intros. intro contra. rewrite contra in H4. inversion H4. subst. 
    inversion H6; subst; inversion H12. subst. inversion H17. subst.
    
    pose proof (erasure_sigma_preserve_context s h s2 h0 H10). rewrite H_flow_l in H11.
    
    assert (flow_to (current_label (SIGMA s'0 h'0)) L_Label = flow_to (current_label (SIGMA
                                                                (update_current_label s2
                                                                   (join_label lb (current_label (SIGMA s2 h0))) ) (get_heap (SIGMA s2 h0)) )) L_Label).   
    apply erasure_preserve_context with t (erasure_L_fun e') CT; auto. 
    pose proof (erasure_sigma_preserve_context s1 h1 s'0 h'0 H18). rewrite H_flow_r in H13. rewrite H13 in H12.
    induction s2.  
      unfold flow_to in H11.  unfold current_label in H11.  unfold get_stack in H11. 
      unfold get_current_label in H11. unfold L_Label in H11. 
      unfold subset in H11. inversion H11.

      induction a. 
          unfold current_label in H11.       unfold get_current_label in H11. 
          unfold get_stack_label in H11. unfold get_stack in H11.
          unfold current_label in H12.       unfold get_current_label in H12. 
          unfold get_stack_label in H12. unfold get_stack in H12.
          unfold update_current_label in H12.   assert (  flow_to (join_label lb l0)  L_Label = false).
          apply flow_join_label with l0 lb; auto. rewrite H14 in H12. inversion H12.

    rewrite H.  

    apply L_reduction with ( Config CT (MethodCall t1 i t) s0); auto.
    inversion H5. subst. apply erasure_L_context; auto. 
    unfold erasure_L_fun. fold erasure_L_fun. rewrite H19. auto. 
    
    subst. assert (flow_to (current_label (SIGMA s'0 h'0)) L_Label = 
                  flow_to (current_label (SIGMA s2 h0)) L_Label). 
    apply erasure_sigma_preserve_context; auto. 

    subst. assert (flow_to (current_label (SIGMA s'0 h'0)) L_Label = 
                  flow_to (current_label (SIGMA s1 h1)) L_Label). 
    apply erasure_sigma_preserve_context; auto.
    rewrite H11 in H9. rewrite H14 in H9. rewrite H15 in H9. inversion H9.  
    inversion H5.
    ++ subst.     rewrite H_flow_r in H15. inversion H15.
(*method call normal *)
-  inversion H6.  subst. rename s0 into s. rename h0 into h.
    induction s.  
      unfold flow_to in H_flow_l.  unfold current_label in H_flow_l.  unfold get_stack in H_flow_l. 
      unfold get_current_label in H_flow_l. unfold L_Label in H_flow_l. 
      unfold subset in H_flow_l. inversion H_flow_l.

      induction a. 
          unfold current_label in H_flow_l.       unfold get_current_label in H_flow_l. 
          unfold get_stack_label in H_flow_l. unfold get_stack in H_flow_l.
          unfold current_label in H_flow_r.       unfold get_current_label in H_flow_r. 
          unfold get_stack_label in H_flow_r. unfold get_stack in H_flow_r.
          unfold update_current_label in H_flow_r. 

          rewrite H_flow_r in H_flow_l. inversion H_flow_l.
(*method call opaque *)
-  inversion H6.  subst. rename s0 into s. rename h0 into h.
    induction s.  
      unfold flow_to in H_flow_l.  unfold current_label in H_flow_l.  unfold get_stack in H_flow_l. 
      unfold get_current_label in H_flow_l. unfold L_Label in H_flow_l. 
      unfold subset in H_flow_l. inversion H_flow_l.

      induction a. 
          unfold current_label in H_flow_l.       unfold get_current_label in H_flow_l. 
          unfold get_stack_label in H_flow_l. unfold get_stack in H_flow_l.
          unfold current_label in H_flow_r.       unfold get_current_label in H_flow_r. 
          unfold get_stack_label in H_flow_r. unfold get_stack in H_flow_r.
          unfold update_current_label in H_flow_r. 

          assert (  flow_to (join_label lb l0)  L_Label = false).
          apply flow_join_label with l0 lb; auto. auto. rewrite H in H_flow_r. inversion H_flow_r.
(*new expression*)
-  inversion H5.  subst. rename s0 into s. rename h0 into h.
    induction s.  
      unfold flow_to in H_flow_l.  unfold current_label in H_flow_l.  unfold get_stack in H_flow_l. 
      unfold get_current_label in H_flow_l. unfold L_Label in H_flow_l. 
      unfold subset in H_flow_l. inversion H_flow_l.

      induction a. 
          unfold current_label in H_flow_l.       unfold get_current_label in H_flow_l. 
          unfold get_stack_label in H_flow_l. unfold get_stack in H_flow_l.
          unfold current_label in H_flow_r.       unfold get_current_label in H_flow_r. 
          unfold get_stack_label in H_flow_r. unfold get_stack in H_flow_r.
          unfold update_current_label in H_flow_r. 

          rewrite H_flow_r in H_flow_l. inversion H_flow_l.

  (*label data context rule*)
- inversion H_erasure_l. 
   + rewrite  H_flow_l in H3. inversion H3. 
   + inversion H_erasure_r. 
    ++ subst. 
     unfold erasure_L_fun. unfold erasure_H_fun. subst. 
     fold erasure_L_fun. fold erasure_H_fun.
     case_eq (return_free t). 
    +++ intro H_return_free. 
     assert (return_free (labelData t l0) = true). unfold return_free. fold return_free. auto. 
     assert ( flow_to (current_label (SIGMA s1 h1)) L_Label = false). 
     inversion H_typing.
     apply return_free_preserve_context with CT t e' s h T0; auto.
     inversion H_valid_syntax. auto.  rewrite H1 in H_flow_r. inversion H_flow_r.

     +++ intro. assert (Config CT (erasure_H_fun t) (SIGMA s' h') ==l>
     Config CT (erasure_L_fun e') (SIGMA s'0 h'0)). 
     inversion H_typing.
     apply IHt with h s (SIGMA s1 h1) (SIGMA s h)  T0 e'; auto.
     inversion H_valid_syntax. auto. apply erasure_H_context; auto. 
      apply erasure_L_context; auto.
    inversion H1. induction c2. assert (CT = c). 
    apply ct_consist with (erasure_H_fun t) t0 (SIGMA s' h') s0; auto.
    subst. rename c into CT.
    assert (Config CT (labelData (erasure_H_fun t) l0)  (SIGMA s' h') 
                ==> Config CT (labelData t0 l0) s0). apply ST_LabelData1. auto.
    apply L_reduction with ( Config CT (labelData t0 l0) s0); auto.
    inversion H4. subst. apply erasure_L_context; auto. rewrite H15.
     unfold erasure_L_fun. fold erasure_L_fun. auto.
    
    subst. assert (flow_to (current_label (SIGMA s'0 h'0)) L_Label = 
                  flow_to (current_label (SIGMA s2 h0)) L_Label). 
    apply erasure_sigma_preserve_context; auto. 

    subst. assert (flow_to (current_label (SIGMA s'0 h'0)) L_Label = 
                  flow_to (current_label (SIGMA s1 h1)) L_Label). 
    apply erasure_sigma_preserve_context; auto.
    rewrite H13 in H7. rewrite H11 in H6. rewrite H7 in H6. inversion H6.  
    inversion H4.
    ++ subst.     rewrite H_flow_r in H13. inversion H13.

(*label data*)
-  rewrite H_flow_r in H_flow_l. inversion H_flow_l.

(*unlabel e*)
- inversion H_erasure_l. 
   + rewrite  H_flow_l in H3. inversion H3. 
   + inversion H_erasure_r. 
    ++ subst. 
     unfold erasure_L_fun. unfold erasure_H_fun. subst. 
     fold erasure_L_fun. fold erasure_H_fun.
     case_eq (return_free t). 
    +++ intro H_return_free. 
     assert (return_free (unlabel t) = true). unfold return_free. fold return_free. auto. 
     assert ( flow_to (current_label (SIGMA s1 h1)) L_Label = false). 
     inversion H_typing.
     apply return_free_preserve_context with CT t e' s h (LabelelTy T); auto.
     inversion H_valid_syntax. auto.  rewrite H1 in H_flow_r. inversion H_flow_r.

     +++ intro. assert (Config CT (erasure_H_fun t) (SIGMA s' h') ==l>
     Config CT (erasure_L_fun e') (SIGMA s'0 h'0)). 
     inversion H_typing.
     apply IHt with h s (SIGMA s1 h1) (SIGMA s h)  (LabelelTy T) e'; auto.
     inversion H_valid_syntax. auto. apply erasure_H_context; auto. 
      apply erasure_L_context; auto.
    inversion H1. induction c2. assert (CT = c). 
    apply ct_consist with (erasure_H_fun t) t0 (SIGMA s' h') s0; auto.
    subst. rename c into CT.
    assert (Config CT (unlabel (erasure_H_fun t))  (SIGMA s' h') 
                ==> Config CT (unlabel t0) s0). apply ST_unlabel1. auto.
    apply L_reduction with ( Config CT (unlabel t0) s0); auto.
    inversion H4. subst. apply erasure_L_context; auto. rewrite H15.
     unfold erasure_L_fun. fold erasure_L_fun. auto.
    
    subst. assert (flow_to (current_label (SIGMA s'0 h'0)) L_Label = 
                  flow_to (current_label (SIGMA s2 h0)) L_Label). 
    apply erasure_sigma_preserve_context; auto. 

    subst. assert (flow_to (current_label (SIGMA s'0 h'0)) L_Label = 
                  flow_to (current_label (SIGMA s1 h1)) L_Label). 
    apply erasure_sigma_preserve_context; auto.
    rewrite H13 in H7. rewrite H11 in H6. rewrite H7 in H6. inversion H6.  
    inversion H4.
    ++ subst.     rewrite H_flow_r in H13. inversion H13.

(* unlabel v*)
-  inversion H4.  subst. rename s0 into s. rename h0 into h.
    induction s.  
      unfold flow_to in H_flow_l.  unfold current_label in H_flow_l.  unfold get_stack in H_flow_l. 
      unfold get_current_label in H_flow_l. unfold L_Label in H_flow_l. 
      unfold subset in H_flow_l. inversion H_flow_l.

      induction a. 
          unfold current_label in H_flow_l.       unfold get_current_label in H_flow_l. 
          unfold get_stack_label in H_flow_l. unfold get_stack in H_flow_l.
          unfold current_label in H_flow_r.       unfold get_current_label in H_flow_r. 
          unfold get_stack_label in H_flow_r. unfold get_stack in H_flow_r.
          unfold update_current_label in H_flow_r. 

          assert (  flow_to (join_label lb l0)  L_Label = false).
          apply flow_join_label with l0 lb; auto. auto. rewrite H in H_flow_r. inversion H_flow_r.

(*labelOf e*)
- inversion H_erasure_l. 
   + rewrite  H_flow_l in H3. inversion H3. 
   + inversion H_erasure_r. 
    ++ subst. 
     unfold erasure_L_fun. unfold erasure_H_fun. subst. 
     fold erasure_L_fun. fold erasure_H_fun.
     case_eq (return_free t). 
    +++ intro H_return_free. 
     assert (return_free (labelOf t) = true). unfold return_free. fold return_free. auto. 
     assert ( flow_to (current_label (SIGMA s1 h1)) L_Label = false). 
     inversion H_typing.
     apply return_free_preserve_context with CT t e' s h (LabelelTy T0); auto.
     inversion H_valid_syntax. auto.  rewrite H1 in H_flow_r. inversion H_flow_r.

     +++ intro. assert (Config CT (erasure_H_fun t) (SIGMA s' h') ==l>
     Config CT (erasure_L_fun e') (SIGMA s'0 h'0)). 
     inversion H_typing.
     apply IHt with h s (SIGMA s1 h1) (SIGMA s h)  (LabelelTy T0) e'; auto.
     inversion H_valid_syntax. auto. apply erasure_H_context; auto. 
      apply erasure_L_context; auto.
    inversion H1. induction c2. assert (CT = c). 
    apply ct_consist with (erasure_H_fun t) t0 (SIGMA s' h') s0; auto.
    subst. rename c into CT.
    assert (Config CT ( labelOf (erasure_H_fun t))  (SIGMA s' h') 
                ==> Config CT (labelOf t0) s0). apply ST_labelof1. auto.
    apply L_reduction with ( Config CT (labelOf t0) s0); auto.
    inversion H4. subst. apply erasure_L_context; auto. rewrite H15.
     unfold erasure_L_fun. fold erasure_L_fun. auto.
    
    subst. assert (flow_to (current_label (SIGMA s'0 h'0)) L_Label = 
                  flow_to (current_label (SIGMA s2 h0)) L_Label). 
    apply erasure_sigma_preserve_context; auto. 

    subst. assert (flow_to (current_label (SIGMA s'0 h'0)) L_Label = 
                  flow_to (current_label (SIGMA s1 h1)) L_Label). 
    apply erasure_sigma_preserve_context; auto.
    rewrite H13 in H7. rewrite H11 in H6. rewrite H7 in H6. inversion H6.  
    inversion H4.
    ++ subst.     rewrite H_flow_r in H13. inversion H13.

(*labelof *)
- rewrite H_flow_r in H_flow_l. inversion H_flow_l.

(*unlabelOpaque e*)
- inversion H_erasure_l. 
   + rewrite  H_flow_l in H3. inversion H3. 
   + inversion H_erasure_r. 
    ++ subst. 
     unfold erasure_L_fun. unfold erasure_H_fun. subst. 
     fold erasure_L_fun. fold erasure_H_fun.
     case_eq (return_free t). 
    +++ intro H_return_free. 
     assert (return_free (unlabelOpaque t) = true). unfold return_free. fold return_free. auto. 
     assert ( flow_to (current_label (SIGMA s1 h1)) L_Label = false). 
     inversion H_typing.
     apply return_free_preserve_context with CT t e' s h (OpaqueLabeledTy T); auto.
     inversion H_valid_syntax. auto.  rewrite H1 in H_flow_r. inversion H_flow_r.

     +++ intro. assert (Config CT (erasure_H_fun t) (SIGMA s' h') ==l>
     Config CT (erasure_L_fun e') (SIGMA s'0 h'0)). 
     inversion H_typing.
     apply IHt with h s (SIGMA s1 h1) (SIGMA s h) (OpaqueLabeledTy T) e'; auto.
     inversion H_valid_syntax. auto. apply erasure_H_context; auto. 
      apply erasure_L_context; auto.
    inversion H1. induction c2. assert (CT = c). 
    apply ct_consist with (erasure_H_fun t) t0 (SIGMA s' h') s0; auto.
    subst. rename c into CT.
    assert (Config CT ( unlabelOpaque (erasure_H_fun t))  (SIGMA s' h') 
                ==> Config CT (unlabelOpaque t0) s0). apply ST_unlabel_opaque1. auto.
    apply L_reduction with ( Config CT (unlabelOpaque t0) s0); auto.
    inversion H4. subst. apply erasure_L_context; auto. rewrite H15.
     unfold erasure_L_fun. fold erasure_L_fun. auto.
    
    subst. assert (flow_to (current_label (SIGMA s'0 h'0)) L_Label = 
                  flow_to (current_label (SIGMA s2 h0)) L_Label). 
    apply erasure_sigma_preserve_context; auto. 

    subst. assert (flow_to (current_label (SIGMA s'0 h'0)) L_Label = 
                  flow_to (current_label (SIGMA s1 h1)) L_Label). 
    apply erasure_sigma_preserve_context; auto.
    rewrite H13 in H7. rewrite H11 in H6. rewrite H7 in H6. inversion H6.  
    inversion H4.
    ++ subst.     rewrite H_flow_r in H13. inversion H13.

(*unlabelOpaque v*)
-  inversion H4.  subst. rename s0 into s. rename h0 into h.
    induction s.  
      unfold flow_to in H_flow_l.  unfold current_label in H_flow_l.  unfold get_stack in H_flow_l. 
      unfold get_current_label in H_flow_l. unfold L_Label in H_flow_l. 
      unfold subset in H_flow_l. inversion H_flow_l.

      induction a. 
          unfold current_label in H_flow_l.       unfold get_current_label in H_flow_l. 
          unfold get_stack_label in H_flow_l. unfold get_stack in H_flow_l.
          unfold current_label in H_flow_r.       unfold get_current_label in H_flow_r. 
          unfold get_stack_label in H_flow_r. unfold get_stack in H_flow_r.
          unfold update_current_label in H_flow_r. 

          assert (  flow_to (join_label lb l0)  L_Label = false).
          apply flow_join_label with l0 lb; auto. auto. rewrite H in H_flow_r. inversion H_flow_r.

(*opaque call e*)
- inversion H_erasure_l. 
   + rewrite  H_flow_l in H3. inversion H3. 
   + inversion H_erasure_r. 
    ++ subst. 
     unfold erasure_L_fun. unfold erasure_H_fun. subst. 
     fold erasure_L_fun. fold erasure_H_fun.
     case_eq (return_free t). 
    +++ intro H_return_free. 
     assert (return_free (opaqueCall t) = true). unfold return_free. fold return_free. auto. 
     assert ( flow_to (current_label (SIGMA s1 h1)) L_Label = false). 
     inversion H_typing.
     apply return_free_preserve_context with CT t e' s h T0; auto.
     inversion H_valid_syntax. auto.  rewrite H14 in H0. inversion H0.

     +++ intro. assert (Config CT (erasure_H_fun t) (SIGMA s' h') ==l>
     Config CT (erasure_L_fun e') (SIGMA s'0 h'0)). 
     inversion H_typing.
     apply IHt with h s (SIGMA s1 h1) (SIGMA s h) T0 e'; auto.
     inversion H_valid_syntax. auto. apply erasure_H_context; auto. 
      apply erasure_L_context; auto.
    inversion H0. induction c2. assert (CT = c). 
    apply ct_consist with (erasure_H_fun t) t0 (SIGMA s' h') s0; auto.
    subst. rename c into CT.
    assert (Config CT ( opaqueCall (erasure_H_fun t))  (SIGMA s' h') 
                ==> Config CT (opaqueCall t0) s0). apply ST_opaquecall1. auto.
    intro v. intro. intro contra.   apply erasure_H_fun_preserve_return_free_false in H.

    rewrite contra in H. unfold return_free in H. 
    rewrite contra in H2. inversion H2. subst. inversion H6; subst; inversion H8.
    subst. inversion H15. subst. 

    subst. assert (flow_to (current_label (SIGMA (lsf :: s'1) h0)) L_Label = 
                  flow_to (current_label (SIGMA s h)) L_Label). 
    apply erasure_sigma_preserve_context; auto. 

    subst. assert (flow_to (current_label (SIGMA s'0 h'0)) L_Label = 
                  flow_to (current_label (SIGMA s1 h1)) L_Label). 
    apply erasure_sigma_preserve_context; auto. 
    inversion H4. subst. 
    subst. assert (flow_to (current_label (SIGMA s'0 h'0)) L_Label = 
                  flow_to (current_label (SIGMA
                           (update_current_label s'1
                              (join_label (get_stack_label lsf) (get_current_label s'1))) h0)) L_Label). 
    apply erasure_sigma_preserve_context; auto. rewrite H14 in H8. rewrite H8 in H10. 
    rewrite H3 in H7. induction lsf.   
    unfold current_label in H7.       unfold get_current_label in H7. 
    unfold get_stack_label in H7. unfold get_stack in H7.
    unfold current_label in H10.  unfold get_stack in H10.   induction s'1. intuition.

    unfold get_stack_label in H10.  induction a.   unfold update_current_label in H10.     
    unfold get_current_label in H10. unfold get_stack_label in H10. 
    assert (flow_to (join_label l0 l1) L_Label = false). 
    apply flow_join_label with l0 l1; auto. apply join_label_commutative. auto. 
    rewrite <- H10 in H11. inversion H11.
    subst.   assert (flow_to (current_label (SIGMA s'0 h'0)) L_Label = 
                  flow_to (current_label (SIGMA
                           (update_current_label s'1
                              (join_label (get_stack_label lsf) (get_current_label s'1))) h0)) L_Label). 
    apply erasure_sigma_preserve_context; auto. rewrite H14 in H8. rewrite H8 in H10. 
    rewrite H3 in H7. induction lsf.   
    unfold current_label in H7.       unfold get_current_label in H7. 
    unfold get_stack_label in H7. unfold get_stack in H7.
    unfold current_label in H10.  unfold get_stack in H10.   induction s'1. intuition.

    unfold get_stack_label in H10.  induction a.   unfold update_current_label in H10.     
    unfold get_current_label in H10. unfold get_stack_label in H10. 
    assert (flow_to (join_label l0 l1) L_Label = false). 
    apply flow_join_label with l0 l1; auto. apply join_label_commutative. auto. 
    rewrite <- H10 in H11. inversion H11.
    inversion H_valid_syntax. auto. auto. 


    apply L_reduction with ( Config CT (opaqueCall t0) s0); auto.
    inversion H4. subst. apply erasure_L_context; auto. rewrite H16.
     unfold erasure_L_fun. fold erasure_L_fun. auto.
    
    subst. assert (flow_to (current_label (SIGMA s'0 h'0)) L_Label = 
                  flow_to (current_label (SIGMA s2 h0)) L_Label). 
    apply erasure_sigma_preserve_context; auto. 

    subst. assert (flow_to (current_label (SIGMA s'0 h'0)) L_Label = 
                  flow_to (current_label (SIGMA s1 h1)) L_Label). 
    apply erasure_sigma_preserve_context; auto.
    rewrite H12 in H7. rewrite H14 in H8. rewrite H7 in H8. inversion H8.  
    inversion H4.
    ++ subst.     rewrite H_flow_r in H14. inversion H14.

(* opaque (return v) *)
- inversion H_erasure_l. 
   + rewrite  H_flow_l in H3. inversion H3. 
   + inversion H_erasure_r. 
    ++ subst. 
     unfold erasure_L_fun. unfold erasure_H_fun. subst. 
     fold erasure_L_fun. fold erasure_H_fun.
     assert (return_free (Return e) = false). unfold return_free.  auto. 
    rewrite H. 
    case_eq (return_free e). 
    +++ intro H_return_free. 
     assert ( flow_to (current_label (SIGMA s1 h1)) L_Label = false). 
     inversion H_typing.
     apply return_free_preserve_context with CT e e' s h T0; auto.
     inversion H_valid_syntax. inversion H10. auto. inversion H6. auto. 
      rewrite H1 in H_flow_r. inversion H_flow_r.
     +++ intro. assert (Config CT (erasure_H_fun (Return e)) (SIGMA s' h') ==l>
     Config CT (erasure_L_fun (Return e')) (SIGMA s'0 h'0)). 
     inversion H_typing.
     apply IHt with h s (SIGMA s1 h1) (SIGMA s h) T0 (Return e'); auto.
     inversion H_valid_syntax. auto. apply erasure_H_context; auto. 
     apply ST_return1; auto.   apply erasure_L_context; auto.
    inversion H2. induction c2. assert (CT = c). 
    apply ct_consist with (erasure_H_fun (Return e)) t (SIGMA s' h') s0; auto.
    subst. rename c into CT.
    assert (Config CT ( opaqueCall (erasure_H_fun (Return e)))  (SIGMA s' h') 
                ==> Config CT (opaqueCall t) s0). apply ST_opaquecall1. auto.
    intro v. intro. intro contra.  unfold erasure_H_fun in contra. 
    fold erasure_H_fun in contra. rewrite H1 in contra. inversion contra.
    assert (erasure_H_fun (Return e) = Return v).
    unfold erasure_H_fun. fold erasure_H_fun. rewrite H1. auto. 
    rewrite H7 in H4. inversion H4. inversion H6; try (rewrite <-H18 in H11; inversion H11);  
    try (rewrite <-H19 in H11; inversion H11). subst. inversion H18. subst. 


    pose proof (erasure_sigma_preserve_context s h (lsf :: s'1) h0 H8). rewrite H_flow_l in H9.
    assert (flow_to (current_label (SIGMA s'0 h'0)) L_Label = flow_to (current_label (SIGMA
                                                                (update_current_label s'1
                                                                   (join_label  (get_current_label (lsf :: s'1)) (get_current_label s'1)) ) h0 )) L_Label).   
    apply erasure_preserve_context with (erasure_H_fun e) (erasure_L_fun (Return e')) CT; auto. 
    pose proof (erasure_sigma_preserve_context s1 h1 s'0 h'0 H16). rewrite H_flow_r in H11. rewrite H11 in H10.
    induction lsf. induction s'1. intuition.  

      induction a. 
          unfold current_label in H9.       unfold get_current_label in H9. 
          unfold get_stack_label in H9. unfold get_stack in H9.
          unfold current_label in H10.       unfold get_current_label in H10. 
          unfold get_stack_label in H10. unfold get_stack in H10.
          unfold update_current_label in H10.   assert (  flow_to (join_label l1 l0)  L_Label = false).
          apply flow_join_label with l0 l1; auto. assert ((join_label l1 l0) = (join_label l0 l1)).
          apply join_label_commutative; auto. rewrite H14 in H12.  rewrite H12 in H10. inversion H10.
    auto. 
    apply L_reduction with ( Config CT (opaqueCall t) s0); auto. 
    unfold erasure_H_fun in H6. fold erasure_H_fun in H6. rewrite H1 in H6. auto. 
    inversion H5. subst. apply erasure_L_context; auto. rewrite H17.
     unfold erasure_L_fun. fold erasure_L_fun. auto.
    
    subst. assert (flow_to (current_label (SIGMA s'0 h'0)) L_Label = 
                  flow_to (current_label (SIGMA s2 h0)) L_Label). 
    apply erasure_sigma_preserve_context; auto. 

    subst. assert (flow_to (current_label (SIGMA s'0 h'0)) L_Label = 
                  flow_to (current_label (SIGMA s1 h1)) L_Label). 
    apply erasure_sigma_preserve_context; auto.
    rewrite H13 in H9. rewrite H12 in H7. rewrite H7 in H9. inversion H9.  
    inversion H5.
    ++ subst.     rewrite H_flow_r in H13. inversion H13.
(*v_opa_l*)
- rewrite H_flow_l in H_flow_r. inversion H_flow_r.
(*opaqueCall (Return v)*) 
-inversion H4. subst. 
  inversion H_erasure_l. 
   + rewrite  H_flow_l in H2. inversion H2. 
   + inversion H_erasure_r. 
    ++ subst. assert (return_free (Return v) = false).
      unfold return_free. auto. unfold  erasure_H_fun. rewrite H. 
      fold  erasure_H_fun. assert (return_free v = true). apply value_is_return_free. auto. 
      rewrite H0. unfold erasure_L_fun. fold erasure_L_fun. rewrite  H2.
      rewrite H10. unfold erasure_sigma_fun. unfold erasure_stack. fold erasure_stack.
      induction lsf. 
      assert (Config CT (opaqueCall (Return dot))
                      (SIGMA (Labeled_frame l0 (fun x : id => erasure_obj_null (s x) h0) :: s')
                         (erasure_heap h0)) 
          ==> (Config CT (v_opa_l dot l0) (SIGMA s' (erasure_heap h0))) ).
      apply ST_opaquecall_return2 with (Labeled_frame l0 (fun x : id => erasure_obj_null (s x) h0) :: s')
                        (erasure_heap h0) s' (Labeled_frame l0 (fun x : id => erasure_obj_null (s x) h0)); auto.
      assert (Config CT (v_opa_l dot l0) (SIGMA s' (erasure_heap h0)) =e=> 
            (Config CT (v_opa_l dot (current_label (SIGMA (Labeled_frame l0 s :: s') h0)))
                      (SIGMA s'1 h'0))).
      rewrite H19. apply erasure_L_context; auto.
      unfold erasure_L_fun. 
      unfold current_label in H2. unfold get_stack in H2. unfold get_current_label in H2. 
      unfold get_stack_label in H2. rewrite H2. unfold current_label. 
      unfold get_stack. unfold get_current_label.
      unfold get_stack_label. auto. 
      unfold erasure_sigma_fun.



  assert (  (erasure_stack s' h0)  = (erasure_stack s' (erasure_heap h0))).
  apply multi_erasure_stack_helper with CT. auto. rewrite H3.
  pose proof (multi_erasure_heap_equal h0). rewrite H5. auto.
  apply L_reduction with ( Config CT (v_opa_l dot l0) (SIGMA s' (erasure_heap h0))); auto. 

 ++ subst. 
    rewrite H14 in H_flow_r. inversion H_flow_r.

(*assignment *)
- inversion H_typing. inversion H5.

- inversion H_typing. inversion H5.

(* field write  *)
-  inversion H_erasure_l. 
   + rewrite  H_flow_l in H3. inversion H3. 
   + inversion H_erasure_r. 
    ++ subst. 
     unfold erasure_L_fun. unfold erasure_H_fun. subst. 
     fold erasure_L_fun. fold erasure_H_fun.
     case_eq (return_free t1). 
    +++ intro H_return_free. 
     assert ( flow_to (current_label (SIGMA s1 h1)) L_Label = false). 
     inversion H_typing.
     apply return_free_preserve_context with CT t1 e1' s h (classTy clsT); auto.  
     unfold dot_free in H_dot_free. fold dot_free in H_dot_free.  apply dot_free_if in H_dot_free. 
      apply H_dot_free. inversion H_valid_syntax.  auto. apply value_is_valid_syntax. auto.  
     rewrite H in H_flow_r. inversion H_flow_r.

     +++ intro. assert (Config CT (erasure_H_fun t1) (SIGMA s' h') ==l>
     Config CT (erasure_L_fun e1') (SIGMA s'0 h'0)). 
     inversion H_typing.
     apply IHt1 with h s (SIGMA s1 h1) (SIGMA s h)  (classTy clsT) e1'; auto.
     inversion H_valid_syntax. auto.
     unfold dot_free in H_dot_free. fold dot_free in H_dot_free.  apply dot_free_if in H_dot_free. 
     apply H_dot_free. 
     unfold dot_free in H_dot_free. fold dot_free in H_dot_free.  apply dot_free_if in H_dot_free. 
     apply H_dot_free.  inversion H_valid_syntax.  auto. apply value_is_valid_syntax. auto.  

     apply erasure_H_context; auto. 
      apply erasure_L_context; auto.
    inversion H1. induction c2. assert (CT = c). 
    apply ct_consist with (erasure_H_fun t1) t (SIGMA s' h') s0; auto.
    subst. rename c into CT.
    assert (Config CT (FieldWrite (erasure_H_fun t1) i t2)  (SIGMA s' h') 
                ==> Config CT (FieldWrite t i t2) s0 ). apply ST_fieldWrite1. auto.
    apply L_reduction with ( Config CT (FieldWrite t i t2) s0); auto.
    inversion H4. subst. apply erasure_L_context; auto. rewrite H15.
     unfold erasure_L_fun. fold erasure_L_fun. auto.
    
    subst. assert (flow_to (current_label (SIGMA s'0 h'0)) L_Label = 
                  flow_to (current_label (SIGMA s2 h0)) L_Label). 
    apply erasure_sigma_preserve_context; auto. 

    subst. assert (flow_to (current_label (SIGMA s'0 h'0)) L_Label = 
                  flow_to (current_label (SIGMA s1 h1)) L_Label). 
    apply erasure_sigma_preserve_context; auto.
    rewrite H13 in H7. rewrite H11 in H6. rewrite H7 in H6. inversion H6.  
    inversion H4.
    ++ subst.     rewrite H_flow_r in H13. inversion H13.

(* Field write e2*)
-  inversion H_erasure_l. 
   + rewrite  H_flow_l in H3. inversion H3. 
   + inversion H_erasure_r. 
    ++ subst. 
     unfold erasure_L_fun. unfold erasure_H_fun. subst. 
     fold erasure_L_fun. fold erasure_H_fun. pose proof (value_is_return_free t1 H7).
     case_eq (return_free t2). 
    +++ intro H_return_free. 
     assert ( flow_to (current_label (SIGMA s1 h1)) L_Label = false). 
     inversion H_typing.
     apply return_free_preserve_context with CT t2 e2' s h (classTy cls'); auto.  
     unfold dot_free in H_dot_free. fold dot_free in H_dot_free.  apply dot_free_if in H_dot_free. 
      apply H_dot_free. inversion H_valid_syntax.  auto. apply surface_syntax_is_valid_syntax. auto. auto. 
     rewrite H0 in H_flow_r. inversion H_flow_r.

     +++ intro. assert (Config CT (erasure_H_fun t2) (SIGMA s' h') ==l>
     Config CT (erasure_L_fun e2') (SIGMA s'0 h'0)). 
     inversion H_typing.
     apply IHt2 with h s (SIGMA s1 h1) (SIGMA s h)  (classTy cls') e2'; auto.
     inversion H_valid_syntax. auto.
     unfold dot_free in H_dot_free. fold dot_free in H_dot_free.  apply dot_free_if in H_dot_free. 
     apply H_dot_free. 
     unfold dot_free in H_dot_free. fold dot_free in H_dot_free.  apply dot_free_if in H_dot_free. 
     apply H_dot_free.  inversion H_valid_syntax.  apply surface_syntax_is_valid_syntax. auto. auto.   

     apply erasure_H_context; auto. 
      apply erasure_L_context; auto.
    inversion H1. induction c2. assert (CT = c). 
    apply ct_consist with (erasure_H_fun t2) t (SIGMA s' h') s0; auto.
    subst. rename c into CT.
    assert (Config CT (FieldWrite t1 i (erasure_H_fun t2))  (SIGMA s' h') 
                ==> Config CT (FieldWrite t1 i t) s0 ). apply ST_fieldWrite2; auto.
    intro t0. intros. intro contra. rewrite contra in H4. inversion H4. subst. 
    inversion H6; subst; inversion H12. subst. inversion H17. subst.
    
    pose proof (erasure_sigma_preserve_context s h s2 h0 H10). rewrite H_flow_l in H11.
    assert (flow_to (current_label (SIGMA s'0 h'0)) L_Label = flow_to (current_label (SIGMA
                                                                (update_current_label s2
                                                                   (join_label lb (current_label (SIGMA s2 h0))) ) (get_heap (SIGMA s2 h0)) )) L_Label).   
    apply erasure_preserve_context with t (erasure_L_fun e2') CT; auto. 
    pose proof (erasure_sigma_preserve_context s1 h1 s'0 h'0 H18). rewrite H_flow_r in H13. rewrite H13 in H12.
    induction s2.  
      unfold flow_to in H11.  unfold current_label in H11.  unfold get_stack in H11. 
      unfold get_current_label in H11. unfold L_Label in H11. 
      unfold subset in H11. inversion H11.

      induction a. 
          unfold current_label in H11.       unfold get_current_label in H11. 
          unfold get_stack_label in H11. unfold get_stack in H11.
          unfold current_label in H12.       unfold get_current_label in H12. 
          unfold get_stack_label in H12. unfold get_stack in H12.
          unfold update_current_label in H12.   assert (  flow_to (join_label lb l0)  L_Label = false).
          apply flow_join_label with l0 lb; auto. rewrite H14 in H12. inversion H12.


    rewrite H.  

    apply L_reduction with ( Config CT (FieldWrite t1 i t) s0); auto.
    inversion H5. subst. apply erasure_L_context; auto. 
    unfold erasure_L_fun. fold erasure_L_fun. rewrite H19. auto. 
    
    subst. assert (flow_to (current_label (SIGMA s'0 h'0)) L_Label = 
                  flow_to (current_label (SIGMA s2 h0)) L_Label). 
    apply erasure_sigma_preserve_context; auto. 

    subst. assert (flow_to (current_label (SIGMA s'0 h'0)) L_Label = 
                  flow_to (current_label (SIGMA s1 h1)) L_Label). 
    apply erasure_sigma_preserve_context; auto.
    rewrite H11 in H9. rewrite H14 in H9. rewrite H15 in H9. inversion H9.  
    inversion H5.
    ++ subst.     rewrite H_flow_r in H15. inversion H15.
(*field write normal *)
-  inversion H6.  subst. rename s0 into s. rename h0 into h.
    induction s.  
      unfold flow_to in H_flow_l.  unfold current_label in H_flow_l.  unfold get_stack in H_flow_l. 
      unfold get_current_label in H_flow_l. unfold L_Label in H_flow_l. 
      unfold subset in H_flow_l. inversion H_flow_l.

      induction a. 
          unfold current_label in H_flow_l.       unfold get_current_label in H_flow_l. 
          unfold get_stack_label in H_flow_l. unfold get_stack in H_flow_l.
          unfold current_label in H_flow_r.       unfold get_current_label in H_flow_r. 
          unfold get_stack_label in H_flow_r. unfold get_stack in H_flow_r.
          unfold update_current_label in H_flow_r. 

          rewrite H_flow_r in H_flow_l. inversion H_flow_l.
(*field write opaque *)
-  inversion H7.  subst. rename s0 into s. rename h0 into h.
    induction s.  
      unfold flow_to in H_flow_l.  unfold current_label in H_flow_l.  unfold get_stack in H_flow_l. 
      unfold get_current_label in H_flow_l. unfold L_Label in H_flow_l. 
      unfold subset in H_flow_l. inversion H_flow_l.

      induction a. 
          unfold current_label in H_flow_l.       unfold get_current_label in H_flow_l. 
          unfold get_stack_label in H_flow_l. unfold get_stack in H_flow_l.
          unfold current_label in H_flow_r.       unfold get_current_label in H_flow_r. 
          unfold get_stack_label in H_flow_r. unfold get_stack in H_flow_r.
          unfold update_current_label in H_flow_r. 

          assert (  flow_to (join_label lb l0)  L_Label = false).
          apply flow_join_label with l0 lb; auto. auto. rewrite H_flow_l in H_flow_r. inversion H_flow_r.

(* if  *)
- inversion H7. subst. rewrite H_flow_l in H_flow_r. inversion H_flow_r.

- inversion H7. subst. rewrite H_flow_l in H_flow_r. inversion H_flow_r.

(*sequence *)
- inversion H_erasure_l. 
   + rewrite  H_flow_l in H3. inversion H3. 
   + inversion H_erasure_r. 
    ++ subst. 
     unfold erasure_L_fun. unfold erasure_H_fun. subst. 
     fold erasure_L_fun. fold erasure_H_fun.
     case_eq (return_free t1). 
    +++ intro H_return_free. 
     assert ( flow_to (current_label (SIGMA s1 h1)) L_Label = false). 
     inversion H_typing.
     apply return_free_preserve_context with CT t1 s1' s h T0; auto.  
     unfold dot_free in H_dot_free. fold dot_free in H_dot_free.  apply dot_free_if in H_dot_free. 
      apply H_dot_free. inversion H_valid_syntax.  auto. apply value_is_valid_syntax. auto.  
     rewrite H in H_flow_r. inversion H_flow_r.

     +++ intro. assert (Config CT (erasure_H_fun t1) (SIGMA s' h') ==l>
     Config CT (erasure_L_fun s1') (SIGMA s'0 h'0)). 
     inversion H_typing.
     apply IHt1 with h s (SIGMA s1 h1) (SIGMA s h) T0 s1'; auto.
     inversion H_valid_syntax. auto.
     unfold dot_free in H_dot_free. fold dot_free in H_dot_free.  apply dot_free_if in H_dot_free. 
     apply H_dot_free. 
     unfold dot_free in H_dot_free. fold dot_free in H_dot_free.  apply dot_free_if in H_dot_free. 
     apply H_dot_free.  inversion H_valid_syntax.  auto. apply value_is_valid_syntax. auto.  

     apply erasure_H_context; auto. 
      apply erasure_L_context; auto.
    inversion H1. induction c2. assert (CT = c). 
    apply ct_consist with (erasure_H_fun t1) t (SIGMA s' h') s0; auto.
    subst. rename c into CT.
    assert (Config CT (Sequence (erasure_H_fun t1) t2)  (SIGMA s' h') 
                ==> Config CT (Sequence t t2) s0 ). apply ST_seq1. auto.
    apply L_reduction with ( Config CT (Sequence t t2) s0); auto.
    inversion H4. subst. apply erasure_L_context; auto. rewrite H15.
     unfold erasure_L_fun. fold erasure_L_fun. auto.

      subst. assert (flow_to (current_label (SIGMA s'0 h'0)) L_Label = 
                  flow_to (current_label (SIGMA s2 h0)) L_Label). 
    apply erasure_sigma_preserve_context; auto. 

    subst. assert (flow_to (current_label (SIGMA s'0 h'0)) L_Label = 
                  flow_to (current_label (SIGMA s1 h1)) L_Label). 
    apply erasure_sigma_preserve_context; auto.
    rewrite H13 in H7. rewrite H11 in H6. rewrite H7 in H6. inversion H6.  
    inversion H4.
    ++ subst.     rewrite H_flow_r in H13. inversion H13.

- rewrite H_flow_r in H_flow_l. inversion H_flow_l. 

(*Return *)
- inversion H_erasure_l. 
   + rewrite  H_flow_l in H3. inversion H3. 
   + inversion H_erasure_r. 
    ++ subst. 
     unfold erasure_L_fun. unfold erasure_H_fun. subst. 
     fold erasure_L_fun. fold erasure_H_fun.
     case_eq (return_free t). 
    +++ intro H_return_free. 
     assert ( flow_to (current_label (SIGMA s1 h1)) L_Label = false). 
     inversion H_typing.
     apply return_free_preserve_context with CT t e' s h T; auto.  
     inversion H_valid_syntax.  auto. rewrite H in H13. inversion H13. 

     +++ intro. assert (Config CT (erasure_H_fun t) (SIGMA s' h') ==l>
     Config CT (erasure_L_fun e') (SIGMA s'0 h'0)). 
     inversion H_typing.
     apply IHt with h s (SIGMA s1 h1) (SIGMA s h) T e'; auto. 
     inversion H_valid_syntax.  auto.


     apply erasure_H_context; auto. 
      apply erasure_L_context; auto.
    inversion H1. induction c2. assert (CT = c). 
    apply ct_consist with (erasure_H_fun t) t0 (SIGMA s' h') s0; auto.
    subst. rename c into CT.
    assert (Config CT (Return (erasure_H_fun t))  (SIGMA s' h') 
                ==> Config CT (Return t0 ) s0 ). apply ST_return1. auto.
    apply L_reduction with ( Config CT (Return t0) s0); auto.
    inversion H4. subst. apply erasure_L_context; auto. rewrite H15.
     unfold erasure_L_fun. fold erasure_L_fun. auto.

      subst. assert (flow_to (current_label (SIGMA s'0 h'0)) L_Label = 
                  flow_to (current_label (SIGMA s2 h0)) L_Label). 
    apply erasure_sigma_preserve_context; auto. 

    subst. assert (flow_to (current_label (SIGMA s'0 h'0)) L_Label = 
                  flow_to (current_label (SIGMA s1 h1)) L_Label). 
    apply erasure_sigma_preserve_context; auto.
    rewrite H13 in H7. rewrite H11 in H6. rewrite H7 in H6. inversion H6.  
    inversion H4.
    ++ subst.     rewrite H_flow_r in H13. inversion H13.

- inversion H5.  subst. 
    induction s'. intuition. 

      induction lsf. induction a. 
          unfold current_label in H_flow_l.       unfold get_current_label in H_flow_l. 
          unfold get_stack_label in H_flow_l. unfold get_stack in H_flow_l.
          unfold current_label in H_flow_r.       unfold get_current_label in H_flow_r. 
          unfold get_stack_label in H_flow_r. unfold get_stack in H_flow_r.
          unfold update_current_label in H_flow_r. 

          assert (  flow_to (join_label l1 l0)  L_Label = false).
          apply flow_join_label with l0 l1; auto. assert ((join_label l1 l0) = (join_label l0 l1)).
          apply join_label_commutative; auto. rewrite H0 in H.  rewrite H in H_flow_r. inversion H_flow_r.
Qed. 



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


    assert ((flow_to (current_label (SIGMA s h)) L_Label = true) \/ (flow_to (current_label (SIGMA s h)) L_Label = false)).
    apply excluded_middle_label.  destruct H4.
    assert (Config c t0 sigma_l_e ==l> (Config c t1_r s0_r)).
    apply simulation_L with t t1 (SIGMA s h)  (SIGMA s0 h0) s h; auto. 
    apply multi_reduction_l_step with (Config c t1_r s0_r); auto.

    assert ((flow_to (current_label (SIGMA s0 h0)) L_Label = true) \/ (flow_to (current_label (SIGMA s0 h0)) L_Label = false)).
        apply excluded_middle_label.  destruct H5.
    assert (Config c t0 sigma_l_e ==l> (Config c t1_r s0_r)).
    apply simulation_H_L with t t1 (SIGMA s h)  (SIGMA s0 h0)   s h T; auto. 
    apply multi_reduction_l_step with (Config c t1_r s0_r); auto.
(*    assert (Config c t0 sigma_l_e = (Config c t1_r s0_r)). *)

     assert  (  (Config c t0 sigma_l_e) = (Config c t1_r s0_r) 
              \/ (Config c t0 sigma_l_e) ==l> (Config c t1_r s0_r) ).

    apply simulation_H_revised with t t1 s h s0 h0 T; auto.
    destruct H6. rewrite <- H6 in H3. auto.
    apply multi_reduction_l_step with (Config c t1_r s0_r); auto.

(*
    (*case for return v*)
    + pose proof (exclude_middle_return t). destruct H4. 
    destruct H4 as [a].
    ++      pose proof (excluded_middle_value a). destruct H5. 
    +++  
    assert (l_reduction (Config c t0 sigma_l_e) (Config c t1_r s0_r)).
     subst. inversion H_typing.
    apply simulation_return_v with a s h s0 h0 t1 T; auto. 
    apply multi_reduction_l_step with (Config c t1_r s0_r); auto.
    +++ 
    assert ((flow_to (current_label (SIGMA s0 h0)) L_Label = true) \/ (flow_to (current_label (SIGMA s0 h0)) L_Label = false)).
    apply excluded_middle_label.  destruct H6.
    ++++ 
    assert (Config c t0 sigma_l_e ==l> (Config c t1_r s0_r)).
    apply simulation_H_L with (CT:=c) (t:=t) (t0:=t0) (t':=t1) (t0':=t1_r) 
      (sigma_l:=(SIGMA s h)) (sigma_r:= (SIGMA s0 h0)) (sigma_l_e:=sigma_l_e) (s:=s) (h:=h) (T:=T); auto.
     apply multi_reduction_l_step with (Config c t1_r s0_r); auto.
    ++++  
    assert ( Config c t0 sigma_l_e = Config c t1_r s0_r).
    apply simulation_H with t t1 s h s0 h0 T; auto. rewrite H7. auto. 
    (*case for opaque call (return v)*)
    ++ pose proof (exclude_middle_opaque_return t). destruct H5.  destruct H5 as [a].
          pose proof (excluded_middle_value a). destruct H6. 
    +++ subst. assert (l_reduction (Config c t0 sigma_l_e) (Config c t1_r s0_r)).
     subst. inversion H_typing.
    apply simulation_opaque_return_v with a s h s0 h0 t1 T0; auto. inversion H10. auto.  
    apply multi_reduction_l_step with (Config c t1_r s0_r); auto.
    +++ assert ((flow_to (current_label (SIGMA s0 h0)) L_Label = true) \/ (flow_to (current_label (SIGMA s0 h0)) L_Label = false)).
    apply excluded_middle_label.  destruct H7.
    ++++ 
    assert (Config c t0 sigma_l_e ==l> (Config c t1_r s0_r)).
    apply simulation_H_L with (CT:=c) (t:=t) (t0:=t0) (t':=t1) (t0':=t1_r) 
      (sigma_l:=(SIGMA s h)) (sigma_r:= (SIGMA s0 h0)) (sigma_l_e:=sigma_l_e) (s:=s) (h:=h) (T:=T); auto.
     apply multi_reduction_l_step with (Config c t1_r s0_r); auto.
    ++++  
    assert ( Config c t0 sigma_l_e = Config c t1_r s0_r).
    apply simulation_H with t t1 s h s0 h0 T; auto. rewrite H8. auto. 
    +++ 
    assert ((flow_to (current_label (SIGMA s0 h0)) L_Label = true) \/ (flow_to (current_label (SIGMA s0 h0)) L_Label = false)).
    apply excluded_middle_label.  destruct H6.

    assert (Config c t0 sigma_l_e ==l> (Config c t1_r s0_r)).
    apply simulation_H_L with (CT:=c) (t:=t) (t0:=t0) (t':=t1) (t0':=t1_r) 
      (sigma_l:=(SIGMA s h)) (sigma_r:= (SIGMA s0 h0)) (sigma_l_e:=sigma_l_e) (s:=s) (h:=h) (T:=T); auto.
    apply multi_reduction_l_step with (Config c t1_r s0_r). auto. auto. 

    assert ( Config c t0 sigma_l_e = Config c t1_r s0_r).
    apply simulation_H with t t1 s h s0 h0 T; auto.
    rewrite <- H7 in H3. auto.  
*)
+
    subst.  apply error_state_cannot_reach_valid_state in H_multistep_reduction. intuition. 
Qed. 






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

Lemma erasure_L_fun_preserve_value : forall v, 
  value v ->
  value (erasure_L_fun v).
Proof. 
  intros. induction v; try (inversion H); try ( unfold erasure_L_fun; auto; fail).
  unfold erasure_L_fun. fold erasure_L_fun. case_eq (flow_to l0 L_Label).  intro. auto. auto. 
  unfold erasure_L_fun. fold erasure_L_fun. case_eq (flow_to l0 L_Label).  intro. auto. auto. 
Qed.  


Lemma erasure_preserve_value : forall v v' sigma sigma' CT, 
  Config CT v sigma =e=> Config CT v' sigma' -> value v ->
  value v'.
Proof. intros. inversion H. subst. apply erasure_L_fun_preserve_value. auto. 
          subst. apply erasure_H_fun_preserve_value. auto.
Qed.  


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






(*-----------------------------------------------------------------------------------------------*)