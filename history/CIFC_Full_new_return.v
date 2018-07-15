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
  | ST_return1 : forall s h s' h' e e' ct,
        Config ct e (SIGMA (removelast s) h) ==> Config ct e' (SIGMA s' h') -> 
        s <> nil ->
        Config ct (Return e) (SIGMA s h) ==> Config ct (Return e') (SIGMA ( s' ++ ( cons ( last s empty_labeled_stack_frame) nil )) h')
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
      has_type CT Gamma h (v_opa_l v lb) (OpaqueLabeledTy T).


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
      valid_syntax (v_opa_l v lb).

Hint Constructors valid_syntax.
Lemma value_is_valid_syntax : forall v, 
  value v -> valid_syntax v.
Proof with eauto. intros. inversion H. apply Valid_ObjId. apply Valid_skip. apply Valid_null. apply Valid_label. apply Valid_v_l.
        auto. apply Valid_v_opa_l. auto.  Qed. 

Lemma surface_syntax_if : forall t1 t2, 
    (if surface_syntax t1 then surface_syntax t2 else false) = true -> surface_syntax t1 = true /\ surface_syntax t2 = true.
    Proof.  intros. case_eq (surface_syntax t1). intro. case_eq (surface_syntax t2). intro. auto.
      intro. rewrite H0 in H. rewrite H1 in H. intuition. intro. rewrite H0 in H. intuition.
Qed.

Lemma surface_syntax_is_valid_syntax : forall t,
  surface_syntax t = true -> valid_syntax t.
Proof with eauto. Admitted. 

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



Inductive wfe_stack_frame : Class_table -> heap -> labeled_stack_frame -> Prop :=
  | stack_frame_wfe : forall h lsf sf lb ct,
        lsf = Labeled_frame lb sf ->
         (forall x, exists v, sf x = Some v  ->
               (
               v = null \/ 
                 ( exists cls_name o, v = ObjId o 
                              /\ (exists F lo field_defs method_defs , lookup_heap_obj h o = Some (Heap_OBJ (class_def cls_name field_defs method_defs) F lo)
                                      /\ (ct cls_name = Some (class_def cls_name field_defs method_defs))
                                   ) 
                  )    )  ) ->
        wfe_stack_frame ct h lsf. 


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



(*lemma*)

Lemma string_eq : forall n1 n2, n1 = n2 -> Id n1 = Id n2.
Proof with eauto.
  intros. rewrite -> H. auto.
Qed. 

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


Lemma some_eq : forall cls_def F lo cls_def' F' lo',
  Some (Heap_OBJ cls_def F lo) = Some (Heap_OBJ cls_def' F' lo') ->
  cls_def = cls_def' /\ F = F'.
Proof with auto. 
  intros. inversion H. auto. 
Qed.  

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

Lemma field_val_of_heap_obj : forall h o CT cls_def F lo cls' fields,
  field_wfe_heap CT h -> 
  wfe_heap CT h ->
  lookup_heap_obj h o  = Some (Heap_OBJ cls_def F lo) ->
  fields = (find_fields cls_def) ->
  forall f, type_of_field fields f = Some cls' -> exists v, F(f) = Some v.

Proof with auto.
  intros. inversion H. 
  assert (exists cn field_defs method_defs, CT cn = Some cls_def 
                    /\ cls_def = (class_def cn field_defs method_defs)).

apply heap_consist_ct with (h:=h) (o:=o) (ct:=CT) 
        (cls:=cls_def) (F:=F) (lo:=lo). auto. auto.
destruct H7 as [cls_name]. destruct H7 as [field_defs]. 
destruct H7 as [method_defs]. destruct H7. 

destruct H4 with (o:=o) (cls_def:=cls_def) (lo:=lo)
    (method_defs:=method_defs) (field_defs:=field_defs) 
    (f:=f) (cls':=cls') (F:=F) (cls_name:=cls_name).
auto. auto. auto.  auto. rewrite H8 in H2. unfold find_fields in H2.
rewrite H2 in H3. auto. exists x. apply H9.
Qed.


Lemma nil_heap_no_obj : forall ho h o,
  nil = update_heap_obj h o ho ->
  h = nil.
Proof.
  intros. induction h. auto. inversion H. 
  case a in H1. 
  case_eq (beq_oid o o0).  intro.  rewrite H0 in H1. inversion H1. 
   intro.  rewrite H0 in H1. inversion H1. 
Qed. 

(*well organized heap is preserved when the heap is extended with a fresh oid*)
Lemma extend_heap_preserve_order : forall CT h h' o c field_defs method_defs lb,
    wfe_heap CT h->
    o = get_fresh_oid h ->
    lookup_heap_obj h o = None -> 
    Some (class_def c field_defs method_defs) = CT c ->
     h' = add_heap_obj h o (Heap_OBJ (class_def c field_defs method_defs)
          (init_field_map field_defs empty_field_map)
          lb) ->  wfe_heap CT h'.
  Proof.
    intros. 
    remember (class_def c field_defs method_defs) as cls_def.
    remember  (init_field_map field_defs empty_field_map) as F.
    apply heap_wfe with (h:=h) (o:=o) 
        (cls_def:=cls_def) (F:=F) (cn:=c) (ho:=(Heap_OBJ cls_def F lb))
        (lo:=lb) (method_defs:=method_defs) (field_defs:=field_defs) ;auto.
        intros. induction h. left. auto. right.
        unfold  get_fresh_oid in H0. 
        induction a. induction o0. 
        exists (OID n). exists h0. exists h. 
        rewrite H0. split. auto. apply nat_compare_oid. intuition. 
  Qed.  

Lemma extend_heap_preserve_field_wfe : forall CT h h' o c field_defs method_defs lb,
    field_wfe_heap CT h -> 
    o = get_fresh_oid h ->
    lookup_heap_obj h o = None -> 
    Some (class_def c field_defs method_defs) = CT c ->  
     h' = add_heap_obj h o (Heap_OBJ (class_def c field_defs method_defs)
          (init_field_map field_defs empty_field_map)
          lb) ->  field_wfe_heap CT h'.
  Proof. 
    intros. 
    remember (class_def c field_defs method_defs) as cls_def.
    remember  (init_field_map field_defs empty_field_map) as F.
    auto.

    assert (        (forall o cls_def F cls_name lo method_defs field_defs,
        lookup_heap_obj  h' o = Some (Heap_OBJ cls_def F lo) ->
        Some cls_def  = CT cls_name ->
        cls_def = class_def cls_name field_defs method_defs ->
        (forall f cls', type_of_field field_defs f = Some cls' -> 
                exists v, F(f) = Some v
                 /\ (v= null  \/ 
                          ( exists o' F' lx field_defs0 method_defs0, v = ObjId o' 
                                  /\ lookup_heap_obj  h' o' = Some (Heap_OBJ (class_def cls' field_defs0 method_defs0) F' lx)
                                    /\ CT cls' = Some (class_def cls' field_defs0 method_defs0)
                          ) ) 
        ))).
      intros. 
   destruct h'. intros. inversion H4. 
   induction h0. 
    unfold add_heap_obj in H3.  inversion H3. 
  case_eq (beq_oid o0 o1).
  intro. 
  unfold  lookup_heap_obj in H4. rewrite H8 in H4. inversion H4. 
  rewrite H10 in H13. inversion H13. rewrite <-H15. 
  exists null. split. 
  assert (forall f, type_of_field field_defs f = Some cls' ->
  F f = Some null).
  apply empty_fields. auto. apply H12. 
  rewrite <- H14 in H6.  rewrite Heqcls_def in H6. inversion H6. auto. 
  left. auto. 
  intro.  
     unfold  lookup_heap_obj in H4. rewrite H8 in H4. fold  lookup_heap_obj in H4.

    inversion H. destruct H12 with (o:=o0) (cls_def:=cls_def0) (F:=F0) (cls_name:=cls_name)
          (lo:=lo) (method_defs:=method_defs0) (field_defs:=field_defs0) (f:=f) (cls':=cls').
   rewrite <- H11. auto. auto. auto. auto. auto. exists x.
   destruct H15. split. auto. destruct H16. auto. right. 
   destruct H16 as [o'].    destruct H16 as [F'].    destruct H16 as [lx]. 
   destruct H16 as [field_defs'].    destruct H16 as [method_defs']. 
   exists o'. exists F'. exists lx. exists field_defs'. exists method_defs'.
  destruct H16. split. auto. destruct H17. 
   assert (o' <> o). intro contra. rewrite <- contra in H1. 
   rewrite H1 in H17. inversion H17.  apply beq_oid_not_equal  in H19.
  unfold lookup_heap_obj.  rewrite H19. fold lookup_heap_obj. auto. auto.
  apply heap_wfe_fields. auto.
Qed. 


Lemma object_write_preserve_heap_order : 
  forall CT o h h' h'' F F' cls_def lb lb'  o0 ho0,
  wfe_heap CT h ->
  h = (o0 , ho0) :: h' ->
  Some (Heap_OBJ cls_def F lb) = lookup_heap_obj h' o ->
  h'' = (update_heap_obj h' o
           (Heap_OBJ cls_def F' lb')) ->
  (h'' = nil \/ (exists o1 ho1 h1, h'' = (o1 , ho1) :: h1 /\ compare_oid o0 o1= true) ).
Proof. 
  intros. generalize dependent ho0. generalize dependent o0.  generalize dependent h'.
generalize dependent h''.
induction h. 
  intros. inversion H0.
  destruct h'. intros. 
  unfold update_heap_obj in H2.  left. auto. 
  right. 
  induction a. induction h0. 

case_eq (beq_oid o o2). intro. 
unfold update_heap_obj in H2.  rewrite H3 in H2. 
exists o. exists (Heap_OBJ cls_def F' lb'). exists h'. 
split; auto. inversion H. destruct H5. inversion H4.
rewrite H15 in H0. rewrite H5 in H0. inversion H0.

inversion H0. subst. inversion H4. 
destruct H5 as [o']. destruct H2 as [ho']. destruct H2 as [h''].
destruct H2. rewrite H2 in H10. inversion H10.
apply beq_oid_equal in H3. subst. auto.   

(*beq_oid o o2 = false*)
intro. unfold update_heap_obj in H2. rewrite H3 in H2. fold update_heap_obj in H2. 
unfold lookup_heap_obj in H1.  rewrite H3 in H1. fold lookup_heap_obj in H1. 

destruct IHh with (h'':=update_heap_obj h' o (Heap_OBJ cls_def F' lb')) 
    (h':=h') (o0:= o2) (ho0:=h0). inversion H. inversion H4. auto. 
auto. auto.  inversion H0. auto. exists o2. exists h0. exists (update_heap_obj h' o (Heap_OBJ cls_def F' lb')).
split. auto. assert (h'=nil). apply nil_heap_no_obj with (ho:=(Heap_OBJ cls_def F' lb')) (o:=o).
auto. rewrite H5 in H1. inversion H1. 

exists  o2. exists h0. exists (update_heap_obj h' o (Heap_OBJ cls_def F' lb')). split. auto. 
inversion H0. rewrite <- H6. inversion H.  inversion H5. destruct H9.
rewrite H19 in H8.  rewrite H9 in H8. inversion H8. 

destruct H9 as [o']. destruct H9 as [ho']. destruct H9. destruct H9.
rewrite H19 in H8. rewrite H8 in H9.  inversion H9. auto. 
Qed. 


Lemma field_write_preserve_wfe_heap : 
  forall CT o h h' i F F' cls_def cls' lb lb' clsT field_defs method_defs,
  wfe_heap CT h ->
(*  wfe_stack CT gamma h s -> *)
  Some (Heap_OBJ cls_def F lb) = lookup_heap_obj h o ->
  type_of_field (find_fields cls_def) i = Some cls' ->
  cls_def = class_def clsT field_defs method_defs ->
  Some cls_def = CT clsT ->
  h' = (update_heap_obj h o
           (Heap_OBJ cls_def F' lb')) ->
  wfe_heap CT h'.

Proof.
  intros CT o h h' i F F' cls_def cls' lb lb' clsT field_defs method_defs.
  intro wfe_h.  intro Ho. intro Htyf. intro Hcls_def. intro Hct.
  intro Hy.

generalize dependent h.  induction h'. 
intros. 
apply nil_heap_no_obj with (ho:=(Heap_OBJ cls_def F' lb')) (h:=h) (o:=o) in Hy.
rewrite Hy in Ho. inversion Ho.

intros. destruct h.  inversion Ho. 
induction a. induction h.
case_eq (beq_oid o o1). 
(*beq_oid o o1 = true  *)
unfold update_heap_obj in Hy. intro. rewrite H in Hy. inversion Hy. 
inversion wfe_h.
apply heap_wfe with (h':= ((o, (Heap_OBJ cls_def F' lb')) :: h0)) 
        (o:=o) (cls_def:=cls_def0) (F:=F') (cn:=cn0) 
        (h:=h0) 
        (ho:=(Heap_OBJ cls_def F' lb'))
        (lo:=lb') (method_defs:=method_defs0) (field_defs:=field_defs0); auto.
inversion H0. auto. apply beq_oid_equal in H. rewrite H. rewrite H12. auto.
inversion H0. auto.
unfold lookup_heap_obj in Ho. rewrite H in Ho. fold lookup_heap_obj in Ho. inversion Ho.
inversion H0. rewrite <- H12 in H14. rewrite H6 in H14. inversion H14. auto.
(*beq_oid o o1 = false  *)
unfold update_heap_obj in Hy. intro. rewrite H in Hy. fold update_heap_obj in Hy.  inversion Hy. 
inversion wfe_h.
apply heap_wfe with (h':=((o1, h) :: update_heap_obj h0 o (Heap_OBJ cls_def F' lb'))) 
        (o:=o1) (cls_def:=cls_def0) (F:=F0) (cn:=cn0) 
        (h:=update_heap_obj h0 o (Heap_OBJ cls_def F' lb')) 
        (ho:=h) (lo:=lo) (method_defs:=method_defs0) (field_defs:=field_defs0).
auto. inversion H0. destruct H4. rewrite H4. left. auto. right.
destruct H4 as [o']. destruct H4 as [ho']. destruct H4 as [h'']. destruct H4. 
remember (update_heap_obj h2 o (Heap_OBJ cls_def F' lb')) as h3. 
assert (  (h3 = nil \/ (exists o1 ho1 h1, h3 = (o1 , ho1) :: h1 /\ compare_oid o0 o1= true) )).
rewrite H1.  rewrite H12. 
apply object_write_preserve_heap_order with (CT:=CT) (o:=o) 
    (h:=(o2, ho) :: h2) (h':=h2) (h'':=h3) (F:=F) (F':=F') 
    (cls_def:=cls_def) (lb:=lb) (lb':=lb')  (o0:=o2) (ho0:=ho).
rewrite <-H0. auto. auto. 
unfold  lookup_heap_obj in Ho. rewrite H in Ho. fold  lookup_heap_obj in Ho. 
rewrite <- H14. auto. auto. destruct H15.  rewrite H15 in  Heqh3.
apply nil_heap_no_obj in Heqh3. 
unfold  lookup_heap_obj in Ho. rewrite H in Ho. fold  lookup_heap_obj in Ho. 
rewrite H14 in Ho. rewrite Heqh3 in Ho. inversion Ho. auto. 
rewrite <- H12. rewrite <- H1. auto.   

rewrite <- H3. 
apply IHh' with (h:=h0). inversion H0. auto. 
unfold lookup_heap_obj in Ho. rewrite H in Ho. fold lookup_heap_obj in Ho. auto.
auto. inversion H0. auto. auto. auto. 
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

Lemma  lookup_updated_not_affected : forall o ho h h' o' ho',
    h' = update_heap_obj h o ho ->
    o' <> o ->
    Some ho' = lookup_heap_obj h o' ->
    Some ho' = lookup_heap_obj h' o'.
  Proof. 
    intros. generalize dependent h. induction h'.
   - intros. apply nil_heap_no_obj in H. rewrite H in H1. inversion H1.
   - intro h. intro.  intro. induction a.
      destruct h. inversion H. 
      induction h. 
      case_eq (beq_oid o o1).  intro.  
      unfold  update_heap_obj in H. rewrite H2 in H. inversion H.
      unfold lookup_heap_obj.
      assert (beq_oid o' o = false).  apply beq_oid_not_equal. auto. 
      rewrite H3.       fold lookup_heap_obj. 
      unfold  lookup_heap_obj in H1. apply beq_oid_equal in H2. rewrite H2 in H3. 
      rewrite H3 in H1. fold lookup_heap_obj in H1. auto.  

      intro. unfold update_heap_obj in H. rewrite H2 in H. fold update_heap_obj in H.  
      case_eq (beq_oid o' o1).
      intro. unfold lookup_heap_obj in H1. rewrite H3 in H1.  
      inversion H. unfold lookup_heap_obj. rewrite H3. auto. 

      intro. unfold lookup_heap_obj in H1. rewrite H3 in H1.  fold lookup_heap_obj in H1.
      inversion H.   unfold lookup_heap_obj. rewrite H3.  fold lookup_heap_obj.
   
      rewrite <- H7. apply IHh' with (h:=h1). auto. auto.  
Qed. 

Lemma  lookup_updated_not_affected_reverse : forall o ho h h' o' ho',
    h' = update_heap_obj h o ho ->
    o' <> o ->
    Some ho' = lookup_heap_obj h' o' ->
    Some ho' = lookup_heap_obj h o'.
  Proof. 
    intros. generalize dependent h. induction h'.
   - intros. apply nil_heap_no_obj in H. inversion H1.
   - intro h. intro.  induction a.
      destruct h. inversion H. 
      induction h. 
      case_eq (beq_oid o o1).  intro.  
      unfold  update_heap_obj in H. rewrite H2 in H. inversion H.
      unfold lookup_heap_obj.
      assert (beq_oid o' o = false).  apply beq_oid_not_equal. auto.
      apply beq_oid_equal in H2. rewrite H2 in H3.   
      rewrite H3.       fold lookup_heap_obj. 
      unfold  lookup_heap_obj in H1. rewrite <-H2 in H3. rewrite H4 in H1. 
      rewrite H3 in H1. fold lookup_heap_obj in H1. rewrite <-H6. auto.  

      intro. unfold update_heap_obj in H. rewrite H2 in H. fold update_heap_obj in H.  
      case_eq (beq_oid o' o1).
      intro. unfold lookup_heap_obj in H1. 
       inversion H. rewrite H5 in H1.  rewrite H3 in H1.    
       unfold lookup_heap_obj. rewrite H3. rewrite <- H6. auto. 

      intro. unfold lookup_heap_obj in H1. inversion H. rewrite H5 in H1. rewrite H3 in H1.  fold lookup_heap_obj in H1.
      unfold lookup_heap_obj. rewrite H3.  fold lookup_heap_obj.
   
      apply IHh' with (h:=h1). auto. auto.  
Qed. 


Lemma field_write_preserve_field_wfe : forall CT gamma h h' o field_defs method_defs lb lb' v i F cls_def clsT cls',
    field_wfe_heap CT h -> 
    value v ->
    Some (Heap_OBJ cls_def F lb) = lookup_heap_obj h o ->
    type_of_field (find_fields cls_def) i = Some cls' ->
    cls_def = class_def clsT field_defs method_defs ->
    has_type CT gamma h v (classTy cls') ->
    Some cls_def = CT clsT ->
    h' = (update_heap_obj h o
           (Heap_OBJ cls_def (fields_update F i v) lb')) ->
    field_wfe_heap CT h'.
Proof. 

    intros. 
    remember  (fields_update F i v) as F'. 

    assert (        (forall o cls_def F cls_name lo method_defs field_defs,
        lookup_heap_obj  h' o = Some (Heap_OBJ cls_def F lo) ->
        Some cls_def  = CT cls_name ->
        cls_def = class_def cls_name field_defs method_defs ->
        (forall f cls', type_of_field field_defs f = Some cls' -> 
                exists v, F(f) = Some v
                 /\ (v= null  \/ 
                          ( exists o' F' lx field_defs0 method_defs0, v = ObjId o' 
                                  /\ lookup_heap_obj  h' o' = Some (Heap_OBJ (class_def cls' field_defs0 method_defs0) F' lx)
                                    /\ CT cls' = Some (class_def cls' field_defs0 method_defs0)
                          ) ) 
        ))).
      intros. 
   destruct h'. intros. apply nil_heap_no_obj in H6. rewrite H6 in H1.  inversion H1.
  destruct h. inversion H1. induction h. induction h0. 

   assert (Some (Heap_OBJ cls_def F' lb') = lookup_heap_obj ((o2, h0) :: h') o).
   apply lookup_updated with (o:=o) (ho':= (Heap_OBJ cls_def F lb))
                                (ho:=(Heap_OBJ cls_def F' lb')) (h:=((o1, h) :: h1)) 
                                (h':=(o2, h0) :: h' ).
   auto. auto.
  (*if this is the element we updated*)
   case_eq (beq_oid o0 o). intro. apply beq_oid_equal in H12. 
   rewrite H12 in H7. 
   rewrite <- H11 in H7. inversion H7. rewrite <- H15. 
   unfold fields_update in HeqF'. rewrite HeqF'.
   (*If this is the field we updating*)
   case_eq (beq_id i f).  intro. 
   exists v. split. auto.
   inversion H0.
   rewrite <- H17 in H4. inversion H4. 
   right. 
   exists o3. 
   destruct H25 as [F'']. destruct H25 as [lx]. 
  destruct H24 as [field_defs''].   destruct H24 as [method_defs''].
  case_eq (beq_oid o3 o).  intro.
  apply beq_oid_equal in H26. rewrite H26.
  exists F'. exists lb'.  exists field_defs0. exists method_defs0.
  split. auto. split. auto. 
  inversion H7.  rewrite <- H28 in H9. rewrite H3 in H9. inversion H9.
  rewrite <- H32 in H10. rewrite H3 in H2. unfold find_fields in H2.
  apply beq_equal in H13. rewrite H13 in H10. rewrite H10 in H2.
  inversion H2. 
  rewrite H26 in H25. rewrite <- H1 in H25. inversion H25.
  rewrite <- H35 in H24. rewrite H3 in H24. inversion H24.
  rewrite <- H11. rewrite H3. rewrite H38. rewrite H33. 
  rewrite H32. rewrite H29. rewrite <- H30.  auto.

  inversion H7.  rewrite <- H28 in H9. rewrite H3 in H9. inversion H9.
  rewrite <- H32 in H10. rewrite H3 in H2. unfold find_fields in H2.
  apply beq_equal in H13. rewrite H13 in H10. rewrite H10 in H2.
  inversion H2.
  rewrite H26 in H25. rewrite <- H1 in H25. inversion H25.
  rewrite <- H35 in H24. rewrite H3 in H24. inversion H24.
  rewrite <- H38. rewrite H3 in H5. 
  rewrite <- H33. rewrite <- H32. auto.

  intro.
  assert (Some (Heap_OBJ cls_def1 F'' lx) = lookup_heap_obj ((o2, h0) :: h') o3).
  apply lookup_updated_not_affected with (h:=((o1, h) :: h1)) 
                  (h':=((o2, h0) :: h')) (ho:= (Heap_OBJ cls_def F' lb'))
                  (o':=o3) (o:=o) (ho':=(Heap_OBJ cls_def1 F'' lx)).
  auto.
  intro contra. rewrite contra in H26. 
   assert (beq_oid o o = true). apply beq_oid_same. rewrite H27 in H26.
  inversion H26. auto.
  exists F''. exists lx. exists field_defs''. exists method_defs''. split; auto.

  rewrite <- H14 in H9. rewrite H3 in H9.  inversion H9.
  apply beq_equal in H13. rewrite H13 in H10. 
  rewrite <- H30 in H10.  rewrite H3 in H2. unfold find_fields in H2. 
  rewrite H10 in H2. inversion H2. rewrite H24 in H27. 
  split; auto. rewrite H24 in H20. auto.

  rewrite <-H17 in H4. inversion H4.
  left. auto.
  rewrite <-H17 in H4. inversion H4.
  rewrite <-H18 in H4. inversion H4.
  rewrite <-H18 in H4. inversion H4.
   (*If this is not the field we updating*)
  intro. 

  inversion H. destruct H17 with (o:=o) (cls_def:=cls_def) (F:=F)
                      (cls_name:=clsT) (lo:=lb) (method_defs:=method_defs)
                      (field_defs:=field_defs) (f:=f) (cls':=cls'0); auto. 
  rewrite <- H14  in H9. rewrite H3 in H9. inversion H9. auto.
  exists x. destruct H20. split; auto. destruct H21. left. auto. right.
  destruct H21 as [o'].   destruct H21 as [F'']. destruct H21 as [lx]. 
  destruct H21 as [field_defs''].   destruct H21 as [method_defs''].

  exists o'.
  case_eq (beq_oid o' o).  intro.
  destruct H21. destruct H23.
  apply beq_oid_equal in H22. rewrite H22 in H23. rewrite H23 in H1.
  inversion H1.
  exists F'. exists lb'. exists field_defs''. exists method_defs''. split; auto. 
  split. rewrite <- H26. rewrite H22. auto. auto.

  intro.
  assert (Some (Heap_OBJ (class_def cls'0 field_defs'' method_defs'') F'' lx)
                 = lookup_heap_obj ((o2, h0) :: h') o').
   apply lookup_updated_not_affected with (h:=((o1, h) :: h1)) 
                  (h':=((o2, h0) :: h')) (ho:= (Heap_OBJ cls_def F' lb'))
                  (o':=o') (o:=o) (ho':=(Heap_OBJ (class_def cls'0 field_defs'' method_defs'') F'' lx) ); auto.
   intro contra. rewrite contra in H22. assert (beq_oid o o = true). apply beq_oid_same.
   rewrite H23 in H22. inversion H22. destruct H21. destruct H23. auto.

  exists F''. exists lx. exists field_defs''. exists method_defs''. destruct H21.
  split; auto. destruct H24. auto. 

  (*if this is not the element we updated*)
  intro. inversion H. destruct H13 with (o:=o0) (cls_def:=cls_def0) (F:=F0)
                      (cls_name:=cls_name) (lo:=lo) (method_defs:=method_defs0)
                      (field_defs:=field_defs0) (f:=f) (cls':=cls'0); auto.
  assert (Some (Heap_OBJ cls_def0 F0 lo) = lookup_heap_obj ((o1, h) :: h1) o0).
  apply lookup_updated_not_affected_reverse with (o:=o) (o':=o0) (ho:=(Heap_OBJ cls_def F' lb'))
                    (h:=((o1, h) :: h1)) (h':=(o2, h0) :: h') (ho':=(Heap_OBJ cls_def0 F0 lo)). 
  auto. intro contra. rewrite contra in H12. assert (beq_oid o o = true). apply beq_oid_same. 
  rewrite H16 in H12. inversion H12. auto.  auto. 
  exists x. destruct H16.  destruct H17. split; auto.  split; auto. right. 

  destruct H17 as [o'].   destruct H17 as [F'']. destruct H17 as [lx]. 
  destruct H17 as [field_defs''].   destruct H17 as [method_defs'']. 

  exists o'.
  case_eq (beq_oid o' o).  intro.
  destruct H17. destruct H19.
  apply beq_oid_equal in H18. rewrite H18 in H19. rewrite H19 in H1.
  inversion H1.
  exists F'. exists lb'. exists field_defs''. exists method_defs''. split; auto. 
  split. rewrite <- H22. rewrite H18. auto. auto.

  intro.
  assert (Some (Heap_OBJ (class_def cls'0 field_defs'' method_defs'') F'' lx)
                 = lookup_heap_obj ((o2, h0) :: h') o').
   apply lookup_updated_not_affected with (h:=((o1, h) :: h1)) 
                  (h':=((o2, h0) :: h')) (ho:= (Heap_OBJ cls_def F' lb'))
                  (o':=o') (o:=o) (ho':=(Heap_OBJ (class_def cls'0 field_defs'' method_defs'') F'' lx) ); auto.
   intro contra. rewrite contra in H18. assert (beq_oid o o = true). apply beq_oid_same.
   rewrite H19 in H18. inversion H18. destruct H17. destruct H19. auto.
  exists F''. exists lx. exists field_defs''. exists method_defs''. destruct H17.
  split; auto. destruct H20. auto.   

   apply heap_wfe_fields. apply H7.
Qed.

Lemma wfe_oid : forall o ct gamma s h sigma cls_def cn, 
  sigma = SIGMA s h ->
  wfe_stack ct h s ->
  (has_type ct gamma h (ObjId o) (classTy cn)) -> ct cn = Some cls_def 
    -> exists fieldsMap lb, lookup_heap_obj h o = Some (Heap_OBJ cls_def fieldsMap lb).
Proof with auto. 
  intros. inversion H1. rewrite H2 in H5. inversion H5. 
  rewrite <- H12. auto.
Qed.


Lemma excluded_middle_opaqueLabel : forall e, (exists t, e = unlabelOpaque t) \/ (forall t, ~ (e = unlabelOpaque t)).
Proof with eauto.
  intros. case e; try (right; intro;  intros contra; inversion contra; fail). left. exists t. auto. 
Qed.

Lemma excluded_middle_returnT : forall e, (exists t, e = Return t) \/ (forall t, ~ (e = Return t)).
Proof with eauto.
  intros. case e; try (right; intro;  intros contra; inversion contra; fail). left. exists t.  auto. 
Qed.

Lemma stack_not_nil : forall sigma CT s h, 
  sigma = SIGMA s h ->  wfe_heap CT h -> wfe_stack CT h s -> exists lsf s', s = cons lsf s'.
Proof with auto.
  intros. inversion H1. exists (Labeled_frame lb0 empty_stack_frame). exists nil. auto. 
  exists (Labeled_frame lb sf). exists s'. auto. 
Qed.

(* every value in the stack should be well-formed, which means that all values should point to null or valid Obj Id*)
Lemma wfe_stack_value : forall gamma CT s h sigma v clsT, 
    sigma = SIGMA s h ->  wfe_heap CT h -> wfe_stack CT h s 
      -> (has_type CT gamma h v (classTy clsT))
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
    destruct H9 as [field_defs].    destruct H9 as [method_defs]. 
    exists F. exists lo. exists field_defs. exists method_defs.  
    split. rewrite <-H9. rewrite <- H10. auto. rewrite <- H9. auto.
    
    inversion H2. 

    left. auto. 
    inversion H2. inversion H2.  inversion H2. 
Qed.   


Lemma change_label_preserve_wfe : forall CT s h lb,
    wfe_heap CT h -> wfe_stack CT h s ->
    wfe_stack CT h (update_current_label s lb).
Proof. 
   intros. inversion H0. 
    - unfold update_current_label. apply main_stack_wfe with (s:=s) (lb:=lb1); auto.
    - subst.  unfold update_current_label. apply stack_wfe with (s':=s') (lb:=lb) (sf:=sf); auto.
        inversion H4.  apply stack_frame_wfe with (sf:=sf) (lb:=lb); auto. inversion H1. auto.
Qed.




Lemma extend_heap_preserve_heap_wfe : forall CT h h' o c field_defs method_defs lb,
    wfe_heap CT h -> 
    o = get_fresh_oid h ->
    lookup_heap_obj h o = None -> 
    Some (class_def c field_defs method_defs) = CT c ->  
     h' = add_heap_obj h o (Heap_OBJ (class_def c field_defs method_defs)
          (init_field_map field_defs empty_field_map)
          lb) -> wfe_heap CT h'.
  Proof. 
    intros. 
    remember (class_def c field_defs method_defs) as cls_def.
    remember  (init_field_map field_defs empty_field_map) as F.
    apply heap_wfe with (h:=h) (o:=o) 
        (cls_def:=cls_def) (F:=F) (cn:=c) (ho:=(Heap_OBJ cls_def F lb))
        (lo:=lb) (method_defs:=method_defs) (field_defs:=field_defs) ;auto.
        intros. induction h. left. auto. right.
        unfold  get_fresh_oid in H0. 
        induction a. induction o0. 
        exists (OID n). exists h0. exists h. 
        rewrite H0. split. auto. apply nat_compare_oid. intuition. 
Qed.


Lemma extend_heap_preserve_stack_wfe : forall CT s h h' o heap_obj,
    wfe_heap CT h -> 
    wfe_stack CT h s ->
    o = get_fresh_oid h ->
    h' = add_heap_obj h o heap_obj -> 
    wfe_heap CT h' -> 
    wfe_stack CT h' s.
Proof.

  intros. induction H0.

  apply main_stack_wfe with (s:=s) (lb:=lb). 
  auto.  auto. auto. auto.
  apply stack_wfe with (s:=s) (ct:=ct) 
                  (s':=s') (lb:=lb) (sf:=sf) (h:=h').
  auto. auto. auto. auto. auto.
  apply stack_frame_wfe with (sf:=sf) (lb:=lb). auto.
  inversion H6. auto. inversion H7.
  intros. destruct H8 with (x:=x) as [v]. exists v. intro.  
  destruct H12. auto.  left. auto. 
  right. destruct H12 as [cls_name]. destruct H12 as [o'].
  exists cls_name. exists o'. destruct H12. split.  auto.
  destruct H16 as [F]. destruct H16 as [lo]. 
  destruct H16 as [field_defs].   destruct H16 as [method_defs]. 
  destruct H16.
  exists F. exists lo. exists field_defs. exists method_defs. 
  rewrite H2. unfold add_heap_obj. unfold lookup_heap_obj.
  assert (lookup_heap_obj h o = None). apply fresh_oid_heap with (CT:=ct); auto.
  assert (o' <> o). intro contra. rewrite contra in H16. rewrite H16 in H18. inversion H18. 

  apply beq_oid_not_equal in H19. rewrite H19. fold lookup_heap_obj. auto. 
Qed. 

(*field write changes the objects in the heap, such field write should preserve the wfe of stack *)
Lemma update_field_preserve_stack_wfe : 
  forall CT o s h h' F F' cls_def lb lb' clsT field_defs method_defs,
  wfe_stack CT h s ->
  wfe_heap CT h ->
  wfe_heap CT h' ->
  Some (Heap_OBJ cls_def F lb) = lookup_heap_obj h o ->
  cls_def = class_def clsT field_defs method_defs ->
  Some cls_def = CT clsT ->
  h' = (update_heap_obj h o
           (Heap_OBJ cls_def F' lb')) ->
  wfe_stack CT h' s.
Proof with auto. 

  intros CT o s h h' F F' cls_def lb lb' clsT field_defs method_defs.
  intro wfe_s. intro wfe_h. intro wfe_h'. intro Ho. intro Hcls_def. intro Hct.
  intro Hy. 

  induction wfe_s. 

  (*s=nil*)
  apply main_stack_wfe with (s:=(Labeled_frame lb1 empty_stack_frame :: nil)) (lb:=lb1). 
  auto.  auto. auto. 

  apply stack_wfe with (s':=s')  (lb:=lb0) (sf:=sf) ; auto.
  inversion H1. 
  apply stack_frame_wfe with (h:=h') (lsf:= (Labeled_frame lb0 sf)) (sf:=sf) (lb:=lb0) (ct:=ct).
  auto. intros.  destruct H3 with (x:=x) . auto. inversion H2. 
  exists x0. intro.  destruct H7. auto. left. auto.  
  destruct H7 as [cls_name]. destruct H7 as [o'].  right. 
  exists cls_name. exists o'. destruct H7. split. auto. 
  case_eq (beq_oid o' o).   intro. 
  apply beq_oid_equal in H12. rewrite H12. 
exists F'. exists lb'. exists field_defs. exists method_defs. split;auto.  
  destruct H11 as [F0]. destruct H11 as [lo0]. destruct H11 as [field_defs0].
  destruct H11 as [method_defs0]. destruct H11.
  rewrite H12 in H11. rewrite H11 in Ho. inversion Ho. rewrite Hcls_def in H15.
  inversion H15.   
  assert (Some (Heap_OBJ cls_def F' lb') = lookup_heap_obj h' o).
  apply lookup_updated with (o:=o) (ho:=(Heap_OBJ cls_def F' lb')) 
          (ho':=(Heap_OBJ (class_def cls_name field_defs0 method_defs0) F0 lo0))
          (h':=h') (h:=h); auto. rewrite <-Hcls_def in H15. rewrite <- H15. auto.  

  destruct H11 as [F0]. destruct H11 as [lo0]. destruct H11 as [field_defs0].
  destruct H11 as [method_defs0]. destruct H11.
  rewrite H12 in H11. rewrite H11 in Ho. inversion Ho. rewrite Hcls_def in H15.
  inversion H15. auto. 

  intro.
  destruct H11 as [F0]. destruct H11 as [lo0]. destruct H11 as [field_defs0].
  destruct H11 as [method_defs0]. destruct H11.
  exists F0. exists lo0. exists field_defs0. exists method_defs0. split;auto.  
  assert (Some (Heap_OBJ (class_def cls_name field_defs0 method_defs0) F0 lo0) = lookup_heap_obj h' o').
  apply lookup_updated_not_affected with (o:=o) 
        (ho':=(Heap_OBJ (class_def cls_name field_defs0 method_defs0) F0 lo0))
        (h:=h) (h':=h') (o':=o') (ho:=(Heap_OBJ cls_def F' lb') ); auto. 
  intro contra. rewrite contra in H12. 
  assert (beq_oid o o = true). apply beq_oid_same. rewrite H12 in H14. inversion H14.
  auto.  
Qed. 

Lemma wfe_stack_not_empty : forall CT s h, 
  wfe_stack CT h s -> s <> nil. 
Proof. intros. inversion H. intro contra. inversion contra .
intro contra. subst. inversion contra. Qed.

Hint Constructors reduction. 

Lemma extend_stack_reduction_preservation : forall CT s h h' t e' s', 
  forall T, has_type CT empty_context h t T ->
wfe_heap CT h -> wfe_stack CT h s ->     field_wfe_heap CT h -> 
  Config CT t (SIGMA (removelast s) h) ==> Config CT e' (SIGMA s' h') ->
  Config CT t (SIGMA s h) ==>
  Config CT e' (SIGMA (s' ++ last s empty_labeled_stack_frame :: nil) h').
Proof with eauto. 
    intros  CT s h h' t e' s'. intro T. intro H_typing. 
    intro H_wfe_heap. intro H_wfe_stack. intro H_field_wfe.  intro H_reduction. 
    generalize dependent s.     generalize dependent h. 
    generalize dependent s'.     generalize dependent h'. 
    generalize dependent e'.      generalize dependent T. 
induction t; intros; subst; auto; inversion H_reduction; subst; auto. 
- inversion H_typing. inversion H3.
- inversion H_typing. subst. 
   assert (Config CT t (SIGMA s h) ==>  
      Config CT e'0 (SIGMA (s' ++ last s empty_labeled_stack_frame :: nil) h')). 
  apply IHt with (classTy clsT); auto. auto. 
- admit. - admit. - admit. - admit. - admit. - admit. - admit. - admit. 
- admit. - admit. - admit. - admit. - admit. - admit. - admit. - admit. 
- admit. - admit.  - admit. - admit. - admit. - admit. - admit. - admit. 
- inversion H_typing. subst. 
   assert (Config CT t (SIGMA (removelast s) h) ==>  
      Config CT e'0 (SIGMA (s'0 ++ last (removelast s) empty_labeled_stack_frame :: nil) h')). 
  apply IHt with T0; auto. auto.
    admit. apply ST_return1. auto. auto.  apply wfe_stack_not_empty with CT h. auto.  
- inversion H5. inversion H9. subst. auto. rewrite H0. destruct s. unfold removelast in H0. 
   inversion H0. destruct lsf. destruct l0. apply ST_return2 with (Labeled_frame l0 s1 :: s) 
                      (s'0 ++ last (Labeled_frame l0 s1 :: s) empty_labeled_stack_frame :: nil) h0 (Labeled_frame l0 s1); auto. 
      inversion H5. subst. destruct s. inversion H1. 
assert (removelast (l2 :: s)  = s'0). auto. inversion H1. auto. 
admit. intro contra. inversion contra. destruct s'0. auto. inversion contra.   
assert (removelast (Labeled_frame l0 s1 :: s)  = (Labeled_frame l0 s1)  :: removelast s). admit.
rewrite H in H0. inversion H0. unfold get_current_label. auto. 
Admitted. 







(* reduction preserve well-form of stack and heap *)
Theorem reduction_preserve_wfe : forall CT s s' h h' sigma sigma',
    sigma = SIGMA s h ->  wfe_heap CT h -> wfe_stack CT h s ->     field_wfe_heap CT h -> 
     sigma' = SIGMA s' h' -> 
    forall t T, has_type CT empty_context h t T -> 
     forall t',  Config CT t sigma ==> Config CT t' sigma' ->
    wfe_heap CT h' /\ wfe_stack CT h' s' /\  field_wfe_heap CT h'.
Proof with auto.

    intros CT s s' h h' sigma sigma'.
    intro H_sigma. intro H_wfe_heap. intro H_wfe_stack. intro H_field_wfe.  
    induction t. (*induction on the terms *)
  (* (Tvar i) *)
  + intro T. intro typing. intro t'.  intro step. inversion step.
      rewrite H_sigma in H4. rewrite H in H4. inversion H4. 
      rewrite <- H10. rewrite <- H11.
      split; auto. 

  (* null *)
  + intro T. intro typing. intro t'.  intro step. inversion step.
  (* field access *)
  + intro T. intro typing. intro t'.  intro step. 
      inversion step.  inversion typing.
      apply IHt with (T:=(classTy clsT)) (t':=e'). auto. auto.
      (*subgoal#2 *)      
      inversion typing. subst. inversion H11. inversion H6. 
      split. rewrite <- H3. auto.
      split. rewrite <- H3. rewrite <- H2. 
      remember (join_label lb (current_label (SIGMA s h))) as lb'.
      unfold update_current_label.
      inversion H_wfe_stack. apply main_stack_wfe with (s:=s1) (lb:=lb0). auto. auto. auto. auto.  
      rewrite H. 

      apply stack_wfe with (s':=s'0) 
                                                      (lb:=lb') (sf:=sf) ; auto.
      inversion H9. apply stack_frame_wfe with (lb:=lb') (sf:=sf); auto.
      inversion H16. apply H17. 
    
      rewrite <- H3. auto.  

  (* method call *)
  + 
      intro T. intro typing. intro t'.  intro step. 
      inversion step.  
      (*subgoal 1*)
      inversion typing. apply IHt1 with (T:=(classTy T0)) (t':=e'); auto.
     
      (*subgoal 2*)
      inversion typing. apply IHt2 with (T:=(classTy arguT)) (t':=e'); auto.
      (*subgoal 3*)
      subst. inversion H15. split. auto. split.
      apply stack_wfe with (s':=s0) 
            (lb:=(current_label (SIGMA s h))) 
            (sf:=(sf_update empty_stack_frame arg_id t2)) ; auto.
      inversion H7. rewrite <- H2. rewrite <- H3. auto.  
      apply stack_frame_wfe with      (lb:=(current_label (SIGMA s h)))
                                                     (sf:=(sf_update empty_stack_frame arg_id t2)) ; auto.
      intros x. exists t2.
      case_eq (beq_id arg_id x). intro. 
      unfold sf_update. rewrite H. intro. 
      inversion typing.
      assert 
      (t2 = null \/ 
                 ( exists o, t2 = ObjId o 
                              /\ (exists F lo field_defs method_defs , 
                                      lookup_heap_obj h o = Some (Heap_OBJ (class_def arguT field_defs method_defs) F lo)
                                      /\ (CT arguT = Some (class_def arguT field_defs method_defs))
                                   )
                  )    ).
      apply wfe_stack_value with (gamma:=empty_context) (s:=s) (sigma:=(SIGMA s h) ); auto. 
      destruct H23. left. auto.  destruct H23 as [o']. right. exists arguT. exists o'. auto.

      intro.  unfold sf_update. rewrite H. intro. inversion H2. auto.  
      
      (*subgoal 4*)
      subst. inversion H15. split. auto. split.
      apply stack_wfe with (s':=s0) 
            (lb:=(join_label lb (current_label (SIGMA s h)))) 
            (sf:=(sf_update empty_stack_frame arg_id v)) ; auto.
      inversion H7. rewrite <- H2. rewrite <- H3. auto.  
      apply stack_frame_wfe with      (lb:=(join_label lb (current_label (SIGMA s h))))
                                                     (sf:=(sf_update empty_stack_frame arg_id v)) ; auto.
      intros x. exists v.
      case_eq (beq_id arg_id x). intro. 
      unfold sf_update. rewrite H. intro. 
      inversion typing.
      assert 
      (v = null \/ 
                 ( exists o, v = ObjId o 
                              /\ (exists F lo field_defs method_defs , 
                                      lookup_heap_obj h o = Some (Heap_OBJ (class_def arguT field_defs method_defs) F lo)
                                      /\ (CT arguT = Some (class_def arguT field_defs method_defs))
                                   )
                  )    ).
      apply wfe_stack_value with (gamma:=empty_context) (s:=s) (sigma:=(SIGMA s h) ); auto.
      inversion H9. inversion H27. auto.  
      destruct H23. left. auto.  destruct H23 as [o']. right. exists arguT. exists o'. auto.

      intro.  unfold sf_update. rewrite H. intro. inversion H2. auto.  

(* new expression *)
+ intro T. intro typing. intro t'.  intro step. inversion step. 
    subst. inversion typing. 
    remember (class_def c field_defs method_defs) as cls_def.
(*
    assert (CT c = Some cls_def).
    apply H5 with (field_defs:=field_defs) (method_defs:=method_defs) (cls_def:=cls_def).
    auto. 
*)
    inversion H6. inversion H12.
    rewrite <- H11. split.  
    remember (current_label (SIGMA s h)) as lb. 
    apply extend_heap_preserve_heap_wfe with (h:=h) (o:=(get_fresh_oid h0))
                          (c:=c) (field_defs:=field_defs)
                          (method_defs:=method_defs) (lb:=lb).
   auto.  rewrite H9. auto. apply fresh_oid_heap with (CT:=CT) .
   auto. rewrite H9. auto. rewrite <- Heqcls_def. auto. auto.
   rewrite  H9. auto. rewrite  Heqcls_def in H11. auto.
  split. 
 (* extend heap with new object preserve wfe *) 
    rewrite <- H8.
    remember (Heap_OBJ cls_def
           (init_field_map (find_fields cls_def) empty_field_map)
           (current_label (SIGMA s h))) as heap_obj.
    apply extend_heap_preserve_stack_wfe with (h:=h0) (o:= (get_fresh_oid h0))
                         (heap_obj:=heap_obj).
     rewrite <- H9.  auto.       rewrite <- H9.  auto.  auto. auto. 
     
     apply extend_heap_preserve_heap_wfe with (h:=h0) (o:=(get_fresh_oid h0)) 
                (c:=c) (field_defs:=field_defs) (method_defs:=method_defs) (lb:=(current_label (SIGMA s h))).
     rewrite <- H9.  auto.       rewrite <- H9.  auto.
     apply fresh_oid_heap with (CT:=CT).  
     rewrite <- H9.  auto.       rewrite <- H9.  auto.
     (*destruct H5 with (field_defs:=field_defs) (method_defs:=method_defs) (cls_def:= (class_def c field_defs method_defs)).*)
     auto. auto. 
     rewrite <- Heqcls_def. auto.
    rewrite Heqheap_obj in H11. 
      rewrite Heqcls_def in H11. unfold find_fields in H11. auto. 

    
    apply extend_heap_preserve_field_wfe with (CT:=CT) (h:=h0) (h':=h') (o:=(get_fresh_oid h0))   
                      (c:=c) (field_defs:=field_defs) (method_defs:=method_defs) (lb:=(current_label (SIGMA s h))).

    rewrite <- H9. auto.  auto. rewrite <- H9. auto. apply fresh_oid_heap with (CT:=CT) . 
    auto. auto.  rewrite Heqcls_def in H5. auto. rewrite <-Heqcls_def. 
    rewrite Heqcls_def in H11.  rewrite Heqcls_def. unfold find_fields in H11.  auto. 

(* label value*)
+ intro T. intro typing. intro t'.  intro step. inversion step. 

(* label data *)
+ intro T. intro typing. intro t'.  intro step. 
    inversion step. inversion typing.
    apply IHt with (T:=T0) (t':=e'); auto.

    subst. inversion H6. rewrite <- H0. rewrite <- H2.
    intuition.

(* unlabel *)
+ intro T. intro typing. intro t'.  intro step. 
    inversion step. inversion typing.
    apply IHt with (T:=(LabelelTy T)) (t':=e'); auto.

    subst. inversion H8. split. auto. 
    inversion H5. rewrite <- H2. rewrite <- H3.
    split.  
    apply change_label_preserve_wfe; auto.
    auto. 

(* label of *)
+ intro T. intro typing. intro t'.  intro step. 
    inversion step. inversion typing.
    apply IHt with (T:=(LabelelTy T0)) (t':=e'); auto.

    subst. inversion H5. rewrite <- H0. rewrite <- H1. 
    split; auto.

(* unlabelopaque *)
+ intro T. intro typing. intro t'.  intro step. 
    inversion step. inversion typing.
    apply IHt with (T:=(OpaqueLabeledTy T)) (t':=e'); auto.

    rewrite H_sigma in H8. rewrite H in H8. unfold get_heap in H8.
    inversion H8. split. auto.
   split.
    rewrite H7.
    rewrite H_sigma in H5. inversion H5. rewrite <- H12. rewrite <- H13.
    apply change_label_preserve_wfe; auto. 
    auto.
     
(* skip *)
+ intro T. intro typing. intro t'.  intro step. 
    inversion step.

(* assignment *)
+ intro T. intro typing. intro t'.  intro step. 
    inversion step. inversion typing.
    apply IHt with (T:=T0) (t':=e'). auto. auto.

   rewrite H_sigma in H7. rewrite H in H9.  inversion H7. inversion H9. 
    rewrite <- H12. split. auto. 
    rewrite H11 in H_wfe_stack.    inversion typing. split. inversion H19.
(*    apply update_stack_preserve_wfe with (s:=s0) (i:=i) (v:=t) (T:=T0) (gamma:=empty_context).*)
   auto.

(* field write *)
+ intro T. intro typing. intro t'.  intro step. 

    inversion step. 
     (*subgoal 1*)
    inversion typing.    apply IHt1 with (T:=(classTy clsT)) (t':=e1'); auto.
    (*subgoal 2*)
    inversion typing.    apply IHt2 with (T:=(classTy cls')) (t':=e2'); auto.  
    (*subgoal 3*)
    (*wfe_stack CT gamma h *)
    assert (wfe_heap CT h' ).
    inversion typing. rewrite H_sigma in H7. inversion H7. 
    rewrite <- H1 in H17. inversion H17. 
    rewrite <- H27 in H8.
    destruct H34 as [F0]. destruct H34 as [lo0].
    rewrite H34 in H8. inversion H8. rewrite <- H23 in H29. inversion H29.
    destruct H33 as [field_defs]. destruct H33 as [method_defs].
    apply field_write_preserve_wfe_heap with (CT:=CT) (o:=o) 
           (h:=h0) (h':=h') (i:=i) (F:=F) (F':=F') (cls_def:=cls)
              (cls':=cls') (lb:=lb) (lb':=l')  (clsT:=clsT) (field_defs:=field_defs) (method_defs:=method_defs).
   rewrite <- H27. auto. rewrite <- H34 in H8. rewrite <- H27. auto.
   rewrite H36. rewrite H39. auto.
   rewrite <- H36 in H33. auto.
   rewrite H36. rewrite H39. auto.
   rewrite H in H12. inversion H12. auto. 
   split; auto. 

   (*wfe_stack CT gamma h' s'*)
   split. rewrite H in H12. inversion H12. rewrite <- H17. 
   inversion typing. rewrite H_sigma in H7. inversion H7. rewrite <- H29. 
    rewrite <- H1 in H20. inversion H20. 
   destruct H37 as [F0]. destruct H37 as [lo0]. 
   destruct H36 as [field_defs0]. destruct H36 as [method_defs0].
   rewrite <- H26 in  H32. inversion H32. 
   apply update_field_preserve_stack_wfe with (CT:=CT) (o:=o)  
          (s:=s) (h:=h) (h':=h') (F:=F) (F':=F') (cls_def:=cls_def) (lb:=lb) (lb':=l') 
          (clsT:=clsT) (field_defs:=field_defs0) (method_defs:=method_defs0); auto.
  rewrite <- H30 in H8. rewrite H37 in H8. inversion H8. rewrite <- H39. auto. 
  rewrite <- H39. auto.  rewrite <- H17 in H11. rewrite <- H30 in H11. 
  rewrite <- H30 in H8. rewrite H37 in H8. inversion H8. 
  rewrite <- H39. rewrite <- H40. auto.  
  assert (field_wfe_heap CT h').
  rewrite H in H12. inversion H12. rewrite <- H17. 
   inversion typing. rewrite H_sigma in H7. inversion H7. 
    rewrite <- H1 in H20. inversion H20. 
   destruct H37 as [F0]. destruct H37 as [lo0]. 
   destruct H36 as [field_defs0]. destruct H36 as [method_defs0].

    apply field_write_preserve_field_wfe with (CT:=CT) (gamma:=empty_context)  (h:=h) 
          (h':=h') (o:=o) (field_defs:=field_defs0) (method_defs:=method_defs0) 
          (lb:=lo0) (lb':=l') (v:=v) (i:=i) (F:=F0) (cls_def:=cls_def0) (clsT:=clsT) 
          (cls':=cls'); auto. 
   rewrite H3. auto.
   assert (cls_def=cls_def0). 
   rewrite <- H32 in H26. inversion H26.  auto. 
  rewrite <- H38. auto. 
   rewrite <- H3 in H24. auto. 
  
rewrite <- H30 in H8. rewrite H37 in H8. inversion H8. 
  rewrite <- H39. rewrite <- H40. rewrite H3. rewrite <-H9. 
  rewrite <- H30 in H11. rewrite <- H17 in H11.  auto.  auto. 
(*subgoal 4 v=unlabelOpaque (v_opa_l v lb)*)
assert (wfe_heap CT h' ).
    inversion typing. rewrite H_sigma in H8. inversion H8. 
    rewrite <- H1 in H18. inversion H18. 
    rewrite <- H28 in H9.
    destruct H35 as [F0]. destruct H35 as [lo0].
    rewrite H35 in H9. inversion H9. rewrite <- H24 in H30. inversion H30.
    destruct H34 as [field_defs]. destruct H34 as [method_defs].
    apply field_write_preserve_wfe_heap with (CT:=CT) (o:=o) 
           (h:=h0) (h':=h') (i:=i) (F:=F) (F':=F') (cls_def:=cls)
              (cls':=cls') (lb:=lo) (lb':=l')  (clsT:=clsT) (field_defs:=field_defs) (method_defs:=method_defs).
   rewrite <- H28. auto. rewrite <- H35 in H9. rewrite <- H28. auto.
   rewrite H37. rewrite H40. auto.
   rewrite <- H37 in H34. auto.
   rewrite H37. rewrite H40. auto.
   rewrite H in H13. inversion H13. auto. 
   split; auto. 

   (*wfe_stack CT gamma h' s'*)
   split. rewrite H in H13. inversion H13. rewrite <- H18. 
   inversion typing. rewrite H_sigma in H8. inversion H8. rewrite <- H30. 
    rewrite <- H1 in H21. inversion H21. 
   destruct H38 as [F0]. destruct H38 as [lo0]. 
   destruct H37 as [field_defs0]. destruct H37 as [method_defs0].
   rewrite <- H27 in  H33. inversion H33. 
   apply update_field_preserve_stack_wfe with (CT:=CT) (o:=o)  
          (s:=s) (h:=h) (h':=h') (F:=F) (F':=F') (cls_def:=cls_def) (lb:=lo) (lb':=l') 
          (clsT:=clsT) (field_defs:=field_defs0) (method_defs:=method_defs0); auto.
  rewrite <- H31 in H9. rewrite H38 in H9. inversion H9. rewrite <- H40. auto. 
  rewrite <- H40. auto.  rewrite <- H18 in H12. rewrite <- H31 in H12. 
  rewrite <- H31 in H9. rewrite H38 in H9. inversion H9. 
  rewrite <- H40. rewrite <- H41. auto.  
  assert (field_wfe_heap CT h').
  rewrite H in H13. inversion H13. rewrite <- H18. 
   inversion typing. rewrite H_sigma in H8. inversion H8. 
    rewrite <- H1 in H21. inversion H21. 
   destruct H38 as [F0]. destruct H38 as [lo0]. 
   destruct H37 as [field_defs0]. destruct H37 as [method_defs0].

    apply field_write_preserve_field_wfe with (CT:=CT) (gamma:=empty_context)  (h:=h) 
          (h':=h') (o:=o) (field_defs:=field_defs0) (method_defs:=method_defs0) 
          (lb:=lo0) (lb':=l') (v:=v) (i:=i) (F:=F0) (cls_def:=cls_def0) (clsT:=clsT) 
          (cls':=cls'); auto. 
   assert (cls_def=cls_def0). 
   rewrite <- H33 in H27. inversion H27.  auto. 
  rewrite <- H39. auto. 
   rewrite H7 in H25. inversion H25. inversion H43. auto.
   
  rewrite <- H31 in H9. rewrite H38 in H9. inversion H9. 
  rewrite <- H40. rewrite <- H41. rewrite <-H10. 
  rewrite <- H31 in H12. rewrite <- H18 in H12.  auto.  auto. 


(* if *)
+ intro T. intro typing. intro t'.  intro step. 
    inversion step. rewrite H_sigma in H8. rewrite H in H8.
    inversion H8. rewrite <- H13. rewrite <- H14.
    split; auto.
    rewrite H_sigma in H8. rewrite H in H8.
    inversion H8. rewrite <- H13. rewrite <- H14.
    split; auto. 

(* sequence *)
+ intro T. intro typing. intro t'.  intro step. 
    inversion step. inversion typing.
    apply IHt1 with (T:=T0) (t':=s1'); auto.

    rewrite H_sigma in H6. rewrite H in H6. inversion H6.
    rewrite <- H8. rewrite <- H9.
    split;auto.

(* return *)
+ intro T. intro typing. intro t'.  intro step. 
    inversion step. inversion typing.
    apply IHt with (T:=T0) (t':=e'); auto. subst.
    inversion H3. inversion H5. subst.  

    apply extend_stack_reduction_preservation with T0; auto.  



    split. rewrite H_sigma in H6.  rewrite H in H10. 
    inversion H6.  inversion H10. rewrite <- H13. auto.

    split. rewrite H_sigma in H6. inversion H6.  
    rewrite <- H12 in H7. rewrite H7 in H_wfe_stack. inversion H_wfe_stack.
    rewrite <- H14 in H8. intuition. 
    inversion H11.  rewrite H in H10. inversion H10. 
    subst. auto. subst. inversion H10. inversion H6. subst. auto.

(* obj id *)
+ intro T. intro typing. intro t'.  intro step. 
    inversion step.

(* runtime labeled *)
+ intro T. intro typing. intro t'.  intro step. 
    inversion step. 

(* runtime opaque labeled *)
+ intro T. intro typing. intro t'.  intro step. 
    inversion step. 
Qed.

Lemma ct_consist : forall CT CT' t t' sigma sigma', 
  Config CT t sigma ==> Config CT' t' sigma' -> CT = CT'. 
 Proof.
   intros. induction t; inversion H; auto. 
  Qed. 

Lemma value_typing_invariant_gamma : forall CT gamma h v T gamma', 
  value v ->
  has_type CT gamma h v T -> 
  has_type CT gamma' h v T.
Proof. 
 intros CT gamma h v T gamma'. intro H_v. intro typing. generalize dependent T. 
 induction H_v; intro T; intro typing. 
 -  inversion typing.   
 apply T_ObjId with (cls_def:=cls_def); auto.
 - inversion typing. apply T_skip.
 - apply T_null. 
 - inversion typing. apply T_label.
 - inversion typing. apply T_v_l. apply T_label. apply IHH_v. auto. auto. 
 - inversion typing. apply T_v_opa_l. apply T_label. apply IHH_v. auto. auto. 
Qed. 


Lemma field_consist_typing : forall CT v h o cls_def F f lb field_cls_name cls_name field_defs method_defs,
  wfe_heap CT h ->
  field_wfe_heap CT h -> 
  lookup_heap_obj h o = Some (Heap_OBJ cls_def F lb) -> 
  cls_def = class_def cls_name field_defs method_defs ->
  type_of_field field_defs f = Some field_cls_name ->
  F f = Some v ->
     ( v = null \/ 
          ( exists o' field_defs0 method_defs0 field_cls_def F' lo, 
           v = (ObjId o') 
          /\ field_cls_def = (class_def field_cls_name field_defs0 method_defs0) 
          /\ lookup_heap_obj h o' = Some (Heap_OBJ field_cls_def F' lo) 
          /\ CT field_cls_name = Some field_cls_def 
          )
      ).
Proof with auto. 
  intros. inversion H0.
  assert (exists v : tm,
       F f = Some v /\
       (v = null \/
        (exists
           (o' : oid) (F' : FieldMap) (lx : Label) (field_defs0 : list field) 
         (method_defs0 : list method_def),
           v = ObjId o' /\
           lookup_heap_obj h o' =
           Some (Heap_OBJ (class_def field_cls_name field_defs0 method_defs0) F' lx) /\
           CT field_cls_name = Some (class_def field_cls_name field_defs0 method_defs0)))).
  apply H5 with (o:=o) (cls_def:=cls_def) (F:=F) (cls_name:=cls_name)
       (lo:=lb) (method_defs:=method_defs) (field_defs:=field_defs); auto. 

assert (exists cn field_defs method_defs, CT cn = Some cls_def /\ cls_def = (class_def cn field_defs method_defs)).
apply heap_consist_ct with (h:=h) (o:=o) (ct:=CT) (cls:=cls_def) (F:=F) (lo:=lb). 
auto. auto. 
destruct H8 as [cls_name0]. destruct H8 as [field_defs0]. destruct H8 as [method_defs0]. destruct H8. 
rewrite H2 in H9. inversion H9. auto.
destruct H8 as [v']. destruct H8. rewrite H4 in H8. inversion H8. 
destruct H9. left. auto. right. 
destruct H9 as [o']. destruct H9 as [F']. destruct H9 as [lx]. 
destruct H9 as [field_defs0]. destruct H9 as [method_defs0].
remember  (class_def field_cls_name field_defs0 method_defs0) as field_cls_def.
exists o'.  exists field_defs0. exists method_defs0. exists field_cls_def. exists F'. exists lx. 
destruct H9.  split; auto. 
Qed. 


Lemma heap_preserve_typing : forall h h' t T CT gamma,
(forall o cls_def F lo, lookup_heap_obj h o = Some  (Heap_OBJ cls_def F lo) 
                              -> exists F' lo', lookup_heap_obj h' o = Some  (Heap_OBJ cls_def F' lo') )
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
        (arguT:=arguT) (Gamma':=Gamma'); auto.
  + apply T_NewExp with (cls_name:=cls_name). auto. 
  + apply T_label.
  + apply T_labelData; auto.
  + apply T_unlabel; auto.
  + apply T_labelOf with (T:=T); auto. 
  + apply T_unlabelOpaque. auto.
  + apply T_skip.
  + apply T_assignment with (T:=T); auto. (*(lsf:=lsf) (s':=s') (lb:=lb) (sf:=sf); auto. *)
  + apply T_FieldWrite with (cls_def:=cls_def) (clsT:=clsT) (cls':=cls'); auto. 
  + apply T_if with (T:=T); auto.
  + apply T_sequence with (T:=T); auto.
  + apply T_return . auto. auto.
  + apply T_ObjId with (cls_def:=cls_def). 
    auto. destruct H1 as [F]. destruct H1 as [lo].
    
    destruct Hyh with (o:=o) (cls_def:=cls_def) (F:=F) (lo:=lo).
    auto. destruct H2 as [lx]. auto.
    auto. destruct H1 as [F]. destruct H1 as [lo].
    destruct Hyh with (o:=o) (cls_def:=cls_def) (F:=F) (lo:=lo).
    auto. exists x.  auto. 
  + apply T_v_l; auto.
  + apply T_v_opa_l; auto.
Qed. 


(* original 
Lemma reduction_preserve_heap_pointer : forall t s s' h h', 
     forall CT gamma T, has_type CT gamma h t T ->
     wfe_heap CT h ->
     forall t', reduction (Config CT t (SIGMA s h)) (Config CT t' (SIGMA s' h')) -> 
     (forall o cls_def F lo, lookup_heap_obj h o = Some  (Heap_OBJ cls_def F lo) 
                              -> exists F' lo', lookup_heap_obj h' o = Some  (Heap_OBJ cls_def F' lo') ).
Proof.
     intros  t s s' h h'.
     intros CT.
     induction t; intro gamma; intro T; intro typing; intro wfe_h; intro t'; intro step; inversion step; inversion typing. 
     + intuition. exists F. exists lo. auto.  
     + apply IHt with (gamma) (classTy clsT) e'; auto.
     + inversion H10. auto. 
          inversion H5. auto.  intuition. exists F. exists lo. auto. 
     + apply IHt1 with gamma (classTy T0) e'; auto.
     + apply IHt2 with (gamma) (classTy arguT) e'; auto.
     + inversion H14. auto.  intuition. exists F. exists lo. auto.
     + inversion H14. auto.   intuition. exists F. exists lo. auto.  
     + inversion H11. rewrite H10. unfold add_heap_obj.
        intros.  
        case_eq (beq_oid o0 o). intro. apply beq_oid_equal in H21. 
        rewrite H21 in H18. assert (lookup_heap_obj h o = None). 
        apply fresh_oid_heap with (h:=h) (CT:=CT) (o:=o).
        auto. inversion H5. auto. rewrite H22 in H18. inversion H18.

        intro.  unfold lookup_heap_obj. 
        rewrite H21. fold lookup_heap_obj.  inversion H5. 
        rewrite <- H24. exists F0. exists lo. auto. 
     + apply IHt with (gamma) T0 e'; auto. 
     + auto.  intuition. exists F. exists lo. auto.  
     + apply IHt with (gamma) (LabelelTy T) e'; auto. 
     + inversion H7. auto.  intuition. exists F. exists lo. auto.   
     + apply IHt with (gamma) (LabelelTy T0) e'; auto. 
     + auto.  intuition. exists F. exists lo. auto.  
     + apply IHt with (gamma) (OpaqueLabeledTy T) e'; auto. 
     + inversion H7. auto.  intuition. exists F. exists lo. auto.   
     + apply IHt with (gamma) T0 e'; auto.
     + auto.  intuition. exists F. exists lo. subst. inversion H6. inversion H8.  subst. auto.  
     + apply IHt1 with (gamma) (classTy clsT) e1'; auto.
     + apply IHt2 with (gamma)  (classTy cls') e2'; auto.
     + inversion H11. rewrite H10. inversion H6.  intros.
        case_eq (beq_oid o0 o). intro. 
        assert (Some (Heap_OBJ cls F' l') = lookup_heap_obj (update_heap_obj h0 o (Heap_OBJ cls F' l')) o).
        apply lookup_updated with (o:=o) (ho:=(Heap_OBJ cls F' l'))
                  (ho':=(Heap_OBJ cls F lb)) (h:=h0) (h':=(update_heap_obj h0 o (Heap_OBJ cls F' l'))); auto.
        apply beq_oid_equal in H29. rewrite H29. 
        exists F'. exists l'. auto. rewrite H29 in H24. rewrite <- H7 in H24. inversion H24. 
       rewrite <- H32. auto. 
       intro. 
       assert (Some (Heap_OBJ cls_def0 F0 lo) = lookup_heap_obj (update_heap_obj h0 o (Heap_OBJ cls F' l')) o0).
       apply lookup_updated_not_affected with (o:=o) (ho:=(Heap_OBJ cls F' l'))
                 (h:=h0) (h':=(update_heap_obj h0 o (Heap_OBJ cls F' l'))) (o':=o0) 
              (ho':=(Heap_OBJ cls_def0 F0 lo)); auto. 
      intro contra. rewrite contra in H29. 
      assert (beq_oid o o = true). apply beq_oid_same. 
      rewrite H30 in H29. inversion H29.
      exists F0. exists lo. auto.
     + inversion H12. rewrite H11. inversion H7.  intros.
        case_eq (beq_oid o0 o). intro. 
        assert (Some (Heap_OBJ cls F' l') = lookup_heap_obj (update_heap_obj h0 o (Heap_OBJ cls F' l')) o).
        apply lookup_updated with (o:=o) (ho:=(Heap_OBJ cls F' l'))
                  (ho':=(Heap_OBJ cls F lo)) (h:=h0) (h':=(update_heap_obj h0 o (Heap_OBJ cls F' l'))); auto.
        apply beq_oid_equal in H30. rewrite H30. 
        exists F'. exists l'. auto. rewrite H30 in H25. rewrite <- H8 in H25. inversion H25. 
       rewrite <- H33. auto. 
       intro. 
       assert (Some (Heap_OBJ cls_def0 F0 lo0) = lookup_heap_obj (update_heap_obj h0 o (Heap_OBJ cls F' l')) o0).
       apply lookup_updated_not_affected with (o:=o) (ho:=(Heap_OBJ cls F' l'))
                 (h:=h0) (h':=(update_heap_obj h0 o (Heap_OBJ cls F' l'))) (o':=o0) 
              (ho':=(Heap_OBJ cls_def0 F0 lo0)); auto. 
      intro contra. rewrite contra in H30. 
      assert (beq_oid o o = true). apply beq_oid_same. 
      rewrite H31 in H30. inversion H30.
      exists F0. exists lo0. auto.
     + intuition. exists F. exists lo. auto. 
     + intuition. exists F. exists lo. auto.
     + apply IHt1 with (gamma) T0 s1'; auto.
     + intuition. exists F. exists lo. auto. 
     +  apply IHt with gamma T0 e'; auto. subst. 
      apply    extend_stack_reduction_preservation with T0; auto. 
     + intuition. exists F. exists lo. inversion H10. inversion H5. rewrite <-H23. auto. 
Qed.
*)

Lemma reduction_preserve_heap_pointer : forall t s s' h h', 
     forall CT T, has_type CT empty_context h t T ->
     wfe_heap CT h -> wfe_stack CT h s ->    field_wfe_heap CT h -> 
     forall t', reduction (Config CT t (SIGMA s h)) (Config CT t' (SIGMA s' h')) -> 
     (forall o cls_def F lo, lookup_heap_obj h o = Some  (Heap_OBJ cls_def F lo) 
                              -> exists F' lo', lookup_heap_obj h' o = Some  (Heap_OBJ cls_def F' lo') ).
Proof with eauto.
     intros  t s s' h h'.
     intros CT.
     induction t; intro T; intro typing; intro wfe_h; intro wfe_s; intro wfe_fields; intro t'; intro step; inversion step; inversion typing; auto. 
     + intuition. exists F. exists lo. auto.  
     + apply IHt with (classTy clsT) e'; auto.
     + inversion H10. auto. 
          inversion H5. auto.  intuition. exists F. exists lo. auto. 
     + apply IHt1 with (classTy T0) e'; auto.
     + apply IHt2 with (classTy arguT) e'; auto.
     + inversion H14. auto.  intuition. exists F. exists lo. auto.
     + inversion H14. auto.   intuition. exists F. exists lo. auto.  
     + inversion H11. rewrite H10. unfold add_heap_obj.
        intros.  
        case_eq (beq_oid o0 o). intro. apply beq_oid_equal in H21. 
        rewrite H21 in H18. assert (lookup_heap_obj h o = None). 
        apply fresh_oid_heap with (h:=h) (CT:=CT) (o:=o).
        auto. inversion H5. auto. rewrite H22 in H18. inversion H18.

        intro.  unfold lookup_heap_obj. 
        rewrite H21. fold lookup_heap_obj.  inversion H5. 
        rewrite <- H24. exists F0. exists lo. auto. 
     + apply IHt with T0 e'; auto. 
     + auto.  intuition. exists F. exists lo. auto.  
     + apply IHt with  (LabelelTy T) e'; auto. 
     + inversion H7. auto.  intuition. exists F. exists lo. auto.   
     + apply IHt with (LabelelTy T0) e'; auto. 
     + auto.  intuition. exists F. exists lo. auto.  
     + apply IHt with (OpaqueLabeledTy T) e'; auto. 
     + inversion H7. auto.  intuition. exists F. exists lo. auto.   
     + apply IHt with  T0 e'; auto.
     + auto.  intuition. exists F. exists lo. subst. inversion H6. inversion H8.  subst. auto.  
     + apply IHt1 with (classTy clsT) e1'; auto.
     + apply IHt2 with  (classTy cls') e2'; auto.
     + inversion H11. rewrite H10. inversion H6.  intros.
        case_eq (beq_oid o0 o). intro. 
        assert (Some (Heap_OBJ cls F' l') = lookup_heap_obj (update_heap_obj h0 o (Heap_OBJ cls F' l')) o).
        apply lookup_updated with (o:=o) (ho:=(Heap_OBJ cls F' l'))
                  (ho':=(Heap_OBJ cls F lb)) (h:=h0) (h':=(update_heap_obj h0 o (Heap_OBJ cls F' l'))); auto.
        apply beq_oid_equal in H29. rewrite H29. 
        exists F'. exists l'. auto. rewrite H29 in H24. rewrite <- H7 in H24. inversion H24. 
       rewrite <- H32. auto. 
       intro. 
       assert (Some (Heap_OBJ cls_def0 F0 lo) = lookup_heap_obj (update_heap_obj h0 o (Heap_OBJ cls F' l')) o0).
       apply lookup_updated_not_affected with (o:=o) (ho:=(Heap_OBJ cls F' l'))
                 (h:=h0) (h':=(update_heap_obj h0 o (Heap_OBJ cls F' l'))) (o':=o0) 
              (ho':=(Heap_OBJ cls_def0 F0 lo)); auto. 
      intro contra. rewrite contra in H29. 
      assert (beq_oid o o = true). apply beq_oid_same. 
      rewrite H30 in H29. inversion H29.
      exists F0. exists lo. auto.
     + inversion H12. rewrite H11. inversion H7.  intros.
        case_eq (beq_oid o0 o). intro. 
        assert (Some (Heap_OBJ cls F' l') = lookup_heap_obj (update_heap_obj h0 o (Heap_OBJ cls F' l')) o).
        apply lookup_updated with (o:=o) (ho:=(Heap_OBJ cls F' l'))
                  (ho':=(Heap_OBJ cls F lo)) (h:=h0) (h':=(update_heap_obj h0 o (Heap_OBJ cls F' l'))); auto.
        apply beq_oid_equal in H30. rewrite H30. 
        exists F'. exists l'. auto. rewrite H30 in H25. rewrite <- H8 in H25. inversion H25. 
       rewrite <- H33. auto. 
       intro. 
       assert (Some (Heap_OBJ cls_def0 F0 lo0) = lookup_heap_obj (update_heap_obj h0 o (Heap_OBJ cls F' l')) o0).
       apply lookup_updated_not_affected with (o:=o) (ho:=(Heap_OBJ cls F' l'))
                 (h:=h0) (h':=(update_heap_obj h0 o (Heap_OBJ cls F' l'))) (o':=o0) 
              (ho':=(Heap_OBJ cls_def0 F0 lo0)); auto. 
      intro contra. rewrite contra in H30. 
      assert (beq_oid o o = true). apply beq_oid_same. 
      rewrite H31 in H30. inversion H30.
      exists F0. exists lo0. auto.
     + intuition. exists F. exists lo. auto. 
     + intuition. exists F. exists lo. auto.
     + apply IHt1 with T0 s1'; auto.
     + intuition. exists F. exists lo. auto. 
     +  apply IHt with T0 e'; auto. subst. 
      apply    extend_stack_reduction_preservation with T0; auto. 
     + intuition. exists F. exists lo. inversion H10. inversion H5. inversion H9. subst. auto. 
Qed.






Theorem progress : forall t T sigma  CT s h, 
  field_wfe_heap CT h -> sigma = SIGMA s h ->  wfe_heap CT h -> wfe_stack CT h s -> 
  has_type CT empty_context h t T -> value t \/ (exists config', Config CT t sigma ==> config').
Proof with auto.
  intros t T sigma CT s h.
  intro wfe_fields. intros.
  remember (empty_context) as Gamma.
  induction H2; subst Gamma... 
(* TVar *)
- inversion H2.

(* null *)
-  left. apply v_null.
(* field access *)
- right. 
    destruct IHhas_type. auto. auto. auto. auto.  
    + auto. 
    + 
      inversion H6. rewrite <- H7 in H2. 
      assert (exists F lb, lookup_heap_obj h o = Some (Heap_OBJ cls_def F lb)).
       apply wfe_oid with (gamma:=empty_context) (o:=o) (ct:=CT) (s:=s) (h:=h) 
                          (sigma:=sigma) (cls_def:=cls_def) (cn:=clsT). auto. auto. auto. auto. 
       destruct H8 as [F]. destruct H8 as [lb].

      assert (exists v, F(f) = Some v).
      apply field_val_of_heap_obj with (h:=h) (o:=o)  (CT:=CT) 
                              (cls_def:=cls_def) (F:=F) (lo:=lb) (cls':=cls') (fields:=fields_def).
      auto. auto. auto. auto. auto. 



      destruct H9 as [v].
      remember (join_label lb (current_label sigma)) as l'.
      remember (update_current_label s l') as s'.
      remember (SIGMA s' h) as sigma'.
            exists (Config CT v sigma'). apply ST_fieldRead2 with 
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
    {rewrite <- H8  in H2. inversion H2. }
    
     (* call field access on opaque label value*)
    {rewrite <- H8  in H2. inversion H2. }

     (* context rule *)
    + destruct H6. destruct x. 
    exists (Config CT (FieldAccess t f) s0). pose proof (ct_consist CT c e t sigma s0). 
    destruct H7.  auto.  
    apply ST_fieldRead1 with (sigma:=sigma) (sigma':=s0) (e:=e) (e':=t) (f:=f). assumption.

    exists Error_state. apply ST_fieldRead3. auto.

(* method call *)
- 
   destruct IHhas_type1. auto. auto. auto. auto.
    + auto.
       + right. inversion H6; try (rewrite <- H7 in H2_; inversion H2_).
          (* case analysis for argument: if the argument is a value *)
             destruct IHhas_type2. auto. auto. auto. auto. auto. subst. 
            remember (sf_update empty_stack_frame arg_id argu) as sf. 
            remember (SIGMA s h ) as sigma.
            remember (current_label sigma) as l.
            remember (Labeled_frame l sf) as lsf. 
            remember (cons lsf s) as s'.
            remember (SIGMA s' (get_heap sigma)) as sigma'. 

            auto. 
            exists (Config CT ((Return body)) sigma').
            destruct H15 as [F]. destruct H as [lo].
            apply ST_MethodCall3 with (sigma:=sigma) (sigma':=sigma') (o:=o) (s:=s) (h:=h) (cls:=cls_def) (fields:=F) 
                                       (v:=argu) (lx:=lo) (l:=l) 
                                       (cls_a:=arguT) (s':=s') (sf:=sf) (lsf:=lsf) (arg_id:=arg_id) 
                                       (body:=body) (meth:=meth) (returnT:=returnT) ;auto.
            rewrite <- H10 in H2. inversion H2.  auto. 
          (* case analysis for argument, if the argument is not a value *)
            subst.
                destruct H16 as [config']. destruct config'. rename t into t'.
                pose proof (excluded_middle_opaqueLabel argu).
                destruct H4.
                  (* case for argu = unlabelOpaque t *)
                  destruct H4 as [t]. 
                  rewrite -> H4 in H. inversion H. subst. 
                  exists (Config c (MethodCall (ObjId o) meth (unlabelOpaque e')) s0).
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
                      exists (Config c (Return body) sigma'').  
                      destruct H15 as [F]. destruct H5 as [lo]. destruct H4 as [lo].
                      apply ST_MethodCall_unlableOpaque with (sigma:=sigma) (sigma':=sigma'') (o:=o) (s:=s) (h:=h) 
                                            (cls:=cls_def0) (fields:=F) (v:=t') (lx:=lo) (l':=l') (lb:=lb) (s':=s')
                                           (sf:=sf) (lsf:=lsf) (arg_id:=arg_id) (cls_a:=arguT) (body:=body) 
                                           (meth:=meth) (returnT:=returnT); auto. 

                      inversion H2_0. inversion H11. auto. 
                      rewrite <- H10 in H2. inversion H2. rewrite <- H7. auto.  

                      auto. 
                  (*exception case
                  subst. exists NPE. exists (SIGMA s h).
                  apply ST_MethodCallOpaqueDataException with (sigma:=(SIGMA s h)) (o:=o).   *)

                  (* case for argu <> unlabelOpaque t *)
                  exists (Config CT (MethodCall (ObjId o) meth t') s0). 
                  apply ST_MethodCall2 with (sigma:=(SIGMA s h)) (sigma':=s0) (v:=((ObjId o))) 
                                            (e:=argu) (e':=t') (id:=meth).
                  intro. intro. intro. 
                  
                  assert (argu <> unlabelOpaque t).  apply (H4 t). apply (H4 t). auto.
                  assert (CT = c). apply ct_consist with (t:=argu) (t':=t') (sigma:=(SIGMA s h)) (sigma':=s0); auto. 
                  rewrite <- H7 in H. auto. apply v_oid.
                   
                  exists Error_state. 
                   apply ST_MethodCall5 with (sigma:=(SIGMA s h)) (v:=(ObjId o)) (e:=argu) (id:=meth).
                  intros. intro contra. rewrite contra in H. inversion H. inversion H4;
                  try (rewrite <- H13 in H9; inversion H9; fail); try (rewrite <- H16 in H9; inversion H9).
                  rewrite <- H11 in H7. auto. auto. auto. subst. inversion H2_. 

                   exists Error_state. 
                  apply ST_MethodCallException with (sigma:= (SIGMA s h) ) (v:=argu) (meth:=meth). 

                  rewrite <- H8 in H2_. inversion H2_. 
                rewrite <- H8 in H2_. inversion H2_.                 

      +  right. destruct H6 as [config']. destruct config'. 

            exists (Config CT (MethodCall t meth argu) (s0)).
                  apply ST_MethodCall1 with (sigma:=sigma) (sigma':=s0) (e2:=argu) (e:=e) (e':=t) (id:=meth). 
                  assert (CT = c). apply ct_consist with (t:=e) (t':=t) (sigma:=sigma) (sigma':=s0); auto. 
                  subst. auto. 

            exists Error_state. apply ST_MethodCall4 with (sigma:=sigma) (e:=e) (e2:=argu) (id:=meth). auto. 

(* new expression *)
- right. inversion H0.
    destruct H2 as [cls_def]. destruct H2 as [field_defs]. destruct H2 as [method_defs].
    destruct H2. 
(*
    assert (exists o, empty_heap o = None). 
      unfold empty_heap. auto. exists (OID 0). auto. 
      destruct H7 as [o]. 
*)
      remember (get_fresh_oid h) as o.
      remember (init_field_map (find_fields cls_def) empty_field_map) as F.
      remember (current_label sigma) as lb. 
      remember  (add_heap_obj h o (Heap_OBJ cls_def F lb)) as h'.
      remember (SIGMA s h') as sigma'.
      exists (Config CT (ObjId o) sigma').
       
      (*destruct H3 as [field_defs]. destruct H3 as [method_defs].*)
      apply ST_NewExp with (sigma:=sigma) (sigma':=sigma') (F:=F) (o:=o) (h:=h) (cls:=cls_def)
                  (h':=h') (s:=s) (lb:=lb) (cls_name:=cls_name) 
                  (field_defs:= field_defs) (method_defs:=method_defs).

      subst; auto. auto.  auto.  auto. auto. auto.  auto. auto.   
      
    destruct H2 as [cls_def']. destruct H2 as [field_defs']. destruct H2 as [method_defs'].
    destruct H2. 

      remember (current_label sigma) as lb. 
    remember (get_fresh_oid h) as o'.
      remember (init_field_map (find_fields cls_def') empty_field_map) as F'.
      remember (add_heap_obj h o' (Heap_OBJ cls_def' F' lb)) as h''.
      remember (SIGMA s h'') as sigma''.
      exists (Config CT (ObjId o') sigma''). 

      apply ST_NewExp with (sigma:=sigma) (sigma':=sigma'') 
                                          (F:=F') (o:=o') (h:=h) (cls:=cls_def')
                                          (h':=h'') (s:=s) (lb:=lb) (cls_name:=cls_name)
                                          (field_defs:=field_defs') (method_defs:=method_defs').
      auto. auto.  auto.  auto. auto. auto.  auto. auto. 

(* label *)
- left. apply  v_label.


(* label Data *)
- right. destruct IHhas_type2. auto. auto. auto. auto. auto. 
            destruct IHhas_type1. auto. auto. auto. auto. auto.
            
            (* subgoal #1 *)
           exists (Config CT (v_l e lb) sigma).
                apply ST_LabelData2 with (sigma:=sigma) (lb:=lb) (v:=e).  auto. 

            (* subgoal #2 *)  
                destruct H3 as [config']. inversion H3.  
                destruct H2 as [config']. destruct config'. 
                    exists (Config CT (labelData t lb) s0).
                    apply ST_LabelData1 with (sigma:=sigma) (sigma':=s0) (e:=e) (e':=t) (lb:=lb).
                    auto.
                    assert (CT = c). apply ct_consist with (t:=e) (t':=t) (sigma:=sigma) (sigma':=s0); auto. 
                    rewrite <- H3 in H2.  auto. 
           (* subgoal #4*)
               exists Error_state. 
                  apply ST_LabelDataError with (e:=e) (sigma:=sigma) (lb:=lb). auto. 

(* unlabel : *)
- right.
 
            destruct IHhas_type. auto. auto. auto. auto. auto.
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
                exists (Config CT v sigma'). 
                apply ST_unlabel2 with (sigma:=sigma) (s':=s') (sigma':=sigma') (l':=l') (s:=s) (h:=h) (lb:=lb) (v:=v). 
                auto. auto. auto. auto. auto.

            (* subgoal #3 *)
                rewrite <- H5 in H2.  inversion H2. 

              + destruct H3 as [config']. 
                 destruct config'. 
                 exists (Config CT (unlabel t) s0). 
                 apply ST_unlabel1 with (sigma:=sigma) (sigma':=s0) (e:=e) (e':=t). auto. 
                assert (CT = c). apply ct_consist with (t:=e) (t':=t) (sigma:=sigma) (sigma':=s0); auto. 
                    rewrite <- H4 in H3. auto.  
                 exists Error_state. apply ST_unlabelContextError with (sigma:=sigma) (e:=e). auto. 

(* label Of *)
(* same issue as above, we may need to add (v_l v lb) as a value*)
- right. 
         destruct IHhas_type. auto. auto. auto. auto. auto.  
            (* subgoal #1 *)
                + inversion H3. rewrite <- H4 in H2. inversion H2. 
                    rewrite <- H4 in H2. inversion H2. 
                    exists Error_state.  apply ST_labelOfDataException with (sigma:=sigma).
                    rewrite <- H4 in H2.  inversion H2.
                    
                   exists (Config CT (l lb) (sigma)). apply ST_labelof2 with (v:=v) (lb:=lb).

                    rewrite <- H5 in H2. inversion H2. 
             (* subgoal #2 *)
                + destruct H3 as [config']. destruct config'. 
                    exists (Config CT (labelOf t) s0). apply ST_labelof1 with (sigma:=sigma) (sigma':=s0) (e:=e) (e':=t).
                    assert (CT = c). apply ct_consist with (t:=e) (t':=t) (sigma:=sigma) (sigma':=s0); auto. 
                    rewrite <- H4 in H3. auto. 
    
             (*error state *)
                 exists Error_state. apply ST_labelofCtxError with (e:=e) (sigma:=sigma). auto. 

(* unlabel opaque *)
- right. 
         destruct IHhas_type. auto. auto. auto. auto. auto. 
            (* subgoal #1 *)
                + inversion H3. rewrite <- H4 in H2. inversion H2. 
                    rewrite <- H4 in H2. inversion H2. 
                    exists Error_state.  apply ST_unlabel_opaqueDataException with (sigma:=sigma).
                    rewrite <- H4 in H2.  inversion H2.
              
                     rewrite <- H5 in H2. inversion H2. 
 
                remember ( join_label lb (current_label sigma)) as l'.
                remember (update_current_label s l') as s'.
                remember (SIGMA s' (get_heap sigma)) as sigma'.
                exists (Config CT v sigma'). 
                apply ST_unlabel_opaque2 with (sigma:=sigma) (s':=s') (sigma':=sigma') (l':=l') (s:=s) (h:=h) (lb:=lb) (v:=v). 
                auto. auto. auto. auto. 

             (* subgoal #2 *)
                + destruct H3 as [config']. destruct config'. 
                    exists (Config CT (unlabelOpaque t) s0). apply ST_unlabel_opaque1 with (sigma:=sigma) (sigma':=s0) (e:=e) (e':=t). auto.
                  assert (CT = c). apply ct_consist with (t:=e) (t':=t) (sigma:=sigma) (sigma':=s0); auto. 
                    rewrite <- H4 in H3. auto.  
                exists Error_state. apply ST_unlabel_opaque_ctx_error with (sigma:=sigma) (e:=e).  auto. 

(* Skip *)
  - left. apply v_none. 

(* assignment *)
- right. destruct IHhas_type. auto. auto. auto. auto. auto. 
                  remember (update_stack_top s x e) as s0.
                  remember (SIGMA s0 h) as sigma'.
                  exists (Config CT Skip sigma').
                  apply ST_assignment2 with (sigma:=sigma) (sigma':=sigma') (id:=x) (v:=e) (s':=s0) (s:=s) (h:=h).
                  auto. auto. auto. auto.

                  destruct H4 as [config']. destruct config'. 
                  exists (Config CT (Assignment x t) s0). 
                  apply ST_assignment1 with (sigma:=sigma) (sigma':=s0) (e:=e) (e':=t) (id:=x).   
                  assert (CT = c). apply ct_consist with (t:=e) (t':=t) (sigma:=sigma) (sigma':=s0); auto. 
                    rewrite <- H5 in H4. auto.  
                  auto.

                  exists Error_state. 
                  apply ST_assignment_ctx_error with (sigma:=sigma) (e:=e) (id:=x). auto.  

(* FieldWrite *)
-right. 
      destruct IHhas_type1. auto. auto. auto. auto. auto. 
       + inversion H4. 
          (* case analysis for argument: if the argument is a value *)
             destruct IHhas_type2. auto. auto. auto. auto. auto. subst.
            assert (exists fieldsMap lb, lookup_heap_obj h o = Some (Heap_OBJ cls_def fieldsMap lb)).
            remember (SIGMA s h ) as sigma.
            apply wfe_oid with (o:=o) (ct:=CT) (gamma:=empty_context) (s:=s) (h:=h) 
                          (sigma:=sigma) (cls_def:=cls_def) (cn:=clsT). auto. auto. auto. auto. auto.
            destruct H as [F]. destruct H as [lb]. 
            remember (SIGMA s h ) as sigma.
            remember (join_label lb (current_label sigma)) as l'. 
            remember (fields_update F f e) as F'. 
            remember (update_heap_obj h o (Heap_OBJ cls_def F' l')) as h'.
            remember (SIGMA s h') as sigma'.
            exists (Config CT Skip sigma').
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
                  exists (Config CT (FieldWrite (ObjId o) f (unlabelOpaque e')) sigma').
                  apply ST_fieldWrite2 with (sigma:=(SIGMA s h)) (sigma':=sigma') 
                                            (v:=(ObjId o)) (e2:=unlabelOpaque t) (e2':=unlabelOpaque e') (f:=f).
                  intros. subst. intro contra. inversion contra.  rewrite H8 in H10. 
                  inversion H5. 
                  rewrite <- H7 in H10.  inversion H10.                   rewrite <- H7 in H10.  inversion H10. 
                  rewrite <- H7 in H10.  inversion H10.                   rewrite <- H7 in H10.  inversion H10. 
                  rewrite <- H9 in H10.  inversion H10.                   rewrite <- H9 in H10.  inversion H10. 
                  auto. auto. 

                  exists Error_state. subst. apply ST_fieldWrite_ctx_error2 
                        with (sigma:=(SIGMA s h)) (f:=f) (v:=(ObjId o)) (e2:=(unlabelOpaque t)).

                  intros. intro contra. inversion contra. rewrite H8 in H10. inversion H5. 
                  rewrite <- H7 in H10.  inversion H10.                   rewrite <- H7 in H10.  inversion H10. 
                  rewrite <- H7 in H10.  inversion H10.                   rewrite <- H7 in H10.  inversion H10. 
                  rewrite <- H9 in H10.  inversion H10.                   rewrite <- H9 in H10.  inversion H10. 
                  auto. auto. 

                  assert (exists fieldsMap lb, lookup_heap_obj h o = Some (Heap_OBJ cls_def fieldsMap lb)).
                      apply wfe_oid with (o:=o) (ct:=CT) (gamma:=empty_context) (s:=s) (h:=h) 
                                    (sigma:=sigma) (cls_def:=cls_def) (cn:=clsT). auto. auto. auto. auto. auto.
                      destruct H14 as [F]. destruct H14 as [lo]. 
                      remember (fields_update F f v) as F'. 
                      remember (join_label lo lb) as l''. 
                      remember (update_heap_obj h o (Heap_OBJ cls_def F' l'')) as h'.
                      remember (SIGMA s h') as sigma''.

                      exists (Config CT Skip sigma'').
                      apply ST_fieldWrite_opaque with (sigma:=(SIGMA s h)) (sigma':=sigma'') (o:=o) (s:=s) (h:=h) (h':=h') (f:=f) 
                                                      (lb:=lb) (lo:=lo) (cls:=cls_def) (F:=F) (F':=F') (v:=v) (l':=l'') (e2:=e).
                      rewrite <- H7 in H5. auto. auto. auto. auto. auto. auto.  auto.

                      rewrite H5 in H2_0. inversion H2_0. rewrite <-H7 in H19. inversion H19. auto. 

                      exists Error_state. 

                      apply ST_fieldWrite_ctx_error2 with (sigma:=(SIGMA s h)) (f:=f) (v:=(ObjId o)) (e2:=e).
                       intros. rewrite H5. intro contra. inversion contra. rewrite <- H13 in H10.
                      rewrite H8 in H11. auto. auto. subst. auto.   

                  (* case for argu <> unlabelOpaque t *)
                  destruct config'. 
                  exists (Config CT (FieldWrite (ObjId o) f t) s0). 
                  apply ST_fieldWrite2 with (sigma:=(SIGMA s h)) (sigma':=s0) (v:=((ObjId o))) 
                                            (e2:=e) (e2':=t) (f:=f).
                  intros. apply H5. apply v_oid. 
                  assert (CT = c). apply ct_consist with (t:=e) (t':=t) (sigma:=(SIGMA s h)) (sigma':=s0); auto. 
                    rewrite <- H6 in H. auto.  

                  exists Error_state. 
                      apply ST_fieldWrite_ctx_error2 with (sigma:=(SIGMA s h)) (f:=f) (v:=(ObjId o)) (e2:=e).
                       intros. apply H5.  auto. auto. 
     
                  destruct  IHhas_type2.  auto. auto. auto. auto.  
                  rewrite <- H5 in H2_. inversion H2_.                   rewrite <- H5 in H2_. inversion H2_.
                  rewrite <- H5 in H2_. inversion H2_.
                  exists Error_state.
                  apply ST_fieldWriteException with (sigma:=sigma) (f:=f) (v:=e). 

                  rewrite <- H5 in H2_. inversion H2_.                   rewrite <- H6 in H2_. inversion H2_.
                  rewrite <- H6 in H2_. inversion H2_.       


          +    destruct H4 as [config'].
                 destruct config'. 
                  exists (Config CT (FieldWrite t f e) (s0)). 
                  apply ST_fieldWrite1 with (sigma:=sigma) (sigma':=s0) (f:=f) (e1:=x) (e1':=t) (e2:=e).
                  assert (CT = c). apply ct_consist with (t:=x) (t':=t) (sigma:=sigma) (sigma':=s0); auto. 
                    rewrite <- H5 in H4. auto.  
        
              exists Error_state. 
              apply ST_fieldWrite_ctx_error1 with (sigma:=sigma) (f:=f) (e1:=x) (e2:=e). auto. 

(* if *)
- inversion H2_0. inversion H7.
(* sequence *)
- right. destruct IHhas_type1; auto.
    exists (Config CT e2 sigma).
    
   apply ST_seq2 with (sigma:=sigma) (v:=e1) (s:=e2); auto.
  
  destruct H2 as [config'].
  destruct config'.
  exists (Config CT (Sequence t e2) s0). 
   apply ST_seq1 with (sigma:=sigma) (s1:=e1) (s2:=e2) (s1':=t); auto.
   assert (CT = c). apply ct_consist with (t:=e1) (t':=t) (sigma:=sigma) (sigma':=s0); auto. 
                  rewrite <- H3 in H2. auto. 

  exists Error_state. apply ST_seq_ctx_error with (sigma:=sigma) (s1:=e1) (s2:=e2).
  auto. 

(* return e *)
- right. destruct IHhas_type; auto.
  assert (exists lsf s', s = cons lsf s'). 
  apply stack_not_nil with (sigma:=sigma) (CT:=CT) (s:=s) (h:=h).
  auto. auto. auto.
  destruct H5 as [lsf0]. destruct H5 as [s0].

destruct s0.
exists Error_state. 
  apply ST_return_terminal with (s:=s) (h:=h) (lsf:=lsf0); auto.

  remember (get_current_label s) as l'.
  remember (SIGMA (l0 :: s0) h) as sigma'.  
  exists (Config CT (v_opa_l e l') sigma'). 
  apply ST_return2 with s (l0 :: s0) h lsf0; auto. 
  intro contra. inversion contra. 

  destruct H4 as [config'].
  destruct config'.

  (* case analysis here*)

Lemma return_helper : forall e t ct s h s' h', 
  forall T, has_type CT empty_context h e T ->
  wfe_heap CT h ->  wfe_stack CT h s -> 
  Config CT e sigma ==> Config CT t s ->field_wfe_heap CT h ->
  Config CT e sigma ==> Config CT t s0

 
  exists (Config CT (Return t) s0). 
  apply ST_return1 with (sigma:=sigma) (sigma':=s0) (e:=e) (e':=t). 

  assert (CT = c). apply ct_consist with (t:=e) (t':=t) (sigma:=sigma) (sigma':=s0); auto. 
                  rewrite <- H5 in H4. auto. 
  auto.

  exists Error_state. apply ST_return_ctx_error with (sigma:=sigma) (e:=e). auto. 

exists (Config CT e sigma').
  apply ST_return2 with (sigma:=sigma) (sigma':=sigma') (v:=e)
                                    (s:=s) (s':=(l0 :: s0)) (h:=h) (lsf:=lsf0) (l':=l').
  auto. auto. auto. intuition. inversion H6. auto. auto. auto. 
  


(* ObjId o *)
- left. apply v_oid. 

(* v_l *)
- left. apply v_labeled. auto.  

(* v_opl_l *)
- left. apply v_opa_labeled. auto.
Qed.

Theorem preservation : forall CT s s' h h' sigma sigma',
    field_wfe_heap CT h -> sigma = SIGMA s h ->  
    wfe_heap CT h -> wfe_stack CT h s -> sigma' = SIGMA s' h' -> 
    forall t T, has_type CT empty_context h t T -> 
     forall t',  Config CT t sigma ==> Config CT t' sigma' ->
     ( has_type CT empty_context h' t' T) .
Proof with auto.
   intros CT s s' h h' sigma sigma'. intro H_field_wfe. 
  intro H_sigma. intro H_wfe_heap. intro H_wfe_stack. intro H_sigma'.
  induction t. (*induction on the terms *)
  (* (Tvar i) *)
  + intro T. intro typing. intro t'.  intro step.
        inversion step.   inversion typing. subst.   inversion H12.
  (* null *)
  + intro T. intro typing. intro t'.  intro step.
        inversion step.  

  (* field access *)
  + intro T'. intro typing. intro t'. inversion typing. intro step. 
     inversion step. subst. apply T_FieldAccess with (Gamma:=empty_context) (e:=e') (f:=i) 
            (cls_def:=cls_def) (CT:=CT) (clsT:=clsT) (cls':=cls') (h:=h') 
            (fields_def:=(find_fields cls_def)). apply IHt. 
             auto. auto. auto. auto. auto.

   assert (wfe_heap CT h' /\ wfe_stack CT h' s' /\ field_wfe_heap CT h').
   apply reduction_preserve_wfe with (t:=(FieldAccess t i)) (t':=t') (T:=T')  (sigma:=sigma) (sigma':=sigma')
           (CT:=CT) (s:=s) (s':=s') (h:=h) (h':=h').
   auto. auto. auto. auto. auto. auto. auto.

   rewrite <- H10 in H1. inversion H1. 

   destruct H28 as [field_defs]. destruct H28 as [method_defs].
      assert (v = null \/
             (exists
                (o' : oid) (field_defs0 : list field) (method_defs0 : 
                                                       list method_def) 
              (field_cls_def : CLASS) (F' : FieldMap) (lo : Label),
                v = ObjId o' /\
                field_cls_def =
                class_def cls' field_defs0 method_defs0 /\
                lookup_heap_obj h' o'  = Some (Heap_OBJ field_cls_def F' lo) /\
                CT cls' = Some field_cls_def)
      ).

    apply field_consist_typing with (CT:=CT)  (v:=v) (h:=h') (o:=o) (cls_def:=cls)
             (F:=fields) (f:=i) (lb:=lb) (field_cls_name:=cls') (cls_name:=cls_name) 
             (field_defs:=field_defs) (method_defs:=method_defs).
    apply H21. apply H21. rewrite H_sigma' in H20. inversion H20. auto. subst. 
    inversion H15. rewrite <- H3 in H16. rewrite <- H16 in H29.
    destruct H29 as [F0]. destruct H as [lo0]. inversion H. auto.  
    rewrite <- H2 in H24. inversion H24. rewrite <- H31 in H6.
    rewrite H28 in H6. unfold find_fields in H6.
    rewrite <- H6. auto. subst. auto. 

    destruct H30. 
    subst. apply T_null with (Gamma:=empty_context) (h:=h') (T:=(classTy cls')) (CT:=CT). 

    destruct H30 as [o']. destruct H30 as [field_defs0]. destruct H30 as [method_defs0]. 
    destruct H30 as [field_cls_def]. destruct H30 as [F']. destruct H30 as [lx]. 
    destruct H30. subst. destruct H31. destruct H0. 


    apply T_ObjId with (h:=h') (Gamma:=empty_context) (CT:=CT) (cls_name:=cls') 
                                  (cls_def:=field_cls_def) (o:=o').

     auto. auto.  
     exists field_defs0. exists method_defs0. auto. 
    exists  F'. exists lx. auto. 

  (* MethodCall  *)
    + intro T'. intro typing. intro t'. inversion typing. intro step. 
        inversion step. 
      (* reduction on the object  *)
        - apply T_MethodCall with (Gamma:=empty_context) (e:=e') (meth:=i) (argu:=t2)
                            ( CT:=CT) (h:=h') (T:=T) (returnT:=returnT) (cls_def:=cls_def)
                            (body:=body) (arg_id:=arg_id) (arguT:=arguT) (Gamma':=Gamma').

      apply IHt1; auto. 

      apply heap_preserve_typing with (h:=h).
      intros o cls_def0 F lo. intro.  

      apply reduction_preserve_heap_pointer with (t:=t1) (s:=s) (s':=s') (h:=h) (h':=h')
                             (CT:=CT) (gamma:=empty_context) (T:=(classTy T))
                              (t':=e') (F:=F) (lo:=lo); auto.
     rewrite <- H_sigma. rewrite <-H_sigma'.
      auto.  auto. auto. auto. auto. auto. auto.
      apply heap_preserve_typing with (h:=h).
      intros o cls_def0 F lo. intro.  
      apply reduction_preserve_heap_pointer with (t:=t1) (s:=s) (s':=s') (h:=h) (h':=h')
                             (CT:=CT) (gamma:=empty_context) (T:=(classTy T))
                              (t':=e') (F:=F) (lo:=lo); auto. 
     rewrite <- H_sigma. rewrite <-H_sigma'.
      auto.  auto. 
      apply heap_preserve_typing with (h:=h).
      intros o cls_def0 F lo. intro.  
      apply reduction_preserve_heap_pointer with (t:=t1) (s:=s) (s':=s') (h:=h) (h':=h')
                                   (CT:=CT) (gamma:=empty_context) (T:=(classTy T))
                                    (t':=e') (F:=F) (lo:=lo); auto. 
     rewrite <- H_sigma. rewrite <-H_sigma'.  auto.  auto.

      (* reduction on the argument  *)
        -  apply T_MethodCall with (Gamma:=empty_context) (e:=t1) (meth:=i) (argu:=e')
                    ( CT:=CT) (h:=h') (T:=T) (returnT:=returnT) (cls_def:=cls_def)
                            (body:=body) (arg_id:=arg_id) (arguT:=arguT) (Gamma':=Gamma').
          apply heap_preserve_typing with (h:=h).
          intros o cls_def0 F lo. intro. 

          apply reduction_preserve_heap_pointer with (t:=t2) (s:=s) (s':=s') (h:=h) (h':=h')
                                 (CT:=CT) (gamma:=empty_context) (T:=classTy arguT)
                                  (t':=e') (F:=F) (lo:=lo); auto. 
         rewrite <- H_sigma. rewrite <-H_sigma'.
          auto.  auto. auto. auto. auto. auto. auto.

          apply heap_preserve_typing with (h:=h).
          intros o cls_def0 F lo. intro. 

          apply reduction_preserve_heap_pointer with (t:=t2) (s:=s) (s':=s') (h:=h) (h':=h')
                                 (CT:=CT) (gamma:=empty_context) (T:=classTy arguT)
                                  (t':=e') (F:=F) (lo:=lo); auto. 
         rewrite <- H_sigma. rewrite <-H_sigma'. auto.  auto. 

apply heap_preserve_typing with (h:=h).
          intros o cls_def0 F lo. intro. 

          apply reduction_preserve_heap_pointer with (t:=t2) (s:=s) (s':=s') (h:=h) (h':=h')
                                 (CT:=CT) (gamma:=empty_context) (T:=classTy arguT)
                                  (t':=e') (F:=F) (lo:=lo); auto. 
         rewrite <- H_sigma. rewrite <-H_sigma'. auto.  auto. 

      (* normal return  *)
          -  apply heap_preserve_typing with (h:=h).
          intros o0 cls_def0 F0 lo0. intro. 

          apply reduction_preserve_heap_pointer with (t:=(MethodCall t1 i t2)) (s:=s) (s':=s') (h:=h) (h':=h')
                                 (CT:=CT) (gamma:=empty_context) (T:=T')
                                  (t':=t') (F:=F0) (lo:=lo0); auto. 
         rewrite <- H_sigma. rewrite <-H_sigma'. auto. subst.  auto.
          inversion H2. inversion H20. destruct H10 as [F']. destruct H10 as [lo'].
         rewrite H15 in H10. rewrite H10 in H21. inversion H21. rewrite <- H16 in H1. 
          rewrite <- H1 in H4. inversion H4. rewrite <- H19 in H22. rewrite H5 in H22. 
          inversion H22.  rewrite <- H15. auto.  
      (* opaque return  *)
      - subst. apply heap_preserve_typing with (h:=h).
          intros o0 cls_def0 F0 lo0. intro. 

          apply reduction_preserve_heap_pointer with 
                    (t:=(MethodCall (ObjId o) i (unlabelOpaque (v_opa_l v lb))))
                     (s:=s) (s':=s') (h:=h) (h':=h')
                                 (CT:=CT) (gamma:=empty_context) (T:= (classTy returnT))
                                  (t':=(Return body0)) (F:=F0) (lo:=lo0); auto. 

          inversion H2. inversion H20. destruct H10 as [F']. destruct H10 as [lo'].
         rewrite H15 in H10. rewrite H10 in H21. inversion H21. rewrite <- H16 in H1. 
          rewrite <- H1 in H4. inversion H4. rewrite <- H19 in H27. rewrite H5 in H27. 
          inversion H27.  rewrite <- H15. auto.

(* new expression  *)
    + intro T. intro typing. intro t'.  intro step. 
   assert (wfe_heap CT h' /\ wfe_stack CT h' s' /\ field_wfe_heap CT h').
   apply reduction_preserve_wfe with (t:=(NewExp c)) (t':=t') (T:=T)  (sigma:=sigma)
           (sigma':=sigma') (CT:=CT) (s:=s) (s':=s') (h:=h) (h':=h').
   auto. auto. auto. auto. auto. auto. auto.   
      inversion step. inversion typing. 
      apply T_ObjId with (h:=h') (Gamma:=empty_context) (CT:=CT) (o:=o)
                (cls_name:=c) (cls_def:=cls). 
      assert (lookup_heap_obj h' o = Some (Heap_OBJ cls F lb)).
      rewrite H_sigma' in H12.       inversion H12.  rewrite H11.       unfold add_heap_obj. 
      assert (beq_oid o o = true). apply beq_oid_same.
      unfold lookup_heap_obj. rewrite H19. auto.
      assert (exists cls_name field_defs method_defs, 
                CT cls_name = Some cls /\ cls = (class_def cls_name field_defs method_defs)).
      apply heap_consist_ct with (h:=h') (o:=o)(F:=F) (lo:=lb).
      apply H. auto. auto. exists field_defs. exists method_defs.  auto.

      rewrite H_sigma' in H12.       inversion H12.  rewrite H11.       unfold add_heap_obj. 
      assert (beq_oid o o = true). apply beq_oid_same.
     unfold lookup_heap_obj. rewrite H19. auto.
      exists F. exists lb. auto.

(* Label  *)
    + intro T. intro typing. intro t'.  intro step. 
       inversion step. 
 
(* label data *)
    + intro T. intro typing. intro t'.  intro step.
        inversion step.   inversion typing.
        apply T_labelData with (h:=h') (Gamma:=empty_context) (lb:=l0) (CT:=CT) (e:=e') (T:=T0).
        apply T_label. apply IHt; auto. inversion typing.
        apply T_v_l with (h:=h') (Gamma:=empty_context) (lb:=l0) (CT:=CT) (v:=t) (T:=T0).
        apply T_label. 
        apply heap_preserve_typing with (h:=h).
          intros o0 cls_def0 F0 lo0. intro. 
        apply reduction_preserve_heap_pointer with 
                    (t:=(labelData t l0))
                     (s:=s) (s':=s') (h:=h) (h':=h')
                                 (CT:=CT) (gamma:=empty_context) (T:= T)
                                  (t':=t') (F:=F0) (lo:=lo0); auto.
        rewrite <- H_sigma.         rewrite <- H_sigma'. auto. auto. auto.

(* unlabel *)
    + intro T. intro typing. intro t'.  intro step.
        inversion step.   inversion typing.
        apply T_unlabel. apply IHt. auto. auto.
        inversion typing. rewrite <- H0 in H13. inversion H13. 
        apply heap_preserve_typing with (h:=h).
          intros o0 cls_def0 F0 lo0. intro. 
        apply reduction_preserve_heap_pointer with 
                    (t:=(unlabel t) )
                     (s:=s) (s':=s') (h:=h) (h':=h')
                                 (CT:=CT) (gamma:=empty_context) (T:= T)
                                  (t':=t') (F:=F0) (lo:=lo0); auto.
         rewrite <- H_sigma.         rewrite <- H_sigma'. auto.
        rewrite <- H2. auto.

(* Label of  *)
   + intro T. intro typing. intro t'.  intro step.
        inversion step.   inversion typing.
        apply T_labelOf with (T:=T0).  apply IHt. auto. auto. 
        inversion typing. apply T_label.

(* unlabelopaque  *)
   + intro T. intro typing. intro t'.  intro step.
        inversion step.   inversion typing.
        apply T_unlabelOpaque. apply IHt. auto. auto.
        inversion typing. rewrite <- H0 in H12. inversion H12. rewrite <- H2.  
        apply heap_preserve_typing with (h:=h).
          intros o0 cls_def0 F0 lo0. intro. 
        apply reduction_preserve_heap_pointer with 
                    (t:=(unlabelOpaque t) )
                     (s:=s) (s':=s') (h:=h) (h':=h')
                                 (CT:=CT) (gamma:=empty_context) (T:= T)
                                  (t':=t') (F:=F0) (lo:=lo0); auto.
         rewrite <- H_sigma.         rewrite <- H_sigma'. auto. auto. 

(* opaque call  *)
   +  intro T. intro typing. intro t'.  intro step.
        inversion step.   inversion typing.
        apply T_opaqueCall. apply IHt. auto. auto.
        inversion typing. 
              apply T_opaqueCall. apply IHt. auto. rewrite <- H1. 
        apply ST_return1. auto.
        inversion typing.  apply T_v_opa_l. apply T_label.
        apply heap_preserve_typing with (h:=h).
          intros o0 cls_def0 F0 lo0. intro. 
        apply reduction_preserve_heap_pointer with 
                    (t:=(opaqueCall t) )
                     (s:=s) (s':=s') (h:=h) (h':=h')
                                 (CT:=CT) (gamma:=empty_context) (T:= T)
                                  (t':=t') (F:=F0) (lo:=lo0); auto.
      rewrite <- H_sigma.         rewrite <- H_sigma'. auto. auto. auto.  

        inversion typing. auto. inversion typing.  apply T_v_opa_l. apply T_label.
        apply heap_preserve_typing with (h:=h).
          intros o0 cls_def0 F0 lo0. intro. 
        apply reduction_preserve_heap_pointer with 
                    (t:=(opaqueCall t) )
                     (s:=s) (s':=s') (h:=h) (h':=h')
                                 (CT:=CT) (gamma:=empty_context) (T:= T)
                                  (t':=t') (F:=F0) (lo:=lo0); auto.
      rewrite <- H_sigma.         rewrite <- H_sigma'. auto. auto.
        rewrite <- H0 in H14. inversion H14. 
        apply value_typing_invariant_gamma with (gamma:=empty_context).
        auto. auto. auto. 

(* skip  *)
   + intro T. intro typing. intro t'.  intro step.
        inversion step.  

(* assignment  *)
   + intro T. intro typing. intro t'.  intro step.
        inversion step.    inversion typing.
        apply T_assignment with (T:=T0); auto.
        inversion typing.
        apply T_skip with (Gamma:=empty_context)(CT:=CT)  (h:=h').

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
                                 (CT:=CT) (gamma:=empty_context) (T:= T)
                                  (t':=t') (F:=F0) (lo:=lo0); auto.
       rewrite <- H_sigma.         rewrite <- H_sigma'. auto. auto. auto. auto.  
        
        inversion typing. 
        apply T_FieldWrite with (cls_def:=cls_def) (clsT:=clsT) (cls':=cls'). 
        
        apply heap_preserve_typing with (h:=h).
          intros o0 cls_def0 F0 lo0. intro. 
        apply reduction_preserve_heap_pointer with 
                    (t:=(FieldWrite t1 i t2) )
                     (s:=s) (s':=s') (h:=h) (h':=h')
                                 (CT:=CT) (gamma:=empty_context) (T:= T)
                                  (t':=t') (F:=F0) (lo:=lo0); auto.
        rewrite <- H_sigma.         rewrite <- H_sigma'. auto. auto. auto. auto. auto. 

        inversion typing. apply T_skip.         inversion typing. apply T_skip.

(* if statement  *)
   + intro T. intro typing. intro t'.  intro step.
        inversion step. 
        inversion typing. inversion H20. inversion H28.
        inversion typing. inversion H20. inversion H28.

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
                                 (CT:=CT) (gamma:=empty_context) (T:= T)
                                  (t':=t') (F:=F0) (lo:=lo0); auto.
        rewrite <- H_sigma.         rewrite <- H_sigma'. auto. auto.

        inversion typing. rewrite <- H4.  
        apply heap_preserve_typing with (h:=h).
          intros o0 cls_def0 F0 lo0. intro. 
        apply reduction_preserve_heap_pointer with 
                    (t:=(Sequence t1 t2)  )
                     (s:=s) (s':=s') (h:=h) (h':=h')
                                 (CT:=CT) (gamma:=empty_context) (T:= T)
                                  (t':=t') (F:=F0) (lo:=lo0); auto.
        rewrite <- H_sigma.         rewrite <- H_sigma'. auto. auto.

(* return   *)
   + intro T. intro typing. intro t'.  intro step.
        inversion step. 
        inversion typing. 
        apply T_return; auto. 
        inversion typing. auto.  rewrite <- H2. 
        apply heap_preserve_typing with (h:=h).
          intros o0 cls_def0 F0 lo0. intro. 
        apply reduction_preserve_heap_pointer with 
                    (t:=(Return t) )
                     (s:=s) (s':=s') (h:=h) (h':=h')
                                 (CT:=CT) (gamma:=empty_context) (T:= T)
                                  (t':=t') (F:=F0) (lo:=lo0); auto.
        rewrite <- H_sigma.         rewrite <- H_sigma'. auto. auto.

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

Inductive multi_step : Class_table -> tm -> Sigma -> Class_table-> tm -> Sigma -> Prop := 
  | multi_refl : forall t ct sigma , multi_step ct t sigma ct t sigma
  | multi_reduction : forall t1 t2 t3 sigma1 sigma2 sigma3 ct, 
                    reduction (Config ct t1 sigma1) (Config ct t2 sigma2) ->
                    multi_step ct t2 sigma2 ct t3 sigma3 ->
                    multi_step ct t1 sigma1 ct t3 sigma3.

Notation "c1 '==>*' c2" := (multi_step_reduction c1 c2) (at level 40).


Theorem soundness : forall CT,
    forall sigma s h, sigma = SIGMA s h ->  
      wfe_heap CT h -> wfe_stack CT h s -> field_wfe_heap CT h ->
    forall t s' h' t',  multi_step CT t sigma CT t' (SIGMA s' h')  ->
    forall T, has_type CT empty_context h t T -> 
     value t' \/ (exists config', Config CT t' (SIGMA s' h') ==> config').
Proof with auto. 
  intros CT sigma s h.  intro. intro. intro. intro. intros t s' h' t'.
  intro multiH. 

generalize dependent s.  generalize dependent h. 
  induction multiH.
  + intro h. intro well_heap. intro well_fields. intro s. intro sigmaH. intro well_stack. intro T. 
     intro typing. apply progress with  (T:=T) (CT:=ct)  (s:=s) (h:=h); auto.
  + intro h1. intro well_heap. intro well_fields. intro s1. intro. intro well_stack. intro T. intro typing. 
      induction sigma2.  
      assert (wfe_heap ct h /\ wfe_stack ct h s /\  field_wfe_heap ct h).
      apply reduction_preserve_wfe with (t:=t1) (t':=t2) 
              (sigma:=sigma1) (sigma':=(SIGMA s h)) (CT:=ct)
              (s:=s1) (s':=s) (h:=h1) (h':=h) (T:=T).
      auto. auto.       auto. auto.       auto. auto. auto. 
      destruct IHmultiH with (h0:=h) (s0:=s) (T:=T).
      apply H1. apply H1.  auto. apply H1. 
      apply preservation with  (CT:=ct) (s:=s1) (s':=s) 
                    (h:=h1) (h':=h) (sigma:=sigma1) (sigma':= (SIGMA s h)) (t:=t1).
      auto.       auto.       auto.       auto.       auto.       auto. auto.  
      left. auto. right. auto.
Qed.


Lemma normal_form_prime : forall v sigma ct, value v->
(forall v' sigma', Config ct v sigma ==> Config ct v' sigma' -> False).
Proof. 
  intros v sigma ct. intro H_v. intros.
  inversion H_v; try (rewrite <-H0 in H; inversion H; fail); 
  try (rewrite <-H1 in H; inversion H).
Qed.


Theorem deterministic: forall ct t sigma t1 sigma1 t2 sigma2, 
     reduction (Config ct t sigma) (Config ct t1 sigma1) ->
     reduction (Config ct t sigma) (Config ct t2 sigma2) -> 
      t1 = t2 /\ sigma1 = sigma2. 
Proof.
     intros ct t sigma t1 sigma1 t2 sigma2 Hy1 Hy2.

     remember (Config ct t1 sigma1) as t1_config. 
     generalize dependent t2.      generalize dependent t1.
     induction Hy1; intro t1; intro; intro t2; intro Hy2; inversion Heqt1_config; subst.
      (*Tvar *)
     - inversion Hy2. subst. inversion H5. rewrite <- H1 in H8. rewrite <- H2 in H8.
        inversion H8.
          split. auto. auto. 
     (*field access*)
    - inversion Hy2. subst. destruct IHHy1 with e' e'0. subst.
       auto. auto. subst. auto.
       subst. inversion Hy1.  
    - inversion Hy2. subst. inversion H2.
      subst. inversion H7. rewrite <- H3 in H8. rewrite <- H8 in H0. inversion H0.
       subst. rewrite <- H1 in H9.  inversion H9.  split; auto.
    - inversion Hy2. subst.  destruct IHHy1 with e' e'0; auto. split; subst; auto.
       subst. apply normal_form_prime in Hy1. intuition. auto.
        
       subst.  inversion Hy1. subst. inversion Hy1.
    - inversion Hy2. 
          subst. apply normal_form_prime in H2. intuition. auto.
          subst. destruct IHHy1 with e' e'0; auto. split; auto. rewrite H1. auto.
          subst. apply normal_form_prime in Hy1. intuition. auto.
          subst. destruct H with (v_opa_l v0 lb). apply v_opa_labeled. auto.
                intuition. inversion H1. auto.
    - inversion Hy2.
          subst. inversion H3. 
          subst. apply normal_form_prime in H10. intuition. auto.
          subst. inversion H9. rewrite <- H4 in H10. rewrite <-H10 in H0.
              inversion H0. rewrite <- H5 in H11. rewrite <-H11 in H1. 
              inversion H1. subst. auto.
          subst.  inversion H9. rewrite <- H4 in H10. rewrite <-H10 in H0.
              inversion H0. rewrite <- H5 in H16. rewrite <-H16 in H1. 
              inversion H1. subst. auto. inversion H2. 
    - inversion Hy2. 
          subst. inversion H1.
          subst. destruct H3 with  (v_opa_l v lb).  apply v_opa_labeled; auto. 
              intuition. inversion H. auto.
          subst. inversion H12. 
          subst. inversion H10. rewrite <- H2 in H11. rewrite <- H11 in H0.
              inversion H0. rewrite <- H3 in H17. rewrite <- H17 in H6. 
              inversion H6.  subst. auto.
      - inversion Hy2. 
          subst. inversion H6. rewrite H5 in H. inversion H. subst.  auto.
      - inversion Hy2. 
          subst. destruct IHHy1 with  e' e'0; auto. rewrite H. auto.
          subst. apply normal_form_prime in Hy1. intuition. auto.
      - inversion Hy2. 
          subst. apply normal_form_prime in H1. intuition. auto. auto.
      - inversion Hy2.
          subst. destruct IHHy1 with  e' e'0; auto. rewrite H. auto.
          subst. inversion Hy1.
      - inversion Hy2.
          subst. inversion H0. 
          subst.  inversion H6. subst. auto.
      - inversion Hy2.
          subst. destruct IHHy1 with  e' e'0; auto.  rewrite H. auto.
          subst. inversion Hy1.
      - inversion Hy2. 
          subst.  inversion H0. 
          subst.  auto.
      - inversion Hy2.
          subst.  destruct IHHy1 with  e' e'0; auto.  rewrite H. auto.
          subst. inversion Hy1.
      - inversion Hy2.
          subst. inversion H0.
          subst. inversion H4. rewrite <-H0. auto.
      - inversion Hy2.
          subst. destruct IHHy1 with  e' e'0; auto.  rewrite H0. auto.
          subst. destruct IHHy1 with e' (Return e'0); auto.
              apply ST_return1 in H1. auto. 
          subst.  auto.
          subst. apply normal_form_prime in Hy1. intuition. auto.
          subst. destruct H with v; auto.
      - inversion Hy2.
          subst. inversion H5. subst.
              destruct IHHy1 with  e' e'1; auto.  
              apply ST_return1 in H0. rewrite <- H. auto.
          subst.   apply normal_form_prime in Hy1. intuition. auto.
          subst. destruct IHHy1 with e' e'0; auto. rewrite H. auto.
          subst. inversion H1.
          subst.  apply normal_form_prime in Hy1. intuition. auto.
       - inversion Hy2.
          subst.   apply normal_form_prime in H6. intuition. auto.
          subst. inversion H.
          subst. auto.
          subst. inversion H.
       - inversion Hy2.
          subst. destruct H2 with v. auto. auto.
          subst.  apply normal_form_prime in H0. intuition. auto.
          subst. inversion H2.
          subst. inversion H6. subst. auto.
       - inversion Hy2.
          subst. destruct IHHy1 with e' e'0; auto. rewrite H. auto.
          subst.  apply normal_form_prime in Hy1. intuition. auto.
       - inversion Hy2.
          subst. apply normal_form_prime in H1. intuition. auto.
          subst.  inversion H7. auto.
       - inversion Hy2.   
          subst. destruct IHHy1 with e1' e1'0; auto. rewrite H. auto.
          subst. apply normal_form_prime in Hy1. intuition. auto.
          subst. inversion Hy1.
          subst. inversion Hy1.
       - inversion Hy2.
          subst. apply normal_form_prime in H2. intuition. auto.
          subst. destruct IHHy1 with e2' e2'0; auto. rewrite H1. auto.
          subst. apply normal_form_prime in Hy1. intuition. auto.
          subst. destruct H with (v_opa_l v0 lb).
              apply v_opa_labeled. auto. intuition. inversion H1.
          subst.  auto.
       - inversion Hy2.
          subst. inversion H1.
          subst. apply normal_form_prime in H10. intuition. auto.
          subst. inversion H8. subst. rewrite <-H9 in H0. inversion H0.
              subst. auto.
          subst. inversion H5.
      - inversion Hy2.
          subst. inversion H0.
          subst.  destruct H3 with (v_opa_l v lb).
              apply v_opa_labeled. auto. intuition. inversion H.
          subst. auto.
          subst. inversion H14.
          subst. inversion H9. subst. rewrite <- H10 in H1. 
            inversion H1. inversion H8. subst. auto.
      - inversion Hy2. 
          subst.  destruct IHHy1 with e' e'0; auto. rewrite H. auto.
          subst. apply normal_form_prime in Hy1. intuition. auto. 
      - inversion Hy2. 
          subst. apply normal_form_prime in H1.  intuition. auto. 
          subst. inversion H7. auto. 
      - inversion Hy2.
          subst. auto. 
          subst. inversion H2.  inversion H4. subst. intuition. 
      - inversion Hy2. 
          subst. inversion H11. inversion H4. subst. intuition. 
          subst. inversion H4. subst. auto. 
      - inversion Hy2. 
          subst. destruct IHHy1 with s1' s1'0; auto. rewrite H. auto.
          subst. apply normal_form_prime in Hy1.  intuition. auto.
      - inversion Hy2. 
          subst. apply normal_form_prime in H1.  intuition. auto.
          subst. auto. 
Qed. 

