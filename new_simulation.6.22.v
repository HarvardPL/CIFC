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

(* special terms *)
  | ObjId: oid -> tm
  (* runtime labeled date*)
  | v_l : tm -> Label -> tm
  | v_opa_l : tm -> Label -> tm
  | hole : tm 
  | dot : tm
  | return_hole : tm.
  

Inductive method_def : Type :=
  | m_def : cn -> id -> cn -> id -> tm -> method_def.


Inductive CLASS : Type :=
  | class_def : cn -> (list field) -> (list method_def) -> CLASS. 

Inductive value : tm -> Prop :=
  (* contants are values or normal form *)
  | v_oid :
      forall o, value (ObjId o)
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

Definition sf_update (sf : stack_frame) (x : id) (v : tm) :=
  fun x' => if beq_id x x' then (Some v) else sf x'.


(*new definition for the code *)
Definition frame_stack  :Type := list tm.

(* unrestricted access L *)
Definition L_Label := LB nil.
Definition H_Label := LB (cons (Principal "Jian") nil).

Definition empty_stack_frame : stack_frame := fun _ => None.


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


(* variable declaration *)
Inductive vd : Type :=
  | var_def : cn -> id -> vd.

Fixpoint find_method_body (methods : list method_def) (m : id) :=
  match methods with
    | nil => None
    | h :: t =>  match h with 
                  | m_def cls m' cls_a arg_id body => if beq_id m m' then Some (m_def cls m' cls_a arg_id  body) else find_method_body t m
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

Inductive container : Type := 
  | Container : tm -> frame_stack -> Label -> stack_frame -> container.

Definition Class_table := cn -> option CLASS.
Inductive config := 
  | Config : Class_table ->container -> list container -> heap -> config
  | Error_state : config
  | Terminal : config. 
Hint Constructors config.

Reserved Notation "c '==>' c'"
  (at level 40, c' at level 39).

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

(* special terms *)
    | ObjId o =>  false
  (* runtime labeled date*)
    | v_l e lb => false
    | v_opa_l e lb => false
    | hole => false
    | dot => false
    | return_hole => false
  end.


Inductive valid_syntax :  tm -> Prop :=
  (*variable *)
  | Valid_var : forall x,
      valid_syntax (Tvar x)
(* null *)
  | Valid_null : 
      valid_syntax null
(* Field read *)
  | Valid_FieldAccess1 : forall e f,
      surface_syntax e = true ->
      valid_syntax (FieldAccess e f)

  | Valid_FieldAccess2 : forall f,
      valid_syntax (FieldAccess hole f)

  | Valid_FieldAccess3 : forall v f,
      value v ->
      valid_syntax (FieldAccess v f)

(* method call *)
  | Valid_MethodCall1 : forall e meth argu,
      surface_syntax e = true ->
      surface_syntax argu = true -> 
      valid_syntax (MethodCall e meth argu)

  | Valid_MethodCall2 : forall meth argu,
      surface_syntax argu = true -> 
      valid_syntax (MethodCall hole meth argu)

  | Valid_MethodCall3 : forall v meth argu,
      value v -> 
      surface_syntax argu = true ->
      valid_syntax (MethodCall v meth argu)

  | Valid_MethodCall4 : forall v meth,
      value v -> 
      valid_syntax (MethodCall v meth hole)

  | Valid_MethodCall5 : forall v1 v2 meth,
      value v1 -> value v2 ->
      valid_syntax (MethodCall v1 meth v2)


(* new exp *)
  | Valid_NewExp : forall cls_name,
      valid_syntax (NewExp cls_name)
(* label *)
  | Valid_label : forall lb,
      valid_syntax (l lb)
(* label data *)
  | Valid_labelData1 : forall e lb,
      surface_syntax e = true ->
      valid_syntax (labelData e lb)

  | Valid_labelData2 : forall lb,
      valid_syntax (labelData hole lb)

  | Valid_labelData3 : forall v lb,
      value v ->
      valid_syntax (labelData v lb)

(* unlabel *)
  | Valid_unlabel1 : forall e,
      surface_syntax e = true ->
      valid_syntax (unlabel e) 

  | Valid_unlabel2 :
      valid_syntax (unlabel hole) 

  | Valid_unlabel3 : forall v,
      value v ->
      valid_syntax (unlabel v) 

(* labelOf *)
  | Valid_labelOf1 : forall e,
      surface_syntax e = true ->
      valid_syntax (labelOf e)

  | Valid_labelOf2 : 
      valid_syntax (labelOf hole)

  | Valid_labelOf3 : forall v,
      value v ->
      valid_syntax (labelOf v)

(* unlabel opaque *)
  | Valid_unlabelOpaque1 : forall e,
      surface_syntax e = true ->
      valid_syntax (unlabelOpaque e)

  | Valid_unlabelOpaque2 : 
      valid_syntax (unlabelOpaque hole)

  | Valid_unlabelOpaque3 : forall v,
      value v ->
      valid_syntax (unlabelOpaque v)

(* Skip *)
  | Valid_skip : 
      valid_syntax Skip
(* assignment *)
  | Valid_assignment1 : forall e x, 
      surface_syntax e = true ->
      valid_syntax (Assignment x e)

  | Valid_assignment2 : forall x, 
      valid_syntax (Assignment x hole)

  | Valid_assignment3 : forall v x, 
      value v ->
      valid_syntax (Assignment x v)

(* Field Write *)
  | Valid_FieldWrite1 : forall e1 f  e2,
      surface_syntax e1 = true ->
      surface_syntax e2 = true -> 
      valid_syntax (FieldWrite e1 f e2)

  | Valid_FieldWrite2 : forall v f  e2,
      value v -> 
      surface_syntax e2 = true -> 
      valid_syntax (FieldWrite v f e2)

  | Valid_FieldWrite3 : forall e2 f,
      surface_syntax e2 = true -> 
      valid_syntax (FieldWrite hole f e2)

  | Valid_FieldWrite4 : forall v1 v2 f,
      value v1 -> 
      value v2 -> 
      valid_syntax (FieldWrite v1 f v2)

  | Valid_FieldWrite5 : forall v f,
      value v -> 
      valid_syntax hole ->
      valid_syntax (FieldWrite v f hole)

(* if *)
  | Valid_if : forall id1 id2 e1 e2,
      surface_syntax e1 = true ->
      surface_syntax e2 = true ->
      valid_syntax (If id1 id2 e1 e2)

(* sequence *)
  | Valid_sequence : forall e1 e2,
      surface_syntax e1 = true ->
      surface_syntax e2 = true -> 
      valid_syntax (Sequence e1 e2)

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
(* dot *)
  | Valid_dot : 
      valid_syntax dot
(* hole *)
  | Valid_hole : 
      valid_syntax hole
(* return_hole *)
  | Valid_return_hole : 
      valid_syntax return_hole.


Fixpoint hole_free (t : tm) :=
  match t with
    | Tvar x => true
    | null => true
    | FieldAccess e f => (hole_free e)
    | MethodCall e1 meth e2 => if (hole_free e1) then (hole_free e2) else false
    | NewExp cls => true
(* label related *)
    | l lb => true
    | labelData e lb => (hole_free e)
    | unlabel e => (hole_free e)
    | labelOf e => (hole_free e)
    | unlabelOpaque e => (hole_free e)
(* statements *)
    | Skip => true
    | Assignment x e => (hole_free e)
    | FieldWrite e1 f e2 =>  if (hole_free e1) then (hole_free e2) else false
    | If id0 id1 e1 e2 =>  if (hole_free e1) then (hole_free e2) else false
    | Sequence e1 e2 =>  if (hole_free e1) then (hole_free e2) else false

(* special terms *)
    | ObjId o =>  true
  (* runtime labeled date*)
    | v_l e lb => (hole_free e)
    | v_opa_l e lb => (hole_free e)
    | dot => true
    | hole => false
    | return_hole => false
  end.

Inductive reduction : config -> config -> Prop :=
(* variabel access *)
  | ST_var : forall id h lb sf v ctns ct fs,
      Some v = sf(id) ->
      Config ct (Container (Tvar id) fs lb sf) ctns h ==> Config ct (Container (Tvar id) fs lb sf) ctns h

(* field read *)
  (* context rule *)
  | ST_fieldRead1 : forall sf h e f ct fs ctns lb,
      ~ value e ->
      Config ct (Container (FieldAccess e f) fs lb sf) ctns h ==> Config ct (Container e ((FieldAccess hole f) :: fs) lb sf) ctns h 
  | ST_fieldRead2 : forall sf h f ct fs v ctns lb,
      value v ->
      Config ct (Container v ((FieldAccess hole f) :: fs) lb sf) ctns h ==> Config ct (Container (FieldAccess v f) fs lb sf) ctns h 

  (* normal field access *)
  | ST_fieldRead3 : forall h o fname lo lb cls F v l'  ct fs ctns sf,
      Some (Heap_OBJ cls F lo) = lookup_heap_obj h o -> 
      Some v = F(fname) -> 
      l' = join_label lo lb ->
      Config ct (Container (FieldAccess (ObjId o) fname) fs lb sf) ctns h ==> Config ct (Container v fs l' sf) ctns h 
  (* null pointer exception for field access *)
  | ST_fieldReadException : forall h f ct fs sf ctns lb,
      Config ct (Container (FieldAccess null f) fs lb sf) ctns h ==> Error_state

(* method call *)
  (* context rule: evaluate object target *)
  | ST_MethodCall1 : forall h e e2 id ct fs ctns sf lb,
      ~ value e ->
      Config ct (Container (MethodCall e id e2) fs lb sf) ctns h ==> Config ct (Container e ((MethodCall hole id e2) :: fs) lb sf) ctns h

  | ST_MethodCall2 : forall h e2 id ct fs v ctns sf lb,
      value v ->
      Config ct (Container v ((MethodCall hole id e2) :: fs) lb sf) ctns h ==> Config ct (Container (MethodCall v id e2) fs lb sf ) ctns h

  | ST_MethodCall3 : forall h id ct fs v1 v2 ctns sf lb,
      value v1 ->
      value v2 ->
      Config ct (Container v2 ((MethodCall v1 id hole) :: fs) lb sf) ctns h ==> Config ct (Container (MethodCall v1 id v2) fs lb sf ) ctns h

  (* context rule: evaluate arguments *)
  | ST_MethodCall4 : forall h v e2 id ct fs ctns sf lb,
      (forall t, value t -> t<> null -> e2 <> unlabelOpaque t) ->
      value v -> ~ value e2 ->
      Config ct (Container (MethodCall v id e2) fs lb sf ) ctns h==> Config ct (Container e2 ((MethodCall v id hole) :: fs) lb sf) ctns h


  (* normal method call *)
  | ST_MethodCall_normal : forall o h cls fields v lx sf  arg_id cls_a body meth returnT ct fs ctns lb sf',
      Some (Heap_OBJ cls fields lx) = lookup_heap_obj h o -> 
      Some (m_def returnT meth cls_a arg_id body) = find_method cls meth -> 
      value v ->
      sf' = sf_update empty_stack_frame arg_id v ->
    Config ct (Container (MethodCall (ObjId o) meth v) fs lb sf ) ctns h 
      ==> Config ct (Container body nil lb sf' ) ((Container (return_hole) fs lb sf ) :: ctns) h

  (* null pointer exception for method call *)
  | ST_MethodCallException : forall h v meth ct fs lb sf  ctns, 
      Config ct (Container (MethodCall null meth v) fs lb sf ) ctns h ==> Error_state

(* method call with unlabel opaque *)
  | ST_MethodCall_unlableOpaque : forall o h cls fields v lx sf  arg_id cls_a body meth returnT ct fs ctns lo lb sf' lb',
      Some (Heap_OBJ cls fields lo) =lookup_heap_obj h o -> 
      sf' = sf_update empty_stack_frame arg_id v ->
      lb' = join_label lb lx->
      value v ->
      Some (m_def returnT meth cls_a arg_id  body) = find_method cls meth ->
    Config ct (Container (MethodCall (ObjId o) meth (unlabelOpaque (v_opa_l v lx))) fs lb sf ) ctns h 
      ==> Config ct (Container body nil lb' sf' ) ((Container return_hole fs lb sf ) :: ctns) h


  (* null pointer exception for method call with unlabel opaque of null data*)
  | ST_MethodCallOpaqueDataException : forall h o meth ct fs lb sf ctns, 
      Config ct (Container (MethodCall (ObjId o) meth  (unlabelOpaque null)) fs lb sf ) ctns h ==> Error_state

(* new expression *)
  | ST_NewExp : forall h h' o lb cls_name field_defs method_defs cls F ct fs ctns sf,
      ct cls_name = Some cls -> 
      o = get_fresh_oid h ->
      cls = (class_def cls_name field_defs method_defs) ->
      F =  (init_field_map (find_fields cls) empty_field_map) ->
      h' = add_heap_obj h o (Heap_OBJ cls F lb) ->
      Config ct (Container (NewExp cls_name) fs lb sf ) ctns h ==> Config ct (Container (ObjId o) fs lb sf ) ctns h'

(* label data express *)
  (* context rule *)
  | ST_LabelData1 : forall h e ct fs lb sf ctns lo,
      ~ value e ->
      Config ct (Container (labelData e lo) fs lb sf) ctns h ==> Config ct (Container e ((labelData hole lo) :: fs) lb sf) ctns h 
  | ST_LabelData2 : forall h ct fs v lb lo ctns sf,
      value v ->
      Config ct (Container v ((labelData hole lo) :: fs) lb sf) ctns h ==> Config ct (Container (labelData v lo) fs lb sf) ctns h 

  | ST_LabelData3 : forall h v ct fs lb lo sf ctns,
      value v ->
      Config ct (Container (labelData v lo) fs lb sf) ctns h ==>  Config ct (Container (v_l v lo) fs lb sf) ctns h
  (* label data exception *)
  | ST_LabelDataException : forall h lb ct fs lo ctns sf,
      Config ct (Container (labelData null lo) fs lb sf) ctns h ==> Error_state

(* unlabel *)
  (* context rule *)
  | ST_unlabel1 : forall h e ct fs lb sf ctns,
      ~ value e ->
      Config ct (Container (unlabel e) fs lb sf) ctns h ==> Config ct (Container e ((unlabel hole) :: fs) lb sf) ctns h 
  | ST_unlabel2 : forall h ct fs v lb ctns sf,
      value v ->
      Config ct (Container v ((unlabel hole) :: fs) lb sf) ctns h ==> Config ct (Container (unlabel v) fs lb sf) ctns h 

  (* unlabel *)
  | ST_unlabel3 : forall v lb lo l' h ct fs ctns sf,
      l' = join_label lb lo ->
      value v ->
      Config ct (Container (unlabel (v_l v lo)) fs lb sf) ctns h ==> Config ct (Container v fs l' sf) ctns h
  (* unlabel data exception *)
  | ST_unlabelDataException : forall h ct fs ctns sf lb,
      Config ct (Container (unlabel null) fs lb sf) ctns h ==> Error_state

(* Label of *)
  (* context rule *)
  | ST_labelof1 : forall h e ct fs lb sf ctns,
      ~ value e ->
      Config ct (Container (labelOf e) fs lb sf) ctns h ==> Config ct (Container e ((labelOf hole) :: fs) lb sf) ctns h 
  | ST_labelof2 : forall h ct fs v lb ctns sf,
      value v ->
      Config ct (Container v ((labelOf hole) :: fs) lb sf) ctns h ==> Config ct (Container (labelOf v) fs lb sf) ctns h 

  | ST_labelof3 : forall v lb lo h ct fs ctns sf,
      value v ->
      Config ct (Container (labelOf (v_l v lo)) fs lb sf) ctns h ==> Config ct (Container (l lo) fs lb sf) ctns h 
  (* unlabel data exception *)
  | ST_labelOfDataException : forall h ct fs ctns sf lb,
      Config ct (Container (labelOf null) fs lb sf) ctns h ==> Error_state

(* unlabel opaque*)
  (* context rule *)
  | ST_unlabel_opaque1 : forall h e ct fs lb sf ctns,
      ~ value e ->
      Config ct (Container (unlabelOpaque e) fs lb sf) ctns h ==> Config ct (Container e ((unlabelOpaque hole) :: fs) lb sf) ctns h 
  | ST_unlabel_opaque2 : forall h ct fs v lb ctns sf,
      value v ->
      Config ct (Container v ((unlabelOpaque hole) :: fs) lb sf) ctns h ==> Config ct (Container (unlabelOpaque v) fs lb sf) ctns h 

  | ST_unlabel_opaque3 : forall v lb lo l' h ct fs ctns sf,
      l' = join_label lb lo ->
      value v ->
      Config ct (Container (unlabelOpaque (v_opa_l v lo)) fs lb sf) ctns h ==> Config ct (Container v fs l' sf) ctns h 
  (* unlabel data exception *)
  | ST_unlabel_opaqueDataException : forall h ct fs ctns sf lb,
      Config ct (Container (unlabelOpaque null) fs lb sf) ctns h ==> Error_state

(* assignment *)
  (* context rule *)
  | ST_assignment1 : forall h e ct fs lb sf ctns id,
      ~ value e ->
      Config ct (Container (Assignment id e) fs lb sf) ctns h ==> Config ct (Container e ((Assignment id hole) :: fs) lb sf) ctns h 
  | ST_assignment2 : forall h ct fs v lb ctns sf id,
      value v ->
      Config ct (Container v ((Assignment id hole) :: fs) lb sf) ctns h ==> Config ct (Container (Assignment id v) fs lb sf) ctns h 

  | ST_assignment3 : forall v lb h ct fs ctns sf sf' id,
      value v ->
      sf' = sf_update sf id v ->
      Config ct (Container (Assignment id v) fs lb sf) ctns h ==> Config ct (Container Skip fs lb sf') ctns h 

(* Field Write *)
  (* context rule 1 *)
   | ST_fieldWrite1 : forall h e e2 f ct fs ctns sf lb,
      ~ value e ->
      Config ct (Container (FieldWrite e f e2) fs lb sf) ctns h ==> Config ct (Container e ((FieldWrite hole f e2) :: fs) lb sf) ctns h

  | ST_fieldWrite2 : forall h e2 f ct fs v ctns sf lb,
      value v ->
      Config ct (Container v ((FieldWrite hole f e2) :: fs) lb sf) ctns h ==> Config ct (Container (FieldWrite v f e2) fs lb sf ) ctns h

  (* context rule: evaluate arguments *)
  | ST_fieldWrite4 : forall h v e2 f ct fs ctns sf lb,
      (forall t, value t -> t<> null -> e2 <> unlabelOpaque t) ->
      value v -> ~ value e2 ->
      Config ct (Container (FieldWrite v f e2) fs lb sf ) ctns h==> Config ct (Container e2 ((FieldWrite v f hole) :: fs) lb sf) ctns h
  | ST_fieldWrite5 : forall h v1 v2 f ct fs lb sf ctns, 
      value v2 ->
      value v1 ->
      Config ct (Container v2 ((FieldWrite v1 f hole) :: fs) lb sf ) ctns h ==> Config ct (Container (FieldWrite v1 f v2) fs lb sf ) ctns h 

  (* normal field write *)
  | ST_fieldWrite_normal : forall o h h' f lo lb cls F F' v ct fs ctns sf,
      Some (Heap_OBJ cls F lo) = lookup_heap_obj h o -> 
      F' = fields_update F f v ->
      flow_to lo lb = true ->
      h' = update_heap_obj h o (Heap_OBJ cls F' lo) ->
      value v->
    Config ct (Container (FieldWrite (ObjId o) f v) fs lb sf ) ctns h 
      ==> Config ct (Container Skip fs lb sf ) ctns h 

  (* normal field information leak *)
  | ST_fieldWrite_leak : forall o h f lo lb cls F v ct fs ctns sf,
      Some (Heap_OBJ cls F lo) = lookup_heap_obj h o -> 
      flow_to lo lb = false ->
      value v->
    Config ct (Container (FieldWrite (ObjId o) f v) fs lb sf ) ctns h 
      ==>  Error_state

  (* null pointer exception for method call *)
  | ST_FieldWrite_Exception : forall h v f ct fs lb sf  ctns, 
      Config ct (Container (FieldWrite null f v) fs lb sf ) ctns h ==> Error_state

(* field write with unlabel opaque *)
  | ST_fieldWrite_unlableOpaque : forall o h h' f lo lb cls F F' v ct fs ctns sf lx,
      Some (Heap_OBJ cls F lo) = lookup_heap_obj h o-> 
      F' = fields_update F f v ->
      flow_to lo (join_label lb lx)  = true ->
      h' = update_heap_obj h o (Heap_OBJ cls F' lo) ->
      value v ->
    Config ct (Container (FieldWrite (ObjId o) f (unlabelOpaque (v_opa_l v lx))) fs lb sf ) ctns h
      ==> Config ct (Container Skip fs lb sf) ctns h' 

(* field write with unlabel opaque and information leak*)
  | ST_fieldWrite_unlableOpaque_leak : forall o h f lo lb cls F v ct fs ctns sf lx,
      Some (Heap_OBJ cls F lo) = lookup_heap_obj h o-> 
      flow_to lo (join_label lb lx)  = false ->
      value v ->
    Config ct (Container (FieldWrite (ObjId o) f (unlabelOpaque (v_opa_l v lx))) fs lb sf ) ctns h
      ==> Error_state

  (* null pointer exception for method call with unlabel opaque of null data*)
  | ST_FieldWriteOpaqueDataException : forall h o f ct fs lb sf ctns, 
      Config ct (Container (FieldWrite (ObjId o) f  (unlabelOpaque null)) fs lb sf ) ctns h ==> Error_state

(* if statement *)
  | ST_if_b1 : forall s1 s2 h lb sf id1 id2 ct fs ctns, 
       sf(id1) = sf(id2) ->
       Config ct (Container (If id1 id2 s1 s2) fs lb sf) ctns h ==> Config ct (Container s1 fs lb sf) ctns h
  | ST_if_b2 : forall s1 s2 h lb sf id1 id2 ct fs ctns, 
       sf(id1) <> sf(id2) ->
       Config ct (Container (If id1 id2 s1 s2) fs lb sf) ctns h ==> Config ct (Container s2 fs lb sf) ctns h
(* sequence *)
   (* context rule *)
  | ST_seq : forall h e1 e2 ct fs ctns lb sf, 
    Config ct (Container  (Sequence e1 e2) fs lb sf) ctns h ==> Config ct (Container  e1 (e2 :: fs) lb sf) ctns h

(* skip *)
  | ST_skip1 : forall h ct e fs lb sf ctns,
    Config ct (Container Skip (e :: fs) lb sf) ctns h ==> Config ct (Container e fs lb sf) ctns h

  | ST_val : forall h v ct e fs lb sf ctns,
    value v ->
    hole_free e = true ->
    Config ct (Container v (e :: fs) lb sf) ctns h ==> Config ct (Container e fs lb sf) ctns h

  | ST_val2 : forall h v ct ctns sf lb lb' sf' fs',
    value v ->
    (*ctn must have return_hole*)
    Config ct (Container v nil lb sf) ((Container return_hole fs' lb' sf') :: ctns) h 
      ==> Config ct (Container (v_opa_l v lb) fs' lb' sf') ctns h

where "c '==>' c'" := (reduction c c').



Inductive ty : Type :=
  | classTy : cn -> ty 
  | LabelTy : ty
  | LabelelTy : ty -> ty
  | OpaqueLabeledTy : ty -> ty
  | voidTy : ty
  | ArrowTy : ty -> ty -> ty.

Definition typing_context := id -> (option ty).
Definition empty_context : typing_context := fun _ => None.

Definition update_typing (gamma : typing_context) (x:id) (T : ty) : typing_context :=
      fun x' => if beq_id x x' then (Some T) else gamma x. 


Hint Constructors valid_syntax.
Lemma value_is_valid_syntax : forall v, 
  value v -> valid_syntax v.
Proof with eauto. intros. inversion H. apply Valid_ObjId.  apply Valid_null. apply Valid_label. apply Valid_v_l.
        auto. apply Valid_v_opa_l. auto. auto. Qed. 

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



Inductive wfe_stack_frame : Class_table -> heap -> stack_frame -> Prop :=
  | stack_frame_wfe : forall h sf ct,
         (forall x, exists v, sf x = Some v  ->
               (
               v = null \/ 
                 ( exists cls_name o, v = ObjId o 
                              /\ (exists F lo field_defs method_defs , lookup_heap_obj h o = Some (Heap_OBJ (class_def cls_name field_defs method_defs) F lo)
                                      /\ (ct cls_name = Some (class_def cls_name field_defs method_defs))
                                   ) 
                  )    )  ) ->
        wfe_stack_frame ct h sf.


Inductive wfe_ctn_list : Class_table -> heap -> list container -> Prop :=
  | wfe_ctns_nil : forall ct h,
        wfe_ctn_list ct h nil
  | wfe_ctns_list : forall ct h t fs lb sf ctns ctns', 
        ctns = cons (Container t fs lb sf) ctns'->
        wfe_ctn_list ct h ctns' ->
        wfe_stack_frame ct h sf ->
        wfe_ctn_list ct h ctns.


Inductive tm_has_type : Class_table -> typing_context -> heap -> tm -> ty -> Prop :=
(*variable *)
  | T_Var : forall Gamma x T CT h , 
      Gamma x = Some (classTy T) ->
      tm_has_type CT Gamma h (Tvar x) (classTy T)
(* null *)
  | T_null : forall Gamma h T CT, 
      tm_has_type CT Gamma h null T
(* Field read *)
  | T_FieldAccess : forall Gamma e f cls_def CT clsT cls' h fields_def,
      tm_has_type CT Gamma h e (classTy clsT) ->
      Some cls_def = CT(clsT) ->
      fields_def = (find_fields cls_def) ->
      type_of_field fields_def f = Some cls' ->
      tm_has_type CT Gamma h (FieldAccess e f) (classTy cls')
(* method call *)
  | T_MethodCall : forall Gamma Gamma' e meth argu CT h T returnT cls_def body arg_id arguT,
      tm_has_type CT Gamma h e (classTy T) ->
      tm_has_type CT Gamma h argu (classTy arguT) ->
      Some cls_def = CT(T) ->
      find_method cls_def meth = Some (m_def returnT meth arguT arg_id  body)  ->
      Gamma' = update_typing empty_context arg_id (classTy arguT) ->
      tm_has_type CT Gamma' h (body) (classTy returnT) ->
      surface_syntax body = true ->
      tm_has_type CT Gamma h (MethodCall e meth argu) (OpaqueLabeledTy (classTy returnT))
(* new exp *)
  | T_NewExp : forall h Gamma cls_name CT, 
      (exists cls_def field_defs method_defs, CT cls_name = Some cls_def /\
              cls_def = class_def cls_name field_defs method_defs) ->
      tm_has_type CT Gamma h (NewExp cls_name) (classTy cls_name)
(* label *)
  | T_label : forall h Gamma lb CT,
      tm_has_type CT Gamma h (l lb) LabelTy
(* label data *)
  | T_labelData : forall h Gamma lb CT e T,
      tm_has_type CT Gamma h (l lb) LabelTy ->
      T <> voidTy ->
      tm_has_type CT Gamma h e T ->
      tm_has_type CT Gamma h (labelData e lb) (LabelelTy T)
(* unlabel *)
  | T_unlabel : forall h Gamma CT e T,
      tm_has_type CT Gamma h e (LabelelTy T) ->
      tm_has_type CT Gamma h (unlabel e) T
(* labelOf *)
  | T_labelOf : forall h Gamma CT e T,
      tm_has_type CT Gamma h e (LabelelTy T) ->
      tm_has_type CT Gamma h (labelOf e) LabelTy
(* unlabel opaque *)
  | T_unlabelOpaque : forall h Gamma CT e T,
      tm_has_type CT Gamma h e (OpaqueLabeledTy T) -> 
      tm_has_type CT Gamma h (unlabelOpaque e) T
(* Skip *)
  | T_skip : forall h Gamma CT,
      tm_has_type CT Gamma h Skip voidTy
(* assignment *)
  | T_assignment : forall h Gamma CT e T x, 
      Gamma x = Some T ->
      tm_has_type CT Gamma h e T ->
      T <> voidTy ->
      tm_has_type CT Gamma h (Assignment x e) voidTy
(* Field Write *)
  | T_FieldWrite : forall h Gamma x f cls_def CT clsT cls' e,
      tm_has_type CT Gamma h x (classTy clsT) ->
      tm_has_type CT Gamma h e (classTy cls') ->
      Some cls_def = CT(clsT) ->
      type_of_field (find_fields cls_def) f = Some cls' ->
      tm_has_type CT Gamma h (FieldWrite x f e) voidTy
(* if *)
  | T_if : forall Gamma h CT id1 id2 s1 s2 T T' ,
      tm_has_type CT Gamma h (Tvar id1) (classTy T) ->
      tm_has_type CT Gamma h (Tvar id2) (classTy T) ->
      tm_has_type CT Gamma h s1 T' ->
      tm_has_type CT Gamma h s2 T' ->
      tm_has_type CT Gamma h (If id1 id2 s1 s2) T'
(* sequence *)
  | T_sequence : forall h Gamma CT e1 e2 T T',
      tm_has_type CT Gamma h e1 T ->
      tm_has_type CT Gamma h e2 T' ->
      tm_has_type CT Gamma h (Sequence e1 e2) T'

(* ObjId *)
  | T_ObjId : forall h Gamma CT o cls_name cls_def,
      Some cls_def = CT(cls_name) ->
      (exists field_defs method_defs, cls_def = (class_def cls_name field_defs method_defs)) ->
      (exists F lo, lookup_heap_obj h o = Some (Heap_OBJ cls_def F lo)) ->
      tm_has_type CT Gamma h (ObjId o) (classTy cls_name)
(* runtime labeled data *)
  | T_v_l : forall h Gamma lb CT v T,
      tm_has_type CT Gamma h (l lb)  LabelTy ->
      tm_has_type CT Gamma h v  T ->
      value v ->
      tm_has_type CT Gamma h (v_l v lb) (LabelelTy T)
(* runtime labeled data *)
  | T_v_opa_l : forall h Gamma lb CT v T,
      tm_has_type CT Gamma h (l lb)  LabelTy ->
      tm_has_type CT Gamma h v  T ->
      value v ->
      tm_has_type CT Gamma h (v_opa_l v lb) (OpaqueLabeledTy T)
(* hole *)
  | T_hole : forall h Gamma CT T,
      tm_has_type CT Gamma h hole T
  | T_dot : forall h Gamma T CT,
      tm_has_type CT Gamma h dot T
  | T_return_hole : forall h Gamma T CT,
      tm_has_type CT Gamma h return_hole T. 
Hint Constructors tm_has_type.

Inductive fs_has_type : Class_table -> typing_context -> heap -> list tm -> ty -> Prop :=
  | T_fs_nil : forall h Gamma CT T, 
      fs_has_type CT Gamma h nil (ArrowTy T T)
(*
  | T_fs : forall h Gamma CT T T' top fs, 
      hole_free top = true ->
      tm_has_type CT Gamma h top T ->
      fs_has_type CT Gamma h fs (ArrowTy T T') ->
      fs_has_type CT Gamma h (top :: fs) (ArrowTy T T') 
*)
  | T_fs_one : forall h Gamma CT T top,  
      hole_free top = true ->
      tm_has_type CT Gamma h top T ->
      fs_has_type CT Gamma h (top :: nil) (ArrowTy T T) 
  | T_fs_hole : forall h Gamma CT T T' top fs p,  
      hole_free top = true ->
      hole_free p  = false ->
      tm_has_type CT Gamma h top T ->
      fs_has_type CT Gamma h (p :: fs) (ArrowTy T T') ->
      fs_has_type CT Gamma h (top :: p :: fs) (ArrowTy T T') 
  | T_fs_no_hole : forall h Gamma CT T T' T0 top fs p,  
      hole_free p  = true ->
      hole_free top = true ->
      tm_has_type CT Gamma h top T ->
      fs_has_type CT Gamma h (p :: fs) (ArrowTy T0 T') ->
      fs_has_type CT Gamma h (top :: p :: fs) (ArrowTy T T') 
  | T_fs_FieldAccess : forall h Gamma CT T' fs clsT cls' fields_def cls_def f, 
      tm_has_type CT Gamma h (FieldAccess hole f) (classTy cls') ->
      Some cls_def = CT(clsT) ->
      fields_def = (find_fields cls_def) ->
      type_of_field fields_def f = Some cls' ->
      fs_has_type CT Gamma h fs (ArrowTy (classTy cls') T') ->
      fs_has_type CT Gamma h ((FieldAccess hole f)  :: fs) (ArrowTy (classTy clsT) T')
(* method call *)
  | T_fs_MethodCall1 : forall Gamma Gamma' meth argu e CT h T returnT cls_def body arg_id arguT T' fs,
      tm_has_type CT Gamma h (MethodCall e meth argu) (OpaqueLabeledTy (classTy returnT)) ->
      tm_has_type CT Gamma h argu (classTy arguT) ->
      Some cls_def = CT(T) ->
      find_method cls_def meth = Some (m_def returnT meth arguT arg_id  body)  ->
      Gamma' = update_typing empty_context arg_id (classTy arguT) ->
      tm_has_type CT Gamma' h (body) (classTy returnT) ->
      surface_syntax body = true ->
      fs_has_type CT Gamma h fs (ArrowTy (OpaqueLabeledTy (classTy returnT)) T') ->
      fs_has_type CT Gamma h ((MethodCall hole meth argu)  :: fs) (ArrowTy (classTy T) T')
  | T_fs_MethodCall2 : forall Gamma Gamma' meth argu e CT h T returnT cls_def body arg_id arguT T' fs,
      tm_has_type CT Gamma h (MethodCall e meth argu) (OpaqueLabeledTy (classTy returnT)) ->
      tm_has_type CT Gamma h e (classTy T) ->
      Some cls_def = CT(T) ->
      find_method cls_def meth = Some (m_def returnT meth arguT arg_id  body)  ->
      Gamma' = update_typing empty_context arg_id (classTy arguT) ->
      tm_has_type CT Gamma' h (body) (classTy returnT) ->
      surface_syntax body = true ->
      fs_has_type CT Gamma h fs (ArrowTy (OpaqueLabeledTy (classTy returnT)) T') ->
      fs_has_type CT Gamma h ((MethodCall e meth hole)  :: fs) (ArrowTy (classTy arguT) T')
  (*label data*)
  | T_fs_labelData : forall h Gamma CT T' fs T lb, 
       tm_has_type CT Gamma h (labelData hole lb) (LabelelTy T) ->
            T <> voidTy ->
      fs_has_type CT Gamma h fs (ArrowTy (LabelelTy T) T') ->
      fs_has_type CT Gamma h ((labelData hole lb)  :: fs) (ArrowTy T T')
  (*unlabel data*)
  | T_fs_unlabel : forall h Gamma CT T' fs T, 
       tm_has_type CT Gamma h (unlabel hole) T ->
      fs_has_type CT Gamma h fs (ArrowTy T T') ->
      fs_has_type CT Gamma h ((unlabel hole)  :: fs) (ArrowTy (LabelelTy T) T')
  (*labelOf data*)
  | T_fs_labelOf : forall h Gamma CT T' fs T, 
       tm_has_type CT Gamma h (labelOf hole) LabelTy ->
      fs_has_type CT Gamma h fs (ArrowTy LabelTy T') ->
      fs_has_type CT Gamma h ((labelOf hole)  :: fs) (ArrowTy (LabelelTy T) T')
  (*unlabel opaque*)
  | T_fs_unlabelOpaque : forall h Gamma CT T' fs T, 
       tm_has_type CT Gamma h (unlabelOpaque hole) T ->
      fs_has_type CT Gamma h fs (ArrowTy T T') ->
      fs_has_type CT Gamma h ((unlabelOpaque hole)  :: fs) (ArrowTy (OpaqueLabeledTy T) T')
(* assignment *)
  | T_fs_assignment : forall h Gamma CT T' T x fs, 
      tm_has_type CT Gamma h (Assignment x hole) voidTy ->
      Gamma x = Some T ->  T <> voidTy ->
      fs_has_type CT Gamma h fs (ArrowTy voidTy T') ->
      fs_has_type CT Gamma h ((Assignment x hole)  :: fs) (ArrowTy T T')
(* Field Write *)
  | T_fs_FieldWrite1 : forall h Gamma f cls_def CT clsT cls' e T' fs,
      tm_has_type CT Gamma h (FieldWrite hole f e) voidTy ->
      tm_has_type CT Gamma h e (classTy cls') ->
      Some cls_def = CT(clsT) ->
      type_of_field (find_fields cls_def) f = Some cls' ->
      fs_has_type CT Gamma h fs (ArrowTy (voidTy) T') ->
      fs_has_type CT Gamma h ((FieldWrite hole f e) :: fs) (ArrowTy (classTy clsT) T')
  | T_fs_FieldWrite2 : forall h Gamma f cls_def CT clsT cls' x T' fs,
      tm_has_type CT Gamma h (FieldWrite x f hole) voidTy ->
      tm_has_type CT Gamma h x (classTy clsT) ->
      Some cls_def = CT(clsT) ->
      type_of_field (find_fields cls_def) f = Some cls' ->
      fs_has_type CT Gamma h fs (ArrowTy (voidTy) T') ->
      fs_has_type CT Gamma h ((FieldWrite x f hole) :: fs) (ArrowTy (classTy cls') T'). 



Inductive ctn_has_type : Class_table -> typing_context -> heap -> container -> ty -> Prop :=
  | T_ctn_fs : forall h Gamma CT T lb fs open_t sf T', 
      tm_has_type CT Gamma h open_t T ->
      fs_has_type CT Gamma h fs (ArrowTy T T')  ->
      ctn_has_type CT Gamma h (Container open_t fs lb sf)  (OpaqueLabeledTy T')
  | T_ctn_sequential_exec : forall h Gamma CT T lb fs top fs' open_t sf T' T0, 
      hole_free top = true ->
      fs = top :: fs' ->
      tm_has_type CT Gamma h open_t T ->
      fs_has_type CT Gamma h fs (ArrowTy T0 T')  ->
      ctn_has_type CT Gamma h (Container open_t fs lb sf)  (OpaqueLabeledTy T').


Inductive ctn_list_has_type : Class_table -> typing_context -> heap -> list container -> ty -> Prop := 
  | T_ctn_nil : forall h Gamma CT T , 
      ctn_list_has_type CT Gamma h nil (ArrowTy T T)

  | T_ctn_list : forall h Gamma CT T T' ctn ctns' fs lb sf Gamma' T0 top T1, 
      ctn_has_type CT Gamma' h ctn (OpaqueLabeledTy T0) ->
      (*The first container has hole in it*)
      ctn = (Container return_hole (top :: fs) lb sf) ->
      (hole_free top = false -> T1 = T ) ->
      fs_has_type CT Gamma h (top :: fs) (ArrowTy (OpaqueLabeledTy T1) T0) ->
      ctn_list_has_type CT Gamma h ctns' (ArrowTy (OpaqueLabeledTy T0) T') ->
      ctn_list_has_type CT Gamma h (ctn :: ctns')  (ArrowTy (OpaqueLabeledTy T) T').


Inductive config_has_type : Class_table -> typing_context -> heap -> config -> ty -> Prop :=
  | T_config_nil : forall h Gamma CT T ctn,  
      ctn_has_type CT Gamma h ctn T ->
      config_has_type CT Gamma h (Config CT ctn nil h) T
  | T_config_ctns : forall h Gamma CT T T' ctn ctns Gamma' fs lb sf, 
      ctn_has_type CT Gamma' h ctn T ->
      ctn_list_has_type CT Gamma h ((Container return_hole fs lb sf) :: ctns) (ArrowTy T T') ->
      config_has_type CT Gamma h (Config CT ctn ((Container return_hole fs lb sf) :: ctns) h) T'
    (*method call crosses container boundary*)
  | T_config_new_container : forall Gamma Gamma' e meth argu CT h T returnT cls_def body arg_id arguT lb sf ctn ctns T'
            fs0 lb0 sf0,
      tm_has_type CT Gamma h e (classTy T) ->
      tm_has_type CT Gamma h argu (classTy arguT) ->
      Some cls_def = CT(T) ->
      find_method cls_def meth = Some (m_def returnT meth arguT arg_id  body)  ->
      Gamma' = update_typing empty_context arg_id (classTy arguT) ->
      tm_has_type CT Gamma' h (body) (classTy returnT) ->
      surface_syntax body = true -> 
      ctn_has_type CT Gamma' h (Container body nil lb sf) (OpaqueLabeledTy (classTy returnT)) ->
      ctn = (Container return_hole fs0 lb0 sf0) ->
      (*fs_has_type CT Gamma h fs0 (ArrowTy (OpaqueLabeledTy (classTy returnT)) T0) ->*)
      ctn_list_has_type CT Gamma h (ctn :: ctns) (ArrowTy (OpaqueLabeledTy (classTy returnT)) T')  ->
      config_has_type CT Gamma h (Config CT (Container body nil lb sf) (ctn::ctns) h) T'.


Hint Constructors config_has_type. 
Hint Constructors ctn_list_has_type. 
Hint Constructors ctn_has_type.
Hint Constructors fs_has_type.


Inductive terminal_state : config -> Prop :=
  | Terminal_Skip : forall lb sf ct h,
    terminal_state (Config ct (Container Skip nil lb sf) nil h)
  | Terminal_value : forall h v ct lb sf,
    value v ->
    terminal_state ( Config ct (Container v nil lb sf) nil h).

Hint Constructors terminal_state. 
Hint Constructors value. 

Hint Constructors reduction. 
Hint Constructors container. 

Inductive valid_fs : list tm -> Prop :=
  | valid_fs_nil : valid_fs nil
  | valid_fs_list : forall t fs, 
      valid_syntax t ->
      valid_fs fs ->
      valid_fs (t :: fs).
Hint Constructors valid_fs. 

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

(* special terms *)
    | ObjId o =>  true
  (* runtime labeled date*)
    | v_l e lb => (dot_free e)
    | v_opa_l e lb => (dot_free e)
    | dot => false
    | hole => true
    | return_hole => true
  end.

Fixpoint dot_free_fs (tms : list tm) : bool :=
match tms with 
| nil => true
| h :: tms' => if (dot_free h) then dot_free_fs tms' else false
end.

Inductive valid_ctn : container -> Prop:= 
  | valid_container : forall t fs lb sf, 
     valid_fs fs ->
     valid_syntax t -> 
  (*right place to go?*)
     dot_free t  = true /\ dot_free_fs fs = true ->
     (forall fs', fs <> hole :: fs') ->
     (forall fs', fs <> return_hole :: fs') ->
     valid_ctn (Container t fs lb sf).
Hint Constructors valid_ctn. 

Inductive valid_ctns : list container -> Prop:= 
  | valid_ctns_nil : valid_ctns nil
  | valid_ctns_list : forall ctn ctns, 
    valid_ctn ctn ->
    valid_ctns ctns ->
    valid_ctns (ctn :: ctns).
    
Inductive valid_config : config -> Prop :=
  | valid_conf : forall CT t fs lb sf ctns h, 
    valid_ctns ctns ->
    valid_ctn (Container t fs lb sf) ->
    hole_free t = true ->
    wfe_heap CT h -> field_wfe_heap CT h ->
    wfe_ctn_list CT h ctns ->  wfe_stack_frame CT h sf ->
    valid_config (Config CT (Container t fs lb sf) ctns h). 

Lemma surface_syntax_is_hole_free : forall t, 
  surface_syntax t = true -> hole_free t = true. 
Proof. intros. induction t; auto; try (apply surface_syntax_if in H; destruct H; apply IHt1 in H; apply IHt2 in H0; 
        unfold hole_free; fold hole_free); try (rewrite H); auto; try (unfold surface_syntax in H; inversion H).
Qed. 

Lemma value_is_hole_free : forall v, 
  value v -> hole_free v = true. 
Proof. intro v. intro H_v. induction H_v; subst; auto. Qed.  

Lemma value_progress : forall CT v fs lb sf ctns h T, 
config_has_type CT empty_context h  (Config CT (Container v fs lb sf) ctns h) T ->
valid_config (Config CT (Container v fs lb sf) ctns h) ->
value v ->
terminal_state (Config CT (Container v fs lb sf) ctns h) \/
(exists config' : config,
   Config CT (Container v fs lb sf) ctns h ==> config').
Proof. intros CT v fs lb sf ctns h T. intro H_typing. intro H_config. intro Hv.
destruct fs.  destruct ctns. auto. inversion H_typing.  inversion H6. subst.
right.   exists (Config CT (Container (v_opa_l v lb) fs lb0 sf0) ctns h). auto.
right.  subst. exists (Config CT (Container (v_opa_l v lb) fs lb0 sf0) ctns h). auto.
subst. 
right. exists (Config CT (Container (v_opa_l v lb) fs0 lb1 sf1) ctns h). auto.
destruct t; right. 
- exists (Config CT (Container (Tvar i) fs lb sf) ctns h); auto. 
- exists (Config CT (Container (null) fs lb sf) ctns h); auto.
- inversion H_config. inversion H7.  subst. inversion H17. inversion H1. subst.  
+ assert (surface_syntax (FieldAccess t i) = true). auto. apply surface_syntax_is_hole_free in H. 
exists (Config CT (Container (FieldAccess t i) fs lb sf) ctns h); auto.
+ subst. exists (Config CT (Container (FieldAccess v i) fs lb sf) ctns h). auto. 
+ subst. apply value_is_hole_free in H4. 
exists (Config CT (Container (FieldAccess t i) fs lb sf) ctns h); auto.
- inversion H_config. inversion H7.  subst. inversion H17. inversion H1. subst.  
+ subst.  assert (surface_syntax (MethodCall t1 i t2) = true). unfold surface_syntax. fold surface_syntax. 
rewrite H5. rewrite H14.  auto. 
apply surface_syntax_is_hole_free in H. 
exists (Config CT (Container (MethodCall t1 i t2)  fs lb sf) ctns h); auto.
+ subst. exists (Config CT (Container (MethodCall v i t2) fs lb sf) ctns h). auto. 
+ subst. apply value_is_hole_free in H5.  apply surface_syntax_is_hole_free in H14.
assert (hole_free (MethodCall t1 i t2) = true). unfold hole_free. fold hole_free. rewrite H5. rewrite H14. auto.
exists (Config CT (Container (MethodCall t1 i t2) fs lb sf) ctns h); auto.
+ subst. exists (Config CT (Container (MethodCall t1 i v)  fs lb sf) ctns h); auto.
+ subst. apply value_is_hole_free in H5. apply value_is_hole_free in H14. 
assert (hole_free (MethodCall t1 i t2) = true). unfold hole_free. fold hole_free. rewrite H5. rewrite H14. auto.
exists (Config CT (Container (MethodCall t1 i t2) fs lb sf) ctns h); auto. 
- exists (Config CT (Container (NewExp c) fs lb sf) ctns h); auto.
-  exists (Config CT (Container (l l0) fs lb sf) ctns h); auto.
- inversion H_config. inversion H7.  subst. inversion H17. inversion H1. subst.  
+ subst. assert (surface_syntax (labelData t l0) = true). unfold surface_syntax. fold surface_syntax. auto.  
apply surface_syntax_is_hole_free in H. 
exists (Config CT (Container (labelData t l0) fs lb sf) ctns h); auto.
+ subst. exists (Config CT (Container (labelData v l0) fs lb sf) ctns h); auto.
+ subst.  assert (hole_free t = true). apply value_is_hole_free. auto. 
assert (hole_free (labelData t l0) = true). unfold hole_free. fold hole_free. auto. 
exists (Config CT (Container (labelData t l0) fs lb sf) ctns h); auto.
- inversion H_config. inversion H7.  subst. inversion H17. inversion H1. subst.  
+ subst. assert (surface_syntax (unlabel t) = true). unfold surface_syntax. fold surface_syntax. auto.  
apply surface_syntax_is_hole_free in H.  
exists (Config CT (Container (unlabel t) fs lb sf) ctns h); auto.
+ subst. exists (Config CT (Container (unlabel v ) fs lb sf) ctns h); auto.
+ subst. assert (hole_free t = true). apply value_is_hole_free. auto. 
assert (hole_free (unlabel t) = true). unfold hole_free. fold hole_free. auto. 
exists (Config CT (Container (unlabel t) fs lb sf) ctns h); auto.
- inversion H_config. inversion H7.  subst. inversion H17. inversion H1. subst.  
+ subst. assert (surface_syntax (labelOf t) = true). unfold surface_syntax. fold surface_syntax. auto.  
apply surface_syntax_is_hole_free in H.  
exists (Config CT (Container (labelOf t) fs lb sf) ctns h); auto.
+ subst. exists (Config CT (Container (labelOf v ) fs lb sf) ctns h); auto.
+ subst. assert (hole_free t = true). apply value_is_hole_free. auto. 
assert (hole_free (labelOf t) = true). unfold hole_free. fold hole_free. auto. 
exists (Config CT (Container (labelOf t) fs lb sf) ctns h); auto.
- inversion H_config. inversion H7.  subst. inversion H17. inversion H1. subst.  
+ subst. assert (surface_syntax (unlabelOpaque t) = true). unfold surface_syntax. fold surface_syntax. auto.  
apply surface_syntax_is_hole_free in H.  
exists (Config CT (Container (unlabelOpaque t) fs lb sf) ctns h); auto.
+ subst. exists (Config CT (Container (unlabelOpaque v ) fs lb sf) ctns h); auto.
+ subst. assert (hole_free t = true). apply value_is_hole_free. auto. 
assert (hole_free (unlabelOpaque t) = true). unfold hole_free. fold hole_free. auto. 
exists (Config CT (Container (unlabelOpaque t) fs lb sf) ctns h); auto.
- exists (Config CT (Container Skip fs lb sf) ctns h); auto.
- inversion H_config. inversion H7.  subst. inversion H17. inversion H1. subst.  
+ subst. assert (surface_syntax (Assignment i t) = true). unfold surface_syntax. fold surface_syntax. auto.  
apply surface_syntax_is_hole_free in H.  
exists (Config CT (Container (Assignment i t) fs lb sf) ctns h); auto.
+ subst. exists (Config CT (Container (Assignment i v) fs lb sf) ctns h); auto.
+ subst. assert (hole_free t = true). apply value_is_hole_free. auto. 
assert (hole_free (Assignment i t) = true). unfold hole_free. fold hole_free. auto. 
exists (Config CT (Container (Assignment i t) fs lb sf) ctns h); auto.
- inversion H_config. inversion H7.  subst. inversion H17. inversion H1. subst.  
+ subst.  assert (surface_syntax (FieldWrite t1 i t2) = true). unfold surface_syntax. fold surface_syntax. 
rewrite H5. rewrite H14.  auto. 
apply surface_syntax_is_hole_free in H. 
exists (Config CT (Container (FieldWrite t1 i t2)  fs lb sf) ctns h); auto.
+ subst. apply value_is_hole_free in H5.  apply surface_syntax_is_hole_free in H14.
assert (hole_free (FieldWrite t1 i t2) = true). unfold hole_free. fold hole_free. rewrite H5. rewrite H14. auto.
exists (Config CT (Container (FieldWrite t1 i t2) fs lb sf) ctns h); auto.
+ subst. exists (Config CT (Container (FieldWrite v i t2) fs lb sf) ctns h); auto. 
+ subst. subst. apply value_is_hole_free in H5.  apply value_is_hole_free in H14.
assert (hole_free (FieldWrite t1 i t2) = true). unfold hole_free. fold hole_free. rewrite H5. rewrite H14. auto.
exists (Config CT (Container (FieldWrite t1 i t2)  fs lb sf) ctns h); auto.
+ subst. exists (Config CT (Container (FieldWrite t1 i v) fs lb sf) ctns h); auto.
- inversion H_config. inversion H7.  subst. inversion H17. inversion H1. subst.  
  apply surface_syntax_is_hole_free in H5.   apply surface_syntax_is_hole_free in H15.
  assert (hole_free (If i i0 t1 t2) = true). unfold  hole_free. fold hole_free.  rewrite H5. rewrite H15.  auto. 
  exists (Config CT (Container (If i i0 t1 t2) fs lb sf) ctns h); auto.
- inversion H_config. inversion H7.  subst. inversion H17. inversion H1. subst.  
  apply surface_syntax_is_hole_free in H5.   apply surface_syntax_is_hole_free in H13.
  assert (hole_free (Sequence t1 t2) = true). unfold  hole_free. fold hole_free.  rewrite H5. rewrite H13.  auto. 
  exists (Config CT (Container (Sequence t1 t2) fs lb sf) ctns h); auto.
- assert (value (ObjId o)). auto. 
  apply value_is_hole_free in H. 
  assert (hole_free (ObjId o) = true). unfold  hole_free. fold hole_free. auto. 
  exists (Config CT (Container (ObjId o) fs lb sf) ctns h); auto.
- inversion H_config. inversion H7.  subst. inversion H17. inversion H1. subst.  
  apply value_is_hole_free in H4. 
  assert (hole_free (v_l t l0) = true). unfold  hole_free. fold hole_free. auto. 
  exists (Config CT (Container (v_l t l0) fs lb sf) ctns h); auto.
- inversion H_config. inversion H7.  subst. inversion H17. inversion H1. subst.  
  apply value_is_hole_free in H4. 
  assert (hole_free (v_opa_l t l0) = true). unfold  hole_free. fold hole_free. auto. 
  exists (Config CT (Container (v_opa_l t l0) fs lb sf) ctns h); auto.
-   inversion H_config. inversion H7. subst. destruct H20 with fs. auto. 
-    inversion H_config. inversion H7. subst. destruct H19. inversion H0. 
-   inversion H_config. inversion H7. subst. destruct H21 with fs. auto. 
Qed. 

Hint Constructors value. 

Lemma excluded_middle_value : forall t,
  (value t) \/ ~ value t.
  Proof with eauto.
    intros. induction t; try (left; auto; fail); try (right; intro contra; inversion contra;fail).
    destruct IHt. left; auto. right. intro contra. inversion contra. intuition. 
      destruct IHt. left; auto. right. intro contra. inversion contra. intuition. 
Qed. 

Lemma exclude_middle_unlabelOpaque : (forall t, ((exists v, value v /\ t = unlabelOpaque v) 
        \/ (forall v, t <> unlabelOpaque v) 
          \/ (exists t', t = unlabelOpaque t' /\ ~ value t'))).
  Proof with eauto. intro t. induction t; try (right; left; intro v0; intro contra; inversion contra; fail).
  pose proof (excluded_middle_value t). destruct H. left. exists t. auto.
  right. right. exists t. auto. Qed.

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


Theorem progress : forall config T CT h t fs lb sf ctns', 
  config = (Config CT (Container t fs lb sf) ctns' h) ->
  valid_config (Config CT (Container t fs lb sf) ctns' h) ->
  config_has_type CT empty_context h config T -> terminal_state config \/ (exists config', config ==> config').
Proof with eauto.
  intros config T CT h t fs lb sf ctns'.
  intro H_config. intro H_valid_config. 
  intro H_typing. 
  remember (empty_context) as Gamma.
  inversion H_typing. inversion H. induction H5. subst. 
- inversion H5. 
- subst.  inversion H3. subst. apply value_progress with  (OpaqueLabeledTy T1); auto.
(*
- subst.  pose proof (excluded_middle_value e). destruct H1.
  right. inversion H1; subst; inversion H6. 
  + subst. destruct H13 as [F]. destruct H2 as [lo].
      inversion H_valid_config. 
      assert (exists v, F(f) = Some v).
      apply field_val_of_heap_obj with h o CT cls_def0 lo cls' (find_fields cls_def); auto. subst. 
      rewrite <- H5 in H14. inversion H14. auto.  subst. 
      destruct H24 as [v]. 
      remember (join_label lo lb0) as l'.
      exists (Config CT (Container v fs0 l' sf0) ctns h); auto.  
      apply ST_fieldRead3 with lo cls_def0 F; auto. 
  +  exists Error_state; subst; auto.
  + subst. inversion H4.  subst.  inversion H_valid_config. inversion H15.  destruct H27. inversion H27. 
  + right. exists (Config CT (Container (e) ((FieldAccess hole f)::fs0) lb0 sf0) ctns h); auto. 
- subst.  pose proof (excluded_middle_value e). destruct H1.
  right. inversion H1; subst; inversion H6_. 
  + subst. pose proof (excluded_middle_value argu). destruct H2. 

 destruct H13 as [F]. destruct H3 as [lx].
  subst. rewrite <- H5 in H6. inversion H6. subst. 
  remember (sf_update empty_stack_frame arg_id argu) as sf'.
  exists (Config CT (Container body nil lb0 sf' ) ((Container (hole) fs0 lb0 sf0 ) :: ctns) h). auto.
  apply ST_MethodCall_normal with cls_def0 F lx arg_id arguT returnT; auto.
    ++ pose proof (exclude_middle_unlabelOpaque argu). destruct H3.  
  +++ destruct H3 as [v]. destruct H3. 
  destruct H13 as [F]. destruct H10 as [lo].
  rewrite H9 in H6_0. inversion H6_0. subst. inversion H3; subst; inversion H18.
  ++++ subst.  ctn_has_type
  exists Error_state. auto.
  ++++ subst.
  remember ( sf_update empty_stack_frame arg_id v0) as sf'. 
  remember ( join_label lb0 lb1) as lb'. 
  exists (Config CT (Container body nil lb' sf' ) ((Container dot fs0 lb0 sf0 ) :: ctns) h). 
  apply ST_MethodCall_unlableOpaque with cls_def0 F arg_id arguT returnT lo; auto. 
  rewrite <- H5 in H6. inversion H6. subst. auto. 
  ++++ subst. inversion H4.  subst.  inversion H_valid_config. inversion H22.
  destruct H33. inversion H33. 
    +++ destruct H3. 
  ++++ exists (Config CT (Container (argu) ((MethodCall (ObjId o) meth hole)::fs0) lb0 sf0) ctns h); auto. 
  ++++ exists (Config CT (Container (argu) ((MethodCall (ObjId o) meth hole)::fs0) lb0 sf0) ctns h); auto.
    apply ST_MethodCall4.  intros. intro contra. destruct H3 as [t']. destruct H3.  
    rewrite H3 in contra. inversion contra.  subst. intuition. 
      auto. auto. 
  +  exists Error_state; subst; auto.
  + subst. inversion H4.  subst.  inversion H_valid_config. inversion H15.  destruct H27. inversion H27. 
  + right. exists (Config CT (Container (e) ((MethodCall hole meth argu)::fs0) lb0 sf0) ctns h); auto.
- subst. inversion H4. subst. destruct H6 as [cls]. destruct H1 as [field_defs]. destruct H1 as [method_defs].
   destruct H1. remember (get_fresh_oid h) as o. 
    remember (init_field_map (find_fields cls) empty_field_map) as F. 
    remember (add_heap_obj h o (Heap_OBJ cls F lb)) as h'.
  right. exists (Config CT (Container (ObjId o) fs lb sf ) ctns' h'). 
  apply ST_NewExp with field_defs method_defs cls F; auto. 
- inversion H4. subst.   inversion H6. subst.  apply value_progress with T; auto.
- subst.  pose proof (excluded_middle_value e). destruct H1.
  right. 
  + exists (Config CT (Container (v_l e lb1)  fs0 lb0 sf0) ctns h); auto. 
  + right. exists (Config CT (Container e ((labelData hole lb1) :: fs0) lb0 sf0) ctns h ). auto. 
- subst.  pose proof (excluded_middle_value e). destruct H1.
  right. 
  + inversion H1; subst; inversion H6. subst.  
  ++ exists Error_state. auto. 
  ++ subst. remember (join_label lb0 lb1) as l'.
    exists (Config CT (Container v fs0 l' sf0) ctns h). auto.
  ++ subst. inversion H4.  subst.  inversion H_valid_config. inversion H14. destruct H25. inversion H25. 
  + right. exists (Config CT (Container (e) ((unlabel hole)::fs0) lb0 sf0) ctns h); auto.
- subst.  pose proof (excluded_middle_value e). destruct H1.
  right. 
  + inversion H1; subst; inversion H6. subst.  
  ++ exists Error_state. auto. 
  ++ subst. 
    exists (Config CT (Container (l lb1) fs0 lb0 sf0) ctns h). auto.
  ++ subst. inversion H4.  subst.  inversion H_valid_config. inversion H14. destruct H25. inversion H25. 
  + right. exists (Config CT (Container (e) ((labelOf hole)::fs0) lb0 sf0) ctns h); auto.
- subst.  pose proof (excluded_middle_value e). destruct H1.
  right. 
  + inversion H1; subst; inversion H6. subst.  
  ++ exists Error_state. auto. 
  ++ subst. 
     remember (join_label lb0 lb1) as l'.
    exists (Config CT (Container (v) fs0 l' sf0) ctns h). auto.
  ++ subst. inversion H4.  subst.  inversion H_valid_config. inversion H14. destruct H25. inversion H25. 
  + right. exists (Config CT (Container (e) ((unlabelOpaque hole)::fs0) lb0 sf0) ctns h); auto.
- subst. destruct fs0. 
  + inversion H4. subst. inversion H_typing. inversion H. subst. inversion H21. subst.  
      inversion H18. subst. intuition.
   + right.   exists (Config CT (Container t0 fs0 lb0 sf0) ctns h ); auto.

- subst.  inversion H6. 
- subst.  pose proof (excluded_middle_value x). destruct H1.
  right. inversion H1; subst; inversion H6_. 
  + subst. pose proof (excluded_middle_value e). destruct H2. 
  ++  destruct H13 as [F]. destruct H3 as [lx].
  subst. rewrite <- H5 in H6. inversion H6. subst. 
  remember (fields_update F f e) as F'. rename lx into lo. 
  case_eq (flow_to lo lb0). +++ intro. 
  exists (Config CT (Container Skip fs0 lb0 sf0) ctns h ); auto.
  remember (update_heap_obj h o (Heap_OBJ cls_def0 F' lo)) as h'. auto. 
  apply ST_fieldWrite_normal with h' lo cls_def0 F F'; auto.
  +++ intro. exists Error_state. apply ST_fieldWrite_leak with lo cls_def0 F; auto. 
  ++ pose proof (exclude_middle_unlabelOpaque e). destruct H3.  
  +++ destruct H3 as [v]. destruct H3. 
  destruct H13 as [F]. destruct H10 as [lo].
  rewrite H9 in H6_0. inversion H6_0. subst. inversion H3; subst; inversion H17.
  ++++ subst.  
  exists Error_state. auto.
  ++++ subst.
  remember (fields_update F f v0) as F'.
  remember (update_heap_obj h o (Heap_OBJ cls_def0 F' lo)) as h'.
  case_eq (flow_to lo (join_label lb0 lb1) ).
  exists (Config CT (Container Skip fs0 lb0 sf0) ctns h'). auto. 
  apply ST_fieldWrite_unlableOpaque with lo cls_def0 F F'; auto.
  intro.  exists Error_state. auto. 
  apply ST_fieldWrite_unlableOpaque_leak with lo cls_def0 F; auto.
  ++++ subst. inversion H4.  subst.  inversion H_valid_config. inversion H21.  destruct H32. inversion H32. 

  +++ destruct H3. 
  ++++ exists (Config CT (Container (e) ((FieldWrite (ObjId o) f hole)::fs0) lb0 sf0) ctns h); auto. 
  ++++ exists (Config CT (Container (e) ((FieldWrite (ObjId o) f hole)::fs0) lb0 sf0) ctns h); auto. 
apply ST_fieldWrite4.  intros. intro contra. destruct H3 as [t']. destruct H3.  
rewrite H3 in contra. inversion contra.  subst. intuition. 
  auto. auto. 
+ subst. exists Error_state. auto. 
+  subst. inversion H4.  subst.  inversion H_valid_config. inversion H15.  destruct H26. inversion H26. 
+ right. exists (Config CT (Container (x) ((FieldWrite hole f e) ::fs0) lb0 sf0) ctns h); auto. 
- inversion H6_. subst. inversion H18. 
- right. exists (Config CT (Container  e1 (e2 :: fs0)  lb0 sf0) ctns h). auto. 
- subst. inversion H4. subst.   apply value_progress with T; auto.
- subst. inversion H4. subst.   apply value_progress with T; auto.
- subst. inversion H4. subst.   apply value_progress with T; auto.
- subst. inversion H4.  subst.  inversion H_valid_config. inversion H12. unfold hole_free in H24. 
    inversion H24. 
- subst. inversion H4.  subst.  inversion H_valid_config. inversion H12. 
  destruct H23. unfold dot_free in H23. inversion H23. 
Qed.  
*)Admitted. 


Lemma value_typing_invariant_gamma : forall CT gamma h v T gamma', 
  value v ->
  tm_has_type CT gamma h v T -> 
  tm_has_type CT gamma' h v T .
Proof with eauto. 
 intros CT gamma h v T gamma'. intro H_v. intro typing. generalize dependent T. 
 induction H_v; intro T; intro typing; try (inversion typing; auto; fail).
 -  inversion typing.   
 apply T_ObjId with (cls_def:=cls_def); auto.
Qed. 

Hint Constructors tm_has_type.
Theorem preservation : forall T CT h t fs lb sf ctns h' t' fs' lb' sf' ctns',
    valid_config (Config CT (Container t fs lb sf) ctns h) ->
    config_has_type CT empty_context h (Config CT (Container t fs lb sf) ctns h)  T ->
     (Config CT (Container t fs lb sf) ctns h) ==>  (Config CT (Container t' fs' lb' sf') ctns' h') ->
    config_has_type CT empty_context h'  (Config CT (Container t' fs' lb' sf') ctns' h') T.
Proof with auto.
  intros T CT h t fs lb sf ctns h' t' fs' lb' sf' ctns'. 
  intro H_valid_config. 
  intro H_typing. 
  remember (empty_context) as Gamma. intro H_reduction.
  remember (Config CT (Container t fs lb sf) ctns h) as config. 
  remember (Config CT (Container t' fs' lb' sf') ctns' h') as config'.
  generalize dependent T.   generalize dependent h.
    generalize dependent t.   generalize dependent fs.
    generalize dependent lb.   generalize dependent sf. generalize dependent ctns. 
  generalize dependent h'.
    generalize dependent t'.   generalize dependent fs'.
    generalize dependent lb'.   generalize dependent sf'. generalize dependent ctns'.
  induction H_reduction; intros; inversion Heqconfig; inversion Heqconfig'; subst.
- inversion H_typing. subst. inversion H6. subst. inversion H10.  inversion H4.
   subst. auto. subst.  auto. subst. auto. 
(*field access*)
-  inversion H_typing. subst. auto.  apply T_config_nil; auto. inversion H6. subst.
    inversion H10. subst. 
  + apply T_ctn_fs with ((classTy clsT)); auto. 
  apply T_fs_FieldAccess with cls' (find_fields cls_def) cls_def; auto. 
  apply T_FieldAccess with cls_def clsT (find_fields cls_def); auto.
(* 
  + subst. inversion H10. subst. apply T_ctn_fs with  (classTy clsT); auto. 
      apply T_fs with (classTy cls'); auto.  
      apply T_FieldAccess with cls_def clsT (find_fields cls_def); auto. apply T_hole.
      induction fs0. inversion H11. 
      intro contra. inversion contra. 
  + subst. apply T_config_ctns with T0; auto. destruct fs0. 
  ++ inversion H5. +++ subst.  
      inversion H11. subst. apply T_ctn_fs with (classTy clsT); auto. 
     apply T_fs_nil. apply T_FieldAccess with cls_def clsT (find_fields cls_def); auto. apply T_hole.
 +++ inversion H12.
 ++ subst. inversion H5.   subst. inversion H12. subst. inversion H11. subst. 
   apply T_ctn_fs with (classTy clsT); auto.  apply T_fs with (classTy cls'); auto. 
   apply T_FieldAccess with cls_def clsT (find_fields cls_def); auto. apply T_hole.
   intro contra. inversion contra.*) + subst. admit. + subst. admit. +admit. 
- inversion H_typing. subst. 
  + apply T_config_nil. inversion H6. subst.  
     inversion H11. subst. 
  ++ inversion H7. ++ inversion H9. 
   ++ subst. inversion H12.
  ++  subst. apply T_ctn_fs with  (classTy cls'); auto.
    apply T_FieldAccess with cls_def clsT (find_fields cls_def); auto.
  ++ subst. inversion H11. subst. inversion H9. 
  + subst. apply T_config_ctns with T0 Gamma'; auto. inversion H5.   subst. inversion H12. 
    ++  subst. inversion H9. ++ subst.      inversion H10. 
    ++ subst. inversion H13. 
    ++ subst. 
      apply T_ctn_fs with  (classTy cls'); auto.
      apply T_FieldAccess with cls_def clsT (find_fields cls_def); auto.
    ++  subst. inversion H12. subst. inversion H10. 

- inversion H_typing. subst. 
  + apply T_config_nil. inversion H7. subst.  inversion H11. 
  ++ subst.
      apply T_ctn_fs with  (classTy cls'); auto.
      inversion H3. subst.   
      destruct H13 as [field_defs]. destruct H1 as [method_defs].
      assert (t' = null \/
             (exists
                (o' : oid) (field_defs0 : list field) (method_defs0 : 
                                                       list method_def) 
              (field_cls_def : CLASS) (F' : FieldMap) (lo : Label),
                t' = ObjId o' /\
                field_cls_def =
                class_def cls' field_defs0 method_defs0 /\
                lookup_heap_obj h' o'  = Some (Heap_OBJ field_cls_def F' lo) /\
                CT cls' = Some field_cls_def)
      ).
      inversion H_valid_config. subst. 
     destruct H15 as [F0]. destruct H1 as [lo0]. rewrite H1 in H. inversion H. subst.
        apply field_consist_typing with o cls_def F0 fname lo0 clsT field_defs method_defs; auto.
     rewrite <- H4 in H5. inversion H5.  auto.      rewrite <- H4 in H5. inversion H5.  auto. 
     rewrite <- H4 in H5. inversion H5.  auto. rewrite <- H6 in H14.    
     unfold find_fields in H14. auto.
    
     destruct H2. subst. apply T_null. auto. destruct H2 as [o']. destruct H2 as [field_defs0]. 
     destruct H2 as [method_defs0]. destruct H2 as [field_cls_def]. destruct H2 as [FF]. destruct H2 as [loF].
     destruct H2. destruct H6. destruct H8. subst.  apply T_ObjId with  (class_def cls' field_defs0 method_defs0); auto.
     exists field_defs0. exists method_defs0. auto. 
     exists FF. exists loF. auto.
    ++  subst. admit. 
  
+ subst. apply T_config_ctns with T0 Gamma'; auto. inversion H6.  subst. inversion H12.
    ++  subst. 
      apply T_ctn_fs with  (classTy cls'); auto.
     inversion H3. subst.    
      destruct H14 as [field_defs]. destruct H1 as [method_defs].
      assert (t' = null \/
             (exists
                (o' : oid) (field_defs0 : list field) (method_defs0 : 
                                                       list method_def) 
              (field_cls_def : CLASS) (F' : FieldMap) (lo : Label),
                t' = ObjId o' /\
                field_cls_def =
                class_def cls' field_defs0 method_defs0 /\
                lookup_heap_obj h' o'  = Some (Heap_OBJ field_cls_def F' lo) /\
                CT cls' = Some field_cls_def)
      ).
      destruct H16 as [F0]. destruct H2 as [lo0]. inversion H_valid_config. subst. 
      rewrite H2 in H. inversion H. subst.
        apply field_consist_typing with o cls_def F0 fname lo0 clsT field_defs method_defs; auto.
     rewrite <- H4 in H5. inversion H5.  auto.      rewrite <- H4 in H5. inversion H5.  auto. 
     rewrite <- H4 in H5. inversion H5.  auto. rewrite <- H7 in H15.    
     unfold find_fields in H15. auto.
    
     destruct H2. subst. apply T_null. auto. destruct H2 as [o']. destruct H2 as [field_defs0]. 
     destruct H2 as [method_defs0]. destruct H2 as [field_cls_def]. destruct H2 as [FF]. destruct H2 as [loF].
     destruct H2. destruct H7. destruct H9. subst.  apply T_ObjId with  (class_def cls' field_defs0 method_defs0); auto.
     exists field_defs0. exists method_defs0. auto. 
     exists FF. exists loF. auto.
    ++  admit. 
  + subst. inversion H17. 

-  inversion H_typing. subst. 
  + apply T_config_nil. inversion H6. 
  ++ subst.  inversion H10. subst. rename id0 into meth. 
       apply T_ctn_fs with  (classTy T); auto. 
      remember (update_typing empty_context arg_id (classTy arguT)) as gamma0. 
      apply T_fs_MethodCall1 with gamma0 t' returnT cls_def body arg_id arguT; auto.
  ++ subst. admit. 

  +  subst. apply T_config_ctns with T0 Gamma'; auto. inversion H5.  subst. inversion H11. 
  ++ subst. 
      apply T_ctn_fs with  (classTy T0); auto.
      remember (update_typing empty_context arg_id (classTy arguT)) as gamma0. 
      apply T_fs_MethodCall1 with gamma0 t' returnT cls_def body arg_id arguT; auto. 
  ++ subst. admit. 
  + subst. admit. 
(*(MethodCall t id0 e2) *)
-   inversion H_typing. subst. 
  + apply T_config_nil. inversion H6. subst.  inversion H11. subst.
   ++inversion H7. 
    ++ subst.  inversion H9. 
    ++ subst.  inversion H12. 
   ++ subst. 
      apply T_ctn_fs with (OpaqueLabeledTy (classTy returnT)); auto.
      remember ((update_typing empty_context arg_id (classTy arguT))) as Gamma'. 
      apply T_MethodCall with Gamma' T cls_def body arg_id arguT; auto. 
   ++   subst.
      inversion H_valid_config. inversion H14. subst.  inversion H29. subst. 
      inversion H2; subst; try (unfold surface_syntax in H4; inversion H4; fail); 
      try (unfold surface_syntax in H1; inversion H1; fail).
   ++ subst. inversion H11. subst. inversion H9.  
  + subst. apply T_config_ctns with T0 Gamma'; auto. inversion H5.  subst. inversion H12. 
    ++ subst. inversion H9.   
    ++ subst. inversion H10. 
    ++ subst. inversion H13. 
    ++ subst. 
     inversion H10. subst. 
      apply T_ctn_fs with (OpaqueLabeledTy (classTy returnT)); auto.
      remember ((update_typing empty_context arg_id (classTy arguT))) as gamma0. 
      apply T_MethodCall with gamma0 T0 cls_def body arg_id arguT; auto.
    ++  subst.
      inversion H_valid_config.  inversion H15. subst. inversion H30. subst. 
      inversion H2; subst; try (unfold surface_syntax in H4; inversion H4; fail); 
      try (unfold surface_syntax in H1; inversion H1; fail).
    ++ subst. inversion H12. subst. inversion H10. 
-   inversion H_typing. subst. 
  + apply T_config_nil. inversion H7. subst.  inversion H12. 
    ++ subst. inversion H8.  case_eq (hole_free v1); intro; rewrite H1 in H2; inversion H2. 
    ++ subst.   inversion H10.  case_eq (hole_free v1); intro; rewrite H1 in H2; inversion H2. 
    ++ subst. inversion H13.  case_eq (hole_free v1); intro; rewrite H1 in H2; inversion H2.
    ++ subst.  
      apply T_ctn_fs with (OpaqueLabeledTy (classTy returnT)); auto. subst. 
      inversion H_valid_config.  inversion H15. subst. inversion H30. subst. 
      inversion H3; subst; try (unfold surface_syntax in H5; inversion H5; fail); 
      try (unfold surface_syntax in H2; inversion H2; fail).
    ++
      apply T_ctn_fs with (OpaqueLabeledTy (classTy returnT)); auto. subst. 
      remember (update_typing empty_context arg_id (classTy arguT)) as gamma0. 
      apply T_MethodCall with gamma0 T cls_def body arg_id arguT; auto.
    ++ subst. inversion H12. subst. inversion H10. 
      case_eq (hole_free v1); intro; rewrite H1 in H2; inversion H2.
  + subst. apply T_config_ctns with T0 Gamma'; auto. inversion H6.  subst. inversion H13. 
     ++ subst.   inversion H10.  case_eq (hole_free v1); intro; rewrite H1 in H2; inversion H2. 
      ++ subst.  inversion H11.  case_eq (hole_free v1); intro; rewrite H1 in H2; inversion H2. 
  ++ subst. inversion H14.  case_eq (hole_free v1); intro; rewrite H1 in H2; inversion H2.
     ++ subst. inversion H_valid_config.  inversion H16. subst. inversion H31. subst. 
      inversion H3; subst; try (unfold surface_syntax in H5; inversion H5; fail); 
      try (unfold surface_syntax in H2; inversion H2; fail).
      ++       apply T_ctn_fs with (OpaqueLabeledTy (classTy returnT)); auto. subst. 
      remember (update_typing empty_context arg_id (classTy arguT)) as gamma0. 
      apply T_MethodCall with gamma0 T0 cls_def body arg_id arguT; auto.
       ++ subst. inversion H13. subst. inversion H11. 
      case_eq (hole_free v1); intro; rewrite H1 in H2; inversion H2.
(*(Container t' (MethodCall v id0 hole :: fs0) lb' sf')  *)
-  inversion H_typing. subst. 
  + apply T_config_nil. inversion H8. subst. 
  ++   inversion H12. subst. rename id0 into meth. 
      apply T_ctn_fs with  (classTy arguT); auto. 

      remember (update_typing empty_context arg_id (classTy arguT)) as gamma0. 
      apply T_fs_MethodCall2 with gamma0 t' T returnT cls_def body arg_id; auto.
   ++ 
      subst.  admit.  
  +  subst. apply T_config_ctns with T0 Gamma'; auto. inversion H7.  
  ++ subst. inversion H13.  subst. 
      apply T_ctn_fs with  (classTy arguT); auto.
      remember (update_typing empty_context arg_id (classTy arguT)) as gamma0. 
      apply T_fs_MethodCall2 with gamma0 t' T0 returnT cls_def body arg_id; auto.
  ++     subst. admit.
  + subst. admit. 
(*(Container t' nil lb' (sf_update empty_stack_frame arg_id v))*)
(*
- inversion H_typing. subst. 
    ++ inversion H8.
    +++  subst. inversion H12. subst. inversion H5. subst. destruct H17 as [F0]. 
    destruct H2 as [lo0]. rewrite H2 in H. inversion H. rewrite <- H4 in H7. inversion H7. subst.
    rewrite H9 in H0. inversion H0. subst.
    remember ( (update_typing empty_context arg_id0 (classTy arguT))) as gamma0.    
    apply T_config_new_container with gamma0 (ObjId o) meth v T
          returnT0 cls_def0 arg_id0   arguT fs0 lb' sf0; auto. 
    apply T_ctn_fs with (classTy returnT0); auto. auto. 
    apply T_ctn_list with fs0 lb' sf0 empty_context T'; auto. 
    apply T_ctn_fs with (OpaqueLabeledTy (classTy returnT0)) ; auto.  

    +++ subst. admit. 
    ++ subst . inversion H7.
    +++  subst. inversion H13. subst. inversion H5. subst. destruct H18 as [F0]. 
    destruct H2 as [lo0]. rewrite H2 in H. inversion H. rewrite <- H4 in H8. inversion H8. subst.
    rewrite H10 in H0. inversion H0. subst.

    remember ((update_typing empty_context arg_id0 (classTy arguT))) as gamma0. 
    apply T_config_new_container with gamma0 (ObjId o) meth v T0
          returnT0 cls_def0 arg_id0   arguT fs0 lb' sf0; auto.
    admit. admit. apply T_ctn_fs with (classTy returnT0); auto.    
    apply T_ctn_list with fs0 lb' sf0 Gamma' T'; auto. 
    apply T_ctn_fs with (OpaqueLabeledTy (classTy returnT0)) ; auto.  

+++ subst. admit. 
++ subst. inversion H18. 
-  (*(Container t' nil (join_label lb0 lx) (sf_update empty_stack_frame arg_id v))*)
   inversion H_typing. subst. 
    ++ inversion H8.
    +++  subst. inversion H11. subst. inversion H5. subst. destruct H17 as [F0]. 
    destruct H0 as [lo0]. rewrite H0 in H. inversion H. rewrite <- H4 in H7. inversion H7. subst.
    rewrite H9 in H3. inversion H3. subst.
    remember ( (update_typing empty_context arg_id0 (classTy arguT))) as gamma0.    
    apply T_config_new_container with gamma0 (ObjId o) meth (unlabelOpaque (v_opa_l v lx)) T
          returnT0 cls_def0 arg_id0 arguT fs0 lb0 sf0; auto. 
    apply T_ctn_fs with (classTy returnT0); auto. 
    apply T_ctn_list with fs0 lb0 sf0 empty_context T'; auto. 
    apply T_ctn_fs with (OpaqueLabeledTy (classTy returnT0)) ; auto.  

    +++ subst. admit. 
    ++ subst . inversion H7.
    +++  subst. inversion H13. subst. inversion H5. subst. destruct H18 as [F0]. 
    destruct H0 as [lo0]. rewrite H0 in H. inversion H. rewrite <- H4 in H8. inversion H8. subst.
    rewrite H10 in H3. inversion H3. subst.
    remember ((update_typing empty_context arg_id0 (classTy arguT))) as gamma0. 
    apply T_config_new_container with gamma0 (ObjId o) meth (unlabelOpaque (v_opa_l v lx)) T0
          returnT0 cls_def0 arg_id0 arguT fs0 lb0 sf0; auto.
    admit. admit.  
    apply T_ctn_fs with (classTy returnT0); auto. 
    apply T_ctn_list with  fs0 lb0 sf0 Gamma' T'; auto. 
    apply T_ctn_fs  with (OpaqueLabeledTy (classTy returnT0)) ; auto.  
+++ subst. admit. 
++ subst. inversion H18. 
(*new expression*)
- inversion H_typing. subst.
  + inversion H6. 
  ++ subst. inversion H9.  subst. 
   apply T_config_nil. 
   apply T_ctn_fs with (classTy cls_name); auto.
   destruct H4 as [cls_def0]. destruct H0 as [field_defs0]. destruct H0 as [method_defs0].
   destruct H0.  
   apply T_ObjId with cls_def0; auto.  
   admit. admit.

  generalize dependent cls_name. generalize dependent h0. generalize dependent T'.
 induction fs'. intros.  inversion H10. auto. 
  intros. inversion H10. subst. 
  +++  admit. 
   +++ admit.  
  +++ subst. admit. 

  +++ subst. apply T_fs_FieldAccess with cls' (find_fields cls_def) cls_def; auto. 
    admit.  admit. 
  +++ admit.   +++ admit.   +++ admit.   +++ admit.   +++ admit. 
   +++ admit. 
++ admit.  
+
remember ((add_heap_obj h0 (get_fresh_oid h0)
     (Heap_OBJ (class_def cls_name field_defs method_defs)
        (init_field_map
           (find_fields (class_def cls_name field_defs method_defs))
           empty_field_map) lb'))) as h'.
(*
   apply T_config_nil. 
   apply T_ctn_fs with (classTy cls_name); auto.
    inversion H15. subst. 
   destruct H9 as [cls_def0]. destruct H0 as [field_defs0]. destruct H0 as [method_defs0].
   destruct H0.  
   apply T_ObjId with cls_def0; auto. admit. admit. admit. *) admit. 

+ admit.
(*(labelData hole lo :: fs0)*)
- inversion H_typing. subst. auto.  apply T_config_nil; auto. inversion H6. subst.
    inversion H10. subst. 
  + apply T_ctn_fs with ( T); auto. 
 + admit. + admit.  + admit. 
 
(*label data t lo*)
-  inversion H_typing. subst. auto.  apply T_config_nil; auto. inversion H6. subst.
   inversion H11. subst.  
   + inversion H7. 
  + subst.  inversion H9. 
  + subst. inversion H12. 
  + subst.
  apply T_ctn_fs with (LabelelTy T0); auto.
  + admit. + admit. 

- (* v_l v lo *)
inversion H_typing. subst.  inversion H6. subst. 
+ apply T_config_nil. inversion H10. subst. 
apply T_ctn_fs with (LabelelTy T); auto.
 + admit. + admit.  + admit.

- (*  (unlabel hole :: fs0)  *)
admit. 

- (*  (unlabel t)  *)
admit.

- (*   (join_label lb0 lo)   *)
admit. 

- (* (labelOf hole :: fs0) *)
admit.

- (* (labelOf t) *)
admit.

- (* l lo *)
admit.

- (* (unlabelOpaque hole :: fs0) *)
admit.


- (* (unlabelOpaque t) *)
admit.

- (*  (join_label lb0 lo)  *)
admit.

- (*(Assignment id0 hole :: fs0)  *)
admit.

- (*(Assignment id0 t)*)
admit.


- (* Skip*)
admit.

- (* (FieldWrite hole f e2 :: fs0)*)
admit.

- 
admit.

- 
admit.


- 
admit.

- 
inversion H_typing. subst. inversion H8. subst.
inversion H11. subst.
+ apply T_config_nil. auto.
apply T_ctn_fs with (voidTy); auto.
+ subst.  apply T_config_nil. auto. apply T_ctn_sequential_exec with voidTy top fs'0 T1; auto. 
 + subst. 
 inversion H7. subst. inversion H13. subst. 
 ++
 apply T_config_ctns with ((OpaqueLabeledTy T')) Gamma'; auto.
 apply  T_ctn_fs with voidTy; auto. 
  ++ subst. 
apply T_config_ctns with ((OpaqueLabeledTy T')) Gamma'; auto.
apply T_ctn_sequential_exec with voidTy top fs'0 T2; auto. 
  + subst. admit. 
  

- (* (FieldWrite update *)
admit.

- (*(Container t' fs' lb' sf')*)
inversion H_typing. subst. inversion H6. subst. 
+ inversion H10.
 ++  subst. inversion H9. subst. inversion H5.
+ subst.  apply T_config_nil.
        apply T_ctn_sequential_exec with T0 top fs'0 T1; auto.
    inversion H12. auto. 
+ subst.  apply T_config_ctns with T0 Gamma'; auto. 
    inversion H5. ++
    auto. subst.  
    apply  T_ctn_fs with T1; auto. inversion H11. auto.
    ++ subst.   
        apply T_ctn_sequential_exec with T1 top fs'0 T2; auto.
    inversion H13. auto. 
+ subst. 
    remember ( (update_typing empty_context arg_id (classTy arguT))) as gamma0.
        apply T_config_ctns with  ((OpaqueLabeledTy (classTy returnT))) gamma0; auto.
        apply  T_ctn_fs with (classTy returnT); auto. inversion H14.  auto.  

- (*(Container t' fs' lb' sf')*)
inversion H_typing. subst. inversion H6. subst. 
+ inversion H10.
 ++  subst. inversion H9. subst. inversion H5.
+ subst.  apply T_config_nil.
        apply T_ctn_sequential_exec with T0 top fs'0 T1; auto.
    inversion H12. auto. 
+ subst.  apply T_config_ctns with T0 Gamma'; auto. 
    inversion H5. ++
    auto. subst.  
    apply  T_ctn_fs with T1; auto. inversion H11. auto.
    ++ subst.   
        apply T_ctn_sequential_exec with T1 top fs'0 T2; auto.
    inversion H13. auto. 
+ subst. 
    remember ( (update_typing empty_context arg_id (classTy arguT))) as gamma0.
        apply T_config_ctns with  ((OpaqueLabeledTy (classTy returnT))) gamma0; auto.
        apply  T_ctn_fs with (classTy returnT); auto. inversion H14.  auto.  

- (*sequence *) inversion  H_typing. subst.
  + inversion H5. subst. inversion H9. subst.
++ apply T_config_nil. auto.
apply T_ctn_sequential_exec with T e2 fs0 T0; auto.
admit.
destruct fs0. inversion H10. subst. auto. 
apply T_fs_one; auto.  admit. 
apply  T_fs_no_hole with T0; auto.  admit. admit. 
++ subst. apply T_config_nil. auto. inversion H11. subst. 
apply T_ctn_sequential_exec with T e2 (top :: fs') T0; auto.

admit. apply  T_fs_no_hole with T1; auto. admit. 
  + subst.  inversion H4. subst. inversion H10. subst.
++ apply T_config_ctns with  ((OpaqueLabeledTy T')) Gamma'; auto.
apply T_ctn_sequential_exec with T0 e2 fs0 T1; auto.
admit. 
destruct fs0. inversion H11. subst. auto. 
apply T_fs_one; auto.  admit.  
apply  T_fs_no_hole with T1; auto.  admit. admit. 
++ subst. apply T_config_ctns with  ((OpaqueLabeledTy T')) Gamma'; auto.
inversion H12. subst. 
apply T_ctn_sequential_exec with T0 e2 (top :: fs') T1; auto.
admit. 
apply  T_fs_no_hole with T2; auto. admit. 

+ subst. inversion H16. subst. inversion H9. 
  ++ subst. remember ((update_typing empty_context arg_id (classTy arguT))) as gamma0.
 apply T_config_ctns with  ((OpaqueLabeledTy T1)) gamma0; auto.
 inversion H14. subst. 
  apply T_ctn_sequential_exec with T2 e2 (nil) (classTy returnT); auto.
  admit. 
 apply T_fs_one; auto. admit.   inversion H18.  sus
  apply T_ctn_list with fs1 lb0 sf0 empty_context (classTy returnT);auto.


   ++ subst. remember ((update_typing empty_context arg_id (classTy arguT))) as gamma0.
 apply T_config_ctns with  ((OpaqueLabeledTy T1)) gamma0; auto. inversion H14. 

(*skip *)
-  inversion  H_typing. subst.
  + inversion H5. subst. 
  ++  apply T_config_nil.  inversion H10; subst; try (inversion H9; fail). 
  +++ apply T_ctn_fs with T';auto.  
  +++ apply T_ctn_fs with T0;auto. 
  +++ apply T_ctn_sequential_exec with  T0 p (fs) T1; auto.
  +++  inversion H9. subst. intuition. 
  +++ subst. inversion H11. 
  ++ subst. inversion H10. subst. 
    inversion H12; subst; try (inversion H8; fail). 
   +++ apply T_config_nil. apply T_ctn_fs with T'; auto. 
  +++ apply T_config_nil.  apply T_ctn_fs with T1;auto. 
  +++ apply T_config_nil.  apply T_ctn_sequential_exec with  T1 p (fs) T2; auto.
  +++ inversion H8. case_eq (hole_free e); intro; rewrite H in H0; inversion H0.
  +++ inversion H8.  case_eq (hole_free x); intro; rewrite H in H0; inversion H0.
 + subst. inversion H4. subst. 
  ++  apply T_config_ctns with (OpaqueLabeledTy T') Gamma'; auto. 
       inversion H11; subst; try (inversion H10; fail). 
  +++  apply T_ctn_fs with T';auto. 
  +++  apply T_ctn_fs with T1;auto. 
  +++ apply T_ctn_sequential_exec with  T1 p (fs) T2; auto.
  +++  inversion H10. subst. intuition. 
  +++ subst. inversion H10. subst. intuition.
  ++ subst. inversion H11. subst. 
    inversion H13; subst; try (inversion H9; fail). 
   +++ apply T_config_ctns with (OpaqueLabeledTy T') Gamma'; auto.  apply T_ctn_fs with T'; auto. 
  +++ apply T_config_ctns with (OpaqueLabeledTy T') Gamma'; auto.  apply T_ctn_fs with T2; auto. 
  +++ apply T_config_ctns with (OpaqueLabeledTy T') Gamma'; auto.  
        apply T_ctn_sequential_exec with  T2 p (fs) T3; auto.
   +++ remember ((update_typing empty_context arg_id (classTy arguT))) as gamma0.
 apply T_config_ctns with  ((OpaqueLabeledTy  T')) Gamma'; auto.
  apply T_ctn_fs with (OpaqueLabeledTy (classTy returnT)); auto.
  apply T_MethodCall with gamma0 T0 cls_def body arg_id arguT; auto.
  +++ inversion H9.  case_eq (hole_free x); intro; rewrite H in H0; inversion H0.

- (*Container t' fs' lb' sf'*)
  inversion  H_typing. subst.
  + inversion H7. subst. 
  ++ apply T_config_nil. 
  inversion H12; subst;  try (inversion H0; fail).
  +++ apply T_ctn_fs with T';auto. 
  +++ apply T_ctn_fs with T0;auto.
  +++  apply T_ctn_sequential_exec with  T0 p ( fs) T1; auto. 
  +++ remember ((update_typing empty_context arg_id (classTy arguT))) as gamma0.
  apply T_ctn_fs with (OpaqueLabeledTy (classTy returnT)); auto.
  apply T_MethodCall with gamma0 T cls_def body arg_id arguT; auto.
  +++   apply T_ctn_fs with ( voidTy); auto. 
  ++ subst. inversion H12. subst. 
    inversion H14; subst; try (inversion H10; fail). 
   +++ apply T_config_nil. apply T_ctn_fs with T'; auto. 
  +++ apply T_config_nil. apply T_ctn_fs with T1; auto. 
  +++ apply T_config_nil. apply T_ctn_sequential_exec with  T1 p ( fs) T2; auto. 
  +++ remember ((update_typing empty_context arg_id (classTy arguT))) as gamma0.
  apply T_config_nil.  apply T_ctn_fs with (OpaqueLabeledTy (classTy returnT)); auto.
  apply T_MethodCall with gamma0 T cls_def body arg_id arguT; auto.
  +++ inversion H10.  case_eq (hole_free x); intro; rewrite H1 in H2; inversion H2.
 + subst. inversion H6. subst. 
  ++  apply T_config_ctns with (OpaqueLabeledTy T') Gamma'; auto.  inversion H13; subst; try (inversion H0; fail). 
  +++  apply T_ctn_fs with T';auto.
  +++  apply T_ctn_fs with T1;auto.
  +++  apply T_ctn_sequential_exec with  T1 p fs T2; auto. 
  +++ remember ((update_typing empty_context arg_id (classTy arguT))) as gamma0.
  apply T_ctn_fs with (OpaqueLabeledTy (classTy returnT)); auto.
  apply T_MethodCall with gamma0 T0 cls_def body arg_id arguT; auto.
  +++ inversion H0. case_eq (hole_free x); intro; rewrite H1 in H2; inversion H2.
  ++ subst. inversion H13. subst. 
    inversion H15; subst; try (inversion H11; fail); 
    apply T_config_ctns with (OpaqueLabeledTy T') Gamma'; auto.  
   +++ apply T_ctn_fs with T'; auto. 
  +++ apply T_ctn_fs with T2; auto. 
  +++ apply T_ctn_sequential_exec with  T2 p fs T3; auto.
  +++ inversion H0.  case_eq (hole_free e); intro; rewrite H1 in H2; inversion H2.
  +++ inversion H0.  case_eq (hole_free x); intro; rewrite H1 in H2; inversion H2.
*)
- admit. - admit. - admit. - admit. - admit. - admit. - admit. - admit. 
- admit. - admit. - admit. - admit. - admit. - admit. - admit. - admit. 
- admit. - admit. - admit. - admit. - admit. - admit. - admit. - admit. 
- admit. - admit. - admit. - admit. - admit. 
(*v_opa_l t lb0*)
- inversion H_typing. subst.
  + inversion H10. subst. 
  ++ inversion H12. subst.  inversion H11. subst.
    inversion H13. subst. 
 inversion H16. subst. 
  +++ apply T_config_nil. case_eq (hole_free top); intro. 
  ++++  apply T_ctn_sequential_exec with (OpaqueLabeledTy T') top fs (OpaqueLabeledTy T2); auto. 
     apply T_v_opa_l; auto. apply value_typing_invariant_gamma with Gamma';auto. 
  ++++ apply H14 in H0. subst.  apply T_ctn_fs with (OpaqueLabeledTy T'); auto. 
    apply T_v_opa_l; auto. apply value_typing_invariant_gamma with Gamma';auto. 
  +++ subst.   apply T_config_ctns with (OpaqueLabeledTy T1) empty_context; auto.  
    case_eq (hole_free top); intro. 
++++  apply T_ctn_sequential_exec with (OpaqueLabeledTy T') top fs (OpaqueLabeledTy T2); auto. 
     apply T_v_opa_l; auto. apply value_typing_invariant_gamma with Gamma';auto. 
  ++++ apply H14 in H0. subst.  apply T_ctn_fs with (OpaqueLabeledTy T'); auto. 
    apply T_v_opa_l; auto. apply value_typing_invariant_gamma with Gamma';auto.

++ subst. inversion H12. 
+ subst. inversion H19. subst. inversion H18. subst. inversion H13. subst.  
    inversion H21. subst. 
    ++ apply T_config_nil.    inversion H17. 
    +++ subst.      remember ( (update_typing empty_context arg_id (classTy arguT))) as gamma0.
    case_eq (hole_free top); intro. 
    ++++  apply T_ctn_sequential_exec with (OpaqueLabeledTy T) top fs (OpaqueLabeledTy T3); auto. 
     apply T_v_opa_l; auto.     apply value_typing_invariant_gamma with gamma0;auto. 

  ++++ apply H15 in H0. subst.  apply T_ctn_fs with (OpaqueLabeledTy (classTy returnT)); auto. 
    apply T_v_opa_l; auto. 
      remember ( (update_typing empty_context arg_id (classTy arguT))) as gamma0.
    apply value_typing_invariant_gamma with gamma0;auto.

 +++ subst. inversion H24. 
++ subst.    apply T_config_ctns with (OpaqueLabeledTy T2) empty_context; auto.      inversion H17. 
    +++ subst.      remember ( (update_typing empty_context arg_id (classTy arguT))) as gamma0.
    case_eq (hole_free top); intro. 
    ++++  apply T_ctn_sequential_exec with (OpaqueLabeledTy T1) top fs (OpaqueLabeledTy T3); auto. 
     apply T_v_opa_l; auto.     apply value_typing_invariant_gamma with gamma0;auto. 

  ++++ apply H15 in H0. subst.  apply T_ctn_fs with (OpaqueLabeledTy (classTy returnT)); auto. 
    apply T_v_opa_l; auto. 
      remember ( (update_typing empty_context arg_id (classTy arguT))) as gamma0.
    apply value_typing_invariant_gamma with gamma0;auto.

 +++ subst. inversion H28.
Admitted. 




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

(* special terms *)
    | ObjId o =>  ObjId o
  (* runtime labeled date*)
    | v_l e lb => if (flow_to lb L_Label) then v_l (erasure_L_fun e) lb else v_l dot lb 
    | v_opa_l e lb => if (flow_to lb L_Label) then v_opa_l (erasure_L_fun e) lb else v_opa_l dot lb 
    | dot => dot
    | return_hole =>  (v_opa_l dot H_Label)
    | hole => hole
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

Fixpoint erasure_L_fs (fs : list tm) := 
  match fs with 
    | nil => nil
    | h1 :: t => erasure_L_fun h1 :: erasure_L_fs t
  end. 

Fixpoint erasure_fun (ct : Class_table) (ctn : container) (ctns_stack : list container) (h : heap) : config :=
match ctn with 
 | (Container t fs lb sf) =>
       if (flow_to lb L_Label) then (Config ct (Container (erasure_L_fun t) (erasure_L_fs fs) lb (fun x => (erasure_obj_null (sf x) h))) ctns_stack  h)
          else match ctns_stack with 
                | nil => (Config ct (Container dot nil lb empty_stack_frame) nil h) 
                | ctn :: ctns' => erasure_fun ct ctn ctns'  h
                end
end. 

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

Lemma join_label_commutative : forall l1 l2, 
    join_label l1 l2 = join_label l2 l1. 
Proof. Admitted. 

Lemma H_Label_not_flow_to_L : forall lb, 
   flow_to lb L_Label = false -> lb = H_Label.
Admitted. 

Lemma L_Label_flow_to_L : forall lb, 
   flow_to lb L_Label = true -> lb = L_Label.
Admitted. 

Lemma join_L_label_flow_to_L : forall lb1 lb2, 
  flow_to lb1 L_Label = true ->
  flow_to lb2 L_Label = true ->
  flow_to (join_label lb1 lb2) L_Label = true.
Admitted. 

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


Lemma extend_heap_preserve_erasure : forall h o h' cls F lb, 
  o = (get_fresh_oid h) ->
  h' =  add_heap_obj h o (Heap_OBJ cls F lb) ->
  flow_to lb L_Label = false ->
  erasure_heap h' = erasure_heap h.
Proof.
  intros h o h' cls F lb. 
  intro H_o. intro H_h'. intro H_flow. 
  induction h. 
  unfold erasure_heap. rewrite H_h'. unfold  add_heap_obj. rewrite H_flow. auto. 
  unfold add_heap_obj in H_h'. remember (a::h) as h0. unfold erasure_heap.
  rewrite H_h'. rewrite H_flow. fold  erasure_heap. auto. 
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

Lemma beq_oid_equal : forall o o0, 
      beq_oid o o0 = true -> o = o0. 
Admitted. 

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

      assert (lookup_heap_obj (update_heap_obj ((o0, Heap_OBJ c f l0) :: h) o (Heap_OBJ cls F' lb')) o1 = None).
      apply lookup_updated_heap_none; auto. 
      intro contra. rewrite contra in H0. rewrite <- H0 in H6. inversion H6. 
      unfold update_heap_obj in H7. rewrite H3 in H7. fold update_heap_obj in H7. rewrite H7. auto. 
        
      auto. 
      apply functional_extensionality in H5. rewrite H5. auto.  
Qed.


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

Inductive L_equivalence_store : stack_frame -> heap -> stack_frame -> heap -> Prop :=
  | L_equivalence_empty : forall h, 
      L_equivalence_store empty_stack_frame h empty_stack_frame h
  | L_equivalence_equal_store : forall sf h,
      L_equivalence_store sf h sf h
  | L_equivalence_store_L : forall sf1 sf2 h1 h2, 
      (forall x v1, sf1 x = Some v1 -> exists v2, sf2 x = Some v2 /\ L_equivalence_tm v1 h1 v2 h2) ->
      (forall x v2, sf2 x = Some v2 -> exists v1, sf1 x = Some v1 /\ L_equivalence_tm v1 h1 v2 h2) ->
      L_equivalence_store sf1 h1 sf2 h2. 

Inductive L_equivalence_config : config -> config -> Prop :=
  | L_equal_config : forall ct t fs lb sf ctns h, 
      L_equivalence_config (Config ct (Container t fs lb sf) ctns h)  (Config ct (Container t fs lb sf) ctns h)
  | L_equivalence_config_L : forall ct t1 fs1 lb1 lb2 sf1 t2 fs2 sf2 ctns1 ctns2 h1 h2, 
      flow_to lb1 L_Label = true ->
      flow_to lb2 L_Label = true ->
      L_equivalence_tm t1 h1 t2 h2->
      L_equivalence_store sf1 h1 sf2 h2 ->
      L_equivalence_config (Config ct (Container t1 fs1 lb1 sf1) ctns1 h1) (Config ct (Container t2 fs2 lb2 sf2) ctns2 h2)
  | L_equivalence_config_H : forall ct t1 fs1 lb1 sf1 t2 fs2 lb2 sf2 ctns1 ctns2 h1 h2, 
      flow_to lb1 L_Label = false ->
      flow_to lb2 L_Label = false ->
      L_equivalence_config (Config ct (Container t1 fs1 lb1 sf1) ctns1 h1) (Config ct (Container t2 fs2 lb2 sf2) ctns2 h2).  

Lemma L_equal_imply_erasure_object_equal : forall t1 t2, 
L_equivalence_tm t1 nil t2 nil -> 
erasure_obj_null (Some t1) nil = erasure_obj_null (Some t2) nil. 
Proof. intros t1 t2. intro Hy. 
induction t1; try (inversion Hy; subst; unfold erasure_obj_null; auto). 
Qed. 



Inductive L_equal_top_container : config -> config -> Prop :=
  | tm_sf_eq : forall ct   t1 fs1 lb1 sf1  t2 fs2 lb2 sf2 ctns_stack1 ctns_stack2 h1 h2, 
      t1 = t2 ->
      fs1 = fs2 ->  
      flow_to lb1 L_Label = flow_to lb2 L_Label ->
      L_equal_top_container (Config ct (Container t1 fs1 lb1 sf1) ctns_stack1 h1)
           (Config ct (Container t2 fs2 lb2 sf2) ctns_stack2 h2).

Hint Constructors L_equal_top_container.

Lemma same_container_L_equal : forall ctn ctns ct h, 
  L_equal_top_container (Config ct ctn ctns h) (Config ct ctn ctns h). 
Proof with eauto. intros. destruct ctn.  apply tm_sf_eq; auto.  Qed.  


Lemma erasure_target : forall ctn ct ctns h, 
  exists ctn' ctns' h',  (erasure_fun ct ctn ctns h) = Config ct ctn' ctns' h'. 
Proof.  intros. generalize dependent ctn.
 induction ctns. destruct ctn. case_eq ( flow_to l0 L_Label); intro.
unfold erasure_fun. rewrite H. exists (Container (erasure_L_fun t) (erasure_L_fs f) l0
       (fun x : id => erasure_obj_null (s x) h)). exists nil. exists h. auto. 
unfold erasure_fun. rewrite H. exists (Container dot nil l0 empty_stack_frame). exists nil. exists h. auto. 
destruct ctn. case_eq ( flow_to l0 L_Label); intro; unfold erasure_fun; rewrite H. 
exists (Container (erasure_L_fun t) (erasure_L_fs f) l0
       (fun x : id => erasure_obj_null (s x) h)). exists (a :: ctns). exists h. auto. 
fold erasure_fun. apply IHctns.
Qed. 


Lemma erasure_same_container_equal : forall ctn ctns ct h, 
  L_equal_top_container (erasure_fun ct ctn ctns h)
  (erasure_fun ct ctn ctns h).
Proof. intros. pose proof (erasure_target ctn ct ctns h). destruct H as [ctn']. destruct H as [ctns'].
destruct H as [h']. rewrite H. destruct ctn'. apply tm_sf_eq; auto.  
Qed. 

Lemma erasure_same_tms_equal : forall ctn ctns ct h h', 
  L_equal_top_container (erasure_fun ct ctn ctns h)
  (erasure_fun ct ctn ctns h').
Proof. intros. generalize dependent ctn.
induction ctns. destruct ctn. case_eq ( flow_to l0 L_Label); intro.
unfold erasure_fun. rewrite H. auto. unfold erasure_fun. rewrite H. auto. 
intro ctn. destruct ctn. case_eq ( flow_to l0 L_Label); intro;
unfold erasure_fun; rewrite H; auto.
Qed. 


Lemma simulation_H : forall ct t1 fs1 lb1 sf1 ctns_stack1 h1  t2 fs2 lb2 sf2 ctns_stack2 h2, 
      valid_syntax t1 ->
      forall T, tm_has_type ct empty_context h1 t1 T -> 
      field_wfe_heap ct h1 -> wfe_heap ct h1 ->         
      wfe_stack_frame ct h1 sf1 ->
      flow_to lb1 L_Label = false ->
     Config ct (Container t1 fs1 lb1 sf1) ctns_stack1 h1 
      ==> Config ct (Container t2 fs2 lb2 sf2) ctns_stack2 h2 ->
      L_equal_top_container (erasure_fun ct (Container t1 fs1 lb1 sf1) ctns_stack1 h1)
      (erasure_fun ct (Container t2 fs2 lb2 sf2) ctns_stack2 h2).
Proof with eauto. intros ct t1 fs1 lb1 sf1 ctns_stack1 h1  t2 fs2 lb2 sf2 ctns_stack2 h2.
     intro H_valid_syntx. intro T. intro H_typing.  intro H_wfe_field. intro H_wfe_heap. 
     intro H_wfe_sf.  intro H_flow. intro H_reduction. 
     remember (Config ct (Container t1 fs1 lb1 sf1) ctns_stack1 h1) as config1. 
     remember (Config ct (Container t2 fs2 lb2 sf2) ctns_stack2 h2) as config2.
     generalize dependent t1. generalize dependent fs1. generalize dependent lb1. 
     generalize dependent ctns_stack1. generalize dependent h1. 

     generalize dependent t2. generalize dependent fs2. generalize dependent lb2. 
     generalize dependent ctns_stack2. generalize dependent h2. 
     generalize dependent T. generalize dependent sf1. generalize dependent sf2. 

induction H_reduction; intros; auto; inversion Heqconfig1; inversion Heqconfig2; subst; auto; try (rename lb2 into lb1);
case_eq (flow_to lb1 L_Label); try (intro H_lb1_true; rewrite H_flow in H_lb1_true; inversion H_lb1_true);
try (induction ctns_stack2; unfold erasure_fun; rewrite H_flow; auto); fold erasure_fun; 
try (apply same_container_L_equal; auto); auto; try (apply erasure_same_container_equal; auto). 

- assert (flow_to (join_label lo lb1) L_Label = false).  apply flow_join_label with lb1 lo; auto. rewrite H1.
apply tm_sf_eq; auto.  rewrite H1. rewrite H_flow. auto. 
- assert (flow_to (join_label lo lb1) L_Label = false).  apply flow_join_label with lb1 lo; auto. rewrite H1.
apply erasure_same_container_equal. 

- unfold erasure_fun. fold erasure_fun. 
rewrite H_flow. destruct ctns_stack1; unfold erasure_fun; fold erasure_fun; rewrite H_flow.
apply same_container_L_equal.
apply erasure_same_container_equal.

- assert (flow_to (join_label lb1 lx) L_Label = false).  apply flow_join_label with lb1 lx. auto. 
  apply join_label_commutative; auto. 
destruct ctns_stack1; unfold erasure_fun; fold erasure_fun; rewrite H_flow; rewrite H0. 
apply same_container_L_equal.
apply erasure_same_container_equal.

- destruct a. case_eq (flow_to l0 L_Label); intro.   destruct ctns_stack2; unfold erasure_fun; fold erasure_fun; rewrite H0;
   apply tm_sf_eq; auto. apply erasure_same_tms_equal. 

- assert (flow_to (join_label lb1 lo) L_Label = false).  apply flow_join_label with lb1 lo. auto. 
  apply join_label_commutative; auto.  rewrite H. apply tm_sf_eq; auto. rewrite H_flow. auto. 

- assert (flow_to (join_label lb1 lo) L_Label = false).  apply flow_join_label with lb1 lo. auto. 
  apply join_label_commutative; auto.  rewrite H. apply erasure_same_container_equal. 

- assert (flow_to (join_label lb1 lo) L_Label = false).  apply flow_join_label with lb1 lo. auto. 
  apply join_label_commutative; auto.  rewrite H. apply tm_sf_eq; auto. rewrite H_flow. auto.

 - assert (flow_to (join_label lb1 lo) L_Label = false).  apply flow_join_label with lb1 lo. auto. 
  apply join_label_commutative; auto.  rewrite H. apply erasure_same_container_equal. 

- apply erasure_same_tms_equal. 

- case_eq (flow_to lb2 L_Label); intro. unfold erasure_L_fun. fold erasure_L_fun. rewrite H_flow. auto.
apply H_Label_not_flow_to_L in H_flow. rewrite H_flow. auto.  auto. 

- case_eq (flow_to lb2 L_Label); intro. unfold erasure_L_fun. fold erasure_L_fun. rewrite H_flow. auto.
apply H_Label_not_flow_to_L in H_flow. rewrite H_flow. auto.  apply erasure_same_container_equal. 
Qed.


Lemma lookup_heap_obj_two_cases : forall h o, 
  ((exists cls F lb, lookup_heap_obj h o = Some (Heap_OBJ cls F lb) ) 
      \/ (lookup_heap_obj h o = None)).
  Proof.   intro h0. induction h0.  right. unfold lookup_heap_obj. auto. 
    intro o0. induction a. case_eq ( beq_oid o0 o). unfold lookup_heap_obj.  intro. unfold lookup_heap_obj. rewrite H.
    rename h into ho. induction ho.     left. exists c. exists f. exists l0. auto. 
    intro. unfold lookup_heap_obj. rewrite H. fold lookup_heap_obj. apply IHh0.
Qed. 

Reserved Notation "c '==l>' c'"
  (at level 40, c' at level 39).

Definition erasure (c : config ) : config :=
  match c with 
    | (Config ct ctn ctns_stack h) => erasure_fun ct ctn ctns_stack h
    | Error_state => Error_state
    | Terminal => Terminal
  end. 

Inductive l_reduction : config -> config -> Prop :=
    | L_reduction : forall c1 c2 c2_r, 
      c1 ==> c2 ->
      erasure  c2 = c2_r ->
      l_reduction c1 c2_r
where "c '==l>' c'" := (l_reduction c c').

Inductive multi_step_reduction : config -> config -> Prop := 
  | multi_reduction_refl : forall config , multi_step_reduction config config
  | multi_reduction_step : forall c1 c2 c3, 
                    reduction c1 c2 ->
                    multi_step_reduction c2 c3 ->
                    multi_step_reduction c1 c3.

Notation "c1 '==>*' c2" := (multi_step_reduction c1 c2) (at level 40).

Inductive multi_step_l_reduction : config -> config -> Prop := 
  | multi_reduction_l_refl : forall config , multi_step_l_reduction config config
  | multi_reduction_l_step : forall c1 c2 c3, 
                    l_reduction c1 c2 ->
                    multi_step_l_reduction c2 c3 ->
                    multi_step_l_reduction c1 c3.

Notation "c1 '==>L*' c2" := (multi_step_l_reduction c1 c2) (at level 40).



Theorem L_reduction_determinacy: forall c c1 c2, 
     l_reduction c c1 ->
     l_reduction c c2 -> 
      c1 = c2.
Proof. Admitted.

Lemma ct_consist : forall ct ctn ctns h ct' ctn' ctns' h', 
  (Config ct ctn ctns h) ==> (Config ct' ctn' ctns' h') -> ct = ct'. 
 Proof.
   intros. remember (Config ct ctn ctns h) as config. 
remember (Config ct' ctn' ctns' h') as config'.  
 induction H; inversion Heqconfig; inversion Heqconfig';  subst; auto.
  Qed. 

Lemma ct_erasure : forall ct ctn ctns h ct' ctn' ctns' h', 
  erasure (Config ct ctn ctns h)  = (Config ct' ctn' ctns' h') -> ct = ct'. 
Proof. intros ct ctn ctns h ct' ctn' ctns' h'. 
  unfold erasure. intro Hy. 
  pose proof (erasure_target ctn ct ctns h). destruct H as [ctn0].
  destruct H as [ctns0]. destruct H as [h0]. rewrite Hy in H. inversion H. auto. 
Qed. 

Lemma l_reduction_ct_consist : forall ct ctn ctns h ct' ctn' ctns' h', 
  (Config ct ctn ctns h) ==l> (Config ct' ctn' ctns' h') -> ct = ct'. 
 Proof.
   intros. inversion H. subst. induction c2. assert (ct = c).
   apply ct_consist with ctn ctns h c0 l0 h0; auto.  subst. apply ct_erasure with c0 l0 h0 ctn' ctns' h'; auto. 
    inversion H1. inversion H1. 
  Qed.  

Theorem L_reduction_multistep_determinacy: forall ct ctn ctns h v1 lb1 sf1 h1 v2 lb2 sf2 h2, 
      (Config ct ctn ctns h) ==>L* (Config ct (Container v1 nil lb1 sf1) nil h1) ->
      (Config ct ctn ctns h) ==>L* (Config ct (Container v2 nil lb2 sf2) nil h2)  -> 
     value v1 -> value v2 ->
      (Config ct (Container v1 nil lb1 sf1) nil h1) = (Config ct (Container v2 nil lb2 sf2) nil h2). 
Proof.
  intros ct ctn ctns h v1 lb1 sf1 h1 v2 lb2 sf2 h2.
  intro Hy1.   intro Hy2. 
  intro Hv1. intro Hv2.  
  remember (Config ct (Container v1 nil lb1 sf1) nil h1) as v1_config. 
  remember (Config ct ctn ctns h) as config. 
  generalize dependent v1.      generalize dependent v2.
  generalize dependent lb1.      generalize dependent lb2.
  generalize dependent sf1.      generalize dependent sf2.
  generalize dependent h1.      generalize dependent h2.
  generalize dependent h.  generalize dependent ctn.      generalize dependent ctns.
  induction Hy1.
  - intros. subst. inversion Heqv1_config. subst. 
    inversion Hy2. auto. inversion H. subst. 
inversion Hv1; subst; inversion H3; subst; inversion H0; try ( inversion H1; inversion H6; fail);
try (inversion H2; inversion H7).
- intros. subst.  inversion Hy2. subst. inversion H.  subst. inversion Hv2; subst; inversion H0; subst;
try (inversion Hy1; inversion H1; inversion H5; fail); try (inversion Hy1; inversion H2; inversion H6; fail).
  subst.  induction c2.  induction c0. 
  assert (ct = c). apply l_reduction_ct_consist with ctn ctns h c1 l0 h0. auto. 
  assert (ct = c0). apply l_reduction_ct_consist with ctn ctns h c2 l1 h3. auto.
  subst. assert (Config c0 c1 l0 h0 = Config c0 c2 l1 h3). 
  apply L_reduction_determinacy with (Config c0 ctn ctns h); auto. 
  rewrite <- H2 in H1. apply IHHy1 with l0 c1 h0 h1 sf1 lb1 v1; auto.
   inversion H1. inversion H2. inversion H6.  
 inversion H1. inversion H2. inversion H6.  
 inversion Hy1. inversion H2. inversion H6. 
 inversion Hy1. inversion H2. inversion H6.
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

Lemma multi_erasure_L_fs_equal : forall fs, 
   erasure_L_fs (erasure_L_fs fs) = (erasure_L_fs fs).
  Proof. induction fs.
  - auto. 
  - unfold erasure_L_fs. fold erasure_L_fs.  pose proof (multi_erasure_L_tm_equal a ).
  rewrite H. rewrite IHfs. auto. Qed. 


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

Lemma field_value : forall h o cls F lb f t' CT cls',  
wfe_heap CT h -> field_wfe_heap CT h ->
Some (Heap_OBJ cls F lb) = lookup_heap_obj h o ->
F f = Some t' ->
tm_has_type CT empty_context h (FieldAccess (ObjId o) f)
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

Lemma erasure_L_fun_value : forall t, 
  value t -> value (erasure_L_fun t). 
Proof. intros.  induction t; auto; inversion H. 
- unfold erasure_L_fun. fold erasure_L_fun.  case_eq ( flow_to l0 L_Label); intro. 
   apply IHt in H1. auto. auto.
- unfold erasure_L_fun. fold erasure_L_fun.  case_eq ( flow_to l0 L_Label); intro. 
   apply IHt in H1. auto. auto.
Qed. 
  

Lemma erasure_L_fun_not_value  : forall t T h ct, 
tm_has_type ct empty_context h t T -> 
t <> return_hole ->
~ value t -> ~ value (erasure_L_fun t).
Proof. intros. induction t; auto; try (unfold erasure_L_fun; fold erasure_L_fun; intro contra; inversion contra; fail). 
  - inversion H. subst. assert (value (v_l t l0)). auto. intuition.
  - inversion H. subst. assert (value (v_opa_l t l0)). auto. intuition.
Qed. 


Lemma simulation_L : forall ct t1 fs1 lb1 sf1 ctns_stack1 h1  t2 fs2 lb2 sf2 ctns_stack2 h2, 
      valid_config (Config ct (Container t1 fs1 lb1 sf1) ctns_stack1 h1 ) ->
      forall T, tm_has_type ct empty_context h1 t1 T -> 
      field_wfe_heap ct h1 -> wfe_heap ct h1 ->         
      wfe_stack_frame ct h1 sf1 ->
      flow_to lb1 L_Label = true ->
     Config ct (Container t1 fs1 lb1 sf1) ctns_stack1 h1 
      ==> Config ct (Container t2 fs2 lb2 sf2) ctns_stack2 h2 ->
l_reduction (erasure_fun ct (Container t1 fs1 lb1 sf1) ctns_stack1 h1)
      (erasure_fun ct (Container t2 fs2 lb2 sf2) ctns_stack2 h2). 
Admitted. 



Lemma multi_step_simulation : forall ct t1 fs1 lb1 sf1 ctns_stack1 h1  t2 fs2 lb2 sf2 ctns_stack2 h2, 
      valid_syntax t1 ->
      forall T, tm_has_type ct empty_context h1 t1 T -> 
      field_wfe_heap ct h1 -> wfe_heap ct h1 ->         
      wfe_stack_frame ct h1 sf1 ->
     Config ct (Container t1 fs1 lb1 sf1) ctns_stack1 h1 
      ==>* Config ct (Container t2 fs2 lb2 sf2) ctns_stack2 h2 ->
      erasure_fun ct (Container t1 fs1 lb1 sf1) ctns_stack1 h1  ==>L*
      erasure_fun ct (Container t2 fs2 lb2 sf2) ctns_stack2 h2.
Proof. Admitted.


Lemma erasure_equal_input : forall ct sf sf' t fs lb, 
      L_equivalence_store sf nil sf' nil ->
      erasure (Config ct (Container t fs lb sf) nil nil) = 
      erasure (Config ct (Container t fs lb sf') nil nil).
Proof. intros ct sf sf' t fs lb. intro Hy. 
    unfold erasure. unfold erasure_fun.  case_eq (flow_to lb L_Label). intro.
 
    inversion Hy. subst. auto.  subst. auto. subst.  
    assert (forall a, (fun x : id => erasure_obj_null (sf x) nil) a = (fun x : id => erasure_obj_null (sf' x) nil) a).
    intro x. remember (sf x) as option_t. induction option_t. destruct H0 with x a; auto. 
    destruct H2. rewrite H2. 
    apply L_equal_imply_erasure_object_equal in H3. auto. 
    remember  (sf' x) as option_t'.  induction option_t'. destruct H1 with x a; auto. destruct H2. 
    rewrite H2 in Heqoption_t. inversion Heqoption_t. auto. 
    apply functional_extensionality in H2. rewrite H2. auto. auto .
Qed.  

Lemma Non_interference : forall ct x t fs lb sf sf' lb1 sf1  lb2 sf2 v1 v2 final_v1 final_v2 h1 h2, 
      valid_syntax t ->
      field_wfe_heap ct nil -> wfe_heap ct nil ->         
      wfe_stack_frame ct nil sf ->
      field_wfe_heap ct nil -> wfe_heap ct nil ->         
      wfe_stack_frame ct nil sf' ->
      L_equivalence_store sf nil sf' nil -> 
      sf x = Some (v_l v1 H_Label) ->
      sf' x = Some (v_l v2 H_Label) ->
     Config ct (Container t fs lb sf) nil nil
      ==>* Config ct (Container final_v1 nil lb1 sf1) nil h1 ->
     Config ct (Container t fs lb sf') nil nil 
      ==>* Config ct (Container final_v2 nil lb2 sf2) nil h2 ->
      value final_v1 -> value final_v2 ->
      forall T, tm_has_type ct empty_context nil t T->
      L_equivalence_config (Config ct (Container final_v1 nil lb1 sf1) nil h1) (Config ct (Container final_v2 nil lb2 sf2) nil h2).
Proof. 
intros  ct x t fs lb sf sf' lb1 sf1  lb2 sf2 v1 v2 final_v1 final_v2 h1 h2.
    intro H_valid_syntax.
    intro H_wfe_field. intro H_wfe_heap. intro H_wfe_frame. 
    intro H_wfe_field'. intro H_wfe_heap'. intro H_wfe_frame'. intro H_equal_input. 
    intro H_sf1. intro H_sf2.  intro H_execution1.  intro H_execution2. intro H_final_v1. intro H_final_v2.
    intro T. intro H_typing.
    remember (erasure (Config ct (Container t fs lb sf) nil nil)) as config_r.
    remember (erasure (Config ct (Container t fs lb sf') nil nil)) as config_r'.

    assert  (config_r = config_r'). subst. 
    apply erasure_equal_input. auto. subst.  

    assert ( (erasure (Config ct (Container t fs lb sf) nil nil))  ==>L* (erasure (Config ct (Container final_v1 nil lb1 sf1) nil h1) ) ).
    apply multi_step_simulation with T; auto.  

    assert ( (erasure (Config ct (Container t fs lb sf') nil nil))  ==>L* (erasure (Config ct (Container final_v2 nil lb2 sf2) nil h2) ) ).
    apply multi_step_simulation with T; auto.  


   assert ((erasure (Config ct (Container final_v1 nil lb1 sf1) nil h1) ) =
       (erasure (Config ct (Container final_v2 nil lb2 sf2) nil h2) ) ).
   (*apply L_reduction_multistep_determinacy.*) admit.

   unfold erasure in H2. unfold erasure_fun in H2. 
    case_eq (flow_to lb1 L_Label). intro. rewrite H3 in H2. 
    case_eq (flow_to lb2 L_Label). intro. rewrite H4 in H2. 
    apply L_equivalence_config_L; auto.  admit. admit. 

    intro. rewrite H4 in H2. inversion H2. rewrite H7 in H3. rewrite H3 in H4. inversion H4. 

    intro.  rewrite H3 in H2. 
    case_eq (flow_to lb2 L_Label). intro. rewrite H4 in H2.  inversion H2. 
    rewrite H7 in H3. rewrite H3 in H4. inversion H4. 

    intro. rewrite H4 in H2. apply L_equivalence_config_H; auto.

Qed. 



-------------------------------------------------------------------



Lemma field_access_erasure_L_fun_pop : forall t2 fs1 lb2 sf2 ctns_stack h2 f ct , 
  flow_to lb2 L_Label = true ->
 (~ value (erasure_L_fun t2)) ->
  erasure_fun ct (Container (FieldAccess t2 f) fs1 lb2 sf2) ctns_stack h2 ==l>
  erasure_fun ct (Container t2 (FieldAccess hole f :: fs1) lb2 sf2) ctns_stack h2.
Proof with eauto. intros t2 fs1 lb2 sf2 ctns_stack h2 f ct. intro H_flow. intro Hy. 
remember ctns_stack as ctns. 
assert (erasure_L_fun (FieldAccess hole f) = (FieldAccess hole f)).
unfold erasure_L_fun. fold erasure_L_fun. auto. 
 pose proof (multi_erasure_heap_equal h2) as H_h.  
  pose proof (multi_erasure_L_tm_equal t2) as Ht2. 
  assert (erasure_fun ct (Container (FieldAccess t2 f) fs1 lb2 sf2) ctns h2 ==>
    Config ct
    (Container (erasure_L_fun t2) (erasure_L_fs  (FieldAccess hole f :: fs1)) lb2
       (fun x : id => erasure_obj_null (sf2 x) h2)) ctns (h2) ).
destruct ctns;  try (induction c); unfold erasure; unfold erasure_fun; 
induction fs1; unfold erasure_L_fs; fold erasure_L_fs; rewrite H_flow; rewrite H; 
 try (eauto using reduction).


  assert ( erasure ( Config ct
       (Container (erasure_L_fun t2) (erasure_L_fs (FieldAccess hole f :: fs1)) lb2
          (fun x : id => erasure_obj_null (sf2 x) h2)) ctns_stack (h2)) =
    erasure_fun ct (Container t2 (FieldAccess hole f :: fs1) lb2 sf2) ctns h2).
  rewrite <- Heqctns. 
  assert (forall a, (fun x : id =>
        erasure_obj_null (erasure_obj_null (sf2 x) h2) (erasure_heap h2)) a = 
         (fun x : id => erasure_obj_null (sf2 x) h2) a ). 
  intro a. apply erasure_obj_null_equal_erasure_h. 
  apply functional_extensionality in H1. 

destruct ctns;  try (induction c); unfold erasure; unfold erasure_fun; 
induction fs1; unfold erasure_L_fs; fold erasure_L_fs; rewrite H_flow;rewrite H1; rewrite H; rewrite H;  
  rewrite H_h;rewrite Ht2; try ( pose proof (multi_erasure_L_tm_equal a) as Ha; rewrite Ha;
  pose proof (multi_erasure_L_fs_equal fs1) as Hfs1; rewrite Hfs1
);auto. 
  rewrite <- Heqctns in H1. 
  apply L_reduction with (Config ct
       (Container (erasure_L_fun t2)
          (erasure_L_fs (FieldAccess hole f :: fs1)) lb2
          (fun x : id => erasure_obj_null (sf2 x) h2)) ctns (erasure_heap h2)); auto.
Qed.  

Lemma field_access_erasure_L_fun_push : forall t1 fs lb sf ctns_stack h f ct , 
  flow_to lb L_Label = true ->
 (value t1) ->
erasure_fun ct (Container t1 (FieldAccess hole f :: fs) lb sf) ctns_stack h ==l>
erasure_fun ct (Container (FieldAccess t1 f) fs lb sf) ctns_stack h.
Proof with eauto. intros t1 fs lb sf ctns_stack h f ct. intro H_flow. intro Hv. 
remember ctns_stack as ctns. 
assert (erasure_L_fun (FieldAccess hole f) = (FieldAccess hole f)).
unfold erasure_L_fun. fold erasure_L_fun. auto. 
 pose  proof (erasure_L_fun_value t1 Hv).
 pose proof (multi_erasure_heap_equal h) as H_h.  
  pose proof (multi_erasure_L_tm_equal t1) as Ht1. 
assert (forall a, (fun x : id =>
        erasure_obj_null (erasure_obj_null (sf x) h) (erasure_heap h)) a = 
         (fun x : id => erasure_obj_null (sf x) h) a ). 
  intro a. apply erasure_obj_null_equal_erasure_h. 
  apply functional_extensionality in H1. 

  assert (erasure_fun ct (Container t1 (FieldAccess hole f :: fs) lb sf) ctns h ==>
    Config ct
    (Container (FieldAccess (erasure_L_fun t1) f) (erasure_L_fs fs) lb
       (fun x : id => erasure_obj_null (sf x) h)) ctns (erasure_heap h) ).
destruct ctns;  try (induction c); unfold erasure; unfold erasure_fun; 
induction fs; unfold erasure_L_fs; fold erasure_L_fs; rewrite H_flow; rewrite H; 
 try (eauto using reduction).

  assert ( erasure ( Config ct
    (Container (FieldAccess (erasure_L_fun t1) f) (erasure_L_fs fs) lb
       (fun x : id => erasure_obj_null (sf x) h)) ctns (erasure_heap h)  ) =
    erasure_fun ct (Container (FieldAccess t1 f) fs lb sf) ctns h).

destruct ctns;  try (induction c); unfold erasure; unfold erasure_fun; 
induction fs; unfold erasure_L_fs; fold erasure_L_fs; rewrite H_flow;
rewrite H1; rewrite H_h; unfold erasure_L_fun; fold erasure_L_fun; rewrite Ht1;  auto;
  try ( pose proof (multi_erasure_L_tm_equal a) as Ha; rewrite Ha;
   pose proof (multi_erasure_L_fs_equal fs) as Hfs; rewrite Hfs);auto. 

  apply L_reduction with (Config ct
       (Container (FieldAccess (erasure_L_fun t1) f) (erasure_L_fs fs) lb
          (fun x : id => erasure_obj_null (sf x) h)) ctns (erasure_heap h)); auto.
Qed. 

Lemma method_call_erasure_L_fun_pop1 : forall t2 fs1 lb2 sf2 ctns_stack h2 ct e2 meth, 
  flow_to lb2 L_Label = true ->
 (~ value (erasure_L_fun t2)) ->
erasure_fun ct (Container (MethodCall t2 meth e2) fs1 lb2 sf2) ctns_stack h2 ==l>
erasure_fun ct (Container t2 (MethodCall hole meth e2 :: fs1) lb2 sf2) ctns_stack h2.
Proof with eauto. intros  t2 fs1 lb2 sf2 ctns_stack h2 ct e2 meth. intro H_flow. intro Hy. 
remember ctns_stack as ctns. 
 pose proof (multi_erasure_heap_equal h2) as H_h.  
  pose proof (multi_erasure_L_tm_equal t2) as Ht2. 
  assert (erasure_fun ct (Container (MethodCall t2 meth e2) fs1 lb2 sf2) ctns h2 ==>
    Config ct
    (Container (erasure_L_fun t2) ((MethodCall hole meth (erasure_L_fun e2)) :: (erasure_L_fs fs1)) lb2
       (fun x : id => erasure_obj_null (sf2 x) h2)) ctns (erasure_heap h2) ).
destruct ctns;  try (induction c); unfold erasure; unfold erasure_fun; 
induction fs1; unfold erasure_L_fs; fold erasure_L_fs; rewrite H_flow; 
 unfold erasure_L_fun; fold erasure_L_fun;
 try (eauto using reduction).

  assert (erasure_fun
     ct
      (Container (erasure_L_fun t2)
         (MethodCall hole meth (erasure_L_fun e2) :: erasure_L_fs fs1) lb2
         (fun x : id => erasure_obj_null (sf2 x) h2)) ctns (erasure_heap h2) =
         erasure_fun ct (Container t2 (MethodCall hole meth e2 :: fs1) lb2 sf2) ctns  h2).
  assert (forall a, (fun x : id =>
        erasure_obj_null (erasure_obj_null (sf2 x) h2) (erasure_heap h2)) a = 
         (fun x : id => erasure_obj_null (sf2 x) h2) a ). 
  intro a. apply erasure_obj_null_equal_erasure_h. 
  apply functional_extensionality in H0. 

 pose proof (multi_erasure_L_tm_equal e2) as He2. 
destruct ctns;  try (induction c); unfold erasure; unfold erasure_fun; 
induction fs1; unfold erasure_L_fs; fold erasure_L_fs; rewrite H_flow; 
try (unfold erasure_L_fun; fold erasure_L_fun);
try( rewrite H0);  try (rewrite He2);
  try (rewrite H_h); try (rewrite Ht2); try ( pose proof (multi_erasure_L_tm_equal a) as Ha; rewrite Ha;
  pose proof (multi_erasure_L_fs_equal fs1) as Hfs1; rewrite Hfs1
);auto. 
  apply L_reduction with (Config ct
      (Container (erasure_L_fun t2)
         (MethodCall hole meth (erasure_L_fun e2) :: erasure_L_fs fs1) lb2
         (fun x : id => erasure_obj_null (sf2 x) h2)) ctns (erasure_heap h2)); auto.
Qed.

Lemma method_call_erasure_L_fun_push1 : forall v fs1 lb2 sf2 ctns_stack h2 ct e2 meth, 
  flow_to lb2 L_Label = true ->
 (value v) ->
erasure_fun ct (Container v ((MethodCall hole meth e2) :: fs1) lb2 sf2) ctns_stack h2 ==l>
erasure_fun ct (Container (MethodCall v meth e2) fs1 lb2 sf2) ctns_stack h2.
Proof with eauto. intros v fs1 lb2 sf2 ctns_stack h2 ct e2 meth. intro H_flow. intro Hv. 
remember ctns_stack as ctns. 
 pose  proof (erasure_L_fun_value v Hv).
 pose proof (multi_erasure_heap_equal h2) as H_h.  
  pose proof (multi_erasure_L_tm_equal v) as H_m_v.
  pose proof (multi_erasure_L_tm_equal e2) as He2. 
assert (forall a, (fun x : id =>
        erasure_obj_null (erasure_obj_null (sf2 x) h2) (erasure_heap h2)) a = 
         (fun x : id => erasure_obj_null (sf2 x) h2) a ). 
  intro a. apply erasure_obj_null_equal_erasure_h. 
  apply functional_extensionality in H0. 

  assert (erasure_fun ct (Container v ((MethodCall hole meth e2) :: fs1) lb2 sf2) ctns h2 ==>
    Config ct
    (Container (MethodCall (erasure_L_fun v) meth (erasure_L_fun e2)) (erasure_L_fs fs1) lb2
       (fun x : id => erasure_obj_null (sf2 x) h2)) ctns (erasure_heap h2) ).
destruct ctns;  try (induction c); unfold erasure; unfold erasure_fun; 
induction fs1; unfold erasure_L_fs; fold erasure_L_fs; rewrite H_flow; 
unfold erasure_L_fun; fold erasure_L_fun;
 try (eauto using reduction).

  assert( erasure ( Config ct
       (Container (MethodCall (erasure_L_fun v) meth (erasure_L_fun e2))
          (erasure_L_fs fs1) lb2 (fun x : id => erasure_obj_null (sf2 x) h2))
       ctns (erasure_heap h2)) =
    erasure_fun ct (Container (MethodCall v meth e2) fs1 lb2 sf2) ctns h2).

destruct ctns;  try (induction c); unfold erasure; unfold erasure_fun; 
induction fs1; unfold erasure_L_fs; fold erasure_L_fs; rewrite H_flow;
try (unfold erasure_L_fun; fold erasure_L_fun);
 try (rewrite He2); try (rewrite H_m_v);

  try (rewrite H_h); try (rewrite H0); try (rewrite Ht2); try ( pose proof (multi_erasure_L_tm_equal a) as Ha; rewrite Ha;
  pose proof (multi_erasure_L_fs_equal fs1) as Hfs1; rewrite Hfs1
);auto. 

  apply L_reduction with (( Config ct
       (Container (MethodCall (erasure_L_fun v) meth (erasure_L_fun e2))
          (erasure_L_fs fs1) lb2 (fun x : id => erasure_obj_null (sf2 x) h2))
       ctns (erasure_heap h2))); auto.
Qed. 

Lemma method_call_erasure_L_fun_push2 : forall v1 t1 fs1 lb2 sf2 ctns_stack h2 ct meth, 
  flow_to lb2 L_Label = true ->
 (value t1) -> (value v1) ->
erasure_fun ct (Container t1 ((MethodCall v1 meth hole) :: fs1) lb2 sf2) ctns_stack h2 ==l>
erasure_fun ct (Container (MethodCall v1 meth t1) fs1 lb2 sf2) ctns_stack h2.
Proof with eauto. intros v1 t1 fs1 lb2 sf2 ctns_stack h2 ct meth.  intro H_flow. intro Hv_t1.
intro Hv_v1.  
remember ctns_stack as ctns. 
 pose  proof (erasure_L_fun_value v1 Hv_v1).
 pose  proof (erasure_L_fun_value t1 Hv_t1).
 pose proof (multi_erasure_heap_equal h2) as H_h.  
  pose proof (multi_erasure_L_tm_equal v1) as H_m_v1.
  pose proof (multi_erasure_L_tm_equal t1) as H_m_t1.

assert (forall a, (fun x : id =>
        erasure_obj_null (erasure_obj_null (sf2 x) h2) (erasure_heap h2)) a = 
         (fun x : id => erasure_obj_null (sf2 x) h2) a ). 
  intro a. apply erasure_obj_null_equal_erasure_h. 
  apply functional_extensionality in H1. 

  assert (erasure_fun ct (Container t1 (MethodCall v1 meth hole :: fs1) lb2 sf2) ctns h2 ==>
    Config ct
    (Container (MethodCall (erasure_L_fun v1) meth (erasure_L_fun t1)) (erasure_L_fs fs1) lb2
       (fun x : id => erasure_obj_null (sf2 x) h2)) ctns (erasure_heap h2) ).
destruct ctns;  try (induction c); unfold erasure; unfold erasure_fun; 
induction fs1; unfold erasure_L_fs; fold erasure_L_fs; rewrite H_flow; 
unfold erasure_L_fun; fold erasure_L_fun;
 try (eauto using reduction).

  assert( erasure_fun ct
      (Container (MethodCall (erasure_L_fun v1) meth (erasure_L_fun t1))
          (erasure_L_fs fs1) lb2 (fun x : id => erasure_obj_null (sf2 x) h2))
       ctns (erasure_heap h2) =
    erasure_fun ct (Container (MethodCall v1 meth t1) fs1 lb2 sf2) ctns h2).

destruct ctns;  try (induction c); unfold erasure; unfold erasure_fun; 
induction fs1; unfold erasure_L_fs; fold erasure_L_fs; rewrite H_flow;
try (unfold erasure_L_fun; fold erasure_L_fun);
 try (rewrite He2); try (rewrite H_m_v1); try (rewrite H_m_t1);
  try (rewrite H_h); try (rewrite H1); try (rewrite Ht2); try ( pose proof (multi_erasure_L_tm_equal a) as Ha; rewrite Ha;
  pose proof (multi_erasure_L_fs_equal fs1) as Hfs1; rewrite Hfs1
);auto. 

  apply L_reduction with (Config ct
       (Container (MethodCall (erasure_L_fun v1) meth (erasure_L_fun t1))
          (erasure_L_fs fs1) lb2 (fun x : id => erasure_obj_null (sf2 x) h2))
       ctns (erasure_heap h2)); auto.
Qed. 


Inductive exp_with_hole : tm -> Prop := 
| Hole_field_access : forall f, 
    exp_with_hole (FieldAccess hole f)
| Hole_methodcall1 : forall e meth, 
    exp_with_hole (MethodCall e meth hole)
| Hole_methodcall2 : forall argu meth, 
    exp_with_hole (MethodCall hole meth argu)
| Hole_labelData : forall lb, 
    exp_with_hole (labelData hole lb)
| Hole_unlabel : 
    exp_with_hole (unlabel hole)
| Hole_labelOf :
    exp_with_hole (labelOf hole)
| Hole_unlabelOpaque :
    exp_with_hole (unlabelOpaque hole)
| Hole_Assignment : forall x,
    exp_with_hole ((Assignment x hole))
| Hole_FieldWrite1 : forall e f, 
    exp_with_hole ((FieldWrite hole f e))
| Hole_FieldWrite2 : forall x f, 
    exp_with_hole ((FieldWrite x f hole)).

Lemma fs_pro_double : forall (t1 : tm) (t2 : tm) (fs : list tm),
  t1 :: t2 :: fs <> fs.
Proof. intros t1 t2 fs.  generalize dependent t1. generalize dependent t2. induction fs. 
  intros.  intro contra. inversion contra. 
  intros.  intro contra. inversion contra. assert (t2 :: a :: fs <> fs). apply IHfs.
subst. rewrite H1 in H. auto. Qed. 

Lemma fs_pro_double_false : forall (t1 : tm) (t2 : tm) (fs : list tm),
  fs = t1 :: t2 :: fs -> False.
Proof. intros t1 t2 fs.  generalize dependent t1. generalize dependent t2. induction fs. 
  intros.  inversion H. 
  intros.  assert (fs = t2 :: a :: fs -> False). apply IHfs. inversion H. subst. apply H0 in H3. 
 auto. Qed. 


Lemma simulation_L : forall ct t1 fs1 lb1 sf1 ctns_stack1 h1  t2 fs2 lb2 sf2 ctns_stack2 h2, 
      valid_config (Config ct (Container t1 fs1 lb1 sf1) ctns_stack1 h1 ) ->
      forall T, tm_has_type ct empty_context h1 t1 T -> 
      field_wfe_heap ct h1 -> wfe_heap ct h1 ->         
      wfe_stack_frame ct h1 sf1 ->
      flow_to lb1 L_Label = true ->
     Config ct (Container t1 fs1 lb1 sf1) ctns_stack1 h1 
      ==> Config ct (Container t2 fs2 lb2 sf2) ctns_stack2 h2 ->
l_reduction (erasure_fun ct (Container t1 fs1 lb1 sf1) ctns_stack1 h1)
      (erasure_fun ct (Container t2 fs2 lb2 sf2) ctns_stack2 h2). 
(*
Proof with eauto. intros ct t1 fs1 lb1 sf1 ctns_stack1 h1  t2 fs2 lb2 sf2 ctns_stack2 h2.
     intro H_valid_config. intro T. intro H_typing.  intro H_wfe_field. intro H_wfe_heap. 
     intro H_wfe_sf.  intro H_flow. intro H_reduction. 
     remember (Config ct (Container t1 fs1 lb1 sf1) ctns_stack1 h1) as config1. 
     remember (Config ct (Container t2 fs2 lb2 sf2) ctns_stack2 h2) as config2.
     generalize dependent t1. generalize dependent fs1. generalize dependent lb1. 
     generalize dependent ctns_stack1. generalize dependent h1. 

     generalize dependent t2. generalize dependent fs2. generalize dependent lb2. 
     generalize dependent ctns_stack2. generalize dependent h2. 
     generalize dependent T. generalize dependent sf1. generalize dependent sf2. 

induction H_reduction; intros; auto; inversion Heqconfig1; inversion Heqconfig2; subst.
- inversion H_typing. inversion H4.  
- apply field_access_erasure_L_fun_pop; auto. 
    assert (~ value (erasure_L_fun t2)). inversion H_typing.  subst. 
    apply erasure_L_fun_not_value with (classTy clsT) h2 ct; auto. 
    intro contra. inversion H_valid_config. subst. inversion H13. auto.  
- apply field_access_erasure_L_fun_push; auto. 
- inversion H_typing. subst. 
  assert  ( t2 = null \/ exists o',  t2 = ObjId o'). 
  apply field_value with h2 o cls F lo fname ct cls'; auto. 
 pose proof (multi_erasure_heap_equal h2) as H_h.  
pose proof (multi_erasure_L_fs_equal fs2) as Hfs; auto.
assert (forall a, (fun x : id =>
        erasure_obj_null (erasure_obj_null (sf2 x) h2) (erasure_heap h2)) a = 
         (fun x : id => erasure_obj_null (sf2 x) h2) a ). 
  intro a. apply erasure_obj_null_equal_erasure_h. 
  apply functional_extensionality in H2. 
   assert ((erasure_L_fun (FieldAccess (ObjId o) fname)) = (FieldAccess (ObjId o) fname)). auto. 
   assert (erasure_L_fun (t2) = t2). destruct H1. rewrite H1. auto. destruct H1 as [o']. rewrite H1. auto.
  remember ctns_stack2 as ctns_tmp.  

  assert (erasure_fun ct (Container (FieldAccess (ObjId o) fname) fs2 lb1 sf2) ctns_tmp
  h2 = Config ct
  (Container (FieldAccess (ObjId o) fname) (erasure_L_fs fs2) lb1
     (fun x : id => erasure_obj_null (sf2 x) h2)) ctns_tmp (erasure_heap h2)).
  destruct ctns_tmp; unfold erasure_fun; fold erasure_fun; rewrite H_flow; rewrite H5; auto.
  rewrite H7. 
  assert (Config ct
  (Container (FieldAccess (ObjId o) fname) (erasure_L_fs fs2) lb1
     (fun x : id => erasure_obj_null (sf2 x) h2)) ctns_tmp (erasure_heap h2) ==> Config ct
  (Container t2 (erasure_L_fs fs2) (join_label lo lb1)
     (fun x : id => erasure_obj_null (sf2 x) h2)) ctns_tmp (erasure_heap h2)).
  apply ST_fieldRead3 with lo cls F; auto. (* important : non sensitive upgrade*)admit.  
  apply L_reduction with (Config ct
       (Container t2 (erasure_L_fs fs2) (join_label lo lb1)
          (fun x : id => erasure_obj_null (sf2 x) h2)) ctns_tmp (erasure_heap h2)); auto. 
destruct ctns_tmp;  try (induction c); unfold erasure; unfold erasure_fun; fold erasure_fun; 
try (pose proof (multi_erasure_L_fs_equal fs2) as Hfs2; rewrite Hfs2; auto);
try ( pose proof (multi_erasure_L_tm_equal a) as Ha; rewrite Ha); auto;
try(rewrite H6); auto; try (rewrite H2; auto); try (rewrite H_h; auto).

- apply method_call_erasure_L_fun_pop1; auto. 
    assert (~ value (erasure_L_fun t2)). inversion H_typing.  subst. 
    apply erasure_L_fun_not_value with (classTy T0) h2 ct; auto. 
    intro contra. inversion H_valid_config. subst. inversion H16. auto.  

- apply method_call_erasure_L_fun_push1; auto. 

- apply method_call_erasure_L_fun_push2; auto. 

- admit. 

-  admit. -  admit. 

- pose proof (multi_erasure_heap_equal h1) as H_h.  
pose proof (multi_erasure_L_fs_equal fs2) as Hfs; auto.
assert (forall a, (fun x : id =>
        erasure_obj_null (erasure_obj_null (sf2 x) h1) (erasure_heap h1)) a = 
         (fun x : id => erasure_obj_null (sf2 x) h1) a ). 
  intro a. apply erasure_obj_null_equal_erasure_h. 
  apply functional_extensionality in H0. 

inversion H_typing. subst. destruct H5 as [cls_def]. destruct H1 as [field_defs0].
destruct H1 as [method_defs0]. destruct H1. rewrite H in H1. inversion H1. 
remember ctns_stack2 as ctns_tmp.  
assert (Config ct
  (Container (NewExp cls_name) (erasure_L_fs fs2) lb2
     (fun x : id => erasure_obj_null (sf2 x)  h1)) ctns_tmp (erasure_heap h1)  ==> 
Config ct
  (Container (ObjId (get_fresh_oid  (erasure_heap h1))) (erasure_L_fs fs2) lb2
     (fun x : id => erasure_obj_null (sf2 x) h1)) ctns_tmp 

(add_heap_obj (erasure_heap h1) (get_fresh_oid (erasure_heap h1))
  (Heap_OBJ (class_def cls_name field_defs method_defs)
     (init_field_map
        (find_fields (class_def cls_name field_defs method_defs))
        empty_field_map) lb2))). 
 apply ST_NewExp with field_defs method_defs (class_def cls_name field_defs method_defs) (init_field_map
           (find_fields (class_def cls_name field_defs method_defs))
           empty_field_map); auto. 


assert (erasure_fun ct (Container (ObjId (get_fresh_oid  (erasure_heap h1))) (erasure_L_fs fs2) lb2
     (fun x : id => erasure_obj_null (sf2 x) h1)) ctns_tmp 

(add_heap_obj (erasure_heap h1) (get_fresh_oid (erasure_heap h1))
  (Heap_OBJ (class_def cls_name field_defs method_defs)
     (init_field_map
        (find_fields (class_def cls_name field_defs method_defs))
        empty_field_map) lb2))
 = erasure_fun ct (Container (ObjId (get_fresh_oid h1)) fs2 lb2 sf2) ctns_tmp
  (add_heap_obj h1 (get_fresh_oid h1)
     (Heap_OBJ (class_def cls_name field_defs method_defs)
        (init_field_map
           (find_fields (class_def cls_name field_defs method_defs))
           empty_field_map) lb2))).
admit. (*This is an issue that needs to be solved*) 
apply L_reduction with (Config ct
  (Container (ObjId (get_fresh_oid  (erasure_heap h1))) (erasure_L_fs fs2) lb2
     (fun x : id => erasure_obj_null (sf2 x) h1)) ctns_tmp 

(add_heap_obj (erasure_heap h1) (get_fresh_oid (erasure_heap h1))
  (Heap_OBJ (class_def cls_name field_defs method_defs)
     (init_field_map
        (find_fields (class_def cls_name field_defs method_defs))
        empty_field_map) lb2))); auto.
assert (erasure_fun ct (Container (NewExp cls_name) fs2 lb2 sf2) ctns_tmp h1 =
    Config ct
  (Container (NewExp cls_name) (erasure_L_fs fs2) lb2
     (fun x : id => erasure_obj_null (sf2 x)  h1)) ctns_tmp (erasure_heap h1)  ).
destruct ctns_tmp; unfold erasure_fun; fold erasure_fun; rewrite H_flow;
unfold erasure_L_fun; fold erasure_L_fun. auto. auto.  rewrite H6. auto.

- admit. -  admit. -  admit. -  admit. -  admit.

- remember ctns_stack2 as ctns_tmp.  
pose proof (multi_erasure_heap_equal h2) as H_h.  
pose proof (multi_erasure_L_fs_equal fs2) as Hfs2.
  pose proof (multi_erasure_L_tm_equal t2) as H_m_t2.
assert (forall a, (fun x : id =>
        erasure_obj_null (erasure_obj_null (sf2 x) h2) (erasure_heap h2)) a = 
         (fun x : id => erasure_obj_null (sf2 x) h2) a ). 
  intro a. apply erasure_obj_null_equal_erasure_h. 
  apply functional_extensionality in H. 
  destruct ctns_tmp; unfold erasure_fun; fold erasure_fun; rewrite H_flow;
  unfold erasure_L_fun; fold erasure_L_fun. 
  case_eq (flow_to lo L_Label); intro H_lo. 
  assert (flow_to (join_label lb1 lo) L_Label = true).
  apply join_L_label_flow_to_L; auto. rewrite H1.
  assert (Config ct
  (Container (unlabel (v_l (erasure_L_fun t2) lo)) (erasure_L_fs fs2) lb1
     (fun x : id => erasure_obj_null (sf2 x) h2)) nil (erasure_heap h2)  ==>
Config ct
  (Container (erasure_L_fun t2) (erasure_L_fs fs2) (join_label lb1 lo)
     (fun x : id => erasure_obj_null (sf2 x) h2)) nil (erasure_heap h2)    ). 
    apply ST_unlabel3; auto. apply erasure_L_fun_value.  auto. 
assert (erasure_fun ct
  (Container (erasure_L_fun t2) (erasure_L_fs fs2) (join_label lb1 lo)
     (fun x : id => erasure_obj_null (sf2 x) h2)) nil (erasure_heap h2)  = 
  Config ct
  (Container (erasure_L_fun t2) (erasure_L_fs fs2) (join_label lb1 lo)
     (fun x : id => erasure_obj_null (sf2 x) h2)) nil (erasure_heap h2)).
  unfold erasure_fun. rewrite H1. 
rewrite H_h. rewrite Hfs2. rewrite H_m_t2. rewrite H.  auto. 
  apply L_reduction with (Config ct
       (Container (erasure_L_fun t2) (erasure_L_fs fs2) (join_label lb1 lo)
          (fun x : id => erasure_obj_null (sf2 x) h2)) nil (erasure_heap h2)); auto.

 assert (flow_to (join_label lb1 lo) L_Label = false). apply flow_join_label with lo lb1; auto.
rewrite H1.  
assert (Config ct
  (Container (unlabel (v_l dot lo)) (erasure_L_fs fs2) lb1
     (fun x : id => erasure_obj_null (sf2 x) h2)) nil (erasure_heap h2)  ==>
Config ct
  (Container dot (erasure_L_fs fs2) (join_label lb1 lo)
     (fun x : id => erasure_obj_null (sf2 x) h2)) nil (erasure_heap h2)    ). 
    apply ST_unlabel3; auto. 
apply L_reduction with (Config ct
  (Container dot (erasure_L_fs fs2) (join_label lb1 lo)
     (fun x : id => erasure_obj_null (sf2 x) h2)) nil (erasure_heap h2)  ); auto.
unfold erasure. unfold erasure_fun. rewrite H1. rewrite H_h.  auto. 

case_eq (flow_to lo L_Label); intro H_lo. 
  assert (flow_to (join_label lb1 lo) L_Label = true).
  apply join_L_label_flow_to_L; auto. rewrite H1.
  assert (Config ct
  (Container (unlabel (v_l (erasure_L_fun t2) lo)) (erasure_L_fs fs2) lb1
     (fun x : id => erasure_obj_null (sf2 x) h2))  (c :: ctns_tmp) (erasure_heap h2)  ==>
Config ct
  (Container (erasure_L_fun t2) (erasure_L_fs fs2) (join_label lb1 lo)
     (fun x : id => erasure_obj_null (sf2 x) h2))  (c :: ctns_tmp) (erasure_heap h2)    ). 
    apply ST_unlabel3; auto. apply erasure_L_fun_value.  auto. 
assert (erasure_fun ct
  (Container (erasure_L_fun t2) (erasure_L_fs fs2) (join_label lb1 lo)
     (fun x : id => erasure_obj_null (sf2 x) h2))  (c :: ctns_tmp) (erasure_heap h2)  = 
  Config ct
  (Container (erasure_L_fun t2) (erasure_L_fs fs2) (join_label lb1 lo)
     (fun x : id => erasure_obj_null (sf2 x) h2))  (c :: ctns_tmp) (erasure_heap h2)).
  unfold erasure_fun. rewrite H1. 
rewrite H_h. rewrite Hfs2. rewrite H_m_t2. rewrite H.  auto. 
  apply L_reduction with (Config ct
       (Container (erasure_L_fun t2) (erasure_L_fs fs2) (join_label lb1 lo)
          (fun x : id => erasure_obj_null (sf2 x) h2))  (c :: ctns_tmp) (erasure_heap h2)); auto.

 assert (flow_to (join_label lb1 lo) L_Label = false). apply flow_join_label with lo lb1; auto.
rewrite H1.  
assert (Config ct
  (Container (unlabel (v_l dot lo)) (erasure_L_fs fs2) lb1
     (fun x : id => erasure_obj_null (sf2 x) h2)) nil (erasure_heap h2)  ==>
Config ct
  (Container dot (erasure_L_fs fs2) (join_label lb1 lo)
     (fun x : id => erasure_obj_null (sf2 x) h2)) nil (erasure_heap h2)    ). 
    apply ST_unlabel3; auto. 
apply L_reduction with (Config ct
  (Container dot (erasure_L_fs fs2) (join_label lb1 lo)
     (fun x : id => erasure_obj_null (sf2 x) h2))  (c :: ctns_tmp) (erasure_heap h2)  ); auto.
unfold erasure. unfold erasure_fun. rewrite H1. rewrite H_h.  auto.

- admit.  - admit. 
-  remember ctns_stack2 as ctns_tmp.  
pose proof (multi_erasure_heap_equal h2) as H_h.  
pose proof (multi_erasure_L_fs_equal fs2) as Hfs2.
  pose proof (multi_erasure_L_tm_equal v) as H_m_v.
assert (forall a, (fun x : id =>
        erasure_obj_null (erasure_obj_null (sf2 x) h2) (erasure_heap h2)) a = 
         (fun x : id => erasure_obj_null (sf2 x) h2) a ). 
  intro a. apply erasure_obj_null_equal_erasure_h. 
  apply functional_extensionality in H0. 
  destruct ctns_tmp; unfold erasure_fun; fold erasure_fun; rewrite H_flow;
  unfold erasure_L_fun; fold erasure_L_fun. 
  case_eq (flow_to lo L_Label); intro H_lo. 
  assert (Config ct
  (Container (labelOf (v_l (erasure_L_fun v) lo)) (erasure_L_fs fs2) lb2
     (fun x : id => erasure_obj_null (sf2 x) h2)) nil (erasure_heap h2)  ==>
Config ct
  (Container (l lo) (erasure_L_fs fs2) lb2
     (fun x : id => erasure_obj_null (sf2 x) h2)) nil (erasure_heap h2)    ). 
  apply ST_labelof3. apply erasure_L_fun_value.  auto. 

assert (erasure_fun ct
  (Container (l lo) (erasure_L_fs fs2) lb2
     (fun x : id => erasure_obj_null (sf2 x) h2)) nil (erasure_heap h2)   = 
  Config ct
  (Container (l lo) (erasure_L_fs fs2) lb2
     (fun x : id => erasure_obj_null (sf2 x) h2)) nil (erasure_heap h2)).
  unfold erasure_fun. rewrite H_flow. 
rewrite H_h. rewrite Hfs2. rewrite H0.  auto. 
  apply L_reduction with (Config ct
  (Container (l lo) (erasure_L_fs fs2) lb2
     (fun x : id => erasure_obj_null (sf2 x) h2)) nil (erasure_heap h2)); auto.

assert (Config ct
  (Container (labelOf (v_l dot lo)) (erasure_L_fs fs2) lb2
     (fun x : id => erasure_obj_null (sf2 x) h2)) nil (erasure_heap h2)  ==>
Config ct
  (Container (l lo) (erasure_L_fs fs2) lb2
     (fun x : id => erasure_obj_null (sf2 x) h2)) nil (erasure_heap h2)    ). 
    apply ST_labelof3; auto. 
apply L_reduction with (Config ct
  (Container (l lo) (erasure_L_fs fs2) lb2
     (fun x : id => erasure_obj_null (sf2 x) h2)) nil (erasure_heap h2)  ); auto.
unfold erasure. unfold erasure_fun. rewrite H_flow. rewrite H_h.
rewrite Hfs2. rewrite H0.  auto. 

case_eq (flow_to lo L_Label); intro H_lo. 
  assert (Config ct
  (Container (labelOf (v_l (erasure_L_fun v) lo)) (erasure_L_fs fs2) lb2
     (fun x : id => erasure_obj_null (sf2 x) h2)) (c :: ctns_tmp)  (erasure_heap h2)  ==>
Config ct
  (Container (l lo) (erasure_L_fs fs2) lb2
     (fun x : id => erasure_obj_null (sf2 x) h2)) (c :: ctns_tmp)  (erasure_heap h2)    ). 
  apply ST_labelof3. apply erasure_L_fun_value.  auto. 

assert (erasure_fun ct
  (Container (l lo) (erasure_L_fs fs2) lb2
     (fun x : id => erasure_obj_null (sf2 x) h2)) (c :: ctns_tmp)  (erasure_heap h2)   = 
  Config ct
  (Container (l lo) (erasure_L_fs fs2) lb2
     (fun x : id => erasure_obj_null (sf2 x) h2)) (c :: ctns_tmp)  (erasure_heap h2)).
  unfold erasure_fun. rewrite H_flow. 
rewrite H_h. rewrite Hfs2. rewrite H0.  auto. 
  apply L_reduction with (Config ct
  (Container (l lo) (erasure_L_fs fs2) lb2
     (fun x : id => erasure_obj_null (sf2 x) h2)) (c :: ctns_tmp)  (erasure_heap h2)); auto.

assert (Config ct
  (Container (labelOf (v_l dot lo)) (erasure_L_fs fs2) lb2
     (fun x : id => erasure_obj_null (sf2 x) h2)) (c :: ctns_tmp)  (erasure_heap h2)  ==>
Config ct
  (Container (l lo) (erasure_L_fs fs2) lb2
     (fun x : id => erasure_obj_null (sf2 x) h2)) (c :: ctns_tmp)  (erasure_heap h2)    ). 
    apply ST_labelof3; auto. 
apply L_reduction with (Config ct
  (Container (l lo) (erasure_L_fs fs2) lb2
     (fun x : id => erasure_obj_null (sf2 x) h2)) (c :: ctns_tmp)  (erasure_heap h2)  ); auto.
unfold erasure. unfold erasure_fun. rewrite H_flow. rewrite H_h.
rewrite Hfs2. rewrite H0.  auto. 


-  admit. -  admit. -admit. 

- admit. - admit.

- admit. 



-  admit. -  admit. -  admit. -  admit.
-  admit.

 
-  admit.


 -  admit. -  admit. -  admit. -  admit. -  admit. 


-  

assert (erasure_fun ct (Container t1 nil lb1 sf1)
  (Container return_hole fs2 lb2 sf2 :: ctns_stack2) h2 = 
(Config ct
  (Container (erasure_L_fun t1) nil lb1
     (fun x : id => erasure_obj_null (sf1 x) h2))
  (Container return_hole fs2 lb2 sf2 :: ctns_stack2) (erasure_heap h2)   )).
unfold erasure_fun. rewrite H_flow. unfold erasure_L_fs. auto.
rewrite H0. 


destruct  ctns_stack2; unfold erasure_fun; fold erasure_fun; case_eq (flow_to lb2 L_Label); intro. 
+ 







unfold erasure_fun. fold erasure_fun. rewrite H_flow.
  + unfold erasure_L_fun. fold erasure_L_fun. auto.
  assert (Config ct
    (Container (FieldAccess (erasure_L_fun t2) f) fs1 lb2
       (fun x : id => erasure_obj_null (sf2 x) h2)) nil (erasure_heap h2) ==>
    Config ct
    (Container (erasure_L_fun t2) (FieldAccess hole f :: fs1) lb2
       (fun x : id => erasure_obj_null (sf2 x) h2)) nil (erasure_heap h2) ). auto. 
    assert (~ value (erasure_L_fun t2)). inversion H_typing.  subst. 
    apply erasure_L_fun_not_value with (classTy clsT) h2 ct; auto. 
    intro contra. inversion H_valid_config. subst. inversion H13.  

    apply ST_fieldRead1; auto.

  assert ( erasure ( Config ct
       (Container (erasure_L_fun t2) (FieldAccess hole f :: fs1) lb2
          (fun x : id => erasure_obj_null (sf2 x) h2)) nil (erasure_heap h2)) =
    Config ct
  (Container (erasure_L_fun t2) (FieldAccess hole f :: fs1) lb2
     (fun x : id => erasure_obj_null (sf2 x) h2)) nil (erasure_heap h2)).
  unfold erasure. unfold erasure_fun. rewrite H_flow. 
  pose proof (multi_erasure_L_tm_equal t2) as Ht2. rewrite Ht2. 
  
assert (forall a, (fun x : id =>
      erasure_obj_null (erasure_obj_null (sf2 x) h2) (erasure_heap h2)) a = 
       (fun x : id => erasure_obj_null (sf2 x) h2) a ). 
intro a. apply erasure_obj_null_equal_erasure_h. 
apply functional_extensionality in H1. rewrite H1.

pose proof (multi_erasure_heap_equal h2).  rewrite H2. auto. 
apply L_reduction with (Config ct
          (Container (erasure_L_fun t2) (FieldAccess hole f :: fs1) lb2
             (fun x : id => erasure_obj_null (sf2 x) h2)) nil
          (erasure_heap h2)); auto. 


+ induction a.   unfold erasure_fun. fold erasure_fun. rewrite H_flow. 
  assert (Config ct
    (Container (FieldAccess (erasure_L_fun t2) f) fs1 lb2
       (fun x : id => erasure_obj_null (sf2 x) h2)) (Container t f0 l0 s :: ctns_stack2) (erasure_heap h2) ==>
    Config ct
    (Container (erasure_L_fun t2) (FieldAccess hole f :: fs1) lb2
       (fun x : id => erasure_obj_null (sf2 x) h2)) (Container t f0 l0 s :: ctns_stack2) (erasure_heap h2) ). auto. 
    assert (~ value (erasure_L_fun t2)). inversion H_typing.  subst. 
    apply erasure_L_fun_not_value with (classTy clsT) h2 ct; auto. 
    intro contra. inversion H_valid_config. subst. inversion H13.  auto. 

  assert ( erasure ( Config ct
       (Container (erasure_L_fun t2) (FieldAccess hole f :: fs1) lb2
          (fun x : id => erasure_obj_null (sf2 x) h2)) (Container t f0 l0 s :: ctns_stack2) (erasure_heap h2)) =
    Config ct
  (Container (erasure_L_fun t2) (FieldAccess hole f :: fs1) lb2
     (fun x : id => erasure_obj_null (sf2 x) h2)) (Container t f0 l0 s :: ctns_stack2) (erasure_heap h2)).
  unfold erasure. unfold erasure_fun. rewrite H_flow. 
  pose proof (multi_erasure_L_tm_equal t2) as Ht2. rewrite Ht2. 
  
assert (forall a, (fun x : id =>
      erasure_obj_null (erasure_obj_null (sf2 x) h2) (erasure_heap h2)) a = 
       (fun x : id => erasure_obj_null (sf2 x) h2) a ). 
intro a. apply erasure_obj_null_equal_erasure_h. 
apply functional_extensionality in H1. rewrite H1.

pose proof (multi_erasure_heap_equal h2).  rewrite H2. auto. 
apply L_reduction with (Config ct
          (Container (erasure_L_fun t2) (FieldAccess hole f :: fs1) lb2
             (fun x : id => erasure_obj_null (sf2 x) h2)) (Container t f0 l0 s :: ctns_stack2)
          (erasure_heap h2)); auto.

(*(Container t1 (FieldAccess hole f :: fs2) lb2 sf2) *)
- induction ctns_stack2; unfold erasure_fun; fold erasure_fun; rewrite H_flow.
  + unfold erasure_L_fun. fold erasure_L_fun. auto.
  assert 
    (Config ct
         (Container (erasure_L_fun t1) (FieldAccess hole f :: fs2) lb2
              (fun x : id => erasure_obj_null (sf2 x) h2)) nil (erasure_heap h2) ==>
    Config ct
  (Container (FieldAccess (erasure_L_fun t1) f) fs2 lb2
     (fun x : id => erasure_obj_null (sf2 x) h2)) nil (erasure_heap h2) ). auto. 
    pose proof (erasure_L_fun_value t1 H). auto. 

  assert ( erasure ( Config ct
  (Container (FieldAccess (erasure_L_fun t1) f) fs2 lb2
     (fun x : id => erasure_obj_null (sf2 x) h2)) nil (erasure_heap h2) )  =
  Config ct
  (Container (FieldAccess (erasure_L_fun t1) f) fs2 lb2
     (fun x : id => erasure_obj_null (sf2 x) h2)) nil (erasure_heap h2)).
  unfold erasure. unfold erasure_fun. rewrite H_flow. 
  pose proof (multi_erasure_L_tm_equal t1) as Ht1. 
  unfold erasure_L_fun. fold erasure_L_fun. rewrite Ht1. 
  
assert (forall a, (fun x : id =>
      erasure_obj_null (erasure_obj_null (sf2 x) h2) (erasure_heap h2)) a = 
       (fun x : id => erasure_obj_null (sf2 x) h2) a ). 
intro a. apply erasure_obj_null_equal_erasure_h. 
apply functional_extensionality in H1. rewrite H1.

pose proof (multi_erasure_heap_equal h2).  rewrite H2. auto. 
apply L_reduction with (Config ct
       (Container (FieldAccess (erasure_L_fun t1) f) fs2 lb2
          (fun x : id => erasure_obj_null (sf2 x) h2)) nil (erasure_heap h2)); auto. 

+ unfold erasure_L_fun. fold erasure_L_fun. auto. induction a. 
  assert 
    (Config ct
         (Container (erasure_L_fun t1) (FieldAccess hole f :: fs2) lb2
              (fun x : id => erasure_obj_null (sf2 x) h2)) (Container t f0 l0 s :: ctns_stack2) (erasure_heap h2) ==>
    Config ct
  (Container (FieldAccess (erasure_L_fun t1) f) fs2 lb2
     (fun x : id => erasure_obj_null (sf2 x) h2)) (Container t f0 l0 s :: ctns_stack2) (erasure_heap h2) ). auto. 
    pose proof (erasure_L_fun_value t1 H). auto. 

  assert ( erasure ( Config ct
  (Container (FieldAccess (erasure_L_fun t1) f) fs2 lb2
     (fun x : id => erasure_obj_null (sf2 x) h2)) (Container t f0 l0 s :: ctns_stack2) (erasure_heap h2) )  =
  Config ct
  (Container (FieldAccess (erasure_L_fun t1) f) fs2 lb2
     (fun x : id => erasure_obj_null (sf2 x) h2)) (Container t f0 l0 s :: ctns_stack2) (erasure_heap h2)).
  unfold erasure. unfold erasure_fun. rewrite H_flow. 
  pose proof (multi_erasure_L_tm_equal t1) as Ht1. 
  unfold erasure_L_fun. fold erasure_L_fun. rewrite Ht1. 
  
assert (forall a, (fun x : id =>
      erasure_obj_null (erasure_obj_null (sf2 x) h2) (erasure_heap h2)) a = 
       (fun x : id => erasure_obj_null (sf2 x) h2) a ). 
intro a. apply erasure_obj_null_equal_erasure_h. 
apply functional_extensionality in H1. rewrite H1.

pose proof (multi_erasure_heap_equal h2).  rewrite H2. auto. 
apply L_reduction with (Config ct
       (Container (FieldAccess (erasure_L_fun t1) f) fs2 lb2
          (fun x : id => erasure_obj_null (sf2 x) h2)) (Container t f0 l0 s :: ctns_stack2) (erasure_heap h2)); auto. 

- induction ctns_stack2; unfold erasure_fun; fold erasure_fun; rewrite H_flow.
  + case_eq (flow_to (join_label lo lb1) L_Label). intro. 
  


 - admit. - admit. - admit. - admit.  - admit. - admit. - admit. - admit.
- admit. - admit. 

- induction ctns_stack2. unfold erasure_fun. fold erasure_fun. rewrite H_flow.

- induction ctns_stack2. unfold erasure_fun. fold erasure_fun. rewrite H_flow.
  unfold erasure_L_fun. fold erasure_L_fun. auto.
  assert (Config ct
    (Container (FieldAccess (erasure_L_fun t2) f) fs1 lb2
       (fun x : id => erasure_obj_null (sf2 x) h2)) nil (erasure_heap h2) ==>
    Config ct
    (Container (erasure_L_fun t2) (FieldAccess hole f :: fs1) lb2
       (fun x : id => erasure_obj_null (sf2 x) h2)) nil (erasure_heap h2) ). auto. 
    pose proof (erasure_L_fun_not_value t2 H).  apply ST_fieldRead1; auto.

 

 auto; try (rename lb2 into lb1);
case_eq (flow_to lb1 L_Label); try (intro H_lb1_true; rewrite H_flow in H_lb1_true; inversion H_lb1_true);
try (induction ctns_stack2; unfold erasure_fun; rewrite H_flow; auto); fold erasure_fun.

*) Admitted. 








Lemma multi_step_simulation : forall ct t1 fs1 lb1 sf1 ctns_stack1 h1  t2 fs2 lb2 sf2 ctns_stack2 h2, 
      valid_syntax t1 ->
      forall T, tm_has_type ct empty_context h1 t1 T -> 
      field_wfe_heap ct h1 -> wfe_heap ct h1 ->         
      wfe_stack_frame ct h1 sf1 ->
     Config ct (Container t1 fs1 lb1 sf1) ctns_stack1 h1 
      ==>* Config ct (Container t2 fs2 lb2 sf2) ctns_stack2 h2 ->
      erasure_fun ct (Container t1 fs1 lb1 sf1) ctns_stack1 h1  ==>L*
      erasure_fun ct (Container t2 fs2 lb2 sf2) ctns_stack2 h2.
Proof. Admitted.


Lemma erasure_equal_input : forall ct sf sf' t fs lb, 
      L_equivalence_store sf nil sf' nil ->
      erasure (Config ct (Container t fs lb sf) nil nil) = 
      erasure (Config ct (Container t fs lb sf') nil nil).
Proof. intros ct sf sf' t fs lb. intro Hy. 
    unfold erasure. unfold erasure_fun.  case_eq (flow_to lb L_Label). intro.
 
    inversion Hy. subst. auto.  subst. auto. subst.  
    assert (forall a, (fun x : id => erasure_obj_null (sf x) nil) a = (fun x : id => erasure_obj_null (sf' x) nil) a).
    intro x. remember (sf x) as option_t. induction option_t. destruct H0 with x a; auto. 
    destruct H2. rewrite H2. 
    apply L_equal_imply_erasure_object_equal in H3. auto. 
    remember  (sf' x) as option_t'.  induction option_t'. destruct H1 with x a; auto. destruct H2. 
    rewrite H2 in Heqoption_t. inversion Heqoption_t. auto. 
    apply functional_extensionality in H2. rewrite H2. auto. auto .
Qed.  

Lemma Non_interference : forall ct x t fs lb sf sf' lb1 sf1  lb2 sf2 v1 v2 final_v1 final_v2 h1 h2, 
      valid_syntax t ->
      field_wfe_heap ct nil -> wfe_heap ct nil ->         
      wfe_stack_frame ct nil sf ->
      field_wfe_heap ct nil -> wfe_heap ct nil ->         
      wfe_stack_frame ct nil sf' ->
      L_equivalence_store sf nil sf' nil -> 
      sf x = Some (v_l v1 H_Label) ->
      sf' x = Some (v_l v2 H_Label) ->
     Config ct (Container t fs lb sf) nil nil
      ==>* Config ct (Container final_v1 nil lb1 sf1) nil h1 ->
     Config ct (Container t fs lb sf') nil nil 
      ==>* Config ct (Container final_v2 nil lb2 sf2) nil h2 ->
      value final_v1 -> value final_v2 ->
      forall T, tm_has_type ct empty_context nil t T->
      L_equivalence_config (Config ct (Container final_v1 nil lb1 sf1) nil h1) (Config ct (Container final_v2 nil lb2 sf2) nil h2).
Proof. 
intros  ct x t fs lb sf sf' lb1 sf1  lb2 sf2 v1 v2 final_v1 final_v2 h1 h2.
    intro H_valid_syntax.
    intro H_wfe_field. intro H_wfe_heap. intro H_wfe_frame. 
    intro H_wfe_field'. intro H_wfe_heap'. intro H_wfe_frame'. intro H_equal_input. 
    intro H_sf1. intro H_sf2.  intro H_execution1.  intro H_execution2. intro H_final_v1. intro H_final_v2.
    intro T. intro H_typing.
    remember (erasure (Config ct (Container t fs lb sf) nil nil)) as config_r.
    remember (erasure (Config ct (Container t fs lb sf') nil nil)) as config_r'.

    assert  (config_r = config_r'). subst. 
    apply erasure_equal_input. auto. subst.  

    assert ( (erasure (Config ct (Container t fs lb sf) nil nil))  ==>L* (erasure (Config ct (Container final_v1 nil lb1 sf1) nil h1) ) ).
    apply multi_step_simulation with T; auto.  

    assert ( (erasure (Config ct (Container t fs lb sf') nil nil))  ==>L* (erasure (Config ct (Container final_v2 nil lb2 sf2) nil h2) ) ).
    apply multi_step_simulation with T; auto.  


   assert ((erasure (Config ct (Container final_v1 nil lb1 sf1) nil h1) ) =
       (erasure (Config ct (Container final_v2 nil lb2 sf2) nil h2) ) ).
   (*apply L_reduction_multistep_determinacy.*) admit.

   unfold erasure in H2. unfold erasure_fun in H2. 
    case_eq (flow_to lb1 L_Label). intro. rewrite H3 in H2. 
    case_eq (flow_to lb2 L_Label). intro. rewrite H4 in H2. 
    apply L_equivalence_config_L; auto.  admit. admit. 

    intro. rewrite H4 in H2. inversion H2. rewrite H7 in H3. rewrite H3 in H4. inversion H4. 

    intro.  rewrite H3 in H2. 
    case_eq (flow_to lb2 L_Label). intro. rewrite H4 in H2.  inversion H2. 
    rewrite H7 in H3. rewrite H3 in H4. inversion H4. 

    intro. rewrite H4 in H2. apply L_equivalence_config_H; auto.

Qed. 

---------------------------------------------------------------------------------------


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


