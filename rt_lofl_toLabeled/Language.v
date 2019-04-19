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
  | EqCmp : tm -> tm -> tm           
  | FieldAccess : tm -> id -> tm
  | MethodCall : tm -> id -> tm -> tm
  | NewExp : cn -> tm
(* boolean *)                    
  | B_true : tm
  | B_false : tm             
                     
(* label related *)
  | l : Label -> tm
  | labelData : tm -> Label -> tm
  | unlabel : tm -> tm
  | labelOf : tm -> tm
  | objectLabelOf : tm -> tm   
  | raiseLabel : tm -> Label -> tm
  | toLabeled : tm -> tm -> tm
  | getCurrentLevel : tm                            
                              
                               

(* statements *)
  | Skip : tm
  | Assignment : id -> tm -> tm
  | FieldWrite : tm -> id -> tm -> tm
  | If : tm -> tm -> tm -> tm 
  | Sequence : tm -> tm -> tm

(* special terms *)
  | ObjId: oid -> tm
  (* runtime labeled date*)
  | v_l : tm -> Label -> tm
  | v_opa_l : tm -> Label -> tm
  | hole : tm 
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
  | v_opa_labeled : forall lb v,
      value v -> (forall v0 lb0, v <> v_opa_l v0 lb0) ->
      value (v_opa_l v lb)
  | v_true :
      value B_true
  | v_false :
      value B_false.
    
Hint Constructors value. 


(* stack frame *)
Definition stack_frame : Type := id -> (option tm).

Definition sf_update (sf : stack_frame) (x : id) (v : tm) :=
  fun x' => if beq_id x x' then (Some v) else sf x'.


(*new definition for the code *)
Definition frame_stack  :Type := list tm.

Definition empty_stack_frame : stack_frame := fun _ => None.

(* Definitions for Heap related*)
Definition FieldMap : Type := id -> (option tm).

Definition fields_update (F : FieldMap) (x : id) (v : tm) :=
  fun x' => if beq_id x x' then (Some v) else F x'.

(* class definition -> Fields -> object label -> label of label*)
Inductive heapObj : Type :=
  | Heap_OBJ : CLASS -> FieldMap -> Label -> Label -> heapObj.

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


Fixpoint assignment_free (t : tm) :=
  match t with
    | Tvar x => true
    | null => true
    | EqCmp e1 e2  => if (assignment_free e1) then (assignment_free e2) else false
    | FieldAccess e f => (assignment_free e)
    | MethodCall e1 meth e2 => if (assignment_free e1) then (assignment_free e2) else false
    | NewExp cls => true
    | B_true => true
    | B_false => true
(* label related *)
    | l lb => true
    | labelData e lb => (assignment_free e)
    | unlabel e => (assignment_free e)
    | labelOf e => (assignment_free e)
    | objectLabelOf e => (assignment_free e)
    | raiseLabel e lb => (assignment_free e)
    | toLabeled e1 e2 => if (assignment_free e1) then (assignment_free e2) else false
    | getCurrentLevel => true
                           
(* statements *)
    | Skip => true
    | Assignment x e => false
    | FieldWrite e1 f e2 =>  if (assignment_free e1) then (assignment_free e2) else false
    | If guard e1 e2 =>  if assignment_free guard then (if (assignment_free e1) then (assignment_free e2) else false )  else false
    | Sequence e1 e2 =>  if (assignment_free e1) then (assignment_free e2) else false

(* special terms *)
    | ObjId o =>  true
  (* runtime labeled date*)
    | v_l e lb => true
    | v_opa_l e lb => true
    | hole => true
    | return_hole => true
  end.

Fixpoint surface_syntax (t : tm) :=
  match t with
    | Tvar x => true
    | null => true
    | EqCmp e1 e2  => if (surface_syntax e1) then (surface_syntax e2) else false
    | FieldAccess e f => (surface_syntax e)
    | MethodCall e1 meth e2 => if (surface_syntax e1) then (surface_syntax e2) else false
    | NewExp cls => true
    | B_true => true
    | B_false => true
(* label related *)
    | l lb => true
    | labelData e lb => (surface_syntax e)
    | unlabel e => (surface_syntax e)
    | labelOf e => (surface_syntax e)
    | objectLabelOf e => (surface_syntax e)
    | raiseLabel e lb => (surface_syntax e)
    | toLabeled e1 e2 => if ((surface_syntax e1) &&  (assignment_free e1))  then (surface_syntax e2) else false
    | getCurrentLevel => true
    
                           
(* statements *)
    | Skip => false
    | Assignment x e => (surface_syntax e)
    | FieldWrite e1 f e2 =>  if (surface_syntax e1) then (surface_syntax e2) else false
    | If guard e1 e2 =>  if surface_syntax guard then (if (surface_syntax e1) then (surface_syntax e2) else false )  else false
    | Sequence e1 e2 =>  if (surface_syntax e1) then (surface_syntax e2) else false

(* special terms *)
    | ObjId o =>  false
  (* runtime labeled date*)
    | v_l e lb => false
    | v_opa_l e lb => false
    | hole => false
    | return_hole => false
  end.




Inductive valid_syntax :  tm -> Prop :=
  (*variable *)
  | Valid_var : forall x,
      valid_syntax (Tvar x)
(* null *)
  | Valid_null : 
      valid_syntax null
                   
(* equal comparison *)
  | Valid_Eq1 : forall e1 e2,
      surface_syntax e1 = true ->
      surface_syntax e2 = true -> 
      valid_syntax (EqCmp e1 e2)

  | Valid_Eq2 : forall  e2,
      surface_syntax e2 = true -> 
      valid_syntax (EqCmp hole e2)

  | Valid_Eq3 : forall v e2,
      value v -> 
      surface_syntax e2 = true ->
      valid_syntax (EqCmp v e2)

  | Valid_Eq4 : forall v,
      value v -> 
      valid_syntax (EqCmp v hole)

  | Valid_Eq5 : forall v1 v2,
      value v1 -> value v2 ->
      valid_syntax (EqCmp v1 v2)               

                   
(* Field read *)
  | Valid_FieldAccess1 : forall e f,
      surface_syntax e = true ->
      valid_syntax (FieldAccess e f)

  | Valid_FieldAccess2 : forall f,
      valid_syntax (FieldAccess hole f)

  | Valid_FieldAccess3 : forall v f,
      value v ->
      valid_syntax (FieldAccess v f)

  | Valid_boolean_true :
      valid_syntax B_true
  | Valid_boolean_false :
      valid_syntax B_false

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

(* objectLabelOf *)
  | Valid_objectLabelOf1 : forall e,
      surface_syntax e = true ->
      valid_syntax (objectLabelOf e)

  | Valid_objectLabelOf2 : 
      valid_syntax (objectLabelOf hole)

  | Valid_objectLabelOf3 : forall v,
      value v ->
      valid_syntax (objectLabelOf v)
                   

(* raise label *)
  | Valid_raiseLabel1 : forall e lb,
      surface_syntax e = true ->
      valid_syntax (raiseLabel e lb)

  | Valid_raiseLabel2 : forall lb,
      valid_syntax (raiseLabel hole lb)

  | Valid_raiseLabel3 : forall v lb,
      value v ->
      valid_syntax (raiseLabel v lb)

(* toLabeled e1 e2 *)
  | Valid_toLabeled1 : forall e1 e2,
      surface_syntax e1 = true ->
      assignment_free e1 = true ->
      surface_syntax e2 = true -> 
      valid_syntax (toLabeled e1 e2)

  | Valid_toLabeled2 : forall e, 
      surface_syntax e = true  ->
      assignment_free e = true ->
      valid_syntax (toLabeled e hole)
                   
  | Valid_toLabeled3 : forall v e,
      value v -> 
      surface_syntax e = true  ->
      assignment_free e = true ->
      valid_syntax (toLabeled e v)

  (*get current context level *)                 
  | Valid_getCurrentLevel :
      valid_syntax getCurrentLevel
  
  
                   
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
  | Valid_if1 : forall guard e1 e2,
      
      surface_syntax guard = true  ->
      surface_syntax e1 = true ->
      surface_syntax e2 = true ->
      valid_syntax (If guard e1 e2)

  | Valid_if2 : forall e1 e2,
      surface_syntax e1 = true ->
      surface_syntax e2 = true ->
      valid_syntax (If hole e1 e2)

  | Valid_if3 : forall guard e1 e2,
      value guard  ->
      surface_syntax e1 = true ->
      surface_syntax e2 = true ->
      valid_syntax (If guard e1 e2)
                   

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
      (forall v0 lb0, v <> v_opa_l v0 lb0) ->
      valid_syntax (v_opa_l v lb)
(* dot 
  | Valid_dot : 
      valid_syntax dot *)
(* hole *)
  | Valid_hole : 
      valid_syntax hole
(* return_hole *)
  | Valid_return_hole : 
      valid_syntax return_hole.
Hint Constructors valid_syntax.

Fixpoint hole_free (t : tm) :=
  match t with
    | Tvar x => true
    | null => true
    | EqCmp e1 e2 => if (hole_free e1) then (hole_free e2) else false            
    | FieldAccess e f => (hole_free e)
    | MethodCall e1 meth e2 => if (hole_free e1) then (hole_free e2) else false
    | NewExp cls => true
    | B_true => true
    | B_false => true              
                      
(* label related *)
    | l lb => true
    | labelData e lb => (hole_free e)
    | unlabel e => (hole_free e)
    | labelOf e => (hole_free e)
    | objectLabelOf e => hole_free e
    | raiseLabel e lb => (hole_free e)
    | toLabeled e1 e2 => if (hole_free e1) then (hole_free e2) else false
    | getCurrentLevel => true
    
(* statements *)
    | Skip => true
    | Assignment x e => (hole_free e)
    | FieldWrite e1 f e2 =>  if (hole_free e1) then (hole_free e2) else false
    | If guard e1 e2 =>  if (hole_free guard) then ( if (hole_free e1) then (hole_free e2) else false ) else false
    | Sequence e1 e2 =>  if (hole_free e1) then (hole_free e2) else false

(* special terms *)
    | ObjId o =>  true
  (* runtime labeled date*)
    | v_l e lb => (hole_free e)
    | v_opa_l e lb => (hole_free e)
    | hole => false
    | return_hole => false
  end.


Fixpoint runtime_label (t : tm) :=
  match t with
  | v_opa_l v lb => lb
  | _ => L_Label
  end.

Fixpoint runtime_val (t : tm) : tm  :=
  match t with
    | v_opa_l v lb =>  v
    | _ => t
  end.


Fixpoint object_label (t : tm)  (h : heap) : Label :=
  match t with
  | ObjId o => match (lookup_heap_obj h o) with
                | Some (Heap_OBJ cls F lo ll) => ll
                | None => L_Label
               end
  | _ => L_Label
  end.

Fixpoint label_label (t : tm)  (h : heap) : Label :=
  match t with
  | ObjId o => match (lookup_heap_obj h o) with
                | Some (Heap_OBJ cls F lo ll) => ll
                | None => L_Label
               end
  | _ => L_Label
  end.

Inductive reduction : config -> config -> Prop :=
(* variabel access *)
  | ST_var : forall id h lb sf v ctns ct fs,
      Some v = sf(id) ->
      Config ct (Container (Tvar id) fs lb sf) ctns h ==> Config ct (Container v fs lb sf) ctns h


(* eq comparison *)
  (* context rule 1 *)
  | ST_EqCmp1 : forall h e1 e2 ct fs ctns sf lb,
      ~ value e1 ->
      Config ct (Container (EqCmp e1 e2) fs lb sf) ctns h ==> Config ct (Container e1 ((EqCmp hole e2) :: fs) lb sf) ctns h

  | ST_EqCmp2 : forall h e2 ct fs v ctns sf lb,
      value v ->
      Config ct (Container v ((EqCmp hole e2) :: fs) lb sf) ctns h ==> Config ct (Container (EqCmp v e2) fs lb sf ) ctns h


  | ST_EqCmp3 : forall h v e2 ct fs ctns sf lb,
      value v ->
      ~ value e2 ->
      Config ct (Container (EqCmp v e2) fs lb sf) ctns h ==> Config ct (Container e2 ((EqCmp v hole) :: fs) lb sf) ctns h
             
  | ST_EqCmp4 : forall h ct fs v1 v2 ctns sf lb,
      value v1 ->
      value v2 ->
      Config ct (Container v2 ((EqCmp v1 hole) :: fs) lb sf) ctns h ==> Config ct (Container (EqCmp v1 v2) fs lb sf ) ctns h

  | ST_EqCmp_result : forall h ct fs v1 v2 ctns sf lb result l' lb' lb'',
      value v1 ->
      value v2 ->
      ((runtime_val v1) = (runtime_val v2) -> result = B_true) ->
      ( (runtime_val v1) <> (runtime_val v2) -> result = B_false) ->
      l' = join_label (runtime_label v1) (runtime_label v2) ->
      lb' = join_label l' lb ->
      lb'' = join_label lb' (join_label (object_label (runtime_val v1) h)
                                        (object_label (runtime_val v2) h)) ->
                                       
      Config ct (Container (EqCmp v1 v2) fs lb sf ) ctns h 
      ==> Config ct (Container result fs lb'' sf) ctns h 
             
(* field read *)
  (* context rule *)
  | ST_fieldRead1 : forall sf h e f ct fs ctns lb,
      ~ value e ->
      Config ct (Container (FieldAccess e f) fs lb sf) ctns h ==> Config ct (Container e ((FieldAccess hole f) :: fs) lb sf) ctns h 
  | ST_fieldRead2 : forall sf h f ct fs v ctns lb,
      value v ->
      Config ct (Container v ((FieldAccess hole f) :: fs) lb sf) ctns h ==> Config ct (Container (FieldAccess v f) fs lb sf) ctns h 

  (* normal field access *)
  | ST_fieldRead3 : forall h o fname lo lb cls F v l'  ct fs ctns sf ll,
      Some (Heap_OBJ cls F lo ll) = lookup_heap_obj h o -> 
      Some v = F(fname) -> 
      l' = join_label lo lb ->
      Config ct (Container (FieldAccess (ObjId o) fname) fs lb sf) ctns h ==>
             Config ct (Container v nil (join_label l' ll) sf) ((Container (return_hole) fs lb sf ) :: ctns) h

  (* field access with opaque obj *)
  | ST_fieldRead4 : forall h o fname lo lb cls F v l'  ct fs ctns sf ell ll,
      Some (Heap_OBJ cls F lo ll) = lookup_heap_obj h o -> 
      Some v = F(fname) -> 
      l' = join_label (join_label lo lb) ell ->
      Config ct (Container (FieldAccess (v_opa_l (ObjId o) ell) fname) fs lb sf) ctns h ==>
             Config ct (Container v nil (join_label l' ll) sf) ((Container (return_hole) fs lb sf ) :: ctns) h
  
  (* null pointer exception for field access *)
  | ST_fieldReadException : forall h f ct fs sf ctns lb,
      Config ct (Container (FieldAccess null f) fs lb sf) ctns h ==> Error_state

  (* null pointer exception opaque for field access *)
  | ST_fieldReadExceptionOpaque : forall h f ct fs sf ctns lb ell,
      Config ct (Container (FieldAccess (v_opa_l null ell) f) fs lb sf) ctns h ==> Error_state
             

(* method call *)
  (* context rule: evaluate object target *)
  | ST_MethodCall1 : forall h e e2 id ct fs ctns sf lb,
      ~ value e ->
      Config ct (Container (MethodCall e id e2) fs lb sf) ctns h ==> Config ct (Container e ((MethodCall hole id e2) :: fs) lb sf) ctns h

  | ST_MethodCall2 : forall h e2 id ct fs v ctns sf lb,
      value v ->
      Config ct (Container v ((MethodCall hole id e2) :: fs) lb sf) ctns h ==> Config ct (Container (MethodCall v id e2) fs lb sf ) ctns h

  | ST_MethodCall3 : forall h e2 id ct fs v ctns sf lb,
      value v ->
      v <> null ->
      ~ value e2 ->
      Config ct (Container (MethodCall v id e2) fs lb sf) ctns h ==>
             Config ct (Container e2 ((MethodCall v id hole) :: fs) lb sf) ctns h
             
             
  | ST_MethodCall4 : forall h id ct fs v1 v2 ctns sf lb,
      value v1 ->
      value v2 ->
      Config ct (Container v2 ((MethodCall v1 id hole) :: fs) lb sf) ctns h ==> Config ct (Container (MethodCall v1 id v2) fs lb sf ) ctns h
             
  (* normal method call *)
  | ST_MethodCall_normal : forall o h cls fields v lo sf  arg_id cls_a body meth returnT ct fs ctns lb sf' ll,
      Some (Heap_OBJ cls fields lo ll) = lookup_heap_obj h o -> 
      Some (m_def returnT meth cls_a arg_id body) = find_method cls meth -> 
      value v ->
      sf' = sf_update empty_stack_frame arg_id v ->
      Config ct (Container (MethodCall (ObjId o) meth v) fs lb sf ) ctns h 
      ==> Config ct (Container body nil (join_label lb ll) sf' ) ((Container (return_hole) fs lb sf ) :: ctns) h

  (* normal method call opaque obj *)
  | ST_MethodCall_normal_opaque_obj : forall o h cls fields v lo sf  arg_id cls_a body meth returnT ct fs ctns lb sf' ell lb' ll,
      Some (Heap_OBJ cls fields lo ll) = lookup_heap_obj h o -> 
      Some (m_def returnT meth cls_a arg_id body) = find_method cls meth -> 
      value v ->
      sf' = sf_update empty_stack_frame arg_id v ->
      lb' = join_label lb ell ->
      Config ct (Container (MethodCall (v_opa_l (ObjId o) ell) meth v) fs lb sf ) ctns h 
             ==> Config ct (Container body nil (join_label lb' ll) sf' ) ((Container (return_hole) fs lb sf ) :: ctns) h

  (* null pointer exception for method call *)
  | ST_MethodCallException : forall h v meth ct fs lb sf  ctns,
      Config ct (Container (MethodCall null meth v) fs lb sf ) ctns h ==> Error_state

  (* null pointer exception opaque for method call *)
  | ST_MethodCallExceptionOpaque : forall h v meth ct fs lb sf ell ctns,
      value v ->
      Config ct (Container (MethodCall  (v_opa_l null ell) meth v) fs lb sf ) ctns h ==> Error_state
             

(* new expression *)
  | ST_NewExp : forall h h' o lb cls_name field_defs method_defs cls F ct fs ctns sf ,
      ct cls_name = Some cls -> 
      o = get_fresh_oid h ->
      cls = (class_def cls_name field_defs method_defs) ->
      F =  (init_field_map (find_fields cls) empty_field_map) ->
      h' = add_heap_obj h o (Heap_OBJ cls F lb lb) ->
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
      v <> null ->
      flow_to lb lo = true ->
      Config ct (Container (labelData v lo) fs lb sf) ctns h ==>  Config ct (Container (v_l v lo) fs lb sf) ctns h
  (* label data exception *)
  | ST_LabelDataException : forall h lb ct fs lo ctns sf,
      Config ct (Container (labelData null lo) fs lb sf) ctns h ==> Error_state
  | ST_LabelDataLeak : forall h v ct fs lb lo ctns sf,
      value v ->
      v <> null ->
      flow_to lb lo = false ->
      Config ct (Container (labelData v lo) fs lb sf) ctns h ==>  Error_state

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

  (* unlabel opaque *)
  | ST_unlabel4 : forall v lb l' h ct fs ctns sf ell,
      l' = join_label lb ell ->
      value (v_opa_l v ell) ->
      Config ct (Container (unlabel (v_opa_l v ell)) fs lb sf) ctns h ==>
             Config ct (Container (unlabel v) fs l' sf) ctns h
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

  | ST_labelof4 : forall v lb h ct fs ctns sf ell l',
      value (v_opa_l v ell) ->
      l' = join_label lb ell ->
      Config ct (Container (labelOf (v_opa_l v ell)) fs lb sf) ctns h ==>
             Config ct (Container (labelOf v) fs l' sf) ctns h           
  (* unlabel data exception *)
  | ST_labelOfDataException : forall h ct fs ctns sf lb,
      Config ct (Container (labelOf null) fs lb sf) ctns h ==> Error_state

(* objectLabelOf *)
  (* context rule *)
  | ST_objectlabelof1 : forall h e ct fs lb sf ctns,
      ~ value e ->
      Config ct (Container (objectLabelOf e) fs lb sf) ctns h ==> Config ct (Container e ((objectLabelOf hole) :: fs) lb sf) ctns h 
  | ST_objectlabelof2 : forall h ct fs v lb ctns sf,
      value v ->
      Config ct (Container v ((objectLabelOf hole) :: fs) lb sf) ctns h ==> Config ct (Container (objectLabelOf v) fs lb sf) ctns h 

  | ST_objectlabelof3 : forall h ct fs sf ctns cls F lb lo o ll,
      Some (Heap_OBJ cls F lo ll) = lookup_heap_obj h o ->
      Config ct (Container (objectLabelOf (ObjId o)) fs lb sf) ctns h ==>  Config ct (Container (l lo) fs (join_label ll lb) sf) ctns h

  | ST_objectlabelof4 : forall h ct fs sf ctns cls F lb lo o l' ell ll,
      Some (Heap_OBJ cls F lo ll) = lookup_heap_obj h o ->
      l' = join_label lb ell ->
      Config ct (Container (objectLabelOf (v_opa_l (ObjId o) ell)) fs lb sf) ctns h ==>  Config ct (Container (l lo) fs (join_label ll l') sf) ctns h
         
  (* objectlabelof exception *)
  | ST_objectlabelofException1 : forall h ct fs ctns sf lb,
      Config ct (Container (objectLabelOf null) fs lb sf) ctns h ==> Error_state
  | ST_objectlabelofException2 : forall h ct fs ctns sf lb ell,
      Config ct (Container (objectLabelOf (v_opa_l null ell)) fs lb sf) ctns h ==> Error_state
             
(* raise label of an object *)
  (* context rule *)
  | ST_raiseLabel1 : forall h e ct fs lb sf ctns lo,
      ~ value e ->
      Config ct (Container (raiseLabel e lo) fs lb sf) ctns h ==> Config ct (Container e ((raiseLabel hole lo) :: fs) lb sf) ctns h 
  | ST_raiseLabel2 : forall h ct fs v lb lo ctns sf,
      value v ->
      Config ct (Container v ((raiseLabel hole lo) :: fs) lb sf) ctns h ==> Config ct (Container (raiseLabel v lo) fs lb sf) ctns h

             (*
  | ST_raiseLabel_opa : forall h ct fs v lb lo ctns sf ell l',
      value v ->
      l' = join_label lb ell ->
      Config ct (Container (raiseLabel (v_opa_l v ell) lo) fs lb sf) ctns h  ==>
             Config ct (Container (raiseLabel v lo) fs l' sf) ctns h 
             *)

  | ST_raiseLabel3 : forall h ct fs sf ctns cls F lb lo lo' o h' ll,
      Some (Heap_OBJ cls F lo ll) = lookup_heap_obj h o -> 
      flow_to lb ll = true  ->
      flow_to lo lo' = true ->
      h' = update_heap_obj h o (Heap_OBJ cls F lo' ll) ->
      Config ct (Container (raiseLabel (ObjId o) lo') fs lb sf) ctns h ==>  Config ct (Container (Skip) fs lb sf) ctns h'

  | ST_raiseLabel4 : forall h ct fs sf ctns cls F lb lo lo' o h' ell ll,
      Some (Heap_OBJ cls F lo ll) = lookup_heap_obj h o -> 
      flow_to (join_label lb ell) ll = true  ->
      flow_to lo lo' = true ->
      h' = update_heap_obj h o (Heap_OBJ cls F lo' ll) ->
      Config ct (Container (raiseLabel (v_opa_l (ObjId o) ell) lo') fs lb sf) ctns h ==>  Config ct (Container (Skip) fs lb sf) ctns h'
             
             
  (*  raise label  exception *)
  | ST_raiseLabelException1 : forall h lb ct fs lo ctns sf,
      Config ct (Container (raiseLabel null lo) fs lb sf) ctns h ==> Error_state

  | ST_raiseLabelException4 : forall h lb ct fs lo ctns sf ell,
      Config ct (Container (raiseLabel (v_opa_l null ell) lo) fs lb sf) ctns h ==> Error_state
  | ST_raiseLabelException2 : forall h lb ct fs o ctns sf lo' cls F lo ll,
      Some (Heap_OBJ cls F lo ll) = lookup_heap_obj h o -> 
      (flow_to lb ll = false \/ 
      flow_to lo lo' = false ) ->
      Config ct (Container (raiseLabel (ObjId o) lo') fs lb sf) ctns h ==>  Error_state
  | ST_raiseLabelException3 : forall h lb ct fs o ctns sf lo' cls F lo ell ll,
      Some (Heap_OBJ cls F lo ll) = lookup_heap_obj h o -> 
      (flow_to (join_label lb ell) ll = false \/ 
      flow_to lo lo' = false ) ->
      Config ct (Container (raiseLabel (v_opa_l (ObjId o) ell) lo') fs lb sf) ctns h ==>  Error_state


  (* toLabeled  *)           
  | ST_toLabeled1 : forall h e1 e2 ct fs lb sf ctns,
      ~ value e2 ->
      Config ct (Container (toLabeled e1 e2) fs lb sf) ctns h ==> Config ct (Container e2 ((toLabeled e1 hole) :: fs) lb sf) ctns h 
  | ST_toLabeled2 : forall h e1 v ct fs lb sf ctns,
      value v ->
     Config ct (Container v ((toLabeled e1 hole) :: fs) lb sf) ctns h ==> Config ct (Container (toLabeled e1 v) fs lb sf) ctns h
  | ST_toLabeled3 : forall h e1 lo ct fs lb sf ctns,
      Config ct (Container (toLabeled e1 (l lo)) fs lb sf) ctns h
             ==> Config ct (Container e1 ((labelData hole lo)::nil) lb sf) ((Container (return_hole) fs lb sf ) :: ctns) h
  | ST_toLabeled4 : forall h e1 ct fs lb sf ctns ell v,
      value (v_opa_l v ell) ->
      Config ct (Container (toLabeled e1 (v_opa_l v ell)) fs lb sf) ctns h
             ==> Config ct (Container (toLabeled e1 v) fs (join_label lb ell) sf) ctns h
  |  ST_toLabeledException : forall h ct fs ctns sf lb e,
      Config ct (Container (toLabeled e null) fs lb sf) ctns h ==> Error_state

  (*getCurrentLevel *)
  |  ST_getCurrentLevel : forall h ct fs ctns sf lb,
      Config ct (Container getCurrentLevel fs lb sf) ctns h ==>  Config ct (Container (l lb) fs lb sf) ctns h      
             
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
  | ST_fieldWrite3 : forall h v e2 f ct fs ctns sf lb,
      value v -> ~ value e2 ->
      v <> null ->
      Config ct (Container (FieldWrite v f e2) fs lb sf ) ctns h==> Config ct (Container e2 ((FieldWrite v f hole) :: fs) lb sf) ctns h
  | ST_fieldWrite4 : forall h v1 v2 f ct fs lb sf ctns, 
      value v2 ->
      value v1 ->
      Config ct (Container v2 ((FieldWrite v1 f hole) :: fs) lb sf ) ctns h ==> Config ct (Container (FieldWrite v1 f v2) fs lb sf ) ctns h 
             
  (* normal field write *)
  | ST_fieldWrite_normal : forall o h h' f lo lb cls F F' v ct fs ctns sf ll,
      Some (Heap_OBJ cls F lo ll) = lookup_heap_obj h o -> 
      F' = fields_update F f (runtime_val v) ->
      flow_to (join_label (runtime_label v) lb) (join_label lo ll) = true -> 
      h' = update_heap_obj h o (Heap_OBJ cls F' lo ll) ->
      value v ->
    Config ct (Container (FieldWrite (ObjId o) f v) fs lb sf ) ctns h 
           ==> Config ct (Container Skip fs lb sf ) ctns h'

  (* normal field write opaque obj *)
  | ST_fieldWrite_normal_opa_obj : forall o h f lo lb cls F F' v ct fs ctns sf lb' ell ll,
      Some (Heap_OBJ cls F lo ll) = lookup_heap_obj h o -> 
      F' = fields_update F f (runtime_val v) ->
      lb' = (join_label ell lb) ->
      value v ->
    Config ct (Container (FieldWrite (v_opa_l (ObjId o) ell) f v) fs lb sf ) ctns h 
           ==> Config ct (Container (FieldWrite (ObjId o) f v) fs lb' sf ) ctns h

  (* normal field information leak *)
  | ST_fieldWrite_leak : forall o h f lo lb cls F v ct fs ctns sf ll,
      Some (Heap_OBJ cls F lo ll) = lookup_heap_obj h o ->
      flow_to (join_label (runtime_label v) lb) (join_label lo ll) = false -> 
      value v ->
    Config ct (Container (FieldWrite (ObjId o) f v) fs lb sf ) ctns h 
           ==>  Error_state

  (* null pointer exception for field write *)
  | ST_FieldWrite_Exception : forall h v f ct fs lb sf  ctns,
      Config ct (Container (FieldWrite null f v) fs lb sf ) ctns h ==> Error_state

 (* null pointer exception opaque *)
  | ST_FieldWrite_ExceptionOpaque : forall h v f ct fs lb sf ell  ctns,
      value v ->
      Config ct (Container (FieldWrite (v_opa_l null ell) f v) fs lb sf ) ctns h ==> Error_state
             
  (* if statement *)
  | ST_if_guard : forall s1 s2 h lb guard ct fs ctns sf, 
       ~ value guard -> 
       Config ct (Container (If guard s1 s2) fs lb sf) ctns h ==> Config ct (Container guard ((If hole s1 s2) :: fs) lb sf) ctns h

  | ST_if_guard_return : forall s1 s2 h lb guard ct fs ctns sf, 
       (value guard) -> 
       Config ct (Container guard ((If hole s1 s2) :: fs) lb sf) ctns h ==>
              Config ct (Container (If guard s1 s2)  fs lb sf) ctns h
  | ST_if_guard_opa : forall s1 s2 h lb guard ct fs ctns sf ell, 
       (value (v_opa_l guard ell)) -> 
        Config ct (Container (If (v_opa_l guard ell) s1 s2) fs lb sf) ctns h ==>
           Config ct (Container (If guard s1 s2) fs (join_label lb ell) sf) ctns h
  | ST_if_b1 : forall s1 s2 h lb ct fs ctns sf, 
       Config ct (Container (If B_true s1 s2) fs lb sf) ctns h ==> Config ct (Container s1 fs lb sf) ctns h
  | ST_if_b2 : forall s1 s2 h lb ct fs ctns sf, 
      Config ct (Container (If B_false s1 s2) fs lb sf) ctns h ==> Config ct (Container s2 fs lb sf) ctns h
  | ST_if_exception : forall s1 s2 h lb ct fs ctns sf, 
       Config ct (Container (If null s1 s2) fs lb sf) ctns h ==> Error_state
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

  | ST_val_return_obj : forall h ct ctns sf lb' sf' fs' v lb,
      (*ctn must have return_hole*)
      value v ->
      (forall v0 ell, value v0 -> v <> (v_opa_l v0 ell))  ->
    Config ct (Container v nil lb sf) ((Container return_hole fs' lb' sf') :: ctns) h 
           ==> Config ct (Container (v_opa_l v lb) fs' lb' sf') ctns h
           
  | ST_val_return_obj_ell : forall h ct ctns sf lb lb' sf' fs' ell v,
    (*ctn must have return_hole*)
    Config ct (Container (v_opa_l v ell) nil lb sf) ((Container return_hole fs' lb' sf') :: ctns) h 
           ==> Config ct (Container (v_opa_l v (join_label ell lb)) fs' lb' sf') ctns h

where "c '==>' c'" := (reduction c c').
Hint Constructors reduction. 


Hint Constructors valid_syntax.



Definition compare_oid (o1 : oid) (o2 : oid) :=
  match o1, o2 with 
      | OID n1, OID n2 => if (gt_dec n1  n2) then true else false
  end.

Inductive wfe_heap : Class_table -> heap -> Prop :=
  | empty_heap_wfe : forall ct, 
        wfe_heap ct  nil
  | heap_wfe : forall h h' o cls_def F ct cn ho lo method_defs field_defs ll,
        h' = (o , ho) :: h ->
        (h = nil \/ (exists o' ho' h'', h = (o' , ho') :: h'' /\ compare_oid o o' = true) ) ->
        wfe_heap ct h ->
        ho = (Heap_OBJ cls_def F lo ll) ->
        Some cls_def  = ct cn ->
        cls_def = class_def cn field_defs method_defs ->
        wfe_heap ct h'.

Inductive field_wfe_heap : Class_table -> heap -> Prop :=
  | heap_wfe_fields : forall h ct, 
        (forall o cls_def F cls_name lo method_defs field_defs ll,
        lookup_heap_obj  h o = Some (Heap_OBJ cls_def F lo ll) ->
        Some cls_def  = ct cls_name ->
        cls_def = class_def cls_name field_defs method_defs ->
        (forall f cls', type_of_field field_defs f = Some cls' -> 
                exists v, F(f) = Some v
                 /\ (v= null  \/ 
                          ( exists o' F' lx field_defs0 method_defs0 llx, v = ObjId o' 
                                  /\ lookup_heap_obj  h o' = Some (Heap_OBJ (class_def cls' field_defs0 method_defs0) F' lx llx)
                                    /\ ct cls' = Some (class_def cls' field_defs0 method_defs0)
                          ) ) 
        ))->
        field_wfe_heap ct h.

Inductive wfe_stack_val : Class_table -> heap -> tm -> Prop :=
| stack_val_null : forall ct h,
    wfe_stack_val ct h null
| stack_val_object : forall ct h  o cls_name F lo field_defs method_defs ll,
      lookup_heap_obj h o = 
      Some (Heap_OBJ (class_def cls_name field_defs method_defs) F lo ll) ->
      (ct cls_name = Some (class_def cls_name field_defs method_defs)) ->
      wfe_stack_val ct h (ObjId o)
| stack_val_labeled : forall ct h  v lb,
    wfe_stack_val ct h v ->
    wfe_stack_val ct h (v_l v lb)
| stack_val_opa_labeled : forall ct h  v lb,
    wfe_stack_val ct h v ->
    wfe_stack_val ct h (v_opa_l v lb)
| stack_val_label : forall ct h lb,
    wfe_stack_val ct h (l lb)
| stack_val_true : forall ct h,
    wfe_stack_val ct h (B_true)                 
| stack_val_false : forall ct h,
    wfe_stack_val ct h (B_false)
.
Hint Constructors wfe_stack_val. 
               

(* be careful with this *)
Inductive wfe_stack_frame : Class_table -> heap -> stack_frame -> Prop :=
  | stack_frame_wfe : forall h sf ct,
      (forall x v,
          sf x = Some v  ->
          value v /\
          wfe_stack_val ct h v
      ) ->
        wfe_stack_frame ct h sf.
Hint Constructors wfe_stack_frame.


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
      t <> hole ->
      t <> return_hole ->
      valid_fs (t :: fs).
Hint Constructors valid_fs. 


Inductive valid_ctn : Class_table ->container -> heap -> Prop:= 
  | valid_container : forall t fs lb sf h ct, 
     valid_fs fs ->
     valid_syntax t ->
     (forall fs', fs <> hole :: fs') ->
     (forall fs', fs <> return_hole :: fs') ->
     wfe_stack_frame ct h sf ->
     valid_ctn ct (Container t fs lb sf) h.
Hint Constructors valid_ctn. 

Inductive valid_ctns : Class_table ->  list container -> heap ->  Prop:= 
| valid_ctns_nil : forall ct h,
    valid_ctns ct nil h
| valid_ctns_list : forall ct ctn ctns h, 
    valid_ctn ct ctn h->
    valid_ctns ct ctns h ->
    valid_ctns ct (ctn :: ctns) h.
Hint Constructors valid_ctns. 

Inductive valid_config : config -> Prop :=
  | valid_conf : forall ct t fs lb sf ctns h, 
    valid_ctns ct ctns h ->
    valid_ctn ct (Container t fs lb sf) h ->
    hole_free t = true ->
    wfe_heap ct h -> field_wfe_heap ct h ->
    (*wfe_stack_frame CT h sf ->*)
    valid_config (Config ct (Container t fs lb sf) ctns h). 
Hint Constructors valid_config. 

Inductive multi_step_reduction : config -> config -> Prop := 
  | multi_reduction_refl : forall config , multi_step_reduction config config
  | multi_reduction_step : forall c1 c2 c3, 
                    reduction c1 c2 ->
                    multi_step_reduction c2 c3 ->
                    multi_step_reduction c1 c3.

Notation "c1 '==>*' c2" := (multi_step_reduction c1 c2) (at level 40).
 