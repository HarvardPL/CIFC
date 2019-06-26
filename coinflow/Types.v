Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.

Require Import Label Language.

Inductive funTy : Type :=
  | ArrowTy : ty -> ty -> funTy. 

Definition typing_context := id -> (option ty).
Definition empty_context : typing_context := fun _ => None.

Definition update_typing (gamma : typing_context) (x:id) (T : ty) : typing_context :=
      fun x' => if beq_id x x' then (Some T) else gamma x. 


Definition empty_heap : heap := nil.


Inductive tm_has_type : Class_table -> typing_context -> heap -> tm -> ty -> Prop :=
(*variable *)
  | T_Var : forall Gamma x T CT h , 
      Gamma x = Some T ->
      tm_has_type CT Gamma h (Tvar x) T
  | T_EqCmp : forall Gamma e1 e2 clsT h CT,
      tm_has_type CT Gamma h e1 (classTy clsT) ->
      tm_has_type CT Gamma h e2 (classTy clsT) ->
      (exists cls_def field_defs method_defs, CT clsT = Some cls_def /\
              cls_def = class_def clsT field_defs method_defs) ->
      tm_has_type CT Gamma h (EqCmp e1 e2) boolTy
(* null *)
  | T_null : forall Gamma h cls CT, 
      tm_has_type CT Gamma h null (classTy cls)
(* Field read *)
  | T_FieldAccess : forall Gamma e f cls_def CT clsT cls' h fields_def,
      tm_has_type CT Gamma h e (classTy clsT) ->
      Some cls_def = CT(clsT) ->
      fields_def = (find_fields cls_def) ->
      type_of_field fields_def f = Some cls' ->
      tm_has_type CT Gamma h (FieldAccess e f) (classTy cls')
(* method call *)
  | T_MethodCall : forall Gamma  e meth argu CT h T returnT cls_def body arg_id arguT,
      tm_has_type CT Gamma h e (classTy T) ->
      tm_has_type CT Gamma h argu arguT ->
      Some cls_def = CT(T) ->
      find_method cls_def meth = Some (m_def returnT meth arguT arg_id  body)  ->
      surface_syntax body = true ->
      tm_has_type CT Gamma h (MethodCall e meth argu) returnT
(* new exp *)
  | T_NewExp : forall h Gamma cls_name CT, 
      (exists cls_def field_defs method_defs, CT cls_name = Some cls_def /\
              cls_def = class_def cls_name field_defs method_defs) ->
      tm_has_type CT Gamma h (NewExp cls_name) (classTy cls_name)

(* booleans  *)                         
  | T_true : forall h Gamma CT,
      tm_has_type CT Gamma h B_true boolTy
  | T_false : forall h Gamma CT,
      tm_has_type CT Gamma h B_false boolTy                 
(* label *)
  | T_label : forall h Gamma lb CT,
      tm_has_type CT Gamma h (l lb) LabelTy
(* label data *)
  | T_labelData : forall h Gamma  CT e1 e2 T,
      tm_has_type CT Gamma h e2 LabelTy ->
      tm_has_type CT Gamma h e1 T ->
      tm_has_type CT Gamma h (labelData e1 e2) (LabelelTy T)
(* unlabel *)
  | T_unlabel : forall h Gamma CT e T,
      tm_has_type CT Gamma h e (LabelelTy T) ->
      tm_has_type CT Gamma h (unlabel e) T
(* labelOf *)
  | T_labelOf : forall h Gamma CT e T,
      tm_has_type CT Gamma h e (LabelelTy T) ->
      tm_has_type CT Gamma h (labelOf e) LabelTy


(* objectLabelOf *)
  | T_objectLabelOf : forall h Gamma CT e clsT,
      tm_has_type CT Gamma h e  (classTy clsT)  ->
      (exists cls_def field_defs method_defs, CT clsT = Some cls_def /\
              cls_def = class_def clsT field_defs method_defs) ->
      tm_has_type CT Gamma h (objectLabelOf e) LabelTy
                  
(* raise label *)
  | T_raiseLabel : forall h Gamma CT e1 e2 clsT,
      tm_has_type CT Gamma h e2 LabelTy ->
      tm_has_type CT Gamma h e1 (classTy clsT) ->
      (exists cls_def field_defs method_defs, CT clsT = Some cls_def /\
              cls_def = class_def clsT field_defs method_defs) ->
      tm_has_type CT Gamma h (raiseLabel e1 e2) (classTy clsT)
(* toLabeled *)
  | T_toLabeled : forall h Gamma v CT e T,
      tm_has_type CT Gamma h v LabelTy ->
      tm_has_type CT Gamma h e T ->
      tm_has_type CT Gamma h (toLabeled e v) (LabelelTy T)
(* getCurrentLevel *)
  | T_getCurrentLevel : forall h Gamma CT,
      tm_has_type CT Gamma h (getCurrentLevel) LabelTy                  
(* assignment *)
  | T_assignment : forall h Gamma CT e T x, 
      Gamma x = Some T ->
      tm_has_type CT Gamma h e T ->
      tm_has_type CT Gamma h (Assignment x e) T
(* Field Write *)
  | T_FieldWrite : forall h Gamma x f cls_def CT clsT cls' e,
      tm_has_type CT Gamma h x (classTy clsT) ->
      tm_has_type CT Gamma h e (classTy cls') ->
      Some cls_def = CT(clsT) ->
      type_of_field (find_fields cls_def) f = Some cls' ->
      tm_has_type CT Gamma h (FieldWrite x f e)  (classTy cls')
(* if *)
  | T_if : forall Gamma h CT guard s1 s2 T' ,
      tm_has_type CT Gamma h guard boolTy ->
      tm_has_type CT Gamma h s1 T' ->
      tm_has_type CT Gamma h s2 T' ->
      tm_has_type CT Gamma h (If guard s1 s2) T'
(* sequence *)
  | T_sequence : forall h Gamma CT e1 e2 T T',
      tm_has_type CT Gamma h e1 T ->
      tm_has_type CT Gamma h e2 T' ->
      tm_has_type CT Gamma h (Sequence e1 e2) T'

(* ObjId *)
  | T_ObjId : forall h Gamma CT o cls_name cls_def,
      Some cls_def = CT(cls_name) ->
      (exists field_defs method_defs, cls_def = (class_def cls_name field_defs method_defs)) ->
      (exists F lo ll, lookup_heap_obj h o = Some (Heap_OBJ cls_def F lo ll)) ->
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
      value  v  ->
      (forall v0 lb0, v <> v_opa_l v0 lb0 ) ->
      tm_has_type CT Gamma h (v_opa_l v lb)  T.
(* hole *)
(*  | T_hole : forall h Gamma CT T,
      tm_has_type CT Gamma h hole T.
 *)
Hint Constructors tm_has_type.

Inductive tm_hole_has_type : Class_table -> typing_context -> heap -> tm -> funTy -> Prop :=
                       
  | T_EqCmp1 : forall e1 e2 Gamma clsT CT h,
      tm_has_type CT Gamma h e1 (classTy clsT) ->
      tm_has_type CT Gamma h e2 (classTy clsT) ->
      (exists cls_def field_defs method_defs, CT clsT = Some cls_def /\
              cls_def = class_def clsT field_defs method_defs) ->
      tm_has_type CT Gamma h (EqCmp e1 e2) boolTy ->
      tm_hole_has_type CT Gamma h (EqCmp hole e2) (ArrowTy (classTy clsT) boolTy) 
  | T_EqCmp2 : forall e1 e2 Gamma clsT CT h,
      tm_has_type CT Gamma h e1 (classTy clsT) ->
      tm_has_type CT Gamma h e2 (classTy clsT) ->
      (exists cls_def field_defs method_defs, CT clsT = Some cls_def /\
              cls_def = class_def clsT field_defs method_defs) ->
      tm_has_type CT Gamma h (EqCmp e1 e2) boolTy ->
      tm_hole_has_type CT Gamma h (EqCmp e1 hole) (ArrowTy (classTy clsT) boolTy)
                       
  | T_hole_FieldAccess : forall  Gamma f cls_def CT clsT cls' h fields_def,
      (*
      tm_has_type CT Gamma h (FieldAccess e f) (classTy cls') ->
      tm_has_type CT Gamma h e (classTy clsT) ->
       *)
      Some cls_def = CT(clsT) ->
      fields_def = (find_fields cls_def) ->
      type_of_field fields_def f = Some cls' ->
      tm_hole_has_type CT Gamma h (FieldAccess hole f) (ArrowTy (classTy clsT) (classTy cls'))
                  
  | T_hole_MethodCall1 : forall Gamma  meth argu CT h T returnT cls_def body arg_id arguT,
      (* tm_has_type CT Gamma h (MethodCall e meth argu) (OpaqueLabeledTy (classTy returnT)) ->
      tm_has_type CT Gamma h e (classTy T) ->  *)
      tm_has_type CT Gamma h argu arguT ->
      Some cls_def = CT(T) ->
      find_method cls_def meth = Some (m_def returnT meth arguT arg_id  body)  ->
      surface_syntax body = true ->
      tm_hole_has_type CT Gamma h (MethodCall hole meth argu) (ArrowTy (classTy T)
                                                                       returnT)
                  
  | T_hole_MethodCall2 : forall Gamma  e meth CT h T returnT cls_def body arg_id arguT,
      (* tm_has_type CT Gamma h (MethodCall e meth argu) (OpaqueLabeledTy (classTy returnT)) ->
      tm_has_type CT Gamma h argu (classTy arguT) -> *)
      tm_has_type CT Gamma h e (classTy T) ->
      Some cls_def = CT(T) ->
      find_method cls_def meth = Some (m_def returnT meth arguT arg_id  body)  ->
      surface_syntax body = true ->
      tm_hole_has_type CT Gamma h (MethodCall e meth hole) (ArrowTy (arguT)
                                                                    ( returnT))


  | T_hole_labelData1 : forall h Gamma CT T e2 , 
      (* tm_has_type CT Gamma h (labelData e lb) (LabelelTy T) -> *)
      tm_has_type CT Gamma h e2 LabelTy ->
      tm_hole_has_type CT Gamma h (labelData hole e2) (ArrowTy T (LabelelTy T))

  | T_hole_labelData2 : forall h Gamma CT T v,
      value v ->
      tm_has_type CT Gamma h v T ->
      tm_hole_has_type CT Gamma h (labelData v hole) (ArrowTy LabelTy (LabelelTy T))

  (*unlabel data*)
  | T_hole_unlabel : forall h Gamma CT T, 
      (* tm_has_type CT Gamma h (unlabel e) T -> *)
      tm_hole_has_type CT Gamma h (unlabel hole) (ArrowTy (LabelelTy T) T)
  (*labelOf data*)
  | T_hole_labelOf : forall h Gamma CT  T, 
      (* tm_has_type CT Gamma h (labelOf e) LabelTy -> *)
      tm_hole_has_type CT Gamma h (labelOf hole) (ArrowTy ( (LabelelTy T)) LabelTy)

  (* objectLabelOf *)
  | T_hole_objectLabelOf : forall h Gamma CT  clsT, 
      (exists cls_def field_defs method_defs, CT clsT = Some cls_def /\
              cls_def = class_def clsT field_defs method_defs) ->
      tm_hole_has_type CT Gamma h (objectLabelOf hole) (ArrowTy (classTy clsT) LabelTy)
                       
  | T_hole_raiseLabel1 : forall  Gamma e2  CT clsT h,
      tm_has_type CT Gamma h e2 LabelTy ->
      (exists cls_def field_defs method_defs, CT clsT = Some cls_def /\
              cls_def = class_def clsT field_defs method_defs) ->
      tm_hole_has_type CT Gamma h (raiseLabel hole e2) (ArrowTy (classTy clsT) (classTy clsT))

  | T_hole_raiseLabel2 : forall  Gamma e1  CT clsT h,
      tm_has_type CT Gamma h e1 (classTy clsT) ->
       (exists cls_def field_defs method_defs, CT clsT = Some cls_def /\
              cls_def = class_def clsT field_defs method_defs) ->
      tm_hole_has_type CT Gamma h (raiseLabel e1 hole) (ArrowTy LabelTy (classTy clsT))

  | T_hole_toLabeled : forall h Gamma CT T e ,
      tm_has_type CT Gamma h e T ->
      tm_hole_has_type CT Gamma h (toLabeled e hole) (ArrowTy LabelTy (LabelelTy T))
                       
(* assignment *)
  | T_hole_assignment : forall h Gamma CT  T x , 
      (* tm_has_type CT Gamma h (Assignment x e) voidTy -> *)
      Gamma x = Some T ->
      tm_hole_has_type CT Gamma h (Assignment x hole) (ArrowTy T T)

  (* sequence *)
  | T_hole_sequence : forall h Gamma CT  T T' s2, 
      tm_has_type CT Gamma h s2 T ->
      tm_hole_has_type CT Gamma h (Sequence hole s2) (ArrowTy T' T)

(* if *)
  | T_hole_if : forall h Gamma CT s1 s2 T,
      tm_has_type CT Gamma h s1 T ->
      tm_has_type CT Gamma h s2 T ->
      tm_hole_has_type CT Gamma h (If hole s1 s2) (ArrowTy boolTy T)
 
                  
(* Field Write *)
  | T_hole_FieldWrite1 : forall  h Gamma f cls_def CT clsT cls' e,
      (*tm_has_type CT Gamma h (FieldWrite x f e) voidTy ->
       tm_has_type CT Gamma h x (classTy clsT) -> *)
      tm_has_type CT Gamma h e (classTy cls') ->
      Some cls_def = CT(clsT) ->
      type_of_field (find_fields cls_def) f = Some cls' ->
      tm_hole_has_type CT Gamma h (FieldWrite hole f e) (ArrowTy (classTy clsT) (classTy cls'))
  | T_hole_FieldWrite2 : forall  h Gamma x f cls_def CT clsT cls',
      tm_has_type CT Gamma h x (classTy clsT) ->
      Some cls_def = CT(clsT) ->
      type_of_field (find_fields cls_def) f = Some cls' ->
      tm_hole_has_type CT Gamma h (FieldWrite x f hole) (ArrowTy (classTy cls') (classTy cls') ).                 
Hint Constructors tm_hole_has_type. 

Inductive fs_has_type : Class_table -> typing_context -> heap -> list tm -> funTy -> Prop :=
  | T_fs_nil : forall h Gamma CT T, 
      fs_has_type CT Gamma h nil (ArrowTy T T)
  | T_fs_hole : forall h Gamma CT T T' top fs T1,  
      hole_free top  = false ->
      tm_hole_has_type CT Gamma h top ((ArrowTy T T')) ->
      fs_has_type CT Gamma h (fs) (ArrowTy T' T1) ->
      fs_has_type CT Gamma h (top :: fs) (ArrowTy T T1).

  (*
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
*) 
Hint Constructors fs_has_type.

Inductive well_typed_stack_frame : Class_table -> typing_context ->
                           stack_frame -> heap -> Prop :=
| well_typed_sf : forall ct gamma sf  h,
    (forall x T, gamma x = Some T ->
    exists v, sf x = Some v /\
    tm_has_type ct gamma h v T) ->
    well_typed_stack_frame ct gamma sf h.
Hint Constructors well_typed_stack_frame.

Inductive ctn_has_type : Class_table -> typing_context -> heap -> container -> funTy -> Prop :=
    | T_ctn_type : forall h Gamma CT T lb fs open_t sf T', 
        tm_has_type CT Gamma h open_t T ->
        well_typed_stack_frame CT Gamma sf h ->
        fs_has_type CT Gamma h fs (ArrowTy T T')  ->
        ctn_has_type CT Gamma h (Container open_t fs lb sf) (ArrowTy T T').
Hint Constructors ctn_has_type. 


Inductive ctn_list_has_type : Class_table -> typing_context -> heap -> list container -> funTy -> Prop := 
  | T_ctn_nil : forall h Gamma CT T , 
      ctn_list_has_type CT Gamma h nil (ArrowTy T T)
  | T_ctn_list : forall h Gamma CT T0 T1 T' Gamma' ctn ctns', 
      ctn_has_type CT Gamma' h ctn (ArrowTy T0 T1) ->
      ctn_list_has_type CT Gamma h ctns' (ArrowTy  T1 T') ->
      ctn_list_has_type CT Gamma h (ctn :: ctns')  (ArrowTy T0 T').                        
Hint Constructors ctn_list_has_type. 

  Inductive well_typed_class_table : Class_table -> Prop :=
  | well_typed_CT : forall CT, 
      (forall clsT cls_def field_defs method_defs,
      CT clsT = Some cls_def -> 
      cls_def = class_def clsT field_defs method_defs ->
      (forall gamma h returnT meth arguT arg_id  body ,
          Some (m_def returnT meth arguT arg_id body) = find_method cls_def meth -> 
          (gamma = update_typing empty_context arg_id arguT) ->
          (tm_has_type CT gamma h body returnT)
      )) ->
      well_typed_class_table CT.
  Hint Constructors well_typed_class_table. 

Inductive config_has_type : Class_table -> typing_context -> config -> ty -> Prop :=
  | T_config_ctns : forall h Gamma CT T T' T0 ctn ctns Gamma', 
      ctn_has_type CT Gamma' h ctn (ArrowTy T0 T) ->
      ctn_list_has_type CT Gamma h ctns (ArrowTy T T') ->
      well_typed_class_table CT ->
      config_has_type CT Gamma (Config CT ctn ctns h) T'.
Hint Constructors config_has_type. 

Hint Constructors ctn_list_has_type. 
Hint Constructors ctn_has_type.
Hint Constructors fs_has_type.
