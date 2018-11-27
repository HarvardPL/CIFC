Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.

Require Import Label Language.

Inductive ty : Type :=
  | classTy : cn -> ty
  | boolTy : ty                  
  | LabelTy : ty
  | LabelelTy : ty -> ty
  | OpaqueLabeledTy : ty -> ty
  | voidTy : ty
  | ArrowTy : ty -> ty -> ty.


Definition typing_context := id -> (option ty).
Definition empty_context : typing_context := fun _ => None.

Definition update_typing (gamma : typing_context) (x:id) (T : ty) : typing_context :=
      fun x' => if beq_id x x' then (Some T) else gamma x. 


Definition empty_heap : heap := nil.



Inductive tm_has_type : Class_table -> typing_context -> heap -> tm -> ty -> Prop :=
(*variable *)
  | T_Var : forall Gamma x T CT h , 
      Gamma x = Some (classTy T) ->
      tm_has_type CT Gamma h (Tvar x) (classTy T)
  | T_EqCmp : forall Gamma e1 e2 clsT h CT,
      tm_has_type CT Gamma h e1 (classTy clsT) ->
      tm_has_type CT Gamma h e2 (classTy clsT) ->
      (exists cls_def field_defs method_defs, CT clsT = Some cls_def /\
              cls_def = class_def clsT field_defs method_defs) ->
      tm_has_type CT Gamma h (EqCmp e1 e2) boolTy
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

(* booleans  *)                         
  | T_true : forall h Gamma CT,
      tm_has_type CT Gamma h B_true boolTy
  | T_false : forall h Gamma CT,
      tm_has_type CT Gamma h B_false boolTy                 
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
      T <> voidTy ->
      tm_has_type CT Gamma h (unlabel e) T
(* labelOf *)
  | T_labelOf : forall h Gamma CT e T,
      tm_has_type CT Gamma h e (LabelelTy T) ->
      T <> voidTy ->
      tm_has_type CT Gamma h (labelOf e) LabelTy
(* unlabel opaque *)
  | T_unlabelOpaque : forall h Gamma CT e T,
      tm_has_type CT Gamma h e (OpaqueLabeledTy T) ->
      T <> voidTy ->
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
      (exists F lo, lookup_heap_obj h o = Some (Heap_OBJ cls_def F lo)) ->
      tm_has_type CT Gamma h (ObjId o) (classTy cls_name)
(* runtime labeled data *)
  | T_v_l : forall h Gamma lb CT v T,
      tm_has_type CT Gamma h (l lb)  LabelTy ->
      tm_has_type CT Gamma h v  T ->
      T <> voidTy ->
      value v ->
      tm_has_type CT Gamma h (v_l v lb) (LabelelTy T)
(* runtime labeled data *)
  | T_v_opa_l : forall h Gamma lb CT v T,
      tm_has_type CT Gamma h (l lb)  LabelTy ->
      tm_has_type CT Gamma h v  T ->
      T <> voidTy ->
      value v ->
      tm_has_type CT Gamma h (v_opa_l v lb) (OpaqueLabeledTy T)
(* hole *)
  | T_hole : forall h Gamma CT T,
      tm_has_type CT Gamma h hole T.
Hint Constructors tm_has_type.

Inductive tm_hole_has_type : Class_table -> typing_context -> heap -> tm -> ty -> Prop :=
  
(* all terms with hole*)
  |T_return_hole : forall h Gamma T CT,
      tm_hole_has_type CT Gamma h return_hole (ArrowTy T (OpaqueLabeledTy T))
                       
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
                  
  | T_hole_MethodCall1 : forall Gamma Gamma'  meth argu CT h T returnT cls_def body arg_id arguT,
      (* tm_has_type CT Gamma h (MethodCall e meth argu) (OpaqueLabeledTy (classTy returnT)) ->
      tm_has_type CT Gamma h e (classTy T) ->  *)
      tm_has_type CT Gamma h argu (classTy arguT) ->
      Some cls_def = CT(T) ->
      find_method cls_def meth = Some (m_def returnT meth arguT arg_id  body)  ->
      Gamma' = update_typing empty_context arg_id (classTy arguT) ->
      tm_has_type CT Gamma' h (body) (classTy returnT) ->
      surface_syntax body = true ->
      tm_hole_has_type CT Gamma h (MethodCall hole meth argu) (ArrowTy (classTy T)
                                                                       (OpaqueLabeledTy (classTy returnT)))
                  
  | T_hole_MethodCall2 : forall Gamma Gamma' e meth CT h T returnT cls_def body arg_id arguT,
      (* tm_has_type CT Gamma h (MethodCall e meth argu) (OpaqueLabeledTy (classTy returnT)) ->
      tm_has_type CT Gamma h argu (classTy arguT) -> *)
      tm_has_type CT Gamma h e (classTy T) ->
      Some cls_def = CT(T) ->
      find_method cls_def meth = Some (m_def returnT meth arguT arg_id  body)  ->
      Gamma' = update_typing empty_context arg_id (classTy arguT) ->
      tm_has_type CT Gamma' h (body) (classTy returnT) ->
      surface_syntax body = true ->
      tm_hole_has_type CT Gamma h (MethodCall e meth hole) (ArrowTy (classTy arguT)
                                                                    (OpaqueLabeledTy (classTy returnT)))
(*newly added rule*)
  | T_hole_MethodCall3 : forall Gamma Gamma' e meth  CT h T returnT cls_def body arg_id arguT,
      (* tm_has_type CT Gamma h (MethodCall e meth argu) (OpaqueLabeledTy (classTy returnT)) ->
      tm_has_type CT Gamma h argu (classTy arguT) -> *)
      tm_has_type CT Gamma h e (classTy T) ->
      Some cls_def = CT(T) ->
      find_method cls_def meth = Some (m_def returnT meth arguT arg_id  body)  ->
      Gamma' = update_typing empty_context arg_id (classTy arguT) ->
      tm_has_type CT Gamma' h (body) (classTy returnT) ->
      surface_syntax body = true ->
      tm_hole_has_type CT Gamma h (MethodCall e meth (unlabelOpaque hole)) (ArrowTy (OpaqueLabeledTy (classTy arguT))
                                                                    (OpaqueLabeledTy (classTy returnT)))

  | T_hole_labelData : forall h Gamma CT T lb , 
      (* tm_has_type CT Gamma h (labelData e lb) (LabelelTy T) -> *)
      T <> voidTy ->
      tm_hole_has_type CT Gamma h (labelData hole lb) (ArrowTy T (LabelelTy T))

  (*unlabel data*)
  | T_hole_unlabel : forall h Gamma CT T, 
      (* tm_has_type CT Gamma h (unlabel e) T -> *)
      T <> voidTy ->
      tm_hole_has_type CT Gamma h (unlabel hole) (ArrowTy (LabelelTy T) T)
  (*labelOf data*)
  | T_hole_labelOf : forall h Gamma CT  T, 
      (* tm_has_type CT Gamma h (labelOf e) LabelTy -> *)
      T <> voidTy ->
      tm_hole_has_type CT Gamma h (labelOf hole) (ArrowTy ( (LabelelTy T)) LabelTy)
  (*unlabel opaque*)
  | T_hole_unlabelOpaque : forall h Gamma CT T, 
      (* tm_has_type CT Gamma h (unlabelOpaque e) T ->*)
      T <> voidTy ->
      tm_hole_has_type CT Gamma h (unlabelOpaque hole) (ArrowTy (OpaqueLabeledTy T) T)

(* assignment *)
  | T_hole_assignment : forall h Gamma CT  T x , 
      (* tm_has_type CT Gamma h (Assignment x e) voidTy -> *)
      Gamma x = Some T ->
      T <> voidTy ->
      (* tm_has_type CT Gamma h e T -> *)
      tm_hole_has_type CT Gamma h (Assignment x hole) (ArrowTy T voidTy)

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
      tm_hole_has_type CT Gamma h (FieldWrite hole f e) (ArrowTy (classTy clsT) voidTy)
  | T_hole_FieldWrite2 : forall  h Gamma x f cls_def CT clsT cls',
      tm_has_type CT Gamma h x (classTy clsT) ->
      Some cls_def = CT(clsT) ->
      type_of_field (find_fields cls_def) f = Some cls' ->
      tm_hole_has_type CT Gamma h (FieldWrite x f hole) (ArrowTy (classTy cls') voidTy)
                       (*newly added rule*)
  | T_hole_FieldWrite3 : forall  h Gamma x f cls_def CT clsT cls',
      tm_has_type CT Gamma h x (classTy clsT) ->
      Some cls_def = CT(clsT) ->
      type_of_field (find_fields cls_def) f = Some cls' ->
      tm_hole_has_type CT Gamma h (FieldWrite x f (unlabelOpaque hole)) (ArrowTy (OpaqueLabeledTy (classTy cls')) voidTy).

                       
Hint Constructors tm_hole_has_type. 

Inductive fs_has_type : Class_table -> typing_context -> heap -> list tm -> ty -> Prop :=
  | T_fs_nil : forall h Gamma CT T, 
      fs_has_type CT Gamma h nil (ArrowTy T T)
  | T_fs_no_hole : forall h Gamma CT T T' top fs T0,  
      hole_free top = true ->
      tm_has_type CT Gamma h top T ->
      (fs = nil -> T0 = T) ->
      (forall top fs', fs = top :: fs' ->
                       hole_free top = false ->
                       T0 = T /\ (T0 <> voidTy) 
      ) ->
      fs_has_type CT Gamma h fs (ArrowTy T0 T') ->
      fs_has_type CT Gamma h (top :: fs) (ArrowTy T T') 
  | T_fs_hole : forall h Gamma CT T T' T0 top fs T1,  
      hole_free top  = false ->
      tm_hole_has_type CT Gamma h top ((ArrowTy T T')) ->
      (fs = nil -> T0 = T') ->
      (forall top fs', fs = top :: fs' ->
                       hole_free top = false ->
                       T0 = T' /\ (T0 <> voidTy) 
      ) ->
      fs_has_type CT Gamma h (fs) (ArrowTy T0 T1) ->
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

Inductive ctn_has_type : Class_table -> typing_context -> heap -> container -> ty -> Prop :=
  (*
  | T_ctn_fs : forall h Gamma CT T lb fs open_t sf T', 
      tm_has_type CT Gamma h open_t T ->
      well_typed_stack_frame CT Gamma sf h ->
       T <> voidTy /\ T' <> voidTy  ->
       fs_has_type CT Gamma h fs (ArrowTy T T')  ->
      ctn_has_type CT Gamma h (Container open_t fs lb sf)  (OpaqueLabeledTy T')
  | T_ctn_sequential_exec : forall h Gamma CT T lb fs open_t sf T' T0, 
      ((fs = nil -> T0 = T) /\ (forall top fs', fs = top :: fs' -> hole_free top = true)) ->
      tm_has_type CT Gamma h open_t T ->
      well_typed_stack_frame CT Gamma sf h /\ (T' <> voidTy)->
      fs_has_type CT Gamma h fs (ArrowTy T0 T')  ->
      ctn_has_type CT Gamma h (Container open_t fs lb sf)  (OpaqueLabeledTy T').
   *)

    | T_ctn_type : forall h Gamma CT T lb fs open_t sf T' T0, 
        tm_has_type CT Gamma h open_t T ->
        well_typed_stack_frame CT Gamma sf h ->
        fs_has_type CT Gamma h fs (ArrowTy T0 T')  ->
        (fs = nil -> T0 = T) ->
        (forall top fs', fs = top :: fs'
                         -> hole_free top = false
                         -> T <> voidTy /\ T0 = T
        ) ->
        (T' <> voidTy)->
        ctn_has_type CT Gamma h (Container open_t fs lb sf) (ArrowTy voidTy T')

    | T_ctn_caller : forall h Gamma CT lb fs  sf  T T0 T',
        well_typed_stack_frame CT Gamma sf h ->
        fs_has_type CT Gamma h fs (ArrowTy T0 T')  ->
        (fs = nil -> T0 = (OpaqueLabeledTy T)) ->
        (forall top fs', fs = top :: fs'
                         -> hole_free top = false
                         -> T <> voidTy /\ T0 = (OpaqueLabeledTy T)
        ) ->
        (T' <> voidTy)->
        ctn_has_type CT Gamma h (Container return_hole fs lb sf) (ArrowTy T T').
Hint Constructors ctn_has_type. 


Inductive ctn_list_has_type : Class_table -> typing_context -> heap -> list container -> ty -> Prop := 
  | T_ctn_nil : forall h Gamma CT T , 
      ctn_list_has_type CT Gamma h nil (ArrowTy T T)
(*  | T_ctn_list : forall h Gamma CT T T' ctn ctns' fs lb sf Gamma' T0 top T1, 
      ctn_has_type CT Gamma' h ctn (OpaqueLabeledTy T0) ->
      
      (*The first container has hole in it*)
     
      ctn = (Container return_hole (top :: fs) lb sf) ->
      (hole_free top = false -> T1 = T ) ->
      fs_has_type CT Gamma h (top :: fs) (ArrowTy (OpaqueLabeledTy T1) T0) -> 
      
      ctn_list_has_type CT Gamma h ctns' (ArrowTy (OpaqueLabeledTy T0) T') ->
      ctn_list_has_type CT Gamma h (ctn :: ctns')  (ArrowTy (OpaqueLabeledTy T) T').

  | T_ctn_list : forall h Gamma CT T T' ctn ctns' fs lb sf  Gamma' T0 T1, 
      ctn_has_type CT Gamma' h ctn T0 ->
      (*The first container has return_hole*)
      ctn = (Container return_hole  fs lb sf) ->
      fs_has_type CT Gamma' h fs (ArrowTy T1 T0) ->
      (forall top fs', fs = top :: fs' -> hole_free top = false -> T1 = (OpaqueLabeledTy T) ) ->
      ctn_list_has_type CT Gamma h ctns' (ArrowTy (OpaqueLabeledTy T0) T') ->
      (*(fs = nil -> T = T0) -> *)
      ctn_list_has_type CT Gamma h (ctn :: ctns')  (ArrowTy (OpaqueLabeledTy T) T').
 *)
  | T_ctn_list : forall h Gamma CT T0 T1 T' Gamma' ctn ctns', 
      ctn_has_type CT Gamma' h ctn (ArrowTy T0 T1) ->
      ctn_list_has_type CT Gamma h ctns' (ArrowTy  T1 T') ->
      ctn_list_has_type CT Gamma h (ctn :: ctns')  (ArrowTy T0 T').                        
Hint Constructors ctn_list_has_type. 

Inductive config_has_type : Class_table -> typing_context -> config -> ty -> Prop :=
  | T_config_ctns : forall h Gamma CT T T' ctn ctns Gamma', 
      ctn_has_type CT Gamma' h ctn (ArrowTy voidTy T) ->
      T <> voidTy ->
      ctn_list_has_type CT Gamma h ctns (ArrowTy T T') ->
      (forall c ctns' , ctns = c :: ctns' ->
                             exists fs lb sf, c = (Container return_hole fs lb sf) ) ->
      config_has_type CT Gamma (Config CT ctn ctns h) T'.
Hint Constructors config_has_type. 
  (*method call crosses container boundary*)
  (*                    
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
      config_has_type CT Gamma (Config CT (Container body nil lb sf) (ctn::ctns) h) T'.
*)


Hint Constructors ctn_list_has_type. 
Hint Constructors ctn_has_type.
Hint Constructors fs_has_type.
