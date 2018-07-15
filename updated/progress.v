
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.

Require Import Language Types.
Require Import Lemmas.
Require Import preservation.
Require Import Label.


Theorem Progress : forall config T ct h ctn ctns, 
  config = (Config ct ctn ctns h) ->
  valid_config (Config ct ctn ctns h) ->
  config_has_type ct empty_context (Config ct ctn ctns h) T
  -> terminal_state config \/ (exists config', config ==> config').
Proof with eauto.
  intros config T ct h ctn ctns.
  intro H_config.
  intro H_valid_config. 
  intro H_typing. 
  remember (empty_context) as Gamma.
  inversion H_typing; subst; auto.
  inversion H2; subst; auto.

  inversion H_valid_config; subst; auto.
  inversion H0; subst; auto; try (apply value_progress with T; auto;fail);
    try (exists Error_state, auto) .
  (*Tvar*)
  - inversion H1; subst; auto.
    destruct H9 with x (classTy T3); auto.
    destruct H10; subst; auto.
    right.
    exists (Config ct (Container x0 fs lb sf) ctns h); auto.


  (*(EqCmp e1 e2)*)
  - pose proof (excluded_middle_value e1).
    destruct H11.
    right.
    + pose proof (excluded_middle_value e2).
      destruct H12. 
      ++ pose proof (exclude_middle_val_eq e1 e2 H11 H12).
         destruct H15.
         +++ inversion H11; subst; inversion H; subst; auto.
             ++++ destruct H26 as [F]. destruct H15 as [lo].
                  case_eq (flow_to lo lb); intro.
                  exists (Config ct (Container (B_true) fs lb sf) ctns h).
                  apply ST_EqCmp_result; auto.
                  intros. intuition.
                  right; exists o; exists cls_def; exists F; exists lo;
                    split; auto.
                  right; exists o; exists cls_def; exists F; exists lo;
                    split; auto.

                  exists Error_state.
                  apply ST_EqCmp_leak; auto.
                  left. exists o; exists cls_def; exists F; exists lo;
                          split; auto.
             ++++
               exists (Config ct (Container (B_true) fs lb sf) ctns h).
               apply ST_EqCmp_result; auto.
               intros. intuition.
         +++ inversion H11; subst; inversion H; subst; auto.
             ++++ destruct H27 as [F]. destruct H16 as [lo].
                  inversion H12; subst; inversion H9; subst; auto.
                  +++++ destruct H30 as [F2]. destruct H21 as [lo2].
                    case_eq (flow_to lo lb); intro.
                    case_eq (flow_to lo2 lb); intro.
                  exists (Config ct (Container (B_false) fs lb sf) ctns h).
                  apply ST_EqCmp_result; auto.
                  intros. intuition.
                  
                  right; exists o; exists cls_def; exists F; exists lo;
                    split; auto.
                  right; exists o0; exists cls_def0; exists F2; exists lo2;
                    split; auto.

                  exists Error_state.
                  apply ST_EqCmp_leak; auto.
                  right. exists o0; exists cls_def0; exists F2; exists lo2;
                           split; auto.
                  
                  exists Error_state.
                  apply ST_EqCmp_leak; auto.
                  left. exists o; exists cls_def; exists F; exists lo;
                    split; auto.
                  +++++ case_eq (flow_to lo lb); intro.
                    * exists (Config ct (Container (B_false) fs lb sf) ctns h).
                       apply ST_EqCmp_result; auto.
                       intros. intuition.
                       right; exists o; exists cls_def; exists F; exists lo;
                         split; auto.
                    * exists Error_state.
                       apply ST_EqCmp_leak; auto.
                       left. exists o; exists cls_def; exists F; exists lo;
                               split; auto.
               ++++ 
                 inversion H12; subst; inversion H9; subst; auto.
                 +++++ destruct H27 as [F2]. destruct H16 as [lo2].
                 case_eq (flow_to lo2 lb); intro.
                 * exists (Config ct (Container (B_false) fs lb sf) ctns h).
                  apply ST_EqCmp_result; auto.
                  intros. intuition.
                  right. exists o; exists cls_def; exists F2; exists lo2;
                           split; auto.
                 * exists Error_state.
                   apply ST_EqCmp_leak; auto.
                   right. exists o; exists cls_def; exists F2; exists lo2;
                            split; auto.
                   +++++ intuition.

                   ++ exists (Config ct (Container e2 ((EqCmp e1 hole) :: fs) lb sf) ctns h).
                      auto.

    + right.
      exists ( Config ct (Container e1 ((EqCmp hole e2) :: fs) lb sf) ctns h). auto. 
         

  (*field access*)
  - pose proof (excluded_middle_value e).
    destruct H10.
    right. inversion H10; subst; inversion H; subst; auto. 
    + destruct H25 as [F].
      destruct H12 as [lo].
      assert (exists v, F(f) = Some v).
      apply field_val_of_heap_obj with h o ct cls_def0 lo cls' (find_fields cls_def); auto.
      subst; auto. 
      rewrite <- H9 in H16; inversion H16; subst; auto.  
      destruct H15 as [v]. 
      remember (Label.join_label lo lb) as l'.
      exists (Config ct (Container v fs l' sf) ctns h); auto.
      eauto using reduction. 
    + exists Error_state; subst; auto.
    + right. exists (Config ct (Container (e) ((FieldAccess hole f)::fs) lb sf) ctns h); auto.
 

  (* method call *)
  - pose proof (excluded_middle_value e).
    destruct H12; subst; auto.
    right. inversion H12; subst; inversion H; subst; auto.
    + pose proof (excluded_middle_value argu). destruct H21.
      ++ destruct H28 as [F]. destruct H22 as [lx].
         subst. rewrite <- H10 in H23. inversion H23;subst. 
         remember (sf_update empty_stack_frame arg_id argu) as sf'.
         case_eq (flow_to lx lb); intro.
         +++ exists (Config ct (Container body nil lb sf' ) ((Container (return_hole) fs lb sf ) :: ctns) h). 
             eauto using reduction.
         +++ exists Error_state; subst; auto.
             eauto using reduction.
      ++ pose proof (exclude_middle_unlabelOpaque argu).
         destruct H22.
         +++ destruct H22 as [v]. destruct H22. 
             destruct H28 as [F].
             destruct H25 as [lo].
             rewrite <- H10 in H23; inversion H23; subst; auto.
             inversion H9; subst; auto.
             inversion H22; subst; inversion H26; subst; auto.
             ++++ exists Error_state. auto.
             ++++ case_eq (flow_to lo lb); intro.
                  +++++
                    remember ( sf_update empty_stack_frame arg_id v0) as sf'. 
                  remember ( join_label lb lb0) as lb'. 
                  exists (Config ct (Container body nil lb' sf' ) ((Container return_hole fs lb sf ) :: ctns) h). 
                  apply ST_MethodCall_unlableOpaque with cls_def F arg_id arguT returnT lo; auto.
                  +++++ exists Error_state.
                  apply ST_MethodCall_unlableOpaque_leak with cls_def F lo (join_label lb lb0); auto.

         +++ destruct H22; subst; auto.
             ++++ exists (Config ct
                                 (Container (argu) ((MethodCall (ObjId o) meth hole)::fs) lb sf)
                                 ctns h); auto. 
             ++++ exists (Config ct (Container (argu) ((MethodCall (ObjId o) meth hole)::fs) lb sf) ctns h); auto.
                  apply ST_MethodCall4.
                  intros. intro contra. destruct H22 as [t']. destruct H22.  
                  rewrite H22 in contra. inversion contra;  subst;auto.
                  auto. auto.  
    + exists Error_state; subst; auto.
    + eauto using reduction.
    

  (*new exp*)
  - destruct H as [cls].
    destruct H as [field_defs].
    destruct H as [method_defs].
    destruct H. remember (get_fresh_oid h) as o. 
    remember (init_field_map (find_fields cls) empty_field_map) as F. 
    remember (add_heap_obj h o (Heap_OBJ cls F lb)) as h'.
    right. exists (Config ct (Container (ObjId o) fs lb sf ) ctns h'). 
    apply ST_NewExp with field_defs method_defs cls F; auto. 

  (*label data*)
  -  pose proof (excluded_middle_value e).
     destruct H11; right.
     + exists (Config ct (Container (v_l e lb0)  fs lb sf) ctns h); auto.       
     + exists (Config ct (Container e ((labelData hole lb0) :: fs) lb sf) ctns h ); auto.

  (*unlabel*)
  - pose proof (excluded_middle_value e).
    destruct H10; right.
    + inversion H10; subst; inversion H; subst; auto.  
      ++ exists Error_state. auto. 
      ++ subst. remember (join_label lb lb0) as l'.
         exists (Config ct (Container v fs l' sf) ctns h); auto.
  + exists (Config ct (Container (e) ((unlabel hole)::fs) lb sf) ctns h); auto.

  (*(labelOf e)*)
  - pose proof (excluded_middle_value e).
    destruct H10; right. 
    + inversion H10; subst; inversion H; subst; auto.  
      ++ exists Error_state. auto. 
      ++ exists (Config ct (Container (l lb0) fs lb sf) ctns h). auto.
    + exists (Config ct (Container (e) ((labelOf hole)::fs) lb sf) ctns h); auto.

  (*(unlabelOpaque e)*)
  - pose proof (excluded_middle_value e).
    destruct H10; right.
    + inversion H10; subst; inversion H; subst; auto.  
      ++ exists Error_state. auto. 
      ++ subst. remember (join_label lb lb0) as l'.
         exists (Config ct (Container v fs l' sf) ctns h); auto.
  + exists (Config ct (Container (e) ((unlabelOpaque hole)::fs) lb sf) ctns h); auto.

  (* skip *)
  - destruct fs. 
    + inversion H_typing; subst; auto.
      inversion H11; subst; auto.
      inversion H28; subst; auto.
      inversion H21; subst; auto.
      assert (T1 = voidTy); auto.
      subst; auto.
      intuition. 
   + right.  exists (Config ct (Container t fs lb sf) ctns h ); auto.

  (*(Assignment x e) *)   
  - pose proof (excluded_middle_value e).
    destruct H11; right.
    + remember ( sf_update sf x e) as sf'.
      exists (Config ct (Container Skip fs lb sf') ctns h). auto.
    + exists (Config ct (Container (e) ((Assignment x hole)::fs) lb sf) ctns h); auto.

  (* (FieldWrite x f e)*)
  - pose proof (excluded_middle_value x).
    destruct H12; subst; auto.
    right. inversion H12; subst; inversion H; subst; auto.
    + pose proof (excluded_middle_value e). destruct H15.
      ++ destruct H26 as [F]. destruct H16 as [lx].
         subst. rewrite <- H10 in H21. inversion H21;subst.
         rename lx into lo. 
         case_eq (flow_to lb lo); intro.
         
         +++ inversion H15; subst; auto; inversion H9; subst; auto.
             ++++ destruct H31 as [F0].
                  destruct H23 as [lo0].
                  case_eq (flow_to lo0 lo); intro.
                  +++++ remember (fields_update F f (ObjId o0)) as F'.
                  remember ( update_heap_obj h o (Heap_OBJ cls_def F' lo)) as h'.
                  exists (Config ct (Container Skip fs lb sf) ctns h' ); auto.
                  apply ST_fieldWrite_normal with lo cls_def F F'; auto.
                  right.
                  exists o0. exists cls_def0.
                  exists F0. exists lo0. split; auto.
                  +++++ exists Error_state.
                  apply ST_fieldWrite_leak with lo cls_def F; auto.
                  right.
                  exists o0. exists cls_def0.
                  exists F0. exists lo0. split; auto.
             ++++ remember (fields_update F f null) as F'.
                  remember ( update_heap_obj h o (Heap_OBJ cls_def F' lo)) as h'.
                  exists (Config ct (Container Skip fs lb sf) ctns h' ); auto.
                  apply ST_fieldWrite_normal with lo cls_def F F'; auto.
         +++ exists Error_state.
             apply ST_fieldWrite_leak with lo cls_def F; auto.
      ++ pose proof (exclude_middle_unlabelOpaque e).
         destruct H16.
         +++ destruct H16 as [v]. destruct H16. 
             destruct H26 as [F].
             destruct H23 as [lo].
             rewrite <- H10 in H21; inversion H21; subst; auto.
             inversion H9; subst; auto.
             inversion H16; subst; inversion H24; subst; auto.
             ++++ exists Error_state. auto.

             
             ++++
               case_eq (flow_to (join_label lb lb0) lo); intro.
               +++++
                 inversion H36; subst; inversion H34; subst; auto.
               destruct H39 as [F0].
               destruct H27 as [lo0].                  
               ++++++ case_eq (flow_to lo0 lo); intro. 
                 * remember (fields_update F f (ObjId o0)) as F'.
               remember ( update_heap_obj h o (Heap_OBJ cls_def F' lo)) as h'.
               exists (Config ct (Container Skip fs lb sf) ctns h' ); auto.
               apply ST_fieldWrite_unlableOpaque with lo cls_def F F'; auto.
               right.
               exists o0. exists cls_def0.
               exists F0. exists lo0. split; auto.
                 * exists Error_state.
                   apply ST_fieldWrite_unlableOpaque_leak with lo cls_def F; auto.
                   right. exists o0. exists cls_def0.
                  exists F0. exists lo0. split; auto.
                  ++++++  remember (fields_update F f null) as F'.
                  remember ( update_heap_obj h o (Heap_OBJ cls_def F' lo)) as h'.
                  exists (Config ct (Container Skip fs lb sf) ctns h' ); auto.
                  apply ST_fieldWrite_unlableOpaque with lo cls_def F F'; auto.

                  +++++ exists Error_state.
                  apply ST_fieldWrite_unlableOpaque_leak with lo cls_def F; auto.

        +++ destruct H16. 
            ++++ exists (Config ct
                                 (Container (e) ((FieldWrite (ObjId o) f hole)::fs) lb sf)
                                 ctns h); auto. 
            ++++ exists (Config ct (Container (e) ((FieldWrite (ObjId o) f hole)::fs) lb sf) ctns h); auto.
                  apply ST_fieldWrite4.
                  intros. intro contra. destruct H16 as [t']. destruct H16.  
                  rewrite H16 in contra. inversion contra;  subst;auto.
                  auto. auto.


    + exists Error_state. auto.
    +  eauto using reduction.

(* if *)
  - pose proof (excluded_middle_value guard). destruct H11; subst; right.
    + inversion H11; subst; inversion H; subst; auto; eauto using reduction.

    + eauto using reduction.

(* sequence *)      
  - right. eauto using reduction.

(* (Container hole fs lb sf) *)    
  - inversion H18. 


(* (Container hole fs lb sf) *)    
  - inversion H_valid_config; subst; auto.
    inversion H17. 
Qed. Hint Resolve Progress. 