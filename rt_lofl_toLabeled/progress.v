
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
      ++ pose proof (exclude_middle_runtime_val e1 e2 H11 H12).
         remember (join_label (runtime_label e1) (runtime_label e2)) as l'.
         remember (join_label l' lb) as lb'.
         remember (join_label lb' (join_label (object_label (runtime_val e1) h)
                                              (object_label (runtime_val e2) h)))
         as lb''.
         destruct H15.
         +++
           exists (Config ct (Container (B_true) fs lb'' sf) ctns h).
           apply ST_EqCmp_result with l' lb'; auto.
            intro. intuition.
         +++
           exists (Config ct (Container (B_false) fs lb'' sf) ctns h).
            apply ST_EqCmp_result with l' lb'; auto.
            intro. intuition.
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
      destruct H12 as [ll]. 
      assert (exists v, F(f) = Some v).
      apply field_val_of_heap_obj with h o ct cls_def0 lo cls' (find_fields cls_def) ll; auto.
      subst; auto. 
      rewrite <- H9 in H16; inversion H16; subst; auto.  
      destruct H15 as [v]. 
      remember (Label.join_label lo lb) as l'.
      exists (Config ct (Container v nil (join_label l' ll) sf) ((Container (return_hole) fs lb sf ) :: ctns) h); auto. 
      eauto using reduction. 
    + exists Error_state; subst; auto.
    + inversion H27; subst; auto; inversion H23; subst; auto.   
      destruct H31 as [F].
      destruct H16 as [lo].
      destruct H16 as [ll].
      assert (exists v, F(f) = Some v).
      apply field_val_of_heap_obj with h o ct cls_def0 lo cls' (find_fields cls_def) ll; auto.
      rewrite <- H9 in H24; inversion H24;  subst; auto. 
      destruct H21 as [v]. 
      remember (join_label (join_label lo lb) lb0) as l'.
      exists (Config ct (Container v nil (join_label l' ll) sf) ((Container (return_hole) fs lb sf ) :: ctns) h); auto. 
      eauto using reduction.

      ++ exists Error_state. eauto using reduction.  
      ++ destruct H15 with v0 lb1; auto. 
      
      + right. exists (Config ct (Container (e) ((FieldAccess hole f)::fs) lb sf) ctns h); auto.
 
  (* method call *)
  - pose proof (excluded_middle_value e).
    destruct H12; subst; auto.
    right. inversion H12; subst; inversion H; subst; auto.
    + pose proof (excluded_middle_value argu). destruct H21.
      ++ destruct H28 as [F]. destruct H22 as [lx].
         destruct H22 as [ll].
         subst. rewrite <- H10 in H23. inversion H23;subst. 
         remember (sf_update empty_stack_frame arg_id argu) as sf'.
         exists (Config ct (Container body nil (join_label (join_label lx lb) ll) sf' ) ((Container (return_hole) fs lb  sf ) :: ctns) h). 
         eauto using reduction.

      ++  exists (Config ct (Container argu ((MethodCall (ObjId o) meth hole) :: fs) lb sf) ctns h). apply  ST_MethodCall3 ; auto.
          intro contra; inversion contra. 
    + pose proof (excluded_middle_value argu).
      eauto using reduction.

    + pose proof (excluded_middle_value argu). destruct H23.
      ++ inversion H30; subst; auto; inversion H26; subst; auto.
         +++ 
         destruct H35 as [F]. destruct H24 as [lo]. destruct H24 as [ll].
         subst;auto.
         rewrite <- H10 in H28. inversion H28; subst. 
         remember (sf_update empty_stack_frame arg_id argu) as sf'.
         remember ( join_label lb lb0) as lb'. 
         exists (Config ct (Container body nil (join_label (join_label lo lb') ll) sf' ) ((Container (return_hole) fs lb sf ) :: ctns) h). 
         eauto using reduction.
         +++ exists Error_state. eauto using reduction. 
         +++ destruct H22 with v0 lb1. auto. 

      ++  exists (Config ct (Container argu ((MethodCall  (v_opa_l v lb0) meth hole) :: fs) lb sf) ctns h). apply  ST_MethodCall3 ; auto.
          intro contra; inversion contra.    
 
    + right. exists (Config ct (Container e ((MethodCall hole meth argu) :: fs) lb sf) ctns h).
      eauto using reduction. 
          
  (*new exp*)
  - destruct H as [cls].
    destruct H as [field_defs].
    destruct H as [method_defs].
    destruct H. remember (get_fresh_oid h) as o. 
    remember (init_field_map (find_fields cls) empty_field_map) as F. 
    remember (add_heap_obj h o (Heap_OBJ cls F lb lb)) as h'.
    right. exists (Config ct (Container (ObjId o) fs lb sf ) ctns h'). 
    apply ST_NewExp with field_defs method_defs cls F; auto. 

    Lemma exclude_middle_null : forall v, value v ->
                                          v = null \/ v <> null.
    Proof with eauto.
      intros.  inversion H; try (right; intro contra; inversion contra; fail).
      left. auto.
    Qed. Hint Resolve exclude_middle_null.      
    
  (*label data*)
  -  pose proof (excluded_middle_value e).
     destruct H11; right.
     + pose proof exclude_middle_null e H11 .
       destruct H12.
       exists Error_state. subst; apply ST_LabelDataException.
       case_eq (flow_to lb lb0); intro.
       ++
         exists (Config ct (Container (v_l e lb0)  fs lb sf) ctns h); auto.
       ++
         exists Error_state. auto. 
     + exists (Config ct (Container e ((labelData hole lb0) :: fs) lb sf) ctns h ); auto.

  (*unlabel*)
  - pose proof (excluded_middle_value e).
    destruct H10; right.
    + inversion H10; subst; inversion H; subst; auto.  
      ++ exists Error_state. auto.
         
      ++ subst. remember (join_label lb lb0) as l'.
         exists (Config ct (Container v fs l' sf) ctns h); auto.
      ++ 
        subst. remember (join_label lb lb0) as l'.
        exists (Config ct (Container (unlabel v) fs l' sf) ctns h); auto.

  + exists (Config ct (Container (e) ((unlabel hole)::fs) lb sf) ctns h); auto.

  (*(labelOf e)*)
  - pose proof (excluded_middle_value e).
    destruct H10; right. 
    + inversion H10; subst; inversion H; subst; auto.  
      ++ exists Error_state. auto.
      ++ exists (Config ct (Container (l lb0) fs lb sf) ctns h). auto.
      ++ remember (join_label lb lb0) as l'.
         exists (Config ct (Container (labelOf v) fs l' sf) ctns h). auto.
    + exists (Config ct (Container (e) ((labelOf hole)::fs) lb sf) ctns h); auto.

  (*(objectLabelOf e)*)
  - pose proof (excluded_middle_value e).
    destruct H10; right. 
    + inversion H10; subst; inversion H; subst; auto.  
      ++ destruct H24 as [F]. destruct H11 as [lo].
         destruct H11 as [ll].
         exists (Config ct (Container (l lo) fs (join_label ll lb) sf) ctns h); auto.
         eauto using reduction.
      ++ exists Error_state. auto.
      ++ inversion H11; subst; auto; inversion H22; subst; auto.
         +++ 
           destruct H30 as [F]. destruct H15 as [lo]. destruct H15 as [ll].
           remember (join_label lb lb0) as l'.
           exists ( Config ct (Container (l lo) fs (join_label ll l') sf) ctns h); auto.
           eauto using reduction.
         +++ exists Error_state. auto.
         +++ destruct H28 with v0 lb1; auto.   
    + exists (Config ct (Container (e) ((objectLabelOf hole)::fs) lb sf) ctns h); auto.
      
  (*raise label*)
  -  pose proof (excluded_middle_value e).
     destruct H11; right.
     + inversion H11; subst; auto; inversion H9; subst; auto.
       ++ 
         destruct H25 as [F]. destruct H12 as [lo]. destruct H12 as [ll].
         case_eq (flow_to lb ll); intro.
         case_eq (flow_to lo lb0); intro.
         remember  (update_heap_obj h o (Heap_OBJ cls_def F lb0 ll)) as h'.
         exists (Config ct (Container Skip fs lb sf) ctns h' ). auto.
         eauto using ST_raiseLabel3 . 

         exists Error_state. eauto using ST_raiseLabelException2.
         exists Error_state. eauto using ST_raiseLabelException2.

       ++         
         exists Error_state. eauto using ST_raiseLabelException1.

       ++ remember (join_label lb lb1) as l'.
          inversion H12; subst; auto; inversion H23; subst; auto.
          +++
            destruct H31 as [F]. destruct H16 as [lo]. destruct H16 as [ll].
            case_eq (flow_to (join_label lb lb1) ll); intro.
            case_eq (flow_to lo lb0); intro.
            remember  (update_heap_obj h o (Heap_OBJ cls_def F lb0 ll)) as h'.
            exists (Config ct (Container Skip fs lb sf) ctns h' ). auto.
            eauto using ST_raiseLabel4.
          ++++ 
            exists Error_state. eauto using ST_raiseLabelException2.
          ++++
            exists Error_state. eauto using ST_raiseLabelException2.
          +++
            exists Error_state. eauto using reduction.
          +++ destruct H15 with v0 lb2; auto.

     + exists (Config ct (Container e ((raiseLabel hole lb0) :: fs) lb sf) ctns h ); auto.

 (*  (toLabeled e v) *)
  -  pose proof (excluded_middle_value v).
     destruct H11; right.
     + pose proof exclude_middle_null v H11 .
       destruct H12.
       ++ 
         exists Error_state. subst; auto.
       ++
         inversion H11; subst; auto;
           inversion H; subst; auto.
         *
           intuition.
         *
           exists ( Config ct (Container e ((labelData hole lb0)::nil) lb sf) ((Container (return_hole) fs lb sf ) :: ctns) h).
           auto.
         *
           exists (Config ct (Container (toLabeled e v0) fs (join_label lb lb0) sf) ctns h).
           auto.
     +
       exists (Config ct (Container v ((toLabeled e hole) :: fs) lb sf) ctns h ); auto.

  (* getCurrentLevel *)     
  - right. exists (Config ct (Container (l lb) fs lb sf) ctns h); auto.
       
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
      ++ destruct H26 as [F]. destruct H16 as [lx]. destruct H16 as [ll].
         subst. rewrite <- H10 in H21. inversion H21;subst.
         rename lx into lo. 
         case_eq (flow_to (join_label (runtime_label e) lb) (join_label lo ll)); intro.
         
         +++ remember (fields_update F f (runtime_val e)) as F'.
             remember ( update_heap_obj h o (Heap_OBJ cls_def F' lo ll)) as h'.
             exists (Config ct (Container Skip fs lb sf) ctns h' ); auto.
             eauto using ST_fieldWrite_normal . 
         +++ exists Error_state. eauto using  ST_fieldWrite_leak.

      ++ exists (Config ct (Container e ((FieldWrite (ObjId o) f hole) :: fs) lb sf) ctns h).
         apply ST_fieldWrite3; auto.
         intro contra; inversion contra.

    + exists Error_state; subst; auto.

    + pose proof (excluded_middle_value e). destruct H21.
      ++ inversion H28; subst; auto; inversion H24; subst; auto.
         +++ 
         destruct H33 as [F]. destruct H22 as [lo]. destruct H22 as [ll].
         subst. rewrite <- H10 in H26. inversion H26; subst.
         remember  (join_label (runtime_label e) lb) as lb'.
         remember ( (join_label lb0 lb)) as lb''.
         exists (Config ct (Container (FieldWrite (ObjId o) f e) fs lb'' sf ) ctns h).
         eauto using reduction.
         
         +++ exists Error_state. eauto using reduction. 
         +++ destruct H16 with v0 lb1; auto.
    ++ exists (Config ct (Container e ((FieldWrite (v_opa_l v lb0) f hole) :: fs) lb sf) ctns h).
         apply ST_fieldWrite3; auto.
         intro contra; inversion contra.

    + right. exists (Config ct (Container x ((FieldWrite hole f e) :: fs) lb sf) ctns h).
      apply ST_fieldWrite1; auto.
    

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