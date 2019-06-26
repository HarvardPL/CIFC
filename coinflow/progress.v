
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


Lemma exclude_middle_null : forall v, value v ->
                                          v = null \/ v <> null.
Proof with eauto.
      intros.  inversion H; try (right; intro contra; inversion contra; fail).
      left. auto.
Qed. Hint Resolve exclude_middle_null.  

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
   match goal with
    | H : ctn_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
   end.
  inversion H_valid_config; subst; auto.
  inversion H1; subst; auto; try (apply value_progress with T; auto;fail);
    try (exists Error_state, auto) .
  (*Tvar*)
  - inversion H9; subst; auto.
    destruct H0 with x T1; auto.
    destruct H2; subst; auto.
    right.
    exists (Config ct (Container x0 fs lb sf) ctns h); auto.

  (*(EqCmp e1 e2)*)
  - pose proof (excluded_middle_value e1).
    destruct H3.
    right.
    + pose proof (excluded_middle_value e2).
      destruct H5. 
      ++ pose proof (exclude_middle_runtime_val e1 e2 H3 H5).
         remember (join_label (runtime_label e1) (runtime_label e2)) as l'.
         remember (join_label l' lb) as lb'.
         remember (join_label lb' (join_label (object_label (runtime_val e1) h)
                                              (object_label (runtime_val e2) h)))
         as lb''.
         destruct H11.
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
    destruct H2.
    right. inversion H2; subst; inversion H; subst; auto. 
    + destruct H21 as [F].
      destruct H5 as [lo].
      destruct H5 as [ll]. 
      assert (exists v, F(f) = Some v).
      apply field_val_of_heap_obj with h o ct cls_def0 lo cls' (find_fields cls_def) ll; auto.
      subst; auto. 
      rewrite <- H0 in H12; inversion H12; subst; auto.  
      destruct H11 as [v]. 
      remember (Label.join_label lo lb) as l'.
      eauto using reduction. 
    + exists Error_state; subst; auto.
    + inversion H23; subst; auto; inversion H19; subst; auto.   
      destruct H27 as [F].
      destruct H12 as [lo].
      destruct H12 as [ll].
      assert (exists v, F(f) = Some v).
      apply field_val_of_heap_obj with h o ct cls_def0 lo cls' (find_fields cls_def) ll; auto.
      rewrite <- H0 in H20; inversion H20;  subst; auto. 
      destruct H17 as [v]. 
      remember (join_label (join_label lo lb) lb0) as l'.
      eauto using reduction.
      ++ exists Error_state. eauto using reduction.  
      ++ destruct H11 with v0 lb1; auto.       
      + right. exists (Config ct (Container (e) ((FieldAccess hole f)::fs) lb sf) ctns h); auto.
 
  (* method call *)
  - pose proof (excluded_middle_value e).
    destruct H11; subst; auto.
    right. inversion H11; subst; inversion H; subst; auto.
    + pose proof (excluded_middle_value argu). destruct H12.
      ++ destruct H23 as [F]. destruct H17 as [lx].
         destruct H17 as [ll].
         subst. rewrite <- H2 in H18; inversion H18; subst. 
         remember (sf_update empty_stack_frame arg_id argu) as sf'.
         eauto using reduction.
      ++  exists (Config ct (Container argu ((MethodCall (ObjId o) meth hole) :: fs) lb sf) ctns h). apply  ST_MethodCall3 ; auto.
          intro contra; inversion contra. 
    + pose proof (excluded_middle_value argu).
      eauto using reduction.

    + pose proof (excluded_middle_value argu). destruct H18.
      ++ inversion H25; subst; auto; inversion H21; subst; auto.
         +++ 
         destruct H30 as [F]. destruct H19 as [lo]. destruct H19 as [ll].
         subst; auto.
         rewrite <- H2 in H23. inversion H23; subst. 
         remember (sf_update empty_stack_frame arg_id argu) as sf'.
         remember ( join_label lb lb0) as lb'.
         eauto using reduction.
         +++ exists Error_state. eauto using reduction. 
         +++ destruct H17 with v0 lb1. auto. 

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
    
    
  (*label data*)

  - pose proof (excluded_middle_value e1).
    destruct H2; subst; auto.
    + 
      right. inversion H2; subst; inversion H0; subst; auto.
      ++ pose proof (excluded_middle_value e2). destruct H3.
      *
        inversion H3; subst; inversion H; subst; auto.
        ** case_eq (flow_to lb lb0); intro; eauto using reduction.
        ** inversion H26; subst; auto; inversion H22; subst; auto.
           *** case_eq (flow_to (join_label lb lb0) lb1); intro; eauto using reduction.
           *** destruct H17 with v0 lb1; auto.
      *
        eauto using reduction.
        ++
          pose proof (excluded_middle_value e2). destruct H3.
      *
        inversion H3; subst; inversion H; subst; auto.
        ** case_eq (flow_to lb lb0); intro; eauto using reduction.
        ** inversion H23; subst; auto; inversion H19; subst; auto.
           *** case_eq (flow_to (join_label lb lb0) lb1); intro; eauto using reduction.
           *** destruct H11 with v0 lb1; auto.
      *
        eauto using reduction.
        ++ 
          pose proof (excluded_middle_value e2). destruct H3.
      *
        inversion H3; subst; inversion H; subst; auto.
        ** case_eq (flow_to lb lb1); intro; eauto using reduction.
        ** inversion H23; subst; auto; inversion H19; subst; auto.
           *** case_eq (flow_to (join_label lb lb1) lb2); intro; eauto using reduction.
           *** destruct H11 with v0 lb2; auto.
      * eauto using reduction.
        ++ 
          pose proof (excluded_middle_value e2). destruct H5.
      *
        inversion H5; subst; inversion H; subst; auto.
        ** case_eq (flow_to lb lb1); intro; eauto using reduction.
        ** inversion H27; subst; auto; inversion H23; subst; auto.
           *** case_eq (flow_to (join_label lb lb1) lb2); intro; eauto using reduction.
           *** destruct H17 with v1 lb2; auto.
      * eauto using reduction.
        ++
          pose proof (excluded_middle_value e2). destruct H11.
      *
        inversion H11; subst; inversion H; subst; auto.
        ** case_eq (flow_to lb lb1); intro; eauto using reduction.
        ** inversion H29; subst; auto; inversion H25; subst; auto.
           *** case_eq (flow_to (join_label lb lb1) lb2); intro; eauto using reduction.
           *** destruct H19 with v1 lb2; auto.
      * eauto using reduction.
        ++
          pose proof (excluded_middle_value e2). destruct H3.
      *
        inversion H3; subst; inversion H; subst; auto.
        ** case_eq (flow_to lb lb0); intro; eauto using reduction.
        ** inversion H23; subst; auto; inversion H19; subst; auto.
           *** case_eq (flow_to (join_label lb lb0) lb1); intro; eauto using reduction.
           *** destruct H11 with v0 lb1; auto.
      * eauto using reduction.
        ++
          pose proof (excluded_middle_value e2). destruct H3.
      *
        inversion H3; subst; inversion H; subst; auto.
        ** case_eq (flow_to lb lb0); intro; eauto using reduction.
        ** inversion H23; subst; auto; inversion H19; subst; auto.
           *** case_eq (flow_to (join_label lb lb0) lb1); intro; eauto using reduction.
           *** destruct H11 with v0 lb1; auto.
      * eauto using reduction.
    +
      eauto using reduction.

  (*unlabel*)
  - pose proof (excluded_middle_value e).
    destruct H0; right.
    + inversion H0; subst; inversion H; subst; auto.  
      ++ eauto using reduction.
      ++ eauto using reduction.
    + eauto using reduction. 

  (*(labelOf e)*)
  - pose proof (excluded_middle_value e).
    destruct H0; right.
    + inversion H0; subst; inversion H; subst; auto.  
      ++ eauto using reduction.
      ++ eauto using reduction.
    + eauto using reduction. 

  (*(objectLabelOf e)*)
  - pose proof (excluded_middle_value e).
    destruct H2; right.
    + inversion H2; subst; inversion H; subst; auto.  
      ++ destruct H20 as [F].
         destruct H3 as [lo].
         destruct H3 as [ll].
         eauto using reduction.
      ++ eauto using reduction.
      ++ inversion H22; subst; auto; inversion H18; subst; auto.
         * destruct H26 as [F].
           destruct H11 as [lo].
           destruct H11 as [ll].
           eauto using reduction.
         * eauto using reduction.
         * destruct H5 with v0 lb1. auto.
    + eauto using reduction. 
      
  (*raise label*)
  - pose proof (excluded_middle_value e1).
    destruct H3; subst; auto.
    + 
      right. inversion H3; subst; inversion H0; subst; auto.
      ++ pose proof (excluded_middle_value e2).
         destruct H21 as [F]. destruct H11 as [lo]. destruct H11 as [ll].         
         destruct H5.
      * inversion H5; subst; inversion H; subst; auto.
        ** case_eq (flow_to lb ll); intro.
           ***
             case_eq (flow_to lo lb0); intro;  eauto using reduction.
           ***
             eauto using reduction.
        ** inversion H27; subst; auto; inversion H23; subst; auto.
           *** case_eq (flow_to (join_label lb lb0) ll); intro; eauto using reduction.
               case_eq (flow_to lo lb1); intro;  eauto using reduction.
           ***
             destruct H18 with v0 lb1; auto.
      *         eauto using reduction.
     ++ pose proof (excluded_middle_value e2).
        destruct H5;  
        eauto using reduction.
      ++ inversion H23; subst; inversion H19; subst; auto.
         *
           pose proof (excluded_middle_value e2).
           destruct H27 as [F].
           destruct H17 as [lo]. destruct H17 as [ll].         
           destruct H12.
           ** inversion H12; subst; inversion H; subst; auto.
              *** case_eq (flow_to (join_label lb lb0) ll); intro.
                  case_eq (flow_to lo lb1); intro;  eauto using reduction.
                  eauto using reduction. 
              *** inversion H33; subst; auto; inversion H29; subst; auto.
                  **** case_eq (flow_to  (join_label (join_label lb lb0) lb1) ll); intro; eauto using reduction.
                       case_eq (flow_to lo lb2); intro;  eauto using reduction.
                  **** destruct H22 with v0 lb2; auto.
           **
             eauto using reduction.
         * pose proof (excluded_middle_value e2).
           destruct H12;
          eauto using reduction.
         * destruct H25 with v0 lb1; auto.
    +
      eauto using reduction. 

 (*  (toLabeled e v) *)
  -  pose proof (excluded_middle_value v).
     destruct H2; right.
     + pose proof exclude_middle_null v H2 .
       destruct H3.
       ++ 
         exists Error_state. subst; auto.
       ++
         inversion H2; subst; auto;
           inversion H; subst; auto;  eauto using reduction. 
     + eauto using reduction. 

  (* getCurrentLevel *)     
  - right. exists (Config ct (Container (l lb) fs lb sf) ctns h); auto.
       

  (*(Assignment x e) *)   
  - pose proof (excluded_middle_value e).
    destruct H2; right; eauto using reduction.
    
  (* (FieldWrite x f e)*)
  - pose proof (excluded_middle_value x).
    destruct H5; subst; auto.
    right. inversion H5; subst; inversion H; subst; auto.
    + pose proof (excluded_middle_value e).
      destruct H11.
      ++ destruct H22 as [F]. destruct H12 as [lx]. destruct H12 as [ll].
         subst. rewrite <- H2 in H17. inversion H17; subst.
         rename lx into lo. 
         case_eq (flow_to (join_label (runtime_label e) lb) (join_label lo ll)); intro.
         
         +++ remember (fields_update F f (runtime_val e)) as F'.
             remember ( update_heap_obj h o (Heap_OBJ cls_def F' lo ll)) as h'.
             eauto using ST_fieldWrite_normal . 
         +++ exists Error_state. eauto using reduction.  
      ++ exists (Config ct (Container e ((FieldWrite (ObjId o) f hole) :: fs) lb sf) ctns h).
         apply ST_fieldWrite3; auto.
         intro contra; inversion contra.
    + exists Error_state; subst; auto.
    + pose proof (excluded_middle_value e). destruct H17.
      ++ inversion H24; subst; auto; inversion H20; subst; auto.
         +++ 
         destruct H29 as [F]. destruct H18 as [lo]. destruct H18 as [ll].
         subst. rewrite <- H2 in H22. inversion H22; subst.
         remember  (join_label (runtime_label e) lb) as lb'.
         remember ( (join_label lb0 lb)) as lb''.
         case_eq (flow_to (join_label (join_label (runtime_label e) lb) lb0) (join_label lo ll)); intro;
           eauto using reduction.
         +++ exists Error_state. eauto using reduction. 
         +++ destruct H12 with v0 lb1; auto.
    ++ exists (Config ct (Container e ((FieldWrite (v_opa_l v lb0) f hole) :: fs) lb sf) ctns h).
         apply ST_fieldWrite3; auto.
         intro contra; inversion contra.
    + right. exists (Config ct (Container x ((FieldWrite hole f e) :: fs) lb sf) ctns h).
      apply ST_fieldWrite1; auto.    

(* if *)
  - pose proof (excluded_middle_value guard). destruct H3; subst; right.
    + inversion H3; subst; inversion H; subst; auto; eauto using reduction.
    + eauto using reduction.

(* sequence *)      
  - right.
    pose proof (excluded_middle_value e1). destruct H2; subst;
    eauto using reduction.       
Qed. Hint Resolve Progress. 