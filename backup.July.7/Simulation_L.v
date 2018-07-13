Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.

Require Import SfLib.
Require Import Language.
Require Import Lemmas.
Require Import Low_eq.
Require Import Label.

Lemma simulation_L : forall ct t1 fs1 lb1 sf1 ctns_stack1 h1  t2 fs2 lb2 sf2 ctns_stack2 h2
      ctn1' ctns_stack1' h1'  ctn2' ctns_stack2' h2' φ, 
      valid_config (Config ct (Container t1 fs1 lb1 sf1) ctns_stack1 h1 ) ->
      valid_config (Config ct (Container t2 fs2 lb2 sf2) ctns_stack2 h2 ) ->
      forall T, config_has_type ct empty_context (Config ct (Container t1 fs1 lb1 sf1) ctns_stack1 h1) T -> 
      config_has_type ct empty_context ((Config ct (Container t2 fs2 lb2 sf2) ctns_stack2 h2 )) T  ->  
      field_wfe_heap ct h1 -> wfe_heap ct h1 ->
      (*wfe_stack_frame ct h1 sf1 -> *)
      field_wfe_heap ct h2 -> wfe_heap ct h2 ->
      (* wfe_stack_frame ct h2 sf2 -> *)
      flow_to lb1 L_Label = true ->
      flow_to lb2 L_Label = true ->
      L_equivalence_config (Config ct (Container t1 fs1 lb1 sf1) ctns_stack1 h1 )
            (Config ct (Container t2 fs2 lb2 sf2) ctns_stack2 h2)  φ ->
     Config ct (Container t1 fs1 lb1 sf1) ctns_stack1 h1 
      ==> Config ct ctn1' ctns_stack1' h1' ->
     Config ct (Container t2 fs2 lb2 sf2) ctns_stack2 h2
      ==> Config ct ctn2' ctns_stack2' h2' ->
     L_equivalence_heap h1 h2 φ ->
      exists  φ', L_equivalence_config (Config ct ctn1' ctns_stack1' h1')
            (Config ct ctn2' ctns_stack2' h2')  φ'.
 Proof with eauto. 
      intros ct t1 fs1 lb1 sf1 ctns_stack1 h1  t2 fs2 lb2 sf2 ctns_stack2 h2
      ctn1' ctns_stack1' h1'  ctn2' ctns_stack2' h2'  φ.
    
      intro H_valid1.       intro H_valid2.
      intro T.
      intro H_typing1. intro H_typing2.
      intro H_wfe_field1. intro H_wfe_heap1.
      intro H_wfe_field2. intro H_wfe_heap2.  
      intro H_flow1. intro H_flow2.
      intro H_low_eq.
      intro H_reduction1.
      intro H_reduction2. 
      intro H_bijection.
     remember (Config ct (Container t1 fs1 lb1 sf1) ctns_stack1 h1) as config1. 
     remember (Config ct ctn1' ctns_stack1' h1') as config1'.
     generalize dependent t1. generalize dependent fs1. generalize dependent lb1. 
     generalize dependent ctns_stack1. generalize dependent h1. 

     generalize dependent t2. generalize dependent fs2. generalize dependent lb2. 
     generalize dependent ctns_stack2. generalize dependent h2. 
     generalize dependent T.
     generalize dependent sf1. generalize dependent sf2.

     induction H_reduction1; intros; auto; inversion Heqconfig1; inversion Heqconfig1'; subst; 
       inversion H_low_eq; subst;  try (inconsist_label).

     Ltac solve_by_invert :=
       match goal with | H : ?T |- _
                         => solve [inversion H; subst; auto]
                          end.
     
     Ltac solve_by_invert_non_value :=
       match goal with | H : ?T |- _ =>
                         match T with
                         | value _  => solve [inversion H; subst]
                         end end.
     
     Ltac solve_by_invert_tm :=
       match goal with | H : ?T |- _ =>
                         match T with 
                         | L_equivalence_tm _ _ _ _ _ => solve [inversion H; subst; try (contradiction); solve_by_invert]
                         end end. 

     Ltac solve_by_invert_ctn :=
       match goal with
       | H : L_eq_container _ _ _ _ _ |- _ =>
          solve [ inversion H; subst; 
                  try (solve_by_invert_tm; subst; intuition); try (solve_by_invert_non_value);
                  try (
                      match goal with
                      | H : L_equivalence_fs _ _ _ _ _ |- _ =>
                        solve [ inversion H; subst; 
                                match goal with
                                | H1 : L_equivalence_tm (_ hole _) _ _ _ _ |- _ =>
                                  inversion H1
                                | H1 : L_equivalence_tm (_ hole _ _) _ _ _ _ |- _ =>
                                  inversion H1
                                | H1 : L_equivalence_tm (_ _ _ hole) _ _ _ _ |- _ =>
                                  inversion H1
                                | H1 : L_equivalence_tm (_ hole ) _ _ _ _ |- _ =>
                                  inversion H1    
                                end
                              ] 
                      end);
                  try (
                      match goal with
                      | H : hole_free _ |- _ =>
                        solve [ inversion H; subst] 
                      end) 
                ]
                
       end. 

     (* var *)

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  inversion H17; subst; auto.
  inversion H19; subst; auto.
  inversion H21; subst; auto.
  inversion H_valid1; subst; auto.
  inversion H26; subst; auto.
  inversion H34; subst; auto.

  assert ( wfe_stack_val ct h1' v). apply H9 with id0; auto.
  inversion H10; subst; auto.
  assert (sf2 id0 = Some null). apply H7; auto.
  rewrite H11 in H1; inversion H1; subst; auto.
  exists φ. auto.
  assert (sf1 id0 = Some (ObjId o)); auto.
  case_eq (flow_to lo L_Label); intro. 
  apply H0 with id0 o (class_def cls_name field_defs method_defs)
                F lo in H23; auto.
  destruct H23 as [o2]. destruct H23. rewrite H23 in H1; inversion H1; subst; auto. 
  exists φ.  auto.


  inversion H_valid2; subst; auto.
  inversion H43; subst; auto.
  inversion H51; subst; auto. 
  
  assert ( wfe_stack_val ct h2' v0). apply H35 with id0; auto.
  inversion H36; subst; auto.
  assert (sf2 id0 = Some null); auto.
  destruct H7 with id0. apply H40 in H37.
  rewrite H37 in H. inversion H.

  assert (sf2 id0 = Some (ObjId o0)); auto.
  case_eq (flow_to lo0 L_Label); intro.
  destruct H2 with id0 o0 (class_def cls_name0 field_defs0 method_defs0)
                   F0 lo0  in H40; auto.
  destruct H52. rewrite H52 in H; inversion H; subst; auto.
  inversion H53; subst; auto.
  rewrite <- H57 in H11; inversion H11; subst; auto.
  try (inconsist_label).

  exists φ.  apply L_equivalence_config_L; auto.

  exists φ.  apply L_equivalence_config_L; auto.
  apply L_eq_ctn; auto.
  remember ((class_def cls_name field_defs method_defs)) as cls1.
  remember (class_def cls_name0 field_defs0 method_defs0) as cls2. 
  apply L_equivalence_tm_eq_object_H with cls1 cls2 F
                                          lo F0 lo0; auto. 

  
  




  apply L_equivalence_tm_eq_object_H with
      (class_def cls_name0 field_defs0 method_defs0)
      F  lo
      F0 lo0; auto.

  inversion H_typing1; subst; auto. inversion H58; subst; auto.
  inversion H61.
  subst; auto. inversion H56. inversion H63. inversion H56. 
  
  
  assert (sf1 id0 = Some null); apply H40; auto. 
  
  
  

        
- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).  
  inversion H17; subst; auto.
  inversion H19; subst; auto. exists φ. auto. 
  inversion H17; subst; auto.
  inversion H20; subst; auto.
  inversion H9; subst; auto; intuition. 

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  inversion H17; subst; auto. 
  inversion H20; subst; auto. inversion H9; subst; auto.  exists φ. auto.
  inversion H17; subst; auto. 
  inversion H21; subst; auto.
  inversion H9; subst; auto.
  inversion H7; subst; auto. inversion H12. 

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  inversion H18; subst; auto.  
  inversion H20; subst; auto.
  inversion H9; subst; auto; intuition. 
  inversion H18; subst; auto.

  exists φ. inversion H21; subst; auto.  inversion H9; subst; auto. 
  inversion H_bijection; subst; auto.
  apply H1 in H3; auto. inversion H3.  subst; auto.
  rewrite <- H5 in H. inversion H. subst; auto. 
  rewrite <- H7 in H4. inversion H4; subst; auto. 

  assert (flow_to (join_label lb0 lb1) L_Label = true).
  apply join_L_label_flow_to_L; auto.
  
  assert (flow_to (join_label lb3 lb2) L_Label = true).
  apply join_L_label_flow_to_L; auto.  
  apply L_equivalence_config_L; auto.
  apply L_eq_ctn; auto.

  rewrite <-H24 in H5; inversion H5; subst; auto.
  rewrite <-H25 in H7; inversion H7; subst; auto.

  apply config_typing_lead_to_tm_typing in H_typing1.
  destruct H_typing1 as [T1].
  destruct H31 as [gamma1].
  
  apply config_typing_lead_to_tm_typing in H_typing2.
  destruct H_typing2 as [T2].
  destruct H32 as [gamma2].

  destruct H28; subst; auto.
  destruct H33; subst; auto.
  destruct H33. destruct H33.
  
  inversion H31; subst; auto. 
  assert (v = null \/ exists o', v = ObjId o').
  apply field_value  with h1' o cls4 F3 lb5 fname0 ct cls' gamma1; auto.

  inversion H32; subst; auto. 
  assert (v0 = null \/ exists o', v0 = ObjId o').
  apply field_value  with h2' o0 cls4 F4 lb5 fname0 ct cls'0 gamma2; auto.

  destruct H35; subst; auto. 
  destruct H33 with fname0.
  assert (F3 fname0 = Some null). auto.
  apply H35 in H42; auto. rewrite <- H13 in H42; inversion H42; subst; auto. 

  destruct H36; subst; auto.
  destruct H33 with fname0.
  assert (F4 fname0 = Some null). auto.
  apply H39 in H42; auto. rewrite <- H0 in H42; inversion H42; subst; auto.

  destruct H35 as [o1]. destruct H36 as [o2].
  subst; auto.
  destruct H34 with fname0 o1 o2; auto. rename x into hfo1.
  destruct H35 as [hfo2].
  destruct H35. destruct H36.
  assert (L_equivalence_object o1 h1' o2 h2' φ).
  apply H1; auto.
  inversion H42; subst; auto. 
  apply L_equivalence_tm_eq_object_L with cls1 F1 lb0 cls2 F2 lb3 ; auto.

  
  assert (flow_to (join_label lo lb1) L_Label = false).
  rewrite <- H3 in H; inversion H; subst; auto.
  apply flow_join_label with lb0 lb1; auto.
  apply join_label_commutative; auto.

  assert (flow_to (join_label lo0 lb2)  L_Label = false).
  rewrite <- H6 in H4; inversion H4; subst; auto.
  apply flow_join_label with lb3 lb2; auto.
  apply join_label_commutative; auto.

  apply L_equivalence_config_H ; auto.

  
  Lemma ctns_eq_lead_to_low_component_eq : forall ct h1 h2
                                                  t1 fs1 lb1 sf1
                                                  t2 fs2 lb2 sf2
                                                  ctns1 ctns2 φ,
      L_eq_ctns ctns1 h1 ctns2 h2 φ ->
      flow_to lb1 L_Label = false ->
      flow_to lb2 L_Label = false ->
      L_equivalence_config
        (low_component ct (Container t1 fs1 lb1 sf1) ctns1 h1)
        (low_component ct (Container t2 fs2 lb2 sf2) ctns2 h2) φ.
  Proof with eauto.
    intros. generalize dependent ctns2. 
    induction ctns1. intros. inversion H; subst.
    unfold low_component. rewrite H0. rewrite H1.
    apply L_equivalence_config_L ; auto.
    apply L_eq_ctn; auto.
    apply L_equivalence_store_L; intros; inversion H2.

    intros. inversion H; subst; auto.
    destruct a. destruct ctn2.
    inversion H4; subst; auto.
    unfold low_component. rewrite H0. rewrite H1.
    fold low_component. 
    
    assert ((low_component ct (Container t f l s) ctns1 h1)  =
            (Config ct (Container t f l s) ctns1 h1)).
    apply low_component_with_L_Label; auto.

    assert ((low_component ct (Container t0 f0 l0 s0) ctns3 h2)  =
            (Config ct (Container t0 f0 l0 s0) ctns3 h2)).
    apply low_component_with_L_Label; auto.

    rewrite H2. rewrite H3.
    apply L_equivalence_config_L ; auto.
Qed. 

  apply ctns_eq_lead_to_low_component_eq ; auto. 
  
      

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  + inversion H17; subst; auto. exists φ. auto.
    inversion H19; subst; auto. 
  + inversion H17; subst; auto.
    intuition.
    inversion H21; subst; auto.
    assert (value e). auto. 
    apply  value_L_eq with v h1' h2' φ; auto. 
    intuition. 
  + inversion H17; subst; auto.
    inversion H21; subst; auto.
    inversion H11; subst; auto; intuition. 
    
  + inversion H17; subst; auto. intuition.
    inversion H21; subst; auto. inversion H11; subst; auto;
    intuition.

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  + inversion H17; subst; auto. exists φ. auto.
    inversion H20; subst; auto.
    inversion H9; subst; auto.
  + inversion H17; subst; auto.
    inversion H21; subst; auto.
    inversion H9; subst; auto.
    inversion H23; subst; auto. inversion H2.
  + inversion H17; subst; auto.
    inversion H21; subst; auto. inversion H9; subst; auto.
    inversion H11; subst; auto.
    inversion H12.

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  + inversion H18; subst; auto. 
    inversion H21; subst; auto.
    inversion H10; subst; auto.
    inversion H23; subst; auto. inversion H.
  + inversion H18; subst; auto. exists φ. auto.
    inversion H22; subst; auto.
    inversion H10; subst; auto.
  + inversion H18; subst; auto. 
    inversion H22; subst; auto.
    inversion H10; subst; auto.
    inversion H14; subst; auto. inversion H13. 
    case_eq ( hole_free e2); intro; rewrite H1 in H2; intuition.

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  + inversion H19; subst; auto.  
    subst. inversion H21; subst; auto.

    assert (value e). apply value_L_eq2 with v h1' h2' φ; auto.
    contradiction.
  + inversion H19; subst; auto.   
    inversion H23; subst; auto.  exists φ. auto.
  + inversion H19; subst; auto. 
    inversion H23; subst; auto.

    assert (value e2). apply value_L_eq with v0 h1' h2' φ; auto. contradiction.
  + inversion H19; subst; auto.
    inversion H23; subst; auto.
    inversion H14; subst; auto.
    destruct H with e1.

    apply value_L_eq with (v_opa_l v0 lx) h1' h2' φ; auto.
    intro contra. rewrite contra in H5. inversion H5.
    auto.                           

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  + inversion H19; subst; auto. 
    inversion H21; subst; auto.
    inversion H13; subst; auto;
    intuition.
    
  + inversion H19; subst; auto. 
    inversion H23; subst; auto. 
    assert (value e2). apply value_L_eq2  with v h1' h2'  φ; auto. contradiction.
  + inversion H19; subst; auto.
    inversion H23; subst; auto.
    inversion H13; subst; auto. 

    assert (cls = cls0). apply cls_def_eq with o o0 fields lx fields0 lx0 h1' h2'  φ; auto.
    subst; auto.
    rewrite <- H0 in H14; inversion H14; subst; auto. 

    exists  φ. apply L_equivalence_config_L; auto.
    apply L_eq_ctn; auto.
    apply surface_syntax_L_equal; auto. 
    inversion H_typing1; subst; auto.

    inversion H28; subst; auto.
    inversion H31; subst; auto.
    inversion H12; subst; auto.
    destruct H36 as [F']. destruct H2 as [lo].
    rewrite H2 in H; inversion H; subst; auto.
    rewrite <- H9 in H27. inversion H27; subst; auto.
    rewrite H29 in H0. inversion H0; subst; auto.

    inversion H33; subst; auto.
    inversion H12; subst; auto. 
    destruct H37 as [F']. destruct H2 as [lo].
    rewrite H2 in H; inversion H; subst; auto.
    rewrite <- H9 in H27. inversion H27; subst; auto.
    rewrite H29 in H0. inversion H0; subst; auto.

    inversion H28; subst; auto.
    inversion H32; subst; auto.
    inversion H12; subst; auto. 
    destruct H37 as [F']. destruct H2 as [lo].
    rewrite H2 in H; inversion H; subst; auto.
    rewrite <- H9 in H27. inversion H27; subst; auto.
    rewrite H30 in H0. inversion H0; subst; auto.

    inversion H34; subst; auto.
    inversion H12; subst; auto.
    destruct H38 as [F']. destruct H2 as [lo].
    rewrite H2 in H; inversion H; subst; auto.
    rewrite <- H9 in H27. inversion H27; subst; auto.
    rewrite H30 in H0. inversion H0; subst; auto.

    inversion H38; subst; auto.
    inversion H27; subst; auto. 
    inversion H12; subst; auto.
    destruct H43 as [F']. destruct H2 as [lo].
    rewrite H2 in H; inversion H; subst; auto.
    rewrite <- H9 in H32. inversion H32; subst; auto.
    rewrite H33 in H0. inversion H0; subst; auto.

    inversion H35. 
    apply  L_equivalence_store_L ; auto.
    
    intros. case_eq (beq_id arg_id x); intro.
    unfold  sf_update in H2. rewrite H12 in H2.
    inversion H2. subst; auto. inversion H16; subst; auto. 
    exists o3. split; auto.
    unfold sf_update. rewrite H12. auto.
    rewrite <- H27 in H3; inversion H3; subst; auto.
    try (inconsist_label).    
    unfold sf_update in H2. rewrite H12 in H2. inversion H2. 

    intros. case_eq (beq_id arg_id x); intro.
    unfold  sf_update in H2. rewrite H12 in H2.
    inversion H2. subst; auto. inversion H16; subst; auto. 
    exists o1. split; auto.
    unfold sf_update. rewrite H12. auto.
    rewrite <- H29 in H3; inversion H3; subst; auto.
    try (inconsist_label).  
    unfold sf_update in H2. rewrite H12 in H2. inversion H2.

    (*(v_l v1 lb)*)
    intros. case_eq (beq_id arg_id x); intro.
    unfold  sf_update in H2. rewrite H9 in H2.
    inversion H2. subst; auto. inversion H16; subst; auto. 
    exists e2. split; auto.
    unfold sf_update. rewrite H9. auto.
    try (inconsist_label).  
    unfold sf_update in H2. rewrite H9 in H2. inversion H2. 
    
    
    intros. case_eq (beq_id arg_id x); intro.
    unfold  sf_update in H2. rewrite H9 in H2.
    inversion H2. subst; auto. inversion H16; subst; auto. 
    exists e1. split; auto.
    unfold sf_update. rewrite H9. auto.
    try (inconsist_label). 
    unfold sf_update in H2. rewrite H9 in H2. inversion H2.

        (*(v_opa_l v1 lb)*)
    intros. case_eq (beq_id arg_id x); intro.
    unfold  sf_update in H2. rewrite H9 in H2.
    inversion H2. subst; auto. inversion H16; subst; auto. 
    exists e2. split; auto.
    unfold sf_update. rewrite H9. auto.
    try (inconsist_label). 
    unfold sf_update in H2. rewrite H9 in H2. inversion H2. 
    
    
    intros. case_eq (beq_id arg_id x); intro.
    unfold  sf_update in H2. rewrite H9 in H2.
    inversion H2. subst; auto. inversion H16; subst; auto. 
    exists e1. split; auto.
    unfold sf_update. rewrite H9. auto.
    try (inconsist_label). 
    unfold sf_update in H2. rewrite H9 in H2. inversion H2.
    rewrite <- H4 in H; inversion H; subst; auto.
    rewrite <- H7 in H6; inversion H6; subst; auto.
    rewrite <- H0 in H14; inversion H14; subst; auto. 
    
    exists φ. apply L_equivalence_config_L; auto.
    apply L_eq_ctn; auto. 

    apply config_typing_lead_to_tm_typing in H_typing1.
    destruct H_typing1 as [T1].
    destruct H2 as [gamma1].
    inversion H2; subst; auto.
    inversion H12; subst; auto.
    destruct H33 as [F0]. destruct H3 as [l0].
    rewrite <- H10 in H27; inversion H27; subst; auto.
    rewrite H3 in H4; inversion H4; subst; auto.
    rewrite H28 in H0; inversion H0; subst; auto.

    apply L_equivalence_store_L; auto.
    
    intros. case_eq (beq_id arg_id x); intro.
    unfold  sf_update in H2. rewrite H10 in H2.
    inversion H2. subst; auto. inversion H16; subst; auto. 
    exists o3. split; auto.
    unfold sf_update. rewrite H10. auto.
    rewrite <- H26 in H3; inversion H3; subst; auto.
    try (inconsist_label).    
    unfold sf_update in H2. rewrite H10 in H2. inversion H2. 

    intros. case_eq (beq_id arg_id x); intro.
    unfold  sf_update in H2. rewrite H10 in H2.
    inversion H2. subst; auto. inversion H16; subst; auto. 
    exists o1. split; auto.
    unfold sf_update. rewrite H10. auto.
    rewrite <- H28 in H3; inversion H3; subst; auto.
    try (inconsist_label).  
    unfold sf_update in H2. rewrite H10 in H2. inversion H2.

    (*(v_l v1 lb)*)
    intros. case_eq (beq_id arg_id x); intro.
    unfold  sf_update in H2. rewrite H8 in H2.
    inversion H2. subst; auto. inversion H16; subst; auto. 
    exists e2. split; auto.
    unfold sf_update. rewrite H8. auto.
    try (inconsist_label).  
    unfold sf_update in H2. rewrite H8 in H2. inversion H2. 
    
    
    intros. case_eq (beq_id arg_id x); intro.
    unfold  sf_update in H2. rewrite H8 in H2.
    inversion H2. subst; auto. inversion H16; subst; auto. 
    exists e1. split; auto.
    unfold sf_update. rewrite H8. auto.
    try (inconsist_label). 
    unfold sf_update in H2. rewrite H8 in H2. inversion H2.

        (*(v_opa_l v1 lb)*)
    intros. case_eq (beq_id arg_id x); intro.
    unfold  sf_update in H2. rewrite H8 in H2.
    inversion H2. subst; auto. inversion H16; subst; auto. 
    exists e2. split; auto.
    unfold sf_update. rewrite H8. auto.
    try (inconsist_label). 
    unfold sf_update in H2. rewrite H8 in H2. inversion H2. 
    
    
    intros. case_eq (beq_id arg_id x); intro.
    unfold  sf_update in H2. rewrite H8 in H2.
    inversion H2. subst; auto. inversion H16; subst; auto. 
    exists e1. split; auto.
    unfold sf_update. rewrite H8. auto.
    try (inconsist_label). 
    unfold sf_update in H2. rewrite H8 in H2. inversion H2.

    
  + inversion H19; subst; auto.
    inversion H23; subst; auto.
    
    inversion H14; subst; auto.
    inversion H1. 

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  inversion H19; subst; auto. 
  inversion H21; subst; auto.
  inversion H13; subst; auto. intuition. 

  inversion H19; subst; auto. intuition.

  inversion H19; subst; auto.
  inversion H23; subst; auto.  
  inversion H16; subst; auto.  
  inversion H1; subst; auto.
  destruct H5 with (v_opa_l e2 lx); auto.
  intro contra. inversion contra. 

  destruct H5 with (v_opa_l e2 l2); auto.
  intro contra. inversion contra.

  inversion H19; subst; auto.
  inversion H23; subst; auto.
  inversion H16; subst; auto.
  inversion H15. 

  inversion H19; subst; auto.
  inversion H23; subst; auto.
  inversion H14; subst; auto.
  inversion H5; subst; auto.
  inversion H13; subst; auto.

  inversion   H_bijection; subst; auto.
  destruct H0 with o o0; auto.
  rewrite <- H32 in H. inversion H; subst; auto.
  rewrite <- H33 in H7; inversion H7; subst; auto.
  destruct H36.  destruct H37; subst; auto.
  destruct H38.  destruct H37. 
  rewrite <- H21 in H3; inversion H3; subst; auto.
  exists  φ. apply L_equivalence_config_L; auto.

  apply join_L_label_flow_to_L; auto. 
  apply join_L_label_flow_to_L; auto. 

  apply L_eq_ctn; auto. 
  apply join_L_label_flow_to_L; auto. 
  apply join_L_label_flow_to_L; auto. 

  apply surface_syntax_L_equal; auto.
  apply config_typing_lead_to_tm_typing in H_typing1.
  destruct H_typing1 as [T1].
  destruct H39 as [gamma1].
  inversion H39; subst; auto.
  inversion H43; subst; auto. 
  destruct H51 as [F']. destruct H40 as [lb'].
  rewrite H40 in H32. inversion H32. subst; auto.
  rewrite <- H42 in H45; inversion H45; subst; auto.
  rewrite H46 in H21. inversion H21; subst; auto. 
  
  rename arg_id0 into arg_id.  
  apply  L_equivalence_store_L ; auto.

  intros. case_eq (beq_id arg_id x); intro.
  unfold  sf_update in H39. rewrite H42 in H39.
  inversion H39. subst; auto. inversion H28; subst; auto. 
  exists o4. split; auto.
  unfold sf_update. rewrite H42. auto.
  rewrite <- H44 in H40. inversion H40; subst; auto.
  try (inconsist_label). 
  unfold  sf_update in H39. rewrite H42 in H39. inversion H39.

  intros. case_eq (beq_id arg_id x); intro.
  unfold  sf_update in H39. rewrite H42 in H39.
  inversion H39; subst; auto. 
  inversion H28. subst; auto. 
  exists o3. split; auto.
  unfold sf_update. rewrite H42. auto.
  rewrite <- H46 in H40. inversion H40; subst; auto. 
  try (inconsist_label).
  unfold  sf_update in H39. rewrite H42 in H39. inversion H39.

  (*(v_l v1 lb)*)
  intros. case_eq (beq_id arg_id x); intro.
  unfold  sf_update in H39. rewrite H41 in H39.
  inversion H39. subst; auto. inversion H28; subst; auto. 
  exists e2. split; auto.
  unfold sf_update. rewrite H41. auto.
  try (inconsist_label). 
  unfold  sf_update in H39. rewrite H41 in H39. inversion H39.

  intros. case_eq (beq_id arg_id x); intro.
  unfold  sf_update in H39. rewrite H41 in H39.
  inversion H39; subst; auto. 
  inversion H28. subst; auto. 
  exists e1. split; auto.
  unfold sf_update. rewrite H41. auto. subst; auto. 
  try (inconsist_label).
  unfold  sf_update in H39. rewrite H41 in H39. inversion H39.

  (*(v_opa_l v1 lb)*)
  intros. case_eq (beq_id arg_id x); intro.
  unfold  sf_update in H39. rewrite H41 in H39.
  inversion H39. subst; auto. inversion H28; subst; auto. 
  exists e2. split; auto.
  unfold sf_update. rewrite H41. auto.
  try (inconsist_label). 
  unfold  sf_update in H39. rewrite H41 in H39. inversion H39.

  intros. case_eq (beq_id arg_id x); intro.
  unfold  sf_update in H39. rewrite H41 in H39.
  inversion H39; subst; auto. 
  inversion H28. subst; auto. 
  exists e1. split; auto.
  unfold sf_update. rewrite H41. auto. subst; auto. 
  try (inconsist_label).
  unfold  sf_update in H39. rewrite H41 in H39. inversion H39.


  
  apply config_typing_lead_to_tm_typing in H_typing1.
  destruct H_typing1 as [T1].
  destruct H0 as [gamma1].
  inversion H0; subst; auto.
  inversion H30; subst; auto.
  destruct H38 as [F0]. destruct H1 as [l0].
  rewrite  H1 in H; inversion H; subst; auto.
  rewrite H1 in H4; inversion H4; subst; auto. 
  rewrite <- H32 in H29; inversion H29; subst; auto.
  rewrite H33 in H3; inversion H3; subst; auto.
  rewrite <- H9 in H7; inversion H7; subst; auto.
  rewrite H33 in H21; inversion H21; subst; auto.

  exists  φ. apply L_equivalence_config_L; auto.
  apply join_L_label_flow_to_L; auto.
  apply join_L_label_flow_to_L; auto.

  apply L_eq_ctn; auto. 
  apply join_L_label_flow_to_L; auto.
  apply join_L_label_flow_to_L; auto.

  rename arg_id1 into arg_id. 
  apply L_equivalence_store_L; auto.
  
  
  intros. case_eq (beq_id arg_id x); intro.
  unfold  sf_update in H11. rewrite H36 in H11.
  inversion H11. subst; auto.
  inversion H28; subst; auto. 
  exists o3. split; auto.
  unfold sf_update. rewrite H36. auto.
  rewrite <- H41 in H34. inversion H34; subst; auto.
  try (inconsist_label). 
  unfold  sf_update in H11. rewrite H36 in H11. inversion H11.

  intros. case_eq (beq_id arg_id x); intro.
  unfold  sf_update in H11. rewrite H36 in H11.
  inversion H11; subst; auto. 
  inversion H28. subst; auto. 
  exists o1. split; auto.
  unfold sf_update. rewrite H36. auto.
  rewrite <- H43 in H34. inversion H34; subst; auto. 
  try (inconsist_label).
  unfold  sf_update in H11. rewrite H36 in H11. inversion H11.

  (*(v_l v1 lb)*)
  intros. case_eq (beq_id arg_id x); intro.
  unfold  sf_update in H11. rewrite H35 in H11.
  inversion H11. subst; auto.
  inversion H28; subst; auto. 
  exists e2. split; auto.
  unfold sf_update. rewrite H35. auto.
  try (inconsist_label). 
  unfold  sf_update in H11. rewrite H35 in H11. inversion H11.

  intros. case_eq (beq_id arg_id x); intro.
  unfold  sf_update in H11. rewrite H35 in H11.
  inversion H11. subst; auto.
  inversion H28; subst; auto. 
  exists e1. split; auto.
  unfold sf_update. rewrite H35. auto.
  try (inconsist_label). 
  unfold  sf_update in H11. rewrite H35 in H11. inversion H11.
  
  (*(v_opa_l v1 lb)*)
  intros. case_eq (beq_id arg_id x); intro.
  unfold  sf_update in H11. rewrite H35 in H11.
  inversion H11. subst; auto.
  inversion H28; subst; auto. 
  exists e2. split; auto.
  unfold sf_update. rewrite H35. auto.
  try (inconsist_label). 
  unfold  sf_update in H11. rewrite H35 in H11. inversion H11.

  intros. case_eq (beq_id arg_id x); intro.
  unfold  sf_update in H11. rewrite H35 in H11.
  inversion H11. subst; auto.
  inversion H28; subst; auto. 
  exists e1. split; auto.
  unfold sf_update. rewrite H35. auto.
  try (inconsist_label). 
  unfold  sf_update in H11. rewrite H35 in H11. inversion H11.
  

  
  exists  φ. apply L_equivalence_config_H; auto. 
  apply flow_join_label with lx lb1; auto.
  apply flow_join_label with lx0 lb2; auto. 
  unfold low_component.
  assert (flow_to (join_label lb1 lx) L_Label = false).
  apply flow_join_label with lx lb1; auto.
  rewrite H0 .
  assert (flow_to (join_label lb2 lx0) L_Label = false).
  apply flow_join_label with lx0 lb2; auto. 
  rewrite H1.
  fold low_component.
  assert ((low_component ct (Container return_hole fs1 lb1 sf1)
                             ctns_stack1 h1') =
          Config ct (Container return_hole fs1 lb1 sf1) ctns_stack1 h1'). apply low_component_with_L_Label; auto. rewrite H4.
  assert ((low_component ct (Container return_hole fs2 lb2 sf2)
                             ctns_stack2 h2') =
          Config ct (Container return_hole fs2 lb2 sf2) ctns_stack2 h2'). apply low_component_with_L_Label; auto. rewrite H6.
  auto. 


- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  inversion   H_bijection; subst; auto.
  assert (lookup_heap_obj h1 (get_fresh_oid h1)  = None). 
  apply fresh_oid_heap with ct; auto.
  assert (lookup_heap_obj h2 (get_fresh_oid h2)  = None). 
  apply fresh_oid_heap with ct; auto.
  apply H1 in H6.
  apply H2 in H7.
  assert (forall a1 a2 : oid, decision.Decision (a1 = a2)). auto.
  
  exists  (bijection.extend_bijection φ (get_fresh_oid h1)  (get_fresh_oid h2) H6 H7). auto.
  apply L_equivalence_config_L; auto.
  
  subst; auto.
  inversion H17; subst; auto.
  (*
  rewrite H5 in H; inversion H; subst; auto.
*)
  inversion H27; subst; auto.
  rewrite H5 in H; inversion H; subst; auto.
  apply  L_Label_flow_to_L in H25.
  apply  L_Label_flow_to_L in H26.  rewrite <- H25 in H26.
  subst; auto.
  apply L_eq_ctn; auto.

  apply L_equivalence_tm_eq_object_L with (class_def cls_name0 field_defs method_defs)
                                          (init_field_map (find_fields (class_def cls_name0 field_defs method_defs)) empty_field_map)
                                          L_Label
                                          (class_def cls_name0 field_defs method_defs)
                                          (init_field_map (find_fields (class_def cls_name0 field_defs method_defs)) empty_field_map)
                                          L_Label

  ; auto. 
  apply extend_heap_preserve_L_eq_fs with ct φ H6 H7; auto.
  apply extend_heap_preserve_L_eq_store with ct φ H6 H7; auto.
  inversion  H_valid1; subst; auto.
  inversion H22; auto. 
  inversion  H_valid2; subst; auto.
  inversion H22; auto. 
  inversion H17; subst; auto.

  inversion H27; subst; auto.


  rewrite H5 in H; inversion H; subst; auto.
  apply  L_Label_flow_to_L in H25.
  apply  L_Label_flow_to_L in H26.  rewrite <- H25 in H26.
  subst; auto.
  apply extend_heap_preserve_L_eq_ctns with ct φ H6 H7; auto.
    inversion  H_valid1; subst; auto.
  inversion  H_valid2; subst; auto.

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  inversion H17; subst; auto. 
  inversion H19; subst; auto. exists φ. auto.
  inversion H17; subst; auto. intuition.  
  inversion H19; subst; auto. 
  assert (value e). apply value_L_eq with v h1' h2'  φ; auto.
  intuition. 

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  inversion H17; subst; auto. 
  inversion H20; subst; auto. inversion H9; subst; auto. 
  exists φ. auto.
  inversion H17; subst; auto.
  inversion H21; subst; auto. inversion H9; subst;auto.
  inversion H3; subst; auto.
  inversion H12. 

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  inversion H17; subst; auto.
  inversion H19; subst; auto.
  assert (value e). apply value_L_eq2 with v h1' h2'  φ; auto.
  intuition.
  inversion H17; subst; auto.
  
  inversion H19; subst; auto. exists φ.
  apply L_equivalence_config_L; auto.
  apply L_eq_ctn; auto.
  case_eq (flow_to lo0 L_Label); intro; auto. 

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  inversion H17; subst; auto.  
  inversion H19; subst; auto.  exists φ. auto.
  inversion H17; subst; auto.
  inversion H19; subst; auto.
  inversion H3; subst; auto; intuition. 

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  inversion H17; subst; auto.  
  inversion H20; subst; auto.  exists φ. auto.
  inversion H17; subst; auto.
  inversion H21; subst; auto. inversion H9; subst; auto.
  inversion H1; subst; auto.
  inversion H12.

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  inversion H17; subst; auto. 
  inversion H19; subst; auto.
  inversion H4; subst; auto; intuition.

  inversion H17; subst; auto.
  (*
  case_eq (flow_to (join_label lb2 lo0) L_Label); intro;
    exists φ. auto.

  apply L_equivalence_config_H; auto.*)
  inversion H18; subst; auto.
  inversion H19; subst; auto.
  inversion H3; subst; auto.
  
  assert (flow_to (join_label lb1 lo0) L_Label = true).
  apply join_L_label_flow_to_L; auto.
  assert (flow_to (join_label lb2 lo0) L_Label = true).
  apply join_L_label_flow_to_L; auto. 
  exists φ. auto. 

  assert (flow_to (join_label lb1 lo) L_Label = false). 
  apply flow_join_label with lo lb1; auto. 
  assert (flow_to (join_label lb2 lo0) L_Label = false). 
  apply flow_join_label with lo0 lb2; auto.

  exists φ.
  apply L_equivalence_config_H; auto. 
  unfold low_component. rewrite H. rewrite H1. auto.
  apply L_equivalence_config_L; auto.
  apply L_eq_ctn; auto. apply L_equivalence_store_L; intros; inversion H2. 

  exists φ.
  inversion H19; subst; auto.
  inversion H5; subst; auto.
  assert (flow_to (join_label lb1 lo0) L_Label = true).
  apply join_L_label_flow_to_L; auto.
  assert (flow_to (join_label lb2 lo0) L_Label = true).
  apply join_L_label_flow_to_L; auto.
  auto.

  assert (flow_to (join_label lb1 lo) L_Label = false). 
  apply flow_join_label with lo lb1; auto. 
  assert (flow_to (join_label lb2 lo0) L_Label = false). 
  apply flow_join_label with lo0 lb2; auto.

  apply L_equivalence_config_H; auto.
  unfold low_component.
  rewrite H2.  rewrite H3. fold low_component.
  auto.

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  inversion H17; subst; auto.   
  inversion H19; subst; auto.  exists φ. auto.
  
  inversion H17; subst; auto. 
  inversion H19; subst; auto.
  inversion H4; subst; auto; intuition. 

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  inversion H17; subst; auto.  
  inversion H20; subst; auto.  exists φ. auto.
  
  inversion H17; subst; auto. 
  inversion H21; subst; auto.
  inversion H9; subst; auto.
  inversion H1; subst; auto. inversion H12.

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  inversion H17; subst; auto. 
  inversion H19; subst; auto.
  inversion H4; subst; auto; intuition. 

  inversion H17; subst; auto.

  inversion H19; subst; auto.
  inversion H4; subst; auto.
  
  exists φ. auto.
  exists φ. 
  apply H_Label_not_flow_to_L in H6. 
  apply H_Label_not_flow_to_L in H9. subst; auto. 
 
- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  inversion H17; subst; auto.  
  inversion H19; subst; auto.  exists φ. auto.
  
  inversion H17; subst; auto. 
  inversion H19; subst; auto.
  inversion H3; subst; auto; intuition. 

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  inversion H17; subst; auto.  
  inversion H20; subst; auto.  exists φ. auto.
  
  inversion H17; subst; auto. 
  inversion H21; subst; auto.
  inversion H9; subst; auto.
  inversion H1; subst; auto. inversion H12. 

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  inversion H17; subst; auto. 
  inversion H19; subst; auto.
  inversion H4; subst; auto; intuition. 


  inversion H17; subst; auto.

  inversion H19; subst; auto.
  inversion H3; subst; auto. 
 
  assert (flow_to (join_label lb1 lo0) L_Label = true).
  apply join_L_label_flow_to_L; auto.
  assert (flow_to (join_label lb2 lo0) L_Label = true).
  apply join_L_label_flow_to_L; auto.
  exists φ. auto.

  assert (flow_to (join_label lb1 lo) L_Label = false). 
  apply flow_join_label with lo lb1; auto. 
  assert (flow_to (join_label lb2 lo0) L_Label = false). 
  apply flow_join_label with lo0 lb2; auto.

  exists φ. 
  apply L_equivalence_config_H; auto.
  destruct ctns_stack1'; inversion H18; subst; auto;
    unfold low_component; rewrite H; rewrite H1; auto.
  apply L_equivalence_config_L; auto.
  apply L_eq_ctn; auto.
  apply L_equivalence_store_L; auto.
  intros. inversion H2. intros. inversion H2.
  intros. inversion H2.  intros. inversion H2.
  intros. inversion H2. intros. inversion H2.

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  inversion H17; subst; auto.
  inversion H19; subst; auto. exists φ. auto. 
  inversion H17; subst; auto.
  inversion H19; subst; auto.
  assert (value e). apply value_L_eq with v h1' h2' φ; auto. intuition.
  
- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  inversion H17; subst; auto.  
  inversion H20; subst; auto.
  inversion H9; subst; auto.  exists φ. auto.

  inversion H17; subst; auto.

  inversion H21; subst; auto.
  inversion H9; subst; auto.
  inversion H3; subst; auto. inversion H12. 

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  inversion H17; subst; auto.
  inversion H19; subst; auto.
  assert (value e). apply value_L_eq2 with v h1' h2' φ; auto. intuition.
  exists φ. auto. 
  inversion H17; subst; auto.
  inversion H19; subst; auto.
  apply L_equivalence_config_L; auto.
  apply L_eq_ctn; auto.
  rename id0 into arg_id. 
  apply L_equivalence_store_L; auto; intros. 

  (* v *)
  case_eq (beq_id arg_id x); intro.
  unfold  sf_update in H0. rewrite H4 in H0.
  inversion H0. subst; auto.
  inversion H8; subst; auto. 
  exists o2. split; auto.
  unfold sf_update. rewrite H4. auto.
  rewrite <- H6 in H1; inversion H1; subst; auto.
  try (inconsist_label).    
  unfold sf_update in H0. rewrite H4 in H0.
  unfold sf_update. rewrite H4.
  inversion H21; subst; auto.
  destruct H5 with x o1 cls1 F1 lb0; auto.
  rename x0 into o2. destruct H22.
  exists o2; auto. 
  
  case_eq (beq_id arg_id x); intro.
  unfold  sf_update in H0. rewrite H4 in H0.
  inversion H0. subst; auto.
  inversion H8; subst; auto. 
  exists o1. split; auto.
  unfold sf_update. rewrite H4. auto.
  rewrite <- H10 in H1; inversion H1; subst; auto.
  try (inconsist_label).    
  unfold sf_update in H0. rewrite H4 in H0.
  unfold sf_update. rewrite H4.
  inversion H21; subst; auto.
  destruct H6 with x o2 cls2 F2 lb0; auto.
  rename x0 into o1. destruct H22.
  exists o1; auto.


  (*(v_l v1 lb)*)
  case_eq (beq_id arg_id x); intro.
  unfold  sf_update in H0. rewrite H3 in H0.
  inversion H0. subst; auto.
  inversion H8; subst; auto. 
  exists e2. split; auto.
  unfold sf_update. rewrite H3. auto.
  try (inconsist_label).    
  unfold sf_update in H0. rewrite H3 in H0.
  unfold sf_update. rewrite H3.
  inversion H21; subst. auto.
  
  case_eq (beq_id arg_id x); intro.
  unfold  sf_update in H0. rewrite H3 in H0.
  inversion H0. subst; auto.
  inversion H8; subst; auto. 
  exists e1. split; auto.
  unfold sf_update. rewrite H3. auto.
  try (inconsist_label).    
  unfold sf_update in H0. rewrite H3 in H0.
  unfold sf_update. rewrite H3.
  inversion H21; subst; auto.

        (*(v_opa_l v1 lb)*)
  case_eq (beq_id arg_id x); intro.
  unfold  sf_update in H0. rewrite H3 in H0.
  inversion H0. subst; auto.
  inversion H8; subst; auto. 
  exists e2. split; auto.
  unfold sf_update. rewrite H3. auto.
  try (inconsist_label).    
  unfold sf_update in H0. rewrite H3 in H0.
  unfold sf_update. rewrite H3.
  inversion H21; subst. auto.
  
  case_eq (beq_id arg_id x); intro.
  unfold  sf_update in H0. rewrite H3 in H0.
  inversion H0. subst; auto.
  inversion H8; subst; auto. 
  exists e1. split; auto.
  unfold sf_update. rewrite H3. auto.
  try (inconsist_label).    
  unfold sf_update in H0. rewrite H3 in H0.
  unfold sf_update. rewrite H3.
  inversion H21; subst; auto.


- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  inversion H17; subst; auto.   
  inversion H19; subst; auto.   exists φ. auto.
  
  inversion H17; subst; auto. 
  inversion H21; subst; auto.
  assert (value e). apply value_L_eq with  v h1' h2'  φ; auto.
  intuition. 

  inversion H17; subst; auto.
  inversion H21; subst; auto.
  assert (value e). apply value_L_eq with  (ObjId o) h1' h2'  φ; auto.
  intuition. 
  
  inversion H17; subst; auto. 
  inversion H21; subst; auto.
  inversion H11; subst; auto.
  assert (value (ObjId o1)); auto. intuition.

  inversion H21; subst; auto.
  assert (value (ObjId o1)); auto. intuition.

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  inversion H17; subst; auto.  
  inversion H20; subst; auto.
  inversion H9; subst; auto. exists φ. auto.
  
  inversion H17; subst; auto. 
  inversion H21; subst; auto.
  inversion H9; subst; auto.
  inversion H23; subst; auto. inversion H12.

  inversion H17; subst; auto. 
  inversion H21; subst; auto. inversion H9; subst; auto.
  inversion H4; subst; auto. inversion H12. 

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  inversion H19; subst; auto. 
  inversion H21; subst; auto.  
  assert (value e). apply value_L_eq2 with v h1' h2' φ; auto.
  intuition.

  inversion H19; subst; auto.
  inversion H23; subst; auto. exists φ. auto.

  inversion H19; subst; auto.
  inversion H23. subst; auto.
  assert (value e2). apply value_L_eq with v0 h1' h2' φ; auto. intuition.

  inversion H19; subst; auto.
  inversion H23; subst; auto. 
  inversion H26; subst; auto.
  inversion H5; subst; auto.
  destruct H with  (v_opa_l e0 lx); auto.
  intro contra. inversion contra. 

  destruct H with (v_opa_l e0 l1); auto.
  intro contra. inversion contra. 

  
- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  inversion H18; subst; auto.
  
  inversion H21; subst; auto.
  inversion H10; subst; auto.
  inversion H23; subst; auto.  inversion H0.

  inversion H18; subst; auto. 
  inversion H22; subst; auto.
  inversion H10; subst; auto.  exists φ. auto.

  inversion H18; subst; auto.
  
  inversion H22; subst; auto.
  inversion H10; subst; auto.
  inversion H24; subst; auto.
  inversion H13.
  case_eq (hole_free e2); intro; rewrite H1 in H2; inversion H2.

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  inversion H19; subst; auto. 
  inversion H21; subst; auto.
  inversion H13; subst; auto;  intuition.
  inversion H19; subst; auto. 
  inversion H23; subst; auto.
  assert (value e2). apply value_L_eq2 with v h1' h2'  φ; auto. intuition.

  inversion H19; subst; auto. 
  inversion H23; subst; auto. exists φ. auto.

  inversion H19; subst; auto. 
  inversion H23; subst.
  inversion H26; subst; auto. inversion H3. 
  
- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  inversion H19; subst; auto. 
  inversion H21; subst; auto.
  inversion H24; subst; auto.
  inversion H13; subst; auto. intuition. 
  
  inversion H19; subst; auto. intuition. 

  inversion H19; subst; auto.
  inversion H23; subst; auto.
  inversion H26; subst; auto. 
  inversion H2; subst; auto.
  destruct H5 with (v_opa_l e2 lx); auto.
  intro contra. inversion contra.

  destruct H5 with  (v_opa_l e2 lx); auto.
  intro contra. inversion contra. 

  inversion H26; subst; auto.
  destruct H5 with  (v_opa_l e2 l2); auto.
  intro contra. inversion contra. 

  inversion H19; subst; auto.

  inversion H23; subst; auto.
  inversion H26; subst; auto. inversion H21. 

  inversion H19; subst; auto.
  inversion H23; subst; auto.
  inversion H13; subst; auto.
  inversion H26; subst; auto. 

  exists  φ. inversion H11; subst; auto. 
  apply L_equivalence_config_L; auto.
  assert (forall a1 a2 : oid, decision.Decision (a1 = a2)). auto.
  apply update_field_preserve_L_eq_ctn with  ct lb1 lx0 lb2 lx0; auto.
  inversion  H_valid1; subst;  auto. 
  apply valid_container; auto; inversion H36; auto.
  inversion  H_valid2; subst;  auto. 
  apply valid_container; auto; inversion H36; auto.

  assert (forall a1 a2 : oid, decision.Decision (a1 = a2)). auto.
  apply update_field_preserve_L_eq_ctns  with  ct lb1 lx0 lb2 lx0; auto.
  inversion  H_valid1; subst;  auto.
  inversion  H_valid2; subst;  auto.

  
  apply L_equivalence_config_L; auto.
  
  assert (forall a1 a2 : oid, decision.Decision (a1 = a2)). auto.
  apply update_field_preserve_L_eq_ctn with  ct lb1 lx lb2 lx0; auto.
  inversion  H_valid1; subst;  auto. 
  apply valid_container; auto; inversion H36; auto.
  inversion  H_valid2; subst;  auto. 
  apply valid_container; auto; inversion H36; auto.

  assert (forall a1 a2 : oid, decision.Decision (a1 = a2)). auto.
  apply update_field_preserve_L_eq_ctns  with  ct lb1 lx lb2 lx0; auto.
  inversion  H_valid1; subst;  auto.
  inversion  H_valid2; subst;  auto.

  
  exists  φ. apply L_equivalence_config_L; auto.
  assert (forall a1 a2 : oid, decision.Decision (a1 = a2)). auto.
  apply update_field_preserve_L_eq_ctn  with  ct lb1 lx lb2 lx0; auto.
  inversion H26; auto.
  inversion H_valid1; subst; auto.
  inversion H30; subst; auto.
  inversion H_valid2; subst; auto.
  inversion H30; subst; auto. 

  assert (forall a1 a2 : oid, decision.Decision (a1 = a2)). auto.
  apply update_field_preserve_L_eq_ctns  with  ct lb1 lx lb2 lx0; auto.
  inversion H26; auto.
  inversion H_valid1; subst; auto.
  inversion H_valid2; subst; auto.
  
- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  inversion H17; subst; auto. 
  inversion H19; subst; auto. exists φ. auto.
  
  inversion H17; subst; auto. 
  inversion H14; subst; auto. 
  inversion H10; subst; auto. intuition. 

  inversion H17; subst; auto. 
  inversion H14; subst; auto. 
  inversion H10; subst; auto. intuition. 


- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  inversion H17; subst; auto.
  inversion H20; subst; auto.
  inversion H9; subst; auto. exists φ. auto.

  
  inversion H17; subst; auto.
  inversion H21; subst; auto.  
  inversion H9; subst; auto.
  inversion H4; subst; auto.
  inversion H12. 

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  inversion H16; subst; auto.
  inversion H18; subst; auto.
  inversion H10; subst; auto. intuition. 

  inversion H16; subst; auto.
  inversion H13; subst; auto.
  
  exists φ. auto.

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  inversion H16; subst; auto.
  inversion H18; subst; auto.
  inversion H10; subst; auto. intuition. 

  inversion H16; subst; auto.
  inversion H13; subst; auto. 
  exists φ. auto.

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
   inversion H16; subst; auto.  
  inversion H13; subst; auto.  exists φ. auto.


- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  inversion H16; subst; auto.  
  inversion H18; subst; auto.  exists φ. auto. 

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn; fail).
  try (inversion H18; subst; auto;  inversion H0;
  inversion H21; subst; auto;
  inversion H11; subst; auto;
  inversion H10; subst; auto;
  inversion H0).

  inversion H18; subst; auto.
  inversion H21; subst; auto.
  inversion H10; subst; auto.
  inversion H12; subst; auto.
  inversion H0.

  inversion H18; subst; auto.
  inversion H22; subst; auto.
  inversion H10; subst; auto.
  inversion H14; subst; auto.
  inversion H0. 
  case_eq ( hole_free e1 ); intro; rewrite H1 in H2; intuition.

  inversion H18; subst; auto.
  inversion H21; subst; auto.
  inversion H10; subst; auto.
  inversion H6; subst; auto.
  inversion H0.

    inversion H18; subst; auto.
  inversion H21; subst; auto.
  inversion H10; subst; auto.
  inversion H5; subst; auto.
  inversion H0.

  inversion H18; subst; auto.

  inversion H21; subst; auto.
  inversion H10; subst; auto.
  inversion H5; subst; auto.
  inversion H0.
  
  inversion H18; subst; auto.
  inversion H21; subst; auto.
  inversion H10; subst; auto.
  inversion H5; subst; auto.
  inversion H0.

  inversion H18; subst; auto.
  inversion H21; subst; auto.
  inversion H10; subst; auto.
  inversion H6; subst; auto.
  inversion H0.

  inversion H18; subst; auto.
  inversion H21; subst; auto.
  inversion H10; subst; auto.
  inversion H7; subst; auto.
  inversion H0.
  
  inversion H18; subst; auto.
  inversion H22; subst; auto.
  inversion H10; subst; auto.
  inversion H24; subst; auto.
  inversion H0. 
  case_eq ( hole_free e1 ); intro; rewrite H1 in H2; intuition.

  inversion H18; subst; auto.
  inversion H21; subst; auto.
  inversion H10; subst; auto.
  inversion H7; subst; auto. 
  inversion H0. 
  
  inversion H18; subst; auto.
  inversion H22; subst; auto.
  exists φ. auto.
  

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  inversion H17; subst; auto.
  inversion H18; subst; auto.
  inversion H9; subst; auto. 
  exists φ.
  apply  L_equivalence_config_L; auto.
  apply L_eq_ctn; auto. auto.
  
  apply L_Label_flow_to_L in H13.
  apply L_Label_flow_to_L in H14.
  rewrite <- H24 in H25. subst; auto.
Qed. 