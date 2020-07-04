Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.

Require Import SfLib.
Require Import Language Types.
Require Import Lemmas.
Require Import Low_eq.
Require Import Label.


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
    apply L_equivalence_store_L; intros.
    split; auto.
    intros. try (empty_sf).
    split; auto. 
    
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


  Lemma beq_id_same : forall o, beq_id o o = true. 
    Proof with auto. 
      intro o. unfold beq_id. destruct o. case_eq (string_dec s s).
      intros. auto. intros. intuition. 
  Qed.       

    Lemma sf_update_non_empty : forall arg_id  v,
        sf_update empty_stack_frame arg_id v <> empty_stack_frame.
    Proof with eauto.
      intros. intro contra.
      assert (forall a, ( sf_update empty_stack_frame arg_id v ) a =  empty_stack_frame a) .
      rewrite contra. auto.
      assert (sf_update empty_stack_frame arg_id v arg_id  = empty_stack_frame arg_id).
      rewrite contra. auto.
      pose proof (beq_id_same arg_id).
      unfold sf_update in H0. rewrite H1 in H0.
      inversion H0. 
    Qed.

    

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
      exists  φ', (L_equivalence_heap h1' h2'  φ') /\ L_equivalence_config (Config ct ctn1' ctns_stack1' h1')
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
  destruct H0.
  exists φ. split; auto.
  apply L_equivalence_config_L; auto.
  apply L_eq_ctn; auto.
  apply H0 with id0; auto.
  inversion H_valid1; subst; auto.  
  inversion H12; subst; auto.
  inversion H28; subst; auto.
  assert (sf1 id0 = Some v); auto. 
  apply H3 in H4. apply H4. 

  inversion H_valid2; subst; auto.
  inversion H12; subst; auto.
  inversion H28; subst; auto.
  assert (sf2 id0 = Some v0); auto. 
  apply H3 in H4. apply H4. 
        
- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).  
  inversion H17; subst; auto.
  inversion H19; subst; auto. exists φ. split; auto. 
  inversion H17; subst; auto.
  inversion H20; subst; auto.
  inversion H9; subst; auto; intuition. 

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  inversion H17; subst; auto. 
  inversion H20; subst; auto. inversion H9; subst; auto.
  exists φ. split; auto.
  inversion H17; subst; auto. 
  inversion H21; subst; auto.
  inversion H9; subst; auto.
  inversion H7; subst; auto. inversion H12. 

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  inversion H18; subst; auto.  
  inversion H20; subst; auto.
  inversion H9; subst; auto; intuition. 
  inversion H18; subst; auto.

  exists φ. split; auto. inversion H21; subst; auto.  inversion H9; subst; auto. 
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

  intro contra; inversion contra.
  intro contra; inversion contra. 

  
  assert (flow_to (join_label lo lb1) L_Label = false).
  rewrite <- H3 in H; inversion H; subst; auto.
  apply flow_join_label with lb0 lb1; auto.
  apply join_label_commutative; auto.

  assert (flow_to (join_label lo0 lb2)  L_Label = false).
  rewrite <- H6 in H4; inversion H4; subst; auto.
  apply flow_join_label with lb3 lb2; auto.
  apply join_label_commutative; auto.

  apply L_equivalence_config_H ; auto.

  apply ctns_eq_lead_to_low_component_eq ; auto. 
  
      

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  + inversion H17; subst; auto. exists φ. split;  auto.
    inversion H19; subst; auto. 
  + inversion H17; subst; auto.
    intuition.
    inversion H21; subst; auto.
    assert (value e). auto. 
    apply  value_L_eq with v h1' h2' φ; auto. 
    intuition. 
  + inversion H17; subst; auto.
    inversion H22; subst; auto.
    assert (value e). auto. 
    apply  value_L_eq with (ObjId o) h1' h2' φ; auto. intuition.
  + inversion H17; subst; auto.
    inversion H22; subst; auto.
    assert (value e). auto. 
    apply  value_L_eq with (ObjId o) h1' h2' φ; auto. intuition.
    
  
- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  + inversion H17; subst; auto. exists φ. split; auto.
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
  + inversion H18; subst; auto. exists φ. split; auto.
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
    inversion H23; subst; auto.  exists φ. split;  auto.
  + inversion H19; subst; auto. 
    inversion H24; subst; auto.

    assert (value e2). apply value_L_eq with v0 h1' h2' φ; auto.
    contradiction.
    
  + inversion H19; subst; auto.
    inversion H24; subst; auto.
    inversion H14; subst; auto.
    destruct H with e1.

    apply value_L_eq with (v_opa_l v0 lx) h1' h2' φ; auto.
    intro contra. rewrite contra in H5. inversion H5.
    auto.                           

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  + inversion H19; subst; auto. 
    inversion H20; subst; auto.
    inversion H23; subst; auto. 
    assert (value e). apply value_L_eq2  with (ObjId o)  h1' h2'  φ; auto. contradiction.
    
    
  + inversion H19; subst; auto. 
    inversion H20; subst; auto.
    inversion H25; subst; auto. 
    assert (value e2). apply value_L_eq2  with v h1' h2'  φ; auto. contradiction.

  + inversion H19; subst; auto.
    inversion H20; subst; auto.
    inversion H26; subst; auto. 
    inversion H22; subst; auto. 

    assert (cls = cls0). apply cls_def_eq with o o0 fields lx fields0 lx0 h1' h2'  φ; auto.
    subst; auto.
    rewrite <- H0 in H15; inversion H15; subst; auto. 

    exists  φ. split; auto.
    apply L_equivalence_config_L; auto.
    apply L_eq_ctn; auto.
    apply surface_syntax_L_equal; auto.
    
    inversion H_typing1; subst; auto.
(*
    inversion H31; subst; auto.
    inversion H34; subst; auto. *)
    inversion H14; subst; auto.
    inversion H32; subst; auto.
    inversion H29; subst; auto.
    destruct H46 as [F']. destruct H3 as [lo].
    rewrite H3 in H; inversion H; subst; auto.
    rewrite <- H11 in H35. inversion H35; subst; auto.
    rewrite H36 in H0. inversion H0; subst; auto.

    apply  L_equivalence_store_L ; auto.
    inversion H28; subst; auto. destruct H3. 
        split; auto.
    intros. case_eq (beq_id arg_id x); intro.
    unfold sf_update in H11. rewrite H31 in H11. inversion H11. 
    unfold sf_update in H29. rewrite H31 in H29; inversion H29.
    subst; auto.     

    unfold sf_update in H11. rewrite H31 in H11. inversion H11.
    
    split; auto; intros.

    apply sf_update_non_empty in H11. intuition. 
    apply sf_update_non_empty in H11. intuition. 

    rewrite <- H9 in H8; inversion H8; subst; auto.
    assert ( flow_to lb2  L_Label = false).
    apply flow_transitive with lb3; auto.
    try (inconsist_label). 
    (*
    inversion H36; subst; auto. 
    inversion H14; subst; auto.
    destruct H40 as [F']. destruct H3 as [lo].
    rewrite H3 in H; inversion H; subst; auto.
    rewrite <- H11 in H30. inversion H30; subst; auto.
    rewrite H32 in H0. inversion H0; subst; auto.

    inversion H31; subst; auto.
    inversion H35; subst; auto. 
    inversion H14; subst; auto.
    destruct H40 as [F']. destruct H3 as [lo].
    rewrite H3 in H; inversion H; subst; auto.
    rewrite <- H11 in H30. inversion H30; subst; auto.
    rewrite H33 in H0. inversion H0; subst; auto.

    inversion H37; subst; auto. 
    inversion H14; subst; auto.
    destruct H41 as [F']. destruct H3 as [lo].
    rewrite H3 in H; inversion H; subst; auto.
    rewrite <- H11 in H30. inversion H30; subst; auto.
    rewrite H33 in H0. inversion H0; subst; auto.

    inversion H41; subst; auto.
    inversion H30; subst; auto. 
    inversion H14; subst; auto.
    destruct H46 as [F']. destruct H3 as [lo].
    rewrite H3 in H; inversion H; subst; auto.
    rewrite <- H11 in H35. inversion H35; subst; auto.
    rewrite H36 in H0. inversion H0; subst; auto.

    inversion H38. 
    apply  L_equivalence_store_L ; auto.
    inversion H28; subst; auto. destruct H3. 

    split; auto.
    intros. case_eq (beq_id arg_id x); intro.
    unfold sf_update in H11. rewrite H31 in H11. inversion H11. 
    unfold sf_update in H29. rewrite H31 in H29; inversion H29.
    subst; auto.     

    unfold sf_update in H11. rewrite H31 in H11. inversion H11.
    
    split; auto; intros.

    apply sf_update_non_empty in H11. intuition. 
    apply sf_update_non_empty in H11. intuition. 

    rewrite <- H9 in H8; inversion H8; subst; auto.
    assert ( flow_to lb2  L_Label = false).
    apply flow_transitive with lb3; auto.
    try (inconsist_label). *)
    
  + inversion H20; subst; auto.
    inversion H25; subst; auto.    
    inversion H15; subst; auto.
    inversion H1; subst; auto. 

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  inversion H20; subst; auto. 
  inversion H22; subst; auto.
  inversion H14; subst; auto; intuition. 
  
  inversion H20; subst; auto.
  inversion H24; subst; auto.
  inversion H17; subst; auto.
  assert (value e0). apply value_L_eq2 with (v_opa_l v lx) h1' h2' φ; auto.
  destruct H6 with e0. auto.
  intro contra. inversion H1; subst; auto; inversion H12.
  auto. 

  
  inversion H20; subst; auto.
  inversion H25; subst; auto.  
  inversion H22; subst; auto.
  inversion H16.


  inversion H20; subst; auto.
  inversion H25; subst; auto.
  inversion H15; subst; auto. 
  
  inversion H14; subst; auto.
  assert (cls1 = cls2).
  inversion H_bijection; subst; auto.
  apply H0 in H5; auto.
  inversion H5; subst;  auto.
  rewrite <- H30 in H7; inversion H7; subst; auto.
  rewrite <- H31 in H10; inversion H10; subst; auto.
  apply H34. 

  assert (body = body0 /\ arg_id = arg_id0 /\
          surface_syntax body = true).
  apply config_typing_lead_to_tm_typing in H_typing1.
  destruct H_typing1 as [T1].
  destruct H1 as [gamma1].
  inversion H1; subst; auto.
  inversion H30; subst; auto.

  destruct H37 as [F0]. destruct H0 as [l0].
  rewrite  H0 in H; inversion H; subst; auto.
  rewrite  H0 in H7; inversion H7; subst; auto.
  rewrite <- H32 in H28; inversion H28; subst; auto.
  rewrite H33 in H4; inversion H4; subst; auto.
  rewrite <- H10 in H9; inversion H9; subst; auto.
  rewrite H33 in H23; inversion H23; subst; auto.
  intro contra; inversion contra.
  destruct H1. destruct H11. 

  subst; auto. 

  inversion H6; subst; auto.
  exists  φ. split; auto. apply L_equivalence_config_L; auto.
  apply join_L_label_flow_to_L; auto.
  apply join_L_label_flow_to_L; auto.

  apply L_eq_ctn; auto. 
  apply join_L_label_flow_to_L; auto.
  apply join_L_label_flow_to_L; auto.

  apply L_equivalence_store_L; auto.
  split; auto.
  intros.
  case_eq (beq_id arg_id0 x); intro.
  unfold sf_update in H0. rewrite H31 in H0. inversion H0.
  unfold sf_update in H11. rewrite H31 in H11. inversion H11.
  subst; auto.
  
  unfold sf_update in H0. rewrite H31 in H0. inversion H0.

  split; auto; intro. 

  pose proof (sf_update_non_empty arg_id0  v).
  intuition.

  pose proof (sf_update_non_empty arg_id0  v0).
  intuition. 
  
  exists  φ. split; auto.  apply L_equivalence_config_H; auto. 
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
          Config ct (Container return_hole fs1 lb1 sf1) ctns_stack1 h1').
  apply low_component_with_L_Label; auto. rewrite H11.
  assert ((low_component ct (Container return_hole fs2 lb2 sf2)
                             ctns_stack2 h2') =
          Config ct (Container return_hole fs2 lb2 sf2) ctns_stack2 h2').
  apply low_component_with_L_Label; auto. rewrite H29.
  auto.

  rewrite <- H5 in H; inversion H; subst; auto.
  assert (flow_to lb1 L_Label = false).
  apply flow_transitive with lb0; auto.
  try (inconsist_label).

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  inversion   H_bijection; subst; auto.
  assert (lookup_heap_obj h1 (get_fresh_oid h1)  = None). 
  apply fresh_oid_heap with ct; auto.
  assert (lookup_heap_obj h2 (get_fresh_oid h2)  = None). 
  apply fresh_oid_heap with ct; auto.
  apply H1 in H6.
  apply H2 in H7.
  assert (forall a1 a2 : oid, decision.Decision (a1 = a2)). auto.
  
  exists  (bijection.extend_bijection φ (get_fresh_oid h1)  (get_fresh_oid h2) H6 H7). split; auto.
  (* L_equivalence_heap  *)
  inversion H17; subst; auto.
  inversion H27; subst; auto. rename cls_name0 into cls_name.
  rewrite H5 in H; inversion H; subst; auto. 

  remember (class_def cls_name field_defs method_defs) as cls_def.
  remember (add_heap_obj h1 (get_fresh_oid h1) 
        (Heap_OBJ  cls_def (init_field_map (find_fields cls_def) empty_field_map) lb2)) as h1'.
  remember (add_heap_obj h2 (get_fresh_oid h2) 
                         (Heap_OBJ  cls_def (init_field_map (find_fields cls_def) empty_field_map) lb2)) as h2'.

  assert (lookup_heap_obj h1 (get_fresh_oid h1)  = None). 
  apply fresh_oid_heap with ct; auto.   
  assert (lookup_heap_obj h2 (get_fresh_oid h2)  = None). 
  apply fresh_oid_heap with ct; auto. 
 (* apply H7 in H4. apply H8 in H5. *)
  remember (get_fresh_oid h1) as  o3.
  remember (get_fresh_oid h2) as o4. 
  assert ( beq_oid (get_fresh_oid h1) (get_fresh_oid h1) = true) by (apply beq_oid_same).
  assert ( beq_oid (get_fresh_oid h2) (get_fresh_oid h2) = true) by (apply beq_oid_same).
  apply  L_eq_heap.
  intros.
  
  destruct (oid_decision o3 o1). subst; auto. simpl in H14.
  destruct (decision.decide (get_fresh_oid h1 = get_fresh_oid h1) ) in H14. inversion H14; subst; auto. 

  remember (class_def cls_name field_defs method_defs) as cls_def.
  remember (add_heap_obj h1 (get_fresh_oid h1) 
                         (Heap_OBJ  cls_def (init_field_map (find_fields cls_def) empty_field_map) lb1)) as h1'.
  
  remember (add_heap_obj h2 (get_fresh_oid h2) 
                         (Heap_OBJ  cls_def (init_field_map (find_fields cls_def) empty_field_map) lb2)) as h2'.

  
  assert (lookup_heap_obj h1' (get_fresh_oid h1) = Some (Heap_OBJ  cls_def (init_field_map (find_fields cls_def) empty_field_map) lb1) ).
  subst; auto.

  assert (lookup_heap_obj h2' (get_fresh_oid h2) = Some (Heap_OBJ  cls_def (init_field_map (find_fields cls_def) empty_field_map) lb2) ).
  subst; auto.
  apply object_equal_L with lb1 lb2 cls_def cls_def (init_field_map (find_fields cls_def) empty_field_map) (init_field_map (find_fields cls_def) empty_field_map); auto.
  
  split; auto. 
  split; auto.
  apply L_Label_flow_to_L in H25.
  apply L_Label_flow_to_L in H26. rewrite <- H26 in H25. auto. 

  split; auto.  split; auto.
  split; auto. split; auto.  
  intros.  
  pose proof (initilized_fields_empty (find_fields cls_def) fname).
  
  destruct H23;
    rewrite H23 in H22; inversion H22.
  intuition.  
   assert ( bijection.left (bijection.extend_bijection φ o3 o4 H6 H7)  o1 = 
           bijection.left φ o1) by (apply bijection.left_extend_bijection_neq; auto).
   rewrite H14 in H19. assert ( bijection.left φ o1 = Some o2). auto.
   apply H0 in H20. inversion H20; subst; auto.
   destruct H30; subst; auto. destruct H31; subst; auto. 

  remember (class_def cls_name field_defs method_defs) as cls_def.
  assert ( lookup_heap_obj
     (add_heap_obj h1 (get_fresh_oid h1)
       (Heap_OBJ cls_def
          (init_field_map (find_fields cls_def) empty_field_map) lb1)) o1 = Some (Heap_OBJ cls2 F1 lb3) ).
  apply extend_heap_lookup_eq; auto. 

  destruct (oid_decision (get_fresh_oid h2) o2 ).
   assert (lookup_heap_obj h2 (get_fresh_oid h2)  = None). 
   apply fresh_oid_heap with ct; auto.  rewrite e in H32.
   rewrite H32 in H22. inversion H22.
   
   assert ( lookup_heap_obj
     (add_heap_obj h2 (get_fresh_oid h2)
       (Heap_OBJ cls_def
          (init_field_map (find_fields cls_def) empty_field_map) lb2)) o2 = Some (Heap_OBJ cls2 F2 lb3) ).
   apply extend_heap_lookup_eq; auto.

   apply object_equal_L with lb3 lb3 cls2 cls2 F1 F2; auto.  
   split; auto.
   split; auto. 
   destruct H31. destruct H33.     
   split; auto. split; auto.
   intros.
   destruct H34 with fname fo1 fo2; auto. rename x into hof1.
   destruct H37 as [hof2]. destruct H37. destruct H38.
   exists hof1. exists hof2.
   split; auto. 
   apply extend_heap_lookup_eq; auto. 
   apply lookup_extend_heap_fresh_oid with ct hof1 ; auto. 
   split; auto. 
   apply extend_heap_lookup_eq; auto. 
   apply lookup_extend_heap_fresh_oid with ct hof2 ; auto. 
   assert (fo1 <> get_fresh_oid h1  ).
   apply lookup_extend_heap_fresh_oid with ct hof1 ; auto.
   assert ( bijection.left (bijection.extend_bijection φ (get_fresh_oid h1) (get_fresh_oid h2) H6 H7)  fo1 = 
          bijection.left φ fo1) by (apply bijection.left_extend_bijection_neq; auto).
   rewrite H41.   auto.
   
   
   intros. subst; auto.  destruct (oid_decision (get_fresh_oid h1) o). subst; auto.
   unfold  lookup_heap_obj in H14. unfold add_heap_obj in H14.
   
   rewrite H11 in H14. inversion H14.
   remember (bijection.extend_bijection φ (get_fresh_oid h1) (get_fresh_oid h2) H6 H7) as φ'.
   rewrite   Heqφ'.
   assert (bijection.left (bijection.extend_bijection φ (get_fresh_oid h1) (get_fresh_oid h2) H6 H7)  o = 
           bijection.left φ o) by (apply bijection.left_extend_bijection_neq; auto).
   remember (class_def cls_name field_defs method_defs) as cls_def. 
   assert ( lookup_heap_obj h1 o = None).
   (apply lookup_extended_heap_none with
        (Heap_OBJ cls_def (init_field_map (find_fields cls_def)
                                          empty_field_map) lb1) ; auto).
   rewrite H19.  apply H1 in H20. auto.
   rewrite   Heqh2'. intros. subst. 
   destruct (oid_decision (get_fresh_oid h2) o). subst; auto.
   unfold  lookup_heap_obj in H14. unfold add_heap_obj in H14.
   rewrite H13 in H14. inversion H14.

   assert (bijection.right (bijection.extend_bijection φ (get_fresh_oid h1) (get_fresh_oid h2) H6 H7)  o = 
           bijection.right φ o). (apply bijection.right_extend_bijection_neq; auto).
   remember (class_def cls_name field_defs method_defs) as cls_def. 
   assert ( lookup_heap_obj h2 o = None) by (apply lookup_extended_heap_none with
                                                 (Heap_OBJ cls_def (init_field_map (find_fields cls_def)
                                                                                   empty_field_map) lb2) ; auto).
   rewrite H19. apply H2 in H20. auto.
   intros.
   destruct (oid_decision o3 o). subst; auto. simpl in H14.
   rewrite H11 in H14. inversion H14. subst; auto.
   try (inconsist_label).
   subst; auto.

   unfold lookup_heap_obj in H14. unfold add_heap_obj in H14.
   assert (o <> get_fresh_oid h1) by (auto). apply  beq_oid_not_equal in H20. rewrite H20 in H14.
   fold lookup_heap_obj in H14. apply H3 in H14.
   assert (bijection.left (bijection.extend_bijection φ (get_fresh_oid h1) (get_fresh_oid h2) H6 H7)  o = 
           bijection.left φ o) by (apply bijection.left_extend_bijection_neq; auto).
   rewrite H21; auto. auto. 

   intros.
   destruct (oid_decision o4 o). subst; auto. simpl in H14.
   rewrite H13 in H14. inversion H14. subst; auto.
   try (inconsist_label).
   subst; auto.

   unfold lookup_heap_obj in H14. unfold add_heap_obj in H14.
   assert (o <> get_fresh_oid h2) by (auto). apply  beq_oid_not_equal in H20. rewrite H20 in H14.
   fold lookup_heap_obj in H14. apply H4 in H14.
   assert (bijection.right (bijection.extend_bijection φ (get_fresh_oid h1) (get_fresh_oid h2) H6 H7)  o = 
           bijection.right φ o) by (apply bijection.right_extend_bijection_neq; auto).
   rewrite H21; auto. auto. 

  

  (*  L_equivalence_config  *)
  apply L_equivalence_config_L; auto.
  
  subst; auto.
  inversion H17; subst; auto.
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
  inversion H19; subst; auto. exists φ. split; auto.
  inversion H17; subst; auto. intuition.  
  inversion H19; subst; auto. 
  assert (value e). apply value_L_eq with v h1' h2'  φ; auto.
  intuition. 

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  inversion H17; subst; auto. 
  inversion H20; subst; auto. inversion H9; subst; auto. 
  exists φ. split; auto.
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
  
  inversion H19; subst; auto. exists φ. split; auto. 
  apply L_equivalence_config_L; auto.
  apply L_eq_ctn; auto.
  case_eq (flow_to lo0 L_Label); intro; auto. 

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  inversion H17; subst; auto.  
  inversion H19; subst; auto.  exists φ. split; auto.
  inversion H17; subst; auto.
  inversion H19; subst; auto.
  inversion H3; subst; auto; intuition. 

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  inversion H17; subst; auto.  
  inversion H20; subst; auto.  exists φ. split; auto.
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
  exists φ.
  split; auto. 

  assert (flow_to (join_label lb1 lo) L_Label = false). 
  apply flow_join_label with lo lb1; auto. 
  assert (flow_to (join_label lb2 lo0) L_Label = false). 
  apply flow_join_label with lo0 lb2; auto.

  exists φ. split; auto. 
  apply L_equivalence_config_H; auto. 
  unfold low_component. rewrite H. rewrite H1. auto.
  apply L_equivalence_config_L; auto.
  apply L_eq_ctn; auto. apply L_equivalence_store_L; intros.
  split; auto;
  intros. match goal with
          | H :  empty_stack_frame _ = Some _ |- _
            => inversion H
          end.
  split; auto. 
           

  exists φ. split; auto. 
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
  inversion H19; subst; auto.  exists φ. split;  auto.
  
  inversion H17; subst; auto. 
  inversion H19; subst; auto.
  inversion H4; subst; auto; intuition. 

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  inversion H17; subst; auto.  
  inversion H20; subst; auto.  exists φ. split;  auto.
  
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
  
  exists φ. split; auto.
  exists φ. split; auto.
  apply H_Label_not_flow_to_L in H6. 
  apply H_Label_not_flow_to_L in H9. subst; auto. 
 
- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  inversion H17; subst; auto.  
  inversion H19; subst; auto.  exists φ. split; auto.
  
  inversion H17; subst; auto. 
  inversion H19; subst; auto.
  inversion H3; subst; auto; intuition. 

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  inversion H17; subst; auto.  
  inversion H20; subst; auto.  exists φ. split; auto.
  
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
  exists φ. split;  auto.

  assert (flow_to (join_label lb1 lo) L_Label = false). 
  apply flow_join_label with lo lb1; auto. 
  assert (flow_to (join_label lb2 lo0) L_Label = false). 
  apply flow_join_label with lo0 lb2; auto.

  exists φ. split; auto. 
  apply L_equivalence_config_H; auto.
  destruct ctns_stack1'; inversion H18; subst; auto;
    unfold low_component; rewrite H; rewrite H1; auto.
  apply L_equivalence_config_L; auto.
  apply L_eq_ctn; auto.
  apply L_equivalence_store_L; auto.
  split; intros.  match goal with
          | H :  empty_stack_frame _ = Some _ |- _
            => inversion H
                  end.
  split; auto. 

  
- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  inversion H17; subst; auto.
  inversion H19; subst; auto. exists φ. split; auto. 
  inversion H17; subst; auto.
  inversion H19; subst; auto.
  assert (value e). apply value_L_eq with v h1' h2' φ; auto. intuition.
  
- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  inversion H17; subst; auto.  
  inversion H20; subst; auto.
  inversion H9; subst; auto.  exists φ. split; auto.

  inversion H17; subst; auto.

  inversion H21; subst; auto.
  inversion H9; subst; auto.
  inversion H3; subst; auto. inversion H12. 

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  inversion H17; subst; auto.
  inversion H19; subst; auto.
  assert (value e). apply value_L_eq2 with v h1' h2' φ; auto. intuition.
  exists φ. split;  auto. 
  inversion H17; subst; auto.
  inversion H19; subst; auto.
  apply L_equivalence_config_L; auto.
  apply L_eq_ctn; auto.
  rename id0 into arg_id. 
  apply L_equivalence_store_L; auto; intros.
  split; auto.
  try ( empty_sf).
  intros. 
  case_eq (beq_id arg_id x); intro.
  unfold sf_update in H0. rewrite H5 in H0. inversion H0.
  unfold sf_update in H3. rewrite H5 in H3. inversion H3.
  subst; auto. 

  unfold sf_update in H0. rewrite H5 in H0. inversion H0.
  unfold sf_update in H3. rewrite H5 in H3. inversion H3.
  subst; auto. 
  
  inversion H21; subst; auto.
  destruct H6.
  apply H6 with x; auto. 
  
  split; auto; intro.

  assert (sf_update sf1 arg_id v arg_id  = empty_stack_frame arg_id).
  rewrite H0. auto.
  unfold   sf_update in H1.
  pose proof (beq_id_same arg_id).
  rewrite H3 in H1.
  inversion H1. 

  assert (sf_update sf2 arg_id v0 arg_id  = empty_stack_frame arg_id).
  rewrite H0. auto.
  unfold   sf_update in H1.
  pose proof (beq_id_same arg_id).
  rewrite H3 in H1.
  inversion H1. 

  
- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  inversion H17; subst; auto.   
  inversion H19; subst; auto.   exists φ. split;  auto.
  
  inversion H17; subst; auto. 
  inversion H21; subst; auto.
  assert (value e). apply value_L_eq with  v h1' h2'  φ; auto.
  intuition. 

  inversion H17; subst; auto.
  inversion H21; subst; auto.
  assert (value e). apply value_L_eq with  (ObjId o) h1' h2  φ; auto.
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
  inversion H9; subst; auto. exists φ. split;  auto.
  
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
  inversion H23; subst; auto. exists φ. split; auto.

  inversion H19; subst; auto.
  inversion H23. subst; auto.
  assert (value e2). apply value_L_eq with v0 h1' h2 φ; auto. intuition.

  inversion H19; subst; auto.
  inversion H23; subst; auto.
  destruct H2 as [o'].
  destruct H2 as [cls'].
  destruct H2 as [F'].
  destruct H2 as [lo']. destruct H2.
  subst; auto.

  intuition.

  inversion H19; subst; auto.
  inversion H23; subst; auto.
  inversion H26; subst; auto.
  assert (value e1). apply value_L_eq with (v_opa_l v0 lx) h1' h2 φ; auto.
  assert (value v0).
  destruct H21. subst; auto. 
  destruct H2 as [o'].
  destruct H2 as [cls'].
  destruct H2 as [F'].
  destruct H2 as [lo']. destruct H2.
  subst; auto. 
  intuition.
  destruct H with  e1; auto.
  intro contra.
  inversion H5; subst; inversion H9. 
  
- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  inversion H18; subst; auto.
  
  inversion H21; subst; auto.
  inversion H10; subst; auto.
  inversion H23; subst; auto.  inversion H0.

  inversion H18; subst; auto. 
  inversion H22; subst; auto.
  inversion H10; subst; auto.  exists φ. split; auto.

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
  assert (value e2). apply value_L_eq2 with v h1 h2'  φ; auto.
  destruct H3.
  subst; auto. 
  destruct H0 as [o'].
  destruct H0 as [cls'].
  destruct H0 as [F'].
  destruct H0 as [lo']. destruct H0.
  subst; auto. intuition. 

  inversion H19; subst; auto. 
  inversion H23; subst; auto. exists φ. split; auto.
  apply update_field_preserve_bijection with ct L_Label L_Label lb1 lb2; auto.

  pose proof (join_L_Label_irrelevant lb1) as Hylb. rewrite Hylb; auto. 
  pose proof (join_L_Label_irrelevant lb2) as Hylb. rewrite Hylb; auto.

  apply L_equivalence_tm_eq_v_opa_l_L; auto.
  destruct H3.
  subst; auto. 
  destruct H0 as [o'].
  destruct H0 as [cls'].
  destruct H0 as [F'].
  destruct H0 as [lo']. destruct H0.
  subst; auto.

  destruct H21.
  subst; auto. 
  destruct H0 as [o'].
  destruct H0 as [cls'].
  destruct H0 as [F'].
  destruct H0 as [lo']. destruct H0.
  subst; auto.

  assert (value v).
  destruct H3.
  subst; auto. 
  destruct H0 as [o'].
  destruct H0 as [cls'].
  destruct H0 as [F'].
  destruct H0 as [lo']. destruct H0.
  subst; auto.

  assert (value v0).
  destruct H21.
  subst; auto. 
  destruct H2 as [o'].
  destruct H2 as [cls'].
  destruct H2 as [F'].
  destruct H2 as [lo']. destruct H2.
  subst; auto.  
  
  apply L_equivalence_config_L; auto.
  assert (forall a1 a2 : oid, decision.Decision (a1 = a2)). auto.
  apply update_field_preserve_L_eq_ctn with  ct lb1 L_Label lb2 L_Label; auto.
  pose proof (join_L_Label_irrelevant lb1) as Hylb. rewrite Hylb; auto. 
  pose proof (join_L_Label_irrelevant lb2) as Hylb. rewrite Hylb; auto.
  
  inversion  H_valid1; subst;  auto. 
  apply valid_container; auto; inversion H28; auto.
  inversion  H_valid2; subst;  auto. 
  apply valid_container; auto; inversion H28; auto.

  assert (forall a1 a2 : oid, decision.Decision (a1 = a2)). auto.
  apply update_field_preserve_L_eq_ctns  with  ct lb1 L_Label lb2 L_Label; auto.
  pose proof (join_L_Label_irrelevant lb1) as Hylb. rewrite Hylb; auto. 
  pose proof (join_L_Label_irrelevant lb2) as Hylb. rewrite Hylb; auto.

  inversion  H_valid1; subst;  auto.
  inversion  H_valid2; subst;  auto.

  
  inversion H19; subst; auto. 
  inversion H23; subst.
  inversion H26; subst; auto.
  destruct H3. inversion H0.
    destruct H0 as [o'].
  destruct H0 as [cls'].
  destruct H0 as [F'].
  destruct H0 as [lo']. destruct H0.
  inversion H0. 
  
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

 
  destruct H5 with  (v_opa_l e2 l2); auto.
  intro contra. inversion contra. 

  inversion H19; subst; auto.
  inversion H23; subst; auto.
  inversion H26; subst; auto.
  destruct H21.
  inversion H0.
  destruct H0 as [o'].
  destruct H0 as [cls'].
  destruct H0 as [F'].
  destruct H0 as [lo']. destruct H0.
  inversion H0. 
  

  exists  φ.

  split; auto. 

  inversion H19; subst; auto.
  inversion H23; subst; auto.
  inversion H26; subst; auto. 
  apply  update_field_preserve_bijection with ct lx lx0 lb1 lb2; auto.

  (*  inversion H11; subst; auto.  *)
  inversion H19; subst; auto.
  inversion H23; subst; auto.
  inversion H26; subst; auto. 
  apply L_equivalence_config_L; auto.
  assert (forall a1 a2 : oid, decision.Decision (a1 = a2)). auto.
  apply update_field_preserve_L_eq_ctn with  ct lb1 lx lb2 lx0; auto.
  destruct H3. subst; auto.
  destruct H2 as [o'].
  destruct H2 as [cls'].
  destruct H2 as [F'].
  destruct H2 as [lo']. destruct H2.
  subst; auto. 

  destruct H21. subst; auto.
  destruct H2 as [o'].
  destruct H2 as [cls'].
  destruct H2 as [F'].
  destruct H2 as [lo']. destruct H2.
  subst; auto. 
  
  inversion  H_valid1; subst;  auto. 
  apply valid_container; auto; inversion H27; auto.
  inversion  H_valid2; subst;  auto. 
  apply valid_container; auto; inversion H27; auto.

  assert (forall a1 a2 : oid, decision.Decision (a1 = a2)). auto.
  apply update_field_preserve_L_eq_ctns  with  ct lb1 lx lb2 lx0; auto.
  destruct H3. subst; auto.
  destruct H2 as [o'].
  destruct H2 as [cls'].
  destruct H2 as [F'].
  destruct H2 as [lo']. destruct H2.
  subst; auto. 

  destruct H21. subst; auto.
  destruct H2 as [o'].
  destruct H2 as [cls'].
  destruct H2 as [F'].
  destruct H2 as [lo']. destruct H2.
  subst; auto.
  
  inversion  H_valid1; subst;  auto.
  inversion  H_valid2; subst;  auto.


  
- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  inversion H17; subst; auto. 
  inversion H19; subst; auto.
  exists φ. split;  auto.
  
  inversion H17; subst; auto. 
  inversion H14; subst; auto. 
  inversion H10; subst; auto. intuition. 

  inversion H17; subst; auto. 
  inversion H14; subst; auto. 
  inversion H10; subst; auto. intuition. 


- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  inversion H17; subst; auto.
  inversion H20; subst; auto.
  inversion H9; subst; auto. exists φ. split; auto.

  
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
  inversion H13; subst; auto.  exists φ. split; auto.


- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  inversion H16; subst; auto.  
  inversion H18; subst; auto.  exists φ. split; auto. 

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
  exists φ.  split; auto.
  

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  inversion H17; subst; auto.
  inversion H18; subst; auto.
  inversion H9; subst; auto. 
  exists φ. split; auto. 
  apply  L_equivalence_config_L; auto.
  apply L_eq_ctn; auto. auto.
  
  apply L_Label_flow_to_L in H13.
  apply L_Label_flow_to_L in H14.
  rewrite <- H24 in H25. subst; auto.
 Qed.
Hint Resolve simulation_L.
 