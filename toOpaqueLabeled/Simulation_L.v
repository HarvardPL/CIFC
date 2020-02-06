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

(*EqCmp*)
- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  + inversion H17; subst; auto. exists φ. split;  auto.
    inversion H19; subst; auto. 
  + inversion H17; subst; auto.
    inversion H20; subst; auto.
    assert (value e1). auto. 
    apply  value_L_eq with v h1' h2' φ; auto. 
    intuition. 
  + inversion H17; subst; auto.
    inversion H24; subst; auto.
    assert (value e1). auto. 
    apply  value_L_eq with v1 h1' h2' φ; auto. intuition.
  
- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  + inversion H17; subst; auto. exists φ. split; auto.
    inversion H20; subst; auto.
    inversion H9; subst; auto.
  + inversion H17; subst; auto.
    inversion H21; subst; auto.
    inversion H9; subst; auto.
    inversion H11; subst; auto. inversion H2.
  + inversion H17; subst; auto.
    inversion H21; subst; auto.
    inversion H9; subst; auto.
    inversion H3; subst; auto.
    inversion H12.

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  + inversion H18; subst; auto. 
    inversion H20; subst; auto.
    assert (value e1). apply value_L_eq2 with v h1' h2' φ; auto.
    intuition. 
  + inversion H18; subst; auto. exists φ. split; auto.
    inversion H21; subst; auto.
  + inversion H18; subst; auto. 
    inversion H25; subst; auto.
    assert (value e2). apply value_L_eq with v2 h1' h2' φ; auto.
    intuition. 

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  + inversion H18; subst; auto.  
    inversion H21; subst; auto.
    inversion H10; subst; auto.
    inversion H12; subst; auto.
    inversion H.

  + inversion H18; subst; auto.   
    inversion H22; subst; auto.
    inversion H10; subst; auto.    
    exists φ. split;  auto.
    
  + inversion H18; subst; auto. 
    inversion H22; subst; auto.
    inversion H10; subst; auto.
    inversion H12; subst; auto.
    inversion H13; subst; auto.
    case_eq (hole_free e2); intro He2; rewrite He2 in H2;  intuition. 

(* EqCmp evaluate to boolean *)    
- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  + inversion H20; subst; auto.
    inversion H22; subst; auto.
    inversion H25; subst; auto. 
    assert (value e1). apply value_L_eq2 with v1 h1' h2' φ; auto.
    intuition.
  + inversion H22; subst; auto.
    inversion H25; subst; auto.
    assert (value e2). apply value_L_eq2 with v2 h1' h2' φ; auto.
    intuition.
  + inversion H22; subst; auto.
    inversion H29; subst; auto.

    pose proof (exclude_middle_val_eq v1 v2 H H0).
    destruct H5.
    ++ destruct H3. subst; auto.
       +++ inversion H14; subst; auto.
           inversion H15; subst; auto.
           assert (result = B_true). auto. 
           assert (result0 = B_true). auto. 
           subst; auto. 
           exists  φ; split; auto.
       +++ destruct H3 as [o1].
           destruct H3 as [cls1].
           destruct H3 as [F1].
           destruct H3 as [lo1].
           destruct H3.

           destruct H4.
           ++++ subst; auto.
                inversion H5.

           ++++
             destruct H4 as [o2].
             destruct H4 as [cls2].
             destruct H4 as [F2].
             destruct H4 as [lo2].
             destruct H4.
             subst; auto.
             inversion H5; subst; auto. 

             inversion H14; subst; auto.
             inversion H15; subst; auto.
             +++++
               rewrite H4 in H16; inversion H16; subst; auto.
             exists  φ. split; auto.
             assert (result = B_true). auto. 
             assert (result0 = B_true). auto.
             subst; auto.
             +++++ rewrite <- H8 in H16; inversion H16; subst; auto.
             try (inconsist).
             +++++ destruct H6.
             rewrite <- H4 in H3; inversion H3; subst; auto.
             assert (flow_to lb1 L_Label = false).
             apply flow_transitive with lb0; auto.
             try (inconsist).
    ++ assert (v0 <> v3).
       intro contra. subst; auto.
       destruct H25; subst; auto.
       +++ 
         inversion H15; subst; auto.
         inversion H14; subst; auto.
       +++
         destruct H6 as [o3].
         destruct H6 as [cls3].
         destruct H6 as [F3].
         destruct H6 as [lo3].
         destruct H6.             subst; auto.
         inversion H14; subst; auto.
         inversion H15; subst; auto.
         Require Import bijection.
         ++++
           apply right_left in H8.
           apply right_left in H16.
           rewrite H8 in H16; inversion H16; subst; auto.
         ++++
           rewrite <- H12 in H32; inversion H32; subst;auto.
           try (inconsist).
         ++++
           destruct H7.
           rewrite <- H6 in H10; inversion H10; subst; auto. 
           assert (flow_to lb2 L_Label = false).
           apply flow_transitive with lo3; auto.
           try (inconsist).
       +++
         assert (result = B_false). auto. 
         assert (result0 = B_false). auto. 
         subst; auto. 
         exists  φ; split; auto.

(*field access*)  
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
  destruct H33.
  
  inversion H31; subst; auto. 
  assert (v = null \/ exists o', v = ObjId o').
  apply field_value  with h1' o cls4 F3 lb4 fname0 ct cls' gamma1; auto.

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
  destruct H35 as [lof1]. destruct H35 as [lof2].
  destruct H35 as [FF1]. destruct H35 as [FF2].
  destruct H35. destruct H36.
  
  destruct H39.
  (*field is low object*)
  assert (L_equivalence_object o1 h1' o2 h2' φ).
  apply H1; auto.
  apply H39. 
  inversion H42; subst; auto. 
  apply L_equivalence_tm_eq_object_L with cls1 F1 lb0 cls2 F2 lb3 ; auto.
  apply H39. 

  (*field is high object*)
  destruct H39.
  eauto using L_equivalence_tm_eq_object_H. 
  
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
    inversion H22; subst; auto.
    assert (value e). auto. 
    apply  value_L_eq with v h1' h2' φ; auto.
    
    intuition. 
  + inversion H17; subst; auto.
    inversion H21; subst; auto.
    assert (value e). auto. 
    apply  value_L_eq with v1 h1' h2' φ; auto. intuition.
  + inversion H17; subst; auto.
    inversion H22; subst; auto.
    assert (value e). auto. 
    apply  value_L_eq with (ObjId o) h1' h2' φ; auto. intuition.
  + inversion H17; subst; auto.
    inversion H22; subst; auto.
    assert (value e). auto. 
    apply  value_L_eq with (ObjId o) h1' h2' φ; auto. intuition.
    
- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  + inversion H17; subst; auto. exists φ. split;  auto.
    inversion H20; subst; auto.
    inversion H9; subst; auto. 
    
  + inversion H17; subst; auto.
    inversion H21; subst; auto.
    inversion H9; subst; auto. 
    assert (value hole). auto. 
    apply  value_L_eq with v1 h1' h2' φ; auto.
    inversion H0. 

  + inversion H17; subst; auto.
    inversion H21; subst; auto.
    inversion H9; subst; auto. 
    assert (value hole). auto. 
    apply  value_L_eq with v1 h1' h2' φ; auto.
    inversion H0.

  + inversion H17; subst; auto.
    inversion H21; subst; auto.
    inversion H9; subst; auto.
    inversion H11; subst; auto.
    inversion H12; subst; auto. 
    
- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  + inversion H18; subst; auto. exists φ. split; auto.
    inversion H21; subst; auto.
    inversion H10; subst; auto.
    inversion H23; subst; auto.
    inversion H.
    
  + inversion H18; subst; auto. exists φ. split; auto.
    inversion H22; subst; auto.
    inversion H10; subst; auto.    
    
  + inversion H18; subst; auto.
    inversion H22; subst; auto.
    inversion H10; subst; auto.
    inversion H25. 
  + inversion H18; subst; auto.
    inversion H22; subst; auto.
    inversion H10; subst; auto.
    inversion H14; subst; auto.
    inversion H13; subst; auto.
    case_eq (hole_free e2); intro Hy; rewrite Hy in H2; inversion H2.     

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  + inversion H20; subst; auto.  
    subst. inversion H22; subst; auto.

    assert (value e). apply value_L_eq2 with v h1' h2' φ; auto.
    contradiction.
  + inversion H20; subst; auto.   
    inversion H25; subst; auto.  exists φ. split;  auto.
  + inversion H20; subst; auto. 
    inversion H24; subst; auto.
    inversion H17; subst; auto.
    destruct H with e1; auto. 
    
  + inversion H20; subst; auto.
    inversion H25; subst; auto.
    assert (value e2). apply value_L_eq with v0 h1' h2' φ; auto.
    contradiction.

  + inversion H20; subst; auto.
    inversion H25; subst; auto.
    inversion H15; subst; auto.
    destruct H with e1; auto.                    

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  + inversion H19; subst; auto. 
    inversion H21; subst; auto.
    assert (value e). apply value_L_eq2 with v1 h1' h2' φ; auto.
    contradiction.

  + inversion H19; subst; auto. 
    inversion H24; subst; auto.
    inversion H21; subst; auto.
    destruct H6 with e3; auto.
    
  + inversion H19; subst; auto. 
    inversion H23; subst; auto.
    inversion H16; subst; auto.
    exists φ. split;  auto.
    apply L_equivalence_config_L; auto.

  + inversion H19; subst; auto. 
    inversion H24; subst; auto.
    assert (value (unlabelOpaque e2)).
    apply value_L_eq  with v  h1' h2'  φ; auto.
    inversion H2.
    
  + inversion H19; subst; auto. 
    inversion H24; subst; auto.
    inversion H14; subst; auto.
    assert (value e2); auto.
    apply value_L_eq  with (v_opa_l v lx)  h1' h2'  φ; auto.
    contradiction.
 

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn);
    try(inversion H18; subst; auto;
    inversion H21; subst; auto;
    inversion H10; subst; auto ).
  + inversion H18; subst; auto.
    inversion H22; subst; auto.
    inversion H10; subst; auto.
  + inversion H24; subst; auto.
    inversion H3; subst; auto.
    inversion H23; subst; auto.
    inversion H. 
  + inversion H18; subst; auto.
    inversion H22; subst; auto.
    inversion H10; subst; auto.
    inversion H25.     
  + inversion H18; subst; auto.
    inversion H22; subst; auto.
    inversion H10; subst; auto.
    exists φ. split;  auto.
  + inversion H18; subst; auto.
    inversion H22; subst; auto.
    inversion H10; subst; auto.
  + inversion H18; subst; auto.
    inversion H22; subst; auto.
    inversion H10; subst; auto.
  + inversion H18; subst; auto.
    inversion H22; subst; auto.
    inversion H10; subst; auto.
    inversion H14; subst; auto.
    inversion H2; subst; auto.
    inversion H13; subst; auto.
    case_eq (hole_free e2); intro Hy; rewrite Hy in H4; inversion H4.    

    
- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  + inversion H20; subst; auto. 
    inversion H22; subst; auto.
    assert (value e). apply value_L_eq2  with (ObjId o)  h1' h2'  φ; auto. contradiction.
   
  + inversion H20; subst; auto.
    inversion H25; subst; auto. 
    assert (value e2). apply value_L_eq2  with v h1' h2'  φ; auto. contradiction.
    
  + inversion H20; subst; auto.
    inversion H24; subst; auto.
    inversion H17; subst; auto.
    inversion H1. 

  + inversion H20; subst; auto.
    inversion H25; subst; auto.
    inversion H14; subst; auto. 

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
    inversion H13; subst; auto.
    inversion H31; subst; auto.
    inversion H28; subst; auto.
    destruct H45 as [F']. destruct H3 as [lo].
    rewrite H3 in H; inversion H; subst; auto.
    rewrite <- H10 in H34. inversion H34; subst; auto.
    rewrite H35 in H0. inversion H0; subst; auto.

    apply  L_equivalence_store_L ; auto.
    inversion H27; subst; auto. destruct H3. 
        split; auto.
    intros. case_eq (beq_id arg_id x); intro.
    unfold sf_update in H10. rewrite H30 in H10. inversion H10. 
    unfold sf_update in H28. rewrite H30 in H28; inversion H28.
    subst; auto.     

    unfold sf_update in H10. rewrite H30 in H10. inversion H10.
    
    split; auto; intros.

    apply sf_update_non_empty in H10. intuition. 
    apply sf_update_non_empty in H10. intuition. 

    rewrite <- H8 in H7; inversion H7; subst; auto.
    assert ( flow_to lb2  L_Label = false).
    apply flow_transitive with lx0; auto.
    try (inconsist_label).


  + inversion H20; subst; auto.
    inversion H25; subst; auto.    
    inversion H15; subst; auto.
    inversion H1; subst; auto. 


- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  (*method call with unlabelOpaque*)
  + inversion H20; subst; auto. 
    inversion H22; subst; auto.
    assert (value e). apply value_L_eq2 with (ObjId o) h1' h2' φ; auto.
    contradiction.

  + inversion H20; subst; auto.
    inversion H25; subst; auto.
    inversion H22; subst; auto.
    destruct H7 with e0; auto.

  + inversion H20; subst; auto.
    inversion H24; subst; auto.
    inversion H17; subst; auto.
    inversion H7; subst; auto.
    assert (value (v_opa_l e0 lx)). auto.
    contradiction.
    assert (value (v_opa_l e0 l2)). auto.
    contradiction.

  + inversion H20; subst; auto.
    inversion H25; subst; auto.
    inversion H14; subst; auto.
    inversion H22; subst; auto.
    inversion H16.
    inversion H22; subst; auto.
    inversion H16.  

  + inversion H20; subst; auto.
    inversion H25; subst; auto.
    inversion H14; subst; auto.

    assert (cls1 = cls2).
    inversion H_bijection; subst; auto.
    apply H0 in H5; auto.
    inversion H5; subst;  auto.
    rewrite <- H29 in H6; inversion H6; subst; auto.
    rewrite <- H30 in H8; inversion H8; subst; auto.
    apply H33.
    
    assert (body = body0 /\ arg_id = arg_id0 /\
          surface_syntax body = true).
    apply config_typing_lead_to_tm_typing in H_typing1.
    destruct H_typing1 as [T1].
    destruct H1 as [gamma1].
    inversion H1; subst; auto.

    inversion H29; subst; auto.

    destruct H36 as [F0]. destruct H0 as [l0].
    rewrite  H0 in H; inversion H; subst; auto.
    rewrite  H0 in H6; inversion H6; subst; auto.
    rewrite <- H31 in H12; inversion H12; subst; auto.
    rewrite H32 in H4; inversion H4; subst; auto.
    rewrite <- H9 in H8; inversion H8; subst; auto.
    rewrite H32 in H23; inversion H23; subst; auto.
    intro contra; inversion contra.
    destruct H1. destruct H10. 
    subst; auto. 

    inversion H15; subst; auto.
    inversion H28; subst; auto. 
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
    unfold sf_update in H10. rewrite H31 in H10. inversion H10.
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
    apply low_component_with_L_Label; auto.
    rewrite H10.
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
  split; auto.   
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
          (init_field_map (find_fields cls_def) empty_field_map) lb1)) o1 = Some (Heap_OBJ cls2 F1 lb0) ).
  apply extend_heap_lookup_eq; auto. 

  destruct (oid_decision (get_fresh_oid h2) o2 ).
   assert (lookup_heap_obj h2 (get_fresh_oid h2)  = None). 
   apply fresh_oid_heap with ct; auto.  rewrite e in H33.
   rewrite H33 in H22. inversion H22.
   
   assert ( lookup_heap_obj
     (add_heap_obj h2 (get_fresh_oid h2)
       (Heap_OBJ cls_def
          (init_field_map (find_fields cls_def) empty_field_map) lb2)) o2 = Some (Heap_OBJ cls2 F2 lb3) ).
   apply extend_heap_lookup_eq; auto.

   apply object_equal_L with lb0 lb3 cls2 cls2 F1 F2; auto.  
   split; auto.
   split; auto. 
   destruct H31.     
   split; auto. 
   intros.
   destruct H34 with fname fo1 fo2; auto. rename x into cls_f1.
   destruct H37 as [cls_f2]. destruct H37 as [lof1]. destruct H37 as [lof2].
   destruct H37 as [FF1]. destruct H37 as [FF2].
   destruct H37. destruct H38.

   exists cls_f1. exists cls_f2.
   exists lof1. exists lof2.
   exists FF1. exists FF2. 
   split; auto. 
   apply extend_heap_lookup_eq; auto. 
   apply lookup_extend_heap_fresh_oid with ct  (Heap_OBJ cls_f1 FF1 lof1) ; auto. 
   split; auto. 
   apply extend_heap_lookup_eq; auto. 
   apply lookup_extend_heap_fresh_oid with ct (Heap_OBJ cls_f2 FF2 lof2) ; auto. 
   assert (fo1 <> get_fresh_oid h1  ).
   apply lookup_extend_heap_fresh_oid with ct  (Heap_OBJ cls_f1 FF1 lof1) ; auto.
   assert ( bijection.left (bijection.extend_bijection φ (get_fresh_oid h1) (get_fresh_oid h2) H6 H7)  fo1 = 
            bijection.left φ fo1) by (apply bijection.left_extend_bijection_neq; auto).

   destruct H39.
   destruct H39.  left. rewrite H41. auto.
   right; auto. 
   
   
   
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
  (*labelData*)
  inversion H17; subst; auto. 
  inversion H19; subst; auto.
  exists φ. split; auto.

  inversion H17; subst; auto. intuition.  
  inversion H20; subst; auto. 
  assert (value e). apply value_L_eq with v h1' h2'  φ; auto.
  intuition. 

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  (* L_eq_container (Container t1 (labelData hole lo :: fs) lb1 sf1) h1' (Container t2 fs2 lb2 sf2) h2 φ *)
  inversion H17; subst; auto. 
  inversion H20; subst; auto. inversion H9; subst; auto. 
  exists φ. split; auto.
  inversion H17; subst; auto.
  inversion H21; subst; auto. inversion H9; subst;auto.
  inversion H3; subst; auto.
  inversion H12. 

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
(*L_eq_container (Container (labelData v lo) fs1 lb1 sf1) h1' (Container t2 fs2 lb2 sf2) h2 φ*)
  inversion H18; subst; auto.
  inversion H20; subst; auto.
  assert (value e). apply value_L_eq2 with v h1' h2'  φ; auto.
  intuition.

  inversion H18; subst; auto.  
  inversion H21; subst; auto.
  
  exists φ. split; auto. 
  apply L_equivalence_config_L; auto.
  apply L_eq_ctn; auto.
  case_eq (flow_to lo0 L_Label); intro; auto. 

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  (* L_eq_container (Container (unlabel e) fs1 lb1 sf1) h1' (Container t2 fs2 lb2 sf2) h2 φ*)
  inversion H17; subst; auto.  
  inversion H19; subst; auto.
  exists φ. split; auto.
  
  inversion H17; subst; auto.
  inversion H19; subst; auto.
  inversion H3; subst; auto; intuition. 

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  (*L_eq_container (Container t1 (unlabel hole :: fs) lb1 sf1) h1' (Container t2 fs2 lb2 sf2) h2 φ*)
  inversion H17; subst; auto.  
  inversion H20; subst; auto.  exists φ. split; auto.
  inversion H17; subst; auto.
  inversion H21; subst; auto. inversion H9; subst; auto.
  inversion H1; subst; auto.
  inversion H12.

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  (* L_eq_container (Container (unlabel (v_l v lo)) fs1 lb1 sf1) h1' (Container t2 fs2 lb2 sf2) h2 φ*)
  inversion H17; subst; auto. 
  inversion H19; subst; auto.
  inversion H4; subst; auto; intuition.

  inversion H17; subst; auto.
  (*
  case_eq (flow_to (join_label lb2 lo0) L_Label); intro;
    exists φ. auto.

  apply L_equivalence_config_H; auto.*)
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
  inversion H18; subst; auto. 
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

  apply L_equivalence_config_H; auto.
  unfold low_component.
  rewrite H.  rewrite H1. fold low_component.
  auto.

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  (*L_eq_container (Container (labelOf e) fs1 lb1 sf1) h1' (Container t2 fs2 lb2 sf2) h2 φ*)
  inversion H17; subst; auto.   
  inversion H19; subst; auto.  exists φ. split;  auto.
  
  inversion H17; subst; auto. 
  inversion H19; subst; auto.
  inversion H4; subst; auto; intuition. 

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  (* L_eq_container (Container t1 (labelOf hole :: fs) lb1 sf1) h1' (Container t2 fs2 lb2 sf2) h2 φ*)
  inversion H17; subst; auto.  
  inversion H20; subst; auto.
  exists φ. split;  auto.
  
  inversion H17; subst; auto. 
  inversion H21; subst; auto.
  inversion H9; subst; auto.
  inversion H1; subst; auto.
  inversion H12.

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  (*L_eq_container (Container (labelOf (v_l v lo)) fs1 lb1 sf1) h1' (Container t2 fs2 lb2 sf2) h2 φ*)
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
  (*L_eq_container (Container (unlabelOpaque e) fs1 lb1 sf1) h1' (Container t2 fs2 lb2 sf2) h2 φ*)
  inversion H17; subst; auto.  
  inversion H19; subst; auto.
  exists φ. split; auto.
  
  inversion H17; subst; auto. 
  inversion H19; subst; auto.
  inversion H3; subst; auto; intuition. 

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  (*L_eq_container (Container t1 (unlabelOpaque hole :: fs) lb1 sf1) h1' (Container t2 fs2 lb2 sf2) h2 φ*)
  inversion H17; subst; auto.  
  inversion H20; subst; auto.
  exists φ. split; auto.
  
  inversion H17; subst; auto. 
  inversion H21; subst; auto.
  inversion H9; subst; auto.
  inversion H1; subst; auto.
  inversion H12. 

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  (*L_eq_container (Container (unlabelOpaque (v_opa_l v lo)) fs1 lb1 sf1) h1' (Container t2 fs2 lb2 sf2) h2 φ*)
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
    unfold low_component; rewrite H; rewrite H1;  auto.

  apply L_equivalence_config_L; auto.
  apply L_eq_ctn; auto.
  apply L_equivalence_store_L; auto.
  split; intros.  match goal with
          | H :  empty_stack_frame _ = Some _ |- _
            => inversion H
                  end.
  split; auto.

  (* raise label *)
- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  inversion H17; subst; auto. 
  inversion H19; subst; auto.
  exists φ. split; auto.

  inversion H17; subst; auto.
  inversion H21; subst; auto.
  assert (value e). apply value_L_eq with  (ObjId o) h1' h2 φ; auto. intuition.


- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  (* L_equivalence_config
               (Config ct (Container t1 (raiseLabel hole lo :: fs) lb1 sf1) ctns_stack1' h1')
               (Config ct (Container t2 (raiseLabel hole lo0 :: fs0) lb2 sf2) ctns_stack2' h2') φ *)
  inversion H17; subst; auto. 
  inversion H20; subst; auto.
  inversion H9; subst; auto. 
  exists φ. split; auto.
  inversion H17; subst; auto.
  inversion H21; subst; auto.
  inversion H9; subst;auto.
  inversion H3; subst; auto.
  inversion H12. 

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
(*L_equivalence_config
               (Config ct (Container (raiseLabel (ObjId o) lo') fs1 lb1 sf1) ctns_stack1' h1)
               (Config ct (Container (raiseLabel e lo0) fs2 lb2 sf2) ctns_stack2' h2') φ*)
  inversion H19; subst; auto. 
  inversion H21; subst; auto.
  assert (value e). apply value_L_eq2 with  (ObjId o) h1 h2' φ; auto. intuition.

  inversion H19; subst; auto. 
  inversion H23; subst; auto.


  case_eq (flow_to lo'0 L_Label).
  (*lo'0 is low*)
  + exists φ. split; auto. 
    apply lbl_L_change_obj_both_lbl_preserve_bijection with ct lo lo0 lb1 lb2; auto. 
    inversion H_valid1; subst; auto.
    inversion H16; subst; auto.

    inversion H_valid2; subst; auto.
    inversion H35; subst; auto.    
    apply lbl_L_change_obj_both_lbl_preserve_l_eq_config with lo lo0; auto.
    
  + (*lo' is high*)
    intro.
    case_eq (flow_to lo L_Label); intro.
    ++
      assert (flow_to lo0 L_Label = true).
      inversion H10; subst; auto.
      +++ 
        rewrite <- H12 in H6; inversion H6; subst; auto.
      +++
        rewrite <- H7 in H; inversion H; subst; auto. try (inconsist).
      +++
        inversion H10; subst; auto.
        assert (forall a1 a2 : oid, decision.Decision (a1 = a2)); auto. 
        exists (reduce_bijection φ o o0 H8).
        split; auto.
        eauto using lbl_H_raise_obj_both_lbl_preserve_bijection.
        inversion H_valid1; subst; auto.
        inversion H33; subst; auto.
        inversion H_valid2; subst; auto.
        inversion H43; subst; auto.    
        apply lbl_H_raise_obj_both_lbl_preserve_l_eq_config with φ lo lo0 H8; auto.
        rewrite <- H8 in H; inversion H; subst; auto.
        try (inconsist).
    ++
      assert (flow_to lo0 L_Label = false).
      inversion H10; subst; auto.
      rewrite <- H8 in H; inversion H; subst; auto.
      try (inconsist).

      rewrite <- H9 in H6; inversion H6; subst; auto.


      exists φ. split; auto.
      eauto using  lbl_H_change_obj_both_lbl_preserve_l_eq_config.
      assert (forall a1 a2 : oid, decision.Decision (a1 = a2)); auto.
      inversion H_valid1; subst; auto.
      inversion H28; subst; auto.
      inversion H_valid2; subst; auto.
      inversion H38; subst; auto.    
      apply lbl_H_change_obj_both_lbl_preserve_l_eq_config  with lo lo0; auto. 
            
  
  
- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  (*L_eq_container (Container (Assignment id e) fs1 lb1 sf1) h1' (Container t2 fs2 lb2 sf2) h2 φ*)
  inversion H17; subst; auto.
  inversion H19; subst; auto.
  exists φ. split; auto. 

  inversion H17; subst; auto.
  inversion H19; subst; auto.
  assert (value e). apply value_L_eq with v h1' h2' φ; auto. intuition.
  
- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  (*L_eq_container (Container t1 (Assignment id hole :: fs) lb1 sf1) h1' (Container t2 fs2 lb2 sf2) h2 φ*)
  inversion H17; subst; auto.  
  inversion H20; subst; auto.
  inversion H9; subst; auto.  exists φ. split; auto.

  inversion H17; subst; auto.

  inversion H21; subst; auto.
  inversion H9; subst; auto.
  inversion H3; subst; auto.
  inversion H12. 

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  (*L_eq_container (Container (Assignment id v) fs1 lb1 sf1) h1' (Container t2 fs2 lb2 sf2) h2 φ*)
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
  inversion H19; subst; auto.
  exists φ. split;  auto.
  
  inversion H17; subst; auto. 
  inversion H22; subst; auto.
  assert (value e). apply value_L_eq with  v h1' h2'  φ; auto.
  intuition.

  inversion H17; subst; auto. 
  inversion H21; subst; auto.
  inversion H24; subst; auto. 
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
  (*L_eq_container (Container t1 (FieldWrite hole f e2 :: fs) lb1 sf1) h1' (Container t2 fs2 lb2 sf2) h2 φ*)
  inversion H17; subst; auto.  
  inversion H20; subst; auto.
  inversion H9; subst; auto. exists φ. split;  auto.
  
  inversion H17; subst; auto. 
  inversion H21; subst; auto.
  inversion H9; subst; auto.
  inversion H23; subst; auto. inversion H12.

  inversion H17; subst; auto. 
  inversion H21; subst; auto.
  inversion H9; subst; auto.
  inversion H25; subst; auto.
  inversion H23; subst; auto.
  inversion H12. 
  
  
  inversion H17; subst; auto. 
  inversion H21; subst; auto. inversion H9; subst; auto.
  inversion H4; subst; auto. inversion H12. 

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  (*L_eq_container (Container (FieldWrite v f e2) fs1 lb1 sf1) h1' (Container t2 fs2 lb2 sf2) h2 φ*)
  inversion H20; subst; auto. 
  inversion H22; subst; auto.  
  assert (value e). apply value_L_eq2 with v h1' h2' φ; auto.
  intuition.

  inversion H20; subst; auto.
  inversion H25; subst; auto.
  exists φ. split; auto.

  inversion H20; subst; auto.
  inversion H24. subst; auto.
  inversion H27; subst; auto.
  destruct H with e1; auto. 

  
  inversion H20; subst; auto.
  inversion H24. subst; auto.
  assert (value e2). apply value_L_eq with v0 h1' h2 φ; auto. intuition.

  inversion H14; subst; auto.
  destruct H3 as [o'].
  destruct H3 as [cls'].
  destruct H3 as [F'].
  destruct H3 as [lo'].
  destruct H3.
  subst; auto.
  intuition.

  inversion H20; subst; auto.
  inversion H24; subst; auto.
  inversion H27; subst; auto.
  assert (value e1). apply value_L_eq with (v_opa_l v0 lx) h1' h2 φ; auto.
  assert (value v0).
  destruct H22; subst; auto. 
  destruct H3 as [o'].
  destruct H3 as [cls'].
  destruct H3 as [F'].
  destruct H3 as [lo'].
  destruct H3.
  subst; auto. 
  intuition.

  destruct H with  e1; auto.
  
- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  (*L_eq_container (Container t1 (FieldWrite v1 f hole :: fs) lb1 sf1) h1' (Container t2 fs2 lb2 sf2) h2 φ *)
  inversion H18; subst; auto.
  
  inversion H21; subst; auto.
  inversion H10; subst; auto.
  inversion H23; subst; auto.
  inversion H0.

  inversion H18; subst; auto. 
  inversion H22; subst; auto.
  inversion H10; subst; auto.  exists φ. split; auto.

  inversion H18; subst; auto.
  
  inversion H22; subst; auto.
  inversion H10; subst; auto.
  inversion H26. 

  inversion H18; subst; auto.
  inversion H22; subst; auto.
  inversion H10; subst; auto. 
  inversion H24; subst; auto.
  inversion H13.
  case_eq (hole_free e2); intro; rewrite H1 in H2; inversion H2.

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  (*L_eq_container (Container (FieldWrite v f (unlabelOpaque e2)) fs1 lb1 sf1) h1' (Container t2 fs2 lb2 sf2) h2 φ*)
  inversion H19; subst; auto. 
  inversion H21; subst; auto.
  assert (value e). apply value_L_eq2 with v h1' h2'  φ; auto.
  contradiction.

  inversion H19; subst; auto.
  inversion H24; subst; auto.
  inversion H27; subst; auto.
  destruct H6 with e3; auto. 

  inversion H19; subst; auto.
  inversion H23; subst; auto.
  inversion H26; subst; auto.
  exists φ. split; auto.
  apply L_equivalence_config_L; auto.
  
  inversion H19; subst; auto.
  inversion H23; subst; auto.
  inversion H26; subst; auto.
  destruct H21.
  inversion H2.
  destruct H2. destruct H2. destruct H2. destruct H2. destruct H2.
  inversion H2.

  inversion H19; subst; auto.
  inversion H23; subst; auto.
  inversion H26; subst; auto.
  assert (value e2); auto.
  apply value_L_eq with (v_opa_l v0 lx) h1' h2  φ; auto.
  destruct H21; subst; auto.
  destruct H2. destruct H2. destruct H2. destruct H2. destruct H2.
  subst; auto.
  contradiction. 


- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn);
  (*L_eq_container (Container t1 (FieldWrite v1 f (unlabelOpaque hole) :: fs) lb1 sf1) h1' (Container t2 fs2 lb2 sf2) h2 φ*)
  try (inversion H18; subst; auto; 
  inversion H21; subst; auto;
  inversion H10; subst; auto).

  inversion H18; subst; auto. 
  inversion H22; subst; auto.
  inversion H10; subst; auto.

  inversion H18; subst; auto. 
  inversion H22; subst; auto.
  inversion H10; subst; auto.

  inversion H18; subst; auto. 
  inversion H22; subst; auto.
  inversion H10; subst; auto.
  inversion H23; subst; auto.
  inversion H0. 

  inversion H18; subst; auto. 
  inversion H22; subst; auto.
  inversion H10; subst; auto.
  inversion H26.

  inversion H18; subst; auto. 
  inversion H22; subst; auto.
  inversion H10; subst; auto.
  exists φ. split; auto.

  inversion H18; subst; auto. 
  inversion H22; subst; auto.
  inversion H10; subst; auto.
  inversion H24; subst; auto.
  inversion H2; subst; auto.
  inversion H13; subst; auto.
  case_eq (hole_free e2); intro Hy; rewrite Hy in H4; inversion H4. 

  
- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  (*L_eq_container (Container (FieldWrite (ObjId o) f v) fs1 lb1 sf1) h1 (Container t2 fs2 lb2 sf2) h2 φ*)
  
  inversion H19; subst; auto. 
  inversion H21; subst; auto.
  assert (value e). apply value_L_eq2 with (ObjId o) h1 h2'  φ; auto.
  contradiction.

  inversion H19; subst; auto.
  inversion H24; subst; auto.
  assert (value e2). apply value_L_eq2 with v h1 h2'  φ; auto.
  destruct H3.
  subst; auto. 
  destruct H0 as [o'].
  destruct H0 as [cls'].
  destruct H0 as [F'].
  destruct H0 as [lo']. destruct H0.
  subst; auto.
  contradiction.

  inversion H19; subst; auto. 
  inversion H23; subst; auto.
  inversion H26; subst; auto.
  destruct H3; subst; auto.
  inversion H0.
  destruct H0. destruct H0. destruct H0. destruct H0. destruct H0.
  inversion H0. 
  
  inversion H19; subst; auto. 
  inversion H23; subst; auto.
  exists φ. split; auto.
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
  (*L_eq_container (Container (FieldWrite (ObjId o) f (unlabelOpaque (v_opa_l v lx))) fs1 lb1 sf1) h1 (Container t2 fs2 lb2 sf2) h2 φ*)
  inversion H19; subst; auto. 
  inversion H21; subst; auto.
  inversion H24; subst; auto.
  inversion H13; subst; auto. intuition. 
  
  inversion H19; subst; auto. intuition.

  inversion H19; subst; auto.
  inversion H24; subst; auto.
  inversion H27; subst; auto. 
  inversion H2; subst; auto.
  destruct H6 with (v_opa_l e2 lx); auto. 
  destruct H6 with  (v_opa_l e2 l2); auto.

  inversion H19; subst; auto.
  inversion H23; subst; auto.
  inversion H26; subst; auto.
  assert (value e2). apply value_L_eq2 with (v_opa_l v lx) h1 h2'  φ; auto.
  destruct H3; subst; auto.
  destruct H0. destruct H0. destruct H0. destruct H0. destruct H0.
  subst; auto.
  contradiction. 

  inversion H19; subst; auto.
  inversion H23; subst; auto.
  inversion H26; subst; auto.
  inversion H2; subst; auto.
  destruct H21; subst; auto.
  inversion H0.
  destruct H0. destruct H0. destruct H0. destruct H0. destruct H0.
  inversion H0.

  
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
  (* L_eq_container (Container (If guard s1 s2) fs1 lb1 sf1) h1' (Container t2 fs2 lb2 sf2) h2 φ*)
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

  + inversion H18; subst; auto.
    inversion H21; subst; auto.
    inversion H10; subst; auto.
    inversion H6; subst; auto.
    inversion H0. 

  + inversion H18; subst; auto.
    inversion H22; subst; auto.
    inversion H10; subst; auto.
    inversion H12; subst; auto.
    inversion H0.
    case_eq ( hole_free e1 ); intro; rewrite H1 in H2; intuition.

  + inversion H18; subst; auto.
    inversion H21; subst; auto.
    inversion H10; subst; auto.
    inversion H8; subst; auto.
    inversion H0.

  +  inversion H18; subst; auto.
     inversion H21; subst; auto.
     inversion H10; subst; auto.
     inversion H12; subst; auto.
     inversion H0. 

  + inversion H18; subst; auto.
    inversion H22; subst; auto.
    inversion H10; subst; auto.
    inversion H14; subst; auto.
    inversion H0.
    case_eq (hole_free e1); intro Hy; rewrite Hy in H2; intuition.

  + inversion H18; subst; auto.
    inversion H22; subst; auto.
    inversion H10; subst; auto.
    inversion H14; subst; auto.
    inversion H5; subst; auto. 
    inversion H0.
    case_eq (hole_free e1); intro Hy; rewrite Hy in H2; intuition.


  + inversion H18; subst; auto.
    inversion H21; subst; auto.
    inversion H10; subst; auto.
    inversion H6; subst; auto.
    inversion H0. 
    
  +  inversion H18; subst; auto.
  inversion H21; subst; auto.
  inversion H10; subst; auto.
  inversion H5; subst; auto.
  inversion H0.

  + inversion H18; subst; auto.
  inversion H21; subst; auto.
  inversion H10; subst; auto.
  inversion H5; subst; auto.
  inversion H0.
  
  + inversion H18; subst; auto.
  inversion H21; subst; auto.
  inversion H10; subst; auto.
  inversion H5; subst; auto.
  inversion H0.

  + inversion H18; subst; auto.
  inversion H21; subst; auto.
  inversion H10; subst; auto.
  inversion H6; subst; auto.
  inversion H0.

  + inversion H18; subst; auto.
  inversion H21; subst; auto.
  inversion H10; subst; auto.
  inversion H6; subst; auto.
  inversion H0.

  + inversion H18; subst; auto.
  inversion H21; subst; auto.
  inversion H10; subst; auto.
  inversion H7; subst; auto.
  inversion H0.
  
  
  + inversion H18; subst; auto.
  inversion H22; subst; auto.
  inversion H10; subst; auto.
  inversion H24; subst; auto.
  inversion H0. 
  case_eq ( hole_free e1 ); intro; rewrite H1 in H2; intuition.

  + inversion H18; subst; auto.
  inversion H22; subst; auto.
  inversion H10; subst; auto.
  inversion H24; subst; auto.
  inversion H5; subst; auto.
  inversion H0; subst; auto. 
  case_eq ( hole_free e1 ); intro; rewrite H1 in H2; intuition.

  + inversion H18; subst; auto.
  inversion H21; subst; auto.
  inversion H10; subst; auto.
  inversion H7; subst; auto. 
  inversion H0. 
  
  + inversion H18; subst; auto.
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
  
- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  inversion H16; subst; auto.
  inversion H13; subst; auto.
  exists φ. split; auto. 
 Qed.
Hint Resolve simulation_L.
 