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
Require Import preservation.


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
  + inversion H17; subst; auto.
    exists φ. split;  auto.
    inversion H19; subst; auto. 
  + inversion H17; subst; auto.
    inversion H20; subst; auto.
    assert (value e1). auto. 
    apply  value_L_eq with v h1' h2' φ; auto. 
    intuition.
  + inversion H17; subst; auto.
    inversion H22; subst; auto.
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
    inversion H23; subst; auto.
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
    assert (value e1). apply value_L_eq2 with v1 h1' h2' φ; auto.
    intuition.
  + inversion H20; subst; auto.
    inversion H23; subst; auto.
    assert (value e2). apply value_L_eq2 with v2 h1' h2' φ; auto.
    intuition.
  + inversion H20; subst; auto.
    inversion H25; subst; auto.

    
    exists  φ; split; auto.

    pose proof (exclude_middle_runtime_val v1 v2 H H0).
    assert (EqCmp v1 v2 <> return_hole). intro contra; inversion contra. 
    pose proof config_typing_lead_to_tm_typing h1' ct  (EqCmp v1 v2) fs1 lb1 sf1 ctns_stack1' T H_typing1 H4.
    destruct H5 as [Ttm]. destruct H5 as [gamma]. inversion H5; subst; auto.

    inversion H; subst; auto; inversion H8; subst; auto.
    (* v = ObjId o*)
    ++
      inversion H10; subst; auto.
      +++
        (* two objects are with low labels and low_eq *)
        inversion H0; subst; auto; inversion H28; subst; auto.
        ++++
          unfold runtime_val in H3. (* inversion H3; subst; auto. *)
          inversion H12; subst; auto.
          +++++
            assert(  flow_to
               (join_label (join_label (join_label (runtime_label (ObjId o)) (runtime_label (ObjId o0))) lb1)
                           (join_label (object_label (runtime_val (ObjId o)) h1') (object_label (runtime_val (ObjId o0)) h1')))  L_Label = true).
          assert (flow_to (runtime_label (ObjId o)) L_Label = true).
          unfold runtime_label. auto.
          assert (flow_to (runtime_label (ObjId o0)) L_Label = true).
          unfold runtime_label. auto.
          apply join_L_label_flow_to_L ; auto.
          apply join_L_label_flow_to_L ; auto.
          apply join_L_label_flow_to_L ; auto.
          unfold runtime_val. unfold object_label.  rewrite <- H13. auto.
          unfold runtime_val. unfold object_label.  rewrite <- H36. auto.

          assert(  flow_to
              (join_label (join_label (join_label (runtime_label (ObjId o2)) (runtime_label (ObjId o3))) lb2)
             (join_label (object_label (runtime_val (ObjId o2)) h2') (object_label (runtime_val (ObjId o3)) h2'))) L_Label = true).
          assert (flow_to (runtime_label (ObjId o2)) L_Label = true).
          unfold runtime_label. auto.
          assert (flow_to (runtime_label (ObjId o3)) L_Label = true).
          unfold runtime_label. auto.
          apply join_L_label_flow_to_L ; auto.
          apply join_L_label_flow_to_L ; auto.
          apply join_L_label_flow_to_L ; auto.
          unfold runtime_val. unfold object_label.  rewrite <- H29. auto.
          unfold runtime_val. unfold object_label.  rewrite <- H38. auto.

          apply L_equivalence_config_L; auto.
          apply L_eq_ctn;auto.

          destruct H3.
          inversion H3; subst; auto.
          rewrite H7 in H34; inversion H34; subst; auto.
          unfold runtime_val in H1. unfold runtime_val in H16.
          assert (result = B_true). auto.
          assert (result0 = B_true). auto.
          subst; auto.

          unfold runtime_val in H2. unfold runtime_val in H17.
          assert (ObjId o2 <> ObjId o3). intro contra; inversion contra.
          subst; auto. apply bijection.right_left in H7.
          apply bijection.right_left in H34. 
          rewrite H34 in H7; inversion H7; subst; auto. 
          assert (result = B_false). auto.
          assert (result0 = B_false). auto.
          subst; auto.

          +++++
            assert (flow_to (join_label (object_label (runtime_val (ObjId o)) h1') (object_label (runtime_val (ObjId o0)) h1')) L_Label = false).
          apply flow_join_label with (object_label (runtime_val (ObjId o0)) h1') (object_label (runtime_val (ObjId o)) h1') ; auto.
          unfold runtime_val. unfold object_label.  rewrite <- H34. auto.

          assert (flow_to (join_label (join_label (join_label (runtime_label (ObjId o)) (runtime_label (ObjId o0))) lb1)
                                      (join_label (object_label (runtime_val (ObjId o)) h1') (object_label (runtime_val (ObjId o0)) h1'))) L_Label = false).
          apply flow_join_label with (join_label (object_label (runtime_val (ObjId o)) h1') (object_label (runtime_val (ObjId o0)) h1'))
                                     (join_label (join_label (runtime_label (ObjId o)) (runtime_label (ObjId o0))) lb1); auto. 

          
          assert (flow_to  (join_label (object_label (runtime_val (ObjId o2)) h2') (object_label (runtime_val (ObjId o3)) h2')) L_Label = false).
          apply flow_join_label with (object_label (runtime_val (ObjId o3)) h2') (object_label (runtime_val (ObjId o2)) h2') ; auto.
          unfold runtime_val. unfold object_label.  rewrite <- H37. auto. 

          assert (flow_to (join_label (join_label (join_label (runtime_label (ObjId o2)) (runtime_label (ObjId o3))) lb2)
                                      (join_label (object_label (runtime_val (ObjId o2)) h2') (object_label (runtime_val (ObjId o3)) h2'))) L_Label = false).
          eauto using flow_join_label.           
          apply L_equivalence_config_H; auto.          
          destruct ctns_stack1'.
          inversion H21; subst; auto. 
          unfold low_component. rewrite H41. rewrite H43. auto.
          apply L_equivalence_config_L; auto.
          apply L_eq_ctn; auto.
          apply  L_equivalence_store_L; auto.
          split; auto.
          intros; auto. inversion H44.
          intuition.

          inversion H21; subst; auto. 
          unfold low_component. rewrite H41. rewrite H43. auto.


        ++++ inversion H12; subst; auto. 
            assert(  flow_to
               (join_label (join_label (join_label (runtime_label (ObjId o)) (runtime_label null)) lb1)
                           (join_label (object_label (runtime_val (ObjId o)) h1') (object_label (runtime_val null) h1')))  L_Label = true).          assert (flow_to (runtime_label (ObjId o)) L_Label = true).
          unfold runtime_label. auto.
          apply join_L_label_flow_to_L ; auto.
          apply join_L_label_flow_to_L ; auto.
          apply join_L_label_flow_to_L ; auto.
          unfold runtime_val. unfold object_label.  rewrite <- H13. auto.

          assert(  flow_to
              (join_label (join_label (join_label (runtime_label (ObjId o2)) (runtime_label null)) lb2)
             (join_label (object_label (runtime_val (ObjId o2)) h2') (object_label (runtime_val null) h2'))) L_Label = true).
          assert (flow_to (runtime_label (ObjId o2)) L_Label = true).
          unfold runtime_label. auto.
          apply join_L_label_flow_to_L ; auto.
          apply join_L_label_flow_to_L ; auto.
          apply join_L_label_flow_to_L ; auto.
          unfold runtime_val. unfold object_label.  rewrite <- H29. auto.
          apply L_equivalence_config_L; auto.
          apply L_eq_ctn;auto.
          assert (ObjId o <> null). intro contra; inversion contra.
          assert (ObjId o2 <> null). intro contra; inversion contra.      
          assert (result = B_false). auto.
          assert (result0 = B_false). auto.
          subst; auto.

        ++++ inversion H12; subst; auto.
             +++++
               inversion H6; subst; auto; inversion H38; subst; auto.
             ++++++
               inversion H48; subst; auto.
             +++++++
               unfold runtime_label.
             unfold runtime_val. unfold object_label. rewrite <- H13.
             rewrite <- H29.  auto. rewrite <- H45.
             rewrite <- H47. 
             apply L_equivalence_config_L; auto.
             apply join_label_flow_L;auto.
             apply join_L_label_flow_to_L; auto.
             apply join_L_label_flow_to_L; auto.
             apply join_L_label_flow_to_L; auto.
             apply join_L_label_flow_to_L; auto.            
                
             apply L_eq_ctn;auto.
             apply join_label_flow_L;auto.
             apply join_L_label_flow_to_L; auto.
             apply join_L_label_flow_to_L; auto.
             apply join_L_label_flow_to_L; auto.
             apply join_L_label_flow_to_L; auto.
               
             unfold runtime_val in H1.
             case_eq (beq_oid o o0); intro.
             apply beq_oid_equal in H35; subst; auto.             
             assert (result = B_true); auto.
             rewrite H36 in H7; inversion H7; subst; auto. 
             unfold runtime_val in H16.
             assert (result0 = B_true); auto.
             subst; auto.

             case_eq (beq_oid o2 o3); intro.
             apply beq_oid_equal in H52; subst; auto.
             Require Import bijection. 
             apply right_left in H7.
             apply right_left in H36.
             rewrite  H36 in H7; inversion H7; subst; auto.
             assert (beq_oid o o = true). apply beq_oid_same.
             try (inconsist).
             
             unfold runtime_val in H2.
             assert (result = B_false).
             apply H2. intro contra; inversion contra.
             subst; auto.
             assert (beq_oid o0 o0 = true). apply beq_oid_same.
             try (inconsist).

             unfold runtime_val in H17.
             assert (result0 = B_false).
             apply H17. intro contra; inversion contra.
             subst; auto.
             assert (beq_oid o3 o3 = true). apply beq_oid_same.
             try (inconsist).
             subst; auto.
             +++++++
               assert (flow_to 
             (join_label
             (join_label
                (join_label (runtime_label (ObjId o))
                   (runtime_label (v_opa_l (ObjId o0) lb))) lb1)
             (join_label (object_label (runtime_val (ObjId o)) h1')
                (object_label (runtime_val (v_opa_l (ObjId o0) lb)) h1'))) L_Label = false).
             unfold runtime_val. unfold runtime_label.
             unfold object_label. rewrite <- H13. rewrite <-H36. 
             apply  join_label_flow_H; auto.

             assert (flow_to 
             (join_label
             (join_label
                (join_label (runtime_label (ObjId o2))
                   (runtime_label (v_opa_l (ObjId o3) lb))) lb2)
             (join_label (object_label (runtime_val (ObjId o2)) h2')
                (object_label (runtime_val (v_opa_l (ObjId o3) lb)) h2'))) L_Label = false).
             unfold runtime_val. 
             unfold runtime_label. unfold object_label.
             rewrite <- H29. rewrite <- H46.  
             apply  join_label_flow_H; auto.

             apply L_equivalence_config_H; auto.   
             inversion H21; subst; auto. 
             unfold low_component. rewrite H35. rewrite H51. 
             apply L_equivalence_config_L; auto.
             apply L_eq_ctn; auto.
             apply  L_equivalence_store_L; auto.
             split; auto.
             intros; auto. inversion H52.
             intuition.

             inversion H21; subst; auto.
             unfold low_component. rewrite H35. rewrite H51. auto.               

             ++++++
               inversion H48; subst; auto.
               unfold runtime_label.
               unfold runtime_val. unfold object_label.
               rewrite <- H13. rewrite <- H29. 
               apply L_equivalence_config_L; auto.
               apply join_label_flow_L;auto.
               apply join_L_label_flow_to_L; auto.
               apply join_L_label_flow_to_L; auto.
               apply join_L_label_flow_to_L; auto.
               apply join_L_label_flow_to_L; auto.            
                
               apply L_eq_ctn;auto.
               apply join_label_flow_L;auto.
               apply join_L_label_flow_to_L; auto.
               apply join_L_label_flow_to_L; auto.
               apply join_L_label_flow_to_L; auto.
               apply join_L_label_flow_to_L; auto.
               
               unfold runtime_val in H2.
               assert (result = B_false); auto.
               apply H2. intro contra; inversion contra.

               unfold runtime_val in H17.
               assert (result0 = B_false); auto.
               apply H17. intro contra; inversion contra. 
               subst; auto.
               ++++++
                 destruct H34 with v0 lb4; auto.
               +++++
              assert (flow_to 
             (join_label
             (join_label
                (join_label (runtime_label (ObjId o)) (runtime_label (v_opa_l v lb))) lb1)
             (join_label (object_label (runtime_val (ObjId o)) h1')
                (object_label (runtime_val (v_opa_l v lb)) h1'))) L_Label = false).
             unfold runtime_val. unfold runtime_label.
             unfold object_label. rewrite <- H13. fold object_label.
             apply  join_label_flow_H; auto.

             assert (flow_to 
             (join_label
             (join_label
                (join_label (runtime_label (ObjId o2)) (runtime_label (v_opa_l e2 l2)))
                lb2)
             (join_label (object_label (runtime_val (ObjId o2)) h2')
                (object_label (runtime_val (v_opa_l e2 l2)) h2'))) L_Label = false).
             unfold runtime_val. 
             unfold runtime_label. unfold object_label. rewrite <- H29. 
             apply  join_label_flow_H; auto.

             apply L_equivalence_config_H; auto.   
             inversion H21; subst; auto. 
             unfold low_component. rewrite H35. rewrite H36. 
             apply L_equivalence_config_L; auto.
             apply L_eq_ctn; auto.
             apply  L_equivalence_store_L; auto.
             split; auto.
             intros; auto. inversion H43.
             intuition.

             inversion H21; subst; auto.
             unfold low_component. rewrite H35. rewrite H36. auto.                 

      +++
        assert (flow_to (join_label
             (join_label (join_label (runtime_label (ObjId o)) (runtime_label v2)) lb1)
             (join_label (object_label (runtime_val (ObjId o)) h1')
                         (object_label (runtime_val v2) h1')))  L_Label = false).
        unfold runtime_val. 
        unfold object_label. rewrite <- H7. fold object_label.
        fold runtime_val. 
        apply  join_label_flow_H; auto.

        assert (flow_to (join_label
             (join_label (join_label (runtime_label (ObjId o2)) (runtime_label v3)) lb2)
             (join_label (object_label (runtime_val (ObjId o2)) h2')
                (object_label (runtime_val v3) h2'))) L_Label = false).
        unfold runtime_val. 
        unfold object_label. rewrite <- H22. fold object_label.
        fold runtime_val. 
        apply  join_label_flow_H; auto.

        apply L_equivalence_config_H; auto.   
        inversion H21; subst; auto. 
        unfold low_component. rewrite H6. rewrite H33. 
        apply L_equivalence_config_L; auto.
        apply L_eq_ctn; auto.
        apply  L_equivalence_store_L; auto.
        split; auto.
        intros; auto. inversion H34.
        intuition.

        inversion H21; subst; auto.
        unfold low_component. rewrite H6. rewrite H33. auto.

    ++ inversion H10; subst; auto.
       inversion H0; subst; auto; inversion H28; subst; auto.
       +++ inversion H12; subst; auto.
           ++++  (* all L label*)
             unfold runtime_label.
             unfold runtime_val. unfold object_label.
             rewrite <- H13. rewrite <- H29. 
             apply L_equivalence_config_L; auto.
             apply join_label_flow_L;auto.
             apply join_L_label_flow_to_L; auto.
             apply join_L_label_flow_to_L; auto.
             apply join_L_label_flow_to_L; auto.

             apply L_eq_ctn;auto.
             apply join_label_flow_L;auto.
             apply join_L_label_flow_to_L; auto.
             apply join_L_label_flow_to_L; auto.
             apply join_L_label_flow_to_L; auto.
               
             unfold runtime_val in H2.
             assert (result = B_false); auto.
             apply H2. intro contra; inversion contra.
             unfold runtime_val in H17.
             assert (result0 = B_false); auto.
             apply H17. intro contra; inversion contra.
             subst; auto.             
           ++++
             assert (flow_to (join_label
             (join_label (join_label (runtime_label null) (runtime_label (ObjId o))) lb1)
             (join_label (object_label (runtime_val null) h1')
                (object_label (runtime_val (ObjId o)) h1')))  L_Label = false).
             unfold runtime_val. 
             unfold object_label. rewrite <- H7.
             apply  join_label_flow_H; auto.

        assert (flow_to (join_label
             (join_label (join_label (runtime_label null) (runtime_label (ObjId o2))) lb2)
             (join_label (object_label (runtime_val null) h2')
                (object_label (runtime_val (ObjId o2)) h2'))) L_Label = false).
        unfold runtime_val. 
        unfold object_label. rewrite <- H22. 
        apply  join_label_flow_H; auto.

        apply L_equivalence_config_H; auto.   
        inversion H21; subst; auto. 
        unfold low_component. rewrite H6. rewrite H33. 
        apply L_equivalence_config_L; auto.
        apply L_eq_ctn; auto.
        apply  L_equivalence_store_L; auto.
        split; auto.
        intros; auto. inversion H34.
        intuition.

        inversion H21; subst; auto.
        unfold low_component. rewrite H6. rewrite H33. auto.
       +++ inversion H12; subst; auto.
           unfold runtime_val. unfold runtime_label. 
           unfold object_label.
           assert (result = B_true); auto.
           assert (result0 = B_true); auto.
           apply L_equivalence_config_L; auto.
           apply join_label_flow_L;auto.
           apply join_label_flow_L;auto.          
          
           apply L_eq_ctn;auto.
           apply join_label_flow_L;auto.
           apply join_label_flow_L;auto.
           subst; auto. 
       +++ inversion H12; subst; auto.
           ++++ inversion H34; subst; inversion H29; subst; auto.
                +++++ inversion H40; subst; auto.
                ++++++
                  apply L_equivalence_config_L; auto.
                apply join_label_flow_L;auto.
                unfold runtime_val. unfold runtime_label. unfold object_label. rewrite <- H37; subst; auto.
                apply join_label_flow_L;auto.
                unfold runtime_val. unfold runtime_label. unfold object_label. rewrite <- H39; subst; auto.
                apply L_eq_ctn;auto.
                apply join_label_flow_L;auto.
                unfold runtime_val. unfold runtime_label. unfold object_label. rewrite <- H37; subst; auto.
                apply join_label_flow_L;auto.
                unfold runtime_val. unfold runtime_label. unfold object_label. rewrite <- H39; subst; auto.
                unfold runtime_val in H2.
                unfold runtime_val in H17.
                assert (result = B_false).
                apply H2; intro contra; inversion contra. 
                assert (result0 = B_false);auto.
                apply H17; intro contra; inversion contra.
                subst; auto. 

                ++++++
                  assert (flow_to (join_label
             (join_label
                (join_label (runtime_label null) (runtime_label (v_opa_l (ObjId o) lb)))
                lb1)
             (join_label (object_label (runtime_val null) h1')
                (object_label (runtime_val (v_opa_l (ObjId o) lb)) h1'))) L_Label = false).
             unfold runtime_val. 
             unfold object_label. rewrite <- H13.
             apply  join_label_flow_H; auto.


             assert (flow_to (join_label
             (join_label
                (join_label (runtime_label null) (runtime_label (v_opa_l (ObjId o2) lb)))
                lb2)
             (join_label (object_label (runtime_val null) h2')
                (object_label (runtime_val (v_opa_l (ObjId o2) lb)) h2'))) L_Label = false).
             unfold runtime_val. 
             unfold object_label. rewrite <- H38. 
             apply  join_label_flow_H; auto.

             apply L_equivalence_config_H; auto.   
             inversion H21; subst; auto. 
             unfold low_component. rewrite H9. rewrite H43. 
             apply L_equivalence_config_L; auto.
             apply L_eq_ctn; auto.
             apply  L_equivalence_store_L; auto.
             split; auto.
             intros; auto. inversion H44.
             intuition.

             inversion H21; subst; auto.
             unfold low_component. rewrite H9. rewrite H43. auto.

             +++++ inversion H40; subst;auto.
             unfold runtime_label. unfold runtime_val. unfold object_label.
             apply L_equivalence_config_L; auto.
             apply join_label_flow_L;auto.
             apply join_L_label_flow_to_L; auto.
             apply join_L_label_flow_to_L; auto.
             apply join_L_label_flow_to_L; auto.

             apply L_eq_ctn;auto.
             apply join_label_flow_L;auto.
             apply join_L_label_flow_to_L; auto.
             apply join_L_label_flow_to_L; auto.
             apply join_L_label_flow_to_L; auto.

             unfold runtime_val in H1.
             assert (result = B_true); auto.
             unfold runtime_val in H16.
             assert (result0 = B_true); auto. 
             subst; auto. 
             
             +++++ destruct H36 with v0 lb0; auto.
           ++++
             assert (flow_to 
             (join_label
             (join_label (join_label (runtime_label null) (runtime_label (v_opa_l v lb)))
                lb1)
             (join_label (object_label (runtime_val null) h1')
                (object_label (runtime_val (v_opa_l v lb)) h1'))) L_Label = false).
             unfold runtime_val. unfold runtime_label.
             apply  join_label_flow_H; auto.

             assert (flow_to (join_label
             (join_label
                (join_label (runtime_label null) (runtime_label (v_opa_l e2 l2))) lb2)
             (join_label (object_label (runtime_val null) h2')
                (object_label (runtime_val (v_opa_l e2 l2)) h2'))) L_Label = false).
             unfold runtime_val. 
             unfold runtime_label.
             apply  join_label_flow_H; auto.

             apply L_equivalence_config_H; auto.   
             inversion H21; subst; auto. 
             unfold low_component. rewrite H9. rewrite H13. 
             apply L_equivalence_config_L; auto.
             apply L_eq_ctn; auto.
             apply  L_equivalence_store_L; auto.
             split; auto.
             intros; auto. inversion H35.
             intuition.

             inversion H21; subst; auto.
             unfold low_component. rewrite H9. rewrite H13. auto.


    ++ inversion H10; subst; auto.
       +++ inversion H6; subst; auto; inversion H29; subst; auto.
           ++++ inversion H40; subst; auto.
                +++++
                  inversion H0; subst; inversion H28; subst; auto.
                ++++++
                  inversion H12; subst; auto.
                +++++++
                  unfold runtime_label.
                unfold runtime_val. unfold object_label.
                rewrite <- H37. rewrite <- H39. rewrite <- H46.
                rewrite <- H48. 
                apply L_equivalence_config_L; auto.
               apply join_label_flow_L;auto.
               apply join_L_label_flow_to_L; auto.
               apply join_L_label_flow_to_L; auto.
               apply join_L_label_flow_to_L; auto.
               apply join_L_label_flow_to_L; auto.            
                
               apply L_eq_ctn;auto.
               apply join_label_flow_L;auto.
               apply join_L_label_flow_to_L; auto.
               apply join_L_label_flow_to_L; auto.
               apply join_L_label_flow_to_L; auto.
               apply join_L_label_flow_to_L; auto.

               unfold runtime_val in H1.
               case_eq (beq_oid o o0); intro.
               apply beq_oid_equal in H9; subst; auto.             
               assert (result = B_true); auto.
               rewrite H44 in H13; inversion H13; subst; auto. 
               unfold runtime_val in H16.
               assert (result0 = B_true); auto.
               subst; auto.

               case_eq (beq_oid o2 o3); intro.
               apply beq_oid_equal in H52; subst; auto.
               apply right_left in H13.
               apply right_left in H44.
               rewrite  H44 in H13; inversion H13; subst; auto.
               assert (beq_oid o o = true). apply beq_oid_same.
               try (inconsist).
             
               unfold runtime_val in H2.
               assert (result = B_false).
               apply H2. intro contra; inversion contra.
               subst; auto.
               assert (beq_oid o0 o0 = true). apply beq_oid_same.
               try (inconsist).

               unfold runtime_val in H17.
               assert (result0 = B_false).
               apply H17. intro contra; inversion contra.
               subst; auto.
               assert (beq_oid o3 o3 = true). apply beq_oid_same.
               try (inconsist).
               subst; auto.
               +++++++
                 assert (flow_to 
             (join_label
             (join_label
                (join_label (runtime_label (v_opa_l (ObjId o) lb))
                   (runtime_label (ObjId o0))) lb1)
             (join_label (object_label (runtime_val (v_opa_l (ObjId o) lb)) h1')
                (object_label (runtime_val (ObjId o0)) h1'))) L_Label = false).
               unfold runtime_val. unfold runtime_label.
               unfold object_label. rewrite <- H44. 
             apply  join_label_flow_H; auto.
             

             assert (flow_to
             (join_label
             (join_label
                (join_label (runtime_label (v_opa_l (ObjId o2) lb))
                   (runtime_label (ObjId o3))) lb2)
             (join_label (object_label (runtime_val (v_opa_l (ObjId o2) lb)) h2')
                (object_label (runtime_val (ObjId o3)) h2')))  L_Label = false).
             unfold runtime_val. 
             unfold runtime_label. unfold object_label. rewrite <- H47. 
             apply  join_label_flow_H; auto.

             apply L_equivalence_config_H; auto.   
             inversion H21; subst; auto. 
             unfold low_component. rewrite H9. rewrite H51. 
             apply L_equivalence_config_L; auto.
             apply L_eq_ctn; auto.
             apply  L_equivalence_store_L; auto.
             split; auto.
             intros; auto. inversion H52.
             intuition.

             inversion H21; subst; auto.
             unfold low_component. rewrite H9. rewrite H51. auto.                
             ++++++
               inversion H12; subst; auto. 
               unfold runtime_label.
             unfold runtime_val. unfold object_label.
             rewrite <- H37. rewrite <- H39. 
             apply L_equivalence_config_L; auto.
             apply join_label_flow_L;auto.
             apply join_L_label_flow_to_L; auto.
             apply join_L_label_flow_to_L; auto.
             apply join_L_label_flow_to_L; auto.
             apply join_L_label_flow_to_L; auto.            
                
             apply L_eq_ctn;auto.
             apply join_label_flow_L;auto.
             apply join_L_label_flow_to_L; auto. 
             apply join_L_label_flow_to_L; auto.
             apply join_L_label_flow_to_L; auto.
             apply join_L_label_flow_to_L; auto.

             unfold runtime_val in H2.
             assert (result = B_false); auto.
             apply H2. intro contra; inversion contra. 

             unfold runtime_val in H17.
             assert (result0 = B_false); auto.
             apply H17. intro contra; inversion contra. 
             subst; auto.

             ++++++
               inversion H12; subst; auto.
             +++++++ inversion H9; subst; inversion H48; subst; auto.
             ++++++++ inversion H58; subst; auto.
             {
               unfold runtime_label.
               unfold runtime_val. unfold object_label.
               rewrite <- H37. rewrite <- H55.
               rewrite <- H39. rewrite <- H57. 
             apply L_equivalence_config_L; auto.
             apply join_label_flow_L;auto.
             apply join_L_label_flow_to_L; auto.
             apply join_L_label_flow_to_L; auto.
             apply join_L_label_flow_to_L; auto.
             apply join_L_label_flow_to_L; auto.            
                
             apply L_eq_ctn;auto.
             apply join_label_flow_L;auto.
             apply join_L_label_flow_to_L; auto. 
             apply join_L_label_flow_to_L; auto.
             apply join_L_label_flow_to_L; auto.
             apply join_L_label_flow_to_L; auto.

             case_eq (beq_oid o o0); intro.
             apply beq_oid_equal in H45; subst; auto.             
             assert (result = B_true); auto.
             rewrite H46 in H13; inversion H13; subst; auto. 
             unfold runtime_val in H16.
             assert (result0 = B_true); auto.
             subst; auto.

             case_eq (beq_oid o2 o3); intro.
             apply beq_oid_equal in H62; subst; auto.
             apply right_left in H13.
             apply right_left in H46.
             rewrite  H46 in H13; inversion H13; subst; auto.
             assert (beq_oid o o = true). apply beq_oid_same.
             try (inconsist).
             
             unfold runtime_val in H2.
             assert (result = B_false).
             apply H2. intro contra; inversion contra.
             subst; auto.
             assert (beq_oid o0 o0 = true). apply beq_oid_same.
             try (inconsist).

             unfold runtime_val in H17.
             assert (result0 = B_false).
             apply H17. intro contra; inversion contra.
             subst; auto.
             assert (beq_oid o3 o3 = true). apply beq_oid_same.
             try (inconsist).
             subst; auto.               
             }
             {
               assert (flow_to 
             (join_label
             (join_label
                (join_label (runtime_label (v_opa_l (ObjId o) lb))
                   (runtime_label (v_opa_l (ObjId o0) lb4))) lb1)
             (join_label (object_label (runtime_val (v_opa_l (ObjId o) lb)) h1')
                (object_label (runtime_val (v_opa_l (ObjId o0) lb4)) h1'))) L_Label = false).
               unfold runtime_val. unfold runtime_label.
               unfold object_label. rewrite <- H46. 
             apply  join_label_flow_H; auto.
             

             assert (flow_to
             (join_label
             (join_label
                (join_label (runtime_label (v_opa_l (ObjId o2) lb))
                   (runtime_label (v_opa_l (ObjId o3) lb4))) lb2)
             (join_label (object_label (runtime_val (v_opa_l (ObjId o2) lb)) h2')
                (object_label (runtime_val (v_opa_l (ObjId o3) lb4)) h2')))  L_Label = false).
             unfold runtime_val. 
             unfold runtime_label. unfold object_label. rewrite <- H56. 
             apply  join_label_flow_H; auto.

             apply L_equivalence_config_H; auto.   
             inversion H21; subst; auto. 
             unfold low_component. rewrite H45. rewrite H61. 
             apply L_equivalence_config_L; auto.
             apply L_eq_ctn; auto.
             apply  L_equivalence_store_L; auto.
             split; auto.
             intros; auto. inversion H62.
             intuition.

             inversion H21; subst; auto.
             unfold low_component. rewrite H45. rewrite H61. auto.
             }
             
             ++++++++ inversion H58; subst; auto.
             unfold runtime_label.
             unfold runtime_val.
             unfold object_label. rewrite <- H37.
             rewrite <- H39. 
             apply L_equivalence_config_L; auto.
             apply join_label_flow_L;auto.
             
             apply join_L_label_flow_to_L; auto.
             apply join_L_label_flow_to_L; auto.
             apply join_L_label_flow_to_L; auto.
             apply join_L_label_flow_to_L; auto.            
                
             apply L_eq_ctn;auto.
             apply join_label_flow_L;auto.
             apply join_L_label_flow_to_L; auto. 
             apply join_L_label_flow_to_L; auto.
             apply join_L_label_flow_to_L; auto.
             apply join_L_label_flow_to_L; auto.

             unfold runtime_val in H2.
             assert (result = B_false); auto.
             apply H2. intro contra; inversion contra. 

             unfold runtime_val in H17.
             assert (result0 = B_false); auto.
             apply H17. intro contra; inversion contra. 
             subst; auto.
             
             ++++++++ destruct H44 with v0 lb5; auto.
             
             +++++++
               assert (flow_to 
             (join_label
             (join_label
                (join_label (runtime_label (v_opa_l (ObjId o) lb))
                   (runtime_label (v_opa_l v lb4))) lb1)
             (join_label (object_label (runtime_val (v_opa_l (ObjId o) lb)) h1')
                (object_label (runtime_val (v_opa_l v lb4)) h1'))) L_Label = false).
             unfold runtime_val. unfold runtime_label.
             apply  join_label_flow_H; auto.

             assert (flow_to 
              (join_label
             (join_label
                (join_label (runtime_label (v_opa_l (ObjId o2) lb))
                   (runtime_label (v_opa_l e2 l2))) lb2)
             (join_label (object_label (runtime_val (v_opa_l (ObjId o2) lb)) h2')
                (object_label (runtime_val (v_opa_l e2 l2)) h2'))) L_Label = false).
             unfold runtime_val. 
             unfold runtime_label.  
             apply  join_label_flow_H; auto.

             apply L_equivalence_config_H; auto.   
             inversion H21; subst; auto. 
             unfold low_component. rewrite H45. rewrite H46. 
             apply L_equivalence_config_L; auto.
             apply L_eq_ctn; auto.
             apply  L_equivalence_store_L; auto.
             split; auto.
             intros; auto. inversion H53.
             intuition.

             inversion H21; subst; auto.
             unfold low_component. rewrite H45. rewrite H46. auto.
              
             +++++
                  assert (flow_to 
             (join_label
             (join_label
                (join_label (runtime_label (v_opa_l (ObjId o) lb)) (runtime_label v2))
                lb1)
             (join_label (object_label (runtime_val (v_opa_l (ObjId o) lb)) h1')
                (object_label (runtime_val v2) h1'))) L_Label = false).
                unfold runtime_val. unfold object_label. rewrite <-H13.
             apply  join_label_flow_H; auto.

             assert (flow_to
            (join_label
             (join_label
                (join_label (runtime_label (v_opa_l (ObjId o2) lb)) (runtime_label v3))
                lb2)
             (join_label (object_label (runtime_val (v_opa_l (ObjId o2) lb)) h2')
                (object_label (runtime_val v3) h2')))  L_Label = false).
              unfold runtime_val. unfold object_label. rewrite <-H38.
             apply  join_label_flow_H; auto.

             apply L_equivalence_config_H; auto.   
             inversion H21; subst; auto. 
             unfold low_component. rewrite H9. rewrite H43. 
             apply L_equivalence_config_L; auto.
             apply L_eq_ctn; auto.
             apply  L_equivalence_store_L; auto.
             split; auto.
             intros; auto. inversion H44.
             intuition.

             inversion H21; subst; auto.
             unfold low_component. rewrite H9. rewrite H43. auto.
           ++++ inversion H40; subst; auto.
                inversion H0; subst; auto; inversion H28; subst; auto.
                +++++ inversion H12;subst; auto.
                ++++++
                  unfold runtime_label. unfold runtime_val. unfold object_label. rewrite <- H37.
                rewrite <- H39; auto. 
                apply L_equivalence_config_L; auto.
                apply join_label_flow_L;auto.
                apply join_L_label_flow_to_L; auto.
                apply join_L_label_flow_to_L; auto.
                apply join_L_label_flow_to_L; auto.
                apply join_L_label_flow_to_L; auto.            
                
                apply L_eq_ctn;auto.
                apply join_label_flow_L;auto.
                apply join_L_label_flow_to_L; auto.
                apply join_L_label_flow_to_L; auto.
                apply join_L_label_flow_to_L; auto.
                apply join_L_label_flow_to_L; auto.

                
             unfold runtime_val in H2.
             assert (result = B_false); auto.
             apply H2. intro contra; inversion contra.
             unfold runtime_val in H17.
             assert (result0 = B_false); auto.
             apply H17. intro contra; inversion contra. 
             subst; auto. 
             ++++++
              assert (flow_to 
             (join_label
             (join_label
                (join_label (runtime_label (v_opa_l null lb)) (runtime_label (ObjId o)))
                lb1)
             (join_label (object_label (runtime_val (v_opa_l null lb)) h1')
                (object_label (runtime_val (ObjId o)) h1'))) L_Label = false).
             unfold runtime_val. unfold runtime_label.
             unfold object_label. rewrite <- H13. 
             apply  join_label_flow_H; auto.

             assert (flow_to 
             (join_label
             (join_label
                (join_label (runtime_label (v_opa_l null lb)) (runtime_label (ObjId o2)))
                lb2)
             (join_label (object_label (runtime_val (v_opa_l null lb)) h2')
                (object_label (runtime_val (ObjId o2)) h2'))) L_Label = false).
             unfold runtime_val. 
             unfold runtime_label. unfold object_label. rewrite <- H38. 
             apply  join_label_flow_H; auto.

             apply L_equivalence_config_H; auto.   
             inversion H21; subst; auto. 
             unfold low_component. rewrite H9. rewrite H43. 
             apply L_equivalence_config_L; auto.
             apply L_eq_ctn; auto.
             apply  L_equivalence_store_L; auto.
             split; auto.
             intros; auto. inversion H44.
             intuition.

             inversion H21; subst; auto.
             unfold low_component. rewrite H9. rewrite H43. auto.
             +++++
               inversion H12; subst; auto. 
               apply L_equivalence_config_L; auto.
               apply join_label_flow_L;auto.
               apply join_L_label_flow_to_L; auto.
               apply join_L_label_flow_to_L; auto.
               apply join_L_label_flow_to_L; auto.
                
               apply L_eq_ctn;auto.
               apply join_label_flow_L;auto.
               apply join_L_label_flow_to_L; auto.
               apply join_L_label_flow_to_L; auto.
               apply join_L_label_flow_to_L; auto.

               unfold runtime_val in H2.
               assert (result = B_true); auto.
               unfold runtime_val in H16.
               assert (result0 = B_true); auto.
               subst; auto. 
               +++++
                 inversion H9; subst; inversion H39; subst; auto.
               ++++++
                 inversion H12; subst; auto.
               +++++++
                 inversion H53; subst; auto.
               ++++++++
                 unfold runtime_val. unfold runtime_label.
               unfold object_label. rewrite <- H49.
               unfold object_label. rewrite <- H51. 
               apply L_equivalence_config_L; auto.               
               apply join_label_flow_L;auto.
               apply join_L_label_flow_to_L; auto.
               apply join_L_label_flow_to_L; auto.
               apply join_L_label_flow_to_L; auto.
               apply join_L_label_flow_to_L; auto.
                
               apply L_eq_ctn;auto.
               apply join_label_flow_L;auto.
               apply join_L_label_flow_to_L; auto.
               apply join_L_label_flow_to_L; auto.
               apply join_L_label_flow_to_L; auto.
               apply join_L_label_flow_to_L; auto.

               unfold runtime_val in H2.
               assert (result = B_false); auto.
               apply H2. intro contra; inversion contra.

               unfold runtime_val in H17.
               assert (result0 = B_false); auto.
               apply H17. intro contra; inversion contra. 
               subst; auto.                                   
               ++++++++
                 assert (flow_to 
             (join_label
             (join_label
                (join_label (runtime_label (v_opa_l null lb))
                   (runtime_label (v_opa_l (ObjId o) lb0))) lb1)
             (join_label (object_label (runtime_val (v_opa_l null lb)) h1')
                (object_label (runtime_val (v_opa_l (ObjId o) lb0)) h1'))) L_Label = false).
             unfold runtime_val. unfold runtime_label.
             unfold object_label. rewrite <- H37. 
             apply  join_label_flow_H; auto.

             assert (flow_to 
             (join_label
             (join_label
                (join_label (runtime_label (v_opa_l null lb))
                   (runtime_label (v_opa_l (ObjId o2) lb0))) lb2)
             (join_label (object_label (runtime_val (v_opa_l null lb)) h2')
                (object_label (runtime_val (v_opa_l (ObjId o2) lb0)) h2'))) L_Label = false).             unfold runtime_val. 
             unfold runtime_label. unfold object_label. rewrite <- H50. 
             apply  join_label_flow_H; auto.

             apply L_equivalence_config_H; auto.   
             inversion H21; subst; auto. 
             unfold low_component. rewrite H35. rewrite H52. 
             apply L_equivalence_config_L; auto.
             apply L_eq_ctn; auto.
             apply  L_equivalence_store_L; auto.
             split; auto.
             intros; auto. inversion H54.
             intuition.

             inversion H21; subst; auto.
             unfold low_component. rewrite H35. rewrite H52. auto.
             +++++++
                 assert (flow_to 
            (join_label
             (join_label
                (join_label (runtime_label (v_opa_l null lb))
                   (runtime_label (v_opa_l (ObjId o) lb0))) lb1)
             (join_label (object_label (runtime_val (v_opa_l null lb)) h1')
                (object_label (runtime_val (v_opa_l (ObjId o) lb0)) h1'))) L_Label = false).
             unfold runtime_val. unfold runtime_label.
             apply  join_label_flow_H; auto.

             assert (flow_to 
             (join_label
             (join_label
                (join_label (runtime_label (v_opa_l null lb))
                   (runtime_label (v_opa_l e2 l2))) lb2)
             (join_label (object_label (runtime_val (v_opa_l null lb)) h2')
                         (object_label (runtime_val (v_opa_l e2 l2)) h2'))) L_Label = false).
             unfold runtime_val. 
             unfold runtime_label.
             apply  join_label_flow_H; auto.

             apply L_equivalence_config_H; auto.   
             inversion H21; subst; auto. 
             unfold low_component. rewrite H35. rewrite H37. 
             apply L_equivalence_config_L; auto.
             apply L_eq_ctn; auto.
             apply  L_equivalence_store_L; auto.
             split; auto.
             intros; auto. inversion H51.
             intuition.

             inversion H21; subst; auto.
             unfold low_component. rewrite H35. rewrite H37. auto.
             ++++++
               inversion H12; subst; auto.
             +++++++
               inversion H50; subst; auto.
             unfold runtime_val. unfold runtime_label.
             unfold object_label.  
             apply L_equivalence_config_L; auto.               
             apply join_label_flow_L;auto.
             apply join_L_label_flow_to_L; auto.
             apply join_L_label_flow_to_L; auto.
             apply join_L_label_flow_to_L; auto.

             apply L_eq_ctn;auto.
             apply join_label_flow_L;auto.
             apply join_L_label_flow_to_L; auto.
             apply join_L_label_flow_to_L; auto.
             apply join_L_label_flow_to_L; auto.
         
             unfold runtime_val in H1.
             assert (result = B_true); auto.
             unfold runtime_val in H16.
             assert (result0 = B_true); auto.
             subst; auto.                         

             +++++++
                 assert (flow_to 
            (join_label
             (join_label
                (join_label (runtime_label (v_opa_l null lb))
                   (runtime_label (v_opa_l null lb0))) lb1)
             (join_label (object_label (runtime_val (v_opa_l null lb)) h1')
                (object_label (runtime_val (v_opa_l null lb0)) h1'))) L_Label = false).
             unfold runtime_val. unfold runtime_label.
             apply  join_label_flow_H; auto.

             assert (flow_to 
             (join_label
             (join_label
                (join_label (runtime_label (v_opa_l null lb))
                   (runtime_label (v_opa_l e2 l2))) lb2)
             (join_label (object_label (runtime_val (v_opa_l null lb)) h2')
                (object_label (runtime_val (v_opa_l e2 l2)) h2'))) L_Label = false).
             unfold runtime_val. 
             unfold runtime_label.
             apply  join_label_flow_H; auto.

             apply L_equivalence_config_H; auto.   
             inversion H21; subst; auto. 
             unfold low_component. rewrite H35. rewrite H37. 
             apply L_equivalence_config_L; auto.
             apply L_eq_ctn; auto.
             apply  L_equivalence_store_L; auto.
             split; auto.
             intros; auto. inversion H45.
             intuition.

             inversion H21; subst; auto.
             unfold low_component. rewrite H35. rewrite H37. auto.
             ++++++
               destruct H13 with v0 lb3. auto.
           ++++ destruct H36 with v0 lb0. auto. 
       +++  
         assert (flow_to 
            (join_label
             (join_label (join_label (runtime_label (v_opa_l v lb)) (runtime_label v2))
                lb1)
             (join_label (object_label (runtime_val (v_opa_l v lb)) h1')
                (object_label (runtime_val v2) h1'))) L_Label = false).
             unfold runtime_val. unfold runtime_label.
             apply  join_label_flow_H; auto.

             assert (flow_to 
             (join_label
             (join_label (join_label (runtime_label (v_opa_l e2 l2)) (runtime_label v3))
                lb2)
             (join_label (object_label (runtime_val (v_opa_l e2 l2)) h2')
                (object_label (runtime_val v3) h2'))) L_Label = false).
             unfold runtime_val. 
             unfold runtime_label.
             apply  join_label_flow_H; auto.

             apply L_equivalence_config_H; auto.   
             inversion H21; subst; auto. 
             unfold low_component. rewrite H9. rewrite H13. 
             apply L_equivalence_config_L; auto.
             apply L_eq_ctn; auto.
             apply  L_equivalence_store_L; auto.
             split; auto.
             intros; auto. inversion H35.
             intuition.

             inversion H21; subst; auto.
             unfold low_component. rewrite H9. rewrite H13. auto.         


(*field access*)  
- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).  
  inversion H17; subst; auto.
  inversion H19; subst; auto. exists φ. split; auto. 
  inversion H17; subst; auto.
  inversion H20; subst; auto.
  inversion H9; subst; auto; intuition.

  inversion H17; subst; auto.
  inversion H20; subst; auto.
  inversion H9; subst; auto; intuition. 


- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  inversion H17; subst; auto. 
  inversion H20; subst; auto.
  inversion H9; subst; auto.
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
  

  (* field access with opaque object  *)

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  inversion H18; subst; auto.  
  inversion H20; subst; auto.
  inversion H9; subst; auto; intuition. 
  inversion H18; subst; auto.

  exists φ. split; auto.
  inversion H21; subst; auto.
  inversion H9; subst; auto.
  inversion H24; subst; auto. 
  inversion H_bijection; subst; auto.
  apply H1 in H3; auto. inversion H3.  subst; auto.
  rewrite <- H5 in H. inversion H. subst; auto. 
  rewrite <- H11 in H4. inversion H4; subst; auto. 

  assert (flow_to (join_label lb0 lb1) L_Label = true).
  apply join_L_label_flow_to_L; auto.
  
  assert (flow_to (join_label lb3 lb2) L_Label = true).
  apply join_L_label_flow_to_L; auto.

  assert (flow_to (join_label (join_label lb0 lb1) ell0) L_Label = true).
  apply join_L_label_flow_to_L; auto.

  assert (flow_to (join_label (join_label lb3 lb2) ell0) L_Label = true).    
  apply join_L_label_flow_to_L; auto.

  apply L_equivalence_config_L; auto.
  apply L_eq_ctn; auto.

  rewrite <-H28 in H5; inversion H5; subst; auto.
  rewrite <-H29 in H11; inversion H11; subst; auto.

  apply config_typing_lead_to_tm_typing in H_typing1.
  destruct H_typing1 as [T1].
  destruct H37 as [gamma1].
  
  apply config_typing_lead_to_tm_typing in H_typing2.
  destruct H_typing2 as [T2].
  destruct H38 as [gamma2].

  destruct H32; subst; auto.
  destruct H39; subst; auto.
  destruct H39.
  
  inversion H37; subst; auto.
  assert (v = null \/ exists o', v = ObjId o').
  apply field_value_opaque   with h1' o cls4 F3 lb4 fname0 ct cls' gamma1 ell0; auto.

  inversion H38; subst; auto. 
  assert (v0 = null \/ exists o', v0 = ObjId o').
  apply field_value_opaque  with h2' o0 cls4 F4 lb5 fname0 ct cls'0 gamma2 ell0; auto.

  destruct H41; subst; auto. 
  destruct H39 with fname0.
  assert (F3 fname0 = Some null). auto.
  apply H41 in H48; auto. rewrite <- H13 in H48; inversion H48; subst; auto. 

  destruct H42; subst; auto.
  destruct H39 with fname0.
  assert (F4 fname0 = Some null). auto.
  apply H45 in H48; auto. rewrite <- H0 in H48; inversion H48; subst; auto.

  destruct H41 as [o1]. destruct H42 as [o2].
  subst; auto.
  destruct H40 with fname0 o1 o2; auto. rename x into hfo1.
  destruct H41 as [hfo2].
  destruct H41 as [lof1]. destruct H41 as [lof2].
  destruct H41 as [FF1]. destruct H41 as [FF2].
  destruct H41. destruct H42.
  
  destruct H45.
  (*field is low object*)
  assert (L_equivalence_object o1 h1' o2 h2' φ).
  apply H1; auto.
  apply H45. 
  inversion H48; subst; auto. 
  apply L_equivalence_tm_eq_object_L with cls1 F1 lb0 cls2 F2 lb3 ; auto.
  apply H45. 

  (*field is high object*)
  destruct H45.
  eauto using L_equivalence_tm_eq_object_H. 
  
  intro contra; inversion contra.
  intro contra; inversion contra. 

  assert (flow_to (join_label (join_label lb0 lb1) ell0) L_Label = false).
  apply flow_join_label with (join_label lb0 lb1) ell0; auto.
  apply flow_join_label with lb0 lb1; auto.
  apply join_label_commutative.
  apply join_label_commutative.   

  assert (flow_to (join_label (join_label lb3 lb2) ell0) L_Label = false).    
  apply flow_join_label with (join_label lb3 lb2) ell0; auto.
  apply flow_join_label with lb3 lb2; auto.
  apply join_label_commutative.
  apply join_label_commutative.   
  
  rewrite <- H3 in H; inversion H; subst; auto.
  rewrite <- H7 in H4; inversion H4; subst; auto.
  apply L_equivalence_config_H ; auto.
  apply ctns_eq_lead_to_low_component_eq ; auto. 

  assert (flow_to (join_label (join_label lo lb1) ell) L_Label = false).
  apply flow_join_label with  ell (join_label lo lb1); auto.

  assert (flow_to (join_label (join_label lo0 lb2) ell0) L_Label = false).
  apply flow_join_label with  ell0 (join_label lo0 lb2); auto.
  apply L_equivalence_config_H ; auto.
  apply ctns_eq_lead_to_low_component_eq ; auto. 

(* method call *)
- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).    
    inversion H17; subst; auto. exists φ. split;  auto.
    inversion H19; subst; auto. 
  + inversion H17; subst; auto.
    inversion H21; subst; auto. 
    assert (value e). auto. 
    apply  value_L_eq with v h1' h2' φ; auto.
    intuition. 
    
  + inversion H17; subst; auto.
    inversion H21; subst; auto.
    assert (value e). auto. 
    apply  value_L_eq with (ObjId o)  h1' h2' φ; auto. intuition.

  + inversion H17; subst; auto.
    inversion H21; subst; auto.
    assert (value e). auto. 
    apply  value_L_eq with (v_opa_l (ObjId o) ell) h1' h2' φ; auto.
    apply  v_opa_labeled; auto.  intros. intro contra; inversion contra.
    intuition.
   
- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  + inversion H17; subst; auto.
    exists φ. split;  auto.
    inversion H20; subst; auto.
    inversion H9; subst; auto. 
    
  + inversion H17; subst; auto.
    inversion H21; subst; auto.
    inversion H9; subst; auto. 
    assert (value hole). auto. 
    apply  value_L_eq with v1 h1' h2' φ; auto.
    inversion H0.

  + inversion   H17; subst; auto.
    inversion H21; subst; auto.
    inversion H9; subst; auto.
    inversion H11; subst; auto.
    inversion H12.


- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  + inversion H19; subst; auto.
    exists φ. split; auto.
    inversion H21; subst; auto.
    assert (value e). auto. 
    apply  value_L_eq2 with v h1' h2' φ; auto.
    intuition.

  + inversion H19; subst; auto.
    inversion H23; subst; auto.
    exists φ. split; auto.

  + inversion H19; subst; auto.
    inversion H23; subst; auto. 
    assert (value e2). auto. 
    apply  value_L_eq with v0 h1' h2' φ; auto.
    intuition.

  + inversion H19; subst; auto.
    inversion H23; subst; auto. 
    assert (value e2). auto. 
    apply  value_L_eq with v0 h1' h2' φ; auto.
    intuition.
     
    
- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  + inversion H18; subst; auto. 
    inversion H21; subst; auto.
    inversion H10; subst; auto.
    inversion H23; subst; auto.
    inversion H.
    
  + inversion H18; subst; auto.
    inversion H22; subst; auto.
    inversion H10; subst; auto.
    exists φ. split; auto.
    
  + inversion H18; subst; auto.
    inversion H22; subst; auto.
    inversion H10; subst; auto.
    inversion H14; subst; auto.
    inversion H13.
    case_eq (hole_free e2); intro ty; rewrite ty in H2; inversion H2.  
  
- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  + inversion H19; subst; auto.  
    inversion H21; subst; auto.

    assert (value e). apply value_L_eq2 with (ObjId o) h1' h2' φ; auto.
    contradiction.
  + inversion H19; subst; auto.   
    inversion H23; subst; auto.
    assert (value e2). apply value_L_eq2 with v h1' h2' φ; auto.
    contradiction.

  + inversion H19; subst; auto.
    inversion H23; subst; auto.
    inversion H13; subst; auto. 

    
    assert (cls = cls0).
    apply cls_def_eq with o o0 fields lo fields0 lo0 h1' h2'  φ; auto.
    subst; auto.
    rewrite <- H0 in H14; inversion H14; subst; auto. 


    ++ 
    exists  φ. split; auto.
    rewrite <- H5 in H; inversion H; subst; auto.
    rewrite <- H8 in H6; inversion H6; subst; auto.
    (* bijection.left φ o = Some o0 *)
    apply L_equivalence_config_L; auto.

    apply join_L_label_flow_to_L; auto.
    apply join_L_label_flow_to_L; auto. 
    apply L_eq_ctn; auto.
    apply join_L_label_flow_to_L; auto.
    apply join_L_label_flow_to_L; auto.
    apply surface_syntax_L_equal; auto.
    
    inversion H_typing1; subst; auto.

    inversion H12; subst; auto.
    inversion H29; subst; auto.
    inversion H26; subst; auto.
    destruct H43 as [F']. destruct H2 as [lo'].
    rewrite H2 in H5; inversion H5; subst; auto.
    rewrite <- H9 in H32; inversion H32; subst; auto.
    rewrite H33 in H0. inversion H0; subst; auto.

    apply  L_equivalence_store_L ; auto.
    inversion H25; subst; auto.
    destruct H2. 
        split; auto.
    intros. case_eq (beq_id arg_id x); intro.
    unfold sf_update in H9. rewrite H28 in H9. inversion H9. 
    unfold sf_update in H26. rewrite H28 in H26; inversion H26.
    subst; auto.     

    unfold sf_update in H9. rewrite H28 in H9. inversion H9. 
    
    split; auto; intros.

    apply sf_update_non_empty in H9. intuition. 
    apply sf_update_non_empty in H9. intuition. 

    ++
      exists  φ. split; auto.
      rewrite <- H4 in H; inversion H; subst; auto.
      rewrite <- H7 in H6; inversion H6; subst; auto.
    
      assert (flow_to (join_label lb0 lb1) L_Label = false).
      apply flow_join_label with lb0 lb1; auto.
      apply join_label_commutative.

      assert (flow_to (join_label lb3 lb2) L_Label = false).
      apply flow_join_label with lb3 lb2; auto.
      apply join_label_commutative.

      apply  L_equivalence_config_H; auto.
      unfold low_component; auto.
      rewrite H2. rewrite H3. fold low_component. 

      fold low_component.
      assert ((low_component ct (Container return_hole fs1 lb1 sf1)
                             ctns_stack1 h1') =
              Config ct (Container return_hole fs1 lb1 sf1) ctns_stack1 h1').
      apply low_component_with_L_Label; auto.
      rewrite H8.
      assert ((low_component ct (Container return_hole fs2 lb2 sf2)
                             ctns_stack2 h2') =
              Config ct (Container return_hole fs2 lb2 sf2) ctns_stack2 h2').
      apply low_component_with_L_Label; auto. rewrite H10. auto. 

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  + inversion H19; subst; auto. 
    inversion H21; subst; auto.
    assert (value e). apply value_L_eq2 with  (v_opa_l (ObjId o) ell) h1' h2' φ; auto.
    apply v_opa_labeled; auto. intros. intro contra; inversion contra. 
    contradiction.

  + inversion H19; subst; auto. 
    inversion H23; subst; auto.
    assert (value e2). apply value_L_eq2 with v h1' h2' φ; auto.
    contradiction.
    
  + inversion H19; subst; auto. 
    inversion H23; subst; auto.
    inversion H13; subst; auto.
    ++ 
      exists φ. split;  auto.
      inversion H27; subst; auto. 
      +++ assert (cls = cls0).
          apply cls_def_eq with o o0 fields lo fields0 lo0 h1' h2'  φ; auto.
          subst; auto.
          rewrite <- H0 in H14; inversion H14; subst; auto. 
          rewrite <- H5 in H; inversion H; subst; auto.
          rewrite <- H10 in H7; inversion H7; subst; auto. 
          apply L_equivalence_config_L; auto.    
          apply join_L_label_flow_to_L; auto.
          apply join_L_label_flow_to_L; auto. 

          apply join_L_label_flow_to_L; auto.
          apply join_L_label_flow_to_L; auto. 

          apply L_eq_ctn; auto.
          apply join_L_label_flow_to_L; auto.
          apply join_L_label_flow_to_L; auto.

          apply join_L_label_flow_to_L; auto.
          apply join_L_label_flow_to_L; auto. 

          apply surface_syntax_L_equal; auto.
          inversion H_typing1; subst; auto.

          inversion H29; subst; auto.
          inversion H33; subst; auto.
          inversion H30; subst; auto.          
          inversion H38; subst; auto.
          destruct H53 as [F']. destruct H2 as [lo'].
          rewrite H2 in H5; inversion H5; subst; auto.
          rewrite <- H36 in H44; inversion H44; subst; auto.
          rewrite H37 in H0; inversion H0; subst; auto.

          apply  L_equivalence_store_L ; auto.
          inversion H25; subst; auto.
          destruct H2. 
          split; auto.
          intros. case_eq (beq_id arg_id x); intro.
          unfold sf_update in H11. rewrite H32 in H11. inversion H11. 
          unfold sf_update in H30. rewrite H32 in H30; inversion H30.
          subst; auto.     

          unfold sf_update in H11. rewrite H32 in H11. inversion H11. 

          split; auto; intros.

          apply sf_update_non_empty in H11. intuition. 
          apply sf_update_non_empty in H11. intuition. 

      +++
        
        assert (flow_to (join_label lo (join_label lb1 ell0)) L_Label = false).
        apply flow_join_label with lo (join_label lb1 ell0); auto.
        rewrite <- H4 in H; inversion H; subst; auto.
        apply join_label_commutative.

        assert (flow_to (join_label lo0 (join_label lb2 ell0)) L_Label = false).
        apply flow_join_label with lo0 (join_label lb2 ell0); auto.
        rewrite <- H8 in H7; inversion H7; subst; auto.
        apply join_label_commutative.

        apply  L_equivalence_config_H; auto.
        unfold low_component; auto.
        rewrite H2. rewrite H3. fold low_component. fold low_component.
        assert ((low_component ct (Container return_hole fs1 lb1 sf1)
                             ctns_stack1 h1') =
          Config ct (Container return_hole fs1 lb1 sf1) ctns_stack1 h1').
        apply low_component_with_L_Label; auto.
        rewrite H10.
        assert ((low_component ct (Container return_hole fs2 lb2 sf2)
                             ctns_stack2 h2') =
          Config ct (Container return_hole fs2 lb2 sf2) ctns_stack2 h2').
        apply low_component_with_L_Label; auto.
        rewrite H28. auto.


    ++ assert (flow_to (join_label lo (join_label lb1 ell)) L_Label = false).
       apply flow_join_label with (join_label lb1 ell) lo; auto.
       eauto using flow_join_label.        

       assert (flow_to (join_label lo0 (join_label lb2 ell0)) L_Label = false).
       apply flow_join_label with  (join_label lb2 ell0) lo0; auto.
       eauto using flow_join_label.
       exists φ. split;  auto.

       apply  L_equivalence_config_H; auto.
       unfold low_component; auto.
       rewrite H2. rewrite H3. fold low_component. fold low_component.
        assert ((low_component ct (Container return_hole fs1 lb1 sf1)
                             ctns_stack1 h1') =
          Config ct (Container return_hole fs1 lb1 sf1) ctns_stack1 h1').
        apply low_component_with_L_Label; auto.
        rewrite H4.
        assert ((low_component ct (Container return_hole fs2 lb2 sf2)
                             ctns_stack2 h2') =
          Config ct (Container return_hole fs2 lb2 sf2) ctns_stack2 h2').
        apply low_component_with_L_Label; auto.
        rewrite H5. auto.

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

  + inversion H17; subst; auto.
    inversion H19; subst; auto.
    inversion H3; subst; auto; try (intuition). 
  + inversion H17; subst; auto.
    inversion H19; subst; auto.
    inversion H3; subst; auto; contradiction.
        

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  (*L_eq_container (Container t1 (unlabel hole :: fs) lb1 sf1) h1' (Container t2 fs2 lb2 sf2) h2 φ*)
  +
    inversion H17; subst; auto.  
    inversion H20; subst; auto.
    exists φ. split; auto.
  +
    inversion H17; subst; auto.
    inversion H21; subst; auto.
    inversion H9; subst; auto.
    inversion H1; subst; auto.
    inversion H12.

 - inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  (* L_eq_container (Container (unlabel (v_l v lo)) fs1 lb1 sf1) h1' (Container (unlabel e) fs2 lb2 sf2) h2' φ *)
  + inversion H17; subst; auto.  
    inversion H19; subst; auto.
    assert (value e).
    apply value_L_eq2 with (v_l v lo)  h1' h2'  φ; auto.
    intuition.
  + inversion H17; subst; auto.
    inversion H19; subst; auto.
    inversion H3; subst; auto.
    ++
      exists φ. split; auto.
      assert (flow_to (join_label lb1 lo0) L_Label = true).
      apply join_L_label_flow_to_L; auto.

      assert (flow_to (join_label lb2 lo0) L_Label = true).
      apply join_L_label_flow_to_L; auto. 
      apply L_equivalence_config_L; auto.

    ++
      exists φ. split; auto.
      assert (flow_to (join_label lb1 lo) L_Label = false).
      apply flow_join_label with lo lb1; auto.

      assert (flow_to (join_label lb2 lo0) L_Label = false).
      apply flow_join_label with lo0 lb2; auto.
      apply L_equivalence_config_H; auto.

      destruct ctns_stack1'; inversion H18; subst; auto.      
      unfold low_component; auto.
      rewrite H. rewrite H1.
      apply L_equivalence_config_L; auto.
      apply L_eq_ctn;auto.
      apply L_equivalence_store_L; auto.
      split; auto. intros. inversion H2. intuition.

      unfold low_component. rewrite H. rewrite H1. 
      fold low_component. auto. 

    
- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  (* L_eq_container (Container (unlabel (v_l v lo)) fs1 lb1 sf1) h1' (Container t2 fs2 lb2 sf2) h2 φ*)
  +
    inversion H17; subst; auto. 
    inversion H19; subst; auto.
    assert (value e).
    apply value_L_eq2 with (v_opa_l v ell)  h1' h2'  φ; auto.
    contradiction. 
  
  + inversion H17; subst; auto. 
    inversion H19; subst; auto.
    inversion H3; subst; auto.
    ++ 
      assert (flow_to (join_label lb1 ell0) L_Label = true).
      apply join_L_label_flow_to_L; auto.

      assert (flow_to (join_label lb2 ell0) L_Label = true).
      apply join_L_label_flow_to_L; auto. 
      exists φ.
      split; auto.

    ++
      assert (flow_to (join_label lb1 ell) L_Label = false). 
      apply flow_join_label with ell lb1; auto. 
      assert (flow_to (join_label lb2 ell0) L_Label = false). 
      apply flow_join_label with ell0 lb2; auto.

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
  + 
  inversion H17; subst; auto.   
  inversion H19; subst; auto.  exists φ. split;  auto.
  
  +
    inversion H17; subst; auto. 
    inversion H19; subst; auto.
    inversion H4; subst; auto; intuition.

  + inversion H17; subst; auto. 
    inversion H19; subst; auto.
    inversion H4; subst; auto; intuition.

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  (* L_eq_container (Container t1 (labelOf hole :: fs) lb1 sf1) h1' (Container t2 fs2 lb2 sf2) h2 φ*)
  + inversion H17; subst; auto.  
    inversion H20; subst; auto.
    exists φ. split;  auto.
  

  +
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
  (*L_eq_container (Container (labelOf (v_opa_l v ell)) fs1 lb1 sf1) h1' (Container t2 fs2 lb2 sf2) h2 φ*)
  inversion H17; subst; auto.  
  inversion H19; subst; auto.
  + 
    assert (value e).
    apply value_L_eq2 with (v_opa_l v ell)  h1' h2'  φ; auto.
    contradiction.

  + inversion H17; subst; auto.
    inversion H19; subst; auto.
    inversion H4; subst; auto.
    ++ 
      assert (flow_to (join_label lb1 ell0) L_Label = true).
      apply join_L_label_flow_to_L; auto.

      assert (flow_to (join_label lb2 ell0) L_Label = true).
      apply join_L_label_flow_to_L; auto. 
      exists φ.
      split; auto.

    ++
      assert (flow_to (join_label lb1 ell) L_Label = false). 
      apply flow_join_label with ell lb1; auto. 
      assert (flow_to (join_label lb2 ell0) L_Label = false). 
      apply flow_join_label with ell0 lb2; auto.

      exists φ. split; auto.
      
      inversion H18; subst; auto. 
      apply L_equivalence_config_H; auto. 
      unfold low_component. rewrite H0. rewrite H1. auto.
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
      rewrite H0.  rewrite H1. fold low_component.
      auto.

(* raise label *)
- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  + inversion H17; subst; auto. 
  inversion H19; subst; auto.
  exists φ. split; auto.

  + inversion H17; subst; auto.
    inversion H21; subst; auto.
    assert (value e).
    apply value_L_eq with (ObjId o) h1' h2 φ; auto.
    contradiction. 
  +
    inversion H17; subst; auto.
    inversion H21; subst; auto.
    assert (value e).
    apply value_L_eq with (v_opa_l (ObjId o) ell) h1' h2 φ; auto.
    apply v_opa_labeled; auto.
    intros. intro contra; inversion contra.
    contradiction.
   
(* raise label *)
- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  + inversion H17; subst; auto. 
  inversion H20; subst; auto.
  inversion H9; subst; auto. 
  exists φ. split; auto.

  +inversion H17; subst; auto.
  inversion H21; subst; auto.
  inversion H9; subst;auto.
  inversion H3; subst; auto.
  inversion H12.

(* L_eq_container (Container (raiseLabel (ObjId o) lo') fs1 lb1 sf1) h1
          (Container t2 fs2 lb2 sf2) h2 φ *)
- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  + inversion H19; subst; auto. 
    inversion H21; subst; auto.
    assert (value e).
    apply value_L_eq2 with (ObjId o) h1 h2' φ; auto.
    contradiction. 

  + inversion H19; subst; auto.
    inversion H23; subst; auto.

    case_eq (flow_to lo'0 L_Label).    
  (*lo'0 is low*)
  ++ exists φ. split; auto. 
    apply lbl_L_change_obj_both_lbl_preserve_bijection with ct lo lo0 lb1 lb2; auto. 
    inversion H_valid1; subst; auto.
    inversion H16; subst; auto.

    inversion H_valid2; subst; auto.
    inversion H35; subst; auto.    
    apply lbl_L_change_obj_both_lbl_preserve_l_eq_config with lo lo0; auto.

    
  ++ (*lo' is high*)
    intro.
    case_eq (flow_to lo L_Label); intro.
    +++
      assert (flow_to lo0 L_Label = true).
      inversion H10; subst; auto.
      ++++ 
        rewrite <- H12 in H6; inversion H6; subst; auto.
      ++++
        rewrite <- H7 in H; inversion H; subst; auto. try (inconsist).
      ++++
        inversion H10; subst; auto.
        assert (forall a1 a2 : oid, decision.Decision (a1 = a2)); auto.
        Require Import bijection. 
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
    +++
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
  (*L_eq_container (Container (raiseLabel (v_opa_l v ell) lo) fs1 lb1 sf1) h1' (Container (raiseLabel e lo0) fs2 lb2 sf2) h2' φ*)
  + inversion H19; subst; auto. 
    inversion H21; subst; auto.
    assert (value e).
    apply value_L_eq2 with (v_opa_l (ObjId o) ell) h1 h2' φ; auto.
    apply v_opa_labeled; auto.
    intros. intro contra; inversion contra.
    contradiction. 

  + inversion H19; subst; auto.
    inversion H23; subst; auto.

    case_eq (flow_to lo'0 L_Label).    
    (*lo'0 is low*)
    ++
      intro.
      assert (flow_to lb1 lo = true).
      assert (flow_to lb1 (join_label lb1 ell) = true); auto.
      eauto using join_def_flow1.
      apply flow_trans with (join_label lb1 ell); auto.

      assert (flow_to lb2 lo0 = true).
      assert (flow_to lb2 (join_label lb2 ell0) = true); auto.
      eauto using join_def_flow1.
      apply flow_trans with (join_label lb2 ell0); auto.  
      
      exists φ. split; auto.
      
      apply lbl_L_change_obj_both_lbl_preserve_bijection with ct lo lo0 lb1 lb2; auto.
      inversion H10; subst; auto.
      assert (flow_to  (join_label lb1 ell) L_Label = false).
      apply flow_join_label with ell lb1; auto.

      assert (flow_to lo L_Label = false).
      apply flow_transitive with  (join_label lb1 ell); auto.
      assert (flow_to lo'0 L_Label = false).
      apply flow_transitive with  lo; auto.
      try (inconsist_label).

      inversion H_valid1; subst; auto.
      inversion H27; subst; auto.

      inversion H_valid2; subst; auto.
      inversion H37; subst; auto.    
      apply lbl_L_change_obj_both_lbl_preserve_l_eq_config with lo lo0; auto.

      inversion H10; subst; auto.
      assert (flow_to  (join_label lb1 ell) L_Label = false).
      apply flow_join_label with ell lb1; auto.

      assert (flow_to lo L_Label = false).
      apply flow_transitive with  (join_label lb1 ell); auto.
      assert (flow_to lo'0 L_Label = false).
      apply flow_transitive with  lo; auto.
      try (inconsist_label).

    ++ (*lo' is high*)
    intro.
    case_eq (flow_to lo L_Label); intro.
    +++
      assert (flow_to lo0 L_Label = true).
      inversion H10; subst; auto.
      ++++
        inversion H28; subst; auto.
        rewrite <- H16 in H6; inversion H6; subst; auto.
        rewrite <- H7 in H; inversion H; subst; auto.
        try (inconsist_label).        
      ++++
        assert (flow_to  (join_label lb1 ell) L_Label = false).
        eauto using flow_join_label.
        assert (flow_to lo L_Label = false).
        apply flow_transitive with (join_label lb1 ell); auto.
        try (inconsist_label).

      ++++
        assert (forall a1 a2 : oid, decision.Decision (a1 = a2)); auto.
        Require Import bijection.
        inversion H10; subst; auto.
        +++++
          pose proof join_def_flow1 lb1 ell0.
          pose proof flow_trans lb1 (join_label lb1 ell0) lo H7 H0; auto. 

          pose proof join_def_flow1 lb2 ell0.
          pose proof flow_trans lb2 (join_label lb2 ell0) lo0 H9 H14; auto. 

          inversion H30; subst; auto.
          ++++++
          exists (reduce_bijection φ o o0 H28).
          split; auto.
          eauto using lbl_H_raise_obj_both_lbl_preserve_bijection. 

        
          inversion H_valid1; subst; auto.
          inversion H41; subst; auto.
          inversion H_valid2; subst; auto.
          inversion H51; subst; auto.    
          apply lbl_H_raise_obj_both_lbl_preserve_l_eq_config with φ lo lo0 H28; auto.
          ++++++
          rewrite <- H28 in H; inversion H; subst; auto.
          try (inconsist).
          +++++
            assert (flow_to  (join_label lb1 ell) L_Label = false).
          eauto using flow_join_label.
          assert (flow_to lo L_Label = false).
          apply flow_transitive with (join_label lb1 ell); auto.
          try (inconsist_label).            
    +++
      assert (flow_to lo0 L_Label = false).
      inversion H10; subst; auto.
      inversion H28; subst; auto. 
      rewrite <- H8 in H; inversion H; subst; auto.
      try (inconsist).

      rewrite <- H12 in H6; inversion H6; subst; auto.
      assert (flow_to  (join_label lb2 ell0) L_Label = false).
      eauto using flow_join_label.
      assert (flow_to lo0 L_Label = false).
      apply flow_transitive with (join_label lb2 ell0); auto.

      auto. 
      assert (flow_to lb1 lo = true).
      assert (flow_to lb1 (join_label lb1 ell) = true); auto.
      eauto using join_def_flow1.
      apply flow_trans with (join_label lb1 ell); auto.

      assert (flow_to lb2 lo0 = true).
      assert (flow_to lb2 (join_label lb2 ell0) = true); auto.
      eauto using join_def_flow1.
      apply flow_trans with (join_label lb2 ell0); auto.        
      
      exists φ. split; auto.
      assert (L_equivalence_tm (ObjId o) h1 (ObjId o0) h2 φ); auto.
      eauto using L_equivalence_tm_eq_object_H.
      assert (forall a1 a2 : oid, decision.Decision (a1 = a2)); auto.
      apply lbl_H_change_obj_both_lbl_preserve_bijection with ct lo lo0 lb1 lb2; auto.

      assert (forall a1 a2 : oid, decision.Decision (a1 = a2)); auto.
      inversion H_valid1; subst; auto.
      inversion H30; subst; auto.
      inversion H_valid2; subst; auto.
      inversion H40; subst; auto.    
      apply lbl_H_change_obj_both_lbl_preserve_l_eq_config  with lo lo0; auto. 
      eauto using L_equivalence_tm_eq_object_H.          
  
- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  (*L_eq_container (Container (Assignment id e) fs1 lb1 sf1) h1' (Container t2 fs2 lb2 sf2) h2 φ*)
  + inversion H17; subst; auto.
  inversion H19; subst; auto.
  exists φ. split; auto. 

  + inversion H17; subst; auto.
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
  +
    inversion H17; subst; auto.   
  inversion H19; subst; auto.
  exists φ. split;  auto.

  +
  inversion H17; subst; auto. 
  inversion H21; subst; auto.
  assert (value e). apply value_L_eq with  v h1' h2'  φ; auto.
  intuition.

  + inversion H17; subst; auto. 
  inversion H21; subst; auto.
  assert (value e). apply value_L_eq with  (ObjId o) h1' h2  φ; auto.
  intuition. 

  + inversion H17; subst; auto.
  inversion H21; subst; auto.
  assert (value e). apply value_L_eq with  (v_opa_l (ObjId o) ell)  h1' h2  φ; auto.
  apply v_opa_labeled; auto.
  intros. intro contra; inversion contra. 
  intuition. 
  
  
- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  (*L_eq_container (Container t1 (FieldWrite hole f e2 :: fs) lb1 sf1) h1' (Container t2 fs2 lb2 sf2) h2 φ*)
  + inversion H17; subst; auto.  
  inversion H20; subst; auto.
  inversion H9; subst; auto.
  exists φ. split;  auto.
  
  + inversion H17; subst; auto. 
  inversion H21; subst; auto.
  inversion H9; subst; auto.
  inversion H23; subst; auto.
  inversion H12.

  + inversion H17; subst; auto. 
  inversion H21; subst; auto.
  inversion H9; subst; auto.
  inversion H4; subst; auto.
  inversion H12. 

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  (*L_eq_container (Container (FieldWrite v f e2) fs1 lb1 sf1) h1' (Container t2 fs2 lb2 sf2) h2 φ*)
  + inversion H19; subst; auto. 
  inversion H21; subst; auto.  
  assert (value e). apply value_L_eq2 with v h1' h2' φ; auto.
  intuition.

  + inversion H19; subst; auto.
  inversion H23; subst; auto.
  exists φ. split; auto.

  + inversion H19; subst; auto.
    inversion H23; subst; auto.
    assert (value e2). apply value_L_eq with v0  h1' h2  φ; auto.
    intuition. 
  + inversion H19; subst; auto.
    inversion H23; subst; auto.
    assert (value e2). apply value_L_eq with v0  h1' h2  φ; auto.
    intuition.



    (*
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
     *)
    
- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  (*L_eq_container (Container t1 (FieldWrite v1 f hole :: fs) lb1 sf1) h1' (Container t2 fs2 lb2 sf2) h2 φ *)
  + inversion H18; subst; auto.  
  inversion H21; subst; auto.
  inversion H10; subst; auto.
  inversion H23; subst; auto.
  inversion H0.

  + inversion H18; subst; auto. 
  inversion H22; subst; auto.
  inversion H10; subst; auto.
  exists φ. split; auto.

  + inversion H18; subst; auto.  
  inversion H22; subst; auto.
  inversion H10; subst; auto.
  inversion H24; subst; auto.
  inversion H13.
  case_eq (hole_free e2); intro; rewrite H1 in H2; inversion H2.
  
- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  (*L_eq_container (Container (FieldWrite (ObjId o) f v) fs1 lb1 sf1) h1 (Container t2 fs2 lb2 sf2) h2 φ*)
  
  + inversion H19; subst; auto. 
  inversion H21; subst; auto.
  assert (value e). apply value_L_eq2 with (ObjId o) h1 h2'  φ; auto.
  contradiction.

  + inversion H19; subst; auto.
  inversion H23; subst; auto.
  assert (value e2). apply value_L_eq2 with v h1 h2'  φ; auto.
  contradiction.

  + inversion H19; subst; auto.
    inversion H23; subst; auto.







assert (FieldWrite (ObjId o) f0 v <> return_hole). intro contra; inversion contra.
pose proof config_typing_lead_to_tm_typing h1 ct (FieldWrite (ObjId o) f0 v) fs1 lb1 sf1 ctns_stack1' T  H_typing1 H0. destruct H2 as [Ty1]. destruct H2 as [gamma1].
inversion H2; subst; auto.
assert (FieldWrite (ObjId o0) f0 v0 <> return_hole). intro contra; inversion contra.
pose proof config_typing_lead_to_tm_typing h2 ct (FieldWrite (ObjId o0) f0 v0) fs2 lb2 sf2 ctns_stack2' T H_typing2 H4. destruct H5 as [Ty2]. destruct H5 as [gamma2].
inversion H5; subst; auto.

inversion H3; subst; auto; inversion H14; subst; auto.
inversion H21; subst; auto; inversion H32; subst; auto.
destruct H36 as [F1]. destruct H6 as [lo1].
destruct H39 as [F2]. destruct H9 as [lo2].
exists φ. split; auto.
apply update_field_preserve_bijection_new with ct L_Label L_Label lb1 lb2; auto.
unfold runtime_val. right.
exists o1.  exists cls_def1. exists F1. exists lo1.  split; auto.
unfold runtime_val. right.
exists o2.  exists cls_def2. exists F2. exists lo2.  split; auto.

unfold runtime_label in H1.
assert (join_label L_Label lb1 =join_label lb1 L_Label).
apply join_label_commutative. rewrite <- H30. auto. 

unfold runtime_label in H15.
assert (join_label L_Label lb2 =join_label lb2 L_Label).
apply join_label_commutative.
rewrite <- H30. auto. 
apply  L_equivalence_tm_eq_v_opa_l_L; auto.
unfold runtime_val.
apply v_opa_labeled; auto.
intros. intro contra; inversion contra.

unfold runtime_val.
apply v_opa_labeled; auto.
intros. intro contra; inversion contra. 


  inversion  H_valid1; subst;  auto.
  inversion H43; subst; auto.

  inversion  H_valid2; subst;  auto.
  inversion H53; subst; auto. 

  assert (forall a1 a2 : oid, decision.Decision (a1 = a2)). auto.
  
  apply L_equivalence_config_L; auto.
  apply update_field_preserve_L_eq_ctn with  ct lb1 L_Label lb2 L_Label; auto.
  assert (join_label L_Label lb1 =join_label lb1 L_Label).
  apply join_label_commutative. rewrite <- H31. auto. 

  assert (join_label L_Label lb2 =join_label lb2 L_Label).
  apply join_label_commutative.
  rewrite <- H31; auto.
  
  apply  L_equivalence_tm_eq_v_opa_l_L; auto.
  unfold runtime_val.
  apply v_opa_labeled; auto.
  intros. intro contra; inversion contra.

  unfold runtime_val.
  apply v_opa_labeled; auto.
  intros. intro contra; inversion contra. 

  apply update_field_preserve_L_eq_ctns  with  ct lb1 L_Label lb2 L_Label; auto.
  assert (join_label L_Label lb1 =join_label lb1 L_Label).
  apply join_label_commutative. rewrite <- H31. auto. 

  assert (join_label L_Label lb2 =join_label lb2 L_Label).
  apply join_label_commutative.
  rewrite <- H31; auto.

  apply  L_equivalence_tm_eq_v_opa_l_L; auto.
  unfold runtime_val.
  apply v_opa_labeled; auto.
  intros. intro contra; inversion contra.

  unfold runtime_val.
  apply v_opa_labeled; auto.
  intros. intro contra; inversion contra. 


    ++
      inversion H26.

    ++
      inversion H26.

    ++
      inversion H26; subst; auto.
      exists φ. split; auto.
      apply update_field_preserve_bijection_new with ct L_Label L_Label lb1 lb2; auto.
      assert (join_label L_Label lb1 =join_label lb1 L_Label).
      apply join_label_commutative. rewrite <- H6. auto. 

      assert (join_label L_Label lb2 =join_label lb2 L_Label).
      apply join_label_commutative.
      rewrite <- H6. auto.
      
      apply  L_equivalence_tm_eq_v_opa_l_L; auto.
      unfold runtime_val.
      apply v_opa_labeled; auto.
      intros. intro contra; inversion contra.

      unfold runtime_val.
      apply v_opa_labeled; auto.
      intros. intro contra; inversion contra. 

      inversion  H_valid1; subst;  auto.
      inversion H37; subst; auto.

      inversion  H_valid2; subst;  auto.
      inversion H47; subst; auto. 

      assert (forall a1 a2 : oid, decision.Decision (a1 = a2)). auto.
  
      apply L_equivalence_config_L; auto.
      apply update_field_preserve_L_eq_ctn with  ct lb1 L_Label lb2 L_Label; auto.
      assert (join_label L_Label lb1 =join_label lb1 L_Label).
      apply join_label_commutative. rewrite <- H9. auto. 

      assert (join_label L_Label lb2 =join_label lb2 L_Label).
      apply join_label_commutative.
      rewrite <- H9; auto.
  
      apply  L_equivalence_tm_eq_v_opa_l_L; auto.
      unfold runtime_val.
      apply v_opa_labeled; auto.
      intros. intro contra; inversion contra.

      unfold runtime_val.
      apply v_opa_labeled; auto.
      intros. intro contra; inversion contra. 

      apply update_field_preserve_L_eq_ctns  with  ct lb1 L_Label lb2 L_Label; auto.
      assert (join_label L_Label lb1 =join_label lb1 L_Label).
      apply join_label_commutative.
      rewrite <- H9. auto. 
      assert (join_label L_Label lb2 =join_label lb2 L_Label).
      apply join_label_commutative.
      rewrite <- H9; auto.

      apply  L_equivalence_tm_eq_v_opa_l_L; auto.
      unfold runtime_val.
      apply v_opa_labeled; auto.
      intros. intro contra; inversion contra.

      unfold runtime_val.
      apply v_opa_labeled; auto.
      intros. intro contra; inversion contra. 

    ++ inversion H26; subst; auto.
       unfold runtime_label in H1.
       unfold runtime_label in H15.

       assert (join_label lb lb1 =join_label lb1 lb).
       apply join_label_commutative. rewrite  H10 in H1. auto.

       assert (join_label lb lb2 =join_label lb2 lb).
       apply join_label_commutative. rewrite  H27 in H15. auto.
       
       +++ (* v_opa_l low label *)
         exists φ. split; auto.
         apply update_field_preserve_bijection_new with ct lb lb lb1 lb2; auto.
         ++++
           inversion H6; subst; auto; inversion H31; subst; auto.
           right. destruct H48 as [F1]. destruct H39 as [lo1].
           exists o1. exists cls_def1. exists F1. exists lo1.
           split; auto.
           destruct H40 with v lb0; auto.
           
         ++++
           inversion H6; subst; auto; inversion H31; subst; auto.
           right. destruct H48 as [F1]. destruct H39 as [lo1].
           inversion H44; subst; auto. 
           exists o3. exists cls2. exists F3. exists lb3.
           split; auto.

           exists o3. exists cls2. exists F3. exists lb3.
           split; auto.

           inversion H44;subst; auto.

           destruct H40 with v lb0; auto. 

         ++++
      inversion  H_valid1; subst;  auto.
      inversion H49; subst; auto.

      inversion  H_valid2; subst;  auto.
      inversion H59; subst; auto. 

      assert (forall a1 a2 : oid, decision.Decision (a1 = a2)). auto.
  
      apply L_equivalence_config_L; auto.
      apply update_field_preserve_L_eq_ctn with  ct lb1 lb lb2 lb; auto.
      apply update_field_preserve_L_eq_ctns  with  ct lb1 lb lb2 lb; auto.
       +++ (* v_opa_l hight label *)
          assert (join_label lb lb1 =join_label lb1 lb).
          apply join_label_commutative.
         
          assert (join_label l2 lb2 =join_label lb2 l2).
          apply join_label_commutative. 

          exists φ. split; auto.
          apply update_field_preserve_bijection_new with ct lb l2 lb1 lb2; auto.
         ++++
           inversion H6; subst; auto; inversion H31; subst; auto.
           right. destruct H48 as [F1]. destruct H39 as [lo1].
           exists o1. exists cls_def1. exists F1. exists lo1.
           split; auto.
           destruct H40 with v lb0; auto.           
         ++++
           inversion H32; subst; auto.
           inversion H48; subst; auto; inversion H43; subst; auto.
           destruct H52 as [F2].  destruct H39 as [lo2].
           right. exists o1. exists cls_def1. exists F2. exists lo2.
           split; auto.
           destruct H50 with v lb0; auto.

         ++++
           unfold runtime_label in H1. rewrite <- H10; auto.
         ++++
           unfold runtime_label in H15. rewrite <- H27; auto.
         ++++
           inversion  H_valid1; subst;  auto.
           inversion H49; subst; auto.
           inversion  H_valid2; subst;  auto.
           inversion H59; subst; auto.
           
           assert (forall a1 a2 : oid, decision.Decision (a1 = a2)). auto.
           apply L_equivalence_config_L; auto.
           apply update_field_preserve_L_eq_ctn with  ct lb1 lb lb2 l2; auto.

           assert (join_label lb1 lb =join_label lb lb1).
           apply join_label_commutative.
           rewrite H41. auto.
           unfold runtime_label in H1.

           assert (join_label lb2 l2 =join_label l2 lb2).
           apply join_label_commutative.
           rewrite H41. auto.
           unfold runtime_label in H15. 

           apply update_field_preserve_L_eq_ctns  with  ct lb1 lb lb2 l2; auto.
           assert (join_label lb1 lb =join_label lb lb1).
           apply join_label_commutative.
           rewrite H41. auto.

           assert (join_label lb2 l2 =join_label l2 lb2).
           apply join_label_commutative.
           rewrite H41. auto.
           
  
- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  (*L_eq_container (Container (FieldWrite (v_opa_l (ObjId o) ell) f v) fs1 lb1 sf1) h1
          (Container t2 fs2 lb2 sf2) h2 φ*)
  +  inversion H19; subst; auto.
     inversion H21; subst; auto.
     inversion H12; subst; auto.
     ++ 
       assert (value e0). apply value_L_eq2 with (ObjId o) h1 h2'  φ; auto.
       contradiction.
     ++
       assert (value e2). apply value_L_eq2 with v h1 h2'  φ; auto.
       contradiction.
  + inversion H19; subst; auto.
    inversion H23; subst; auto.
    assert (value e2). apply value_L_eq2 with v h1 h2'  φ; auto.
    contradiction.

  + inversion H19; subst; auto.
    inversion H23; subst; auto.
    assert ((FieldWrite (v_opa_l (ObjId o) ell) f0 v) <> return_hole). intro contra; inversion contra.
    pose proof config_typing_lead_to_tm_typing h1 ct (FieldWrite (v_opa_l (ObjId o) ell) f0 v) fs1 lb1 sf1 ctns_stack1' T  H_typing1 H0. destruct H1 as [Ty1]. destruct H1 as [gamma1].
    inversion H1; subst; auto.
    assert ((FieldWrite (v_opa_l (ObjId o0) ell0) f0 v0) <> return_hole). intro contra; inversion contra.
    pose proof config_typing_lead_to_tm_typing h2 ct (FieldWrite (v_opa_l (ObjId o0) ell0) f0 v0) fs2 lb2 sf2 ctns_stack2' T H_typing2 H3.
    destruct H5 as [Ty2]. destruct H5 as [gamma2].
    inversion H5; subst; auto.

    inversion H4; subst; auto; inversion H14; subst; auto.
    ++
    inversion H22; subst; auto; inversion H32; subst; auto.
    +++
      unfold runtime_label in H2. assert (join_label L_Label lb1 = join_label lb1 L_Label).
      apply join_label_commutative.
      pose proof join_L_Label_irrelevant lb1.
      pose proof join_L_Label_irrelevant lb2.
      rewrite H6 in H2. rewrite H9 in H2.
      assert (join_label L_Label lb2 = join_label lb2 L_Label).
      apply join_label_commutative.
      unfold runtime_label in H16. 
      rewrite H31 in H16. rewrite H30 in H16.
      
      destruct H36 as [F1]. destruct H36 as [lo1].
      destruct H39 as [F2]. destruct H37 as [lo2].
      exists φ. split; auto.   
      apply update_field_preserve_bijection_new with ct L_Label L_Label lb1 lb2; auto.
      unfold runtime_val. right.
      exists o1.  exists cls_def1. exists F1. exists lo1.  split; auto.
      unfold runtime_val. right.

      exists o2.  exists cls_def2. exists F2. exists lo2.  split; auto.

      rewrite H9. auto.
      pose proof join_def_flow1 lb1 ell.
      apply flow_trans with ((join_label lb1 ell)); auto.

      rewrite H30.
      pose proof join_def_flow1 lb2 ell0.
      apply flow_trans with ((join_label lb2 ell0)); auto.

      inversion H12; subst; auto.
      assert (flow_to lo L_Label = false).
      apply flow_transitive with (join_label lb1 ell); auto.
      apply flow_transitive with ell; auto.
      apply join_def_flow2.

      assert (flow_to lo0 L_Label = false).
      apply flow_transitive with (join_label lb2 ell0); auto.
      apply flow_transitive with ell0; auto.
      apply join_def_flow2. 

      apply  L_equivalence_tm_eq_object_H with cls  cls0   F lo  F0 lo0 ; auto.         

      unfold runtime_val.
      apply  L_equivalence_tm_eq_v_opa_l_L; auto.
      apply v_opa_labeled; auto.
      intros. intro contra; inversion contra.

      apply v_opa_labeled; auto.
      intros. intro contra; inversion contra.

      inversion  H_valid1; subst;  auto.
      inversion H47; subst; auto.
      inversion  H_valid2; subst;  auto.
      inversion H57; subst; auto. 
        
      assert (forall a1 a2 : oid, decision.Decision (a1 = a2)). auto.
      apply L_equivalence_config_L; auto.
      apply update_field_preserve_L_eq_ctn with  ct lb1 L_Label lb2 L_Label; auto.
      rewrite H9. pose proof join_def_flow1 lb1 ell.
      apply flow_trans with (join_label lb1 ell); auto. 

      rewrite H30; auto.
      pose proof join_def_flow1 lb2 ell0.
      apply flow_trans with (join_label lb2 ell0); auto. 

      inversion H12; subst; auto.
      assert (flow_to lo L_Label = false).
      apply flow_transitive with (join_label lb1 ell); auto.
      apply flow_transitive with ell; auto.
      apply join_def_flow2.

      assert (flow_to lo0 L_Label = false).
      apply flow_transitive with (join_label lb2 ell0); auto.
      apply flow_transitive with ell0; auto.
      apply join_def_flow2. 

      apply  L_equivalence_tm_eq_object_H with cls  cls0   F lo  F0 lo0 ; auto.         

      apply  L_equivalence_tm_eq_v_opa_l_L; auto.
      unfold runtime_val.
      apply v_opa_labeled; auto.
      intros. intro contra; inversion contra.

      unfold runtime_val.
      apply v_opa_labeled; auto.
      intros. intro contra; inversion contra. 

      apply update_field_preserve_L_eq_ctns  with  ct lb1 L_Label lb2 L_Label; auto.
      rewrite H9. pose proof join_def_flow1 lb1 ell.
      apply flow_trans with (join_label lb1 ell); auto. 
      rewrite H30; auto.
      pose proof join_def_flow1 lb2 ell0.
      apply flow_trans with (join_label lb2 ell0); auto. 

      inversion H12; subst; auto.
      assert (flow_to lo L_Label = false).
      apply flow_transitive with (join_label lb1 ell); auto.
      apply flow_transitive with ell; auto.
      apply join_def_flow2.

      assert (flow_to lo0 L_Label = false).
      apply flow_transitive with (join_label lb2 ell0); auto.
      apply flow_transitive with ell0; auto.
      apply join_def_flow2. 

      apply  L_equivalence_tm_eq_object_H with cls  cls0   F lo  F0 lo0 ; auto.         
      apply  L_equivalence_tm_eq_v_opa_l_L; auto.
      unfold runtime_val.
      apply v_opa_labeled; auto.
      intros. intro contra; inversion contra.

      unfold runtime_val.
      apply v_opa_labeled; auto.
      intros. intro contra; inversion contra. 
    +++
      inversion H26.
    +++
      inversion H26.

    ++
      pose proof join_L_Label_irrelevant lb1.
      pose proof join_L_Label_irrelevant lb2.      
      inversion H26; subst; auto.
      exists φ. split; auto.
      apply update_field_preserve_bijection_new with ct L_Label L_Label lb1 lb2; auto.
      assert (join_label L_Label lb1 =join_label lb1 L_Label).
      apply join_label_commutative.
      rewrite <- H10.
      unfold runtime_label in H2. auto.
      apply flow_trans with (join_label (join_label L_Label lb1) ell); auto.
      apply join_def_flow1.

      assert (join_label L_Label lb2 =join_label lb2 L_Label).
      apply join_label_commutative.
      rewrite <- H10.
      unfold runtime_label in H16. auto.
      apply flow_trans with (join_label (join_label L_Label lb2) ell0); auto.
      apply join_def_flow1.

      inversion H12; subst; auto.
      assert (flow_to lo L_Label = false).
      apply flow_transitive with (join_label (join_label (runtime_label null) lb1) ell); auto.
      apply flow_transitive with ell; auto.
      apply join_def_flow2. 

      assert (flow_to lo0 L_Label = false).
      apply flow_transitive with (join_label (join_label (runtime_label null) lb2) ell0); auto.
      apply flow_transitive with ell0; auto.
      apply join_def_flow2. 

      apply  L_equivalence_tm_eq_object_H with cls  cls0   F lo  F0 lo0 ; auto.         

      apply  L_equivalence_tm_eq_v_opa_l_L; auto.
      unfold runtime_val.
      apply v_opa_labeled; auto.
      intros. intro contra; inversion contra.

      unfold runtime_val.
      apply v_opa_labeled; auto.
      intros. intro contra; inversion contra.

      inversion H_valid1; subst; auto.
      inversion H39; subst; auto. 
      inversion H_valid2; subst; auto.
      inversion H49; subst; auto.

      assert (join_label L_Label lb1 =join_label lb1 L_Label).
      apply join_label_commutative.
      assert (flow_to (join_label lb1 L_Label) lo = true).
      rewrite <- H10.
      unfold runtime_label in H2. auto.
      apply flow_trans with (join_label (join_label L_Label lb1) ell); auto.
      apply join_def_flow1.

      assert (join_label L_Label lb2 =join_label lb2 L_Label).
      apply join_label_commutative.
      assert (flow_to (join_label lb2 L_Label) lo0 = true).
      rewrite <- H30.
      unfold runtime_label in H16. auto.
      apply flow_trans with (join_label (join_label L_Label lb2) ell0); auto.
      apply join_def_flow1.

      assert (forall a1 a2 : oid, decision.Decision (a1 = a2)). auto.  
      apply L_equivalence_config_L; auto.
      
      apply update_field_preserve_L_eq_ctn with  ct lb1 L_Label lb2 L_Label; auto.
      
      inversion H12; subst; auto.
      assert (flow_to lo L_Label = false).
      apply flow_transitive with (join_label (join_label (runtime_label null) lb1) ell); auto.
      apply flow_transitive with ell; auto.
      apply join_def_flow2. 

      assert (flow_to lo0 L_Label = false).
      apply flow_transitive with (join_label (join_label (runtime_label null) lb2) ell0); auto.
      apply flow_transitive with ell0; auto.
      apply join_def_flow2. 

      apply  L_equivalence_tm_eq_object_H with cls  cls0   F lo  F0 lo0 ; auto.  
      apply  L_equivalence_tm_eq_v_opa_l_L; auto.
      unfold runtime_val.
      apply v_opa_labeled; auto.
      intros. intro contra; inversion contra.

      unfold runtime_val.
      apply v_opa_labeled; auto.
      intros. intro contra; inversion contra.
      
      apply update_field_preserve_L_eq_ctns  with  ct lb1 L_Label lb2 L_Label; auto.
      inversion H12; subst; auto.
      assert (flow_to lo L_Label = false).
      apply flow_transitive with (join_label (join_label (runtime_label null) lb1) ell); auto.
      apply flow_transitive with ell; auto.
      apply join_def_flow2. 

      assert (flow_to lo0 L_Label = false).
      apply flow_transitive with (join_label (join_label (runtime_label null) lb2) ell0); auto.
      apply flow_transitive with ell0; auto.
      apply join_def_flow2. 

      apply  L_equivalence_tm_eq_object_H with cls  cls0   F lo  F0 lo0 ; auto.  
      apply  L_equivalence_tm_eq_v_opa_l_L; auto.
      unfold runtime_val.
      apply v_opa_labeled; auto.
      intros. intro contra; inversion contra.

      unfold runtime_val.
      apply v_opa_labeled; auto.
      intros. intro contra; inversion contra.
      

    ++
      inversion H22; subst; auto; inversion H32; subst; auto.
      +++
        inversion H26.
      +++
        inversion H26.
      +++
        unfold runtime_label in H2. unfold runtime_label in H16.
        unfold runtime_val.
        assert (join_label lb1 lb =join_label lb lb1).
        apply join_label_commutative.
        assert (flow_to (join_label lb1 lb) lo = true). rewrite H33. 
        apply flow_trans with (join_label (join_label lb lb1) ell); auto.
        apply join_def_flow1.

        assert (join_label lb2 lb0 =join_label lb0 lb2).
        apply join_label_commutative.
        assert (flow_to (join_label lb2 lb0) lo0 = true). rewrite H41. 
        apply flow_trans with (join_label (join_label lb0 lb2) ell0); auto.
        apply join_def_flow1.

        inversion H12; subst; auto.
        ++++
          exists φ. split; auto.
        +++++
          apply update_field_preserve_bijection_new with ct lb lb0 lb1 lb2; auto.
        inversion H6; subst; inversion H31; subst; auto.
        right. destruct H56 as [F']. destruct H43 as [lo'].
        exists o1. exists cls_def1. exists F'. exists lo'. split; auto.
        destruct H40 with v0 lb3; auto. 

        inversion H44; subst; inversion H39; subst; auto.
        right. destruct H56 as [F']. destruct H43 as [lo'].
        exists o1. exists cls_def1. exists F'. exists lo'. split; auto.
        destruct H27 with v0 lb3; auto.
        +++++
          assert (forall a1 a2 : oid, decision.Decision (a1 = a2)). auto.  
          inversion H_valid1; subst; auto.
          inversion H58; subst; auto.
          inversion H_valid2; subst; auto.
          inversion H68; subst; auto.
          apply L_equivalence_config_L; auto.
          apply update_field_preserve_L_eq_ctn with  ct lb1 lb lb2 lb0; auto.
          apply update_field_preserve_L_eq_ctns  with  ct lb1 lb lb2 lb0; auto.

        ++++
          assert (flow_to lo L_Label = false).
          apply flow_transitive with (join_label (join_label lb lb1) ell); auto.
          apply flow_transitive with ell; auto.
          apply join_def_flow2. 

          assert (flow_to lo0 L_Label = false).
          apply flow_transitive with (join_label (join_label lb0 lb2) ell0); auto.
          apply flow_transitive with ell0; auto.
          apply join_def_flow2. 
          exists φ. split; auto.
          +++++
          apply update_field_preserve_bijection_new with ct lb lb0 lb1 lb2; auto.
          inversion H6; subst; inversion H31; subst; auto.
          right. destruct H58 as [F']. destruct H47 as [lo'].
          exists o1. exists cls_def1. exists F'. exists lo'. split; auto.
          destruct H40 with v0 lb3; auto. 

          inversion H44; subst; inversion H39; subst; auto.
          right. destruct H58 as [F']. destruct H47 as [lo'].
          exists o1. exists cls_def1. exists F'. exists lo'. split; auto.
          destruct H27 with v0 lb3; auto.
          apply  L_equivalence_tm_eq_object_H with cls  cls0   F lo  F0 lo0 ; auto.  
          +++++
          assert (forall a1 a2 : oid, decision.Decision (a1 = a2)). auto.  
          inversion H_valid1; subst; auto.
          inversion H60; subst; auto.
          inversion H_valid2; subst; auto.
          inversion H70; subst; auto.
          apply L_equivalence_config_L; auto.
          apply update_field_preserve_L_eq_ctn with  ct lb1 lb lb2 lb0; auto.
          apply  L_equivalence_tm_eq_object_H with cls  cls0   F lo  F0 lo0 ; auto.  
          apply update_field_preserve_L_eq_ctns  with  ct lb1 lb lb2 lb0; auto.
          apply  L_equivalence_tm_eq_object_H with cls  cls0   F lo  F0 lo0 ; auto.  
          

  
- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  (* L_eq_container (Container (If guard s1 s2) fs1 lb1 sf1) h1' (Container t2 fs2 lb2 sf2) h2 φ*)
  + inversion H17; subst; auto. 
  inversion H19; subst; auto.
  exists φ. split;  auto.
  
  + inversion H17; subst; auto. 
    inversion H19; subst; auto.
    assert (value guard).
    apply value_L_eq with (v_opa_l guard0 ell) h1' h2' φ; auto.
    contradiction.

  + 
    inversion H17; subst; auto. 
    inversion H14; subst; auto. 
    inversion H10; subst; auto.
    intuition.

  + inversion H17; subst; auto. 
    inversion H14; subst; auto. 
    inversion H10; subst; auto.
    intuition. 

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  + inversion H17; subst; auto.
  inversion H20; subst; auto.
  inversion H9; subst; auto.
  exists φ. split; auto.

  
  + inversion H17; subst; auto.
  inversion H21; subst; auto.  
  inversion H9; subst; auto.
  inversion H4; subst; auto.
  inversion H12. 

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  + inversion H17; subst; auto.
    inversion H19; subst; auto.

    assert (value guard0).
    apply value_L_eq2 with (v_opa_l guard ell) h1' h2' φ; auto.
    contradiction.

  + inversion H17; subst; auto. 
    inversion H19; subst; auto.
    inversion H11; subst; auto.
    exists φ. split; auto.
    ++
      assert (flow_to (join_label lb1 ell0) L_Label = true).
      apply join_L_label_flow_to_L; auto. 
      apply L_Label_flow_to_L in H0.
      rewrite H0.

      assert (flow_to (join_label lb2 ell0) L_Label = true).
      apply join_L_label_flow_to_L; auto.
      apply L_Label_flow_to_L in H2. 
      rewrite H2. 

      apply  L_equivalence_config_L; auto.
    ++
      exists φ. split; auto.
      assert (flow_to (join_label lb1 ell) L_Label = false).
      apply flow_transitive with ell; auto.
      apply join_def_flow2; auto.

      assert (flow_to (join_label lb2 ell0) L_Label = false).
      apply flow_transitive with ell0; auto.
      apply join_def_flow2; auto. 
      apply  L_equivalence_config_H; auto.

      inversion H18; subst; auto.
      +++ unfold low_component; auto. rewrite H0. rewrite H2. auto.
          apply L_equivalence_config_L; auto.
          apply L_eq_ctn; auto.
          apply  L_equivalence_store_L; auto.
          split; auto.
          intros; auto. inversion H3.
          intuition.
      +++
        induction ctn1. induction ctn2. 
        unfold low_component. rewrite H0. rewrite H2. auto.

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  +
    inversion H16; subst; auto.
    inversion H18; subst; auto.
    inversion H10; subst; auto. intuition. 

  +
    inversion H16; subst; auto.
    inversion H13; subst; auto. 
    exists φ. auto.

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  + 
    inversion H16; subst; auto.  
    inversion H18; subst; auto.
    inversion H10; subst; auto.
    intuition.

  +
    inversion H16;subst; auto.
    inversion H13; subst; auto. 
    exists φ. split; auto.


- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  inversion H16; subst; auto.
  inversion H13; subst; auto.
  exists φ. split; auto.

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  (*  L_eq_container (Container Skip (e :: fs) lb1 sf1) h1' (Container Skip (e0 :: fs0) lb2 sf2) h2' φ *)
  inversion H16; subst; auto.
  inversion H18; subst; auto. 
  exists φ. split; auto. 


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

  +  inversion H18; subst; auto.
     inversion H21; subst; auto.
     inversion H10; subst; auto.
     inversion H6; subst; auto.
     inversion H0; subst; auto.

  +  inversion H18; subst; auto.
     inversion H21; subst; auto.
     inversion H10; subst; auto.
     inversion H5; subst; auto.
     inversion H0; subst; auto.

  +  inversion H18; subst; auto.
     inversion H21; subst; auto.
     inversion H10; subst; auto.
     inversion H5; subst; auto.
     inversion H0; subst; auto. 
     
  + inversion H18; subst; auto.
    inversion H21; subst; auto.
    inversion H10; subst; auto.
    inversion H6; subst; auto.
    inversion H0. 
    
  +  inversion H18; subst; auto.
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
  inversion H21; subst; auto.
  inversion H10; subst; auto.
  inversion H7; subst; auto.
  inversion H0.
    
  + inversion H18; subst; auto.
    inversion H22; subst; auto.
    exists φ.  split; auto.

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  + inversion H19; subst; auto.
    inversion H18; subst; auto.
    inversion H10; subst; auto. 
     exists φ. split; auto. 
     apply  L_equivalence_config_L; auto.
     apply L_eq_ctn; auto.
     apply  L_Label_flow_to_L in H21.
     apply  L_Label_flow_to_L in H22.
     subst; auto. 
     apply L_equivalence_tm_eq_v_opa_l_L; auto.

     apply v_opa_labeled; auto. intros.
     intro contra; subst; auto. 
     destruct H0 with v0 lb0; auto. inversion H; subst; auto.

     apply v_opa_labeled; auto. intros.
     intro contra; subst; auto. 
     destruct H13 with v0 lb0; auto.
     inversion H3; subst; auto. 

  + inversion H18; subst; auto.
    inversion H15; subst; auto.
    ++ destruct H0 with e1 ell; auto.
       inversion H4; auto. 
    ++ destruct H0 with e1 l1; auto.
       inversion H7; auto. 

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  + inversion H16; subst; auto.
    inversion H19; subst; auto.
    ++ destruct H11 with e2 ell; auto.
       inversion H4; subst; auto. 
    ++ destruct H11 with e2 l2; auto.
       inversion H10; subst; auto.

  + inversion H17; subst; auto.
    inversion H16; subst; auto.
    inversion H6; subst; auto. 
    inversion H19; subst; auto.
    ++ exists φ. split; auto. 
       apply  L_equivalence_config_L; auto.
       apply L_eq_ctn; auto.
       assert (flow_to (join_label ell0 lb1) L_Label = true).
       apply join_L_label_flow_to_L; auto. 
       apply L_Label_flow_to_L in H.
       
       assert (flow_to (join_label ell0 lb2) L_Label = true).
       apply join_L_label_flow_to_L; auto. 
       apply L_Label_flow_to_L in H0.
       subst; auto. rewrite H. rewrite H0. 
       apply L_equivalence_tm_eq_v_opa_l_L; auto.
       inversion H5; subst; auto.
       inversion H11; subst; auto.
       
    ++ exists φ. split; auto. 
       apply  L_equivalence_config_L; auto.
       apply L_eq_ctn; auto.
       assert (flow_to (join_label ell lb1) L_Label = false).
       apply flow_transitive with ell; auto.
       apply join_def_flow1; auto.

       assert (flow_to (join_label ell0 lb2) L_Label = false).
       apply flow_transitive with ell0; auto.
       apply join_def_flow1; auto. 

       apply L_equivalence_tm_eq_v_opa_l_H; auto.
       inversion H11; subst; auto.
       inversion H12; subst; auto.

 Qed.
Hint Resolve simulation_L.
 