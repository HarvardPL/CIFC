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
  inversion H16; subst; auto.
  inversion H18; subst; auto.
  inversion H13; subst; auto.
  destruct H0.
  exists φ. split; auto.
  apply L_equivalence_config_L; auto.
  apply L_eq_ctn; auto.
  apply H0 with id0; auto.
  inversion H_valid1; subst; auto.  
  inversion H19; subst; auto.
  inversion H26; subst; auto.
  assert (sf1 id0 = Some v); auto. 
  apply H3 in H4. apply H4. 

  inversion H_valid2; subst; auto.
  inversion H19; subst; auto.
  inversion H26; subst; auto.
  assert (sf2 id0 = Some v0); auto. 
  apply H3 in H4. apply H4. 

Ltac invert_l_eq_ctn :=
       match goal with
       | H : L_eq_container _ _ _ _ _ |- _ => inversion H; subst; auto
       end. 

Ltac invert_l_eq_tm :=
       match goal with
       | H : L_equivalence_tm _ _ _ _ _ |- _ => inversion H; subst; auto
       end.

Ltac invert_l_eq_fs :=
       match goal with
       | H : L_equivalence_fs _ _ _ _ _ |- _ => inversion H; subst; auto
       end. 

(*EqCmp*)
- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  + invert_l_eq_ctn. 
    exists φ. split;  auto.
    invert_l_eq_tm.
  + invert_l_eq_ctn.
    invert_l_eq_tm.
    assert (value e1). auto.
    eauto using value_L_eq. 
    intuition.
  + invert_l_eq_ctn. 
    invert_l_eq_tm.
    assert (value e1). auto. 
    apply  value_L_eq with v1 h1' h2' φ; auto. intuition.
  
- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
(* + try (invert_l_eq_ctn; exists φ; split;  auto; invert_l_eq_tm ). *)
  + invert_l_eq_ctn. 
    exists φ. split;  auto.
    invert_l_eq_fs.
    invert_l_eq_tm.
  + invert_l_eq_ctn.
    invert_l_eq_fs.
    invert_l_eq_tm.
    Ltac invert_l_eq_tm_hole :=
       match goal with
       | H : L_equivalence_tm hole _ _ _ _ |- _ => inversion H; subst; auto
       | H1 : L_equivalence_tm _ _ hole _ _ |- _ => inversion H1; subst; auto                                        
       end.
    Ltac invert_value_hole :=
       match goal with
       | H : value hole |- _ => inversion H; subst; auto                                  
       end.
    invert_l_eq_tm_hole.
    invert_value_hole.
  + invert_l_eq_ctn.
    invert_l_eq_fs.
    inversion H9; subst; auto. 
    invert_l_eq_tm_hole.
    Ltac invert_hole_free :=
       match goal with
       | H : hole_free _ = true |- _ => inversion H; subst; auto                                  
       end.
    invert_hole_free.

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  +  invert_l_eq_ctn.
     invert_l_eq_tm.
     assert (value e1). apply value_L_eq2 with v h1' h2' φ; auto.
     intuition. 
  + invert_l_eq_ctn.
    invert_l_eq_tm.
    exists φ. split;  auto.
  + invert_l_eq_ctn.
    invert_l_eq_tm.
    assert (value e2). apply value_L_eq with v2 h1' h2' φ; auto.
    intuition.

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  + invert_l_eq_ctn.
    invert_l_eq_fs.
    invert_l_eq_tm.
    inversion H12; subst; auto.
    invert_value_hole.

  + invert_l_eq_ctn.
    invert_l_eq_fs.
    invert_l_eq_tm.
    exists φ. split;  auto.
  + invert_l_eq_ctn.
    invert_l_eq_fs.
    invert_l_eq_tm.
    invert_l_eq_tm_hole.
    invert_hole_free.
    case_eq (hole_free e2); intro He2; rewrite He2 in H2;  intuition. 

(* EqCmp evaluate to boolean *)    
- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  + invert_l_eq_ctn.
    invert_l_eq_tm.
    assert (value e1). apply value_L_eq2 with v1 h1' h2' φ; auto.
    intuition.
  + invert_l_eq_ctn.
    invert_l_eq_tm.
    assert (value e2). apply value_L_eq2 with v2 h1' h2' φ; auto.
    intuition.
  + invert_l_eq_ctn.
    invert_l_eq_tm.    
    exists  φ; split; auto.

    pose proof (exclude_middle_runtime_val v1 v2 H H0).
    assert (EqCmp v1 v2 <> return_hole). intro contra; inversion contra. 
    pose proof config_typing_lead_to_tm_typing h1' ct  (EqCmp v1 v2) fs1 lb2 sf1 ctns_stack1' T H_typing1 H4.
    destruct H5 as [Ttm]. destruct H5 as [gamma]. inversion H5; subst; auto.

    inversion H; subst; auto; inversion H8; subst; auto.
    (* v = ObjId o*)
    ++
      inversion H10; subst; auto.
      +++
        (* two objects are with low labels and low_eq *)
        inversion H0; subst; auto; inversion H26; subst; auto.
        ++++
          unfold runtime_val in H3. (* inversion H3; subst; auto. *)
          inversion H12; subst; auto.
          unfold runtime_label. unfold runtime_val. unfold object_label. rewrite <- H13.
          rewrite <- H27. rewrite <- H33. rewrite <- H35.
          remember ((join_label
             (join_label (join_label L_Label L_Label) lb2)
             (join_label ll ll0))) as lb''.
          case_eq (flow_to lb'' L_Label); intro. 
          apply L_equivalence_config_L; auto.          
          apply L_eq_ctn;auto.
          
          destruct H3.
          inversion H3; subst; auto.
          rewrite H7 in H31; inversion H31; subst; auto. 
          assert (result0 = B_true). auto.
          assert (result = B_true). auto.
          rewrite H38. rewrite H39. auto. 
          
          unfold runtime_val in H2. unfold runtime_val in H17.
          assert (ObjId o2 <> ObjId o3). intro contra; inversion contra.
          subst; auto. apply bijection.right_left in H7.
          apply bijection.right_left in H31. 
          rewrite H31 in H7; inversion H7; subst; auto. 
          assert (result = B_false). auto.
          assert (result0 = B_false). auto.
          subst; auto.
          apply L_equivalence_config_H; auto.

           unfold runtime_label. unfold runtime_val. unfold object_label. rewrite <- H13.
           rewrite <- H27. rewrite <- H31. rewrite <- H33.
           assert (flow_to (join_label (join_label (join_label L_Label L_Label) lb2) (join_label ll ll1))  L_Label = false).
           apply flow_transitive with ll1; auto.
           apply flow_trans with (join_label ll ll1); auto.
           apply join_def_flow2.
           apply join_def_flow2.

           assert (flow_to (join_label (join_label (join_label L_Label L_Label) lb2) (join_label ll ll2))  L_Label = false).
           apply flow_transitive with ll2; auto.
           apply flow_trans with (join_label ll ll2); auto. 
           apply join_def_flow2.
           apply join_def_flow2.
           
           apply L_equivalence_config_H; auto.

        ++++
          inversion H12; subst; auto.
          unfold runtime_label. unfold runtime_val. unfold object_label. rewrite <- H13.
          rewrite <- H27.
          remember (join_label (join_label (join_label L_Label L_Label) lb2) (join_label ll L_Label)) as lb''.
          case_eq (flow_to lb'' L_Label); intro. 
          apply L_equivalence_config_L; auto.          
          apply L_eq_ctn;auto.
          
          destruct H3.
          inversion H3; subst; auto.
          unfold runtime_val in H2. unfold runtime_val in H17.
          assert (result0 = B_false). apply H17.
          intro contra; inversion contra. 

          assert (result = B_false). apply H2. auto.
          rewrite H31. rewrite H32. auto.
          subst; auto.

        ++++
          inversion H12; subst; auto.
             +++++
               inversion H6; subst; auto; inversion H35; subst; auto.
             ++++++
               inversion H45; subst; auto.
             +++++++
               unfold runtime_label.
             unfold runtime_val. unfold object_label. rewrite <- H13. rewrite <- H27.              
             rewrite <- H42.             rewrite <- H44.
             remember(join_label (join_label (join_label L_Label lb) lb2) (join_label ll ll0))  as lb''.

             case_eq (flow_to lb'' L_Label); intro. 
             apply L_equivalence_config_L; auto.          
             apply L_eq_ctn;auto.
          
             destruct H3.
             * 
               inversion H3; subst; auto.
               rewrite H7 in H33; inversion H33; subst; auto. 
               assert (result0 = B_true). auto.
               assert (result = B_true). auto.
               rewrite H48. rewrite H49. auto. 
             *          
               unfold runtime_val in H2. unfold runtime_val in H17.
               assert (ObjId o2 <> ObjId o3). intro contra; inversion contra.
               subst; auto. apply bijection.right_left in H7.
               apply bijection.right_left in H33. 
               rewrite H33 in H7; inversion H7; subst; auto. 
               assert (result = B_false). auto.
               assert (result0 = B_false). auto.
               subst; auto.
             *
               apply L_equivalence_config_H; auto.
               +++++++
                 unfold runtime_val. unfold runtime_label.
               unfold object_label. rewrite <- H13. rewrite <-H42. rewrite <- H33. rewrite <- H27.
               assert (flow_to (join_label (join_label (join_label L_Label lb) lb2) (join_label ll ll1)) L_Label = false).
               apply flow_transitive with ll1; auto.
               apply flow_trans with (join_label ll ll1); auto. 
               apply join_def_flow2.
               apply join_def_flow2.
           

               assert (flow_to (join_label (join_label (join_label L_Label lb) lb2) (join_label ll ll2)) L_Label =   false).
               apply flow_transitive with ll2; auto.
               apply flow_trans with (join_label ll ll2); auto. 
               apply join_def_flow2.
               apply join_def_flow2.
           
               apply L_equivalence_config_H; auto.
               ++++++
               inversion H45; subst; auto.
               unfold runtime_label.
               unfold runtime_val. unfold object_label.
               rewrite <- H13. rewrite <- H27.
               remember (join_label (join_label (join_label L_Label lb) lb2) (join_label ll L_Label))  as lb''.
               case_eq (flow_to lb'' L_Label); intro. 
               apply L_equivalence_config_L; auto.          
               apply L_eq_ctn;auto.
          
               destruct H3.
             * 
               inversion H3; subst; auto.

             * unfold runtime_val in H2. unfold runtime_val in H17.
               assert (result = B_false). auto.
               assert (result0 = B_false). apply H17. intro contra; inversion contra.
               rewrite H33. rewrite H40 . auto. 
             *          
               apply L_equivalence_config_H; auto.

               ++++++
                 destruct H31 with v0 lb0; auto.
               +++++
                 apply L_equivalence_config_H; auto.
               +++
                 assert (flow_to
    (join_label (join_label (join_label (runtime_label (ObjId o)) (runtime_label v2)) lb2)
             (join_label (object_label (runtime_val (ObjId o)) h1') (object_label (runtime_val v2) h1'))) L_Label = false).
                 apply flow_transitive with (join_label (object_label (runtime_val (ObjId o)) h1') (object_label (runtime_val v2) h1')); auto.
                 apply flow_transitive with (object_label (runtime_val (ObjId o)) h1').
                 unfold runtime_val.                   unfold object_label. rewrite <- H7; auto. 
                 apply join_def_flow1; auto. 
                 apply join_def_flow2; auto.

                 assert (flow_to
    (join_label (join_label (join_label (runtime_label (ObjId o2)) (runtime_label v3)) lb2)
             (join_label (object_label (runtime_val (ObjId o2)) h2') (object_label (runtime_val v3) h2'))) L_Label = false).
                 apply flow_transitive with (join_label (object_label (runtime_val (ObjId o2)) h2') (object_label (runtime_val v3) h2')); auto.
                 apply flow_transitive with (object_label (runtime_val (ObjId o2)) h2').
                 unfold runtime_val.                   unfold object_label. rewrite <- H13; auto. 
                 apply join_def_flow1; auto. 
                 apply join_def_flow2; auto.
                 apply L_equivalence_config_H; auto.

  ++ inversion H10; subst; auto.
     inversion H0; subst; auto; inversion H26; subst; auto.
     +++
        (* two objects are with low labels and low_eq *)
        inversion H0; subst; auto; inversion H26; subst; auto.
        ++++
          unfold runtime_val in H3.
          inversion H12; subst; auto.
          *
          unfold runtime_label. unfold runtime_val. unfold object_label. rewrite <- H25.
          rewrite <- H31.
          remember (join_label (join_label (join_label L_Label L_Label) lb2) (join_label L_Label ll)) as lb''.
          case_eq (flow_to lb'' L_Label); intro.
          **
          apply L_equivalence_config_L; auto.          
          apply L_eq_ctn; auto.
          unfold runtime_val in H2. unfold runtime_val in H17.
          destruct H3.
          ***
            inversion H3; subst; auto.
          ***
          assert (result = B_false). auto.
          assert (result0 = B_false). apply H17; intro contra; inversion contra.
          rewrite H34. rewrite H35. auto.
          **
            eauto using L_equivalence_config_H; auto.
          *
            unfold runtime_label.  unfold runtime_val. unfold object_label. rewrite <- H7. rewrite <- H25.                 
            assert (flow_to (join_label (join_label (join_label L_Label L_Label) lb2) (join_label L_Label ll1)) L_Label = false).
            apply flow_transitive with (join_label L_Label ll1); auto.
            apply flow_transitive with ll1; auto. 
            apply join_def_flow2.
            apply join_def_flow2.

            assert (flow_to (join_label (join_label (join_label L_Label L_Label) lb2) (join_label L_Label ll2)) L_Label = false).
            apply flow_transitive with  (join_label L_Label ll2); auto.
            apply flow_transitive with ll2; auto. 
            apply join_def_flow2.
            apply join_def_flow2.
            
            apply L_equivalence_config_H; auto.

   +++
     inversion H12; subst; auto. 
     unfold runtime_val. unfold runtime_label. unfold object_label.
     assert (flow_to (join_label (join_label (join_label L_Label L_Label) lb2) (join_label L_Label L_Label)) L_Label = true).
     apply join_L_label_flow_to_L; auto.
     apply join_L_label_flow_to_L; auto. 
 
     apply L_equivalence_config_L; auto.
     apply L_eq_ctn; auto.
     assert (result = B_true); auto.
     assert (result0 = B_true); auto.
     rewrite H7. rewrite H9. auto.

   +++  inversion H12; subst; auto.
        ++++
          inversion H32; subst; inversion H27; subst; auto.
          * inversion H38; subst; auto.
            **
              unfold runtime_label. unfold runtime_val. unfold object_label. rewrite <- H35.
              rewrite <- H37.
              remember  (join_label (join_label (join_label L_Label lb) lb2) (join_label L_Label ll))  as lb''.
              case_eq (flow_to lb'' L_Label); intro.
              ***
              apply L_equivalence_config_L; auto.
              apply L_eq_ctn; auto.
              unfold runtime_val in H2.
              unfold runtime_val in H17.
              assert (result = B_false). apply H2. intro contra; inversion contra. 
              assert (result0 = B_false). apply H17. intro contra; inversion contra.
              rewrite H41. rewrite H42. auto.
              ***
                eauto using  L_equivalence_config_H.
            **
              unfold runtime_label. unfold runtime_val.
              assert (flow_to (join_label (join_label (join_label L_Label lb) lb2)
             (join_label (object_label null h1') (object_label (ObjId o) h1')))
                              L_Label = false).
              apply flow_transitive with (object_label (ObjId o) h1'); auto.
              unfold object_label ;auto. rewrite <- H13; auto.
              apply flow_trans with (join_label (object_label null h1') (object_label (ObjId o) h1')); auto. 
              apply join_def_flow2. 
              apply join_def_flow2. 

              assert (flow_to (join_label (join_label (join_label L_Label lb) lb2)
             (join_label (object_label null h2') (object_label (ObjId o2) h2')))
                              L_Label = false).
              apply flow_transitive with (object_label (ObjId o2) h2'); auto.
              unfold object_label ;auto. rewrite <- H35; auto.
              apply flow_trans with (join_label (object_label null h2') (object_label (ObjId o2) h2')); auto. 
              apply join_def_flow2. 
              apply join_def_flow2.
              eauto using  L_equivalence_config_H.

          * inversion H38; subst; auto. 
            unfold runtime_label. unfold runtime_val. unfold object_label.
            assert (flow_to (join_label (join_label (join_label L_Label lb) lb2) (join_label L_Label L_Label)) L_Label = true).
            apply join_L_label_flow_to_L; auto.
            apply join_L_label_flow_to_L; auto.
            apply join_L_label_flow_to_L; auto.
            apply  L_equivalence_config_L; auto.
            apply L_eq_ctn; auto. 

            unfold runtime_val in H1. unfold runtime_val in H16.
            assert (result = B_true). auto. 
            assert (result0 = B_true). auto.
            rewrite H13. rewrite H33. auto. 


          * destruct H34 with v0 lb0; auto.
            ++++
              unfold runtime_label. unfold runtime_val.
              apply L_equivalence_config_H; auto.

  ++ (* v =  (v_opa_l v lb)  *)
    inversion H10; subst; auto.
    inversion H0; subst; auto; inversion H26; subst; auto.
    (* v2 cases *) 
     +++
       (* two objects are with low labels and low_eq *)
       inversion H6; subst; auto; inversion H27; subst; auto.
       ++++
         unfold runtime_val in H3.
         inversion H12; subst; auto.
          *
            inversion H38; subst; auto.
            **
              unfold runtime_label. unfold runtime_val. unfold object_label. rewrite <- H36.
              rewrite <- H41. rewrite <- H45. rewrite <- H47. 
              remember ((join_label (join_label (join_label lb L_Label) lb2) (join_label ll0 ll)))  as lb''.
              case_eq (flow_to lb'' L_Label); intro.
            ***
              apply L_equivalence_config_L; auto.          
              apply L_eq_ctn; auto.
              unfold runtime_val in H1. unfold runtime_val in H16.
              
              destruct H3.
            ****
              inversion H3; subst; auto.              
              rewrite H13 in H44; inversion H44; subst; auto. 
              assert (result0 = B_true). auto.
              assert (result = B_true). auto.
              rewrite H48. rewrite H49. auto.
            ****
              unfold runtime_val in H2. unfold runtime_val in H17.
               assert (ObjId o2 <> ObjId o3). intro contra; inversion contra.
               subst; auto. apply bijection.right_left in H13.
               apply bijection.right_left in H44. 
               rewrite H44 in H13; inversion H13; subst; auto. 
               assert (result = B_false). auto.
               assert (result0 = B_false). auto.
               subst; auto.
            ***
               eauto using L_equivalence_config_H; auto.               
          **
            unfold runtime_val. unfold runtime_label. unfold object_label.
            rewrite <- H36.              rewrite <- H41. rewrite <- H44. rewrite <- H45. 
            assert (flow_to  (join_label (join_label (join_label lb L_Label) lb2) (join_label ll1 ll)) L_Label = false).            
            apply flow_transitive with (join_label ll1 ll); auto.
            apply flow_transitive with ll1; auto. 
            apply join_def_flow1.
            apply join_def_flow2.

            assert (flow_to (join_label (join_label (join_label lb L_Label) lb2) (join_label ll2 ll)) L_Label = false).            
            apply flow_transitive with (join_label ll2 ll); auto.
            apply flow_transitive with ll2; auto. 
            apply join_def_flow1.
            apply join_def_flow2.
            
            apply L_equivalence_config_H; auto.

          * unfold runtime_val. unfold runtime_label.
            assert (flow_to (join_label (join_label (join_label lb L_Label) lb2)
             (join_label (object_label (ObjId o0) h1') (object_label (ObjId o) h1'))) L_Label = false).            
            apply flow_transitive with (join_label (object_label (ObjId o0) h1') (object_label (ObjId o) h1')); auto.
            apply flow_transitive with (object_label (ObjId o) h1'); auto.
            unfold object_label. rewrite <- H13; auto. 
            apply join_def_flow2.
            apply join_def_flow2.

            assert (flow_to (join_label (join_label (join_label lb L_Label) lb2)
             (join_label (object_label e2 h2') (object_label (ObjId o2) h2'))) L_Label = false).            
            apply flow_transitive with (join_label (object_label e2 h2') (object_label (ObjId o2) h2')); auto.
            apply flow_transitive with (object_label (ObjId o2) h2'); auto.
            unfold object_label. rewrite <- H36; auto. 
            apply join_def_flow2.
            apply join_def_flow2.
            
            apply L_equivalence_config_H; auto.

     ++++
       unfold runtime_val in H3.
       inversion H12; subst; auto.
       *
         inversion H38; subst; auto.
         unfold runtime_label. unfold runtime_val. unfold object_label. rewrite <- H35.
         rewrite <- H37. 
         remember (join_label (join_label (join_label lb L_Label) lb2) (join_label L_Label ll)) as lb''.
         case_eq (flow_to lb'' L_Label); intro.
         **
           apply L_equivalence_config_L; auto.          
           apply L_eq_ctn; auto.
           unfold runtime_val in H2. unfold runtime_val in H17.              
           destruct H3.
           inversion H3. 
           assert (result = B_false). auto.
           assert (result0 = B_false). apply H17. intro contra; inversion contra. 
           subst; auto.

         **    eauto using L_equivalence_config_H; auto.               
       *
         inversion H38; subst; auto. 
         unfold runtime_val. unfold runtime_label. unfold object_label.
         rewrite <- H35.              rewrite <- H13.  
         assert (flow_to (join_label (join_label (join_label lb L_Label) lb2) (join_label L_Label ll1))  L_Label = false).            
            apply flow_transitive with (join_label L_Label ll1); auto.
            apply flow_transitive with ll1; auto. 
            apply join_def_flow2.
            apply join_def_flow2.

            assert (flow_to (join_label (join_label (join_label lb L_Label) lb2) (join_label L_Label ll2))  L_Label = false).            
            apply flow_transitive with (join_label L_Label ll2); auto.
            apply flow_transitive with ll2; auto. 
            apply join_def_flow2.
            apply join_def_flow2.
            apply L_equivalence_config_H; auto.

         ++++
           destruct H34 with v0 lb0; auto.

  +++
    inversion H12; subst; auto. 
    unfold runtime_val. unfold runtime_label.
    inversion H6; subst; auto; inversion H27; subst; auto.
    ++++
      unfold runtime_val in H3.
      inversion H38; subst; auto.
       *
         unfold object_label. rewrite <- H35.
         rewrite <- H37.
         remember  (join_label (join_label (join_label lb L_Label) lb2) (join_label ll L_Label))   as lb''.
         case_eq (flow_to lb'' L_Label); intro.
         **
           apply L_equivalence_config_L; auto.          
           apply L_eq_ctn; auto.
           unfold runtime_val in H2. unfold runtime_val in H17.              
           destruct H3.
           inversion H3. 
           assert (result0 = B_false). apply H17. intro contra; inversion contra. 
           assert (result = B_false). auto.
           subst; auto.

         **
           eauto using L_equivalence_config_H; auto.

       *
         unfold object_label.
         rewrite <- H13.              rewrite <- H35.
         assert (flow_to (join_label (join_label (join_label lb L_Label) lb2) (join_label ll1 L_Label))  L_Label = false).            
         apply flow_transitive with (join_label ll1 L_Label); auto.
         apply flow_transitive with ll1; auto. 
         apply join_def_flow1.
         apply join_def_flow2.

         assert (flow_to (join_label (join_label (join_label lb L_Label) lb2) (join_label ll2 L_Label))  L_Label = false).            
         apply flow_transitive with (join_label ll2 L_Label); auto.
         apply flow_transitive with ll2; auto. 
         apply join_def_flow1.
         apply join_def_flow2.
            
         apply L_equivalence_config_H; auto.

         ++++
           inversion H38; subst; auto. 
           unfold runtime_val. unfold object_label.
           assert (flow_to (join_label (join_label (join_label lb L_Label) lb2) (join_label L_Label L_Label)) L_Label = true).
           apply join_L_label_flow_to_L; auto.
           apply join_L_label_flow_to_L; auto.
           apply join_L_label_flow_to_L; auto.
           apply  L_equivalence_config_L; auto.
           apply L_eq_ctn; auto.
           unfold runtime_val in H1. unfold runtime_val in H16.
           assert (result = B_true). auto.
           assert (result0 = B_true). auto.
           subst; auto.
         ++++
           destruct H34 with v0 lb0; auto.
   +++
       inversion H6; subst; auto; inversion H27; subst; auto.
       ++++
         unfold runtime_val in H3.
         inversion H12; subst; auto.
       *
         inversion H38; subst; auto.
            **
              unfold runtime_label. unfold runtime_val.
              inversion H9; subst; auto; inversion H37; subst; auto.
              ***
                inversion H51; subst; auto.
                ****
                  unfold object_label. rewrite <- H47.
              rewrite <- H49. rewrite <- H53. rewrite <- H55. 
              remember (join_label (join_label (join_label lb lb0) lb2) (join_label ll ll0))  as lb''.
              case_eq (flow_to lb'' L_Label); intro.
              *****
                apply L_equivalence_config_L; auto.          
              apply L_eq_ctn; auto.
              unfold runtime_val in H1. unfold runtime_val in H16.              
              destruct H3.
              {  inversion H3; subst; auto.              
              rewrite H35 in H50; inversion H50; subst; auto. 
              assert (result0 = B_true). auto.
              assert (result = B_true). auto.
              subst; auto.
              }
              {
                 unfold runtime_val in H2. unfold runtime_val in H17.
                 assert (ObjId o2 <> ObjId o3). intro contra; inversion contra.
               subst; auto. apply bijection.right_left in H35.
               apply bijection.right_left in H50. 
               rewrite H50 in H35; inversion H35; subst; auto. 
               assert (result = B_false). auto.
               assert (result0 = B_false). auto.
               subst; auto.
              }
              *****
              eauto using L_equivalence_config_H; auto.
                ****
                  unfold object_label. rewrite <- H47.
                  rewrite <- H49. rewrite <- H50. rewrite <- H53.
                  assert (flow_to (join_label (join_label (join_label lb lb0) lb2) (join_label ll ll1)) L_Label = false).            
                  apply flow_transitive with (join_label ll ll1); auto.
                  apply flow_transitive with ll1; auto. 
                  apply join_def_flow2.
                  apply join_def_flow2.

                  assert (flow_to (join_label (join_label (join_label lb lb0) lb2) (join_label ll ll2))  L_Label = false).            
                  apply flow_transitive with (join_label ll ll2); auto.
                  apply flow_transitive with ll2; auto. 
                  apply join_def_flow2.
                  apply join_def_flow2.
                  apply L_equivalence_config_H; auto.


              ***
                inversion H51; subst; auto.
                unfold runtime_val. unfold runtime_label. unfold object_label.
                rewrite <- H47. rewrite <- H49. 
                remember  (join_label (join_label (join_label lb lb0) lb2) (join_label ll L_Label))  as lb''.
                case_eq (flow_to lb'' L_Label); intro.
                ****
                  destruct H3. inversion H3.
                  apply L_equivalence_config_L; auto.          
                  apply L_eq_ctn; auto.
                  unfold runtime_val in H2. unfold runtime_val in H17.              
                  assert (result0 = B_false). apply H17. intro contra; inversion contra. 
                  assert (result = B_false). auto.
                  subst; auto.
                ****
                  eauto using  L_equivalence_config_H; auto.

              ***
                destruct H44 with v lb1; auto. 
            **
              unfold runtime_val. unfold runtime_label.
              assert (flow_to  (join_label (join_label (join_label lb lb0) lb2) (join_label (object_label (ObjId o) h1') (object_label v0 h1'))) L_Label = false).
             
              apply flow_transitive with (join_label (object_label (ObjId o) h1') (object_label v0 h1')); auto.
              apply flow_transitive with (object_label (ObjId o) h1'); auto.
              unfold object_label. rewrite <- H35; auto. 
              apply join_def_flow1.
              apply join_def_flow2.

              assert (flow_to  (join_label (join_label (join_label lb lb0) lb2) (join_label (object_label (ObjId o2) h2') (object_label e0 h2'))) L_Label = false).             
              apply flow_transitive with (join_label (object_label (ObjId o2) h2') (object_label e0  h2')); auto.
              apply flow_transitive with (object_label (ObjId o2) h2'); auto.
              unfold object_label. rewrite <- H47; auto. 
              apply join_def_flow1.
              apply join_def_flow2.
            
              apply L_equivalence_config_H; auto.

       * unfold runtime_val. unfold runtime_label.
         assert (flow_to  (join_label (join_label (join_label lb lb0) lb2) (join_label (object_label (ObjId o) h1') (object_label v0 h1'))) L_Label = false).             
         apply flow_transitive with (join_label (join_label lb lb0) lb2); auto.
         apply flow_transitive with (join_label lb lb0); auto.
         apply flow_transitive with lb0; auto. 
         apply join_def_flow2.
         apply join_def_flow1.
         apply join_def_flow1.


         assert (flow_to  (join_label (join_label (join_label lb l2) lb2) (join_label (object_label e2 h2') (object_label e0 h2'))) L_Label = false).
         apply flow_transitive with (join_label (join_label lb l2) lb2); auto.
         apply flow_transitive with (join_label lb l2); auto.
         apply flow_transitive with l2; auto. 
         apply join_def_flow2.
         apply join_def_flow1.
         apply join_def_flow1.
            
         apply L_equivalence_config_H; auto.         

     ++++
       unfold runtime_val in H3.
       inversion H12; subst; auto.
       *
         inversion H38; subst; auto.
         unfold runtime_label. unfold runtime_val.

         inversion H9; subst; auto; inversion H37; subst; auto.
         **
           inversion H48; subst; auto.
           ***
              unfold object_label. rewrite <- H45.
              rewrite <- H47.
              remember (join_label (join_label (join_label lb lb0) lb2) (join_label L_Label ll)) as lb''.
              case_eq (flow_to lb'' L_Label); intro.
              ****
                apply L_equivalence_config_L; auto.          
                apply L_eq_ctn; auto.
                unfold runtime_val in H2. unfold runtime_val in H17.              
                destruct H3.
                inversion H3. 
                assert (result = B_false). auto.
                assert (result0 = B_false). apply H17. intro contra; inversion contra. 
                subst; auto.
              ****
                eauto using L_equivalence_config_H; auto.               
           ***             
             unfold runtime_val. unfold runtime_label. unfold object_label.
             rewrite <- H35.              rewrite <- H45.  
         assert (flow_to  (join_label (join_label (join_label lb lb0) lb2) (join_label L_Label ll1)) L_Label = false).            
         apply flow_transitive with (join_label L_Label ll1); auto.
         apply flow_transitive with ll1; auto. 
         apply join_def_flow2.
         apply join_def_flow2.

         assert (flow_to (join_label (join_label (join_label lb lb0) lb2) (join_label L_Label ll2)) L_Label = false).            
         apply flow_transitive with (join_label L_Label ll2); auto.
         apply flow_transitive with ll2; auto. 
         apply join_def_flow2.
         apply join_def_flow2.

         apply L_equivalence_config_H; auto.

         **
           inversion H48; subst; auto.
           unfold runtime_val. unfold runtime_label. unfold object_label.
           assert (flow_to (join_label (join_label (join_label lb lb0) lb2) (join_label L_Label L_Label)) L_Label = true).
           apply join_L_label_flow_to_L; auto.
           apply join_L_label_flow_to_L; auto.
           apply join_L_label_flow_to_L; auto.

           apply L_equivalence_config_L; auto.
           apply L_eq_ctn; auto.
           destruct H3.
           unfold runtime_val in H1. unfold runtime_val in H17.
           assert (result = B_true). auto.
           assert (result0 = B_true). auto.
           subst; auto.
           intuition.
         **
           destruct H44 with v lb1; auto.

       *
         unfold runtime_label. unfold runtime_val.
         assert (flow_to (join_label (join_label (join_label lb lb0) lb2) (join_label (object_label null h1') (object_label v0 h1'))) L_Label = false).
         apply flow_transitive with  (join_label (join_label lb lb0) lb2); auto.
         apply flow_transitive with (join_label lb lb0); auto.
         apply flow_transitive with lb0; auto. 
         apply join_def_flow2.
         apply join_def_flow1.
         apply join_def_flow1.

         assert (flow_to (join_label (join_label (join_label lb l2) lb2) (join_label (object_label e2 h2') (object_label e0 h2'))) L_Label = false).            
         apply flow_transitive with (join_label (join_label lb l2) lb2); auto.
         apply flow_transitive with (join_label lb l2); auto.
         apply flow_transitive with l2; auto. 
         apply join_def_flow2.
         apply join_def_flow1.
         apply join_def_flow1.
         apply L_equivalence_config_H; auto.
           
         ++++
           destruct H7 with v1 lb1; auto.
          

(*field access*)  
- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  + invert_l_eq_ctn.
    invert_l_eq_tm.
    exists φ. split; auto. 
  + invert_l_eq_ctn.
    invert_l_eq_tm.
    assert (value e). apply value_L_eq with  (ObjId o)  h1' h2' φ; auto.
    intuition.
  + invert_l_eq_ctn.
    invert_l_eq_tm.
    assert (value e). apply value_L_eq with (v_opa_l (ObjId o) ell)  h1' h2' φ; auto.
    apply v_opa_labeled; auto.
    intros. intro contra; inversion contra.
    intuition. 
- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  invert_l_eq_ctn.
  + invert_l_eq_fs.
    invert_l_eq_tm.
    exists φ. split; auto.

  + invert_l_eq_ctn.
    invert_l_eq_fs.
    invert_l_eq_tm.
    invert_l_eq_tm_hole.
    inversion H12 ; subst; auto. 

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  + invert_l_eq_ctn.
    invert_l_eq_tm.
    assert (value e). apply value_L_eq2 with  (ObjId o)  h1' h2' φ; auto.
    intuition.

  + invert_l_eq_ctn.
    invert_l_eq_tm.
    
    exists φ. split; auto.
    inversion H9; subst; auto.
    ++
      inversion H_bijection; subst; auto.
      apply H1 in H3; auto. inversion H3.
      +++
        subst; auto.
      rewrite <- H5 in H. inversion H; subst; auto. 
      rewrite <- H8 in H4; inversion H4; subst; auto.
      rewrite <- H22 in H8; inversion H8; subst; auto. 
      rewrite <- H21 in H5; inversion H5; subst; auto. 
      
      assert (flow_to (join_label (join_label lb lb2) ll2)  L_Label = false).
      apply flow_transitive with ((join_label lb lb2)); auto.
      apply flow_transitive with lb; auto.
      apply join_def_flow1; auto.
      apply join_def_flow1; auto.

      eauto using L_equivalence_config_H; auto.
      +++
        subst; auto. 
        rewrite <-H21 in H5; inversion H5; subst; auto.
        rewrite <-H22 in H8; inversion H8; subst; auto.

        apply config_typing_lead_to_tm_typing in H_typing1.
        destruct H_typing1 as [T1].
        destruct H26 as [gamma1].
  
        apply config_typing_lead_to_tm_typing in H_typing2.
        destruct H_typing2 as [T2].
        destruct H27 as [gamma2].
        
        destruct H25; subst; auto.
        destruct H28; subst; auto.
        destruct H28.
        
        rewrite <-H21 in H; inversion H; subst; auto.
        rewrite <-H22 in H4; inversion H4; subst; auto.

        assert (flow_to (join_label (join_label lb lb2) ll2)  L_Label = true).
        apply join_L_label_flow_to_L ; auto.
        apply join_L_label_flow_to_L ; auto. 

        apply L_equivalence_config_L; auto.
        apply L_eq_ctn; auto. 
        
        inversion H26; subst; auto. 
        assert (v = null \/ exists o', v = ObjId o').
        eauto using field_value. 

        inversion H27; subst; auto. 
        assert (v0 = null \/ exists o', v0 = ObjId o').
        apply field_value with h2' o0 cls4 F4 lb fname0 ct cls'0 gamma2 ll2; auto.

        destruct H31; subst; auto. 
        destruct H28 with fname0.
        assert (F3 fname0 = Some null). auto.
        apply H31 in H38; auto. rewrite <- H13 in H38; inversion H38; subst; auto.
        
        destruct H32; subst; auto.
        destruct H28 with fname0.
        assert (F4 fname0 = Some null). auto.
        apply H35 in H38; auto. rewrite <- H0 in H38; inversion H38; subst; auto.

        destruct H31 as [o1]. destruct H32 as [o2].
        subst; auto.
        destruct H29 with fname0 o1 o2; auto.
        rename x into cls_f1.
        destruct H31 as [cls_f2].
        destruct H31 as [lof1]. destruct H31 as [lof2].
        
        destruct H31 as [FF1]. destruct H31 as [FF2].
        destruct H31 as [llf1]. destruct H31 as [llf2].
        destruct H31. destruct H32.
        
  
        destruct H35.
        *
        (*field is low object*)
        assert (L_equivalence_object o1 h1' o2 h2' φ).
        apply H1; auto.
        apply H35. 
        inversion H38; subst; auto.
        **
        apply L_equivalence_tm_eq_object_L with cls2 F1 lb0 cls2 F2 ll ; auto.
        apply H35.
        **
          apply L_equivalence_tm_eq_object_L with cls2 F1 lb0 cls2 F2 ll ; auto.
          apply H35. 
          destruct H45.  subst; auto. 
        * apply L_equivalence_tm_eq_object_H with cls_f1 cls_f2 FF1 lof1 FF2 lof2 llf1 llf2 ; auto;
          apply H35. 
        *
          intro contra; inversion contra.
        *
          intro contra; inversion contra.

          ++
            assert (flow_to (join_label (join_label lo lb2) ll) L_Label = false).
            rewrite <- H3 in H; inversion H; subst; auto.
            apply flow_transitive with ll1; auto.
            apply  join_def_flow2; auto.
            
            assert (flow_to (join_label (join_label lo0 lb2) ll0) L_Label = false).
            rewrite <- H5 in H4; inversion H4; subst; auto.
            apply flow_transitive with ll2; auto.
            apply  join_def_flow2; auto.

            apply L_equivalence_config_H ; auto.  

  (* field access with opaque object  *)
- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).

  + invert_l_eq_ctn.
    invert_l_eq_tm.
    assert (value e). apply value_L_eq2 with (v_opa_l (ObjId o) ell)  h1' h2' φ; auto.
    apply v_opa_labeled; auto.
    intros. intro contra; inversion contra.
    intuition. 
    
  + invert_l_eq_ctn.
    invert_l_eq_tm.
    exists φ. split; auto.
    invert_l_eq_tm.
    ++ inversion H22; subst; auto.
       +++
         inversion H_bijection; subst; auto.
         apply H1 in H3; auto. inversion H3.
         ++++
           subst; auto.
           rewrite <- H5 in H. inversion H; subst; auto. 
           rewrite <- H12 in H4; inversion H4; subst; auto.
           rewrite <- H25 in H5; inversion H5; subst; auto. 
           rewrite <- H26 in H12; inversion H12; subst; auto. 
      
           assert (flow_to (join_label (join_label (join_label lb lb2) ell0) ll2) L_Label = false).
           apply flow_transitive with (join_label (join_label lb lb2) ell0); auto.
           apply flow_transitive with (join_label lb lb2); auto.
           apply flow_transitive with lb; auto.
           apply join_def_flow1; auto.
           apply join_def_flow1; auto.
           apply join_def_flow1; auto.
           eauto using L_equivalence_config_H; auto.
         ++++
        subst; auto. 
        rewrite <-H25 in H5; inversion H5; subst; auto.
        rewrite <-H26 in H12; inversion H12; subst; auto.

        apply config_typing_lead_to_tm_typing in H_typing1.
        destruct H_typing1 as [T1].
        destruct H30 as [gamma1].
  
        apply config_typing_lead_to_tm_typing in H_typing2.
        destruct H_typing2 as [T2].
        destruct H31 as [gamma2].
        
        destruct H29; subst; auto.
        destruct H32; subst; auto.
        destruct H32.
        
        rewrite <-H25 in H; inversion H; subst; auto.
        rewrite <-H26 in H4; inversion H4; subst; auto.

        assert (flow_to (join_label (join_label (join_label lb lb2) ell0) ll2)  L_Label = true).
        apply join_L_label_flow_to_L ; auto.
        apply join_L_label_flow_to_L ; auto.
        apply join_L_label_flow_to_L ; auto. 


        apply L_equivalence_config_L; auto.
        apply L_eq_ctn; auto. 
        
        inversion H30; subst; auto.
        assert (v = null \/ exists o', v = ObjId o').
        apply field_value_opaque with h1' o cls4 F3 lb fname0 ct cls' gamma1 ell0 ll2; auto.

        inversion H31; subst; auto. 
        assert (v0 = null \/ exists o', v0 = ObjId o').
        apply field_value_opaque with h2' o0 cls4 F4 lb fname0 ct cls'0 gamma2 ell0 ll2; auto.

        destruct H35; subst; auto. 
        destruct H32 with fname0.
        assert (F3 fname0 = Some null). auto.
        apply H35 in H42; auto. rewrite <- H13 in H42; inversion H42; subst; auto.
        
        destruct H36; subst; auto.
        destruct H32 with fname0.
        assert (F4 fname0 = Some null). auto.
        apply H39 in H42; auto. rewrite <- H0 in H42; inversion H42; subst; auto.

        destruct H35 as [o1]. destruct H36 as [o2].
        subst; auto.
        destruct H33 with fname0 o1 o2; auto.
        rename x into cls_f1.
        destruct H35 as [cls_f2].
        destruct H35 as [lof1]. destruct H35 as [lof2].        
        destruct H35 as [FF1]. destruct H35 as [FF2].
        destruct H35 as [llf1]. destruct H35 as [llf2]. 
        destruct H35. destruct H36.        
  
        destruct H39.
        *
        (*field is low object*)
        assert (L_equivalence_object o1 h1' o2 h2' φ).
        apply H1; auto.
        apply H39. 
        inversion H42; subst; auto.
        **
        apply L_equivalence_tm_eq_object_L with cls2 F1 lb0 cls2 F2 ll ; auto.
        apply H39.
        **
          apply L_equivalence_tm_eq_object_L with cls2 F1 lb0 cls2 F2 ll ; auto.
          apply H39. 
          destruct H49.  subst; auto. 
        * apply L_equivalence_tm_eq_object_H with cls_f1 cls_f2 FF1 lof1 FF2 lof2 llf1 llf2 ; auto;
          apply H39. 
        *
          intro contra; inversion contra.
        *
          intro contra; inversion contra.
          +++           
            assert (flow_to (join_label (join_label (join_label lo lb2) ell0) ll) L_Label = false).
            rewrite <- H3 in H; inversion H; subst; auto.
            apply flow_transitive with ll1; auto.
            apply  join_def_flow2; auto.
            
            assert (flow_to (join_label (join_label (join_label lo0 lb2) ell0) ll0) L_Label = false).
            rewrite <- H5 in H4; inversion H4; subst; auto.
            apply flow_transitive with ll2; auto.
            apply  join_def_flow2; auto.

            apply L_equivalence_config_H ; auto.

          ++
            assert (flow_to (join_label (join_label (join_label lo lb2) ell) ll) L_Label = false).
            apply flow_transitive with (join_label (join_label lo lb2) ell) ; auto.
            apply flow_transitive with ell; auto. 
            apply  join_def_flow2; auto.
            apply  join_def_flow1; auto.

            
            assert (flow_to (join_label (join_label (join_label lo0 lb2) ell0) ll0) L_Label = false).
            apply flow_transitive with (join_label (join_label lo0 lb2) ell0) ; auto.
            apply flow_transitive with ell0; auto. 
            apply  join_def_flow2; auto.
            apply  join_def_flow1; auto.

            apply L_equivalence_config_H ; auto.
            




    
   



(* method call *)
- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  + invert_l_eq_ctn.
    invert_l_eq_tm.
    exists φ. split; auto.

  + invert_l_eq_ctn.
    invert_l_eq_tm.
    assert (value e). auto. 
    apply  value_L_eq with v h1' h2' φ; auto.
    intuition. 
  + invert_l_eq_ctn.
    invert_l_eq_tm.
    assert (value e). auto. 
    apply  value_L_eq with (ObjId o)  h1' h2' φ; auto. intuition.

  + invert_l_eq_ctn.
    invert_l_eq_tm.
    assert (value e). auto. 
    apply  value_L_eq with (v_opa_l (ObjId o) ell) h1' h2' φ; auto.
    apply  v_opa_labeled; auto.  intros. intro contra; inversion contra.
    intuition.
   
- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  + invert_l_eq_ctn.
    exists φ. split; auto.
    invert_l_eq_fs.
    invert_l_eq_tm.
    
  + invert_l_eq_ctn.
    invert_l_eq_fs.
    invert_l_eq_tm.
    inversion H21; subst; auto.
    invert_value_hole.

  + invert_l_eq_ctn.
    invert_l_eq_fs.
    inversion H9; subst; auto.
    inversion H11; subst; auto.
    inversion H12. 

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  + invert_l_eq_ctn.
    invert_l_eq_tm.
    assert (value e). auto. 
    apply  value_L_eq2 with v h1' h2' φ; auto.
    intuition.

  + invert_l_eq_ctn.
    invert_l_eq_tm.
    exists φ. split; auto.

  + invert_l_eq_ctn.
    invert_l_eq_tm.     
    assert (value e2). auto. 
    apply  value_L_eq with v0 h1' h2' φ; auto.
    intuition.

  + invert_l_eq_ctn.
    invert_l_eq_tm.
    assert (value e2). auto. 
    apply  value_L_eq with v0 h1' h2' φ; auto.
    intuition.
     
    
- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  + invert_l_eq_ctn.
    invert_l_eq_fs.
    invert_l_eq_tm.    
    inversion H21; subst; auto.
    invert_value_hole.
    
  + invert_l_eq_ctn.
    invert_l_eq_fs.
    invert_l_eq_tm.    
    exists φ. split; auto.
    
  + invert_l_eq_ctn.
    invert_l_eq_fs.
    invert_l_eq_tm.
    inversion H21; subst; auto.
    inversion H13; subst; auto.
    case_eq (hole_free e2); intro ty; rewrite ty in H2; inversion H2.  
  
- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  + invert_l_eq_ctn.
    invert_l_eq_tm.
    assert (value e). apply value_L_eq2 with (ObjId o) h1' h2' φ; auto.
    contradiction.

  + invert_l_eq_ctn.
    invert_l_eq_tm.
    assert (value e2). apply value_L_eq2 with v h1' h2' φ; auto.
    contradiction.

  + invert_l_eq_ctn.
    invert_l_eq_tm.
    inversion H13; subst; auto.
    
    *
      
      assert (cls = cls0).
      inversion H_bijection. subst; auto. 
      apply H2 in H4. inversion H4; subst; auto.
      rewrite <- H24 in H; inversion H; subst; auto.
      rewrite <- H25 in H6; inversion H6; subst; auto.
      destruct H28.
      rewrite <- H24 in H; inversion H; subst; auto.
      rewrite <- H25 in H6; inversion H6; subst; auto.
      
      (* eauto using cls_def_eq. *) 
      subst; auto.
      rewrite <- H0 in H14; inversion H14; subst; auto. 

      exists  φ. split; auto.
      rewrite <- H5 in H; inversion H; subst; auto.
      rewrite <- H9 in H6; inversion H6; subst; auto.
      remember (join_label lb2 ll1) as lb''.
      case_eq (flow_to lb'' L_Label); intro.
      **
      apply L_equivalence_config_L; auto.
      apply L_eq_ctn; auto. 
      apply surface_syntax_L_equal; auto.
      inversion H_typing1; subst; auto.

      inversion H12; subst; auto.
      inversion H27; subst; auto.
      inversion H24; subst; auto.
      destruct H41 as [F']. destruct H3 as [lo']. destruct H3 as [ll'].    
      rewrite H3 in H5; inversion H5; subst; auto.
      rewrite <- H10 in H30; inversion H30; subst; auto.
      rewrite H31 in H0; inversion H0; subst; auto.

      apply  L_equivalence_store_L ; auto.
      inversion H22; subst; auto.
      destruct H3. 
        split; auto.
        intros. case_eq (beq_id arg_id x); intro.
        unfold sf_update in H10. rewrite H26 in H10; inversion H10. 
        unfold sf_update in H24. rewrite H26 in H24; inversion H24.
        subst; auto.     

        unfold sf_update in H10. rewrite H26 in H10. inversion H10. 
   
        split; auto; intros.

        apply sf_update_non_empty in H10; intuition. 
        apply sf_update_non_empty in H10. intuition.

      **
        eauto using L_equivalence_config_H; auto.

    *
      exists  φ. split; auto.
      rewrite <- H4 in H; inversion H; subst; auto.
      rewrite <- H5 in H6; inversion H6; subst; auto.

      assert ( flow_to (join_label lb2 ll1) L_Label = false).
      apply flow_transitive with ll1; auto. 
      apply join_def_flow2 ; auto. 

      assert (flow_to (join_label lb2 ll2) L_Label = false).
      apply flow_transitive with ll2; auto. 
      apply join_def_flow2 ; auto.
      apply  L_equivalence_config_H; auto.

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  + invert_l_eq_ctn.
    invert_l_eq_tm.   
    assert (value e). apply value_L_eq2 with  (v_opa_l (ObjId o) ell) h1' h2' φ; auto.
    apply v_opa_labeled; auto. intros. intro contra; inversion contra. 
    contradiction.

  + invert_l_eq_ctn.
    invert_l_eq_tm.
    assert (value e2). apply value_L_eq2 with v h1' h2' φ; auto.
    contradiction.
    
  + invert_l_eq_ctn.
    invert_l_eq_tm.
    inversion H13; subst; auto.
    ++ 
      exists φ. split;  auto.
      inversion H25; subst; auto. 
      +++ assert (cls = cls0).
          eauto using cls_def_eq; auto. 
          subst; auto.
          rewrite <- H0 in H14; inversion H14; subst; auto. 
          rewrite <- H5 in H; inversion H; subst; auto.
          rewrite <- H11 in H7; inversion H7; subst; auto.
          remember  (join_label (join_label lb2 ell0) ll1) as lb''.
          case_eq (flow_to lb'' L_Label); intro.
          apply L_equivalence_config_L; auto.
          apply L_eq_ctn; auto. 

          apply surface_syntax_L_equal; auto.
          inversion H_typing1; subst; auto.
          
          inversion H27; subst; auto.
          inversion H31; subst; auto.
          inversion H28; subst; auto.          
          inversion H36; subst; auto.
          destruct H51 as [F']. destruct H3 as [lo']. destruct H3 as [ll'].
          rewrite H3 in H5; inversion H5; subst; auto.
          rewrite <- H34 in H42; inversion H42; subst; auto.
          rewrite H35 in H0; inversion H0; subst; auto.

          apply  L_equivalence_store_L ; auto.
          inversion H22; subst; auto.
          destruct H3. 
          split; auto.
          intros. case_eq (beq_id arg_id x); intro.
          unfold sf_update in H26. rewrite H30 in H26; inversion H26. 
          unfold sf_update in H28. rewrite H30 in H28; inversion H28.
          subst; auto.

          unfold sf_update in H26. rewrite H30 in H26; inversion H26. 

          split; auto; intros.
          apply sf_update_non_empty in H26. intuition. 
          apply sf_update_non_empty in H26. intuition.
          eauto using  L_equivalence_config_H; auto.

      +++
        assert (flow_to (join_label (join_label lb2 ell0) ll) L_Label = false).
        rewrite <- H4 in H; inversion H; subst; auto.
        apply flow_transitive with ll1; auto.
        apply  join_def_flow2; auto. 
        
        assert (flow_to (join_label (join_label lb2 ell0) ll0) L_Label = false). 
        rewrite <- H5 in H7; inversion H7; subst; auto.
        apply flow_transitive with ll2; auto.
        apply  join_def_flow2; auto. 
        
        apply  L_equivalence_config_H; auto.

    ++
      exists φ. split;  auto.
      assert (flow_to (join_label (join_label lb2 ell) ll) L_Label = false).
      apply flow_transitive with (join_label lb2 ell); auto.
      apply flow_transitive with ell; auto.
      apply  join_def_flow2; auto.
      apply  join_def_flow1; auto. 
        
      assert (flow_to (join_label (join_label lb2 ell0) ll0) L_Label = false). 
      apply flow_transitive with (join_label lb2 ell0); auto.
      apply flow_transitive with ell0; auto.
      apply  join_def_flow2; auto.
      apply  join_def_flow1; auto.
      
      apply  L_equivalence_config_H; auto.

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
  inversion H16; subst; auto.
  inversion H24; subst; auto. rename cls_name0 into cls_name.
  rewrite H5 in H; inversion H; subst; auto. 

  remember (class_def cls_name field_defs method_defs) as cls_def.
  remember (add_heap_obj h1 (get_fresh_oid h1) 
        (Heap_OBJ  cls_def (init_field_map (find_fields cls_def) empty_field_map) lb2 lb2)) as h1'.
  remember (add_heap_obj h2 (get_fresh_oid h2) 
                         (Heap_OBJ  cls_def (init_field_map (find_fields cls_def) empty_field_map) lb2 lb2)) as h2'.

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
                         (Heap_OBJ  cls_def (init_field_map (find_fields cls_def) empty_field_map) lb2 lb2)) as h1'.
  
  remember (add_heap_obj h2 (get_fresh_oid h2) 
                         (Heap_OBJ  cls_def (init_field_map (find_fields cls_def) empty_field_map) lb2 lb2)) as h2'.
  
  assert (lookup_heap_obj h1' (get_fresh_oid h1) = Some (Heap_OBJ  cls_def (init_field_map (find_fields cls_def) empty_field_map) lb2 lb2) ).
  subst; auto.

  assert (lookup_heap_obj h2' (get_fresh_oid h2) = Some (Heap_OBJ  cls_def (init_field_map (find_fields cls_def) empty_field_map) lb2 lb2) ).
  subst; auto.
  apply object_equal_L with lb2 cls_def cls_def (init_field_map (find_fields cls_def) empty_field_map) (init_field_map (find_fields cls_def) empty_field_map) lb2; auto.
  
  split; auto. 
  split; auto.
  
  split; auto.  split; auto.
  split; auto.
  intros.  
  pose proof (initilized_fields_empty (find_fields cls_def) fname).

  destruct H22. rewrite H22 in H20; inversion H20.
  rewrite H22 in H20; inversion H20. intuition. 

  assert ( bijection.left (bijection.extend_bijection φ o3 o4 H6 H7)  o1 = 
           bijection.left φ o1) by (apply bijection.left_extend_bijection_neq; auto).
   rewrite H14 in H18. assert ( bijection.left φ o1 = Some o2). auto.
   apply H0 in H19. inversion H19; subst; auto.
   * 
   (* destruct H31; subst; auto. destruct H32; subst; auto. *)

  remember (class_def cls_name field_defs method_defs) as cls_def.
  assert ( lookup_heap_obj
     (add_heap_obj h1 (get_fresh_oid h1)
       (Heap_OBJ cls_def
          (init_field_map (find_fields cls_def) empty_field_map) lb2 lb2)) o1 = Some (Heap_OBJ cls2 F1 lb ll ) ).
  apply extend_heap_lookup_eq; auto. 

  destruct (oid_decision (get_fresh_oid h2) o2 ).
   assert (lookup_heap_obj h2 (get_fresh_oid h2)  = None). 
   apply fresh_oid_heap with ct; auto.  rewrite e in H29.
   rewrite H29 in H21. inversion H21.
   
   assert ( lookup_heap_obj
     (add_heap_obj h2 (get_fresh_oid h2)
       (Heap_OBJ cls_def
          (init_field_map (find_fields cls_def) empty_field_map) lb2 lb2)) o2 = Some (Heap_OBJ cls2 F2 lb ll) ).
   apply extend_heap_lookup_eq; auto.

   apply object_equal_H with lb cls2 cls2 F1 F2 ll; auto.
   *
   destruct H28; subst; auto. destruct H29; subst; auto. 

   remember (class_def cls_name field_defs method_defs) as cls_def.
   assert ( lookup_heap_obj
     (add_heap_obj h1 (get_fresh_oid h1)
       (Heap_OBJ cls_def
          (init_field_map (find_fields cls_def) empty_field_map) lb2 lb2)) o1 = Some (Heap_OBJ cls2 F1 lb ll ) ).
   apply extend_heap_lookup_eq; auto. 

  destruct (oid_decision (get_fresh_oid h2) o2 ).
   assert (lookup_heap_obj h2 (get_fresh_oid h2)  = None). 
   apply fresh_oid_heap with ct; auto.  rewrite e in H31.
   rewrite H31 in H21; inversion H21.
   
   assert ( lookup_heap_obj
     (add_heap_obj h2 (get_fresh_oid h2)
       (Heap_OBJ cls_def
          (init_field_map (find_fields cls_def) empty_field_map) lb2 lb2)) o2 = Some (Heap_OBJ cls2 F2 lb ll) ).
   apply extend_heap_lookup_eq; auto.

   apply object_equal_L with lb cls2 cls2 F1 F2 ll; auto.  
   split; auto.
   split; auto.
   destruct H29.     
   split; auto. 
   intros.
   destruct H32 with fname fo1 fo2; auto. rename x into cls_f1.
   destruct H35 as [cls_f2]. destruct H35 as [lof1]. destruct H35 as [lof2].
   destruct H35 as [FF1]. destruct H35 as [FF2].
   destruct H35 as [llf1]. destruct H35 as [llf2].
   destruct H35. destruct H36.

   exists cls_f1. exists cls_f2.
   exists lof1. exists lof2.
   exists FF1. exists FF2.
   exists llf1. exists llf2.  
   split; auto. 
   apply extend_heap_lookup_eq; auto. 
   apply lookup_extend_heap_fresh_oid with ct  (Heap_OBJ cls_f1 FF1 lof1 llf1) ; auto. 
   split; auto. 
   apply extend_heap_lookup_eq; auto. 
   apply lookup_extend_heap_fresh_oid with ct (Heap_OBJ cls_f2 FF2 lof2 llf2) ; auto. 
   assert (fo1 <> get_fresh_oid h1  ).
   apply lookup_extend_heap_fresh_oid with ct  (Heap_OBJ cls_f1 FF1 lof1 llf1) ; auto.
   assert ( bijection.left (bijection.extend_bijection φ (get_fresh_oid h1) (get_fresh_oid h2) H6 H7)  fo1 = 
            bijection.left φ fo1) by (apply bijection.left_extend_bijection_neq; auto).

   destruct H37.
   destruct H37.  left. rewrite H39. auto.
   right; auto. 

   *
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
                                          empty_field_map) lb2 lb2) ; auto).
     rewrite H18.  apply H1 in H19; auto.

   *
     rewrite   Heqh2'. intros. subst. 
     destruct (oid_decision (get_fresh_oid h2) o). subst; auto.
     unfold  lookup_heap_obj in H14. unfold add_heap_obj in H14.
     rewrite H13 in H14. inversion H14.

   assert (bijection.right (bijection.extend_bijection φ (get_fresh_oid h1) (get_fresh_oid h2) H6 H7)  o = 
           bijection.right φ o). (apply bijection.right_extend_bijection_neq; auto).
   remember (class_def cls_name field_defs method_defs) as cls_def. 
   assert ( lookup_heap_obj h2 o = None) by (apply lookup_extended_heap_none with
                                                 (Heap_OBJ cls_def (init_field_map (find_fields cls_def)
                                                                                   empty_field_map) lb2 lb2) ; auto).
   rewrite H18. apply H2 in H19. auto.

   *
     intros.
     destruct (oid_decision o3 o). subst; auto. simpl in H14.
     rewrite H11 in H14. inversion H14. subst; auto.
     try (inconsist_label).

     subst; auto.

   unfold lookup_heap_obj in H14. unfold add_heap_obj in H14.
   assert (o <> get_fresh_oid h1) by (auto). apply  beq_oid_not_equal in H19. rewrite H19 in H14.
   fold lookup_heap_obj in H14. apply H3 in H14.
   assert (bijection.left (bijection.extend_bijection φ (get_fresh_oid h1) (get_fresh_oid h2) H6 H7)  o = 
           bijection.left φ o) by (apply bijection.left_extend_bijection_neq; auto).
   rewrite H20; auto. auto.
   *
   intros.
   destruct (oid_decision o4 o). subst; auto. simpl in H14.
   rewrite H13 in H14. inversion H14. subst; auto.
   try (inconsist_label).
   subst; auto.
   unfold lookup_heap_obj in H14. unfold add_heap_obj in H14.
   assert (o <> get_fresh_oid h2) by (auto). apply  beq_oid_not_equal in H19. rewrite H19 in H14.
   fold lookup_heap_obj in H14. apply H4 in H14.
   assert (bijection.right (bijection.extend_bijection φ (get_fresh_oid h1) (get_fresh_oid h2) H6 H7)  o = 
           bijection.right φ o) by (apply bijection.right_extend_bijection_neq; auto).
   rewrite H20; auto. auto.
   *
  (*  L_equivalence_config  *)
  apply L_equivalence_config_L; auto.
  
  subst; auto.
  inversion H16; subst; auto.
  inversion H24; subst; auto.
  rewrite H5 in H; inversion H; subst; auto.
  apply L_eq_ctn; auto.

  apply L_equivalence_tm_eq_object_L with (class_def cls_name0 field_defs method_defs)
                                          (init_field_map (find_fields (class_def cls_name0 field_defs method_defs)) empty_field_map)
                                          lb2
                                          (class_def cls_name0 field_defs method_defs)
                                          (init_field_map (find_fields (class_def cls_name0 field_defs method_defs)) empty_field_map)
                                          lb2

  ; auto. 
  apply extend_heap_preserve_L_eq_fs with ct φ H6 H7; auto.
  apply extend_heap_preserve_L_eq_store with ct φ H6 H7; auto.
  inversion  H_valid1; subst; auto.
  inversion H21; auto. 
  inversion  H_valid2; subst; auto.
  inversion H21; auto. 
  inversion H16; subst; auto.
  
  inversion H24; subst; auto.

  rewrite H5 in H; inversion H; subst; auto.
  apply extend_heap_preserve_L_eq_ctns with ct φ H6 H7; auto.
    inversion  H_valid1; subst; auto.
  inversion  H_valid2; subst; auto.

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  (*labelData*)

  + invert_l_eq_ctn.
    invert_l_eq_tm.
    exists φ. split; auto.

  + invert_l_eq_ctn.
    invert_l_eq_tm.
    assert (value e). apply value_L_eq with v h1' h2'  φ; auto.
    intuition. 

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  (* L_eq_container (Container t1 (labelData hole lo :: fs) lb1 sf1) h1' (Container t2 fs2 lb2 sf2) h2 φ *)
  + invert_l_eq_ctn.
    invert_l_eq_fs.
    invert_l_eq_tm.
    exists φ. split; auto.
  + invert_l_eq_ctn.
    invert_l_eq_fs.
    invert_l_eq_tm.
    inversion H3; subst; auto.
    inversion H12. 

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
(*L_eq_container (Container (labelData v lo) fs1 lb1 sf1) h1' (Container t2 fs2 lb2 sf2) h2 φ*)

  + invert_l_eq_ctn.
    invert_l_eq_tm.
    assert (value e). apply value_L_eq2 with v h1' h2'  φ; auto.
    intuition.

  + invert_l_eq_ctn.
    invert_l_eq_tm.
    exists φ. split; auto. 
    apply L_equivalence_config_L; auto.
    apply L_eq_ctn; auto.
    case_eq (flow_to lo0 L_Label); intro; auto. 

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  (* L_eq_container (Container (unlabel e) fs1 lb1 sf1) h1' (Container t2 fs2 lb2 sf2) h2 φ*)
  + invert_l_eq_ctn.
    invert_l_eq_tm.
    exists φ. split; auto.

  + invert_l_eq_ctn.
    invert_l_eq_tm.
    inversion H3; subst; auto; try (intuition). 
  + invert_l_eq_ctn.
    invert_l_eq_tm.
    inversion H3; subst; auto; contradiction.        

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  (*L_eq_container (Container t1 (unlabel hole :: fs) lb1 sf1) h1' (Container t2 fs2 lb2 sf2) h2 φ*)
  + invert_l_eq_ctn.
    invert_l_eq_fs.
    invert_l_eq_tm.  
    exists φ. split; auto.

  + invert_l_eq_ctn.
    invert_l_eq_fs.
    invert_l_eq_tm.
    inversion H1; subst; auto.
    inversion H12.

 - inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  (* L_eq_container (Container (unlabel (v_l v lo)) fs1 lb1 sf1) h1' (Container (unlabel e) fs2 lb2 sf2) h2' φ *)
  + invert_l_eq_ctn.
    invert_l_eq_tm.
    assert (value e).
    apply value_L_eq2 with (v_l v lo)  h1' h2'  φ; auto.
    intuition.
  + invert_l_eq_ctn.
    invert_l_eq_tm.
    inversion H3; subst; auto.
    ++
      exists φ. split; auto.
      assert (flow_to (join_label lb2 lo0) L_Label = true).
      apply join_L_label_flow_to_L; auto.
      apply L_equivalence_config_L; auto.

    ++
      exists φ. split; auto.
      assert (flow_to (join_label lb2 lo0) L_Label = false).
      apply flow_join_label with lo0 lb2; auto.
      apply L_equivalence_config_H; auto.
    
- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  (* L_eq_container (Container (unlabel (v_l v lo)) fs1 lb1 sf1) h1' (Container t2 fs2 lb2 sf2) h2 φ*)
  +
    invert_l_eq_ctn.
    invert_l_eq_tm.
    assert (value e).
    apply value_L_eq2 with (v_opa_l v ell)  h1' h2'  φ; auto.
    contradiction. 
  
  + invert_l_eq_ctn.
    invert_l_eq_tm.
    inversion H3; subst; auto.
    ++ 
      assert (flow_to (join_label lb2 ell0) L_Label = true).
      apply join_L_label_flow_to_L; auto.

      assert (flow_to (join_label lb2 ell0) L_Label = true).
      apply join_L_label_flow_to_L; auto. 
      exists φ.
      split; auto.

    ++
      assert (flow_to (join_label lb2 ell) L_Label = false). 
      apply flow_join_label with ell lb2; auto. 
      assert (flow_to (join_label lb2 ell0) L_Label = false). 
      apply flow_join_label with ell0 lb2; auto.

      exists φ. split; auto.

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  (*L_eq_container (Container (labelOf e) fs1 lb1 sf1) h1' (Container t2 fs2 lb2 sf2) h2 φ*)
  + 
    invert_l_eq_ctn.
    invert_l_eq_tm.  exists φ. split;  auto.
  +
    invert_l_eq_ctn.
    invert_l_eq_tm.
    inversion H4; subst; auto; intuition.

  + invert_l_eq_ctn.
    invert_l_eq_tm.
    inversion H4; subst; auto; intuition.

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  (* L_eq_container (Container t1 (labelOf hole :: fs) lb1 sf1) h1' (Container t2 fs2 lb2 sf2) h2 φ*)
  + invert_l_eq_ctn.
    invert_l_eq_fs.
    invert_l_eq_tm.
    exists φ. split;  auto.
  +
    invert_l_eq_ctn.
    invert_l_eq_fs.
    invert_l_eq_tm.
    inversion H1; subst; auto.
    inversion H12.

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  (*L_eq_container (Container (labelOf (v_l v lo)) fs1 lb1 sf1) h1' (Container t2 fs2 lb2 sf2) h2 φ*)
  + invert_l_eq_ctn.
    invert_l_eq_tm.
    inversion H4; subst; auto; intuition. 

  + invert_l_eq_ctn.
    invert_l_eq_tm.
    inversion H4; subst; auto.
  
    exists φ. split; auto.
    exists φ. split; auto.
 
- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  (*L_eq_container (Container (labelOf (v_opa_l v ell)) fs1 lb1 sf1) h1' (Container t2 fs2 lb2 sf2) h2 φ*)
  + invert_l_eq_ctn.
    invert_l_eq_tm.
    assert (value e).
    apply value_L_eq2 with (v_opa_l v ell)  h1' h2'  φ; auto.
    contradiction.

  + invert_l_eq_ctn.
    invert_l_eq_tm.
    inversion H4; subst; auto.
    ++ 
      assert (flow_to (join_label lb2 ell0) L_Label = true).
      apply join_L_label_flow_to_L; auto.

      assert (flow_to (join_label lb2 ell0) L_Label = true).
      apply join_L_label_flow_to_L; auto. 
      exists φ.
      split; auto.

    ++
      assert (flow_to (join_label lb2 ell) L_Label = false). 
      apply flow_join_label with ell lb2; auto. 
      assert (flow_to (join_label lb2 ell0) L_Label = false). 
      apply flow_join_label with ell0 lb2; auto.

      exists φ. split; auto.

(* objectLabelOf 1*)
- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  (* L_eq_container (Container (objectLabelOf e) fs1 lb1 sf1) h1' (Container (objectLabelOf e0) fs2 lb2 sf2) h2' φ φ*)
  + invert_l_eq_ctn.
    invert_l_eq_tm.
    exists φ. split;  auto.  
  + invert_l_eq_ctn.
    invert_l_eq_tm.
    inversion H4; subst; auto; intuition.
  + invert_l_eq_ctn.
    invert_l_eq_tm.
    inversion H4; subst; auto; intuition.

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  (* L_eq_container (Container t1 (objectLabelOf hole :: fs) lb1 sf1) h1' (Container t2 (objectLabelOf hole :: fs0) lb2 sf2) h2' φ *)
  + invert_l_eq_ctn.
    invert_l_eq_fs.
    invert_l_eq_tm.
    exists φ. split;  auto.
  + invert_l_eq_ctn.
    invert_l_eq_fs.
    invert_l_eq_tm.
    inversion H1; subst; auto.
    inversion H12.

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  (* L_eq_container (Container (objectLabelOf (ObjId o)) fs1 lb1 sf1) h1' (Container (objectLabelOf e) fs2 lb2 sf2) h2' φ *)
  + invert_l_eq_ctn.
    invert_l_eq_tm.
    inversion H4; subst; auto; intuition. 

  + invert_l_eq_ctn.
    invert_l_eq_tm.
    inversion H4; subst; auto.
    ++
      exists φ. split; auto.
      rewrite <- H in H5; inversion H5; subst; auto.
      rewrite <- H1 in H9; inversion H9; subst; auto.  

      assert (flow_to (join_label ll0 lb2) L_Label = true).   
      apply join_L_label_flow_to_L; auto.
      apply L_equivalence_config_L; auto.
    ++
      exists φ. split; auto.
      rewrite <- H3 in H; inversion H; subst; auto.
      rewrite <- H5 in H1; inversion H1; subst; auto. 
      assert (flow_to (join_label ll1 lb2) L_Label = false).      
      apply  flow_join_label with ll1 lb2; auto.
      apply join_label_commutative; auto.

      assert (flow_to (join_label ll2 lb2) L_Label = false).      
      apply  flow_join_label with ll2 lb2; auto.
      apply join_label_commutative; auto.
      apply L_equivalence_config_H; auto.
      

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  (*  L_eq_container (Container (objectLabelOf (v_opa_l (ObjId o) ell)) fs1 lb1 sf1) h1' (Container (objectLabelOf e) fs2 lb2 sf2) h2' φ *)
  + invert_l_eq_ctn.
    invert_l_eq_tm.
    inversion H4; subst; auto; intuition. 

  + invert_l_eq_ctn.
    invert_l_eq_tm.
    inversion H4; subst; auto.
    ++ inversion H20; subst; auto.
       +++ exists φ. split; auto.
           rewrite <- H in H5; inversion H5; subst; auto.
           rewrite <- H2 in H11; inversion H11; subst; auto.
           remember  (join_label ll0 (join_label lb2 ell0)) as lb''.
           case_eq (flow_to lb'' L_Label ); intro.
           apply L_equivalence_config_L; auto.
           eauto using L_equivalence_config_H.
          
       +++
         exists φ. split; auto.
         rewrite <- H3 in H; inversion H; subst; auto.
         rewrite <- H5 in H2; inversion H2; subst; auto.
         assert (flow_to  (join_label ll1 (join_label lb2 ell0)) L_Label = false).
         apply flow_transitive with ll1; auto.
         apply join_def_flow1 ; auto.
         assert (flow_to  (join_label ll2 (join_label lb2 ell0)) L_Label = false).
         apply flow_transitive with ll2; auto.
         apply join_def_flow1 ; auto. 
         eauto using L_equivalence_config_H.
    ++
    exists φ. split; auto.
    assert (flow_to (join_label ll (join_label lb2 ell)) L_Label = false).
    apply flow_join_label with (join_label lb2 ell) ll; auto.
    apply flow_join_label with ell lb2; auto. 
  
    assert (flow_to (join_label ll0 (join_label lb2 ell0)) L_Label = false). 
    apply flow_join_label  with (join_label lb2 ell0) ll0; auto.
    apply flow_join_label with ell0 lb2; auto. 

    apply L_equivalence_config_H; auto.
      
(* raise label *)
- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn);
    try (invert_l_eq_ctn; invert_l_eq_tm; exists φ; split;  auto; fail);
    try (invert_l_eq_ctn; invert_l_eq_tm; inversion H4; subst; auto; intuition; fail);
    try (invert_l_eq_ctn; invert_l_eq_fs; invert_l_eq_tm; exists φ; split;  auto; fail).
  + invert_l_eq_ctn.
    invert_l_eq_tm.
    assert (value e).
    apply value_L_eq with (ObjId o) h1' h2 φ; auto.
    contradiction. 
  + invert_l_eq_ctn.
    invert_l_eq_tm.
    assert (value e).
    apply value_L_eq with (v_opa_l (ObjId o) ell) h1' h2 φ; auto.
    apply v_opa_labeled; auto.
    intros. intro contra; inversion contra.
    contradiction.
   
(* raise label *)
- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn);
    try (invert_l_eq_ctn; invert_l_eq_tm; exists φ; split;  auto; fail);
    try (invert_l_eq_ctn; invert_l_eq_tm; inversion H4; subst; auto; intuition; fail);
    try (invert_l_eq_ctn; invert_l_eq_fs; invert_l_eq_tm; exists φ; split;  auto; fail);
    try (invert_l_eq_ctn; invert_l_eq_fs; invert_l_eq_tm; inversion H3; subst; auto; inversion H12; fail).

(* L_eq_container (Container (raiseLabel (ObjId o) lo') fs1 lb1 sf1) h1
          (Container t2 fs2 lb2 sf2) h2 φ *)
- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  + invert_l_eq_ctn.
    invert_l_eq_tm.    
    assert (value e).
    apply value_L_eq2 with (ObjId o) h1 h2' φ; auto.
    contradiction. 

  + invert_l_eq_ctn.
    invert_l_eq_tm.
    exists φ. split; auto.
    eauto using change_obj_preserve_bijection .
    apply lbl_change_obj_both_lbl_preserve_l_eq_config with lo lo0; auto.
    inversion H_valid1; subst; auto. 
    apply valid_conf ; auto.
    inversion H13; subst; auto.
    inversion H_valid2; subst; auto.
    apply valid_conf ; auto.
    inversion H13; subst; auto.


- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  (*L_eq_container (Container (raiseLabel (v_opa_l v ell) lo) fs1 lb1 sf1) h1' (Container (raiseLabel e lo0) fs2 lb2 sf2) h2' φ*)
  + invert_l_eq_ctn.
    invert_l_eq_tm.
    assert (value e).
    apply value_L_eq2 with (v_opa_l (ObjId o) ell) h1 h2' φ; auto.
    apply v_opa_labeled; auto.
    intros. intro contra; inversion contra.
    contradiction. 

  + invert_l_eq_ctn.
    invert_l_eq_tm.
    assert (flow_to lb2 ll = true). 
    apply flow_trans with (join_label lb2 ell); auto.
    apply join_def_flow1; auto.

    assert (flow_to lb2 ll0 = true). 
    apply flow_trans with (join_label lb2 ell0); auto. 
    apply join_def_flow1; auto.

    exists φ. split; auto.
    apply change_obj_preserve_bijection  with ct lo lo0 lb2 lb2; auto.
    inversion H10; subst; auto.
      
    assert (flow_to ll L_Label = false).
    apply flow_transitive with (join_label lb2 ell); auto.
    apply flow_transitive with ell; auto.
    apply join_def_flow2; auto.

    assert (flow_to ll0 L_Label = false).
    apply flow_transitive with (join_label lb2 ell0); auto.
    apply flow_transitive with ell0; auto.
    apply join_def_flow2; auto.
    eauto using  L_equivalence_tm_eq_object_H . 

    apply lbl_change_obj_both_lbl_preserve_l_eq_config with lo lo0; auto.

    inversion H_valid1; subst; auto.
    apply valid_conf ; auto.
    inversion H24; subst; auto.
      
    inversion H_valid2; subst; auto.
    apply valid_conf ; auto.
    inversion H24; subst; auto.

    inversion H10; subst; auto. 
    assert (flow_to ll L_Label = false).
    apply flow_transitive with (join_label lb2 ell); auto.
    apply flow_transitive with ell; auto.
    apply join_def_flow2; auto.

    assert (flow_to ll0 L_Label = false).
    apply flow_transitive with (join_label lb2 ell0); auto.
    apply flow_transitive with ell0; auto.
    apply join_def_flow2; auto.

    eauto using  L_equivalence_tm_eq_object_H .  

(* toLabled *)

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn);
    try (invert_l_eq_ctn; invert_l_eq_tm; exists φ; split;  auto; fail);
    try (invert_l_eq_ctn; invert_l_eq_tm; inversion H4; subst; auto; intuition; fail);
    try (invert_l_eq_ctn; invert_l_eq_fs; invert_l_eq_tm; exists φ; split;  auto; fail).
  + invert_l_eq_ctn.
    invert_l_eq_tm.
    assert (value e2).
    apply value_L_eq with (l lo) h1' h2' φ; auto.
    contradiction. 
  + invert_l_eq_ctn.
    invert_l_eq_tm.
    assert (value e2).
    apply value_L_eq with (v_opa_l (v) ell) h1' h2' φ; auto.
    contradiction.

(* toLabeled 2 *)
- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn);
    try (invert_l_eq_ctn; invert_l_eq_tm; exists φ; split;  auto; fail);
    try (invert_l_eq_ctn; invert_l_eq_tm; inversion H4; subst; auto; intuition; fail);
    try (invert_l_eq_ctn; invert_l_eq_fs; invert_l_eq_tm; exists φ; split;  auto; fail).
  + invert_l_eq_ctn.
    invert_l_eq_fs.    
    invert_l_eq_tm.
    inversion H11; subst; auto.
    inversion H12; subst; auto.
    case_eq (hole_free e2); intro;
    rewrite H0 in H1; inversion H1. 

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn);
    try (invert_l_eq_ctn; invert_l_eq_tm; exists φ; split;  auto; fail);
    try (invert_l_eq_ctn; invert_l_eq_tm; inversion H4; subst; auto; intuition; fail);
    try (invert_l_eq_ctn; invert_l_eq_fs; invert_l_eq_tm; exists φ; split;  auto; fail).
  + invert_l_eq_ctn.
    invert_l_eq_tm.
    assert (value e2).
    apply value_L_eq2 with (l lo) h1' h2' φ; auto.
    contradiction. 
  + invert_l_eq_ctn.
    invert_l_eq_tm.
    exists φ. split; auto.
    inversion H8; subst; auto.
    
- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn);
    try (invert_l_eq_ctn; invert_l_eq_tm; exists φ; split;  auto; fail);
    try (invert_l_eq_ctn; invert_l_eq_tm; inversion H4; subst; auto; intuition; fail);
    try (invert_l_eq_ctn; invert_l_eq_fs; invert_l_eq_tm; exists φ; split;  auto; fail).
  + invert_l_eq_ctn.
    invert_l_eq_tm.
    assert (value e2).
    apply value_L_eq2 with (v_opa_l (v) ell) h1' h2' φ; auto.
    contradiction. 
  + invert_l_eq_ctn.
    invert_l_eq_tm.
    exists φ. split; auto.
    inversion H10; subst; auto.
    ++
      assert (flow_to (join_label lb2 ell0) L_Label = true).
      apply join_L_label_flow_to_L; auto. 
      apply L_equivalence_config_L; auto.
    ++
      assert (flow_to (join_label lb2 ell0) L_Label = false).
      apply flow_transitive with ell0; auto.
      apply join_def_flow2.

      assert (flow_to (join_label lb2 ell) L_Label = false).
      apply flow_transitive with ell; auto.
      apply join_def_flow2.
      eauto using L_equivalence_config_H; auto.

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  (* L_eq_container (Container getCurrentLevel fs1 lb2 sf1) h1'
          (Container getCurrentLevel fs2 lb2 sf2) h2' φ *)
  invert_l_eq_ctn.
  exists φ. split; auto. 
      
- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  (*L_eq_container (Container (Assignment id e) fs1 lb1 sf1) h1' (Container t2 fs2 lb2 sf2) h2 φ*)
  + invert_l_eq_ctn.
    invert_l_eq_tm.
    exists φ. split; auto. 

  + invert_l_eq_ctn.
    invert_l_eq_tm.
    assert (value e). apply value_L_eq with v h1' h2' φ; auto. intuition.
  
- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  (*L_eq_container (Container t1 (Assignment id hole :: fs) lb1 sf1) h1' (Container t2 fs2 lb2 sf2) h2 φ*)
  +  invert_l_eq_ctn.
     invert_l_eq_fs.
     invert_l_eq_tm.
     exists φ. split; auto.

  + invert_l_eq_ctn.
    invert_l_eq_fs.
    invert_l_eq_tm.
    inversion H3; subst; auto.
    inversion H12. 

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  (*L_eq_container (Container (Assignment id v) fs1 lb1 sf1) h1' (Container t2 fs2 lb2 sf2) h2 φ*)
  + invert_l_eq_ctn.
    invert_l_eq_tm.
    assert (value e). apply value_L_eq2 with v h1' h2' φ; auto. intuition.

  + invert_l_eq_ctn.
    invert_l_eq_tm.  exists φ. split;  auto. 

    apply L_equivalence_config_L; auto.
    apply L_eq_ctn; auto.
    rename id0 into arg_id. 
    apply L_equivalence_store_L; auto; intros.
    split; auto;
    try ( empty_sf).
    intros. 
    case_eq (beq_id arg_id x); intro.
    * 
    unfold sf_update in H0; rewrite H5 in H0; inversion H0.
    unfold sf_update in H3; rewrite H5 in H3; inversion H3.
    subst; auto.
    *
    unfold sf_update in H0; rewrite H5 in H0; inversion H0.
    unfold sf_update in H3; rewrite H5 in H3; inversion H3.
    subst; auto. 
  
    inversion H18; subst; auto.
    destruct H6.
    apply H6 with x; auto.

    *
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
    invert_l_eq_ctn.
    invert_l_eq_tm.
    exists φ. split;  auto.
  +
    invert_l_eq_ctn.
    invert_l_eq_tm.
    assert (value e). apply value_L_eq with  v h1' h2'  φ; auto.
    intuition.

  + invert_l_eq_ctn.
    invert_l_eq_tm.
    assert (value e). apply value_L_eq with  (ObjId o) h1' h2  φ; auto.
    intuition. 
  
  + invert_l_eq_ctn.
    invert_l_eq_tm.
    assert (value e). apply value_L_eq with  (v_opa_l (ObjId o) ell)  h1' h2'  φ; auto.
    apply v_opa_labeled; auto.
    intros. intro contra; inversion contra. 
    intuition. 
  
  
- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  (*L_eq_container (Container t1 (FieldWrite hole f e2 :: fs) lb1 sf1) h1' (Container t2 fs2 lb2 sf2) h2 φ*)
  + invert_l_eq_ctn.
    invert_l_eq_fs.
    invert_l_eq_tm.
    inversion H9; subst; auto.
    exists φ. split;  auto.
  
  + invert_l_eq_ctn.
    invert_l_eq_fs.
    invert_l_eq_tm.
    inversion H21; subst; auto.
    inversion H12.

  + invert_l_eq_ctn.
    invert_l_eq_fs.
    invert_l_eq_tm.
    inversion H4; subst; auto.
    inversion H12. 

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  (*L_eq_container (Container (FieldWrite v f e2) fs1 lb1 sf1) h1' (Container t2 fs2 lb2 sf2) h2 φ*)
  + invert_l_eq_ctn.
    invert_l_eq_tm.
    assert (value e). apply value_L_eq2 with v h1' h2' φ; auto.
    intuition.

  + invert_l_eq_ctn.
    invert_l_eq_tm.
    exists φ. split; auto.

  + invert_l_eq_ctn.
    invert_l_eq_tm.
    assert (value e2). apply value_L_eq with v0  h1' h2  φ; auto.
    intuition. 
  + invert_l_eq_ctn.
    invert_l_eq_tm.
    assert (value e2). apply value_L_eq with v0  h1' h2'  φ; auto.
    intuition.
    
- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  (*L_eq_container (Container t1 (FieldWrite v1 f hole :: fs) lb1 sf1) h1' (Container t2 fs2 lb2 sf2) h2 φ *)
  + invert_l_eq_ctn.
    invert_l_eq_fs.
    invert_l_eq_tm.
    inversion H21; subst; auto.
    invert_value_hole. 

  + invert_l_eq_ctn.
    invert_l_eq_fs.
    invert_l_eq_tm.
    exists φ. split; auto.

  + invert_l_eq_ctn.
    invert_l_eq_fs.
    invert_l_eq_tm.
    inversion H22; subst; auto.
    inversion H13.
    case_eq (hole_free e2); intro; rewrite H1 in H2; inversion H2.
  
- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  (*L_eq_container (Container (FieldWrite (ObjId o) f v) fs1 lb1 sf1) h1 (Container t2 fs2 lb2 sf2) h2 φ*)
  + invert_l_eq_ctn.
    invert_l_eq_tm.
    assert (value e). apply value_L_eq2 with (ObjId o) h1 h2'  φ; auto.
    contradiction.

  + invert_l_eq_ctn.
    invert_l_eq_tm.
    assert (value e2). apply value_L_eq2 with v h1 h2'  φ; auto.
    contradiction.

  + invert_l_eq_ctn.
    invert_l_eq_tm.
    
    assert (FieldWrite (ObjId o) f0 v <> return_hole). intro contra; inversion contra.
    pose proof config_typing_lead_to_tm_typing h1 ct (FieldWrite (ObjId o) f0 v) fs1 lb2 sf1 ctns_stack1' T H_typing1 H0.
    destruct H2 as [Ty1]. destruct H2 as [gamma1].
    inversion H2; subst; auto.

    assert (FieldWrite (ObjId o0) f0 v0 <> return_hole).
    intro contra; inversion contra.
    pose proof config_typing_lead_to_tm_typing h2 ct (FieldWrite (ObjId o0) f0 v0) fs2 lb2 sf2 ctns_stack2' T H_typing2 H4.
    destruct H5 as [Ty2]. destruct H5 as [gamma2].
    inversion H5; subst; auto.

    inversion H3; subst; auto; inversion H23; subst; auto.
    ++
      inversion H20; subst; auto; inversion H30; subst; auto.
      *
        destruct H34 as [F1]. destruct H6 as [lo1]. destruct H6 as [ll1].
        destruct H37 as [F2]. destruct H9 as [lo2]. destruct H9 as [ll2].
        exists φ. split; auto.
        **
          apply update_field_preserve_bijection_new with ct L_Label L_Label lb2 lb2; auto.
          unfold runtime_val. right.
          exists o1.  exists cls_def1. exists F1. exists lo1.  exists ll1. split; auto.
          unfold runtime_val. right.
          exists o2.  exists cls_def2. exists F2. exists lo2.  exists ll2. split; auto.

          unfold runtime_label in H1.
          pose proof  join_label_commutative L_Label lb2.
          rewrite <- H28; auto.
          pose proof  join_label_commutative L_Label lb2.
          rewrite <- H28; auto.          

          apply  L_equivalence_tm_eq_v_opa_l_L; auto.
          unfold runtime_val.
          apply v_opa_labeled; auto.
          intros. intro contra; inversion contra.

          unfold runtime_val.
          apply v_opa_labeled; auto.
          intros. intro contra; inversion contra.
        **
          inversion  H_valid1; subst;  auto.
          inversion H41; subst; auto.

          inversion  H_valid2; subst;  auto.
          inversion H51; subst; auto. 

          assert (forall a1 a2 : oid, decision.Decision (a1 = a2)). auto.
  
          apply L_equivalence_config_L; auto.
          ***
          apply update_field_preserve_L_eq_ctn with  ct lb2 L_Label lb2 L_Label; auto.
          assert (join_label L_Label lb2 =join_label lb2 L_Label).
          apply join_label_commutative.
          rewrite <- H29; auto. 

          assert (join_label L_Label lb2 =join_label lb2 L_Label).
          apply join_label_commutative.
          rewrite <- H29; auto.
 
          apply  L_equivalence_tm_eq_v_opa_l_L; auto.
          unfold runtime_val.
          apply v_opa_labeled; auto.
          intros. intro contra; inversion contra.

          unfold runtime_val.
          apply v_opa_labeled; auto.
          intros. intro contra; inversion contra.
          ***
            apply update_field_preserve_L_eq_ctns  with  ct lb2 L_Label lb2 L_Label; auto.
            assert (join_label L_Label lb2  = join_label lb2 L_Label).
            apply join_label_commutative. rewrite <- H29. auto. 

            assert (join_label L_Label lb2 =join_label lb2 L_Label).
            apply join_label_commutative.
            rewrite <- H29; auto.

            apply  L_equivalence_tm_eq_v_opa_l_L; auto.
            unfold runtime_val.
            apply v_opa_labeled; auto.
            intros. intro contra; inversion contra.

            unfold runtime_val.
            apply v_opa_labeled; auto.
            intros. intro contra; inversion contra. 

      *
        inversion H24.

      *
        inversion H24.
    ++
      inversion H24; subst; auto.
      exists φ. split; auto.
      apply update_field_preserve_bijection_new with ct L_Label L_Label lb2 lb2; auto.
      assert (join_label L_Label lb2 =join_label lb2 L_Label).
      apply join_label_commutative.
      rewrite <- H6; auto. 

      assert (join_label L_Label lb2 =join_label lb2 L_Label).
      apply join_label_commutative.
      rewrite <- H6; auto.
      
      apply  L_equivalence_tm_eq_v_opa_l_L; auto.
      unfold runtime_val.
      apply v_opa_labeled; auto.
      intros. intro contra; inversion contra.

      unfold runtime_val.
      apply v_opa_labeled; auto.
      intros. intro contra; inversion contra. 

      inversion  H_valid1; subst;  auto.
      inversion H35; subst; auto.

      inversion  H_valid2; subst;  auto.
      inversion H45; subst; auto. 

      assert (forall a1 a2 : oid, decision.Decision (a1 = a2)). auto.  
      apply L_equivalence_config_L; auto.
      apply update_field_preserve_L_eq_ctn with  ct lb2 L_Label lb2 L_Label; auto.
      assert (join_label L_Label lb2  = join_label lb2 L_Label).
      apply join_label_commutative.
      rewrite <- H9; auto. 

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

      apply update_field_preserve_L_eq_ctns  with  ct lb2 L_Label lb2 L_Label; auto.
      assert (join_label L_Label lb2 =join_label lb2 L_Label).
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

    ++ inversion H24; subst; auto.
       unfold runtime_label in H1.
       unfold runtime_label in H15.
       assert (join_label lb lb2  =join_label lb2 lb).
       apply join_label_commutative.
       rewrite  H10 in H1; auto.
       rewrite  H10 in H15. auto.
       
       +++ (* v_opa_l low label *)
         exists φ. split; auto.
         apply update_field_preserve_bijection_new with ct lb lb lb2 lb2; auto.
         ++++
           inversion H6; subst; auto; inversion H29; subst; auto.
           right. destruct H45 as [F1]. destruct H25 as [lo1]. destruct H25 as [ll1].
           exists o1. exists cls_def1. exists F1. exists lo1. exists ll1. 
           split; auto.
           destruct H38 with v lb0; auto.           
         ++++
           inversion H6; subst; auto; inversion H29; subst; auto.
           right. destruct H45 as [F1]. destruct H25 as [lo1]. destruct H25 as [ll1].
           inversion H42; subst; auto.
           *
           exists o3. exists cls2. exists F3. exists lo2. exists ll2. 
           split; auto.

           *
           exists o3. exists cls2. exists F3. exists lo3. exists ll3. 
           split; auto.

           *
             inversion H42;subst; auto.
           *
             destruct H38 with v lb0; auto. 
         ++++
           inversion  H_valid1; subst;  auto.
           inversion H46; subst; auto.

           inversion  H_valid2; subst;  auto.
           inversion H56; subst; auto. 

           assert (forall a1 a2 : oid, decision.Decision (a1 = a2)). auto.
          
           apply L_equivalence_config_L; auto.
           apply update_field_preserve_L_eq_ctn with  ct lb2 lb lb2 lb; auto.
           apply update_field_preserve_L_eq_ctns  with  ct lb2 lb lb2 lb; auto.
       +++ (* v_opa_l hight label *)
          assert (join_label lb lb2 =join_label lb2 lb).
          apply join_label_commutative.

          exists φ. split; auto.
          *
          apply update_field_preserve_bijection_new with ct lb l2 lb2 lb2; auto.
         ++++
           inversion H6; subst; auto; inversion H29; subst; auto.
           right. destruct H45 as [F1]. destruct H25 as [lo1]. destruct H25 as [ll1]. 
           exists o1. exists cls_def1. exists F1. exists lo1. exists ll1. 
           split; auto.
           destruct H38 with v lb0; auto.           
         ++++
           inversion H30; subst; auto.
           inversion H45; subst; auto; inversion H40; subst; auto.
           destruct H49 as [F2].  destruct H25 as [lo2]. destruct H25 as [ll2].
           right. exists o1. exists cls_def1. exists F2. exists lo2. exists ll2. 
           split; auto.

           destruct H47 with v lb0; auto.

         ++++
           unfold runtime_label in H1. rewrite <- H10; auto.
         ++++
           unfold runtime_label in H15.
           assert (join_label l2 lb2 =join_label lb2 l2).
           apply join_label_commutative.
           rewrite <- H25; auto.
           *
           inversion  H_valid1; subst;  auto.
           inversion H46; subst; auto.
           inversion  H_valid2; subst;  auto.
           inversion H56; subst; auto.
           
           assert (forall a1 a2 : oid, decision.Decision (a1 = a2)). auto.
           apply L_equivalence_config_L; auto.
           apply update_field_preserve_L_eq_ctn with  ct lb2 lb lb2 l2; auto.

           assert (join_label lb2 lb =join_label lb lb2).
           apply join_label_commutative.
           rewrite H37. auto.
           unfold runtime_label in H1.

           assert (join_label lb2 l2 =join_label l2 lb2).
           apply join_label_commutative.
           rewrite H37. auto.
           unfold runtime_label in H15. 

           apply update_field_preserve_L_eq_ctns  with  ct lb2 lb lb2 l2; auto.
           assert (join_label lb2 lb =join_label lb lb2).
           apply join_label_commutative.
           rewrite H37. auto.

           assert (join_label lb2 l2 =join_label l2 lb2).
           apply join_label_commutative.
           rewrite H37. auto.
           
  
- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  (*L_eq_container (Container (FieldWrite (v_opa_l (ObjId o) ell) f v) fs1 lb1 sf1) h1
          (Container t2 fs2 lb2 sf2) h2 φ*)
  + invert_l_eq_ctn.
    invert_l_eq_tm.
    assert (value e). apply value_L_eq2 with  (v_opa_l (ObjId o) ell)  h1' h2'  φ; auto.
    apply v_opa_labeled; auto.
    intros. intro contra; inversion contra.
    contradiction.

  + invert_l_eq_ctn.
    invert_l_eq_tm.
    assert (value e2). apply value_L_eq2 with v h1' h2'  φ; auto.
    contradiction.
    
  +
    invert_l_eq_ctn.
    invert_l_eq_tm.
    inversion H12; subst; auto.
    ++
      exists φ. split; auto.
      assert (flow_to (join_label ell0 lb2) L_Label = true).
      apply join_L_label_flow_to_L; auto. 
      apply L_equivalence_config_L ; auto.

    ++
      exists φ. split; auto.
      assert (flow_to (join_label ell lb2) L_Label = false).
      apply flow_transitive with ell; auto.
      apply join_def_flow1; auto.

      assert (flow_to (join_label ell0 lb2) L_Label = false).
      apply flow_transitive with ell0; auto.
      apply join_def_flow1; auto.

      eauto using L_equivalence_config_H ; auto.
          

  
- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  (* L_eq_container (Container (If guard s1 s2) fs1 lb1 sf1) h1' (Container t2 fs2 lb2 sf2) h2 φ*)
  + invert_l_eq_ctn.
    invert_l_eq_tm.
    exists φ. split;  auto.
  
  + invert_l_eq_ctn.
    invert_l_eq_tm.
    assert (value guard).
    apply value_L_eq with (v_opa_l guard0 ell) h1' h2' φ; auto.
    contradiction.

  + invert_l_eq_ctn.
    invert_l_eq_tm.
    inversion H10; subst; auto.
    assert (value B_true); auto. 
    contradiction.

  + invert_l_eq_ctn.
    invert_l_eq_tm.
    inversion H10; subst; auto.
    intuition. 

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  + invert_l_eq_ctn.
    invert_l_eq_fs.
    invert_l_eq_tm.
    exists φ. split; auto.
  
  + invert_l_eq_ctn.
    invert_l_eq_fs.
    invert_l_eq_tm.
    inversion H4; subst; auto.
    inversion H12. 

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  + invert_l_eq_ctn.
    invert_l_eq_tm.
    assert (value guard0).
    apply value_L_eq2 with (v_opa_l guard ell) h1' h2' φ; auto.
    contradiction.

  + invert_l_eq_ctn.
    invert_l_eq_tm.
    inversion H11; subst; auto.
    exists φ. split; auto.
    ++
      assert (flow_to (join_label lb2 ell0) L_Label = true).
      apply join_L_label_flow_to_L; auto. 
      apply  L_equivalence_config_L; auto.
    ++
      exists φ. split; auto.
      assert (flow_to (join_label lb2 ell) L_Label = false).
      apply flow_transitive with ell; auto.
      apply join_def_flow2; auto.

      assert (flow_to (join_label lb2 ell0) L_Label = false).
      apply flow_transitive with ell0; auto.
      apply join_def_flow2; auto. 
      apply  L_equivalence_config_H; auto.

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  +
    invert_l_eq_ctn.
    invert_l_eq_tm.
    inversion H10; subst; auto. intuition. 

  +
    invert_l_eq_ctn.
    invert_l_eq_tm. 
    exists φ. auto.

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  + 
    invert_l_eq_ctn.
    invert_l_eq_tm.
    inversion H10; subst; auto.
    intuition.

  +
    invert_l_eq_ctn.
    invert_l_eq_tm.
    exists φ. split; auto.


- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  invert_l_eq_ctn.
  invert_l_eq_tm.
  exists φ. split; auto.

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  (*  L_eq_container (Container Skip (e :: fs) lb1 sf1) h1' (Container Skip (e0 :: fs0) lb2 sf2) h2' φ *)
  invert_l_eq_ctn.
  invert_l_eq_fs.
    exists φ. split; auto. 


- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn; fail).
  + invert_l_eq_ctn.
    invert_l_eq_fs.
    invert_l_eq_tm.
    inversion H6; subst; auto.
    inversion H0. 

  + invert_l_eq_ctn.
    invert_l_eq_fs.
    invert_l_eq_tm.
    inversion H12; subst; auto.
    inversion H0.
    case_eq ( hole_free e1 ); intro; rewrite H1 in H2; intuition.

  + invert_l_eq_ctn.
    invert_l_eq_fs.
    invert_l_eq_tm.
    inversion H8; subst; auto.
    inversion H0.

  + invert_l_eq_ctn.
    invert_l_eq_fs.
    invert_l_eq_tm.
    inversion H12; subst; auto.
    inversion H0. 

  + invert_l_eq_ctn.
    invert_l_eq_fs.
    invert_l_eq_tm.
    inversion H21; subst; auto.
    inversion H0.
    case_eq (hole_free e1); intro Hy; rewrite Hy in H2; intuition.

  +  invert_l_eq_ctn.
     invert_l_eq_fs.
     invert_l_eq_tm.
     inversion H6; subst; auto.
     inversion H0; subst; auto.

  +  invert_l_eq_ctn.
    invert_l_eq_fs.
    invert_l_eq_tm.
    inversion H5; subst; auto.
    inversion H0; subst; auto.

  +
    invert_l_eq_ctn.
    invert_l_eq_fs.
    invert_l_eq_tm.
    inversion H5; subst; auto.
    inversion H0; subst; auto. 

  + invert_l_eq_ctn.
    invert_l_eq_fs.
    invert_l_eq_tm.
    inversion H5; subst; auto.
    inversion H0. 
  
  + invert_l_eq_ctn.
    invert_l_eq_fs.
    invert_l_eq_tm.
    inversion H6; subst; auto.
    inversion H0. 


  + invert_l_eq_ctn.
    invert_l_eq_fs.
    invert_l_eq_tm.
    inversion H12; subst; auto.
    inversion H0.
    case_eq (hole_free e0); intro;
    rewrite H1 in H3; inversion H3. 
    
    
  + invert_l_eq_ctn.
    invert_l_eq_fs.
    invert_l_eq_tm.
    inversion H6; subst; auto.
    inversion H0.

  + invert_l_eq_ctn.
    invert_l_eq_fs.
    invert_l_eq_tm.
    inversion H7; subst; auto.
    inversion H0.
  
  
  + invert_l_eq_ctn.
    invert_l_eq_fs.
    invert_l_eq_tm.
    inversion H22; subst; auto.
  inversion H0. 
  case_eq ( hole_free e1 ); intro; rewrite H1 in H2; intuition.

  + invert_l_eq_ctn.
    invert_l_eq_fs.
    invert_l_eq_tm.
    inversion H7; subst; auto.
  inversion H0.
    
  + invert_l_eq_ctn.
    invert_l_eq_fs.
    exists φ.  split; auto.

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  + 
    inversion H18; subst; auto.
    inversion H17; subst; auto.
    inversion H10; subst; auto. 
    exists φ. split; auto. 
    apply  L_equivalence_config_L; auto.
    apply L_eq_ctn; auto.
    apply L_equivalence_tm_eq_v_opa_l_L; auto.

    apply v_opa_labeled; auto. intros.
    intro contra; subst; auto. 
    destruct H0 with v0 lb0; auto.
    inversion H; subst; auto.

    apply v_opa_labeled; auto. intros.
    intro contra; subst; auto. 
    destruct H13 with v0 lb0; auto.
     inversion H3; subst; auto. 

  + inversion H17; subst; auto.
    inversion H13; subst; auto.
    ++ destruct H0 with e1 ell; auto.
       inversion H4; auto. 
    ++ destruct H0 with e1 l1; auto.
       inversion H7; auto. 

- inversion H_reduction2; subst; auto; try (solve_by_invert_ctn).
  + inversion H15; subst; auto.
    inversion H13; subst; auto.
    ++ destruct H11 with e2 ell; auto.
       inversion H4; subst; auto. 
    ++ destruct H11 with e2 l2; auto.
       inversion H10; subst; auto.

  + inversion H16; subst; auto.
    inversion H15; subst; auto.
    inversion H6; subst; auto. 
    inversion H13; subst; auto.
    ++ exists φ. split; auto. 
       apply  L_equivalence_config_L; auto.
       apply L_eq_ctn; auto.
       assert (flow_to (join_label ell0 lb2) L_Label = true).
       apply join_L_label_flow_to_L; auto.
       apply  L_equivalence_tm_eq_v_opa_l_L; auto. 
       inversion H5; subst; auto.
       inversion H11; subst; auto.
       
    ++ exists φ. split; auto. 
       apply  L_equivalence_config_L; auto.
       apply L_eq_ctn; auto.
       assert (flow_to (join_label ell lb2) L_Label = false).
       apply flow_transitive with ell; auto.
       apply join_def_flow1; auto.

       assert (flow_to (join_label ell0 lb2) L_Label = false).
       apply flow_transitive with ell0; auto.
       apply join_def_flow1; auto. 

       apply L_equivalence_tm_eq_v_opa_l_H; auto.
       inversion H11; subst; auto.
       inversion H19; subst; auto.

 Qed.
Hint Resolve simulation_L.
 