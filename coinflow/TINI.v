
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.

Require Import Language Types.
Require Import Lemmas.
Require Import Low_eq.
Require Import Label.

Require Import Simulation_L.
Require Import simulation_full.
Require Import preservation.
Require Import execution. 

Require Import progress.




Lemma low_eq_preservation : forall ct  ctn1 ctns1 h1 ctn2 ctns2 h2
                                   ctn1' ctns1' h1'
                                   ctn2' ctns2' h2' φ T,
    valid_config (Config ct  ctn1 ctns1 h1 ) ->
    valid_config (Config ct  ctn2 ctns2 h2 ) ->
    config_has_type ct empty_context (Config ct ctn1  ctns1 h1) T ->
    config_has_type ct empty_context (Config ct ctn2  ctns2 h2) T ->
    L_equivalence_heap h1 h2 φ ->
    parallel_reduction (Config ct ctn1 ctns1 h1)
                           (Config ct ctn2 ctns2 h2)
                           (Config ct ctn1' ctns1' h1')
                           (Config ct ctn2' ctns2' h2') ->
     L_equivalence_config (Config ct ctn1 ctns1 h1 )
                          (Config ct ctn2 ctns2 h2)  φ ->

          exists  φ', (L_equivalence_heap h1' h2'  φ')  /\ L_equivalence_config (Config ct ctn1' ctns1' h1')  (Config ct ctn2' ctns2' h2')  φ'.
Proof with eauto.
  intros  ct  ctn1 ctns1 h1 ctn2 ctns2 h2 ctn1' ctns1' h1' ctn2' ctns2' h2'  φ  T. 
  intro H_valid1. intro H_valid2.
  intro H_typing1. intro H_typing2.
  intro H_bijection.
  intro H_p_execution. 
  intro H_low_eq. 

  inversion H_p_execution; subst; auto.
  -
    apply  simulation_L with t1 fs1 lb1 sf1 ctns1 h1
                             t2 fs2 lb2 sf2 ctns2 h2
                             φ T; auto; inversion H_valid1; inversion H_valid2; auto.   

  - try (eauto using simulation_H2H_H).
  - try (eauto using simulation_H_H2H).
  - try (eauto using simulation_H2L_H2L).
  - 
    try (eauto using simulation_Terminal_H2H).
Qed. Hint Resolve low_eq_preservation.











  
  


Lemma two_exes_to_parallel_execution : forall ct ctn1 ctns_stack1 h1
                                                    ctn2 ctns_stack2 h2 lb1' sf1' lb2' sf2'
                                                    final_v1  final_v2  h1' h2' T  φ n, 
    valid_config (Config ct  ctn1 ctns_stack1 h1 ) ->
    valid_config (Config ct  ctn2 ctns_stack2 h2 ) ->
    config_has_type ct empty_context (Config ct ctn1  ctns_stack1 h1) T ->
    config_has_type ct empty_context (Config ct ctn2  ctns_stack2 h2) T ->
    two_terminate_num (Config ct ctn1 ctns_stack1 h1)
                  (Config ct ctn2 ctns_stack2 h2)
                  (Config ct (Container final_v1 nil lb1' sf1') nil h1')
                  (Config ct (Container final_v2 nil lb2' sf2') nil h2')
                  n ->
    L_equivalence_config (Config ct ctn1 ctns_stack1 h1 )
            (Config ct ctn2 ctns_stack2 h2)  φ ->
    value final_v1 -> value final_v2 ->
    L_equivalence_heap h1 h2 φ ->
    multi_step_p_reduction (Config ct ctn1 ctns_stack1 h1)
                           (Config ct ctn2 ctns_stack2 h2)
                           (Config ct (Container final_v1 nil lb1' sf1') nil h1')
                           (Config ct (Container final_v2 nil lb2' sf2') nil h2') .
Proof with eauto.
  intros ct ctn1 ctns_stack1 h1
         ctn2 ctns_stack2 h2 lb1' sf1' lb2' sf2'
         final_v1  final_v2  h1' h2' T  φ n.
  intro H_valid1. intro H_valid2.
  intro H_typing1. intro H_typing2.
  intro H_reduction.
  intro H_low_eq.
  intro Hv_final1. intro Hv_final2.
  intro H_bijection.
(*
  remember (Config ct ctn1 ctns_stack1 h1) as config1.
  remember (Config ct ctn2 ctns_stack2 h2) as config2.
  *)
  generalize dependent ctn1. generalize dependent ctn2.
  generalize dependent ctns_stack1. generalize dependent ctns_stack2.
  generalize dependent h1. generalize dependent h2. generalize dependent  φ.

  induction n as [ n IHn ] using (well_founded_induction lt_wf).
  intros; subst; auto.

  destruct ctn1. rename l into lb1. rename f into fs1. rename s into sf1. rename t into t1. 
  destruct ctn2. rename l into lb2. rename f into fs2. rename s into sf2. rename t into t2. 

  assert  (terminal_state  (Config ct (Container t1 fs1 lb1 sf1) ctns_stack1 h1)
             \/ (exists config', (Config ct (Container t1 fs1 lb1 sf1) ctns_stack1 h1) ==> config')).
  eauto using Progress.

  assert  (terminal_state  (Config ct (Container t2 fs2 lb2 sf2) ctns_stack2 h2)
             \/ (exists config', (Config ct (Container t2 fs2 lb2 sf2) ctns_stack2 h2) ==> config')).
  eauto using Progress.

  assert (exists m0 n0, terminate_num (Config ct (Container t1 fs1 lb1 sf1) ctns_stack1 h1)
                                        (Config ct (Container final_v1 nil lb1' sf1') nil h1')
                                        m0 /\
                        terminate_num (Config ct (Container t2 fs2 lb2 sf2) ctns_stack2 h2)
                                        (Config ct (Container final_v2 nil lb2' sf2') nil h2')
                                        n0 /\ (m0 + n0 = n)).
  eauto using two_executions_split.
  destruct H1 as [m0].
  destruct H1 as [n0].
  destruct H1.
  destruct H2.
  
  case_eq (flow_to lb1 L_Label); intro.
  - (* conf1 is a low configuration  *)
    destruct H.
    + (* conf1 already terminated *)
      assert ((Config ct (Container t1 fs1 lb1 sf1) ctns_stack1 h1)
                  = (Config ct (Container final_v1 nil lb1' sf1') nil h1')).
      eauto using terminated_same_as_final.
      destruct H0.
      ++ (*conf2 also terminated *)        
        assert ((Config ct (Container t2 fs2 lb2 sf2) ctns_stack2 h2)
                  = (Config ct (Container final_v2 nil lb2' sf2') nil h2')).
        eauto using terminated_same_as_final.
        inversion H5; subst; auto.
        inversion H6; subst; auto.
      ++ (*conf2 steps; this is impossible*)
         inversion H_low_eq; subst; auto;
           try (inconsist).

         inversion H5; subst; auto.
         inversion H21; subst; auto.
         
         inversion H22; subst; auto.
         inversion H17; subst; auto.
         destruct H0 as [config2'].
         inversion H; subst; auto.
         
         assert (value t2).
         apply value_L_eq2 with final_v1 h1' h2 φ; auto.
         inversion H3; subst; auto; inversion H0.

    + (* conf1 steps *)
      destruct H as [config1'].
      destruct H0.
      ++ (*conf2 terminated; this is impossible *)  
        assert ((Config ct (Container t2 fs2 lb2 sf2) ctns_stack2 h2)
                  = (Config ct (Container final_v2 nil lb2' sf2') nil h2')).
        eauto using terminated_same_as_final.
        inversion H5; subst; auto.
        inversion H_low_eq; subst; auto;
           try (inconsist).
        inversion H20; subst; auto.
        inversion H21; subst; auto.

        inversion H17; subst; auto.
        inversion H0; subst; auto.
        assert (value t1).
        apply value_L_eq with final_v2 h1 h2' φ; auto.
        inversion H3; subst; auto; inversion H.
      ++ (*conf2 steps*)
        destruct H0 as [config2'].
        assert (exists ctn' ctns' h', config1' = 
                                      (Config ct ctn' ctns' h')).
        eauto using execution_no_exception.
        assert (exists ctn' ctns' h', config2' = 
                                      (Config ct ctn' ctns' h')).
        eauto using execution_no_exception.
        destruct H5 as [ctn1'].
        destruct H5 as [ctns1'].
        destruct H5 as [h1'0]; subst; auto.
        destruct H6 as [ctn2'].
        destruct H3 as [ctns2'].
        destruct H3 as [h2'0]; subst; auto.
        inversion H_low_eq; subst; auto;
          try (inconsist).
        destruct ctn1'. destruct ctn2'.
        assert (exists  φ', L_equivalence_heap h1'0 h2'0 φ'
                /\ L_equivalence_config (Config ct (Container t f l s) ctns1' h1'0)
                                        (Config ct (Container t0 f0 l0 s0) ctns2' h2'0) φ'); auto.
        eauto using  simulation_L; auto.
        destruct H3 as [φ'].
        destruct H3.         
        apply multi_p_reduction_step with
              (Config ct (Container t f l s) ctns1' h1'0)
              (Config ct (Container t0 f0 l0 s0) ctns2' h2'0).
        eauto using L_L_reduction.
        assert (exists m0', 1 + m0' = m0).
        eauto using execution_num_step_nonzero.
        destruct H6 as [m0'].
        assert (exists n0', 1 + n0' = n0).
        eauto using execution_num_step_nonzero.
        destruct H7 as [n0'].
        rewrite <- H6 in H1.
        rewrite <- H7 in H2.
        apply IHn with (m0' + n0')  φ'; auto; try (apply H5).
        rewrite <- H6. rewrite <- H7.
        assert (forall n, n < 1 + n). auto.
        pose proof H8 (n0').
        apply lt_trans with (m0' + (1 + n0')); auto.

        eauto using valid_config_preservation.
        inversion H_typing2; subst; auto.
        eauto using typing_preservation.
        eauto using valid_config_preservation.
        inversion H_typing1; subst; auto.
        eauto using typing_preservation.

        assert (forall n, 1 + n -1 = n).
        intros. induction n; auto.       
        assert (terminate_num (Config ct (Container t f l s) ctns1' h1'0)
                                     (Config ct (Container final_v1 nil lb1' sf1') nil h1')
                                     (1 + m0' - 1)).
        eauto using execution_num_step.

        assert (terminate_num (Config ct (Container t0 f0 l0 s0) ctns2' h2'0)
                                     (Config ct (Container final_v2 nil lb2' sf2') nil h2')
                                     (1 + n0' - 1)).
        eauto using execution_num_step.
        pose proof H8 m0'. rewrite H11 in H9.
        pose proof H8 n0'. rewrite H12 in H10.
        auto.

  - (* conf1 is a high configuration  *)
    inversion H_low_eq; subst; auto.
    try (inconsist).

    destruct H.
    (* first configuration is terminated *)
    + destruct H0.
      ++ (* conf2 also terminated *)
        eauto using terminated_both_p_reduction.

      ++ (* conf2 steps *)
        destruct H0 as [config2'].
        assert (exists ctn' ctns' h', config2' = 
                                      (Config ct ctn' ctns' h')).
        eauto using execution_no_exception.
        destruct H3 as [ctn2'].
        destruct H3 as [ctns2'].
        destruct H3 as [h2'0]; subst; auto.
        destruct ctn2'.
        case_eq (flow_to l L_Label); intro.
        +++ (*conf2 steps to a low configuration*)
          assert (flow_to l L_Label = false).
          inversion H; subst; auto. 
          apply terminate_H_must_2H with ct t1 lb1 sf1 h1
                                         (Container t2 fs2 lb2 sf2)  ctns_stack2 h2 s f t ctns2' h2'0 T φ; auto.
          try (inconsist).
        +++ (*conf2 steps to a high configuration*)
          assert (L_equivalence_heap h1 h2'0 φ /\ L_equivalence_config (Config ct (Container t1 fs1 lb1 sf1) ctns_stack1 h1)
                                                                          (Config ct (Container t f l s) ctns2' h2'0 )  φ); auto.
          eauto using  simulation_H_H2H; auto.
          apply multi_p_reduction_step with
              (Config ct (Container t1 fs1 lb1 sf1) ctns_stack1 h1)
              (Config ct (Container t f l s) ctns2' h2'0).
          assert ((Config ct (Container t1 fs1 lb1 sf1) ctns_stack1 h1)
                  = (Config ct (Container final_v1 nil lb1' sf1') nil h1')).
          eauto using terminated_same_as_final.
          inversion H6; subst; auto.
          assert (exists n0', 1 + n0' = n0).
          eauto using execution_num_step_nonzero.
          destruct H6 as [n0'].
          rewrite <- H6 in H2. 
          apply IHn with (m0 + n0')  φ ; auto; try (apply H5).
          ++++ pose proof addition_exchange_all 1 n0'.
               rewrite H7 in H6. rewrite <-H6.
               rewrite <- H7.
               apply lt_addition_plus1. 
          ++++ eauto using valid_config_preservation.
          ++++
            inversion H_typing2. eauto using typing_preservation.
          ++++ assert (terminate_num (Config ct (Container t f l s) ctns2' h2'0)
                                     (Config ct (Container final_v2 nil lb2' sf2') nil h2') 
                                     (1 + n0' - 1)).
               eauto using execution_num_step.
               assert (forall n, 1 + n -1 = n).
               intros. induction n; auto.
               pose proof H8 n0'.
               rewrite H9 in H7; auto.
    + (* first configuration steps  *)
      destruct H as [config1'].
      assert (exists ctn' ctns' h', config1' = 
                                      (Config ct ctn' ctns' h')).
      eauto using execution_no_exception.
      destruct H3 as [ctn1'].
      destruct H3 as [ctns1'].
      destruct H3 as [h1'0]; subst; auto.
      destruct ctn1'.
      case_eq (flow_to l L_Label); intro.
      ++ (* conf1 steps to a low configuration *)
        destruct H0.
        +++ (*conf2 terminated; impossible case*)
          assert (flow_to l L_Label = false).
          inversion H0; subst; auto.
          eauto using H_terminate_must_2H.
          try (inconsist).
        +++ (*conf2 steps *)
          destruct H0 as [config2'].
          assert (exists ctn' ctns' h', config2' = 
                                      (Config ct ctn' ctns' h')).
          eauto using execution_no_exception.
          destruct H5 as [ctn2'].
          destruct H5 as [ctns2'].
          destruct H5 as [h2'0]; subst; auto.
          destruct ctn2'.
          case_eq (flow_to l0 L_Label); intro.
          ++++ (* conf2 steps into low configuration  *)
             assert (L_equivalence_heap h1'0 h2'0 φ /\ L_equivalence_config (Config ct (Container t f l s) ctns1' h1'0)
                                                                         ( Config ct (Container t0 f0 l0 s0) ctns2' h2'0)  φ); auto.
             eauto using simulation_H2L_H2L.
             destruct H6.
             apply multi_p_reduction_step with
                 (Config ct (Container t f l s) ctns1' h1'0)
                 ( Config ct (Container t0 f0 l0 s0) ctns2' h2'0).
             eauto using H2L_H2L_reduction. 
             assert (exists m0', 1 + m0' = m0).
             eauto using execution_num_step_nonzero.
             destruct H8 as [m0'].
             assert (exists n0', 1 + n0' = n0).
             eauto using execution_num_step_nonzero.
             destruct H9 as [n0'].
             rewrite <- H8 in H1.
             rewrite <- H9 in H2.
             apply IHn with (m0' + n0')  φ; auto; try (apply H7).
             rewrite <- H8. rewrite <- H9.
             assert (forall n, n < 1 + n). auto.
             pose proof H10 (n0').
             apply lt_trans with (m0' + (1 + n0')); auto.

             eauto using valid_config_preservation.
             inversion H_typing2; subst; auto. 
             eauto using typing_preservation.

             eauto using valid_config_preservation.
             inversion H_typing1; subst; auto. 
             eauto using typing_preservation.

             assert (forall n, 1 + n -1 = n).
             intros. induction n; auto.       
             assert (terminate_num (Config ct (Container t f l s) ctns1' h1'0)
                                     (Config ct (Container final_v1 nil lb1' sf1') nil h1')
                                     (1 + m0' - 1)).
             eauto using execution_num_step.

             assert (terminate_num (Config ct (Container t0 f0 l0 s0) ctns2' h2'0)
                                     (Config ct (Container final_v2 nil lb2' sf2') nil h2')
                                     (1 + n0' - 1)).
             eauto using execution_num_step.
             pose proof H10 m0'. rewrite H13 in H11.
             pose proof H10 n0'. rewrite H14 in H12.
             auto. 

          ++++ (* conf2 steps into high configuration *)
            assert (L_equivalence_heap h1 h2'0 φ /\ L_equivalence_config (Config ct (Container t1 fs1 lb1 sf1) ctns_stack1 h1)
                                                                         ( Config ct (Container t0 f0 l0 s0) ctns2' h2'0)  φ); auto.
            eauto using simulation_H_H2H.
            destruct H6.
            apply multi_p_reduction_step with
              (Config ct (Container t1 fs1 lb1 sf1) ctns_stack1 h1)
              ( Config ct (Container t0 f0 l0 s0) ctns2' h2'0).
            eauto using H2L_H2H_reduction. 
            assert (exists n0', 1 + n0' = n0).
            eauto using execution_num_step_nonzero.

            destruct H8 as [n0'].
            rewrite <- H8 in H2. 
            apply IHn with (m0 + n0')  φ ; auto; try (apply H7).            
          +++++ rewrite <- H8; auto. 
          +++++ eauto using valid_config_preservation.
          +++++ inversion H_typing2; subst; auto.
          eauto using typing_preservation.
          +++++ assert (terminate_num (Config ct (Container t0 f0 l0 s0) ctns2' h2'0)
                                     (Config ct (Container final_v2 nil lb2' sf2') nil h2') 
                                     (1 + n0' - 1)).
          eauto using execution_num_step.
          assert (forall n, 1 + n -1 = n).
          intros. induction n; auto.
          pose proof H10 n0'.
          rewrite H11 in H9; auto.   
        
      ++ (* conf1 steps to a high configuration *)
         assert (L_equivalence_heap h1'0 h2 φ /\  L_equivalence_config (Config ct (Container t f l s) ctns1' h1'0)
                                                                       (Config ct (Container t2 fs2 lb2 sf2) ctns_stack2 h2 )  φ).
         eauto using  simulation_H2H_H; auto.
         apply multi_p_reduction_step with
              (Config ct (Container t f l s) ctns1' h1'0)
              (Config ct (Container t2 fs2 lb2 sf2) ctns_stack2 h2).
         apply H2H_H_reduction; auto. 
         assert (exists m0', 1 + m0' = m0).
         eauto using execution_num_step_nonzero.
         destruct H6 as [m0'].
         rewrite <- H6 in H1. 
         apply IHn with (m0' + n0)  φ; auto; try (apply H5).
         +++ rewrite <- H6. simpl.
             assert (forall n, n < S n).
             induction n; auto.
             pose proof H7 (m0' + n0); auto.
         +++ eauto using valid_config_preservation.
         +++ inversion H_typing1; subst; auto. 
           eauto using typing_preservation.
         +++ assert (terminate_num (Config ct (Container t f l s) ctns1' h1'0)
                                     (Config ct (Container final_v1 nil lb1' sf1') nil h1')
                                     (1 + m0' - 1)).
               eauto using execution_num_step.
               assert (forall n, 1 + n -1 = n).
               intros. induction n; auto.
               pose proof H8 m0'.
               rewrite H9 in H7; auto.
Qed. Hint Resolve  two_exes_to_parallel_execution.



Lemma p_reduction_NI : forall ct ctn1 ctns_stack1 h1 ctn2 ctns_stack2 h2 lb1' sf1' lb2' sf2' final_v1  final_v2  h1' h2' φ T, 
    valid_config (Config ct  ctn1 ctns_stack1 h1 ) ->
    valid_config (Config ct  ctn2 ctns_stack2 h2 ) ->
    config_has_type ct empty_context (Config ct ctn1  ctns_stack1 h1) T ->
    config_has_type ct empty_context (Config ct ctn2  ctns_stack2 h2) T ->
    multi_step_p_reduction (Config ct ctn1 ctns_stack1 h1)
                           (Config ct ctn2 ctns_stack2 h2)
                           (Config ct (Container final_v1 nil lb1' sf1') nil h1')
                           (Config ct (Container final_v2 nil lb2' sf2') nil h2') ->
     L_equivalence_config (Config ct ctn1 ctns_stack1 h1 )
            (Config ct ctn2 ctns_stack2 h2)  φ ->
     value final_v1 -> value final_v2 ->
     L_equivalence_heap h1 h2 φ ->
     exists  φ', L_equivalence_config (Config ct (Container final_v1 nil lb1' sf1') nil h1')  (Config ct (Container final_v2 nil lb2' sf2') nil h2')  φ'.
Proof with eauto.
  intros ct ctn1 ctns_stack1 h1 ctn2 ctns_stack2 h2 lb1' sf1' lb2' sf2' final_v1  final_v2  h1' h2' φ T. 
  intro H_valid1. intro H_valid2.
  intro H_typing1. intro H_typing2.
  intro H_p_execution.
  intro H_low_eq. intro Hv_final1. intro Hv_final2.
  intro H_bijection.
  remember  (Config ct ctn1 ctns_stack1 h1) as config1.
  remember  (Config ct ctn2 ctns_stack2 h2) as config2.
  generalize dependent ctn1.   generalize dependent ctn2.
  generalize dependent ctns_stack1.   generalize dependent ctns_stack2.
  generalize dependent h1.   generalize dependent h2.
  generalize dependent T. generalize dependent φ. 
  induction   H_p_execution; intros; inversion   Heqconfig1; inversion   Heqconfig2; subst; auto. 
  exists φ.  auto.
  induction c2; try (inversion H; fail). 
  induction c2'; try (inversion H; fail).
  assert (ct = ct /\ ct = c /\ ct = c1).
  try (eauto using ct_consist_p_reduction).
  destruct H2. destruct H3. subst; auto. rename c1 into ct.

  assert (valid_config ( (Config ct c0 l h)) /\  valid_config (Config ct c2 l0 h0) ).
  try (eauto using valid_config_after_p_reduction).
  destruct H3.
  assert (exists φ', L_equivalence_heap h h0 φ' /\  L_equivalence_config (Config ct c0 l h) (Config ct c2 l0 h0) φ').
  eauto using low_eq_preservation.
  destruct H5 as [φ'].
  destruct H5. 

  assert ((config_has_type ct  empty_context ((Config ct c0 l h)) T  ) /\
          (config_has_type ct  empty_context (Config ct c2 l0 h0) T  )).
  apply typing_preservation_p_reduction with ctn1 ctns_stack1 h1 ctn2 ctns_stack2 h2; auto.
  destruct H7. 
  apply IHH_p_execution with φ' T h0 h l0 l c2 c0; auto; auto.
Qed. Hint Resolve  p_reduction_NI. 



Theorem TINI : forall ct ctn1 ctns1 h1 ctn2 ctns2 h2 lb1' sf1' lb2' sf2' final_v1  final_v2  h1' h2' φ T m n, 
    valid_config (Config ct  ctn1 ctns1 h1 ) ->
    valid_config (Config ct  ctn2 ctns2 h2 ) ->
    config_has_type ct empty_context (Config ct ctn1  ctns1 h1) T ->
    config_has_type ct empty_context (Config ct ctn2  ctns2 h2) T ->
    terminate_num (Config ct ctn1 ctns1 h1)
                  (Config ct (Container final_v1 nil lb1' sf1') nil h1')
                  m ->
    terminate_num (Config ct ctn2 ctns2 h2)
                  (Config ct (Container final_v2 nil lb2' sf2') nil h2') 
                  n -> 
    L_equivalence_config (Config ct ctn1 ctns1 h1 )
            (Config ct ctn2 ctns2 h2)  φ ->
    value final_v1 -> value final_v2 ->
     L_equivalence_heap h1 h2 φ ->
     exists  φ', L_equivalence_config (Config ct (Container final_v1 nil lb1' sf1') nil h1')  (Config ct (Container final_v2 nil lb2' sf2') nil h2')  φ'.
Proof with eauto.
  intros  ct ctn1 ctns1 h1 ctn2 ctns2 h2 lb1' sf1' lb2' sf2' final_v1  final_v2  h1' h2' φ T m n.
  intro H_valid1. intro H_valid2.
  intro H_typing1. intro H_typing2.
  intro H_execution1. intro H_execution2. 
  intro H_low_eq. intro Hv_final1. intro Hv_final2.
  intro H_bijection.
  assert (two_terminate_num (Config ct ctn1 ctns1 h1)
                  (Config ct ctn2 ctns2 h2)
                  (Config ct (Container final_v1 nil lb1' sf1') nil h1')
                  (Config ct (Container final_v2 nil lb2' sf2') nil h2')
                  (m+n)).
  eauto using  two_executions_to_one.
  assert (multi_step_p_reduction (Config ct ctn1 ctns1 h1)
                           (Config ct ctn2 ctns2 h2)
                           (Config ct (Container final_v1 nil lb1' sf1') nil h1')
                           (Config ct (Container final_v2 nil lb2' sf2') nil h2') ).
  eauto using two_exes_to_parallel_execution.
  eauto using p_reduction_NI.
Qed. 






