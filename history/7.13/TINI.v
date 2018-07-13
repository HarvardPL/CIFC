
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
Require Import simulation_full.
Require Import preservation.
Require Import Simulation_L.

Inductive parallel_reduction : config -> config -> config -> config -> Prop :=
| L_L_reduction : forall ct t1 fs1 lb1 sf1 ctns1 h1
                         t2 fs2 lb2 sf2  ctns2 h2
                         t1' fs1' lb1' sf1' ctns1' h1'
                         t2' fs2' lb2' sf2' ctns2' h2', 
    Config ct (Container t1 fs1 lb1 sf1) ctns1 h1 ==>
           Config ct (Container t1' fs1' lb1' sf1') ctns1' h1' ->
    flow_to lb1 L_Label = true ->
    Config ct (Container t2 fs2 lb2 sf2) ctns2 h2 ==>
           Config ct (Container t2' fs2' lb2' sf2') ctns2' h2' ->
    flow_to lb2 L_Label = true ->
    parallel_reduction (Config ct (Container t1 fs1 lb1 sf1) ctns1 h1)
                       (Config ct (Container t2 fs2 lb2 sf2) ctns2 h2)
                       (Config ct (Container t1' fs1' lb1' sf1') ctns1' h1') (Config ct (Container t2' fs2' lb2' sf2') ctns2' h2')
| H2H_H_reduction : forall ct t1 fs1 lb1 sf1 ctns1 h1
                           t1' fs1' lb1' sf1' ctns1' h1'
                           t2 fs2 lb2 sf2 ctns2 h2,
    Config ct (Container t1 fs1 lb1 sf1) ctns1 h1 ==>
           Config ct (Container t1' fs1' lb1' sf1') ctns1' h1' ->
    flow_to lb1 L_Label = false ->
    flow_to lb1' L_Label = false ->
    flow_to lb2 L_Label = false ->
    parallel_reduction (Config ct (Container t1 fs1 lb1 sf1) ctns1 h1)
                       (Config ct (Container t2 fs2 lb2 sf2) ctns2 h2)
                       (Config ct (Container t1' fs1' lb1' sf1') ctns1' h1')
                       (Config ct (Container t2 fs2 lb2 sf2) ctns2 h2)
| H2L_H2H_reduction : forall ct t1 fs1 lb1 sf1 ctns1 h1
                           t1' fs1' lb1' sf1' ctns1' h1'
                           t2 fs2 lb2 sf2 ctns2 h2
                           t2' fs2' lb2' sf2' ctns2' h2', 
    Config ct (Container t1 fs1 lb1 sf1) ctns1 h1 ==>
           Config ct (Container t1' fs1' lb1' sf1') ctns1' h1' ->
    flow_to lb1 L_Label = false ->
    flow_to lb1' L_Label = true ->
    Config ct (Container t2 fs2 lb2 sf2) ctns2 h2 ==>
           Config ct (Container t2' fs2' lb2' sf2') ctns2' h2' ->
    flow_to lb2 L_Label = false ->
    flow_to lb2' L_Label = false ->
    parallel_reduction (Config ct (Container t1 fs1 lb1 sf1) ctns1 h1)
                       (Config ct (Container t2 fs2 lb2 sf2) ctns2 h2)
                       (Config ct (Container t1 fs1 lb1 sf1) ctns1 h1)
                       (Config ct (Container t2' fs2' lb2' sf2') ctns2' h2')
| H2L_H2L_reduction : forall ct t1 fs1 lb1 sf1 ctns1 h1
                           t1' fs1' lb1' sf1' ctns1' h1'
                           t2 fs2 lb2 sf2 ctns2 h2
                           t2' fs2' lb2' sf2' ctns2' h2', 
    Config ct (Container t1 fs1 lb1 sf1) ctns1 h1 ==>
           Config ct (Container t1' fs1' lb1' sf1') ctns1' h1' ->
    flow_to lb1 L_Label = false ->
    flow_to lb1' L_Label = true ->
    Config ct (Container t2 fs2 lb2 sf2) ctns2 h2 ==>
           Config ct (Container t2' fs2' lb2' sf2') ctns2' h2' ->
    flow_to lb2 L_Label = false ->
    flow_to lb2' L_Label = true ->
    parallel_reduction (Config ct (Container t1 fs1 lb1 sf1) ctns1 h1)
                       (Config ct (Container t2 fs2 lb2 sf2) ctns2 h2)
                       (Config ct (Container t1' fs1' lb1' sf1') ctns1' h1')
                       (Config ct (Container t2' fs2' lb2' sf2') ctns2' h2').
Hint Constructors parallel_reduction.

Lemma ct_consist_p_reduction : forall ct1 ctn1 ctns1 h1
  ct2 ctn2 ctns2 h2 ct1' ctn1' ctns1' h1' ct2' ctn2' ctns2' h2' ,
    parallel_reduction (Config ct1 ctn1 ctns1 h1)
                       (Config ct2 ctn2 ctns2 h2)
                       (Config ct1' ctn1' ctns1' h1')
                       (Config ct2' ctn2' ctns2' h2') ->
    ct1 = ct2 /\ ct1 = ct1' /\ ct1 = ct2'.
Proof with eauto.
  intros. inversion H; subst; auto.
Qed. Hint Resolve ct_consist_p_reduction.

(*
Lemma p_reduction_deterministic : forall c c' c1 c1' c2 c2',
    parallel_reduction c  c' c1 c1' ->
    parallel_reduction c  c' c2 c2' ->
    c1 = c2 /\ c1' = c2'.
Proof with eauto.
  intros. induction c; try (inversion H; fail). induction c1; try (inversion H; fail). induction c2; try (inversion H; fail); try (inversion H0; fail).
  induction c'; try (inversion H; fail).
  induction c1';  try (inversion H; fail).
  induction c2';  try (inversion H0; fail).
  assert (c = c5 /\ c = c1 /\ c = c7).
  try (eauto using ct_consist_p_reduction).
  assert (c = c5 /\ c = c2 /\ c = c9).
  try (eauto using ct_consist_p_reduction).
  destruct H1. destruct H3. destruct H2. destruct H4. destruct H5;  subst; auto.
  rename c9 into ct.
  destruct c0. destruct c6.
  rename l5 into lb1. rename l6 into lb2. 
  case_eq (flow_to lb1 L_Label); intro.
  case_eq (flow_to lb2 L_Label); intro.
  induction H; subst; auto.
  induction H0; subst; auto.
  assert (ct1 = ct0).
  try (eauto using ct_consist ). subst; auto.
  pose proof (reduction_determinacy
                (Config ct0 (Container t3 fs0 lb4 sf0) ctns0 h7)
                (Config ct0 (Container t1' fs1' lb1' sf1') ctns1' h1')
                (Config ct0 (Container t1'0 fs1'0 lb1'0 sf1'0) ctns1'0 h1'0)
                H H0). inversion H10; subst; auto.
Admitted.
 *)

Inductive multi_step_p_reduction : config -> config -> config -> config -> Prop :=
| multi_p_reduction_refl : forall config1 config2,
    multi_step_p_reduction config1 config2 config1 config2
| multi_p_reduction_step : forall c1 c1'  c2 c2'  c3 c3', 
                    parallel_reduction c1 c1' c2 c2' ->
                    multi_step_p_reduction c2 c2' c3 c3' ->
                    multi_step_p_reduction c1 c1' c3 c3'.                        
Hint Constructors multi_step_p_reduction. 

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
Qed. Hint Resolve low_eq_preservation.
    
Lemma valid_config_after_p_reduction : forall ct  ctn1 ctns1 h1 ctn2 ctns2 h2
                                   ctn1' ctns1' h1'
                                   ctn2' ctns2' h2'  T,
    valid_config (Config ct  ctn1 ctns1 h1 ) ->
    valid_config (Config ct  ctn2 ctns2 h2 ) ->
    config_has_type ct empty_context (Config ct ctn1  ctns1 h1) T ->
    config_has_type ct empty_context (Config ct ctn2  ctns2 h2) T ->
    parallel_reduction (Config ct ctn1 ctns1 h1)
                           (Config ct ctn2 ctns2 h2)
                           (Config ct ctn1' ctns1' h1')
                           (Config ct ctn2' ctns2' h2') ->
    valid_config (Config ct  ctn1' ctns1' h1' ) /\  valid_config (Config ct  ctn2' ctns2' h2' ) .
Proof with eauto.
  intros ct  ctn1 ctns1 h1 ctn2 ctns2 h2 ctn1' ctns1' h1' ctn2' ctns2' h2' T.
  intro H_valid1. intro H_valid2.
  intro H_typing1. intro H_typing2.  
  intro H_p_execution.
  inversion  H_p_execution; subst; auto.
  assert (valid_config (Config ct (Container t1' fs1' lb1' sf1') ctns1' h1')).
  try (eauto using valid_config_preservation).
  assert (valid_config (Config ct (Container t2' fs2' lb2' sf2') ctns2' h2')).
  try (eauto using valid_config_preservation).
  split; auto.

  assert (valid_config (Config ct (Container t1' fs1' lb1' sf1') ctns1' h1')).
  try (eauto using valid_config_preservation).  
  split; auto. 

  assert (valid_config (Config ct (Container t2' fs2' lb2' sf2') ctns2' h2')).
  try (eauto using valid_config_preservation).
  split; auto.
  
  assert (valid_config (Config ct (Container t1' fs1' lb1' sf1') ctns1' h1')).
  try (eauto using valid_config_preservation).
  assert (valid_config (Config ct (Container t2' fs2' lb2' sf2') ctns2' h2')).
  try (eauto using valid_config_preservation).
  split; auto.
Qed. Hint Resolve   valid_config_after_p_reduction.


    
Lemma typing_preservation_p_reduction : forall ct  ctn1 ctns1 h1 ctn2 ctns2 h2
                                   ctn1' ctns1' h1'
                                   ctn2' ctns2' h2'  T,
    valid_config (Config ct  ctn1 ctns1 h1 ) ->
    valid_config (Config ct  ctn2 ctns2 h2 ) ->
    config_has_type ct empty_context (Config ct ctn1  ctns1 h1) T ->
    config_has_type ct empty_context (Config ct ctn2  ctns2 h2) T ->
    parallel_reduction (Config ct ctn1 ctns1 h1)
                           (Config ct ctn2 ctns2 h2)
                           (Config ct ctn1' ctns1' h1')
                           (Config ct ctn2' ctns2' h2') ->
    (config_has_type ct  empty_context (Config ct ctn1'  ctns1' h1') T  ) /\
    (config_has_type ct  empty_context (Config ct ctn2'  ctns2' h2') T  ).
Proof with eauto.
  intros ct  ctn1 ctns1 h1 ctn2 ctns2 h2 ctn1' ctns1' h1' ctn2' ctns2' h2' T.
  intro H_valid1. intro H_valid2.
  intro H_typing1. intro H_typing2.  
  intro H_p_execution.
  inversion  H_p_execution; subst; auto.
  assert (config_has_type ct empty_context (Config ct (Container t1' fs1' lb1' sf1') ctns1' h1') T).
  try (eauto using typing_preservation).
  assert (config_has_type ct empty_context (Config ct (Container t2' fs2' lb2' sf2') ctns2' h2') T).
  try (eauto using typing_preservation).
  split; auto.

   assert (config_has_type ct empty_context (Config ct (Container t1' fs1' lb1' sf1') ctns1' h1') T).
  try (eauto using typing_preservation).
  split; auto. 

  assert (config_has_type ct empty_context (Config ct (Container t2' fs2' lb2' sf2') ctns2' h2') T).
  try (eauto using typing_preservation).
  split; auto.
  
  assert (config_has_type ct empty_context (Config ct (Container t1' fs1' lb1' sf1') ctns1' h1') T).
  try (eauto using typing_preservation).
  assert (config_has_type ct empty_context (Config ct (Container t2' fs2' lb2' sf2') ctns2' h2') T).
  try (eauto using typing_preservation).
  split; auto.
Qed. Hint Resolve typing_preservation_p_reduction.

Lemma NI : forall ct ctn1 ctns_stack1 h1 ctn2 ctns_stack2 h2 lb1' sf1' lb2' sf2' final_v1  final_v2  h1' h2' φ T, 
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
Qed. 
  


  