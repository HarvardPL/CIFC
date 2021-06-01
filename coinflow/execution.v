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

Require Import preservation.

Require Import progress.


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
                       (Config ct (Container t2' fs2' lb2' sf2') ctns2' h2')
| finished_running_execution :  forall ct  t1 lb1 sf1 h1 
                           t2 fs2 lb2 sf2 ctns2 h2
                           t2' fs2' lb2' sf2' ctns2' h2', 
    terminal_state (Config ct (Container t1 nil lb1 sf1) nil h1) ->
    flow_to lb1 L_Label = false ->
    Config ct (Container t2 fs2 lb2 sf2) ctns2 h2 ==>
           Config ct (Container t2' fs2' lb2' sf2') ctns2' h2' ->
    flow_to lb2 L_Label = false ->
    flow_to lb2' L_Label = false ->
    parallel_reduction (Config ct (Container t1 nil lb1 sf1) nil h1)
                       (Config ct (Container t2 fs2 lb2 sf2) ctns2 h2)
                       (Config ct (Container t1 nil lb1 sf1) nil h1)
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
  inversion H_typing1; subst; auto.
  inversion H_typing2; subst; auto.
  inversion  H_p_execution; subst; auto;
    split; auto;
    try (eauto using typing_preservation).
Qed. Hint Resolve typing_preservation_p_reduction.

Lemma terminate_state_no_more_reduction : forall ct v lb sf h c,
    value v ->
    (Config ct (Container v nil lb sf) nil h) ==> c ->
    False.
Proof with eauto.
  intros. induction H; inversion H0.
Qed. Hint Resolve terminate_state_no_more_reduction.

Inductive multi_step_p_reduction : config -> config -> config -> config -> Prop :=
| multi_p_reduction_refl : forall config1 config2,
    multi_step_p_reduction config1 config2 config1 config2
| multi_p_reduction_step : forall c1 c1'  c2 c2'  c3 c3', 
                    parallel_reduction c1 c1' c2 c2' ->
                    multi_step_p_reduction c2 c2' c3 c3' ->
                    multi_step_p_reduction c1 c1' c3 c3'.                        
Hint Constructors multi_step_p_reduction. 



Inductive  terminate_num : config -> config  -> nat ->  Prop :=
| terminate_zero : forall ctn ct h,
    terminal_state (Config ct ctn nil h) -> 
    terminate_num (Config ct ctn nil h)
                  (Config ct ctn nil h)
                  0
| terminate_step : forall ctn1 ctns1  final_ctn  ct h1  n ctn1' ctns1' h1' h_final_1,
    (Config ct ctn1 ctns1 h1) ==>
                              (Config ct ctn1' ctns1' h1') ->
    terminal_state (Config ct final_ctn nil h_final_1) ->
    terminate_num (Config ct ctn1' ctns1'  h1')
                  (Config ct final_ctn nil h_final_1)
                  n ->
     terminate_num (Config ct ctn1 ctns1 h1)                
                   (Config ct final_ctn nil h_final_1)
                   (1 + n) .
Hint Constructors terminate_num.

Inductive  two_terminate_num : config -> config -> config -> config -> nat ->  Prop :=
| two_terminate_zero : forall final_ctn1 h_final_1 final_ctn2 h_final_2 ct,
    terminal_state (Config ct final_ctn1 nil h_final_1) ->
    terminal_state (Config ct final_ctn2 nil h_final_2) -> 
    two_terminate_num (Config ct final_ctn1 nil h_final_1)
                  (Config ct final_ctn2 nil h_final_2)
                  (Config ct final_ctn1 nil h_final_1)
                  (Config ct final_ctn2 nil h_final_2)
                  0
| two_terminate_first : forall ctn1 ctn2 ctns1 ctns2 ct
                               final_ctn1 final_ctn2 n ctn1' ctns1' h1'
                               h_final_1 h_final_2 h1 h2,
    (Config ct ctn1 ctns1 h1) ==>
                              (Config ct ctn1' ctns1' h1') ->
    terminal_state (Config ct final_ctn1 nil h_final_1) ->
    terminal_state (Config ct final_ctn2 nil h_final_2) -> 
    two_terminate_num (Config ct ctn1' ctns1'  h1')
                  (Config ct ctn2 ctns2 h2)
                  (Config ct final_ctn1 nil h_final_1)
                  (Config ct final_ctn2 nil h_final_2)
                  n ->
    two_terminate_num (Config ct ctn1 ctns1 h1)
                  (Config ct ctn2 ctns2 h2)
                  (Config ct final_ctn1 nil h_final_1)
                  (Config ct final_ctn2 nil h_final_2)
                  (1 + n) 
                  
| two_terminate_second : forall ctn1 ctn2 ctns1 ctns2 ct final_ctn1 h1 final_ctn2 h2 n ctn2' ctns2' h2'
  h_final_1 h_final_2,
    (Config ct ctn2 ctns2 h2) ==>
                              (Config ct ctn2' ctns2' h2') ->
    terminal_state (Config ct final_ctn1 nil h_final_1) ->
    terminal_state (Config ct final_ctn2 nil h_final_2) ->
    two_terminate_num (Config ct ctn1 ctns1 h1)
                  (Config ct ctn2' ctns2' h2')
                  (Config ct final_ctn1 nil h_final_1)
                  (Config ct final_ctn2 nil h_final_2)
                  n ->
    two_terminate_num (Config ct ctn1 ctns1 h1)
                  (Config ct ctn2 ctns2 h2)
                  (Config ct final_ctn1 nil h_final_1)
                  (Config ct final_ctn2 nil h_final_2)
                  (1 + n) 
                  
| two_terminate_both : forall ctn1 ctn2 ctns1 ctns2 ct final_ctn1 h1 final_ctn2 h2 n
                            ctn1' ctns1' h1'
                            ctn2' ctns2' h2'
  h_final_1 h_final_2,
    (Config ct ctn2 ctns2 h2) ==>
                              (Config ct ctn2' ctns2' h2') ->
    (Config ct ctn1 ctns1 h1) ==>
                              (Config ct ctn1' ctns1' h1') ->
    terminal_state (Config ct final_ctn1 nil h_final_1) ->
    terminal_state (Config ct final_ctn2 nil h_final_2) ->
        two_terminate_num (Config ct ctn1' ctns1' h1')
                  (Config ct ctn2' ctns2' h2')
                  (Config ct final_ctn1 nil h_final_1)
                  (Config ct final_ctn2 nil h_final_2)
                  n ->
        two_terminate_num (Config ct ctn1 ctns1 h1)
                  (Config ct ctn2 ctns2 h2)
                  (Config ct final_ctn1 nil h_final_1)
                  (Config ct final_ctn2 nil h_final_2)
                  (2 + n)  . 
Hint Constructors   two_terminate_num.

Require Import deterministic. 

Lemma execution_no_exception : forall ct ctn ctns h config'
                                      final_ctn h_final n,
    terminate_num (Config ct ctn ctns h)
                  (Config ct final_ctn nil h_final)
                  n ->
    (Config ct ctn ctns h) ==> config' ->
    exists ctn' ctns' h', config' = 
                          (Config ct ctn' ctns' h').
Proof with eauto.
  intros ct ctn ctns h config'
         final_ctn h_final n.
  intro H_run. intro H_reduction.
  inversion H_run; subst; auto.
  + inversion H6; subst; auto.
    induction H0; subst; inversion H_reduction; auto.

  + 
    assert ( (Config ct ctn1' ctns1' h1') = config').
    eauto using deterministic_prime.
    exists ctn1'. exists ctns1'. exists h1'. auto. 
Qed. Hint Resolve execution_no_exception.     

Lemma addition_exchange : (forall m n, m + (1 + n) = 1 + m + n).
  intros. simpl.
  induction m; auto.
Qed. Hint Resolve addition_exchange.


Lemma addition_exchange_all :  (forall m n, m + n = n + m).
  intros. induction m; auto.
  simpl. rewrite IHm.
  simpl. induction n ;auto.
Qed. Hint Resolve  addition_exchange_all. 
  

Lemma two_executions_split : forall ct ctn1 ctns1 h1 ctn2 ctns2 h2
                                     final_ctn1 h_final_1
                                     final_ctn2 h_final_2 k,
    two_terminate_num (Config ct ctn1 ctns1 h1)
                  (Config ct ctn2 ctns2 h2)
                  (Config ct final_ctn1 nil h_final_1)
                  (Config ct final_ctn2 nil h_final_2)
                  k ->
    exists m n, terminate_num (Config ct ctn1 ctns1 h1)
                  (Config ct final_ctn1 nil h_final_1)
                  m /\
                terminate_num (Config ct ctn2 ctns2 h2)
                  (Config ct final_ctn2 nil h_final_2)
                  n /\ (m + n = k).
Proof with eauto.
  intros ct ctn1 ctns1 h1 ctn2 ctns2 h2
                                     final_ctn1 h_final_1
                                     final_ctn2 h_final_2 k.
  intro Hy.
  generalize dependent ctn1. generalize dependent ctns1.
  generalize dependent h1.
  generalize dependent ctn2. generalize dependent ctns2.
  generalize dependent h2.
  generalize dependent k.
  induction k as [ k IHk ] using (well_founded_induction lt_wf).
  + intros. inversion Hy; subst; auto.
    ++ exists 0. exists 0. split; auto.
    ++  assert (exists m0 n0 : nat,
          terminate_num (Config ct ctn1' ctns1' h1') (Config ct final_ctn1 nil h_final_1) m0 /\
          terminate_num (Config ct ctn2 ctns2 h2) (Config ct final_ctn2 nil h_final_2) n0 /\ (m0 + n0 = n)).
        apply IHk; auto.
        destruct H as [m0]. destruct H as [n0].  
        destruct H. exists (1 + m0). exists n0. split; auto.
        apply terminate_step with ctn1' ctns1' h1'; auto.
        destruct H0. split; auto. simpl. rewrite H1. auto. 
    ++ apply IHk in H14; auto. destruct H14 as [m0].
       destruct H as [n0].
       destruct H. destruct H0. 
       exists  m0. exists (1 + n0).
       split; auto.
       split; auto.        
       apply terminate_step with ctn2' ctns2' h2'; auto.
       pose proof addition_exchange m0 n0.
       rewrite H2. simpl. rewrite H1. auto. 
    ++ apply IHk in H15; auto. destruct H15 as [m0].
       destruct H as [n0].
       destruct H. destruct H0. 
       exists  ( 1 + m0). exists (1 + n0).
       split; auto.
       apply terminate_step with ctn1' ctns1' h1'; auto.
       split; auto. 
       apply terminate_step with ctn2' ctns2' h2'; auto.
       pose proof addition_exchange (1 + m0) n0.
       rewrite H2.
       pose proof addition_exchange 1 m0.
       rewrite H3. 
       assert (1 + 1 =2 ). simpl. auto. 
       rewrite H4. simpl. rewrite H1. auto. 
       
       assert (forall n, n < 1 + n). auto.
       pose proof H n. pose proof H (1 + n).
       apply lt_trans with (1 + n); auto.
Qed. Hint Resolve two_executions_split.     


Lemma execution_num_step : forall ct ctn ctns h final_ctn h_final
                                  ctn' ctns' h' n,
    terminate_num (Config ct ctn ctns h)
                  (Config ct final_ctn nil h_final)
                  n ->
    (Config ct ctn ctns h) ==> (Config ct ctn' ctns' h') ->
    terminate_num (Config ct ctn' ctns' h')
                  (Config ct final_ctn nil h_final)
                  (n - 1).
Proof with eauto.
  intros.
  inversion H; subst; auto.
  inversion H8; subst; auto.
  inversion H2; subst; auto; inversion H0. 
  assert (1 + n0 -1 = n0).
  induction n0; auto.
  rewrite H1.
  assert (ctn' = ctn1' /\ ctns' = ctns1' /\ h' = h1').
  eauto using deterministic.
  destruct H2. destruct H3. subst; auto.
Qed. Hint Resolve execution_num_step.



Lemma execution_num_step_nonzero : forall ct ctn ctns h final_ctn h_final
                                  ctn' ctns' h' n,
    terminate_num (Config ct ctn ctns h)
                  (Config ct final_ctn nil h_final)
                  n ->
    (Config ct ctn ctns h) ==> (Config ct ctn' ctns' h') ->
    exists m, 1 + m = n . 
Proof with eauto.
  intros.
  inversion H; subst; auto.
  inversion H8; subst; auto.
  inversion H2; subst; auto; inversion H0.
  exists n0. auto.
Qed. Hint Resolve execution_num_step_nonzero.


Lemma two_executions_to_one : forall ct ctn1 ctns1 h1 ctn2 ctns2 h2
                                     final_ctn1 h_final_1
                                     final_ctn2 h_final_2 m n,
    terminate_num (Config ct ctn1 ctns1 h1)
                  (Config ct final_ctn1 nil h_final_1)
                  m ->
    terminate_num (Config ct ctn2 ctns2 h2)
                  (Config ct final_ctn2 nil h_final_2)
                  n -> 
    two_terminate_num (Config ct ctn1 ctns1 h1)
                  (Config ct ctn2 ctns2 h2)
                  (Config ct final_ctn1 nil h_final_1)
                  (Config ct final_ctn2 nil h_final_2)
                  (m+n).
Proof with eauto.
  intros ct ctn1 ctns1 h1 ctn2 ctns2 h2
         final_ctn1 h_final_1
         final_ctn2 h_final_2 m n.
  intro H_run1. intro H_run2.
  generalize dependent ctn1. generalize dependent ctns1.
  generalize dependent h1. generalize dependent m.
  induction m; auto. intros. 
  inversion H_run1; subst; auto.


  - assert (forall n, 0 + n = n). auto.
    pose proof H n. rewrite H1.
    generalize dependent ctn2. generalize dependent ctns2.
    generalize dependent h2. generalize dependent n.
    induction n; auto; intros.
    inversion H_run2; subst; auto.
    inversion H_run2; subst; auto.
    apply two_terminate_second with ctn1' ctns1' h1'; auto.
    
  - intros. inversion H_run1; subst; auto.
    apply  two_terminate_first with ctn1' ctns1' h1'; auto.
    inversion H_run2; auto.    
Qed. Hint Resolve two_executions_to_one.



Lemma minus_zero : forall m, m - 0 = m.
  intros. induction m; auto.
Qed. Hint Resolve minus_zero. 

  
Lemma two_executions_split_first : forall ctn1 ctns1 h1
                                          ct ctn1' ctns1' h1'
                                          ctn2 ctns2 h2
                                     final_ctn1 h_final_1
                                     final_ctn2 h_final_2 k,
    two_terminate_num (Config ct ctn1 ctns1 h1)
                  (Config ct ctn2 ctns2 h2)
                  (Config ct final_ctn1 nil h_final_1)
                  (Config ct final_ctn2 nil h_final_2)
                  (1 + k) ->
    (Config ct ctn1 ctns1 h1) ==> (Config ct ctn1' ctns1' h1') ->
    two_terminate_num (Config ct ctn1' ctns1' h1')
                  (Config ct ctn2 ctns2 h2)
                  (Config ct final_ctn1 nil h_final_1)
                  (Config ct final_ctn2 nil h_final_2)
                  k.
Proof with eauto.
  intros.
  assert (exists m n, terminate_num (Config ct ctn1 ctns1 h1)
                  (Config ct final_ctn1 nil h_final_1)
                  m /\
                terminate_num (Config ct ctn2 ctns2 h2)
                  (Config ct final_ctn2 nil h_final_2)
                  n /\ (m + n =  1 + k)).
  eauto using two_executions_split.
  destruct H1 as [m0]. destruct H1 as [n0].
  destruct H1.  destruct H2. 
  assert (terminate_num (Config ct ctn1' ctns1' h1')
                  (Config ct final_ctn1 nil h_final_1)
                  (m0 - 1)). 
  eauto using execution_num_step.
  assert (exists m1, 1 + m1 = m0).
  eauto using execution_num_step_nonzero.
  destruct H5 as [m1].
  rewrite <- H5 in H1.
  rewrite <- H5 in H4.
  simpl in H4. pose proof  minus_zero m1.
  rewrite H6 in H4. 
  assert (two_terminate_num (Config ct ctn1' ctns1' h1') (Config ct ctn2 ctns2 h2)
                            (Config ct final_ctn1 nil h_final_1) (Config ct final_ctn2 nil h_final_2)
                            (m1 + n0)).
  apply  two_executions_to_one; auto.
  assert (m1 + n0 = k).
  rewrite <- H5 in H3. simpl in H3. inversion H3; auto.
  rewrite <- H8. auto. 
Qed. Hint Resolve two_executions_split_first. 


(* if the first run already terminated, and its label is H, then the other run must be H run *)
Lemma terminate_H_must_2H : forall ct t1 lb1 sf1 h1
                                            
                                            ctn2 ctns2 h2  sf2' lb2' fs2'
                                            t2' ctns2' h2'
                                             T  φ ,
    valid_config (Config ct (Container t1 nil lb1 sf1) nil h1) ->
    valid_config (Config ct ctn2 ctns2 h2) ->
    config_has_type ct empty_context (Config ct (Container t1 nil lb1 sf1) nil h1) T ->
    config_has_type ct empty_context (Config ct ctn2 ctns2 h2) T ->
    terminal_state (Config ct (Container t1 nil lb1 sf1) nil h1) ->
    L_equivalence_config (Config ct (Container t1 nil lb1 sf1) nil h1 )
                         (Config ct ctn2 ctns2 h2)  φ ->
    L_equivalence_heap h1 h2 φ ->
    Config ct ctn2 ctns2 h2 ==>
           Config ct (Container t2' fs2' lb2' sf2') ctns2' h2' ->
    flow_to lb1 L_Label = false ->
    flow_to lb2' L_Label = false.
Proof. intros ct t1 lb1 sf1 h1
              ctn2 ctns2 h2  sf2' lb2' fs2'
              t2' ctns2' h2'
              T  φ.
       intro H_valid1. intro H_valid2.
       intro H_typing1. intro H_typing2.
       intro H_terminal1.
       intro H_low_eq. intro H_low_heap.
       intro H_reduction2.
       intro H_flow1.
       remember (Config ct ctn2 ctns2 h2) as config. 
       remember (Config ct (Container t2' fs2' lb2' sf2') ctns2' h2') as config'.
       generalize dependent t1.  generalize dependent lb1. 
       generalize dependent h1. 
       generalize dependent ctns2. generalize dependent h2. 
       generalize dependent sf1. 
       induction H_reduction2; intros; auto; inversion Heqconfig; inversion Heqconfig'; subst; auto;
         inversion H_low_eq; subst; auto;
                      try (inconsist_label).
       - apply flow_transitive with (join_label lo lb); auto.
         apply flow_transitive with lb; auto.
         apply join_def_flow2.
         apply join_def_flow1.
         
       - apply flow_transitive with (join_label (join_label lo lb) ell); auto.
         apply flow_transitive with (join_label lo lb); auto.
         apply flow_transitive with lb; auto.
         apply join_def_flow2.
         apply join_def_flow1.
         apply join_def_flow1.

       - apply flow_transitive with lb; auto.
         apply join_def_flow1.

       - apply flow_transitive with (join_label lb ell); auto.
         apply flow_transitive with lb; auto.
         apply join_def_flow1.
         apply join_def_flow1.

       -
         apply flow_transitive with lb; auto.
         apply join_def_flow1.

       -
         apply flow_transitive with lb; auto.
         apply join_def_flow1.


       -
         apply flow_transitive with lb; auto.
         apply join_def_flow1.

       -
         apply flow_transitive with lb; auto.
         apply join_def_flow1.
         
       -
         apply flow_transitive with lb; auto.
         apply join_def_flow2.

       -
         apply flow_transitive with (join_label lb ell); auto.
         apply flow_transitive with lb; auto.
         apply join_def_flow1.
         apply join_def_flow2.

       -
         apply flow_transitive with lb; auto.
         apply join_def_flow1.

       -
         apply flow_transitive with lb; auto.
         apply join_def_flow1.
         
       -
         apply flow_transitive with lb; auto.
         apply join_def_flow1.         

       - unfold low_component in H18.
         rewrite H16 in H18. rewrite H17 in H18.

         destruct ctns2'. 
         case_eq ( flow_to lb2' L_Label); intro.
         rewrite H1 in H18. inversion H18; subst; auto.
         inversion H21; subst; auto.
         inversion H14; subst; auto.
         inversion H_valid2; subst; auto.
         inversion H8; subst; auto.

         (* hole cannot be typed *)
         inversion H_typing2; subst; auto.
         inversion H27; subst; auto.
         inversion H29; subst; auto.
         inversion H30. 
         auto. 
         case_eq ( flow_to lb2' L_Label); intro.
         rewrite H1 in H18; inversion H18; subst; auto.
         inversion H21; auto; subst; auto. inversion H14; subst; auto.
         inversion H_typing2; subst; auto.
         inversion H10; subst; auto.
         inversion H12; subst; auto.
         inversion H23.         
         auto.

        - unfold low_component in H16.
         rewrite H14 in H16. rewrite H15 in H16.
         destruct ctns2'. 
         case_eq ( flow_to lb2' L_Label); intro.
         rewrite H in H16. inversion H16; subst; auto.
         inversion H19; subst; auto. inversion H12; subst; auto.
         inversion H_typing2; subst; auto.
         inversion H8; subst; auto.
         inversion H10; subst; auto.
         inversion H21.
         auto.

         
         case_eq ( flow_to lb2' L_Label); intro.
         rewrite H in H16. inversion H16; subst; auto.
         inversion H19; subst; auto. inversion H12; subst; auto.
         inversion H_typing2; subst; auto.
         inversion H8; subst; auto.
         inversion H10; subst; auto.
         inversion H21.
         
         auto.              
Qed. Hint Resolve  terminate_H_must_2H.


(* if the second run already terminated, and its label is H, then the other run must be H run *)
Lemma H_terminate_must_2H : forall ct t2 lb2 sf2 h2
                                   ctn1 ctns1 h1  sf1' lb1' fs1'
                                   t1' ctns1' h1'
                                             T  φ ,
    valid_config (Config ct ctn1 ctns1 h1) ->
    valid_config (Config ct  (Container t2 nil lb2 sf2) nil h2) ->
    config_has_type ct empty_context  (Config ct ctn1 ctns1 h1)  T ->
    config_has_type ct empty_context (Config ct  (Container t2 nil lb2 sf2) nil h2)  T ->
    terminal_state (Config ct  (Container t2 nil lb2 sf2) nil h2) ->
    L_equivalence_config (Config ct ctn1 ctns1 h1 )
                         (Config ct  (Container t2 nil lb2 sf2) nil h2)  φ ->
    L_equivalence_heap h1 h2 φ ->
    Config ct ctn1 ctns1 h1 ==>
           Config ct (Container t1' fs1' lb1' sf1') ctns1' h1' ->
    flow_to lb2 L_Label = false ->
    flow_to lb1' L_Label = false.
Proof. intros ct t2 lb2 sf2 h2
              ctn1 ctns1 h1  sf1' lb1' fs1'
              t1' ctns1' h1'
              T  φ .
       intro H_valid1. intro H_valid2.
       intro H_typing1. intro H_typing2.
       intro H_terminal2.
       intro H_low_eq. intro H_low_heap.
       intro H_reduction1.
       intro H_flow2.
       remember (Config ct ctn1 ctns1 h1 ) as config. 
       remember (Config ct (Container t1' fs1' lb1' sf1') ctns1' h1') as config'.
       generalize dependent t2.  generalize dependent lb2. 
       generalize dependent h2. 
       generalize dependent ctns1. generalize dependent h1. 
       generalize dependent sf2. 
       induction H_reduction1; intros; auto; inversion Heqconfig; inversion Heqconfig'; subst; auto;
         inversion H_low_eq; subst; auto;
           try (inconsist_label); try (apply flow_transitive with lb; auto; try (apply join_def_flow1; fail); try (apply join_def_flow2; fail); fail). 
       - apply flow_transitive with (join_label lo lb); auto.
         apply flow_transitive with lb; auto.
         apply join_def_flow2.
         apply join_def_flow1. 
       - apply flow_transitive with (join_label lo lb); auto.
         apply flow_transitive with lb; auto.
         apply join_def_flow2.
         apply flow_trans with (join_label (join_label lo lb) ell).
         apply join_def_flow1.
         apply join_def_flow1.

       - apply flow_transitive with (join_label lb ell); auto.
         apply flow_transitive with lb; auto.
         apply join_def_flow1.
         apply join_def_flow1.


       - apply flow_transitive with (join_label lb ell); auto.
         apply flow_transitive with lb; auto.
         apply join_def_flow1.
         apply join_def_flow2.

       - unfold low_component in H18.
         rewrite H16 in H18. rewrite H17 in H18.

         destruct ctns1'. 
         case_eq ( flow_to lb1' L_Label); intro.
         rewrite H1 in H18. inversion H18; subst; auto. inversion H21; subst; auto. inversion H14; subst; auto.

         inversion H_typing1; subst; auto.
         inversion H10; subst; auto.
         inversion H12; subst; auto.
         inversion H23.        
         auto. 
         case_eq ( flow_to lb1' L_Label); intro.
         rewrite H1 in H18; inversion H18; subst; auto. inversion H21; auto; subst; auto. inversion H14.
         inversion H_typing1; subst; auto.
         inversion H24; subst; auto.
         inversion H9; subst; auto.
         inversion H10.        
         auto.

        - unfold low_component in H16.
         rewrite H14 in H16. rewrite H15 in H16.
         destruct ctns1'. 
         case_eq ( flow_to lb1' L_Label); intro.
         rewrite H in H16. inversion H16; subst; auto.
         inversion H19; subst; auto.
         inversion H12; subst; auto.
         inversion H_typing1; subst; auto.
         inversion H8; subst; auto.
         inversion H10; subst; auto.
         inversion H21.        

         auto. 
         case_eq ( flow_to lb1' L_Label); intro.
         rewrite H in H16. inversion H16; subst; auto.
         inversion H19; subst; auto.
         inversion H12; subst; auto.
         inversion H_typing1; subst; auto.
         inversion H8; subst; auto.
         inversion H10; subst; auto.
         inversion H21.        
         auto.
Qed. Hint Resolve  H_terminate_must_2H.





Lemma terminating_run_no_exception : forall final_v1 lb1' sf1' h1'
                                            final_v2 lb2' sf2' h2'
                                            config2'
                                            ct ctn1 ctns1 h1
                                            ctn2 ctns2 h2
                                            n,

    Config ct ctn2 ctns2 h2 ==> config2' ->
    terminal_state (Config ct (Container final_v1 nil lb1' sf1') nil h1') ->
    terminal_state (Config ct (Container final_v2 nil lb2' sf2') nil h2') ->
    two_terminate_num (Config ct ctn1 ctns1 h1)
                      (Config ct ctn2 ctns2 h2)
                      (Config ct (Container final_v1 nil lb1' sf1') nil h1')
                      (Config ct (Container final_v2 nil lb2' sf2') nil h2') n ->
    exists ctn' ctns' h', config2' =  (Config ct ctn' ctns' h').

Proof with eauto.
  intros final_v1 lb1' sf1' h1' final_v2 lb2' sf2' h2'
         config2' ct ctn1 ctns1 h1
         ctn2 ctns2 h2  n.
  intro H_reduction2. intro H_terminate1. intro H_terminate2.
  intro H_two_reduction.
  assert (exists m0 n0, terminate_num (Config ct ctn1 ctns1 h1)
                                    (Config ct (Container final_v1 nil lb1' sf1') nil h1')
                                    m0 /\
                      terminate_num (Config ct ctn2 ctns2 h2)
                                    (Config ct (Container final_v2 nil lb2' sf2') nil h2')
                                    n0 /\ (m0 + n0 = n)).
  eauto using two_executions_split .
  destruct H as [m']. destruct H as [n'].
  destruct H.   destruct H0.      
  inversion H_two_reduction; subst; auto.         
  + inversion H15; subst; auto.
    inversion H2; subst; auto; inversion H_reduction2; subst; auto.
  + apply execution_no_exception with ctn2 ctns2 h2  (Container final_v2 nil lb2' sf2')
                                      h2' n'; auto.
  + apply execution_no_exception with ctn2 ctns2 h2  (Container final_v2 nil lb2' sf2')
                                      h2' n'; auto.
  + apply execution_no_exception with ctn2 ctns2 h2  (Container final_v2 nil lb2' sf2')
                                      h2' n'; auto.
Qed. Hint Resolve terminating_run_no_exception.


Lemma terminated_both_p_reduction : forall ct ctn1 ctns1 h1
                                           ctn2 ctns2 h2 n
                                           final_ctn1  final_ctn2 h1' h2', 
    terminal_state (Config ct ctn1 ctns1 h1) -> 
    terminal_state (Config ct ctn2 ctns2 h2) ->
    two_terminate_num (Config ct ctn1 ctns1 h1)
                      (Config ct ctn2 ctns2 h2)
                      (Config ct final_ctn1 nil h1')
                      (Config ct final_ctn2 nil h2') n ->                               
  multi_step_p_reduction (Config ct ctn1 ctns1 h1)
                         (Config ct ctn2 ctns2 h2)
                         (Config ct final_ctn1 nil h1')
                         (Config ct final_ctn2 nil h2').
Proof with eauto.
  intros.
  inversion H1; subst; auto.
  + inversion H; subst; auto.
    inversion H3; subst; auto; inversion H14.
  + inversion H0; subst; auto.
    inversion H3; subst; auto; inversion H14.
  + inversion H; subst; auto.
    inversion H3; subst; auto; inversion H15.
Qed. Hint Resolve terminated_both_p_reduction. 


Lemma lt_addition_plus1 : forall m n,
    m + n < m + (1 + n).
Proof with eauto.
  intros. induction m; auto. simpl.
  apply lt_n_S. auto.
Qed. Hint Resolve   lt_addition_plus1.


Lemma terminated_same_as_final : forall ct ctn ctns h final_v lb sf h' n, 
    terminal_state (Config ct ctn ctns h) ->
    terminate_num (Config ct ctn ctns h)
                  (Config ct (Container final_v nil lb sf) nil h') n ->
    (Config ct ctn ctns h) = (Config ct (Container final_v nil lb sf) nil h').
Proof with eauto.
  intros.
  inversion H0; subst; auto.
  inversion H; subst; auto. 
  inversion H2; subst; auto; inversion H8. 
Qed. Hint Resolve   terminated_same_as_final.
