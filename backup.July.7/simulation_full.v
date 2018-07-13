Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.

Require Import Language.
Require Import Lemmas.
Require Import Low_eq.
Require Import Label.


Lemma simulation_H2H_H : forall ct t1 fs1 lb1 sf1 ctns1 h1
                              t2 fs2 lb2 sf2 ctns2 h2 
                              t1' fs1' lb1' sf1' ctns1' h1' φ, 
      valid_config (Config ct (Container t1 fs1 lb1 sf1) ctns1 h1 ) ->
      valid_config (Config ct (Container t2 fs2 lb2 sf2) ctns2 h2 ) ->
(*      config_has_type ct empty_context (Config ct (Container t1 fs1 lb1 sf1)  ctns1 h1) T ->
      config_has_type ct empty_context (Config ct (Container t2 fs2 lb2 sf2)  ctns2 h2) T -> *)
      Config ct (Container t1 fs1 lb1 sf1) ctns1 h1
             ==> Config ct (Container t1' fs1' lb1' sf1') ctns1' h1' ->
      flow_to lb1 L_Label = false ->
      flow_to lb2 L_Label = false ->
      flow_to lb1' L_Label = false ->
      L_equivalence_config (Config ct (Container t1 fs1 lb1 sf1) ctns1 h1 )
            (Config ct (Container t2 fs2 lb2 sf2) ctns2 h2)  φ ->
     L_equivalence_heap h1 h2 φ ->
     L_equivalence_heap h1' h2 φ /\  L_equivalence_config (Config ct (Container t1' fs1' lb1' sf1') ctns1' h1')
                          (Config ct (Container t2 fs2 lb2 sf2) ctns2 h2 )  φ.
Proof with eauto.
  intros ct t1 fs1 lb1 sf1 ctns1 h1
         t2 fs2 lb2 sf2 ctns2 h2 
         t1' fs1' lb1' sf1' ctns1' h1' φ (*T*).
  intro H_valid1.       intro H_valid2.
(*  intro H_typing1. intro H_typing2.*)
  intro H_reduction1. 
  intro H_flow1. intro H_flow2. intro H_flow1'.
  intro H_low_eq.    
  intro H_bijection.
  remember (Config ct (Container t1 fs1 lb1 sf1) ctns1 h1) as config1. 
  remember (Config ct (Container t1' fs1' lb1' sf1') ctns1' h1') as config1'.
  generalize dependent t1. generalize dependent fs1. generalize dependent lb1. 
  generalize dependent ctns1. generalize dependent h1. 

  generalize dependent t2. generalize dependent fs2. generalize dependent lb2. 
  generalize dependent ctns2. generalize dependent h2. 

  (*generalize dependent T. *)
  generalize dependent sf1. generalize dependent sf2.
  induction H_reduction1; intros; auto; inversion Heqconfig1; inversion Heqconfig1'; subst;
    inversion H_low_eq; subst; 
  try( match goal with
    | H : flow_to ?T L_Label = true |- _
      =>  solve [ try (rewrite H_flow1 in H; inversion H; fail); try (rewrite H_flow2 in H; inversion H; fail)]
  end);   

   try (split; auto;
         match goal with
         | H : L_equivalence_config _ _ _  |- _ 
           => unfold low_component in H; subst; auto;
              destruct ctns1'; destruct ctns2;
              rewrite H_flow1 in H; rewrite H_flow2 in H;
              apply L_equivalence_config_H; auto; 
              unfold low_component; subst; auto;
              rewrite H_flow1; rewrite H_flow2; auto  
         end
       ).
(* field access *)
  - split; auto.
    assert (flow_to (join_label lo lb1) L_Label = false).
    apply flow_join_label with lb1 lo; auto. 
    unfold low_component in H18; subst; auto;
      destruct ctns1'; destruct ctns2;
        rewrite H_flow1 in H18; rewrite H_flow2 in H18;
          apply L_equivalence_config_H; auto; 
            unfold low_component; subst; auto; rewrite H1; auto;
              rewrite H_flow2; auto .
(* (MethodCall (ObjId o) meth v)  *)
  - split; auto.
    unfold low_component in H19; subst; auto;
      destruct ctns1; destruct ctns2;
        rewrite H_flow1 in H19; rewrite H_flow2 in H19;
          apply L_equivalence_config_H; auto; 
            unfold low_component; subst; auto; rewrite H_flow1; auto;
              rewrite H_flow2; auto .

  (* (MethodCall (ObjId o) meth (v_opa_l v lx)) )  *)
  - split; auto.
    assert (flow_to (join_label lb1 lx) L_Label = false).
    apply flow_join_label with lb1 lx; auto.
    apply join_label_commutative. 
    unfold low_component in H19; subst; auto;
      destruct ctns1; destruct ctns2;
        rewrite H_flow1 in H19; rewrite H_flow2 in H19;
          apply L_equivalence_config_H; auto; 
            unfold low_component; subst; auto; rewrite H0; auto;
              rewrite H_flow1; rewrite H_flow2;  auto .
(*new exp*)
  - split; auto.
    apply extend_h1_with_H_preserve_bijection with ct ;auto.
    inversion H_valid1; auto. 

    apply extend_h1_with_H_preserve_config_eq; auto.
    inversion H_valid1; subst; auto. 
    apply  valid_conf; auto.
    inversion H8; subst; auto.

    apply L_equivalence_config_H; auto.
    destruct ctns1'.
    unfold low_component in H17.
    unfold low_component.
    rewrite H15. rewrite H15 in H17. auto.
    unfold low_component in H17.
    unfold low_component.
    rewrite H15. rewrite H15 in H17. auto.


  - split; auto.
    assert (flow_to (join_label lb1 lo) L_Label = false).
    apply flow_join_label with lb1 lo; auto.
    apply join_label_commutative. 
    unfold low_component in H17; subst; auto;
      destruct ctns1'; destruct ctns2;
        rewrite H_flow1 in H17; rewrite H_flow2 in H17;
          apply L_equivalence_config_H; auto; 
            unfold low_component; subst; auto; rewrite H; auto;
               rewrite H_flow2;  auto .

  - split; auto.
    assert (flow_to (join_label lb1 lo) L_Label = false).
    apply flow_join_label with lb1 lo; auto.
    apply join_label_commutative. 
    unfold low_component in H17; subst; auto;
      destruct ctns1'; destruct ctns2;
        rewrite H_flow1 in H17; rewrite H_flow2 in H17;
          apply L_equivalence_config_H; auto; 
            unfold low_component; subst; auto; rewrite H; auto;
              rewrite H_flow2;  auto .
(*field update *)
  - split; auto.
    
    apply update_h1_with_H_preserve_bijection with ct lb1' lx; auto.
    inversion H_valid1. auto.

    assert (forall a1 a2 : oid, decision.Decision (a1 = a2)). auto.     
    apply update_field_h1_preserve_config_eq with lb1' lx; auto.
    inversion H_valid2. auto.
    inversion H_valid1; auto.

    apply L_equivalence_config_H; auto.
    destruct ctns1'.
    unfold low_component in H19.
    unfold low_component.
    rewrite H17. rewrite H17 in H19. auto.
    unfold low_component in H19.
    unfold low_component.
    rewrite H17. rewrite H17 in H19. auto.
        
  - split; auto.
    unfold low_component in H17; subst; auto;
      destruct ctns1'; destruct ctns2;
        rewrite H_flow1 in H17; rewrite H_flow2 in H17;
          apply L_equivalence_config_H; auto; 
            unfold low_component; subst; auto; rewrite  H_flow1';  auto;
              rewrite H_flow2; auto; rewrite   H_flow1' in H17; auto.
Qed. Hint Resolve      simulation_H2H_H.



Lemma simulation_H2L_H2L : forall ct t1 fs1 lb1 sf1 ctns1 h1
                              t2 fs2 lb2 sf2 ctns2 h2 
                              t1' fs1' lb1' sf1' ctns1' h1'
                              t2' fs2' lb2' sf2' ctns2' h2' φ, 
      valid_config (Config ct (Container t1 fs1 lb1 sf1) ctns1 h1 ) ->
      valid_config (Config ct (Container t2 fs2 lb2 sf2) ctns2 h2 ) ->
(*      config_has_type ct empty_context (Config ct (Container t1 fs1 lb1 sf1)  ctns1 h1) T ->
      config_has_type ct empty_context (Config ct (Container t2 fs2 lb2 sf2)  ctns2 h2) T -> *)
      Config ct (Container t1 fs1 lb1 sf1) ctns1 h1
             ==> Config ct (Container t1' fs1' lb1' sf1') ctns1' h1' ->
      Config ct (Container t2 fs2 lb2 sf2) ctns2 h2
             ==> Config ct (Container t2' fs2' lb2' sf2') ctns2' h2' ->
      flow_to lb1 L_Label = false ->
      flow_to lb2 L_Label = false ->
      flow_to lb1' L_Label = true ->
      flow_to lb2' L_Label = true ->
      L_equivalence_config (Config ct (Container t1 fs1 lb1 sf1) ctns1 h1 )
                           (Config ct (Container t2 fs2 lb2 sf2) ctns2 h2)  φ ->
     L_equivalence_heap h1 h2 φ ->
     L_equivalence_heap h1' h2' φ /\ L_equivalence_config (Config ct (Container t1' fs1' lb1' sf1') ctns1' h1')
                          (Config ct (Container t2' fs2' lb2' sf2') ctns2' h2' )  φ.
Proof with eauto.
intros ct t1 fs1 lb1 sf1 ctns1 h1
                              t2 fs2 lb2 sf2 ctns2 h2 
                              t1' fs1' lb1' sf1' ctns1' h1'
                              t2' fs2' lb2' sf2' ctns2' h2' φ.
  intro H_valid1.       intro H_valid2.
 (* intro H_typing1. intro H_typing2.*)
  intro H_reduction1.
  intro H_reduction2. 
  intro H_flow1. intro H_flow2.
  intro H_flow1'. intro H_flow2'.
  
  intro H_low_eq.    
  intro H_bijection.
  remember (Config ct (Container t1 fs1 lb1 sf1) ctns1 h1) as config1. 
  remember (Config ct (Container t1' fs1' lb1' sf1') ctns1' h1') as config1'.
  generalize dependent t1. generalize dependent fs1. generalize dependent lb1. 
  generalize dependent ctns1. generalize dependent h1. 

  generalize dependent t2. generalize dependent fs2. generalize dependent lb2. 
  generalize dependent ctns2. generalize dependent h2. 

  generalize dependent sf1. generalize dependent sf2.
  induction H_reduction1; intros; auto; inversion Heqconfig1; inversion Heqconfig1'; subst;
    inversion H_low_eq; subst; 
  try( match goal with
    | H : flow_to ?T L_Label = true |- _
      =>  solve [ try (rewrite H_flow1 in H; inversion H; fail); try (rewrite H_flow2 in H; inversion H; fail)]
       end).
- assert (flow_to (join_label lo lb1) L_Label = false).
  apply flow_join_label with lb1 lo; auto.
  try (inconsist_label).

- assert (flow_to (join_label lb1 lx) L_Label = false).
  apply flow_join_label with lb1 lx; auto.
  apply join_label_commutative. 
  try (inconsist_label).

- assert (flow_to (join_label lb1 lo) L_Label = false).
  apply flow_join_label with lb1 lo; auto.
  apply join_label_commutative. 
  try (inconsist_label).

- assert (flow_to (join_label lb1 lo) L_Label = false).
  apply flow_join_label with lb1 lo; auto.
  apply join_label_commutative. 
  try (inconsist_label).

- inversion  H_reduction2; subst; auto;
    try( match goal with
    | H : flow_to ?T L_Label = true |- _
      =>  solve [ try (rewrite H_flow1 in H; inversion H; fail); try (rewrite H_flow2 in H; inversion H; fail)]
         end).
  + assert (flow_to (join_label lo lb2) L_Label = false).
    apply flow_join_label with lb2 lo; auto.
    try (inconsist_label).
  + assert (flow_to (join_label lb2 lx) L_Label = false).
    apply flow_join_label with lb2 lx; auto.
    apply join_label_commutative. 
    try (inconsist_label).

  + assert (flow_to (join_label lb2 lo) L_Label = false).
    apply flow_join_label with lb2 lo; auto.
    apply join_label_commutative. 
    try (inconsist_label).

  + assert (flow_to (join_label lb2 lo) L_Label = false).
    apply flow_join_label with lb2 lo; auto.
    apply join_label_commutative. 
    try (inconsist_label).

  + split; auto.

    unfold low_component in H17; rewrite H15 in H17. rewrite H16 in H17.
    fold low_component in H17.
    
    assert ((low_component ct (Container return_hole fs1' lb1' sf1') ctns1' h1') =
           Config  ct (Container return_hole fs1' lb1' sf1') ctns1' h1').
    apply low_component_with_L_Label; auto.
    assert ((low_component ct (Container return_hole fs2' lb2' sf2') ctns2' h2') =
           Config  ct (Container return_hole fs2' lb2' sf2') ctns2' h2').
    apply low_component_with_L_Label; auto.
    rewrite H0 in H17. rewrite H2 in H17; auto.
    inversion H17; subst; auto.
    inversion H23; subst; auto.
    apply L_equivalence_config_L; auto.
    try (inconsist_label).
    try (inconsist_label).
Qed. Hint Resolve simulation_H2L_H2L.


Lemma simulation_H_H2H : forall ct t1 fs1 lb1 sf1 ctns1 h1
                              t2 fs2 lb2 sf2 ctns2 h2 
                              t1' fs1' lb1' sf1' ctns1' h1'
                              t2' fs2' lb2' sf2' ctns2' h2' φ, 
      valid_config (Config ct (Container t1 fs1 lb1 sf1) ctns1 h1 ) ->
      valid_config (Config ct (Container t2 fs2 lb2 sf2) ctns2 h2 ) ->
      Config ct (Container t1 fs1 lb1 sf1) ctns1 h1
             ==> Config ct (Container t1' fs1' lb1' sf1') ctns1' h1' ->
      Config ct (Container t2 fs2 lb2 sf2) ctns2 h2
             ==> Config ct (Container t2' fs2' lb2' sf2') ctns2' h2' ->
      flow_to lb1 L_Label = false ->
      flow_to lb2 L_Label = false ->
      flow_to lb1' L_Label = true ->
      flow_to lb2' L_Label = false ->
      L_equivalence_config (Config ct (Container t1 fs1 lb1 sf1) ctns1 h1 )
                           (Config ct (Container t2 fs2 lb2 sf2) ctns2 h2)  φ ->
     L_equivalence_heap h1 h2 φ ->
     L_equivalence_heap h1 h2' φ /\ L_equivalence_config (Config ct (Container t1 fs1 lb1 sf1) ctns1 h1)
                          (Config ct (Container t2' fs2' lb2' sf2') ctns2' h2' )  φ.
Proof with eauto. 
  intros ct t1 fs1 lb1 sf1 ctns1 h1
                              t2 fs2 lb2 sf2 ctns2 h2 
                              t1' fs1' lb1' sf1' ctns1' h1'
                              t2' fs2' lb2' sf2' ctns2' h2' φ.
  intro H_valid1.       intro H_valid2.
  intro H_reduction1.
  intro H_reduction2. 
  intro H_flow1. intro H_flow2.
  intro H_flow1'. intro H_flow2'. 
  intro H_low_eq.    
  intro H_bijection.
  remember (Config ct (Container t2 fs2 lb2 sf2) ctns2 h2) as config. 
  remember (Config ct (Container t2' fs2' lb2' sf2') ctns2' h2') as config'.
  generalize dependent t1. generalize dependent fs1. generalize dependent lb1. 
  generalize dependent ctns1. generalize dependent h1. 

  generalize dependent t2. generalize dependent fs2. generalize dependent lb2. 
  generalize dependent ctns2. generalize dependent h2. 

  generalize dependent sf1. generalize dependent sf2.
  induction H_reduction2; intros; auto; inversion Heqconfig; inversion Heqconfig'; subst;
    inversion H_low_eq; subst;
      try (inconsist_label); 
      try (split; auto;
         match goal with
         | H : L_equivalence_config _ _ _  |- _ 
           => unfold low_component in H; subst; auto;
              destruct ctns1; destruct ctns2';
              rewrite H_flow1 in H; rewrite H_flow2 in H;
              apply L_equivalence_config_H; auto; 
              unfold low_component; subst; auto;
              rewrite H_flow1; rewrite H_flow2; auto  
         end
       ).
(* field access *)
  - split; auto.    
    unfold low_component in H18; subst; auto;
      destruct ctns1; destruct ctns2';
        rewrite H_flow1 in H18; rewrite H_flow2 in H18;
          apply L_equivalence_config_H; auto; 
            unfold low_component; subst; auto; rewrite H_flow1; auto;
             rewrite   H_flow2';  auto .
(* (MethodCall (ObjId o) meth v)  *)
  - split; auto.
    unfold low_component in H19; subst; auto;
      destruct ctns1; destruct ctns2;
        rewrite H_flow1 in H19; rewrite H_flow2 in H19;
          apply L_equivalence_config_H; auto; 
            unfold low_component; subst; auto; rewrite H_flow1; auto;
              rewrite H_flow2; auto .

  (* (MethodCall (ObjId o) meth (v_opa_l v lx)) )  *)
  - split; auto.
    unfold low_component in H19; subst; auto;
      destruct ctns1; destruct ctns2;
        rewrite H_flow1 in H19; rewrite H_flow2 in H19;
          apply L_equivalence_config_H; auto; 
            unfold low_component; subst; auto; rewrite H17; auto;
              rewrite H_flow2; rewrite H_flow2';  auto .
(*new exp*)
  - split; auto.
    apply extend_h2_with_H_preserve_bijection with ct ;auto.
    inversion H_valid2; auto.
    
    apply extend_h2_with_H_preserve_config_eq; auto.
    inversion H_valid2; subst; auto. 
    apply  valid_conf; auto.
    inversion H8; subst; auto.

    apply L_equivalence_config_H; auto.
    destruct ctns2'.
    unfold low_component in H17.
    unfold low_component.
    rewrite H16. rewrite H16 in H17. auto.
    unfold low_component in H17.
    unfold low_component.
    rewrite H16. rewrite H16 in H17. auto.


  - split; auto.
    assert (flow_to (join_label lb2 lo) L_Label = false).
    apply flow_join_label with lb2 lo; auto.
    apply join_label_commutative. 
    unfold low_component in H17; subst; auto;
      destruct ctns1; destruct ctns2';
        rewrite H_flow1 in H17; rewrite H_flow2 in H17;
          apply L_equivalence_config_H; auto; 
            unfold low_component; subst; auto; rewrite H; auto;
               rewrite H_flow1;  auto .

  - split; auto.
    assert (flow_to (join_label lb2 lo) L_Label = false).
    apply flow_join_label with lb2 lo; auto.
    apply join_label_commutative. 
    unfold low_component in H17; subst; auto;
      destruct ctns1; destruct ctns2';
        rewrite H_flow1 in H17; rewrite H_flow2 in H17;
          apply L_equivalence_config_H; auto; 
            unfold low_component; subst; auto; rewrite H; auto;
              rewrite H_flow1;  auto .
(*field update *)
  - split; auto.
    apply update_h2_with_H_preserve_bijection with ct lb2' lx; auto.
    inversion H_valid1. auto.

    assert (forall a1 a2 : oid, decision.Decision (a1 = a2)). auto.     
    apply update_field_h2_preserve_config_eq with lb2' lx; auto.
    inversion H_valid2. auto.
    inversion H_valid1; auto.

    apply L_equivalence_config_H; auto.
    destruct ctns2'.
    unfold low_component in H19.
    unfold low_component.
    rewrite H18. rewrite H18 in H19. auto.
    unfold low_component in H19.
    unfold low_component.
    rewrite H18. rewrite H18 in H19. auto.
        
  - split; auto.
    unfold low_component in H17; subst; auto;
      destruct ctns1; destruct ctns2';
        rewrite H_flow1 in H17; rewrite H_flow2 in H17;
          apply L_equivalence_config_H; auto; 
            unfold low_component; subst; auto; rewrite  H_flow2';  auto;
              rewrite H_flow1; auto; rewrite   H_flow2' in H17; auto.
    Qed. 
Hint Resolve simulation_H_H2H. 



Lemma simulation_L : forall ct t1 fs1 lb1 sf1 ctns1 h1  t2 fs2 lb2 sf2 ctns2 h2 
      ctn1' ctns1' h1'  ctn2' ctns2' h2' φ T, 
      valid_config (Config ct (Container t1 fs1 lb1 sf1) ctns1 h1 ) ->
      valid_config (Config ct (Container t2 fs2 lb2 sf2) ctns2 h2 ) ->
      config_has_type ct empty_context (Config ct (Container t1 fs1 lb1 sf1)  ctns1 h1) T ->
      config_has_type ct empty_context (Config ct (Container t2 fs2 lb2 sf2)  ctns2 h2) T ->
      flow_to lb1 L_Label = true ->
      flow_to lb2 L_Label = true ->
      L_equivalence_config (Config ct (Container t1 fs1 lb1 sf1) ctns1 h1 )
            (Config ct (Container t2 fs2 lb2 sf2) ctns2 h2)  φ ->
     Config ct (Container t1 fs1 lb1 sf1) ctns1 h1 
      ==> Config ct ctn1' ctns1' h1' ->
     Config ct (Container t2 fs2 lb2 sf2) ctns2 h2
      ==> Config ct ctn2' ctns2' h2' ->
     L_equivalence_heap h1 h2 φ ->
      exists  φ', L_equivalence_heap h1' h2' φ' /\ L_equivalence_config (Config ct ctn1' ctns1' h1')
                                      (Config ct ctn2' ctns2' h2')  φ'.
Proof. Admitted.
Hint Resolve  simulation_L.