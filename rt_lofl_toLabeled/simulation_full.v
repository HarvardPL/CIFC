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
Require Import decision. 


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
(* emp *)
  - split; auto.
    unfold low_component in H20; subst; auto;
      destruct ctns1'; destruct ctns2;
        rewrite H_flow1 in H20; rewrite H_flow2 in H20;
          apply L_equivalence_config_H; auto; 
            unfold low_component; subst; auto; rewrite H_flow1'; auto;
              rewrite H_flow2; auto .

  - (* field access 1 *)
    split; auto.
    unfold low_component in H18; subst; auto;
      destruct ctns1; destruct ctns2;
        rewrite H_flow1 in H18; rewrite H_flow2 in H18;
          apply L_equivalence_config_H; auto; 
            unfold low_component; subst; auto; rewrite H_flow1'; auto;
              rewrite H_flow1; auto;rewrite H_flow2; auto.

  - (* field access 2*)
    split; auto.
    unfold low_component in H18; subst; auto;
      destruct ctns1; destruct ctns2;
        rewrite H_flow1 in H18; rewrite H_flow2 in H18;
          apply L_equivalence_config_H; auto; 
            unfold low_component; subst; auto; rewrite H_flow1'; auto;
              rewrite H_flow1; auto;rewrite H_flow2; auto.

(* (MethodCall (ObjId o) meth v)  *)
  - split; auto.
    unfold low_component in H19; subst; auto;
      destruct ctns1; destruct ctns2;
        rewrite H_flow1 in H19; rewrite H_flow2 in H19;
          apply L_equivalence_config_H; auto; 
            unfold low_component; subst; auto; rewrite H_flow1; rewrite H_flow1'; auto;
              rewrite H_flow2; auto .

(* (MethodCall (v_opa_l v ell) meth v)  *)
  - split; auto.
    unfold low_component in H19; subst; auto;
      destruct ctns1; destruct ctns2;
        rewrite H_flow1 in H19; rewrite H_flow2 in H19;
          apply L_equivalence_config_H; auto; 
            unfold low_component; subst; auto; rewrite H_flow1; auto;
              rewrite H_flow2; auto;rewrite H_flow1'; auto .
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

(* (Config ct (Container t1' fs1' (join_label lb1 lo) sf1') ctns1' h1') *)

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

(* unlabel v*)
  - split; auto.
    unfold low_component in H17; subst; auto;
      destruct ctns1'; destruct ctns2;
        rewrite H_flow1 in H17; rewrite H_flow2 in H17;
          apply L_equivalence_config_H; auto; 
            unfold low_component; subst; auto; rewrite H_flow1'; auto;
              rewrite H_flow2;  auto .

(* labelof v*)
  - split; auto.
    unfold low_component in H17; subst; auto;
      destruct ctns1'; destruct ctns2;
        rewrite H_flow1 in H17; rewrite H_flow2 in H17;
          apply L_equivalence_config_H; auto; 
            unfold low_component; subst; auto; rewrite H_flow1'; auto;
              rewrite H_flow2;  auto .
    
(* objectLabelof v*)
  - split; auto.
    unfold low_component in H17; subst; auto;
      destruct ctns1'; destruct ctns2;
        rewrite H_flow1 in H17; rewrite H_flow2 in H17;
          apply L_equivalence_config_H; auto; 
            unfold low_component; subst; auto; rewrite H_flow1'; auto;
              rewrite H_flow2;  auto . 

(* objectLabelof v*)
  - split; auto.
    unfold low_component in H17; subst; auto;
      destruct ctns1'; destruct ctns2;
        rewrite H_flow1 in H17; rewrite H_flow2 in H17;
          apply L_equivalence_config_H; auto; 
            unfold low_component; subst; auto; rewrite H_flow1'; auto;
              rewrite H_flow2;  auto .     
    

  (* raise skip *)  
  - split; auto.
    apply change_obj_lbl_h1_with_H_preserve_bijection with ct lo lb1' L_Label; auto.
    inversion H_valid1; auto.
    assert (join_label lb1' L_Label = lb1').
    apply join_L_Label_irrelevant.
    rewrite H2; auto.

    inversion H_valid1; subst; auto.
    inversion H_valid2; subst; auto.
    apply change_obj_lbl_h1_preserve_config_eq with lo lb1' L_Label; auto.
    apply L_equivalence_config_H; auto.
    destruct ctns1'.
    unfold low_component in H19.
    unfold low_component.
    rewrite H17. rewrite H17 in H19. auto.
    unfold low_component in H19.
    unfold low_component.
    rewrite H17. rewrite H17 in H19. auto.
    assert (join_label lb1' L_Label = lb1').
    apply join_L_Label_irrelevant.
    rewrite H2; auto. 

  (* raise skip 2 *)  
  - split; auto.
    apply change_obj_lbl_h1_with_H_preserve_bijection with ct lo lb1' L_Label; auto.
    inversion H_valid1; auto.
    assert (join_label lb1' L_Label = lb1').
    apply join_L_Label_irrelevant.
    rewrite H2; auto.

    inversion H_valid1; subst; auto.
    inversion H_valid2; subst; auto.
    assert (flow_to lb1' (join_label lb1' ell) = true).
    apply join_def_flow1.
    eauto using flow_trans. 

    
    apply change_obj_lbl_h1_preserve_config_eq with lo lb1' L_Label; auto.
    inversion H_valid1; subst; auto.
    inversion H_valid2; subst; auto.
    inversion H_valid1; subst; auto. 


    apply L_equivalence_config_H; auto.
    destruct ctns1'.
    unfold low_component in H19.
    unfold low_component.
    rewrite H17. rewrite H17 in H19. auto.
    unfold low_component in H19.
    unfold low_component.
    rewrite H17. rewrite H17 in H19. auto.
    assert (join_label lb1' L_Label = lb1').
    apply join_L_Label_irrelevant.
    rewrite H2; auto.
    assert (flow_to lb1' (join_label lb1' ell) = true).
    apply join_def_flow1.
    eauto using flow_trans. 

   (* toLabled result*)
  -
    split; auto.
    unfold low_component in H16; subst; auto;
      destruct ctns1; destruct ctns2;
        rewrite H_flow1 in H16; rewrite H_flow2 in H16;
          apply L_equivalence_config_H; auto; 
            unfold low_component; subst; auto; rewrite H_flow1'; auto;
              rewrite H_flow2;  auto .  

  -
    (* (toLabeled e1 (v_opa_l v ell)) fs *)
    split; auto.
    unfold low_component in H17; subst; auto;
      destruct ctns1'; destruct ctns2;
        rewrite H_flow1 in H17; rewrite H_flow2 in H17;
          apply L_equivalence_config_H; auto; 
            unfold low_component; subst; auto; rewrite H_flow1'; auto;
              rewrite H_flow2;  auto .  
    
(*field update normal *)
  - assert ((join_label lb1' L_Label) = lb1').
    apply join_L_Label_irrelevant ; auto.

    assert (flow_to lb1' (join_label  (runtime_label v)  lb1') = true).
    apply join_def_flow2.
    assert (flow_to lb1' (join_label lo ll) = true).
    eauto using flow_trans. 
    
    split; auto.    
   
    apply update_h1_with_H_preserve_bijection with ct lb1' L_Label; auto.
    inversion H_valid1; auto.
    rewrite H0; auto.
    

    assert (forall a1 a2 : oid, decision.Decision (a1 = a2)). auto.     
    apply update_field_h1_preserve_config_eq with lb1' L_Label; auto.
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

    rewrite H0; auto.

(*field update v_opa_l *)
  -
    split; auto.
    apply L_equivalence_config_H; auto.
    destruct ctns1'.
    unfold low_component in H18.
    unfold low_component.
    rewrite   H_flow1'. rewrite H16 in H18. auto.
    unfold low_component in H18.
    unfold low_component.
    rewrite   H_flow1'. rewrite H16 in H18. auto.

(* if guard s1 s2*)
  - split; auto.
    unfold low_component in H17; subst; auto;
      destruct ctns1'; destruct ctns2;
        rewrite H_flow1 in H17; rewrite H_flow2 in H17;
          apply L_equivalence_config_H; auto; 
            unfold low_component; subst; auto; rewrite  H_flow1';  auto;
              rewrite H_flow2; auto; rewrite   H_flow1' in H17; auto.


  (*  L_equivalence_config (Config ct (Container (v_opa_l t1 lb1) fs1' lb1' sf1') ctns1' h1')
   (Config ct (Container t2 fs2 lb2 sf2) ctns2 h2) φ *)
  - split; auto.
    unfold low_component in H18; subst; auto;
      destruct ctns1'; destruct ctns2;
        rewrite H_flow1 in H18; rewrite H_flow2 in H18;
          apply L_equivalence_config_H; auto; 
            unfold low_component; subst; auto; rewrite  H_flow1';  auto;
              rewrite H_flow2; auto; rewrite   H_flow1' in H18; auto.


  (* L_equivalence_config
   (Config ct (Container (v_opa_l v (join_label ell lb1)) fs1' lb1' sf1') ctns1' h1')
   (Config ct (Container t2 fs2 lb2 sf2) ctns2 h2) φ *)
  - split; auto.
    unfold low_component in H16; subst; auto;
      destruct ctns1'; destruct ctns2;
        rewrite H_flow1 in H16; rewrite H_flow2 in H16;
          apply L_equivalence_config_H; auto; 
            unfold low_component; subst; auto; rewrite  H_flow1';  auto;
              rewrite H_flow2; auto; rewrite   H_flow1' in H16; auto.
  
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
- assert (flow_to (join_label (join_label (runtime_label v1) (runtime_label v2)) lb1) L_Label = false). eauto using flow_join_label.
  assert (flow_to (join_label (join_label (join_label (runtime_label v1) (runtime_label v2)) lb1)
             (join_label (object_label (runtime_val v1) h1')
                (object_label (runtime_val v2) h1')))
                  L_Label = false).
  apply flow_join_label with 
                             
      (join_label (join_label (runtime_label v1) (runtime_label v2)) lb1)
      (join_label (object_label (runtime_val v1) h1')
                                         (object_label (runtime_val v2) h1'))
  ; auto.
  apply join_label_commutative.
  remember (join_label (join_label (join_label (runtime_label v1) (runtime_label v2)) lb1)
                       (join_label (object_label (runtime_val v1) h1') (object_label (runtime_val v2) h1'))) as lb''.
  assert ( flow_to (join_label lb'' (label_label (runtime_val v1) h1')) L_Label = false).
  apply flow_transitive with lb''; auto. 
  apply join_def_flow1 . 
  try (inconsist_label).

- assert (flow_to (join_label lo lb1) L_Label = false).
  eauto using flow_join_label.
  assert (flow_to (join_label (join_label lo lb1) ll) L_Label = false).
  apply flow_transitive with (join_label lo lb1);auto.
  apply  join_def_flow1; auto. 
  try (inconsist_label).

- assert (flow_to (join_label lo lb1) L_Label = false).
  eauto using flow_join_label.
  assert (flow_to (join_label (join_label lo lb1) ell) L_Label = false).
  apply flow_join_label with (join_label lo lb1) ell; auto. 
  eauto using join_label_commutative.   

  assert (flow_to (join_label (join_label (join_label lo lb1) ell) ll) L_Label = false).
  apply flow_transitive with (join_label (join_label lo lb1) ell);auto.
  apply  join_def_flow1; auto. 

  try (inconsist_label).


- assert (flow_to (join_label lb1 ll) L_Label = false).
  apply flow_transitive with lb1;auto.
  apply  join_def_flow1; auto. 
  try (inconsist_label).


-
  assert (flow_to (join_label (join_label lb1 ell) ll) L_Label = false).
  apply flow_transitive with  (join_label lb1 ell); auto.
  apply flow_transitive with lb1; auto.
  apply join_def_flow1; auto.
  apply join_def_flow1; auto. 
  try (inconsist_label).

- assert (flow_to (join_label lb1 lo) L_Label = false).
  apply flow_join_label with lb1 lo; auto.
  apply join_label_commutative.
  try (inconsist_label).

- assert (flow_to (join_label lb1 ell) L_Label = false).
  apply flow_join_label with lb1 ell; auto.
  apply join_label_commutative. 
  try (inconsist_label).


- assert (flow_to (join_label lb1 ell) L_Label = false).
  apply flow_join_label with lb1 ell; auto.
  apply join_label_commutative. 
  try (inconsist_label).
  

(* start objectLabelOf*)
  
- assert (flow_to (join_label ll lb1) L_Label = false).
  apply flow_join_label with lb1 ll; auto.
  try (inconsist_label).

- assert (flow_to (join_label ll (join_label lb1 ell)) L_Label = false).
  apply flow_join_label with (join_label lb1 ell) ll; auto.
  apply flow_join_label with lb1 ell; auto. 
  apply join_label_commutative. 
  try (inconsist_label).  
  
(* end objectLabelOf*)

(* toLabeled *)
- assert (flow_to (join_label lb1 ell) L_Label = false).
  apply flow_join_label with lb1 ell; auto.
  apply join_label_commutative. 
  try (inconsist_label).  
  
- assert (flow_to (join_label ell lb1) L_Label = false).
  apply flow_transitive with lb1; auto.
  apply join_def_flow2. 
  try (inconsist_label).
  
 
- inversion  H_reduction2; subst; auto;
    try( match goal with
    | H : flow_to ?T L_Label = true |- _
      =>  solve [ try (rewrite H_flow1 in H; inversion H; fail); try (rewrite H_flow2 in H; inversion H; fail)]
         end); try (pose proof join_def_flow1  lb1  ell as Hc1;
    pose proof (flow_transitive (join_label lb1 ell) lb1  H_flow1 Hc1);
    try (inconsist_label)).
  
- inversion  H_reduction2; subst; auto;
    try( match goal with
    | H : flow_to ?T L_Label = true |- _
      =>  solve [ try (rewrite H_flow1 in H; inversion H; fail); try (rewrite H_flow2 in H; inversion H; fail)]
         end).
  + assert (flow_to (join_label (join_label (runtime_label v1) (runtime_label v2)) lb2) L_Label = false). eauto using flow_join_label.
  assert (flow_to (join_label (join_label (join_label (runtime_label v1) (runtime_label v2)) lb2)
             (join_label (object_label (runtime_val v1) h2')
                (object_label (runtime_val v2) h2')))
                  L_Label = false).
  apply flow_join_label with 
                             
      (join_label (join_label (runtime_label v1) (runtime_label v2)) lb2)
      (join_label (object_label (runtime_val v1) h2')
                                         (object_label (runtime_val v2) h2'))
  ; auto.
  apply join_label_commutative.
      apply flow_dist in H_flow2'; destruct H_flow2'; auto.

  try (inconsist_label).
    
  + assert (flow_to (join_label lo lb2) L_Label = false).
    eauto using flow_join_label.

    apply flow_dist in H_flow2'; destruct H_flow2'; auto.

    try (inconsist_label).
  + assert (flow_to (join_label lo lb2) L_Label = false).
    eauto using flow_join_label.     
    assert (flow_to (join_label (join_label lo lb2) ell) L_Label = false).
    apply flow_join_label with (join_label lo lb2) ell ;auto.
    apply join_label_commutative.
    apply flow_dist in H_flow2'; destruct H_flow2'; auto.
    try (inconsist_label).

  + assert (flow_to (join_label lo lb2) L_Label = false).
    eauto using flow_join_label.
    apply flow_dist in H_flow2'; destruct H_flow2'; auto.
    try (inconsist_label).
    
  + assert (flow_to (join_label (join_label lb2 ell) ll) L_Label = false).
    apply flow_transitive with (join_label lb2 ell); auto.
    apply flow_transitive with lb2; auto.
    apply join_def_flow1; auto.
    apply join_def_flow1; auto. 
    try (inconsist_label).

  + assert (flow_to (join_label lb2 lo) L_Label = false).
    apply flow_join_label with lb2 lo ;auto.
    apply join_label_commutative. 
    try (inconsist_label).
  + assert (flow_to (join_label lb2 ell) L_Label = false).
    apply flow_join_label with lb2 ell ;auto.
    apply join_label_commutative. 
    try (inconsist_label).
  + assert (flow_to (join_label lb2 ell) L_Label = false).
    apply flow_join_label with lb2 ell;auto.
    apply join_label_commutative. 
    try (inconsist_label).

  + assert (flow_to (join_label ll lb2) L_Label = false).
    apply flow_join_label with lb2 ll ;auto.
    try (inconsist_label).
  + assert (flow_to (join_label ll (join_label lb2 ell)) L_Label = false).
    apply flow_join_label with (join_label lb2 ell) ll ;auto.
    apply flow_join_label with lb2 ell;auto.
    apply join_label_commutative. 
    try (inconsist_label).

  + assert (flow_to (join_label lb2 ell) L_Label = false).
    apply flow_transitive with lb2; auto.
    apply join_def_flow1. 
    try (inconsist_label).
    
  + assert (flow_to (join_label ell lb2) L_Label = false).
    apply flow_transitive with lb2; auto.
    apply join_def_flow2. 
    try (inconsist_label).

    
  + assert (flow_to (join_label lb2 ell) L_Label = false).
    apply flow_transitive with lb2; auto.
    apply join_def_flow1. 
    try (inconsist_label).


  + split; auto.
    unfold low_component in H18; rewrite H16 in H18; rewrite H17 in H18.
    fold low_component in H18.    
    assert ((low_component ct (Container return_hole fs1' lb1' sf1') ctns1' h1') =
           Config  ct (Container return_hole fs1' lb1' sf1') ctns1' h1').
    apply low_component_with_L_Label; auto.
    assert ((low_component ct (Container return_hole fs2' lb2' sf2') ctns2' h2') =
           Config  ct (Container return_hole fs2' lb2' sf2') ctns2' h2').
    apply low_component_with_L_Label; auto.
    rewrite H1 in H18. rewrite H2 in H18. 
    inversion H18; subst; auto.    
    ++
      apply L_equivalence_config_L; auto.
      apply L_eq_ctn; auto.
      apply  L_equivalence_tm_eq_v_opa_l_H ; auto.
      apply v_opa_labeled; auto.
      intros. intro contra; subst; auto.  destruct H0 with v0 lb0; auto.  inversion H; auto. 

      apply v_opa_labeled; auto.
      intros. intro contra; subst; auto.  destruct H19 with v0 lb0; auto.  inversion H3; auto.

      inversion H24; subst; auto.
      inversion H24; subst; auto. 
    ++
      try (inconsist).

  + split; auto.
    unfold low_component in H18; rewrite H16 in H18; rewrite H17 in H18.
    fold low_component in H18.    
    assert ((low_component ct (Container return_hole fs1' lb1' sf1') ctns1' h1') =
           Config  ct (Container return_hole fs1' lb1' sf1') ctns1' h1').
    apply low_component_with_L_Label; auto.
    assert ((low_component ct (Container return_hole fs2' lb2' sf2') ctns2' h2') =
           Config  ct (Container return_hole fs2' lb2' sf2') ctns2' h2').
    apply low_component_with_L_Label; auto.
    rewrite H1 in H18. rewrite H2 in H18. 
    inversion H18; subst; auto.    
    ++
      apply L_equivalence_config_L; auto.
      apply L_eq_ctn; auto.
      apply  L_equivalence_tm_eq_v_opa_l_H ; auto.
      apply flow_transitive with lb2; auto.
      apply join_def_flow2. 
      apply v_opa_labeled; auto.
      intros. intro contra; subst; auto.  destruct H0 with v0 lb0; auto.  inversion H; auto. 

      inversion H_valid2; subst; auto.
      inversion H12; subst; auto.
      inversion H11; subst; auto.
      
      inversion H22; subst; auto.
      inversion H22; subst; auto. 

    ++
      try (inconsist).      
- inversion  H_reduction2; subst; auto;
    try( match goal with
    | H : flow_to ?T L_Label = true |- _
      =>  solve [ try (rewrite H_flow1 in H; inversion H; fail); try (rewrite H_flow2 in H; inversion H; fail)]
         end); try (inconsist); try (apply flow_dist in H_flow2'; destruct H_flow2'; auto;
      pose proof join_def_flow2 lo lb2 as Hc1;
      pose proof (flow_transitive (join_label lo lb2) lb2 H_flow2 Hc1); try (inconsist)).


  + assert (flow_to (join_label (join_label (runtime_label v1) (runtime_label v2)) lb2) L_Label = false).
    eauto using flow_join_label.
    assert (flow_to (join_label (join_label (join_label (runtime_label v1) (runtime_label v2)) lb2)
             (join_label (object_label (runtime_val v1) h2')
                (object_label (runtime_val v2) h2')))
                  L_Label = false).
    apply flow_join_label with                              
      (join_label (join_label (runtime_label v1) (runtime_label v2)) lb2)
      (join_label (object_label (runtime_val v1) h2')
                                         (object_label (runtime_val v2) h2'))
  ; auto.
    apply join_label_commutative.
    apply flow_dist in H_flow2'; destruct H_flow2'; auto.
    try (inconsist_label).
    
  + assert (flow_to (join_label lo lb2) L_Label = false).
    eauto using flow_join_label.     
    assert (flow_to (join_label (join_label lo lb2) ell0) L_Label = false).
    apply flow_join_label with (join_label lo lb2) ell0 ;auto.
    apply join_label_commutative.
    try (inconsist_label).

  + assert (flow_to (join_label lb2 ell0) L_Label = false).
    apply flow_transitive with lb2; auto.
    apply join_def_flow1; auto. 
    try (inconsist_label).

  + assert (flow_to (join_label lb2 ell0) L_Label = false).
    apply flow_transitive with lb2; auto.
    apply join_def_flow1. 
    try (inconsist_label).

  + assert (flow_to (join_label lb2 ell0) L_Label = false).
    apply flow_transitive with lb2; auto.
    apply join_def_flow1. 
    try (inconsist_label).
    
  + assert (flow_to (join_label lb2 ell0) L_Label = false).
    apply flow_transitive with lb2; auto.
    apply join_def_flow1. 
    try (inconsist_label).
    
  + assert (flow_to (join_label lb2 ell0) L_Label = false).
    apply flow_transitive with lb2; auto.
    apply join_def_flow1. 
    try (inconsist_label).

  + assert (flow_to (join_label lb2 ell0) L_Label = false).
    apply flow_transitive with lb2; auto.
    apply join_def_flow1. 
    try (inconsist_label).
    

  + split; auto.
    unfold low_component in H16; rewrite H14 in H16; rewrite H15 in H16.
    fold low_component in H16.    
    assert ((low_component ct (Container return_hole fs1' lb1' sf1') ctns1' h1') =
           Config  ct (Container return_hole fs1' lb1' sf1') ctns1' h1').
    apply low_component_with_L_Label; auto.
    assert ((low_component ct (Container return_hole fs2' lb2' sf2') ctns2' h2') =
           Config  ct (Container return_hole fs2' lb2' sf2') ctns2' h2').
    apply low_component_with_L_Label; auto.
    rewrite H in H16. rewrite H0 in H16. 
    inversion H16; subst; auto.    
    ++
      apply L_equivalence_config_L; auto.
      apply L_eq_ctn; auto.
      apply  L_equivalence_tm_eq_v_opa_l_H ; auto.
      apply flow_transitive with lb1; auto.
      apply join_def_flow2.      
      inversion H_valid1; subst; auto.
      inversion H11; subst; auto.
      inversion H10; subst; auto. 
      apply v_opa_labeled; auto.
      intros. intro contra; subst; auto.  destruct H17 with v0 lb0; auto.
      inversion H1; auto. 

      inversion H22; subst; auto.
      inversion H22; subst; auto. 
    ++
      try (inconsist).
      
  + split; auto.
    unfold low_component in H16; rewrite H14 in H16; rewrite H15 in H16.
    fold low_component in H16.    
    assert ((low_component ct (Container return_hole fs1' lb1' sf1') ctns1' h1') =
           Config  ct (Container return_hole fs1' lb1' sf1') ctns1' h1').
    apply low_component_with_L_Label; auto.
    assert ((low_component ct (Container return_hole fs2' lb2' sf2') ctns2' h2') =
           Config  ct (Container return_hole fs2' lb2' sf2') ctns2' h2').
    apply low_component_with_L_Label; auto.
    rewrite H in H16. rewrite H0 in H16. 
    inversion H16; subst; auto.    
    ++
      apply L_equivalence_config_L; auto.
      apply L_eq_ctn; auto.
      
      apply  L_equivalence_tm_eq_v_opa_l_H ; auto.
      apply flow_transitive with lb1; auto.
      apply join_def_flow2.
      apply flow_transitive with lb2; auto.
      apply join_def_flow2.      
      inversion H_valid1; subst; auto.
      inversion H10; subst; auto.
      inversion H9; subst; auto.

      inversion H_valid2; subst; auto.
      inversion H10; subst; auto.
      inversion H9; subst; auto. 

      inversion H20; subst; auto.
      inversion H20; subst; auto. 
    ++
      try (inconsist).
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
(* emp *)
  - split; auto.
    unfold low_component in H20; subst; auto;
      destruct ctns1; destruct ctns2';
        rewrite H_flow1 in H20; rewrite H_flow2 in H20;
          apply L_equivalence_config_H; auto; 
            unfold low_component; subst; auto; rewrite H_flow1; auto;
              rewrite H_flow2'; auto .

  - (* field access 1 *)
    split; auto.
    unfold low_component in H18; subst; auto;
      destruct ctns1; destruct ctns2;
        rewrite H_flow1 in H18; rewrite H_flow2 in H18;
          apply L_equivalence_config_H; auto; 
            unfold low_component; subst; auto; rewrite H_flow1; auto;
              rewrite H_flow2; auto;rewrite H_flow2'; auto.

  - (* field access 2*)
    split; auto.
    unfold low_component in H18; subst; auto;
      destruct ctns1; destruct ctns2;
        rewrite H_flow1 in H18; rewrite H_flow2 in H18;
          apply L_equivalence_config_H; auto; 
            unfold low_component; subst; auto; rewrite H_flow1; auto;
              rewrite H_flow2; auto;rewrite H_flow2'; auto.
    
(* (MethodCall (ObjId o) meth v)  *)
  - split; auto.
    unfold low_component in H19; subst; auto;
      destruct ctns1; destruct ctns2;
        rewrite H_flow1 in H19; rewrite H_flow2 in H19;
          apply L_equivalence_config_H; auto; 
            unfold low_component; subst; auto; rewrite H_flow1; auto;
              rewrite H_flow2; auto;rewrite H_flow2'; auto.

(* (MethodCall (v_opa_l v ell) meth v)  *)
  - split; auto.
    unfold low_component in H19; subst; auto;
      destruct ctns1; destruct ctns2;
        rewrite H_flow1 in H19; rewrite H_flow2 in H19;
          apply L_equivalence_config_H; auto; 
            unfold low_component; subst; auto; rewrite H_flow1; auto;
              rewrite H_flow2; auto;rewrite H_flow2'; auto.
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


(* (Config ct (Container t1' fs1' (join_label lb1 lo) sf1') ctns1' h1') *)

  - split; auto.
    assert (flow_to (join_label lb2 lo) L_Label = false).
    apply flow_join_label with lb2 lo; auto.
    apply join_label_commutative.
    
    unfold low_component in H17; subst; auto;
      destruct ctns1; destruct ctns2';
        rewrite H_flow1 in H17; rewrite H_flow2 in H17;
          apply L_equivalence_config_H; auto; 
            unfold low_component; subst; auto; rewrite H_flow1; auto;
              rewrite H_flow2'; auto;rewrite H_flow2'; auto.

(* unlabel v*)
  - split; auto.
    unfold low_component in H17; subst; auto;
      destruct ctns1; destruct ctns2';
        rewrite H_flow1 in H17; rewrite H_flow2 in H17;
          apply L_equivalence_config_H; auto; 
            unfold low_component; subst; auto; rewrite H_flow1; auto;
              rewrite H_flow2'; auto;rewrite H_flow2'; auto.

(* labelof v*)
  - split; auto.
    unfold low_component in H17; subst; auto;
      destruct ctns1; destruct ctns2';
        rewrite H_flow1 in H17; rewrite H_flow2 in H17;
          apply L_equivalence_config_H; auto; 
            unfold low_component; subst; auto; rewrite H_flow1; auto;
              rewrite H_flow2'; auto;rewrite H_flow2'; auto.  

(* objectLabelOf v*)
  - split; auto.
    unfold low_component in H17; subst; auto;
      destruct ctns1; destruct ctns2';
        rewrite H_flow1 in H17; rewrite H_flow2 in H17;
          apply L_equivalence_config_H; auto; 
            unfold low_component; subst; auto; rewrite H_flow1; auto;
              rewrite H_flow2'; auto;rewrite H_flow2'; auto.
    
  - split; auto.
    unfold low_component in H17; subst; auto;
      destruct ctns1; destruct ctns2';
        rewrite H_flow1 in H17; rewrite H_flow2 in H17;
          apply L_equivalence_config_H; auto; 
            unfold low_component; subst; auto; rewrite H_flow1; auto;
              rewrite H_flow2'; auto;rewrite H_flow2'; auto.
    
  (* raise skip *)  
  - split; auto.
    inversion H_valid1; auto. 
    inversion H_valid2; auto. 
    apply change_obj_lbl_h2_with_H_preserve_bijection with ct lo lb2' L_Label ;auto.
    subst; auto.
    assert ((join_label lb2' L_Label) = lb2').
    apply join_L_Label_irrelevant ; auto. rewrite H2. auto. 

    inversion H_valid1; subst; auto. 
    inversion H_valid2; subst; auto. 
    apply change_obj_lbl_h2_preserve_config_eq with lo lb2' L_Label; auto.

    apply L_equivalence_config_H; auto.
    destruct ctns2'.
    unfold low_component in H19.
    unfold low_component.
    rewrite H18. rewrite H18 in H19. auto.
    unfold low_component in H19.
    unfold low_component.
    rewrite H18. rewrite H18 in H19. auto.

    assert ((join_label lb2' L_Label) = lb2').
    apply join_L_Label_irrelevant ; auto. rewrite H2. auto. 

  (* raise skip *)  
  - split; auto.
    inversion H_valid1; auto. 
    inversion H_valid2; auto. 
    apply change_obj_lbl_h2_with_H_preserve_bijection with ct lo lb2' L_Label ;auto.
    subst; auto.
    assert ((join_label lb2' L_Label) = lb2').
    apply join_L_Label_irrelevant ; auto. rewrite H2. auto. 

    inversion H_valid1; subst; auto. 
    inversion H_valid2; subst; auto.
    assert (flow_to lb2' (join_label lb2' ell) = true).
    apply join_def_flow1.
    eauto using flow_trans. 
    apply change_obj_lbl_h2_preserve_config_eq with lo lb2' L_Label; auto.
    inversion H_valid2; subst; auto.
    inversion H_valid1; subst; auto.
    
    apply L_equivalence_config_H; auto.
    destruct ctns2'.
    unfold low_component in H19.
    unfold low_component.
    rewrite H18. rewrite H18 in H19. auto.
    unfold low_component in H19.
    unfold low_component.
    rewrite H18. rewrite H18 in H19. auto.

    assert ((join_label lb2' L_Label) = lb2').
    apply join_L_Label_irrelevant ; auto.
    rewrite H2.
    assert (flow_to lb2' (join_label lb2' ell) = true).
    apply join_def_flow1.
    eauto using flow_trans. 

  - (* labelData*)
    split; auto.
    unfold low_component in H16; subst; auto;
      destruct ctns1; destruct ctns2;
        rewrite H_flow1 in H16; rewrite H_flow2 in H16;
          apply L_equivalence_config_H; auto; 
            unfold low_component; subst; auto; rewrite H_flow1; auto;
              rewrite H_flow2'; auto;rewrite H_flow2'; auto.


  - split; auto.
    unfold low_component in H17; subst; auto;
      destruct ctns1; destruct ctns2';
        rewrite H_flow1 in H17; rewrite H_flow2 in H17;
          apply L_equivalence_config_H; auto; 
            unfold low_component; subst; auto; rewrite H_flow1; auto;
              rewrite H_flow2'; auto;rewrite H_flow2'; auto.
    
  (*field update normal *)

  - split; auto.
    apply update_h2_with_H_preserve_bijection with ct lb2' L_Label; auto.
    inversion H_valid1. auto.

    assert ((join_label lb2' L_Label) = lb2').
    apply join_L_Label_irrelevant ; auto.
    rewrite H0.
    assert (flow_to lb2' (join_label (runtime_label v) lb2')  = true).
    apply join_def_flow2.
    eauto using flow_trans. 

    
    assert (forall a1 a2 : oid, decision.Decision (a1 = a2)). auto.     
    apply update_field_h2_preserve_config_eq with lb2' L_Label; auto.
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

    assert ((join_label lb2' L_Label) = lb2').
    apply join_L_Label_irrelevant ; auto.
    rewrite H2.
    assert (flow_to lb2' (join_label (runtime_label v) lb2')  = true).
    apply join_def_flow2.
    eauto using flow_trans. 
    

  (*field update opaque  *)

  - split; auto.
    unfold low_component in H18; subst; auto;
      destruct ctns1; destruct ctns2';
        rewrite H_flow1 in H18; rewrite H_flow2 in H18;
          apply L_equivalence_config_H; auto; 
            unfold low_component; subst; auto; rewrite H_flow1; auto;
              rewrite H_flow2'; auto;rewrite H_flow2'; auto.

(* if guard s1 s2*)
  - split; auto.
    unfold low_component in H17; subst; auto;
      destruct ctns1; destruct ctns2';
        rewrite H_flow1 in H17; rewrite H_flow2 in H17;
          apply L_equivalence_config_H; auto; 
            unfold low_component; subst; auto; rewrite H_flow1; auto;
              rewrite H_flow2'; auto;rewrite H_flow2'; auto.


  (*  L_equivalence_config (Config ct (Container (v_opa_l t1 lb1) fs1' lb1' sf1') ctns1' h1')
   (Config ct (Container t2 fs2 lb2 sf2) ctns2 h2) φ *)
  - split; auto.
    unfold low_component in H18; subst; auto;
      destruct ctns2'; destruct ctns1;
        rewrite H_flow2 in H18; rewrite H_flow1 in H18;
          apply L_equivalence_config_H; auto; 
            unfold low_component; subst; auto; rewrite  H_flow2';  auto;
              rewrite H_flow1; auto; rewrite   H_flow2' in H18; auto.


  (* L_equivalence_config
   (Config ct (Container (v_opa_l v (join_label ell lb1)) fs1' lb1' sf1') ctns1' h1')
   (Config ct (Container t2 fs2 lb2 sf2) ctns2 h2) φ *)
  - split; auto.
    unfold low_component in H16; subst; auto;
      destruct ctns2'; destruct ctns1;
        rewrite H_flow1 in H16; rewrite H_flow2 in H16;
          apply L_equivalence_config_H; auto; 
            unfold low_component; subst; auto; rewrite  H_flow2';  auto;
              rewrite H_flow1; auto; rewrite   H_flow2' in H16; auto.
Qed. Hint Resolve simulation_H_H2H.





Lemma simulation_Terminal_H2H : forall ct t1 fs1 lb1 sf1 ctns1 h1
                              t2 fs2 lb2 sf2 ctns2 h2 
                              t2' fs2' lb2' sf2' ctns2' h2' φ, 
      valid_config (Config ct (Container t1 fs1 lb1 sf1) ctns1 h1 ) ->
      valid_config (Config ct (Container t2 fs2 lb2 sf2) ctns2 h2 ) ->
      terminal_state (Config ct (Container t1 fs1 lb1 sf1) ctns1 h1)
              ->
      Config ct (Container t2 fs2 lb2 sf2) ctns2 h2
             ==> Config ct (Container t2' fs2' lb2' sf2') ctns2' h2' ->
      flow_to lb1 L_Label = false ->
      flow_to lb2 L_Label = false ->
      flow_to lb2' L_Label = false ->
      L_equivalence_config (Config ct (Container t1 fs1 lb1 sf1) ctns1 h1 )
                           (Config ct (Container t2 fs2 lb2 sf2) ctns2 h2)  φ ->
     L_equivalence_heap h1 h2 φ ->
     L_equivalence_heap h1 h2' φ /\ L_equivalence_config (Config ct (Container t1 fs1 lb1 sf1) ctns1 h1)
                          (Config ct (Container t2' fs2' lb2' sf2') ctns2' h2' )  φ.
Proof with eauto. 
  intros ct t1 fs1 lb1 sf1 ctns1 h1
                              t2 fs2 lb2 sf2 ctns2 h2 
                              t2' fs2' lb2' sf2' ctns2' h2' φ.
  intro H_valid1.       intro H_valid2.
  intro H_terminal.
  intro H_reduction2. 
  intro H_flow1. intro H_flow2. intro H_flow2'. 
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

(* emp *)
  - split; auto.
    unfold low_component in H20; subst; auto;
      destruct ctns1; destruct ctns2';
        rewrite H_flow1 in H20; rewrite H_flow2 in H20;
          apply L_equivalence_config_H; auto; 
            unfold low_component; subst; auto; rewrite H_flow1; auto;
              rewrite H_flow2'; auto .

  - (* field access 1 *)
    split; auto.
    unfold low_component in H18; subst; auto;
      destruct ctns1; destruct ctns2;
        rewrite H_flow1 in H18; rewrite H_flow2 in H18;
          apply L_equivalence_config_H; auto; 
            unfold low_component; subst; auto; rewrite H_flow1; auto;
              rewrite H_flow2; auto;rewrite H_flow2'; auto.

  - (* field access 2*)
    split; auto.
    unfold low_component in H18; subst; auto;
      destruct ctns1; destruct ctns2;
        rewrite H_flow1 in H18; rewrite H_flow2 in H18;
          apply L_equivalence_config_H; auto; 
            unfold low_component; subst; auto; rewrite H_flow1; auto;
              rewrite H_flow2; auto;rewrite H_flow2'; auto.
    
(* (MethodCall (ObjId o) meth v)  *)
  - split; auto.
    unfold low_component in H19; subst; auto;
      destruct ctns1; destruct ctns2;
        rewrite H_flow1 in H19; rewrite H_flow2 in H19;
          apply L_equivalence_config_H; auto; 
            unfold low_component; subst; auto; rewrite H_flow1; auto;
              rewrite H_flow2; auto;rewrite H_flow2'; auto.

(* (MethodCall (v_opa_l v ell) meth v)  *)
  - split; auto.
    unfold low_component in H19; subst; auto;
      destruct ctns1; destruct ctns2;
        rewrite H_flow1 in H19; rewrite H_flow2 in H19;
          apply L_equivalence_config_H; auto; 
            unfold low_component; subst; auto; rewrite H_flow1; auto;
              rewrite H_flow2; auto;rewrite H_flow2'; auto.
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


(* (Config ct (Container t1' fs1' (join_label lb1 lo) sf1') ctns1' h1') *)

  - split; auto.
    assert (flow_to (join_label lb2 lo) L_Label = false).
    apply flow_join_label with lb2 lo; auto.
    apply join_label_commutative.
    
    unfold low_component in H17; subst; auto;
      destruct ctns1; destruct ctns2';
        rewrite H_flow1 in H17; rewrite H_flow2 in H17;
          apply L_equivalence_config_H; auto; 
            unfold low_component; subst; auto; rewrite H_flow1; auto;
              rewrite H_flow2'; auto;rewrite H_flow2'; auto.

(* unlabel v*)
  - split; auto.
    unfold low_component in H17; subst; auto;
      destruct ctns1; destruct ctns2';
        rewrite H_flow1 in H17; rewrite H_flow2 in H17;
          apply L_equivalence_config_H; auto; 
            unfold low_component; subst; auto; rewrite H_flow1; auto;
              rewrite H_flow2'; auto;rewrite H_flow2'; auto.

(* labelof v*)
  - split; auto.
    unfold low_component in H17; subst; auto;
      destruct ctns1; destruct ctns2';
        rewrite H_flow1 in H17; rewrite H_flow2 in H17;
          apply L_equivalence_config_H; auto; 
            unfold low_component; subst; auto; rewrite H_flow1; auto;
              rewrite H_flow2'; auto;rewrite H_flow2'; auto.  

(* objectLabelOf  *)
  - split; auto.
    unfold low_component in H17; subst; auto;
      destruct ctns1; destruct ctns2';
        rewrite H_flow1 in H17; rewrite H_flow2 in H17;
          apply L_equivalence_config_H; auto; 
            unfold low_component; subst; auto; rewrite H_flow1; auto;
              rewrite H_flow2'; auto;rewrite H_flow2'; auto.

  - split; auto.
    unfold low_component in H17; subst; auto;
      destruct ctns1; destruct ctns2';
        rewrite H_flow1 in H17; rewrite H_flow2 in H17;
          apply L_equivalence_config_H; auto; 
            unfold low_component; subst; auto; rewrite H_flow1; auto;
              rewrite H_flow2'; auto;rewrite H_flow2'; auto.  
    
  (* raise skip *)  
  - split; auto.
    inversion H_valid1; auto. 
    inversion H_valid2; auto. 
    apply change_obj_lbl_h2_with_H_preserve_bijection with ct lo lb2' L_Label ;auto.
    subst; auto.
    assert ((join_label lb2' L_Label) = lb2').
    apply join_L_Label_irrelevant ; auto. rewrite H2. auto. 

    inversion H_valid1; subst; auto. 
    inversion H_valid2; subst; auto. 
    apply change_obj_lbl_h2_preserve_config_eq with lo lb2' L_Label; auto.

    apply L_equivalence_config_H; auto.
    destruct ctns2'.
    unfold low_component in H19.
    unfold low_component.
    rewrite H18. rewrite H18 in H19. auto.
    unfold low_component in H19.
    unfold low_component.
    rewrite H18. rewrite H18 in H19. auto.

    assert ((join_label lb2' L_Label) = lb2').
    apply join_L_Label_irrelevant ; auto. rewrite H2. auto. 

  (* raise skip *)  
  - split; auto.
    inversion H_valid1; auto. 
    inversion H_valid2; auto. 
    apply change_obj_lbl_h2_with_H_preserve_bijection with ct lo lb2' L_Label ;auto.
    subst; auto.
    assert ((join_label lb2' L_Label) = lb2').
    apply join_L_Label_irrelevant ; auto. rewrite H2. auto. 

    inversion H_valid1; subst; auto. 
    inversion H_valid2; subst; auto.
    assert (flow_to lb2' (join_label lb2' ell) = true).
    apply join_def_flow1.
    eauto using flow_trans. 
    apply change_obj_lbl_h2_preserve_config_eq with lo lb2' L_Label; auto.
    inversion H_valid2; subst; auto.
    inversion H_valid1; subst; auto.
    
    apply L_equivalence_config_H; auto.
    destruct ctns2'.
    unfold low_component in H19.
    unfold low_component.
    rewrite H18. rewrite H18 in H19. auto.
    unfold low_component in H19.
    unfold low_component.
    rewrite H18. rewrite H18 in H19. auto.

    assert ((join_label lb2' L_Label) = lb2').
    apply join_L_Label_irrelevant ; auto.
    rewrite H2.
    assert (flow_to lb2' (join_label lb2' ell) = true).
    apply join_def_flow1.
    eauto using flow_trans. 

 (* toLabled *)   
  - split; auto.
    unfold low_component in H16; subst; auto;
      destruct ctns1; destruct ctns2;
        rewrite H_flow1 in H16; rewrite H_flow2 in H16;
          apply L_equivalence_config_H; auto; 
            unfold low_component; subst; auto; rewrite H_flow1; auto;
              rewrite H_flow2'; auto;rewrite H_flow2'; auto.

- split; auto.
    unfold low_component in H17; subst; auto;
      destruct ctns1; destruct ctns2';
        rewrite H_flow1 in H17; rewrite H_flow2 in H17;
          apply L_equivalence_config_H; auto; 
            unfold low_component; subst; auto; rewrite H_flow1; auto;
              rewrite H_flow2'; auto;rewrite H_flow2'; auto.

    
  (*field update normal *)

  - split; auto.
    apply update_h2_with_H_preserve_bijection with ct lb2' L_Label; auto.
    inversion H_valid1. auto.

    assert ((join_label lb2' L_Label) = lb2').
    apply join_L_Label_irrelevant ; auto.
    rewrite H0.
    assert (flow_to lb2' (join_label (runtime_label v) lb2')  = true).
    apply join_def_flow2.
    eauto using flow_trans. 

    
    assert (forall a1 a2 : oid, decision.Decision (a1 = a2)). auto.     
    apply update_field_h2_preserve_config_eq with lb2' L_Label; auto.
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

    assert ((join_label lb2' L_Label) = lb2').
    apply join_L_Label_irrelevant ; auto.
    rewrite H2.
    assert (flow_to lb2' (join_label (runtime_label v) lb2')  = true).
    apply join_def_flow2.
    eauto using flow_trans. 
    

  (*field update opaque  *)

  - split; auto.
    unfold low_component in H18; subst; auto;
      destruct ctns1; destruct ctns2';
        rewrite H_flow1 in H18; rewrite H_flow2 in H18;
          apply L_equivalence_config_H; auto; 
            unfold low_component; subst; auto; rewrite H_flow1; auto;
              rewrite H_flow2'; auto;rewrite H_flow2'; auto.

(* if guard s1 s2*)
  - split; auto.
    unfold low_component in H17; subst; auto;
      destruct ctns1; destruct ctns2';
        rewrite H_flow1 in H17; rewrite H_flow2 in H17;
          apply L_equivalence_config_H; auto; 
            unfold low_component; subst; auto; rewrite H_flow1; auto;
              rewrite H_flow2'; auto;rewrite H_flow2'; auto.


  (*  L_equivalence_config (Config ct (Container (v_opa_l t1 lb1) fs1' lb1' sf1') ctns1' h1')
   (Config ct (Container t2 fs2 lb2 sf2) ctns2 h2) φ *)
  - split; auto.
    unfold low_component in H18; subst; auto;
      destruct ctns2'; destruct ctns1;
        rewrite H_flow2 in H18; rewrite H_flow1 in H18;
          apply L_equivalence_config_H; auto; 
            unfold low_component; subst; auto; rewrite  H_flow2';  auto;
              rewrite H_flow1; auto; rewrite   H_flow2' in H18; auto.


  (* L_equivalence_config
   (Config ct (Container (v_opa_l v (join_label ell lb1)) fs1' lb1' sf1') ctns1' h1')
   (Config ct (Container t2 fs2 lb2 sf2) ctns2 h2) φ *)
  - split; auto.
    unfold low_component in H16; subst; auto;
      destruct ctns2'; destruct ctns1;
        rewrite H_flow1 in H16; rewrite H_flow2 in H16;
          apply L_equivalence_config_H; auto; 
            unfold low_component; subst; auto; rewrite  H_flow2';  auto;
              rewrite H_flow1; auto; rewrite   H_flow2' in H16; auto.
    Qed. 
Hint Resolve simulation_Terminal_H2H. 
