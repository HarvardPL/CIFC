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

Lemma runtime_label_consist : forall v1 v2 h1 h2 φ,
        L_equivalence_tm v1 h1 v2 h2 φ ->
        value v1 ->
        flow_to (runtime_label v1) L_Label = 
        flow_to (runtime_label v2) L_Label.
    Proof with eauto.
      intros.
      inversion H0; subst; auto;
        inversion H; subst; auto.
      unfold runtime_label. rewrite H5; rewrite H6. auto.
    Qed. Hint Resolve runtime_label_consist.
    

Lemma l_eq_val_not_opa : forall v1 v2 h1 h2 φ,
        L_equivalence_tm v1 h1 v2 h2 φ ->
        value v1 ->
        (forall (v0 : tm) (lb0 : Label), v1 <> v_opa_l v0 lb0) ->
        (forall (v0 : tm) (lb0 : Label), v2 <> v_opa_l v0 lb0).
    Proof with eauto.
      intros.
      inversion H0; subst; auto;
        inversion H; subst; auto;
          try (intro contra; inversion contra; fail).
      destruct H1 with v lb; auto.
      destruct H1 with v lb;  auto.
    Qed. Hint Resolve l_eq_val_not_opa.

Lemma l_eq_val_opa : forall v1 v2 h1 h2 φ,

    L_equivalence_tm v1 h1 v2 h2 φ ->
    value v1 ->
    (exists v0 lb0,  v1 = v_opa_l v0 lb0) ->
    (exists v0 lb0,  v2 = v_opa_l v0 lb0).
Proof with eauto.
      intros.
      inversion H0; subst; auto;
        inversion H; subst; auto;
          try (destruct H1 as [v0]; destruct H1 as [lb0]; inversion H1).
      inversion H1; subst; auto.
      exists e2. exists lb0; auto.
      inversion H1; subst; auto.
      exists e2. exists l2; auto.
Qed. Hint Resolve l_eq_val_opa.

  
  
  
  