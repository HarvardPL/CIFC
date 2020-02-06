Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Require Import Language.
Require Import Lemmas.
(* Require Import Low_eq. *)
Require Import Label.
Require Import Types. 


Lemma typed_value_is_wfe_stack_val : forall h v T ct gamma, 
    tm_has_type ct gamma h v T ->
    value v ->
    wfe_stack_val ct h v.
Proof with eauto.
      intros.
      generalize dependent T. 
      induction H0; subst; auto.
      intros.
      inversion H; subst; auto.
      destruct H6 as [F0].
      destruct H0 as [lo0].
      destruct H2 as [field_defs].
      destruct H2 as [method_defs].
      subst; auto. 
      apply stack_val_object with cls_name F0 lo0 field_defs method_defs; auto.

      intros.
      inversion H; subst; auto.
      apply stack_val_labeled; auto.
      apply IHvalue with T0; auto.

      intros.
      inversion H0; subst; auto.
      apply stack_val_opa_labeled; auto.
      inversion H2; subst; auto.
      inversion H6; subst; auto.
      destruct H8 as [field_defs].
      destruct H3 as [method_defs].
      destruct H14 as [F].
      destruct H8 as [lo].
      eauto using stack_val_object.

      inversion H2; subst; auto.
      eauto using stack_val_object.

      destruct H with v0 lb0.
      auto. 
Qed. Hint Resolve typed_value_is_wfe_stack_val.


Lemma hole_free_if : forall t1 t2,
    (if hole_free t1 then hole_free t2 else false)
    = true
    -> hole_free t1 = true /\ hole_free t2 = true.
Proof.
      intros.
      case_eq (hole_free t1).
      intro. case_eq (hole_free t2). intro. auto.
      intro. rewrite H0 in H. rewrite H1 in H. intuition. intro. rewrite H0 in H. intuition.
Qed. Hint Resolve hole_free_if.

Lemma hole_free_if_triple : forall guard s1 s2,
    (if hole_free guard then if hole_free s1 then hole_free s2 else false else false) = true
    -> hole_free guard = true /\ hole_free s1 = true /\ hole_free s2 = true.
Proof with eauto.
  intros.
  case_eq (hole_free guard); intro.
  rewrite H0 in H.
  apply hole_free_if in H.
  destruct H. auto.
  rewrite H0 in H. intuition. 
Qed.
Hint Resolve hole_free_if_triple.


Lemma expand_heap_preserve_wfe_stack_val : forall v h ct ho,
         value v -> wfe_heap ct h ->
         wfe_stack_val ct h v ->
         wfe_stack_val ct (add_heap_obj h (get_fresh_oid h) ho) v.
Proof with eauto.
       intros.
       induction H; inversion H1; subst; auto.
        apply stack_val_object with cls_name F lo
                                   field_defs  method_defs; auto.
       apply extend_heap_lookup_eq; auto.
       apply lookup_extend_heap_fresh_oid with ct (Heap_OBJ (class_def cls_name field_defs method_defs) F lo); auto.
Qed. Hint Resolve expand_heap_preserve_wfe_stack_val.
     

Lemma expand_heap_preserve_valid_ctn : forall ctn ho h ct,
         wfe_heap ct h ->
         valid_ctn ct ctn h ->
         valid_ctn ct ctn (add_heap_obj h (get_fresh_oid h) ho).
Proof with eauto.
       intros.
       inversion H0; subst; auto.
       apply valid_container; auto.
       inversion H5; subst; auto.
       apply stack_frame_wfe; auto.
       intros. destruct H6 with x v;auto.
Qed. Hint Resolve expand_heap_preserve_valid_ctn.


Lemma expand_heap_preserve_valid_ctns : forall ctns ho h ct,
         wfe_heap ct h ->
         valid_ctns ct ctns h ->
         valid_ctns ct ctns (add_heap_obj h (get_fresh_oid h) ho).
Proof with eauto.
       intros. induction ctns. auto.
       destruct a. auto.
       inversion H0; subst; auto.
Qed. Hint Resolve  expand_heap_preserve_valid_ctns.


Lemma update_heap_preserve_wfe_stack_val : forall o v h ct F f cls lo v0,
         value v0 -> wfe_heap ct h ->
         wfe_stack_val ct h v0 ->
         Some (Heap_OBJ cls F lo) = lookup_heap_obj h o ->
         wfe_stack_val ct (update_heap_obj h o (Heap_OBJ cls (fields_update F f v) lo)) v0.
Proof with eauto.
       intros.
       induction H; inversion H1; subst; auto.
       case_eq (beq_oid o0 o); intro.
       apply beq_oid_equal in H. subst; auto. 
       assert (Some (Heap_OBJ cls (fields_update F f v) lo) =
                     lookup_heap_obj
                       (update_heap_obj h o (Heap_OBJ cls (fields_update F f v) lo)) o).
       apply lookup_updated with h (Heap_OBJ cls F lo); auto.       
       apply stack_val_object with cls_name (fields_update F f v) lo
                                   field_defs  method_defs; auto.
       rewrite <- H2 in H3; inversion H3; subst; auto.
       inversion H1; subst; auto.
       assert (Some (Heap_OBJ (class_def cls_name0 field_defs0 method_defs0) F1 lo1) =
                     lookup_heap_obj
                       (update_heap_obj h o (Heap_OBJ cls (fields_update F f v) lo)) o0).
       apply lookup_updated_not_affected with o (Heap_OBJ cls (fields_update F f v) lo) h; auto. intro contra. rewrite contra in H.
       pose proof (beq_oid_same o). try (inconsist).
       apply stack_val_object with cls_name0 F1 lo1
                                   field_defs0  method_defs0; auto.
Qed. Hint Resolve update_heap_preserve_wfe_stack_val.

Lemma update_heap_preserve_valid_ctn  : forall  o v h ct F f cls lo ctn,
    wfe_heap ct h ->
    valid_ctn ct ctn h ->
    Some (Heap_OBJ cls F lo) = lookup_heap_obj h o ->
    valid_ctn ct ctn (update_heap_obj h o (Heap_OBJ cls (fields_update F f v) lo)).
Proof with eauto.
  intros.
  inversion H0; subst; auto.
  apply valid_container; auto.
  apply stack_frame_wfe; auto.
  intros.
  split; auto.
  inversion H6; subst; auto.
  destruct H8 with x v0; auto.
  apply update_heap_preserve_wfe_stack_val; auto.
  inversion H6; subst; auto.
  destruct H8 with x v0; auto.
  inversion H6; subst; auto.
  destruct H8 with x v0; auto. 
Qed. Hint Resolve  update_heap_preserve_valid_ctn.


Lemma update_heap_preserve_valid_ctns : forall  o v h ct F f cls lo ctns,
    wfe_heap ct h ->
    valid_ctns ct ctns h ->
    Some (Heap_OBJ cls F lo) = lookup_heap_obj h o ->
    valid_ctns ct ctns (update_heap_obj h o (Heap_OBJ cls (fields_update F f v) lo)).
Proof with eauto.
       intros. induction ctns. auto.
       destruct a. auto.
       inversion H0; subst; auto.
Qed. Hint Resolve  update_heap_preserve_valid_ctns.


Lemma change_obj_label_preserve_wfe_stack_val : forall o v h ct F cls lo lo',
         value v ->
         wfe_heap ct h ->
         wfe_stack_val ct h v ->
         Some (Heap_OBJ cls F lo) = lookup_heap_obj h o ->
         wfe_stack_val ct (update_heap_obj h o (Heap_OBJ cls F lo')) v.
Proof with eauto.
  intros.
  induction H; subst; auto.
  inversion H1; subst; auto.
  
  case_eq (beq_oid o0 o); intro.
  apply beq_oid_equal in H. subst; auto. 
  assert (Some (Heap_OBJ cls F lo') =
                     lookup_heap_obj
                       (update_heap_obj h o (Heap_OBJ cls F lo')) o).
  apply lookup_updated with h (Heap_OBJ cls F lo); auto.       
  apply stack_val_object with cls_name F lo'
                              field_defs  method_defs; auto.
  rewrite <- H2 in H3; inversion H3; subst; auto. 

  inversion H1; subst; auto.
  assert (Some (Heap_OBJ (class_def cls_name0 field_defs0 method_defs0) F1 lo1) =
                     lookup_heap_obj
                       (update_heap_obj h o (Heap_OBJ cls F lo')) o0).
  apply lookup_updated_not_affected with o (Heap_OBJ cls F lo') h; auto.
  intro contra. rewrite contra in H.
  pose proof (beq_oid_same o).
  try (inconsist).
  apply stack_val_object with cls_name0 F1 lo1
                              field_defs0  method_defs0; auto.

  inversion H1; subst; auto.
  inversion H1; subst; auto.
Qed. Hint Resolve change_obj_label_preserve_wfe_stack_val .


Lemma change_obj_label_preserve_valid_ctn  : forall  o h ct F cls lo lo' ctn,
    wfe_heap ct h ->
    valid_ctn ct ctn h ->
    Some (Heap_OBJ cls F lo) = lookup_heap_obj h o ->
    valid_ctn ct ctn (update_heap_obj h o (Heap_OBJ cls F lo')).
Proof with eauto.
  intros.
  inversion H0; subst; auto.
  apply valid_container; auto.
  apply stack_frame_wfe; auto.
  intros.
  split; auto.
  inversion H6; subst; auto.
  destruct H8 with x v; auto.

  apply change_obj_label_preserve_wfe_stack_val with lo; auto.
  inversion H6; subst; auto.
  destruct H8 with x v; auto.

  inversion H6; subst; auto.
  destruct H8 with x v; auto.
Qed. Hint Resolve change_obj_label_preserve_valid_ctn.


Lemma change_obj_label_preserve_valid_ctns : forall  o h ct F cls lo lo' ctns,
    wfe_heap ct h ->
    valid_ctns ct ctns h ->
    Some (Heap_OBJ cls F lo) = lookup_heap_obj h o ->
    valid_ctns ct ctns (update_heap_obj h o (Heap_OBJ cls F lo')).
Proof with eauto.
       intros. induction ctns. auto.
       destruct a. auto.
       inversion H0; subst; auto.
       apply valid_ctns_list; auto.
       apply change_obj_label_preserve_valid_ctn with lo; auto. 
Qed. Hint Resolve change_obj_label_preserve_valid_ctns.

Lemma exclude_middle_runtime_val : forall v1 v2,
    value v1 -> value v2->
    runtime_val v1 = runtime_val v2 \/ runtime_val v1 <> runtime_val v2.
Proof with eauto.

  intros.
  generalize dependent v2.
  induction v1; inversion H; intros;
    induction v2; inversion H0; intros; auto;
      try (intros; right; unfold runtime_val; intro contra; inversion contra; fail); try (subst; auto); try (inversion H2; subst; auto; fail); try (inversion H1; subst; auto; fail).
Qed.
Hint Resolve exclude_middle_runtime_val. 


Lemma valid_config_preservation : forall T ct
                                          ctn ctns h
                                          ctn' ctns' h',
    config_has_type ct empty_context (Config ct ctn ctns h) T ->
    valid_config (Config ct  ctn ctns h) ->
    Config ct ctn ctns h
           ==> Config ct ctn' ctns' h' ->
    valid_config (Config ct ctn' ctns' h').
Proof with eauto.
  intros T ct ctn ctns h ctn' ctns' h'.
  intro H_typing. 
  intro H_valid.
  intro H_reduction.
  remember (Config ct ctn ctns h) as config.
  remember (Config ct ctn' ctns' h') as config'.
  generalize dependent ctn. generalize dependent ctn'.
  generalize dependent T. generalize dependent h.
  generalize dependent h'.
  generalize dependent ctns. 
  generalize dependent ctns'.
  induction H_reduction; intros;
    inversion   Heqconfig'; inversion  Heqconfig;
      inversion H_valid; subst; auto;        try
      (match goal with
    | H : valid_ctn _ _ _ |- _
      => inversion H; subst; auto 
      end;
        subst; auto;
    apply valid_conf; auto;
    apply valid_container; auto;
    try (apply valid_fs_list; auto;
      intro contra; inversion contra);
    try (
        match goal with
        | H :  valid_syntax (_ _) |- _
          => inversion H; subst; auto
        | H :  valid_syntax (_ _ _) |- _
          => inversion H; subst; auto
        | H :  valid_syntax (_ _ _ _) |- _
          => inversion H; subst; auto
        end; auto);
      intros; intro contra; inversion contra; fail);
    try (apply valid_conf; auto;
    match goal with
    | H : valid_ctn _ _ _ |- _
      => inversion H; subst; auto 
    end;
    apply valid_container; auto;
    match goal with
    | H : valid_fs _ |- _
      => inversion H; subst; auto 
    end;
    match goal with
    | H : valid_fs _ |- _
      => inversion H; subst; auto 
    end;
    inversion H3; auto; 
    intros;
    intro contra; inversion contra; 
    subst; auto; fail).  
  
  
  - inversion H16; subst; auto.
    inversion H11; subst; auto.
    destruct H0 with id v; auto.

    (*e1 ( EqCmp hole e2) *)
  - apply valid_conf; auto;
    match goal with
    | H : valid_ctn _ _ _ |- _
      => inversion H; subst; auto 
    end;
    match goal with
    | H :  valid_fs _  |- _
      => inversion H; subst; auto 
    end;
    match goal with
    | H :  hole_free  _ = true |- _
      => inversion H; subst; auto;
           match goal with
           | H : (if hole_free _ then hole_free _ else false) = true |- _
             => apply hole_free_if in H; destruct H
           end
    end;
    try (apply valid_container; auto);
      try (apply valid_fs_list; auto;
          intro contra; inversion contra; fail);
    try (    match goal with
    | H :  valid_syntax (_ _ _) |- _
      => inversion H; subst; auto
    | H :  valid_syntax (_ _ _ _) |- _
      => inversion H; subst; auto 
    end; auto; 
    intros; 
    intro contra; inversion contra);
    try (apply valid_fs_list; auto);
    try (intro contra; inversion contra);
    try (
        match goal with
    | H :  valid_syntax (_ _ _) |- _
      => inversion H; subst; auto
    | H :  valid_syntax (_ _ _ _) |- _
      => inversion H; subst; auto
        end; auto); 
    match goal with
    | H :  hole_free _ = true |- _
      => rewrite H; auto;
           try (
               match goal with
               | H1 :  hole_free _ = true |- _
                 => rewrite H1; auto
               end
             )
    end;
    try (
    match goal with
    | H : valid_ctn _ _ _ |- _
      => inversion H; subst; auto 
    end;
    apply valid_conf; auto;
    apply valid_container; auto;
    try (apply valid_fs_list; auto);
    try (intro contra; inversion contra);
         try (
        match goal with
    | H :  valid_syntax (_ _ _) |- _
      => inversion H; subst; auto
    | H :  valid_syntax (_ _ _ _) |- _
      => inversion H; subst; auto
        end; auto); 
         try (intro contra0;
              inversion contra0); fail).

  (*(Container (EqCmp v e2) fs lb sf)*)
  - apply valid_conf; auto.
    match goal with
    | H : valid_ctn _ _ _ |- _
      => inversion H; subst; auto 
    end;
    match goal with
    | H :  valid_fs _  |- _
      => inversion H; subst; auto 
    end.
    apply valid_container; auto.
    inversion H2; subst; auto.
    intros.
    intro contra. rewrite contra in H3; inversion H3.
    subst; auto.
    intros.
    intro contra. rewrite contra in H3; inversion H3.
    subst; auto.
    unfold hole_free; fold hole_free.
    inversion H16; subst; auto.
    inversion H4; subst; auto.
    inversion H2; subst; auto; try (inversion H12).
    apply surface_syntax_is_hole_free in H1.
    rewrite H1. rewrite H17; auto.
    inversion H1.     

    (*(Container e2 (EqCmp v hole :: fs) lb sf) *)
  - apply valid_conf; auto;
    match goal with
    | H : valid_ctn _ _ _ |- _
      => inversion H; subst; auto 
    end;
    match goal with
    | H :  valid_fs _  |- _
      => inversion H; subst; auto 
    end;
    match goal with
    | H :  hole_free  _ = true |- _
      => inversion H; subst; auto;
           match goal with
           | H : (if hole_free _ then hole_free _ else false) = true |- _
             => apply hole_free_if in H; destruct H
           end
    end;
    try (apply valid_container; auto);
      try (apply valid_fs_list; auto;
          intro contra; inversion contra; fail);
    try (    match goal with
    | H :  valid_syntax (_ _ _) |- _
      => inversion H; subst; auto
    | H :  valid_syntax (_ _ _ _) |- _
      => inversion H; subst; auto 
    end; auto; 
    intros; 
    intro contra; inversion contra);
    try (apply valid_fs_list; auto);
    try (intro contra; inversion contra);
    try (
        match goal with
    | H :  valid_syntax (_ _ _) |- _
      => inversion H; subst; auto
    | H :  valid_syntax (_ _ _ _) |- _
      => inversion H; subst; auto
        end; auto); 
    match goal with
    | H :  hole_free _ = true |- _
      => rewrite H; auto;
           try (
               match goal with
               | H1 :  hole_free _ = true |- _
                 => rewrite H1; auto
               end
             )
    end;
    try (
    match goal with
    | H : valid_ctn _ _ _ |- _
      => inversion H; subst; auto 
    end;
    apply valid_conf; auto;
    apply valid_container; auto;
    try (apply valid_fs_list; auto);
    try (intro contra; inversion contra);
         try (
        match goal with
    | H :  valid_syntax (_ _ _) |- _
      => inversion H; subst; auto
    | H :  valid_syntax (_ _ _ _) |- _
      => inversion H; subst; auto
        end; auto); 
         try (intro contra0;
              inversion contra0); fail).
    
    
  (*(Container (EqCmp v1 v2) fs lb sf) *)
- apply valid_conf; auto.
    match goal with
    | H : valid_ctn _ _ _ |- _
      => inversion H; subst; auto 
    end;
    match goal with
    | H :  valid_fs _  |- _
      => inversion H; subst; auto 
    end.
    apply valid_container; auto;
    intros;
    intro contra; rewrite contra in H4; inversion H4;
      subst; auto.
    apply value_is_hole_free in H.
    unfold hole_free; fold hole_free.
    rewrite H18. rewrite H; auto.
    
(*(Container result fs lb sf) ct *)
- assert (valid_syntax result);
  assert (runtime_val v1 = runtime_val v2 \/ runtime_val v1 <> runtime_val v2); auto.
  destruct H3; auto. apply H1 in H3; subst; auto.
  apply H2 in H3; subst; auto.
  destruct H4; subst; auto.  apply H1 in H4.
  try ( 
  apply valid_conf; auto;
    match goal with
    | H : valid_ctn _ _ _ |- _
      => inversion H; subst; auto 
    end;
    match goal with
    | H :  valid_fs _  |- _
      => inversion H; subst; auto 
    end;
    apply valid_container; auto).
  apply H2 in H4.
  try ( 
  apply valid_conf; auto;
    match goal with
    | H : valid_ctn _ _ _ |- _
      => inversion H; subst; auto 
    end;
    match goal with
    | H :  valid_fs _  |- _
      => inversion H; subst; auto 
    end;
    apply valid_container; auto).

  - apply config_typing_lead_to_tm_typing in H_typing.
    destruct H_typing as [T'].
    destruct H1 as [gamma].
    inversion H1; subst; auto. 
    assert (v = null \/ exists o', v = ObjId o').
    apply field_value with h0 o cls F lo fname ct cls' gamma; auto.
    apply valid_conf; auto;
    match goal with
    | H : valid_ctn _ _ _ |- _
      => inversion H; subst; auto 
    end.
    apply valid_container; auto.
    destruct H2; subst; auto.
    destruct H2 as [o']. subst; auto.
    intros; intro contra; inversion contra.
    intros; intro contra; inversion contra.
    destruct H2; subst; auto.
    destruct H2 as [o']. subst; auto.

    intro contra; inversion contra. 

  - apply config_typing_lead_to_tm_typing in H_typing.
    destruct H_typing as [T'].
    destruct H1 as [gamma].
    inversion H1; subst; auto.
    inversion H4; subst; auto.
    assert (v = null \/ exists o', v = ObjId o').
    eauto using field_value_opaque. 
    apply valid_conf; auto;
    match goal with
    | H : valid_ctn _ _ _ |- _
      => inversion H; subst; auto 
    end.
    apply valid_container; auto.
    
    destruct H2; subst; auto.
    destruct H2 as [o']. subst; auto.
    intros; intro contra; inversion contra.
    intros; intro contra; inversion contra.
    destruct H2; subst; auto.
    destruct H2 as [o']. subst; auto.

    intro contra; inversion contra. 
    
  - apply valid_conf; auto;
    match goal with
    | H : valid_ctn _ _ _ |- _
      => inversion H; subst; auto 
    end;
    match goal with
    | H :  valid_fs _  |- _
      => inversion H; subst; auto 
    end;
    match goal with
    | H :  hole_free  _ = true |- _
      => inversion H; subst; auto;
           match goal with
           | H : (if hole_free _ then hole_free _ else false) = true |- _
             => apply hole_free_if in H; destruct H
           end
    end;
    try (apply valid_container; auto);
      try (apply valid_fs_list; auto;
          intro contra; inversion contra; fail);
    try (    match goal with
    | H :  valid_syntax (_ _ _) |- _
      => inversion H; subst; auto
    | H :  valid_syntax (_ _ _ _) |- _
      => inversion H; subst; auto 
    end; auto; 
    intros; 
    intro contra; inversion contra);
    try (apply valid_fs_list; auto);
    try (intro contra; inversion contra);
    try (
        match goal with
    | H :  valid_syntax (_ _ _) |- _
      => inversion H; subst; auto
    | H :  valid_syntax (_ _ _ _) |- _
      => inversion H; subst; auto
        end; auto); 
    match goal with
    | H :  hole_free _ = true |- _
      => rewrite H; auto;
           try (
               match goal with
               | H1 :  hole_free _ = true |- _
                 => rewrite H1; auto
               end
             )
    end;
    try (
    match goal with
    | H : valid_ctn _ _ _ |- _
      => inversion H; subst; auto 
    end;
    apply valid_conf; auto;
    apply valid_container; auto;
    try (apply valid_fs_list; auto);
    try (intro contra; inversion contra);
         try (
        match goal with
    | H :  valid_syntax (_ _ _) |- _
      => inversion H; subst; auto
    | H :  valid_syntax (_ _ _ _) |- _
      => inversion H; subst; auto
        end; auto); 
         try (intro contra0;
              inversion contra0); fail).


  - inversion H16; subst; auto.
    inversion H4; subst; auto.
    apply valid_conf; auto.
    apply valid_container; auto.
    inversion H2; subst; auto.
    intros. intro contra.
    rewrite contra in H3; inversion H3; intuition.
    intros. intro contra.
    rewrite contra in H3; inversion H3; intuition.
    inversion H2; subst; auto.
    inversion H12. try (
    apply surface_syntax_is_hole_free in H1;
    unfold hole_free; fold hole_free;
    rewrite H17; rewrite H1; auto).
    inversion H12. inversion H1. inversion H12.    

   -  match goal with
    | H : valid_ctn _ _ _ |- _
      => inversion H; subst; auto 
      end.
     apply valid_conf; auto.
     apply valid_container; auto.
     apply valid_fs_list; auto.
     intro contra; inversion contra.
     intro contra; inversion contra.
     inversion H9; subst; auto.
     intros.
     intro contra; inversion contra. 
     intros.
     intro contra; inversion contra.
     inversion H19; subst; auto.
     apply hole_free_if in H3.
     destruct H3. rewrite H2. rewrite H3. auto. 

    
  - inversion H17; subst; auto.
    inversion H5; subst; auto.
    apply valid_conf; auto.
    apply valid_container; auto.
    inversion H5; subst; auto.
    intros. intro contra.
    rewrite contra in H4; inversion H4; intuition.
    intros. intro contra.
    rewrite contra in H4; inversion H4; intuition.
    unfold hole_free; fold hole_free.
    apply value_is_hole_free in H.
    apply value_is_hole_free in H0.
    rewrite H. rewrite H0. auto.


  - inversion H20; subst; auto.
    apply config_typing_lead_to_tm_typing in H_typing.
    destruct H_typing as [T'].
    destruct H2 as [gamma].
    inversion H2; subst; auto.
    inversion H7; subst; auto.
    destruct H17 as [F0].
    destruct H4 as [lo0].
    rewrite H4 in H; inversion H; subst; auto.
    rewrite <- H6 in H10. inversion H10; subst; auto.
    rewrite H11 in H0; inversion H0; subst; auto.
    
    apply valid_conf; auto.
    apply valid_ctns_list; auto.
    inversion H19; subst; auto. 
    apply valid_container; auto.
    intros. intro contra. inversion contra.
    intros. intro contra. inversion contra.
    apply stack_frame_wfe; auto.
    intros.
    case_eq (beq_id arg_id0 x);intro.
    unfold sf_update in H5. rewrite H12 in H5.
    inversion H5; subst; auto.
    split; auto. 
    induction H1; subst; inversion H9; subst; auto.
    destruct H27 as [F'].
    destruct H1 as [lo'].
    destruct H26 as [field_defs].
    destruct H13 as [method_defs].
    subst; auto. 
    apply stack_val_object with arguT F' lo'
                                field_defs method_defs; auto.
    apply stack_val_opa_labeled.
    inversion H31; subst; auto; inversion H26; subst; auto.
    destruct H35 as [F'].
    destruct H17 as [lo'].
    destruct H34 as [field_defs].
    destruct H24 as [method_defs].
    subst; auto. 
    apply stack_val_object with arguT F' lo'
                                field_defs method_defs; auto.
    destruct H33 with v0 lb1; auto. 
    
    
    unfold sf_update in H5. rewrite H12 in H5.
    inversion H5.
    intro contra; inversion contra.

(*   valid_config (Config ct (Container (MethodCall (ObjId o) meth v) fs lb sf) ctns0 h0) *)
  - inversion H20; subst; auto.
    apply config_typing_lead_to_tm_typing in H_typing.
    destruct H_typing as [T'].
    destruct H2 as [gamma].
    inversion H2; subst; auto.
    inversion H7; subst; auto.
    inversion H16; subst; auto. 
    destruct H32 as [F0].
    destruct H3 as [lo0].
    rewrite H3 in H; inversion H; subst; auto.
    rewrite <- H19 in H14; inversion H14; subst; auto.
    rewrite H15 in H0; inversion H0; subst; auto.
    
    apply valid_conf; auto.
    apply valid_container; auto.
    intros. intro contra. inversion contra.
    intros. intro contra. inversion contra.
    apply stack_frame_wfe; auto.
    intros.
    case_eq (beq_id arg_id0 x);intro.
    unfold sf_update in H4. rewrite H24 in H4.
    inversion H4; subst; auto.
    split; auto. 
    induction H1; subst; inversion H10; subst; auto.
    destruct H36 as [F'].
    destruct H1 as [lo'].
    destruct H35 as [field_defs].
    destruct H25 as [method_defs].
    subst; auto. 
    apply stack_val_object with arguT F' lo'
                                field_defs method_defs; auto.
    apply stack_val_opa_labeled.
    inversion H40; subst; auto; inversion H35; subst; auto.
    destruct H44 as [F'].
    destruct H32 as [lo'].
    destruct H43 as [field_defs].
    destruct H33 as [method_defs].
    subst; auto. 
    apply stack_val_object with arguT F' lo'
                                field_defs method_defs; auto.
    destruct H42 with v0 lb1; auto. 
    
    
    unfold sf_update in H4. rewrite H24 in H4.
    inversion H4.
    intro contra; inversion contra.

    
   - inversion H20; subst; auto.
     apply valid_conf; auto.
     auto. auto.
     apply  extend_heap_preserve_order with h0 (get_fresh_oid h0)
                                            cls_name
                                            field_defs
                                            method_defs lb; auto.
     apply fresh_oid_heap with ct ; auto.
     apply extend_heap_preserve_field_wfe with h0 (get_fresh_oid h0)
                                            cls_name
                                            field_defs
                                            method_defs lb; auto.
     apply fresh_oid_heap with ct ; auto.

     (* raise label*)
   -
     apply valid_conf; auto.
     apply change_obj_label_preserve_valid_ctns with lo; auto.
     apply change_obj_label_preserve_valid_ctn with lo; auto.
     inversion H19; subst; auto.

     eauto using change_obj_label_preserve_wfe_heap.
     eauto using change_obj_label_preserve_field_wfe.

     (* raise label*)
   -
     apply valid_conf; auto.
     apply change_obj_label_preserve_valid_ctns with lo; auto.
     apply change_obj_label_preserve_valid_ctn with lo; auto.
     inversion H19; subst; auto.

     eauto using change_obj_label_preserve_wfe_heap.
     eauto using change_obj_label_preserve_field_wfe.
     

     (* assignment *)
   -  apply valid_conf; auto;
    match goal with
    | H : valid_ctn _ _ _ |- _
      => inversion H; subst; auto 
    end.
      apply config_typing_lead_to_tm_typing in H_typing.
    destruct H_typing as [T'].
    destruct H0 as [gamma].
    inversion H0; subst; auto.
    match goal with
    | H :  valid_fs _  |- _
      => inversion H; subst; auto 
    end;    
    apply valid_container; auto;
      try (apply valid_fs_list; auto;
          intro contra; inversion contra; fail); 
    try (    match goal with
    | H :  valid_syntax (_ _ _) |- _
      => inversion H; subst; auto
    | H :  valid_syntax (_ _ _ _) |- _
      => inversion H; subst; auto 
    end;
    intros; 
    intro contra; inversion contra);
    apply stack_frame_wfe; auto;
    intros x v0; intro Hy. 
    match goal with
    | H : wfe_stack_frame  _ _ _ |- _
      => inversion H; subst; auto
    end;

    unfold sf_update in Hy; auto;
    case_eq (beq_id id x); intro;
      rewrite H2 in Hy;
    inversion Hy; subst; auto;
      split; auto.
    try (apply typed_value_is_wfe_stack_val with T0 gamma; auto).
    destruct H1 with x v0; auto.

    destruct H1 with x v0; auto.
    unfold sf_update in Hy;
    case_eq (beq_id id x); intro;
      rewrite H12 in Hy.
    inversion Hy; subst; auto. 
    split; auto.
    apply typed_value_is_wfe_stack_val with T0 gamma; auto.
    inversion H11; subst; auto.
    destruct H15 with x v0; auto.
    intro contra; inversion contra. 


   - match goal with
    | H : valid_ctn _ _ _ |- _
      => inversion H; subst; auto 
     end.
     apply valid_conf; auto.
     apply valid_container; auto.
     apply valid_fs_list; auto.
     try (
         match goal with
    | H :  valid_syntax (_ _ _) |- _
      => inversion H; subst; auto
    | H :  valid_syntax (_ _ _ _) |- _
      => inversion H; subst; auto
        end; auto).

    intro contra. inversion contra. 
    intro contra. inversion contra.
    try (
         match goal with
    | H :  valid_syntax (_ _ _) |- _
      => inversion H; subst; auto
    | H :  valid_syntax (_ _ _ _) |- _
      => inversion H; subst; auto
         end; auto).
      intros;
    intro contra; inversion contra.
    intros;
      intro contra; inversion contra.
    match goal with
    | H :  hole_free  _ = true |- _
      => inversion H; subst; auto;
           match goal with
           | H : (if hole_free _ then hole_free _ else false) = true |- _
             => apply hole_free_if in H; destruct H
           end
    end.
    rewrite H0; auto. 

   -  match goal with
    | H : valid_ctn _ _ _ |- _
      => inversion H; subst; auto 
      end.
      inversion H4; subst; auto.
     apply valid_conf; auto.
     apply valid_container; auto.     
    try (
         match goal with
    | H :  valid_syntax (_ _ _) |- _
      => inversion H; subst; auto
    | H :  valid_syntax (_ _ _ _) |- _
      => inversion H; subst; auto
         end; auto).
      intros;
        intro contra; inversion contra;
          rewrite contra in H3; inversion H3; intuition.
            intros;
        intro contra; inversion contra;
          rewrite contra in H3; inversion H3; intuition.
            inversion H2; subst; auto; try (inversion H12).
            apply surface_syntax_is_hole_free in H1; auto.
            unfold hole_free. fold hole_free.
            rewrite H1; rewrite H17. auto.

   -  match goal with
    | H : valid_ctn _ _ _ |- _
      => inversion H; subst; auto 
     end.
     apply valid_conf; auto.
     apply valid_container; auto.
     apply valid_fs_list; auto.
     intro contra; inversion contra.
     intro contra; inversion contra.
     try (
         match goal with
    | H :  valid_syntax (_ _ _) |- _
      => inversion H; subst; auto
    | H :  valid_syntax (_ _ _ _) |- _
      => inversion H; subst; auto
        end; auto).
    intro. intro contra. inversion contra. 
    intro. intro contra. inversion contra.
    match goal with
    | H :  hole_free  _ = true |- _
      => inversion H; subst; auto;
           match goal with
           | H : (if hole_free _ then hole_free _ else false) = true |- _
             => apply hole_free_if in H; destruct H
           end
    end.
    rewrite H2; auto.

    
   -  match goal with
    | H : valid_ctn _ _ _ |- _
      => inversion H; subst; auto 
      end.
      inversion H5; subst; auto.
     apply valid_conf; auto.
     apply valid_container; auto.
     intro. intro contra.
     rewrite contra in H4;
       inversion H4; subst; auto.
     intro. intro contra.
     rewrite contra in H4;
       inversion H4; subst; auto.
     unfold hole_free. fold hole_free.
     apply value_is_hole_free in H. 
     apply value_is_hole_free in H0.
     rewrite H. rewrite H0. auto.

(* valid_config (Config ct (Container (FieldWrite (ObjId o) f v) fs lb sf) ctns0 h0) *)
     (*field write normal*)
   - inversion H20; subst; auto.
     apply config_typing_lead_to_tm_typing in H_typing.
     destruct H_typing as [T'].
     destruct H0 as [gamma].
     inversion H0; subst; auto.
     inversion H7; subst; auto.
     destruct H25 as [F'].
     destruct H2 as [lo'].
     rewrite H2 in H; inversion H; subst; auto.
     rewrite <- H19 in H5; inversion H5; subst; auto. 
     
     apply valid_conf; auto.
     destruct H18 as [field_defs].
     destruct H4 as [method_defs].
     apply field_write_preserve_wfe_heap with o h0 f F' (fields_update F' f (runtime_val v))
                                              cls_def cls' lo' lo' clsT
                                              field_defs method_defs; auto.
     destruct H18 as [field_defs].
     destruct H4 as [method_defs].
     inversion H7; subst; auto.
     apply field_write_preserve_field_wfe with gamma h0 o field_defs
                                               method_defs lo'
                                               lo' v f F' (class_def clsT field_defs method_defs) clsT cls'; auto.
     
    intro contra; inversion contra. 


 (* (Config ct (Container Skip fs lb sf) ctns0 (update_heap_obj h0 o (Heap_OBJ cls (fields_update F f (runtime_val v)) lo)) *)   
   - inversion H21; subst; auto.
     apply config_typing_lead_to_tm_typing in H_typing.
     destruct H_typing as [T'].
     destruct H0 as [gamma].
     inversion H0; subst; auto.
     inversion H7; subst; auto.
     inversion H9; subst; auto. 
     destruct H30 as [F'].
     destruct H1 as [lo'].
     rewrite H1 in H; inversion H; subst; auto.
     rewrite <- H19 in H15; inversion H15; subst; auto. 
     
     apply valid_conf; auto.
     destruct H29 as [field_defs].
     destruct H3 as [method_defs].
     apply field_write_preserve_wfe_heap with o h0 f F' (fields_update F' f (runtime_val v))
                                              cls_def cls' lo' lo' clsT
                                              field_defs method_defs; auto.
     destruct H29 as [field_defs].
     destruct H3 as [method_defs].
     apply field_write_preserve_field_wfe with gamma h0 o field_defs
                                               method_defs lo'
                                               lo' v f F' (class_def clsT field_defs method_defs) clsT cls'; subst;  auto.
     
     intro contra; inversion contra.
     
 (* (Config ct (Container guard (If hole s1 s2 :: fs) lb sf) ctns0 h0) *)    
   -  match goal with
    | H : valid_ctn _ _ _ |- _
      => inversion H; subst; auto 
      end.
     apply valid_conf; auto.
     apply valid_container; auto.
     inversion H17; subst; auto.
     apply valid_fs_list; auto.
     inversion H7; subst; auto.
     intro contra; inversion contra. 
     intro contra; inversion contra.
     inversion H7; subst; auto.
     intro. intro contra; inversion contra. 
     intro. intro contra; inversion contra.
     inversion H17; subst; auto.
     apply hole_free_if_triple in H1.
     destruct H1. destruct H1.
     rewrite H0. rewrite H1. rewrite H2. auto. 

 (* (Config ct (Container guard (If hole s1 s2 :: fs) lb sf) ctns0 h0) *)    
   -  match goal with
    | H : valid_ctn _ _ _ |- _
      => inversion H; subst; auto 
      end.
     apply valid_conf; auto.
     apply valid_container; auto.
     inversion H4; subst; auto.
     apply Valid_if3; auto.
     inversion H4; subst; auto. inversion H2; subst; auto.
     inversion H4; subst; auto. inversion H2; subst; auto. 

     
     intro. intro contra; subst; auto.
     inversion H4; subst; auto.
     inversion H3; subst; auto.

     intro. intro contra; subst; auto.
     inversion H4; subst; auto.
     inversion H3; subst; auto.

     unfold hole_free. fold hole_free.
     inversion H4; subst; auto.
     inversion H2; subst; auto.

     + inversion H14.
     +
       apply surface_syntax_is_hole_free in H12.
       apply surface_syntax_is_hole_free in H14.
       rewrite H17. rewrite H12. rewrite H14. auto.

     + apply surface_syntax_is_hole_free in H15.
       apply surface_syntax_is_hole_free in H20.
       rewrite H17. rewrite H15. rewrite H20. auto.



      (* (Config ct (Container s1 fs lb sf) ctns0 h0) *)
  -   match goal with
    | H : valid_ctn _ _ _ |- _
      => inversion H; subst; auto 
      end.
     apply valid_conf; auto.
     apply valid_container; auto.
     try (
         match goal with
    | H :  valid_syntax (_ _ _) |- _
      => inversion H; subst; auto
    | H :  valid_syntax (_ _ _ _) |- _
      => inversion H; subst; auto
         end; auto).
     inversion H16; subst; auto.
     apply hole_free_if in H0.
     destruct H0. rewrite H. rewrite H0. auto. 

     (* (Config ct (Container s2 fs lb sf) ctns0 h0) *)
   -   match goal with
    | H : valid_ctn _ _ _ |- _
      => inversion H; subst; auto 
      end.
     apply valid_conf; auto.
     apply valid_container; auto.
     try (
         match goal with
    | H :  valid_syntax (_ _ _) |- _
      => inversion H; subst; auto
    | H :  valid_syntax (_ _ _ _) |- _
      => inversion H; subst; auto
         end; auto).
     inversion H16; subst; auto.
     apply hole_free_if in H0.
     destruct H0. rewrite H. rewrite H0. auto. 

     (* (Config ct (Container e1 (e2 :: fs) lb sf) ctns0 h0) *)
     
   -   match goal with
    | H : valid_ctn _ _ _ |- _
      => inversion H; subst; auto 
       end.
       apply valid_conf; auto.
       inversion H6; subst; auto.
     apply valid_container; auto.
     apply valid_fs_list; auto.  
     try (
         match goal with
    | H :  valid_syntax (_ _ _) |- _
      => inversion H; subst; auto
    | H :  valid_syntax (_ _ _ _) |- _
      => inversion H; subst; auto
         end; auto).     
     apply surface_syntax_is_hole_free in H2.
     intro contra. subst; auto. inversion H2.
     inversion H6; subst; auto.
     intro contra. subst; auto.
     unfold surface_syntax in H2. discriminate. 
     try (
         match goal with
    | H :  valid_syntax (_ _ _) |- _
      => inversion H; subst; auto
    | H :  valid_syntax (_ _ _ _) |- _
      => inversion H; subst; auto
         end; auto).
     intro. intro contra. inversion contra.
     subst; auto. inversion H2. 
     intro. intro contra. inversion contra.
     subst; auto. inversion H2. 
     inversion H6; subst; auto.     


 (* (Config ct (Container e fs lb sf) ctns0 h0) *)
   -   match goal with
    | H : valid_ctn _ _ _ |- _
      => inversion H; subst; auto 
       end.
       apply valid_conf; auto.
       inversion H3; subst; auto. 
       apply valid_container; auto.
       intro. intro contra.
       rewrite contra in H2; inversion H2;
         subst; auto.
       intro. intro contra.
       rewrite contra in H2; inversion H2;
         subst; auto.
       inversion H_typing; subst; auto.
       inversion H2; subst; auto.
       inversion H13; subst; auto.
       
       case_eq (hole_free e); intro. auto.       
       destruct H26 with e fs; auto.

   (*(Config ct (Container (v_opa_l v lb) fs' lb' sf') ctns' h0)*)

   -   match goal with
    | H : valid_ctn _ _ _ |- _
      => inversion H; subst; auto 
       end.       
       inversion H15; subst; auto.
       inversion H5; subst; auto.       
       apply valid_conf; auto.
       apply valid_container; auto.
       apply Valid_v_opa_l; auto.
       intros. intro contra; subst; auto.
       destruct H1 with v0 lb0; auto. inversion H;auto. 
       
   -   match goal with
    | H : valid_ctn _ _ _ |- _
      => inversion H; subst; auto 
       end.       
       inversion H15; subst; auto.
       inversion H12; subst; auto. 
       inversion H11; subst; auto.
       inversion H2; subst; auto. 
       
   -   match goal with
    | H : valid_ctn _ _ _ |- _
      => inversion H; subst; auto 
       end.       
       inversion H15; subst; auto.
       inversion H12; subst; auto. 
       inversion H11; subst; auto.
       inversion H2; subst; auto. 
Qed.  Hint Resolve valid_config_preservation. 



(*
Inductive well_typed_ctn : Class_table -> typing_context ->
                           stack_frame -> heap -> Prop :=           
| well_typed_sf_obj :  forall ct sf gamma x h cls_def F lb o clsT field_defs method_defs,
    gamma x = Some (classTy clsT) ->
    sf x = Some (ObjId o) ->
    cls_def = class_def clsT field_defs method_defs -> 
    lookup_heap_obj h o = Some (Heap_OBJ cls_def F lb) ->
    well_typed_ctn ct gamma sf h
| well_typed_sf_lb : forall ct sf gamma x h lb,
    gamma x = Some LabelTy ->
    sf x = Some lb ->
    well_typed_ctn ct gamma sf h
| well_typed_sf_labeled_v : forall sf ct gamma x h lb v T,
    tm_has_type ct gamma h v T ->
    gamma x = Some LabelTy ->
    sf x = Some lb ->
    well_typed_ctn ct gamma sf h.         
                   
    *)

Ltac inconsist_hole_free :=
  match goal with
  | H : hole_free  (_ hole)  = true |- _
    =>  solve [inversion H]
  | H : hole_free  (_ hole _)  = true |- _
    =>  solve [inversion H]
  | H : hole_free  (_ hole _ _)  = true |- _
    =>  solve [inversion H]
  | H : hole_free  (_ _ _ hole)  = true |- _
    =>  solve [inversion H]
  | H : surface_syntax hole = true |- _
    => solve [inversion H]
  | H : value hole  |- _
    => solve [inversion H]
  end. 
  

Ltac destruct_hole_free :=
  match goal with
  |  H : forall (top : tm) (fs' : list tm),
      ?X :: ?Y = top :: fs'
      -> hole_free top = true |- _
     => pose proof (H ?X ?Y) as Hy;
        simpl in Hy; intuition 
  end.

Ltac destructs :=
  match goal with
  | H : _ /\ _ |- _
    => destruct H; destructs
  end.


Lemma expand_heap_preserve_typed_tm : forall t h ct ho T Gamma,
         wfe_heap ct h ->
         tm_has_type ct Gamma h t T ->
         tm_has_type ct Gamma (add_heap_obj h (get_fresh_oid h) ho) t T.
  Proof with eauto.
    intros.
    induction H0; auto.
    apply T_EqCmp with clsT; subst; auto.    
    apply T_FieldAccess with cls_def clsT (find_fields cls_def); subst; auto.
    apply T_MethodCall with (update_typing empty_context arg_id (classTy arguT))
                            T cls_def body arg_id arguT; subst; auto.
    eauto using tm_has_type.
    apply T_raiseLabel with clsT; auto. 
    apply T_assignment with T; subst; auto.
    apply T_FieldWrite with cls_def clsT cls'; subst;  auto.
    apply T_sequence with T; subst; auto. 

    destruct H2 as [F].
    destruct H2 as [lo].
    assert (lookup_heap_obj
                 (add_heap_obj h (get_fresh_oid h) ho) o
               = Some  (Heap_OBJ cls_def F lo)).
    apply extend_heap_lookup_eq; auto.
    apply lookup_extend_heap_fresh_oid with CT (Heap_OBJ cls_def F lo); auto.
    apply T_ObjId with cls_def; auto.
    exists F. exists lo. auto.
Qed. Hint Resolve  expand_heap_preserve_typed_tm.

  Lemma expand_heap_preserve_typed_hole_tm : forall t h ct ho T Gamma,
         wfe_heap ct h ->
         tm_hole_has_type ct Gamma h t T ->
         tm_hole_has_type ct Gamma (add_heap_obj h (get_fresh_oid h) ho) t T.
  Proof with eauto.
    intros.
    induction H0; subst; auto.
    eauto using T_EqCmp1.
    eauto using T_EqCmp2.
    eauto using T_hole_FieldAccess.
    eauto using T_hole_MethodCall1.
    eauto using T_hole_MethodCall2.
    eauto using T_hole_FieldWrite1.
    eauto using T_hole_FieldWrite2.
  Qed. Hint Resolve expand_heap_preserve_typed_hole_tm.

  
  Lemma expand_heap_preserve_typed_fs : forall fs h ct ho T T0 Gamma,
         wfe_heap ct h ->
         fs_has_type ct Gamma h fs (ArrowTy T T0) ->
         fs_has_type ct Gamma (add_heap_obj h (get_fresh_oid h) ho) fs (ArrowTy T T0).
  Proof with eauto.
    intros. generalize dependent T. generalize dependent T0.
    induction fs; intros; auto.
    inversion H0; auto.
    inversion H0; subst; auto.
    apply T_fs_no_hole with T2; auto.
    apply T_fs_hole with T' T2; auto.
  Qed. Hint Resolve expand_heap_preserve_typed_fs.
    

  Lemma expand_heap_preserve_typed_sf : forall ct Gamma sf h ho,
      wfe_heap ct h ->
      well_typed_stack_frame ct Gamma sf h -> 
      well_typed_stack_frame ct Gamma sf (add_heap_obj h (get_fresh_oid h) ho).
  Proof with eauto.
    intros.     
    inversion H0; subst; auto.
    apply well_typed_sf; auto; intros.
    destruct H1 with x T; auto. destruct H3. 
    rename x0 into v. exists v; split; auto.
  Qed. Hint Resolve expand_heap_preserve_typed_sf.

  Lemma expand_heap_preserve_typed_ctn : forall  h ct ho T Gamma ctn,
         wfe_heap ct h ->
         ctn_has_type ct Gamma h ctn T ->
         ctn_has_type ct Gamma (add_heap_obj h (get_fresh_oid h) ho) ctn T.
  Proof with eauto.
    intros.
    induction H0; subst; auto.
    apply T_ctn_type with T T0; auto.
    apply T_ctn_caller with  T0; auto. 
  Qed. Hint Resolve   expand_heap_preserve_typed_ctn.

  
  Lemma expand_heap_preserve_typed_ctns : forall  h ct ho T T0 Gamma ctns,
         wfe_heap ct h ->
         ctn_list_has_type ct Gamma h ctns (ArrowTy T0 T) ->
         ctn_list_has_type ct Gamma (add_heap_obj h (get_fresh_oid h) ho) ctns (ArrowTy T0 T).
  Proof with eauto.
    intros.
    induction H0; subst; auto.
    apply T_ctn_list with T2 Gamma'; auto. 
  Qed. Hint Resolve   expand_heap_preserve_typed_ctns.

  
  
  Lemma field_write_preserve_typed_tm : forall ct h t Gamma o F lb F' lb' T
                                               cls_def clsT field_defs method_defs,
      wfe_heap ct h ->
      tm_has_type ct Gamma h t T ->
      Some (Heap_OBJ cls_def F lb) = lookup_heap_obj h o ->
      cls_def = class_def clsT field_defs method_defs ->
      Some cls_def = ct clsT ->
      tm_has_type ct Gamma (update_heap_obj h o (Heap_OBJ cls_def F' lb')) t T.
  Proof with eauto.
    intros.
    induction H0; auto.
    apply T_EqCmp with clsT0; auto.
    apply T_FieldAccess with cls_def0 clsT0 (find_fields cls_def0); subst; auto.
    apply T_MethodCall with (update_typing empty_context arg_id (classTy arguT))
                            T cls_def0 body arg_id arguT; subst; auto.
    eauto using tm_has_type.
    apply T_raiseLabel with clsT0; auto. 
    apply T_assignment with T; subst; auto.
    apply T_FieldWrite with cls_def0 clsT0 cls'; subst;  auto.
    apply T_sequence with T; subst; auto. 

    destruct H5 as [F0].
    destruct H5 as [lo'].
    remember ( (update_heap_obj h o (Heap_OBJ cls_def F' lb'))) as h'.
    case_eq (beq_oid o0 o); intro.
    apply beq_oid_equal in H6.
    
    assert (Some (Heap_OBJ cls_def F' lb') = lookup_heap_obj h' o0).
    apply lookup_updated with h (Heap_OBJ cls_def F lb); auto;
      subst; auto.
    subst; auto.
    rewrite H5 in H1; inversion H1; subst; auto.
    apply T_ObjId with (class_def clsT field_defs method_defs); auto.
    exists F'. exists lb'. auto.

    assert (Some (Heap_OBJ cls_def0 F0 lo') = lookup_heap_obj h' o0).
    apply lookup_updated_not_affected with o  (Heap_OBJ cls_def F' lb') h; auto.
    intro contra; subst; auto.
    pose proof (beq_oid_same o); try (inconsist).
    apply T_ObjId with cls_def0; auto.
    exists F0. exists lo'. auto.
  Qed. Hint Resolve field_write_preserve_typed_tm.


  Lemma field_write_preserve_typed_hole_tm : forall ct h t Gamma o F lb F' lb' T
                                               cls_def clsT field_defs method_defs,
      wfe_heap ct h ->
      tm_hole_has_type ct Gamma h t T ->
      Some (Heap_OBJ cls_def F lb) = lookup_heap_obj h o ->
      cls_def = class_def clsT field_defs method_defs ->
      Some cls_def = ct clsT ->
      tm_hole_has_type ct Gamma (update_heap_obj h o (Heap_OBJ cls_def F' lb')) t T.
  Proof with eauto.
    intros.
    induction H0; subst; auto.
    apply T_EqCmp1 with e1; auto;
      eauto using field_write_preserve_typed_tm; auto. 
    apply T_EqCmp2 with e2; auto;
      eauto using field_write_preserve_typed_tm; auto. 
    apply T_hole_FieldAccess with cls_def0 (find_fields cls_def0); auto;
      eauto using field_write_preserve_typed_tm; auto.

    eauto using T_hole_MethodCall1.
    eauto using T_hole_MethodCall2.

    eauto using T_hole_if. 
    eauto using T_hole_FieldWrite1.
    eauto using T_hole_FieldWrite1.
  Qed. Hint Resolve  field_write_preserve_typed_hole_tm.



   Lemma field_write_preserve_typed_fs : forall ct h fs Gamma o F lb F' lb' T T0
                                                cls_def clsT field_defs method_defs ,
      wfe_heap ct h ->
      fs_has_type ct Gamma h fs (ArrowTy T T0) ->
      Some (Heap_OBJ cls_def F lb) = lookup_heap_obj h o ->
      cls_def = class_def clsT field_defs method_defs ->
      Some cls_def = ct clsT ->
      fs_has_type ct Gamma (update_heap_obj h o (Heap_OBJ cls_def F' lb')) fs (ArrowTy T T0).
  Proof with eauto.
    intros. generalize dependent T. generalize dependent T0.
    induction fs; intros; auto.
    inversion H0; auto.
    inversion H0; subst; auto.
    apply T_fs_no_hole with T2; auto.
    eauto using field_write_preserve_typed_tm; auto.     
    apply T_fs_hole with T' T2; auto.
    eauto using field_write_preserve_typed_hole_tm; auto.
  Qed. Hint Resolve field_write_preserve_typed_fs.


  Lemma field_write_preserve_typed_sf : forall ct h sf Gamma o F lb F' lb'
                                                cls_def clsT field_defs method_defs,
      wfe_heap ct h ->
      well_typed_stack_frame ct Gamma sf h ->
      Some (Heap_OBJ cls_def F lb) = lookup_heap_obj h o ->
      cls_def = class_def clsT field_defs method_defs ->
      Some cls_def = ct clsT ->
      well_typed_stack_frame ct Gamma sf (update_heap_obj h o (Heap_OBJ cls_def F' lb')).
  Proof with eauto.
    intros.     
    inversion H0; subst; auto.
    apply well_typed_sf; auto; intros.
    destruct H4 with x T; auto. destruct H5.
    rename x0 into v. 
    exists v; split; auto.    
    apply field_write_preserve_typed_tm with F lb clsT field_defs
                                             method_defs; auto.
  Qed. Hint Resolve field_write_preserve_typed_sf.

  Lemma field_write_preserve_typed_ctn : forall ct h ctn Gamma o F lb F' lb' T T0
                                                cls_def clsT field_defs method_defs ,
      wfe_heap ct h ->
      ctn_has_type ct Gamma h ctn (ArrowTy T T0) ->
      Some (Heap_OBJ cls_def F lb) = lookup_heap_obj h o ->
      cls_def = class_def clsT field_defs method_defs ->
      Some cls_def = ct clsT ->
      ctn_has_type ct Gamma (update_heap_obj h o (Heap_OBJ cls_def F' lb')) ctn (ArrowTy T T0).
  Proof with eauto.
    intros.
    induction H0; subst; auto.
    apply T_ctn_type with T1 T2; auto.
    eauto using field_write_preserve_typed_tm; auto.
    eauto using field_write_preserve_typed_sf; auto.
    eauto using field_write_preserve_typed_fs; auto.
    
    apply T_ctn_caller with T2; auto.
    eauto using field_write_preserve_typed_tm; auto.
    eauto using field_write_preserve_typed_sf; auto.
  Qed. Hint Resolve field_write_preserve_typed_ctn.
  
  
  Lemma field_write_preserve_typed_ctns : forall ct h ctns Gamma o F lb F' lb' T T0
                                                cls_def clsT field_defs method_defs ,
      wfe_heap ct h ->
     ctn_list_has_type ct Gamma h ctns (ArrowTy T T0) ->
      Some (Heap_OBJ cls_def F lb) = lookup_heap_obj h o ->
      cls_def = class_def clsT field_defs method_defs ->
      Some cls_def = ct clsT ->
      ctn_list_has_type ct Gamma (update_heap_obj h o (Heap_OBJ cls_def F' lb')) ctns (ArrowTy T T0).
  Proof with eauto.
    intros.
    induction H0; subst; auto.
    apply T_ctn_list with T2 Gamma'; auto.
    eauto using field_write_preserve_typed_ctn; auto.
  Qed. Hint Resolve field_write_preserve_typed_ctns.
  




  Lemma change_obj_label_preserve_typed_hole_tm : forall ct h t Gamma o F lo lo' T
                                               cls_def clsT field_defs method_defs,
      wfe_heap ct h ->
      tm_hole_has_type ct Gamma h t T ->
      Some (Heap_OBJ cls_def F lo) = lookup_heap_obj h o ->
      cls_def = class_def clsT field_defs method_defs ->
      Some cls_def = ct clsT ->
      tm_hole_has_type ct Gamma (update_heap_obj h o (Heap_OBJ cls_def F lo')) t T.
  Proof with eauto.
    intros.
    induction H0; subst; auto.
    apply T_EqCmp1 with e1; auto;
      eauto using field_write_preserve_typed_tm; auto. 
    apply T_EqCmp2 with e2; auto;
      eauto using field_write_preserve_typed_tm; auto. 
    apply T_hole_FieldAccess with cls_def0 (find_fields cls_def0); auto;
      eauto using field_write_preserve_typed_tm; auto.

    eauto using T_hole_MethodCall1.
    eauto using T_hole_MethodCall2.
    
    eauto using T_hole_if.
    eauto using T_hole_FieldWrite1.
    eauto using T_hole_FieldWrite1.

  Qed. Hint Resolve  change_obj_label_preserve_typed_hole_tm.



   Lemma change_obj_label_preserve_typed_fs : forall ct h fs Gamma o F lo lo' T T0
                                                cls_def clsT field_defs method_defs ,
      wfe_heap ct h ->
      fs_has_type ct Gamma h fs (ArrowTy T T0) ->
      Some (Heap_OBJ cls_def F lo) = lookup_heap_obj h o ->
      cls_def = class_def clsT field_defs method_defs ->
      Some cls_def = ct clsT ->
      fs_has_type ct Gamma (update_heap_obj h o (Heap_OBJ cls_def F lo')) fs (ArrowTy T T0).
  Proof with eauto.
    intros. generalize dependent T. generalize dependent T0.
    induction fs; intros; auto.
    inversion H0; auto.
    inversion H0; subst; auto.
    apply T_fs_no_hole with T2; auto.
    eauto using field_write_preserve_typed_tm; auto.     
    apply T_fs_hole with T' T2; auto.
    eauto using field_write_preserve_typed_hole_tm; auto.
  Qed. Hint Resolve change_obj_label_preserve_typed_fs.


  Lemma change_obj_label_preserve_typed_sf : forall ct h sf Gamma o F lo lo'
                                                cls_def clsT field_defs method_defs,
      wfe_heap ct h ->
      well_typed_stack_frame ct Gamma sf h ->
      Some (Heap_OBJ cls_def F lo) = lookup_heap_obj h o ->
      cls_def = class_def clsT field_defs method_defs ->
      Some cls_def = ct clsT ->
      well_typed_stack_frame ct Gamma sf (update_heap_obj h o (Heap_OBJ cls_def F lo')).
  Proof with eauto.
    intros.     
    inversion H0; subst; auto.
    apply well_typed_sf; auto; intros.
    destruct H4 with x T; auto. destruct H5.
    rename x0 into v. 
    exists v; split; auto.    
    apply field_write_preserve_typed_tm with F lo clsT field_defs
                                             method_defs; auto.
  Qed. Hint Resolve change_obj_label_preserve_typed_sf.

  Lemma change_obj_label_preserve_typed_ctn : forall ct h ctn Gamma o F lo lo' T T0
                                                cls_def clsT field_defs method_defs ,
      wfe_heap ct h ->
      ctn_has_type ct Gamma h ctn (ArrowTy T T0) ->
      Some (Heap_OBJ cls_def F lo) = lookup_heap_obj h o ->
      cls_def = class_def clsT field_defs method_defs ->
      Some cls_def = ct clsT ->
      ctn_has_type ct Gamma (update_heap_obj h o (Heap_OBJ cls_def F lo')) ctn (ArrowTy T T0).
  Proof with eauto.
    intros.
    induction H0; subst; auto.
    apply T_ctn_type with T1 T2; auto.
    eauto using field_write_preserve_typed_tm; auto.
    eauto using field_write_preserve_typed_sf; auto.
    eauto using field_write_preserve_typed_fs; auto.
    
    apply T_ctn_caller with T2; auto.
    eauto using field_write_preserve_typed_tm; auto.
    eauto using field_write_preserve_typed_sf; auto.
  Qed. Hint Resolve change_obj_label_preserve_typed_ctn.
  
  
  Lemma change_obj_label_preserve_typed_ctns : forall ct h ctns Gamma o F lo lo' T T0
                                                cls_def clsT field_defs method_defs ,
      wfe_heap ct h ->
     ctn_list_has_type ct Gamma h ctns (ArrowTy T T0) ->
      Some (Heap_OBJ cls_def F lo) = lookup_heap_obj h o ->
      cls_def = class_def clsT field_defs method_defs ->
      Some cls_def = ct clsT ->
      ctn_list_has_type ct Gamma (update_heap_obj h o (Heap_OBJ cls_def F lo')) ctns (ArrowTy T T0).
  Proof with eauto.
    intros.
    induction H0; subst; auto.
    apply T_ctn_list with T2 Gamma'; auto.
    eauto using field_write_preserve_typed_ctn; auto.
  Qed. Hint Resolve change_obj_label_preserve_typed_ctns.




  
  
Theorem typing_preservation : forall T ct
                                   ctn ctns h
                                   ctn' ctns' h',
    config_has_type ct empty_context (Config ct ctn ctns h) T ->
    valid_config (Config ct  ctn ctns h) ->
    Config ct ctn ctns h
           ==> Config ct ctn' ctns' h' ->
    config_has_type ct empty_context (Config ct ctn' ctns' h') T.
Proof with eauto.
  intros T ct ctn ctns h ctn' ctns' h'. 
  intro H_typing.
  intro H_valid_config. 
  remember (empty_context) as Gamma.
  intro H_reduction.
  remember (Config ct ctn ctns h) as config. 
  remember (Config ct ctn' ctns' h') as config'.
  generalize dependent T.   generalize dependent h.
  generalize dependent ctn. 
  generalize dependent ctns. 
  generalize dependent h'.
  generalize dependent ctn'. 
  generalize dependent ctns'.
  induction H_reduction; intros; inversion Heqconfig; inversion Heqconfig'; subst; auto.

- (*Tvar*)
  inversion H_typing; subst;auto.
  +  inversion H3; subst; auto.
     inversion H8; subst; auto.
     inversion H14; subst; auto. 
     assert (tm_has_type ct Gamma' h' v (classTy T3) ).
     destruct H0 with id (classTy T3); auto.
     destruct H1; subst; auto.
     rewrite H1 in H; inversion H; subst; auto.
     eauto using config_has_type.

     
(* (Container e1 (EqCmp hole e2 :: fs) lb sf) *)
-  inversion H_typing; subst; auto.
   apply T_config_ctns with T0 Gamma'; auto.
   inversion H3; subst; auto. 
   inversion H9; subst; auto.
   + inversion H8; subst; auto.
     assert ( tm_hole_has_type ct Gamma' h' (EqCmp hole e2)
                               (ArrowTy (classTy clsT) boolTy)).
     eauto using tm_hole_has_type.          
     apply T_ctn_type with (classTy clsT)
                           (classTy clsT) ; auto.
     destruct fs.          
     ++ apply T_fs_hole with boolTy
                             boolTy; auto.
          intros. split; auto.
          intro contra; inversion contra.          
          assert ( T2 = boolTy); auto; subst; auto.
     ++ case_eq (hole_free t); intro.           
        apply T_fs_hole with boolTy T2; auto.
        intros. inversion H4; subst; auto. try (inconsist).
        apply T_fs_hole with boolTy T2; auto.
        intros. inversion H4; subst; auto.
        destruct H17 with top fs'; auto.
        subst; auto.
     ++ intros. split; auto.
        intro contra; inversion contra. 

   + inversion H8; subst; auto.
     assert ( tm_hole_has_type ct Gamma' h' (EqCmp hole e2)
                               (ArrowTy (classTy clsT)  boolTy)).
     eauto using tm_hole_has_type.          
     apply T_ctn_type with (classTy clsT)
                           (classTy clsT); auto.
     destruct fs.          
     ++ apply T_fs_hole with boolTy
                             boolTy; auto.
        intros. split; auto.
        intro contra; inversion contra.
        assert ( T2 = boolTy); auto; subst; auto.          
     ++ case_eq (hole_free t); intro.           
        apply T_fs_hole with boolTy T2; auto.
        intros. inversion H4; subst; auto. try (inconsist).
        apply T_fs_hole with boolTy T2; auto.
        intros. inversion H4; subst; auto.
        destruct H17 with top fs'; auto.
        subst; auto.
     ++ intros. split; auto.
        intro contra; inversion contra. 


(*(Container (EqCmp v e2)*)
  - inversion H_typing; subst; auto. 
    apply T_config_ctns with T0 Gamma'; auto.
    inversion H3; subst; auto.  
    inversion H15; subst; auto.
    inversion H6.
    inversion H19; subst; auto.
    apply T_ctn_type with boolTy T4; auto.
    destruct H17 with ( EqCmp hole e2) fs; auto.
    subst; auto.
    eauto using tm_has_type.
    intros. destruct H21 with top fs' ; auto.
    subst; auto.
    inversion H_valid_config; subst; auto.
    inversion H28; subst; auto.
    inversion H11; subst; auto.
    inversion H2; subst; auto; try (inconsist_hole_free).

    inversion H.

(* e2 (EqCmp v hole :: fs) *)
-  inversion H_typing; subst; auto.
   apply T_config_ctns with T0 Gamma'; auto.
   inversion H4; subst; auto. 
   inversion H10; subst; auto.
   + inversion H9; subst; auto.
     assert ( tm_hole_has_type ct Gamma' h' (EqCmp v hole)
                               (ArrowTy (classTy clsT) boolTy)).
     eauto using tm_hole_has_type.          
     apply T_ctn_type with (classTy clsT)
                           (classTy clsT) ; auto.
     assert (hole_free (EqCmp v hole) = false).
     unfold hole_free. fold hole_free.
     case_eq (hole_free v); intro Hy; auto.  
     destruct fs.          
     ++ apply T_fs_hole with boolTy
                             boolTy; auto.
        intros; inversion H2.
        split; auto. intro contra; inversion contra. 
        assert ( T2 = boolTy); auto; subst; auto.
     ++ case_eq (hole_free t); intro.           
        apply T_fs_hole with boolTy T2; auto.
        intros. inversion H7; subst; auto. try (inconsist).
        apply T_fs_hole with boolTy T2; auto.
        intros. inversion H7; subst; auto.
        destruct H18 with top fs'; auto.
        subst; auto.
     ++ intros. split; auto.
        intro contra; inversion contra. 

   + inversion H9; subst; auto.
     assert ( tm_hole_has_type ct Gamma' h' (EqCmp v hole)
                               (ArrowTy (classTy clsT) boolTy)).
     eauto using tm_hole_has_type.          
     apply T_ctn_type with (classTy clsT)
                           (classTy clsT); auto.
     assert (hole_free (EqCmp v hole) = false).
     unfold hole_free. fold hole_free.
     case_eq (hole_free v); intro Hy; auto.  
     destruct fs.          
     ++ apply T_fs_hole with boolTy
                             boolTy; auto.
        intros. split; auto.
        intro contra; inversion contra.
        assert ( T2 = boolTy); auto; subst; auto.          
     ++ case_eq (hole_free t); intro.           
        apply T_fs_hole with boolTy T2; auto.
        intros. inversion H7; subst; auto. try (inconsist).
        apply T_fs_hole with boolTy T2; auto.
        intros. inversion H7; subst; auto.
        destruct H18 with top fs'; auto.
        subst; auto. 
     ++ intros. split; auto.
        intro contra; inversion contra. 

    
(*(Container (EqCmp v1 v2)*)
  - inversion H_typing; subst; auto. 
    apply T_config_ctns with T0 Gamma'; auto.
    inversion H4; subst; auto.  
    inversion H16; subst; auto.
    inversion H7.
    apply value_is_hole_free in H.
    rewrite H in H2. inversion H2.
    
    inversion H20; subst; auto.
    inversion H_valid_config; subst; auto.
    inversion H29; subst; auto.
    inversion H12; subst; auto.
    inversion H3; subst; auto; try (inconsist_hole_free).
    apply T_ctn_type with boolTy T4; auto.
    destruct H18 with ( EqCmp v1 hole) fs; auto.
    subst; auto.
    eauto using tm_has_type.    
    intros. destruct H22 with top fs' ; auto.
    split; auto.
    intro contra; inversion contra. 

    inversion H0.
    

- (* (Container result fs lb sf)  *)
  inversion H_typing; subst; auto.
  apply T_config_ctns with T0 Gamma'; auto.
  inversion H6; subst; auto.
  inversion H11; subst; auto.
  apply T_ctn_type with boolTy T2; auto.
  pose proof (exclude_middle_runtime_val v1 v2 H H0).
  destruct H3.
  apply H1 in H3; subst; auto.
  apply H2 in H3; subst; auto.
  

  (* (Container e (FieldAccess hole f :: fs) lb sf) *)
-  inversion H_typing; subst; auto.
   apply T_config_ctns with T0 Gamma'; auto.
   inversion H3; subst; auto. 
   inversion H9; subst; auto.
   + inversion H8; subst; auto.          
     assert (tm_hole_has_type ct Gamma' h' (FieldAccess hole f)
                                   (ArrowTy (classTy clsT) (classTy cls'))).
     eauto using tm_hole_has_type.          
     apply  T_ctn_type with (classTy clsT) (classTy clsT) ; auto.
     destruct fs.          
     ++ apply T_fs_hole with (classTy cls') (classTy cls'); auto.
        intros. split; auto.
          intro contra; inversion contra.
          assert ( T2 = classTy cls'); auto; subst; auto.
     ++ case_eq (hole_free t); intro.           
        apply T_fs_hole with (classTy cls') T2; auto.
        intros. inversion H6; subst; auto. try (inconsist).
        apply T_fs_hole with (classTy cls') T2; auto.
        intros. inversion H6; subst; auto.
        destruct H17 with top fs'; auto.
        subst; auto.
     ++ intros.
        inversion H1; subst; auto.
        split; auto.
        intro contra; inversion contra.

   + inversion H8; subst; auto.          
     assert (tm_hole_has_type ct Gamma' h' (FieldAccess hole f)
                                   (ArrowTy (classTy clsT) (classTy cls'))).
     eauto using tm_hole_has_type.          
     apply  T_ctn_type with (classTy clsT) (classTy clsT) ; auto.
     destruct fs.          
       ++ apply T_fs_hole with (classTy cls') (classTy cls'); auto.
          intros. split; auto.
          intro contra; inversion contra.
          assert ( T2 = classTy cls'); auto; subst; auto.

       ++ case_eq (hole_free t); intro.           
          apply T_fs_hole with (classTy cls') T2; auto.
          intros. inversion H6; subst; auto. try (inconsist).
          apply T_fs_hole with (classTy cls') T2; auto.
          intros. inversion H6; subst; auto.
          destruct H17 with top fs'; auto.
          subst; auto.
       ++ intros.
          inversion H1; subst; auto.
          split; auto.
          intro contra; inversion contra.

          
  (*field access return v to hole *)
  - inversion H_typing; subst; auto. 
    apply T_config_ctns with T0 Gamma'; auto.
    inversion H3; subst; auto.  
    inversion H15; subst; auto.
    inversion H6.
    inversion H19; subst; auto.
    apply T_ctn_type with (classTy cls') T4; auto.
    destruct H17 with (FieldAccess hole f) fs; auto.
    subst; auto.
    eauto using tm_has_type.
    intros. destruct H21 with top fs' ; auto.
    subst; auto.

    inversion H.

  (*(Container v fs (join_label lo lb) sf)*)
  - inversion H_typing; subst; auto.
    inversion H4; subst; auto.
    inversion H9; subst; auto.
    inversion H3; subst; auto. 
    destruct H22 as [F0].
    destruct H1 as [lo0].
    rewrite H1 in H; inversion H; subst; auto.
    rewrite <- H6 in H5; inversion H5; subst; auto.

    apply T_config_ctns with (classTy  cls') Gamma'; auto.
    apply T_ctn_type with  (classTy  cls')
                           (classTy  cls'); auto.

    destruct H20 as [field_defs].
    destruct H2 as [method_defs].
    assert (v = null \/
             (exists
                (o' : oid) (field_defs0 : list field) (method_defs0 : 
                                                       list method_def) 
              (field_cls_def : CLASS) (F' : FieldMap) (lo : Label),
                v = ObjId o' /\
                field_cls_def =
                class_def cls' field_defs0 method_defs0 /\
                lookup_heap_obj h' o'  = Some (Heap_OBJ field_cls_def F' lo) /\
                ct cls' = Some field_cls_def)
           ).

    inversion H_valid_config; subst; auto.
    
    apply field_consist_typing with o
                                    (class_def clsT field_defs method_defs)
                                    F0 fname lo0 clsT field_defs method_defs; auto.

    destruct H12; subst; auto.
    destruct H12 as [o'].
    destruct H2 as [field_defs0]. 
    destruct H2 as [method_defs0].
    destruct H2 as [field_cls_def].
    destruct H2 as [FF].
    destruct H2 as [loF].
    destruct H2.
    destruct H12. destruct H13. subst;auto.
    apply T_ObjId with  (class_def cls' field_defs0 method_defs0); auto.
    exists field_defs0. exists method_defs0. auto. 
    exists FF. exists loF. auto.

    intros. inversion H2.
    try (intro contra; inversion contra).
    try (intro contra; inversion contra).

    apply T_ctn_list with  T0 Gamma'; auto.
    apply T_ctn_caller with 
                          T2; auto.
    intros.
    inversion H2; subst; auto. 
    exists fs. exists lb. exists sf. auto.     

    (* config_has_type ct empty_context
   (Config ct (Container v nil (join_label (join_label lo lb) ell) sf)
      (Container return_hole fs lb sf :: ctns0) h') T *)


  (*(Container v fs (join_label lo lb) sf)*)
  - inversion H_typing; subst; auto.
    inversion H4; subst; auto.
    inversion H9; subst; auto.
    inversion H3; subst; auto.
    inversion H12; subst; auto. 
    destruct H27 as [F0].
    destruct H1 as [lo0].
    rewrite H1 in H; inversion H; subst; auto.
    rewrite <- H14 in H5; inversion H5; subst; auto.

    apply T_config_ctns with (classTy  cls') Gamma'; auto.
    apply T_ctn_type with  (classTy  cls')
                           (classTy  cls'); auto.

    destruct H26 as [field_defs].
    destruct H2 as [method_defs].
    assert (v = null \/
             (exists
                (o' : oid) (field_defs0 : list field) (method_defs0 : 
                                                       list method_def) 
              (field_cls_def : CLASS) (F' : FieldMap) (lo : Label),
                v = ObjId o' /\
                field_cls_def =
                class_def cls' field_defs0 method_defs0 /\
                lookup_heap_obj h' o'  = Some (Heap_OBJ field_cls_def F' lo) /\
                ct cls' = Some field_cls_def)
           ).

    inversion H_valid_config; subst; auto.
    
    apply field_consist_typing with o
                                    (class_def clsT field_defs method_defs)
                                    F0 fname lo0 clsT field_defs method_defs; auto.

    destruct H20; subst; auto.
    destruct H20 as [o'].
    destruct H2 as [field_defs0]. 
    destruct H2 as [method_defs0].
    destruct H2 as [field_cls_def].
    destruct H2 as [FF].
    destruct H2 as [loF].
    destruct H2.
    destruct H20. destruct H22. subst;auto.
    apply T_ObjId with  (class_def cls' field_defs0 method_defs0); auto.
    exists field_defs0. exists method_defs0. auto. 
    exists FF. exists loF. auto.

    intros. inversion H2.
    try (intro contra; inversion contra).
    try (intro contra; inversion contra).

    apply T_ctn_list with  T0 Gamma'; auto.
    apply T_ctn_caller with 
                          T2; auto.
    intros.
    inversion H2; subst; auto. 
    exists fs. exists lb. exists sf. auto.     

    
  (* method call context *)
-  inversion H_typing; subst; auto.
   apply T_config_ctns with T0 Gamma'; auto.
   inversion H3; subst; auto. 
   inversion H9; subst; auto.
   + inversion H8; subst; auto.
     rename id into meth.
     assert ( tm_hole_has_type ct Gamma' h' (MethodCall hole meth e2)
                               (ArrowTy (classTy T0) (classTy returnT))).
     eauto using tm_hole_has_type.
     apply T_ctn_type with (classTy T0)
                           (classTy T0) ; auto.
     destruct fs.          
     ++ apply T_fs_hole with  (classTy returnT)
                             (classTy returnT); auto.
          intros. split; auto.
          intro contra; inversion contra.
          assert ( T2 = (classTy returnT)); auto; subst; auto.

       ++ case_eq (hole_free t); intro.           
          apply T_fs_hole with (classTy returnT) T2; auto.
          intros. inversion H2; subst; auto. try (inconsist).
          apply T_fs_hole with (classTy returnT)  T2; auto.
          intros. inversion H2; subst; auto.
          destruct H17 with top fs'; auto.
          subst; auto.
       ++ intros.
          inversion H1; subst; auto.
          split; auto.
          intro contra; inversion contra.

   + inversion H8; subst; auto.
     rename id into meth.
     assert ( tm_hole_has_type ct Gamma' h' (MethodCall hole meth e2)
                               (ArrowTy (classTy T3)  (classTy returnT))).
     eauto using tm_hole_has_type.          
     apply T_ctn_type with (classTy T3)
                           (classTy T3) ; auto.
     destruct fs.          
     ++ apply T_fs_hole with  (classTy returnT)
                             (classTy returnT); auto.
          intros. split; auto.
          intro contra; inversion contra.
          assert ( T2 = (classTy returnT)); auto; subst; auto.

       ++ case_eq (hole_free t); intro.           
          apply T_fs_hole with (classTy returnT) T2; auto.
          intros. inversion H2; subst; auto. try (inconsist).
          apply T_fs_hole with (classTy returnT)  T2; auto.
          intros. inversion H2; subst; auto.
          destruct H17 with top fs'; auto.
          subst; auto.
       ++ intros.
          inversion H1; subst; auto.
          split; auto.
          intro contra; inversion contra.

          

(*(MethodCall t id0 e2) *)
  - inversion H_typing; subst; auto. 
    apply T_config_ctns with T0 Gamma'; auto.
    inversion H3; subst; auto.  
    inversion H15; subst; auto.
    inversion H6.
    inversion H19; subst; auto.
    apply T_ctn_type with (classTy returnT) T4; auto.
    destruct H17 with ( MethodCall hole id e2) fs; auto.
    subst; auto.
    eauto using tm_has_type.
    intros. destruct H21 with top fs' ; auto.
    subst; auto.
    inversion H_valid_config; subst; auto.
    inversion H27; subst; auto.
    inversion H11; subst; auto.
    inversion H2; subst; auto; try (inconsist_hole_free).

    inversion H_valid_config; subst; auto. inversion H19.     

-  inversion H_typing; subst; auto.
   apply T_config_ctns with T0 Gamma'; auto.
   inversion H5; subst; auto. 
   inversion H10; subst; auto.   
   rename id into meth.
   assert ( tm_hole_has_type ct Gamma' h' (MethodCall v meth hole)
                               (ArrowTy (classTy arguT) (classTy returnT))).
   eauto using tm_hole_has_type.
   apply T_ctn_type with (classTy arguT)
                           (classTy arguT) ; auto.
   destruct fs.          
   + apply T_fs_hole with  (classTy returnT)
                             (classTy returnT); auto.
     intros. unfold hole_free. fold hole_free.
     apply value_is_hole_free in H. rewrite H. auto.
     intros. inversion H3.
     inversion H17; subst; auto.
     assert (T0 = classTy returnT). auto. subst; auto.
   +
     apply T_fs_hole with (classTy returnT) T2; auto.
     intros.  unfold hole_free. fold hole_free.
     apply value_is_hole_free in H. rewrite H. auto.
     intros. inversion H3; subst; auto.
     destruct H19 with top fs'; auto.
     split; auto. subst; auto.
   +  intros. inversion H3; subst; auto.
      split; auto. intro contra; inversion contra.
         
    
 (*(MethodCall v1 id v2) *)   
  - inversion H_typing; subst; auto. 
    apply T_config_ctns with T0 Gamma'; auto.
    inversion H4; subst; auto.  
    inversion H16; subst; auto.
    inversion H7.
    apply value_is_hole_free in H.
    rewrite H in H2. inversion H2. 
    inversion H20; subst; auto.
    inversion H_valid_config; subst; auto.
    inversion H28; subst; auto.
    inversion H12; subst; auto.
    inversion H3; subst; auto; try (inconsist_hole_free).
    
    apply T_ctn_type with  (classTy returnT) T4; auto.
    destruct H18 with ( MethodCall v1 id hole) fs; auto.
    subst; auto.
    eauto using tm_has_type.    
    intros. destruct H22 with top fs' ; auto.
    subst; auto.

    inversion H0. 



(* config_has_type ct empty_context (Config ct (Container body nil lb (sf_update empty_stack_frame arg_id v)) (Container return_hole fs lb sf :: ctns0) h') T *)
     
  - inversion H_typing; subst; auto.  
    inversion H5; subst; auto.
    inversion H10; subst; auto.
    inversion H6; subst; auto. 
    destruct H24 as [F0].
    destruct H2 as [lo0].
    rewrite H2 in H; inversion H; subst; auto.
    rewrite <- H4 in H13; inversion H13; subst; auto.
    rewrite H14 in H0; inversion H0; subst; auto.
    remember ( (update_typing empty_context arg_id0 (classTy arguT))) as gamma0.
    apply T_config_ctns with (classTy returnT0) gamma0; auto.
    apply T_ctn_type with  (classTy returnT0)
                           (classTy returnT0); auto.

    (*well typed stack frame*)
    apply well_typed_sf;auto.
    intros.
    case_eq (beq_id arg_id0 x);intro;
      unfold sf_update. rewrite H15;
    exists v; split; auto.
    subst; auto. unfold update_typing in H3; rewrite H15 in H3.
    inversion H3; subst; auto. 
    apply value_typing_invariant_gamma with Gamma';auto.

    rewrite H15.
    subst; auto. unfold update_typing in H3; rewrite H15 in H3.
    inversion H3. 

    intros. inversion H3.     
    intro contra. inversion contra.
    intro contra. inversion contra.
    apply T_ctn_list with  T0 Gamma'; auto.
    apply T_ctn_caller with 
                          T2; auto.
    intros.
    inversion H3; subst; auto. 
    exists fs. exists lb. exists sf. auto. 

(* config_has_type ct empty_context (Config ct (Container body nil (join_label lb ell) (sf_update empty_stack_frame arg_id v)) (Container return_hole fs lb sf :: ctns0) h') T *)

  - inversion H_typing; subst; auto.  
    inversion H5; subst; auto.
    inversion H10; subst; auto.
    inversion H6; subst; auto.
    inversion H15; subst; auto. 
    destruct H31 as [F0].
    destruct H2 as [lo0].
    rewrite H2 in H; inversion H; subst; auto.
    rewrite <- H22 in H13; inversion H13; subst; auto.
    rewrite H14 in H0; inversion H0; subst; auto.
    remember ( (update_typing empty_context arg_id0 (classTy arguT))) as gamma0.
    apply T_config_ctns with (classTy returnT0) gamma0; auto.
    apply T_ctn_type with  (classTy returnT0)
                           (classTy returnT0); auto.

    (*well typed stack frame*)
    apply well_typed_sf;auto.
    intros.
    case_eq (beq_id arg_id0 x);intro;
      unfold sf_update. rewrite H23;
    exists v; split; auto.
    subst; auto. unfold update_typing in H3; rewrite H23 in H3.
    inversion H3; subst; auto. 
    apply value_typing_invariant_gamma with Gamma';auto.

    rewrite H23.
    subst; auto. unfold update_typing in H3; rewrite H23 in H3.
    inversion H3. 

    intros. inversion H3.     
    intro contra. inversion contra.
    intro contra. inversion contra.
    apply T_ctn_list with  T0 Gamma'; auto.
    apply T_ctn_caller with 
                          T2; auto.
    intros.
    inversion H3; subst; auto. 
    exists fs. exists lb. exists sf. auto.     
    
  
(*new expression*)
- inversion H_typing; subst;auto.
  inversion H3; subst; auto. 
  inversion H7; subst; auto.

  destruct H5 as [cls_def0].
  destruct H0 as [field_defs0].
  destruct H0 as [method_defs0].
  destruct H0.         

  apply T_config_ctns with T0 Gamma'; auto;
    try (intro contra; inversion contra).
  apply T_ctn_type with (classTy cls_name) T2; auto.
  apply T_ObjId with cls_def0; auto.
  exists field_defs0. exists method_defs0. auto.


  pose proof (extend_heap_lookup_new h0
                (Heap_OBJ (class_def cls_name field_defs method_defs)
                          (init_field_map
                             (find_fields (class_def cls_name field_defs method_defs))
                             empty_field_map) lb)).
  rewrite H0 in H. inversion H; subst; auto.
  inversion H5; subst; auto.
  exists ((init_field_map (find_fields (class_def cls_name field_defs method_defs))
               empty_field_map)).
  exists lb; auto.  
   
  apply expand_heap_preserve_typed_sf;auto.
  inversion H_valid_config ; auto. 

  apply expand_heap_preserve_typed_fs ; auto.
  inversion H_valid_config ; auto. 

  apply expand_heap_preserve_typed_ctns; auto. 
  inversion H_valid_config ; auto. 
       
(*(labelData hole lo :: fs0)*)
  -  inversion H_typing; subst; auto.
     apply T_config_ctns with T0 Gamma'; auto.
     inversion H3; subst; auto.
     inversion H8; subst; auto.
     inversion H9; subst; auto.
     + assert (tm_hole_has_type ct Gamma' h' (labelData hole lo)
                                   (ArrowTy T3 (LabelelTy T3))).
       eauto using tm_hole_has_type.          
       apply T_ctn_type with T3 T3 ; auto.
       destruct fs.          
       ++ apply T_fs_hole with (LabelelTy T3) (LabelelTy T3); auto.
          intros. split; auto.
          intro contra; inversion contra.
          assert ( T2 = (LabelelTy T3)); auto; subst; auto.

       ++ case_eq (hole_free t); intro.           
          apply T_fs_hole with (LabelelTy T3) T2; auto.
          intros. inversion H4; subst; auto; try (inconsist).
          apply T_fs_hole with (LabelelTy T3) T2; auto.
          intros. inversion H4; subst; auto;
          destruct H17 with top fs'; auto.
          subst; auto.
      
     + assert (tm_hole_has_type ct Gamma' h' (labelData hole lo)
                                   (ArrowTy T3 (LabelelTy T3))).
       eauto using tm_hole_has_type.          
       apply T_ctn_type with T3 T3 ; auto.
       destruct fs.          
       ++ apply T_fs_hole with (LabelelTy T3) (LabelelTy T3); auto.
          intros. split; auto.
          intro contra; inversion contra.
          assert ( T2 = (LabelelTy T3)); auto; subst; auto.

       ++ case_eq (hole_free t); intro.           
          apply T_fs_hole with (LabelelTy T3) T2; auto.
          intros. inversion H4; subst; auto; try (inconsist).
          apply T_fs_hole with (LabelelTy T3) T2; auto.
          intros. inversion H4; subst; auto;
          destruct H17 with top fs'; auto.
          subst; auto.

  (*label data t lo*)
  - inversion H_typing; subst; auto. 
    apply T_config_ctns with T0 Gamma'; auto.
    inversion H3; subst; auto.  
    inversion H15; subst; auto.
    inversion H6.
    inversion H19; subst; auto.
    apply T_ctn_type with (LabelelTy T2) T4; auto.
    destruct H17 with (labelData hole lo) fs; auto.
    subst; auto.
    eauto using tm_has_type.
    intros. destruct H21 with top fs' ; auto.
    subst; auto.

    inversion H.


- (* v_l v lo *)
  inversion H_typing; subst; auto.
  apply T_config_ctns with T0 Gamma'; auto.
  inversion H4; subst; auto.
  inversion H9; subst; auto.
  apply T_ctn_type with (LabelelTy T3) T2; auto.


        
 (*  (unlabel hole :: fs0)  *)
- inversion H_typing; subst; auto.
  apply T_config_ctns with T0 Gamma'; auto.
  inversion H3; subst; auto.
  inversion H8; subst; auto.
  inversion H9; subst; auto.
  + assert (tm_hole_has_type ct Gamma' h' (unlabel hole) (ArrowTy (LabelelTy T1) T1)).
    eauto using tm_hole_has_type.          
    apply T_ctn_type with (LabelelTy T1) (LabelelTy T1) ; auto.
    destruct fs.          
    ++ apply T_fs_hole with T1 T1; auto.
       assert ( T2 = T1); auto; subst; auto.
    ++ case_eq (hole_free t); intro.           
       apply T_fs_hole with T1 T2; auto.
       intros. inversion H4; subst; auto; try (inconsist).
       apply T_fs_hole with T1 T2; auto.
       intros. inversion H4; subst; auto;
                 destruct H17 with top fs'; auto.
       subst; auto.
    ++ intros. inversion H2; subst; auto.
       split; auto. intro contra; inversion contra. 
  + assert (tm_hole_has_type ct Gamma' h' (unlabel hole) (ArrowTy (LabelelTy T1) T1)).
    eauto using tm_hole_has_type.          
    apply T_ctn_type with (LabelelTy T1) (LabelelTy T1) ; auto.
    destruct fs.          
    ++ apply T_fs_hole with T1 T1; auto.
       assert ( T2 = T1); auto; subst; auto.
    ++ case_eq (hole_free t); intro.           
       apply T_fs_hole with T1 T2; auto.
       intros. inversion H4; subst; auto; try (inconsist).
       apply T_fs_hole with T1 T2; auto.
       intros. inversion H4; subst; auto;
                 destruct H17 with top fs'; auto.
       subst; auto.
    ++ intros. inversion H2; subst; auto.
       split; auto. intro contra; inversion contra. 


  

(*  (unlabel t)  *)

- inversion H_typing; subst; auto. 
  apply T_config_ctns with T0 Gamma'; auto.
  inversion H3; subst; auto.  
  inversion H15; subst; auto.
  inversion H6.
  inversion H19; subst; auto.
  apply T_ctn_type with T' T4; auto.
  destruct H17 with (unlabel hole) fs; auto.
  subst; auto.
  intros. destruct H21 with top fs' ; auto.

  inversion H. 

- (*   (join_label lb0 lo)   *)
  inversion H_typing; subst; auto.
  apply T_config_ctns with T0 Gamma'; auto.
  inversion H3; subst; auto.
  inversion H8; subst; auto.
  inversion H1; subst; auto.
  apply T_ctn_type with T1 T2; auto.
  

    
(* (labelOf hole :: fs0) *)
- inversion H_typing; subst; auto.
  apply T_config_ctns with T0 Gamma'; auto.
  inversion H3; subst; auto.
  inversion H8; subst; auto.
  inversion H1; subst; auto. 
  inversion H9; subst; auto.
  + assert (tm_hole_has_type ct Gamma' h' (labelOf hole) (ArrowTy (LabelelTy T1) LabelTy)).
    eauto using tm_hole_has_type.
    eauto using T_ctn_type.

  
    (*
    apply T_ctn_type with (LabelelTy) (LabelelTy); auto.
    destruct fs.          
    ++ apply T_fs_hole with LabelTy LabelTy; auto.
       intros. inversion H2. 
       assert ( T2 =  LabelTy); auto; subst; auto.
    ++ case_eq (hole_free t); intro.           
       apply T_fs_hole with LabelTy T2; auto.
       intros. inversion H4; subst; auto; try (inconsist).
       apply T_fs_hole with LabelTy T2; auto.
       intros. inversion H4; subst; auto;
                 destruct H17 with top fs'; auto.
       subst; auto.
    ++ intros. inversion H2; subst; auto.
       split; auto. intro contra; inversion contra. *)
  + assert (tm_hole_has_type ct Gamma' h' (labelOf hole) (ArrowTy (LabelelTy T1) LabelTy)).
    eauto using tm_hole_has_type.
    eauto using T_ctn_type.

(* (labelOf t) *)
- inversion H_typing; subst; auto. 
  apply T_config_ctns with T0 Gamma'; auto.
  inversion H3; subst; auto.  
  inversion H15; subst; auto.  
  inversion H8; subst; auto. 
  apply T_ctn_type with (LabelelTy T2) (LabelelTy T2); auto.
  eauto using T_fs_hole.
  intros. split; auto. intro contra; inversion contra. 

  inversion H8;subst; auto. 
  apply T_ctn_type with (LabelelTy T3) (LabelelTy T3); auto.
  apply T_fs_hole with (LabelTy) T2; auto.
  intros. split; auto. inversion H0; subst; auto.
  destruct H17 with top0 fs'; auto.
  inversion H0; subst; auto.
  destruct H17 with top0 fs'; subst;  auto.

  intros.  split; auto. 
  intro contra; inversion contra. 

  inversion H8; subst; auto. 
  apply T_ctn_type with (LabelelTy T3) (LabelelTy T3); auto.
  apply T_fs_hole with (LabelTy) T2; auto.
  intros. split; auto. inversion H0; subst; auto.
  destruct H17 with top0 fs'; auto.
  inversion H0; subst; auto.
  destruct H17 with top0 fs'; subst;  auto.

  intros.  split; auto. 
  intro contra; inversion contra. 

- (* l lo *)
  inversion H_typing; subst; auto.
  apply T_config_ctns with T0 Gamma'; auto.
  inversion H3; subst; auto.
  inversion H15; subst; auto.

  + inversion H6; subst; auto.

  + inversion H19; subst; auto.
    destruct H17 with (labelOf hole) fs; auto. subst; auto. 
    apply T_ctn_type with LabelTy T4; auto.
    eauto using T_labelOf.
    intros; subst; auto. split; auto.
    intro contra; inversion contra. destruct H21 with top fs'; auto.

  +
    destruct H17 with (labelOf hole) fs; auto. subst; auto.
    intuition. 


- (* l lo *)
  inversion H_typing; subst; auto.
  apply T_config_ctns with T0 Gamma'; auto.
  inversion H3; subst; auto.
  inversion H8; subst; auto.
  inversion H1; subst; auto.
  apply T_ctn_type with LabelTy T2; auto.
  
(*(Config ct (Container (labelOf v) fs (join_label lb ell) sf) ctns' h') T*)
- inversion H_typing; subst; auto.
  apply T_config_ctns with T0 Gamma'; auto.
  inversion H3; subst; auto.
  inversion H8; subst; auto.
  inversion H1; subst; auto.
  apply T_ctn_type with LabelTy T2; auto.
  eauto using  T_labelOf.
  
(* (Config ct (Container e (raiseLabel hole lo :: fs) lb sf) ctns' h') *)
  -  inversion H_typing; subst; auto.
     apply T_config_ctns with T0 Gamma'; auto.
     inversion H3; subst; auto.
     inversion H8; subst; auto.
     inversion H9; subst; auto. 
     + assert (tm_hole_has_type ct Gamma' h' (raiseLabel hole lo)
                                   (ArrowTy (classTy clsT)  voidTy)).
       eauto using tm_hole_has_type.          
       apply T_ctn_type with (classTy clsT)  (classTy clsT) ; auto.
       destruct fs.          
       ++ apply T_fs_hole with voidTy voidTy; auto.
          intros. split; auto.
          intro contra; inversion contra. inversion H1.
          inversion H15; subst; auto.
          destruct H16; auto. 

       ++ case_eq (hole_free t); intro.
          +++ apply T_fs_hole with voidTy T2  ; auto.
              intros. inversion H4; subst; auto; try (inconsist).
          +++ apply T_fs_hole with voidTy T2 ; auto.
          intros. inversion H4; subst; auto;
                    destruct H17 with top fs'; auto.
       ++ intros. inversion H1; subst; auto. split; auto.
          intro contra; inversion contra. 
      
     + assert (tm_hole_has_type ct Gamma' h' (raiseLabel hole lo)
                                   (ArrowTy (classTy clsT) voidTy)).
       eauto using tm_hole_has_type.          
       apply T_ctn_type with (classTy clsT)  (classTy clsT) ; auto.
       destruct fs.          
       ++ apply T_fs_hole with voidTy T2; auto.
          intros. inversion H1. 
       ++ case_eq (hole_free t); intro.           
          apply T_fs_hole with voidTy T2; auto.
          intros. inversion H4; subst; auto; try (inconsist).
          apply T_fs_hole with voidTy T2; auto.
          intros. inversion H4; subst; auto;
                    destruct H17 with top fs'; auto.
       ++ intros. split; auto. intro contra; inversion contra. 
         
  (* (Container (raiseLabel v lo) fs lb sf)*)
  - inversion H_typing; subst; auto. 
    apply T_config_ctns with T0 Gamma'; auto.
    inversion H3; subst; auto.  
    inversion H15; subst; auto.
    inversion H6.
    inversion H19; subst; auto.
    apply T_ctn_type with voidTy T4; auto.
    destruct H17 with (raiseLabel hole lo) fs; auto.
    subst; auto.
    eauto using tm_has_type.
    intros.
    destruct H21 with top fs' ; auto.
    subst; auto.

    inversion H.

  (* (Config ct (Container (raiseLabel v lo) fs (join_label lb ell) sf) *)
  - inversion H_typing; subst; auto. 
    apply T_config_ctns with T0 Gamma'; auto.
    inversion H3; subst; auto.
    inversion H8; subst; auto.
    inversion H12; subst; auto.
    inversion H15; subst; auto.
    + apply T_ctn_type with voidTy T0; auto.
      eauto using T_raiseLabel; auto.

    + apply T_ctn_type with voidTy T2; auto.
      eauto using T_raiseLabel; auto.
    + destruct H17 with top fs0; auto. intuition. 
    

-  (*(Container (raiseLabel (ObjId o) lo') fs lb sf)*)
  inversion H_typing; subst; auto.
  apply T_config_ctns with T0 Gamma'; auto.
  inversion H5; subst; auto.
  inversion H10; subst; auto.
  apply T_ctn_type with voidTy T2; auto.
  apply well_typed_sf; auto.
  intros.
  inversion H16; subst; auto.
  apply H3 in H2; auto. destruct H2 as [v]. destruct H2.
  exists v. split; auto.
  apply heap_preserve_typing with h0; auto.
  intros.
  case_eq (beq_oid o0 o); intro.
  apply beq_oid_equal in H13; subst; auto.
  assert (Some (Heap_OBJ cls F lo') =
          lookup_heap_obj (update_heap_obj h0 o (Heap_OBJ cls F lo')) o).
  apply lookup_updated with h0 ((Heap_OBJ cls F lo)); auto.
  exists F. exists lo'.
  rewrite H7 in H; inversion H; subst; auto. 

  assert (Some  (Heap_OBJ cls_def F0 lo0) =
          lookup_heap_obj (update_heap_obj h0 o (Heap_OBJ cls F lo')) o0).
  apply lookup_updated_not_affected with o (Heap_OBJ cls F lo') h0; auto.
  intro contra; subst; auto.
  assert (beq_oid o o = true).
  apply beq_oid_same. try(inconsist).
  exists F0. exists lo0.  auto. 

  
  destruct H21 as [cls_def].
  destruct H2 as [field_defs].
  destruct H2 as [method_defs].
  destruct H2.
  inversion H14; subst; auto.
  destruct H24 as [F0].
  destruct H3 as [lo0].
  rewrite H3 in H; inversion H; subst; auto. 
  apply change_obj_label_preserve_typed_fs with lo0 clsT field_defs
                                                method_defs; auto.
  inversion H_valid_config; subst; auto. 
  

  rewrite <- H13 in H2. inversion H2; auto. 

  inversion H5; subst; auto.
  inversion H10; subst; auto.
  destruct H21 as [cls_def].
  destruct H2 as [field_defs].
  destruct H2 as [method_defs].
  destruct H2.
  inversion H14; subst; auto.
  destruct H24 as [F0].
  destruct H3 as [lo0].
  rewrite H3 in H; inversion H; subst; auto. 
  apply change_obj_label_preserve_typed_ctns with lo0 clsT field_defs
                                                  method_defs; auto.
  inversion H_valid_config; subst; auto. 
  rewrite <- H13 in H2. inversion H2; auto.   


-  (*(Container (raiseLabel (v_opa_l (ObjId o) ell) lo') fs lb sf)*)
  inversion H_typing; subst; auto.
  apply T_config_ctns with T0 Gamma'; auto.
  inversion H5; subst; auto.
  inversion H10; subst; auto.
  inversion H14; subst; auto.
  inversion H7; subst; auto.
  apply T_ctn_type with voidTy T2; auto.
  apply well_typed_sf; auto.
  intros.
  inversion H16; subst; auto.
  apply H3 in H2; auto. destruct H2 as [v]. destruct H2.
  exists v. split; auto.
  apply heap_preserve_typing with h0; auto.
  intros.
  case_eq (beq_oid o0 o); intro.
  apply beq_oid_equal in H25; subst; auto.
  assert (Some (Heap_OBJ cls F lo') =
          lookup_heap_obj (update_heap_obj h0 o (Heap_OBJ cls F lo')) o).
  apply lookup_updated with h0 ((Heap_OBJ cls F lo)); auto.
  exists F. exists lo'. auto. 
  rewrite H23 in H; inversion H; subst; auto. 

  assert (Some  (Heap_OBJ cls_def0 F0 lo0) =
          lookup_heap_obj (update_heap_obj h0 o (Heap_OBJ cls F lo')) o0).
  apply lookup_updated_not_affected with o (Heap_OBJ cls F lo') h0; auto.
  intro contra; subst; auto.
  assert (beq_oid o o = true).
  apply beq_oid_same. try(inconsist).


  exists F0. exists lo0. auto. 
  
  destruct H21 as [cls_def0].
  destruct H2 as [field_defs].
  destruct H2 as [method_defs].
  destruct H2.
  destruct H28 as [F0].
  destruct H21 as [lo0].
  rewrite H21 in H; inversion H; subst; auto. 
  apply change_obj_label_preserve_typed_fs with lo0 clsT field_defs
                                                method_defs; auto.
  inversion H_valid_config; subst; auto. 
  

  rewrite <- H15 in H2. inversion H2; auto. 

  inversion H5; subst; auto.
  inversion H10; subst; auto.
  destruct H21 as [cls_def].
  destruct H2 as [field_defs].
  destruct H2 as [method_defs].
  destruct H2.
  inversion H14; subst; auto.
  inversion H15; subst; auto. 
  destruct H28 as [F0].
  destruct H3 as [lo0].
  rewrite H3 in H; inversion H; subst; auto. 
  apply change_obj_label_preserve_typed_ctns with lo0 clsT field_defs
                                                  method_defs; auto.
  inversion H_valid_config; subst; auto. 
  rewrite <- H7 in H2. inversion H2; auto.  
  
(*(Assignment id0 hole :: fs0)  *)
- inversion H_typing; subst; auto.
  apply T_config_ctns with T0 Gamma'; auto.
  inversion H3; subst; auto.
  inversion H8; subst; auto.
  inversion H9; subst; auto.
  + assert (tm_hole_has_type ct Gamma' h' (Assignment id hole) (ArrowTy T3 voidTy)).
    eauto using tm_hole_has_type.          
    apply T_ctn_type with T3 T3; auto.
    destruct fs.          
    ++ apply T_fs_hole with voidTy voidTy; auto.
       intros. inversion H1. 
       assert ( T2 = voidTy); auto; subst; auto.
    ++ case_eq (hole_free t); intro.           
       apply T_fs_hole with voidTy T2; auto.
       intros. inversion H4; subst; auto; try (inconsist).
       apply T_fs_hole with voidTy T2; auto.
       intros. inversion H4; subst; auto;
                 destruct H17 with top fs'; auto.
  + assert (tm_hole_has_type ct Gamma' h' (Assignment id hole) (ArrowTy T3 voidTy)).
    eauto using tm_hole_has_type.          
    apply T_ctn_type with T3 T3; auto.
    destruct fs.          
    ++ apply T_fs_hole with voidTy voidTy; auto.
       intros. inversion H1. 
       assert ( T2 = voidTy); auto; subst; auto.
    ++ case_eq (hole_free t); intro.           
       apply T_fs_hole with voidTy T2; auto.
       intros. inversion H4; subst; auto; try (inconsist).
       apply T_fs_hole with voidTy T2; auto.
       intros. inversion H4; subst; auto;
                 destruct H17 with top fs'; auto.
       

(*(Assignment id0 t)*)
- inversion H_typing; subst; auto. 
  apply T_config_ctns with T0 Gamma'; auto.
  inversion H3; subst; auto.  
  inversion H15; subst; auto.
  inversion H6.
  inversion H19; subst; auto.
  apply T_ctn_type with voidTy T4; auto.
  destruct H17 with (Assignment id hole) fs; auto.
  subst; auto.
  eauto using tm_has_type. 
  intros. destruct H21 with top fs' ; auto.

  inversion H.
  
- (* Skip*)
  inversion H_typing; subst; auto.
  apply T_config_ctns with T0 Gamma'; auto.
  inversion H3; subst; auto.
  inversion H8; subst; auto.
  apply T_ctn_type with voidTy T2; auto.
  apply well_typed_sf; auto; intros.
  case_eq (beq_id id x);intro.
  unfold sf_update. rewrite H1.
  exists v; split; auto.
  apply beq_equal in H1.  subst; auto.
  rewrite H0 in H2; inversion H2; subst; auto.
  unfold sf_update. rewrite H1.
  inversion H14; subst; auto.


(* (FieldWrite hole f e2 :: fs0)*)
-  inversion H_typing; subst; auto.
   apply T_config_ctns with T0 Gamma'; auto.
   inversion H3; subst; auto. 
   inversion H9; subst; auto.
   + inversion H8; subst; auto.
     assert ( tm_hole_has_type ct Gamma' h' (FieldWrite hole f e2)
                               (ArrowTy (classTy clsT) voidTy)).
     eauto using tm_hole_has_type.          
     apply T_ctn_type with (classTy clsT)
                           (classTy clsT) ; auto.
     destruct fs.          
     ++ apply T_fs_hole with voidTy
                             voidTy; auto.
          intros. split; auto.
          intro contra; inversion contra.
          inversion H1. 
          assert ( T2 = voidTy); auto; subst; auto.          
     ++ case_eq (hole_free t); intro.           
        apply T_fs_hole with voidTy T2; auto.
        intros. inversion H2; subst; auto. try (inconsist).
        apply T_fs_hole with voidTy T2; auto.
        intros. inversion H2; subst; auto.
        destruct H17 with top fs'; auto.
     ++ intros.
        inversion H1; subst; auto.
        split; auto.          intro contra; inversion contra.

   + inversion H8; subst; auto.
     assert ( tm_hole_has_type ct Gamma' h' (FieldWrite hole f e2)
                               (ArrowTy (classTy clsT) voidTy)).
     eauto using tm_hole_has_type.          
     apply T_ctn_type with (classTy clsT)
                           (classTy clsT) ; auto.
     destruct fs.          
     ++ apply T_fs_hole with voidTy
                             voidTy; auto.
          intros. split; auto.
          intro contra; inversion contra.
          inversion H1. 
          assert ( T2 = voidTy); auto; subst; auto.          
     ++ case_eq (hole_free t); intro.           
        apply T_fs_hole with voidTy T2; auto.
        intros. inversion H2; subst; auto. try (inconsist).
        apply T_fs_hole with voidTy T2; auto.
        intros. inversion H2; subst; auto.
        destruct H17 with top fs'; auto.
     ++ intros.
        inversion H1; subst; auto.
        split; auto.
        intro contra; inversion contra.


(*FieldWrite v f e2)*)
  - inversion H_typing; subst; auto. 
    apply T_config_ctns with T0 Gamma'; auto.
    inversion H3; subst; auto.  
    inversion H15; subst; auto.
    inversion H6.
    inversion H19; subst; auto.
    apply T_ctn_type with voidTy T4; auto.
    destruct H17 with ( FieldWrite hole f e2) fs; auto.
    subst; auto.
    eauto using tm_has_type.
    intros. destruct H21 with top fs' ; auto.
    subst; auto.
    inversion H_valid_config; subst; auto.
    inversion H27; subst; auto.
    inversion H11; subst; auto.
    inversion H2; subst; auto; try (inconsist_hole_free).
      
    inversion H.


(* (Container e2 (FieldWrite v f hole :: fs) lb sf) *)
-  inversion H_typing; subst; auto.
   apply T_config_ctns with T0 Gamma'; auto.
   inversion H5; subst; auto. 
   inversion H11; subst; auto.
   + inversion H10; subst; auto.
     assert ( tm_hole_has_type ct Gamma' h' (FieldWrite v f hole)
                               (ArrowTy (classTy cls') voidTy)).
     eauto using tm_hole_has_type.          
     apply T_ctn_type with (classTy cls')
                           (classTy cls') ; auto.
     destruct fs.          
     ++ apply T_fs_hole with voidTy
                             voidTy; auto.
        unfold hole_free. fold hole_free.
        apply value_is_hole_free in H. rewrite H.  auto. 
        intros. inversion H3.  
        inversion H16; subst; auto.
        destruct H18; auto. 
     ++ case_eq (hole_free t); intro.           
        apply T_fs_hole with voidTy T2; auto.
        unfold hole_free. fold hole_free.
        apply value_is_hole_free in H. rewrite H.  auto.
        intros. inversion H4; subst; auto. try (inconsist).
        destruct H19 with t fs; auto.
        subst; auto.
        apply T_fs_hole with voidTy
                             voidTy; auto.
        unfold hole_free. fold hole_free.
        apply value_is_hole_free in H. rewrite H.  auto.
     ++ intros.
        split; auto. 
        intro contra; inversion contra.

   + inversion H10; subst; auto.
     assert ( tm_hole_has_type ct Gamma' h' (FieldWrite v f hole)
                               (ArrowTy (classTy cls') voidTy)).
     eauto using tm_hole_has_type.          
     apply T_ctn_type with (classTy cls')
                           (classTy cls') ; auto.
     destruct fs.          
     ++ apply T_fs_hole with voidTy
                             voidTy; auto.
        unfold hole_free. fold hole_free.
        apply value_is_hole_free in H. rewrite H.  auto. 
        intros. inversion H3.  
        inversion H16; subst; auto.
        destruct H18; auto. 
     ++ case_eq (hole_free t); intro.           
        apply T_fs_hole with voidTy T2; auto.
        unfold hole_free. fold hole_free.
        apply value_is_hole_free in H. rewrite H.  auto.
        intros. inversion H4; subst; auto. try (inconsist).
        destruct H19 with t fs; auto.
        subst; auto.
        apply T_fs_hole with voidTy
                             voidTy; auto.
        unfold hole_free. fold hole_free.
        apply value_is_hole_free in H. rewrite H.  auto.
     ++ intros.
        split; auto. 
        intro contra; inversion contra.

        
(*(Container (FieldWrite v1 f v2)*)
  - inversion H_typing; subst; auto. 
    apply T_config_ctns with T0 Gamma'; auto.
    inversion H4; subst; auto.  
    inversion H16; subst; auto.
    inversion H7.
    apply value_is_hole_free in H0.
    rewrite H0 in H2. inversion H2. 
    inversion H20; subst; auto.
    inversion H_valid_config; subst; auto.
    inversion H28; subst; auto.
    inversion H12; subst; auto.
    inversion H3; subst; auto; try (inconsist_hole_free).
    apply T_ctn_type with voidTy T4; auto.
    destruct H18 with ( FieldWrite v1 f hole) fs; auto.
    subst; auto.
    eauto using tm_has_type.    
    intros. destruct H22 with top fs' ; auto.
    inversion H.
              
        
(* field write normal*)
  -
    inversion H_typing; subst; auto.
    inversion H5; subst; auto.
    inversion H10; subst; auto.
    inversion H6; subst; auto.
    destruct H24 as [F0].
    destruct H0 as [lo0].
    destruct H21 as [field_defs0].
    destruct H2 as [method_defs0].
    rewrite H0 in H; inversion H; subst; auto.
    inversion H_valid_config; subst; auto.

    apply T_config_ctns with T0 Gamma'; auto.   
    apply T_ctn_type with voidTy T2; auto.
    apply field_write_preserve_typed_sf with F0 lo0 clsT field_defs0
                                             method_defs0; auto.
    eauto using field_write_preserve_typed_fs.
    eauto using field_write_preserve_typed_ctns. 

(* field write opaque *)
  -
    inversion H_typing; subst; auto.
    inversion H5; subst; auto.
    inversion H9; subst; auto.
    inversion H6; subst; auto.
    inversion H7; subst; auto. 
    destruct H29 as [F0].
    destruct H0 as [lo0].
    destruct H28 as [field_defs0].
    destruct H1 as [method_defs0].
    rewrite H0 in H; inversion H; subst; auto.
    inversion H_valid_config; subst; auto.

    apply T_config_ctns with T0 Gamma'; auto.   
    apply T_ctn_type with voidTy T2; auto.
    apply field_write_preserve_typed_sf with F0 lo0 clsT field_defs0
                                             method_defs0; auto.
    eauto using field_write_preserve_typed_fs.
    eauto using field_write_preserve_typed_ctns. 
    

(* if with hole*)
- inversion H_typing; subst; auto.
  apply T_config_ctns with T0 Gamma'; auto.
  inversion H3; subst; auto.
  inversion H8; subst; auto.
  inversion H9; subst; auto.
  + assert (tm_hole_has_type ct Gamma' h' (If hole s1 s2 )  (ArrowTy boolTy T1)).
    eauto using tm_hole_has_type.          
    apply T_ctn_type with boolTy boolTy; auto.
    destruct fs.          
    ++ apply T_fs_hole with T1 T1; auto.
       intros. inversion H1. 
       assert ( T2 = T1); auto; subst; auto.
    ++ case_eq (hole_free t); intro.           
       apply T_fs_hole with T1 T2; auto.
       intros. inversion H2; subst; auto; try (inconsist).
       apply T_fs_hole with T1 T2; auto.
       intros. inversion H2; subst; auto;
                 destruct H17 with top fs'; auto.
       split; subst; auto.
    ++ intros.
       inversion H1; subst; auto.
       split; auto. intro contra; inversion contra .
  + assert (tm_hole_has_type ct Gamma' h' (If hole s1 s2 )  (ArrowTy boolTy T1)).
    eauto using tm_hole_has_type.          
    apply T_ctn_type with boolTy boolTy; auto.
    destruct fs.          
    ++ apply T_fs_hole with T1 T1; auto.
       intros. inversion H1. 
       assert ( T2 = T1); auto; subst; auto.
    ++ case_eq (hole_free t); intro.           
       apply T_fs_hole with T1 T2; auto.
       intros. inversion H2; subst; auto; try (inconsist).
       apply T_fs_hole with T1 T2; auto.
       intros. inversion H2; subst; auto;
                 destruct H17 with top fs'; auto.
       split; subst; auto.
    ++ intros.
       inversion H1; subst; auto.
       split; auto. intro contra; inversion contra .


(* if guard s1 s2*)
- inversion H_typing; subst; auto. 
  apply T_config_ctns with T0 Gamma'; auto.
  inversion H3; subst; auto.  
  inversion H15; subst; auto.
  inversion H6.
  inversion H19; subst; auto.
  apply T_ctn_type with T' T4; auto.
  apply  T_if ; auto.
  
  
  destruct H17 with (If hole s1 s2) fs; auto.
  subst; auto.
  intros. destruct H21 with top fs' ; auto.
  subst; auto.

  inversion H.

(* (Container (If guard s1 s2) fs (join_label lb ell) sf) *)
- inversion H_typing; subst; auto. 
  apply T_config_ctns with T0 Gamma'; auto.
  inversion H3; subst; auto.  
  inversion H8; subst; auto.
  inversion H12; subst; auto. 
  apply T_ctn_type with T1 T2; auto.

  
- (*   B_true   *)
  inversion H_typing; subst; auto.
  apply T_config_ctns with T0 Gamma'; auto.
  inversion H2; subst; auto.  
  inversion H7; subst; auto.
  apply T_ctn_type with T1 T2; auto.

- (*   B_false   *)
  inversion H_typing; subst; auto.
  apply T_config_ctns with T0 Gamma'; auto.
  inversion H2; subst; auto.  
  inversion H7; subst; auto.
  apply T_ctn_type with T1 T2; auto.

(*sequence *)       
- inversion H_typing; subst; auto. 
  apply T_config_ctns with T0 Gamma'; auto.
  inversion H2; subst; auto.  
  inversion H7; subst; auto.

  inversion H_valid_config; subst;  auto.
  inversion H20; subst; auto.
  inversion H19; subst; auto. 
  
  apply T_ctn_type with T3 T1; auto.
  apply T_fs_no_hole with T2; auto.
  intros. destruct H16 with top fs'; auto.
  subst; auto.

  intro. inversion H.

  intros. inversion H; subst; auto.
  apply surface_syntax_is_hole_free in H3.
  try (inconsist).

         
- (*(Container t' fs' lb' sf')*)
  inversion H_typing; subst; auto.
  apply T_config_ctns with T0 Gamma'; auto.
  inversion H2; subst; auto.  
  inversion H7; subst; auto.
  inversion H14; subst; auto. 
  apply T_ctn_type with T2 T3; auto.
  intros.
  destruct H20 with top fs'; auto.
  subst; auto.
  destruct H16 with e fs; auto.
  intuition. 


- (*\(Container e fs lb sf)*)
  inversion H_typing; subst; auto.
  apply T_config_ctns with T0 Gamma'; auto.
  inversion H4; subst; auto.  
  inversion H16; subst; auto.
  + apply T_ctn_type with T2 T4; auto.
    intros.
    destruct H22 with top fs'; auto.
    subst; auto. 
  + try (inconsist).
  + inversion H.

(* config_has_type ct empty_context (Config ct (Container (v_opa_l v lb) fs' lb' sf') ctns' h') T *)
  - inversion H_typing; subst; auto.
    inversion H5; subst; auto.
    + inversion H11; subst; auto.
      inversion H14; subst; auto.
      inversion H24.      
      apply T_config_ctns with  T4  Gamma'0; auto.
      apply T_ctn_type with  T1 T5; auto.
      apply T_v_opa_l; auto. 
      apply value_typing_invariant_gamma with Gamma';auto.
      
      intros. intro contra.
      rewrite contra in H; inversion H; subst; auto.
      destruct H1 with v0 lb0; auto. 
      
      inversion H17; subst; auto.
      assert (T0 = T1); auto.
      subst; auto.
      intros; subst; auto.
      inversion H17; subst; auto.
      assert (T0 = T1); auto; subst; auto.

      intros.
      destruct H26 with top fs'0; auto.
      subst; auto.
      inversion H17; subst; auto.
      assert (T0 = T1); auto; subst; auto.

      intros.
      inversion H21; subst; auto.
      inversion H8.
      inversion H15; subst; auto.
      inversion H22; subst; auto.
      intuition.
      exists fs. exists lb0. exists sf0. auto.

    + inversion H.
    
(* config_has_type ct empty_context (Config ct (Container (v_opa_l v lb) fs' lb' sf') ctns' h') T *)
  - inversion H_typing; subst; auto.
    inversion H2; subst; auto.
    inversion H7; subst; auto.
    inversion H8; subst; auto.
    inversion H21; subst; auto.
    +
      inversion H26.
    
    +
      apply T_config_ctns with  T4  Gamma'0; auto.
      apply T_ctn_type with  T1 T5; auto.
      apply T_v_opa_l; auto. 
      apply value_typing_invariant_gamma with Gamma';auto.
      inversion H14; subst; auto.
      assert (T0 = T1); auto.
      subst; auto.
      intros; subst; auto.
      inversion H14; subst; auto. 
      assert (T0 = T1); auto.
      subst; auto.

      destruct H28 with top fs'0; auto.
      intros; subst; auto.
      inversion H23; subst; auto.
      inversion H22; subst; auto.
      intuition.
      exists fs. exists lb0. exists sf0. auto.
      
(*v_opa_l t lb0*)
  - inversion H_typing; subst; auto.
    inversion H2; subst; auto.
    inversion H8; subst; auto.
    inversion H11; subst; auto.
    intuition.     
    apply T_config_ctns with  T4  Gamma'0; auto.
    apply T_ctn_type with  T1 T5; auto.
    
    assert (T2 = T1); auto.
    inversion H14; subst; auto.
    intros; subst; auto.
    assert (T2 = T1); auto.    
    inversion H14; subst; auto.
    destruct H23 with top fs'0; auto. 

    intros; subst; auto.
    inversion H18; subst; auto.
    inversion H12; subst; auto.
    intuition.
    exists fs. exists lb0. exists sf0. auto.
Qed. 
Hint Resolve typing_preservation. 











    





  