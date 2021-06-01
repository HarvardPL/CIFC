Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Require Import Language.
Require Import Lemmas.
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
      destruct H0 as [ll].
      subst; auto. 
      apply stack_val_object with cls_name F0 lo0 field_defs method_defs ll; auto.

      intros.
      inversion H; subst; auto.
      apply stack_val_labeled; auto.
      apply IHvalue with T0; auto.

      intros.
      inversion H0; subst; auto.
      apply stack_val_opa_labeled; auto.
      inversion H1; subst; auto.
      inversion H5; subst; auto.
      destruct H6 as [field_defs].
      destruct H2 as [method_defs].
      destruct H12 as [F].
      destruct H6 as [lo].
      destruct H6 as [ll].
      eauto using stack_val_object.

      inversion H1; subst; auto.
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
                                   field_defs  method_defs ll; auto.
       apply extend_heap_lookup_eq; auto.
       apply lookup_extend_heap_fresh_oid with ct (Heap_OBJ (class_def cls_name field_defs method_defs) F lo ll); auto.
Qed. Hint Resolve expand_heap_preserve_wfe_stack_val.
     

Lemma expand_heap_preserve_valid_ctn : forall ctn ho h ct,
         wfe_heap ct h ->
         valid_ctn ct ctn h ->
         valid_ctn ct ctn (add_heap_obj h (get_fresh_oid h) ho).
Proof with eauto.
       intros.
       inversion H0; subst; auto.
       apply valid_container; auto.
       inversion H4; subst; auto.
       apply stack_frame_wfe; auto.
       intros. destruct H5 with x v;auto.
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


Lemma update_heap_preserve_wfe_stack_val : forall o v h ct F f cls lo v0 ll,
         value v0 -> wfe_heap ct h ->
         wfe_stack_val ct h v0 ->
         Some (Heap_OBJ cls F lo ll) = lookup_heap_obj h o ->
         wfe_stack_val ct (update_heap_obj h o (Heap_OBJ cls (fields_update F f v) lo ll)) v0.
Proof with eauto.
       intros.
       induction H; inversion H1; subst; auto.
       case_eq (beq_oid o0 o); intro.
       apply beq_oid_equal in H. subst; auto. 
       assert (Some (Heap_OBJ cls (fields_update F f v) lo ll) =
                     lookup_heap_obj
                       (update_heap_obj h o (Heap_OBJ cls (fields_update F f v) lo ll)) o).
       apply lookup_updated with h (Heap_OBJ cls F lo ll); auto.       
       apply stack_val_object with cls_name (fields_update F f v) lo
                                   field_defs  method_defs ll; auto.
       rewrite <- H2 in H3; inversion H3; subst; auto.
       inversion H1; subst; auto.
       assert (Some (Heap_OBJ (class_def cls_name0 field_defs0 method_defs0) F1 lo1 ll1) =
                     lookup_heap_obj
                       (update_heap_obj h o (Heap_OBJ cls (fields_update F f v) lo ll)) o0).
       apply lookup_updated_not_affected with o (Heap_OBJ cls (fields_update F f v) lo ll) h; auto. intro contra. rewrite contra in H.
       pose proof (beq_oid_same o). try (inconsist).
       apply stack_val_object with cls_name0 F1 lo1
                                   field_defs0  method_defs0 ll1; auto.
Qed. Hint Resolve update_heap_preserve_wfe_stack_val.

Lemma update_heap_preserve_valid_ctn  : forall  o v h ct F f cls lo ctn ll,
    wfe_heap ct h ->
    valid_ctn ct ctn h ->
    Some (Heap_OBJ cls F lo ll) = lookup_heap_obj h o ->
    valid_ctn ct ctn (update_heap_obj h o (Heap_OBJ cls (fields_update F f v) lo ll)).
Proof with eauto.
  intros.
  inversion H0; subst; auto.
  apply valid_container; auto.
  apply stack_frame_wfe; auto.
  intros.
  split; auto.
  inversion H5; subst; auto.
  destruct H7 with x v0; auto.
  apply update_heap_preserve_wfe_stack_val; auto.
  inversion H5; subst; auto.
  destruct H7 with x v0; auto.
  inversion H5; subst; auto.
  destruct H7 with x v0; auto. 
Qed. Hint Resolve  update_heap_preserve_valid_ctn.


Lemma update_heap_preserve_valid_ctns : forall  o v h ct F f cls lo ctns ll,
    wfe_heap ct h ->
    valid_ctns ct ctns h ->
    Some (Heap_OBJ cls F lo ll) = lookup_heap_obj h o ->
    valid_ctns ct ctns (update_heap_obj h o (Heap_OBJ cls (fields_update F f v) lo ll)).
Proof with eauto.
       intros. induction ctns. auto.
       destruct a. auto.
       inversion H0; subst; auto.
Qed. Hint Resolve  update_heap_preserve_valid_ctns.


Lemma change_obj_label_preserve_wfe_stack_val : forall o v h ct F cls lo lo' ll,
         value v ->
         wfe_heap ct h ->
         wfe_stack_val ct h v ->
         Some (Heap_OBJ cls F lo ll) = lookup_heap_obj h o ->
         wfe_stack_val ct (update_heap_obj h o (Heap_OBJ cls F lo' ll)) v.
Proof with eauto.
  intros.
  induction H; subst; auto.
  inversion H1; subst; auto.
  
  case_eq (beq_oid o0 o); intro.
  apply beq_oid_equal in H. subst; auto. 
  assert (Some (Heap_OBJ cls F lo' ll) =
                     lookup_heap_obj
                       (update_heap_obj h o (Heap_OBJ cls F lo' ll)) o).
  apply lookup_updated with h (Heap_OBJ cls F lo ll); auto.       
  apply stack_val_object with cls_name F lo'
                              field_defs  method_defs ll; auto.
  rewrite <- H2 in H3; inversion H3; subst; auto. 

  inversion H1; subst; auto.
  assert (Some (Heap_OBJ (class_def cls_name0 field_defs0 method_defs0) F1 lo1 ll1) =
                     lookup_heap_obj
                       (update_heap_obj h o (Heap_OBJ cls F lo' ll)) o0).
  apply lookup_updated_not_affected with o (Heap_OBJ cls F lo' ll) h; auto.
  intro contra. rewrite contra in H.
  pose proof (beq_oid_same o).
  try (inconsist).
  apply stack_val_object with cls_name0 F1 lo1
                              field_defs0  method_defs0 ll1; auto.
  inversion H1; subst; auto.
  inversion H1; subst; auto.
Qed. Hint Resolve change_obj_label_preserve_wfe_stack_val .


Lemma change_obj_label_preserve_valid_ctn  : forall  o h ct F cls lo lo' ctn ll,
    wfe_heap ct h ->
    valid_ctn ct ctn h ->
    Some (Heap_OBJ cls F lo ll) = lookup_heap_obj h o ->
    valid_ctn ct ctn (update_heap_obj h o (Heap_OBJ cls F lo' ll)).
Proof with eauto.
  intros.
  inversion H0; subst; auto.
  apply valid_container; auto.
  apply stack_frame_wfe; auto.
  intros.
  split; auto.
  inversion H5; subst; auto.
  destruct H7 with x v; auto.

  apply change_obj_label_preserve_wfe_stack_val with lo; auto.
  inversion H5; subst; auto.
  destruct H7 with x v; auto.

  inversion H5; subst; auto.
  destruct H7 with x v; auto.
Qed. Hint Resolve change_obj_label_preserve_valid_ctn.


Lemma change_obj_label_preserve_valid_ctns : forall  o h ct F cls lo lo' ctns ll,
    wfe_heap ct h ->
    valid_ctns ct ctns h ->
    Some (Heap_OBJ cls F lo ll) = lookup_heap_obj h o ->
    valid_ctns ct ctns (update_heap_obj h o (Heap_OBJ cls F lo' ll)).
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
    inversion H10; subst; auto.
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
    intro contra. rewrite contra in H4; inversion H4.
    subst; auto.
    unfold hole_free; fold hole_free.
    inversion H16; subst; auto.
    inversion H6; subst; auto.
    inversion H2; subst; auto; try (inversion H11).
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
    intro contra; inversion contra).
    + apply valid_fs_list; auto. unfold hole_free; fold hole_free.
      rewrite H1; auto. try (intro contra; inversion contra).
    + apply valid_fs_list; auto. unfold hole_free; fold hole_free.
      rewrite H5; auto. try (intro contra; inversion contra).
    + rewrite H1. rewrite H2; auto.
    + rewrite H5. rewrite H8; auto. 
    
    
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
    intro contra; rewrite contra in H5; inversion H5;
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
    eauto using field_value. 
    apply valid_conf; auto;
    match goal with
    | H : valid_ctn _ _ _ |- _
      => inversion H; subst; auto 
    end.
    apply valid_container; auto.
    destruct H2; subst; auto.
    destruct H2 as [o']. subst; auto.
    intros; intro contra; inversion contra.
    destruct H2; subst; auto.
    destruct H2 as [o']. subst; auto.

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
    destruct H2; subst; auto.
    destruct H2 as [o']. subst; auto.

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


  - match goal with
    | H : valid_ctn _ _ _ |- _
      => inversion H; subst; auto 
    end;
    match goal with
    | H :  valid_fs _  |- _
      => inversion H; subst; auto 
    end.
    apply valid_conf; auto.
    apply valid_container; auto.
    inversion H2; subst; auto.
    intros. intro contra.
    rewrite contra in H4; inversion H4; intuition.
    inversion H2; subst; auto; try (inversion H11);
    try (
    apply surface_syntax_is_hole_free in H1;
    unfold hole_free; fold hole_free;
    rewrite H17; rewrite H1; auto).  inversion H1.     

   -  match goal with
    | H : valid_ctn _ _ _ |- _
      => inversion H; subst; auto 
      end.
     apply valid_conf; auto.
     apply valid_container; auto.
     apply valid_fs_list; auto.
     inversion H19; subst; auto.
     apply hole_free_if in H3. destruct H3.
     unfold hole_free; fold hole_free.
     rewrite H2; auto.

     intro contra; inversion contra.
     inversion H10; subst; auto. 
     intros.
     intro contra; inversion contra.
     inversion H19; subst; auto.
     apply hole_free_if in H3.
     destruct H3. rewrite H2. rewrite H3. auto. 
    
  -  match goal with
    | H : valid_ctn _ _ _ |- _
      => inversion H; subst; auto 
    end;
    match goal with
    | H :  valid_fs _  |- _
      => inversion H; subst; auto 
    end.
    apply valid_conf; auto.
    apply valid_container; auto.
    intros. intro contra.
    rewrite contra in H5; inversion H5; intuition.
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
    destruct H18 as [F0].
    destruct H4 as [lo0].
    destruct H4 as [ll0].
    rewrite H4 in H; inversion H; subst; auto.
    rewrite <- H6 in H13; inversion H13; subst; auto.
    rewrite H15 in H0; inversion H0; subst; auto.
    
    apply valid_conf; auto.
    apply valid_container; auto.
    intros. intro contra. inversion contra.
    apply stack_frame_wfe; auto.
    intros.
    case_eq (beq_id arg_id0 x);intro.
    unfold sf_update in H5. rewrite H10 in H5.
    inversion H5; subst; auto.
    split; auto. 
    induction H1; subst; inversion H9; subst; auto.
    +
    destruct H25 as [F'].
    destruct H1 as [lo'].
    destruct H12 as [field_defs].
    destruct H12 as [method_defs].
    destruct H1 as [ll].
    
    subst; auto.
    eauto using stack_val_object.
    + eauto using stack_val_object.
    + apply stack_val_opa_labeled.
      inversion H28; subst; auto; inversion H24; subst; auto.
      destruct H31 as [F'].
      destruct H12 as [lo'].
      destruct H25 as [field_defs].
      destruct H25 as [method_defs].
      destruct H12 as [ll]. 
      subst; auto.
      eauto using stack_val_object.
      eauto using stack_val_object.
      apply stack_val_opa_labeled.      
      eauto using stack_val_object.
    +
      unfold sf_update in H5. rewrite H10 in H5.
      inversion H5.
      
(*   valid_config (Config ct (Container (MethodCall (ObjId o) meth v) fs lb sf) ctns0 h0) *)
  - inversion H20; subst; auto.
    apply config_typing_lead_to_tm_typing in H_typing.
    destruct H_typing as [T'].
    destruct H2 as [gamma].
    inversion H2; subst; auto.
    inversion H6; subst; auto.
    inversion H13; subst; auto. 
    destruct H29 as [F0].
    destruct H3 as [lo0].
    destruct H3 as [ll0].
    rewrite H3 in H; inversion H; subst; auto.
    rewrite <- H16 in H14; inversion H14; subst; auto.
    rewrite H19 in H0; inversion H0; subst; auto.
    
    apply valid_conf; auto.
    apply valid_container; auto.
    intros. intro contra. inversion contra.
    apply stack_frame_wfe; auto.
    intros.
    case_eq (beq_id arg_id0 x);intro.
    unfold sf_update in H4. rewrite H15 in H4.
    inversion H4; subst; auto.
    split; auto. 
    induction H1; subst; inversion H8; subst; auto.
    destruct H32 as [F'].
    destruct H1 as [lo'].
    destruct H26 as [field_defs].
    destruct H26 as [method_defs].
    destruct H1 as [ll].
    eauto using stack_val_object.
    eauto using stack_val_object.
    apply stack_val_opa_labeled.      
    eauto using stack_val_object.

    unfold sf_update in H4. rewrite H15 in H4.
    inversion H4.

    
   - inversion H20; subst; auto.
     apply valid_conf; auto.
     auto. auto.
     apply  extend_heap_preserve_order with h0 (get_fresh_oid h0)
                                            cls_name
                                            field_defs
                                            method_defs lb lb; auto.
     apply fresh_oid_heap with ct ; auto.
     apply extend_heap_preserve_field_wfe with h0 (get_fresh_oid h0)
                                            cls_name
                                            field_defs
                                            method_defs lb lb; auto.
     apply fresh_oid_heap with ct ; auto.

(* valid_config (Config ct (Container e1 (labelData hole e2 :: fs) lb sf) ctns0 h0) *)
   - match goal with
    | H : valid_ctn _ _ _ |- _
      => inversion H; subst; auto 
    end;
     apply valid_conf; auto.
     apply valid_container; auto.
     inversion H8; subst; auto.
     apply valid_fs_list; auto.
     intro contra; inversion contra. 
     apply valid_fs_list; auto.
     intro contra; inversion contra.
     inversion H8; subst; auto.
     intros. intro contra; inversion contra.
     apply hole_free_if in H17. destruct H17; auto.      

     (* valid_config (Config ct (Container (labelData v e2) fs lb sf) ctns0 h0) *)
   - match goal with
    | H : valid_ctn _ _ _ |- _
      => inversion H; subst; auto 
    end;
     apply valid_conf; auto.
     apply valid_container; auto.
     inversion H6; subst; auto.
     inversion H6; subst; auto.
     inversion H2; subst; auto.
     intros; intro contra; inversion contra; subst; auto.
     inversion H6; subst; auto.
     inversion H7; subst; auto.

     inversion H6; subst; auto.
     inversion H2; subst; auto; try (inversion H11).
     apply surface_syntax_is_hole_free in H1.
     unfold hole_free; fold hole_free.
     rewrite H1.
     apply value_is_hole_free in H.
     rewrite H. auto.
     inversion H1. 

(* valid_config (Config ct (Container e2 (labelData v hole :: fs) lb sf) ctns0 h0) *)
   - match goal with
    | H : valid_ctn _ _ _ |- _
      => inversion H; subst; auto 
    end;
     apply valid_conf; auto.
     apply valid_container; auto.
     apply valid_fs_list; auto.
     unfold hole_free; fold hole_free.
     apply value_is_hole_free in H.
     rewrite H. auto.
     
     intro contra; inversion contra.
     inversion H9; subst; auto.
     intros. 
     intro contra; inversion contra.

     inversion H18; subst; auto.
     apply hole_free_if in H2; destruct H2; auto.
     rewrite H1. rewrite H2; auto. 

     (*  valid_config (Config ct (Container (labelData v1 v2) fs lb sf) ctns0 h0) *)
   - match goal with
    | H : valid_ctn _ _ _ |- _
      => inversion H; subst; auto 
    end;
     apply valid_conf; auto.
     apply valid_container; auto.
     inversion H7; subst; auto.
     intros; intro contra; subst; auto.
     inversion H7; subst; auto.
     inversion H5; subst; auto.

     apply value_is_hole_free in H.
     apply value_is_hole_free in H0.
     unfold hole_free; fold hole_free.
     rewrite H; rewrite H0; auto. 

     
     
(* valid_config (Config ct (Container (unlabel v) fs (join_label lb ell) sf) ctns0 h0) *)
   - match goal with
    | H : valid_ctn _ _ _ |- _
      => inversion H; subst; auto 
    end;
    apply valid_conf; auto.
     apply valid_container; auto.
     inversion H0; subst; auto. 

   (* valid_config (Config ct (Container (labelOf v) fs (join_label lb ell) sf) ctns0 h0) *)
   - match goal with
    | H : valid_ctn _ _ _ |- _
      => inversion H; subst; auto 
    end;
    apply valid_conf; auto.
     apply valid_container; auto.
     inversion H; subst; auto. 

     (* valid_config (Config ct (Container e1 (raiseLabel hole e2 :: fs) lb sf) ctns0 h0) *)
   - match goal with
    | H : valid_ctn _ _ _ |- _
      => inversion H; subst; auto 
    end;
    apply valid_conf; auto.
     apply valid_container; auto.
     apply valid_fs_list; auto.
     inversion H8; subst; auto.
     intro contra; inversion contra.

     inversion H8; subst; auto.
     intros. 
     intro contra; inversion contra; subst; auto. 
     
     inversion H17. apply hole_free_if in H1.
     destruct H1. rewrite H0. rewrite H1. auto. 

(* valid_config (Config ct (Container (raiseLabel v e2) fs lb sf) ctns0 h0) *)
   - match goal with
    | H : valid_ctn _ _ _ |- _
      => inversion H; subst; auto 
    end;
    apply valid_conf; auto.
     apply valid_container; auto.
     inversion H6; subst; auto.
     inversion H6; subst; auto.
     inversion H2; subst; auto.
     intro; intro contra; inversion contra.
     subst; auto.
     inversion H6; subst; auto.
     inversion H7; subst; auto. 

     inversion H6; subst; auto.
     inversion H2; subst; auto; try (inversion H11).

     apply surface_syntax_is_hole_free in H1.
     unfold hole_free; fold hole_free.
     rewrite H1.
     apply value_is_hole_free in H.
     rewrite H. auto.
     inversion H1.

 (* valid_config (Config ct (Container e2 (raiseLabel v hole :: fs) lb sf) ctns0 h0) *)
   - match goal with
    | H : valid_ctn _ _ _ |- _
      => inversion H; subst; auto 
    end;
    apply valid_conf; auto.
     apply valid_container; auto.
     apply valid_fs_list; auto.
     unfold hole_free. fold hole_free.
     apply value_is_hole_free in H. rewrite H. auto. 
     intro contra; inversion contra.

     inversion H9; subst; auto.
     intros. 
     intro contra; inversion contra; subst; auto. 
     
     inversion H18. apply hole_free_if in H2.
     destruct H2. rewrite H1. rewrite H2. auto. 
(*  valid_config (Config ct (Container (raiseLabel v1 v2) fs lb sf) ctns0 h0) *)
   - match goal with
    | H : valid_ctn _ _ _ |- _
      => inversion H; subst; auto 
    end;
    apply valid_conf; auto.
     apply valid_container; auto.
     inversion H7; subst; auto.
     intros. intro contra; inversion contra; subst; auto.
     inversion H7; subst; auto.
     inversion H8; subst; auto. 
     apply value_is_hole_free in H.
     apply value_is_hole_free in H0.
     unfold hole_free. fold hole_free.
     rewrite H. rewrite H0.  auto. 
     
     (* raise label*)
   -
     apply valid_conf; auto.
     apply change_obj_label_preserve_valid_ctns with lo; auto.
     apply change_obj_label_preserve_valid_ctn with lo; auto.
     inversion H19; subst; auto.

     eauto using change_obj_label_preserve_wfe_heap.
     eauto using change_obj_label_preserve_field_wfe.

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

     (* raise label*)
   -
     apply valid_conf; auto.
     apply change_obj_label_preserve_valid_ctns with lo; auto.
     apply change_obj_label_preserve_valid_ctn with lo; auto.
     inversion H19; subst; auto.

     eauto using change_obj_label_preserve_wfe_heap.
     eauto using change_obj_label_preserve_field_wfe.

     (*  valid_config (Config ct (Container e2 (toLabeled e1 hole :: fs) lb sf) ctns0 h0) *)

   - match goal with
    | H : valid_ctn _ _ _ |- _
      => inversion H; subst; auto 
    end;
    apply valid_conf; auto.
     apply valid_container; auto.
     apply valid_fs_list; auto.
     inversion H8; subst; auto. 
     unfold hole_free. fold hole_free.
     case_eq (hole_free e1); intro; auto.
     intro contra; inversion contra.

     inversion H8; subst; auto. 
     intros. 
     intro contra; inversion contra; subst; auto. 
     
     inversion H8; subst; auto;
     inversion H17;
     apply surface_syntax_is_hole_free in H2;
     rewrite H2 in H1; inversion H1. 

(* valid_config (Config ct (Container (toLabeled e1 v) fs lb sf) ctns0 h0) *)
   - match goal with
    | H : valid_ctn _ _ _ |- _
      => inversion H; subst; auto 
    end;
    apply valid_conf; auto.
     apply valid_container; auto.
     inversion H6; subst; auto.
     inversion H6; subst; auto.
     inversion H2; subst; auto. 
     intros. intro contra; inversion contra; subst; auto.
     inversion H6; subst; auto.
     inversion H7; subst; auto.

     inversion H6; subst; auto.
     apply value_is_hole_free in H. 
     inversion H2; subst; auto; try (inversion H14);    
     unfold hole_free; fold hole_free;
       rewrite H; try(
                      apply surface_syntax_is_hole_free in H1; rewrite H1; auto).
     inversion H11. 

(* valid_config (Config ct (Container e1 (labelData hole (l lo) :: nil) lb sf) (Container (toLabeled e1 (l lo)) fs lb sf :: ctns0) *)
   - inversion H15; subst; auto.
     apply valid_conf; auto.
     + 
       apply valid_container; auto.
       *
         apply valid_fs_list; auto.
         intro contra; inversion contra.
       *
         inversion H7; subst; auto.
       *
         intros. intro contra; inversion contra.
     +
       inversion H7; subst; auto. 
     
   (* toLabeled opaque*)
   - inversion H16; subst; auto.
     apply valid_conf; auto.
     apply valid_container; auto.
     inversion H8; subst; auto.
     inversion H4; subst; auto.
     inversion H2; subst; auto. 
       
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
    eauto using typed_value_is_wfe_stack_val. 
    destruct H1 with x v0; auto.

    destruct H1 with x v0; auto.
    unfold sf_update in Hy;
    case_eq (beq_id id x); intro;
      rewrite H7 in Hy.
    inversion Hy; subst; auto. 
    split; auto.
    eauto using typed_value_is_wfe_stack_val.
    inversion H10; subst; auto.
    destruct H12 with x v0; auto.

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
    try (
         match goal with
    | H :  valid_syntax (_ _ _) |- _
      => inversion H; subst; auto
    | H :  valid_syntax (_ _ _ _) |- _
      => inversion H; subst; auto
         end; auto).
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
      inversion H6; subst; auto.
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
          rewrite contra in H4; inversion H4; intuition.
            inversion H2; subst; auto; try (inversion H11).
            apply surface_syntax_is_hole_free in H1; auto.
            unfold hole_free. fold hole_free.
            rewrite H1; rewrite H17. auto.

(* valid_config (Config ct (Container e2 (FieldWrite v f hole :: fs) lb sf) ctns0 h0) *)            
   -  match goal with
    | H : valid_ctn _ _ _ |- _
      => inversion H; subst; auto 
     end.
     apply valid_conf; auto.
     apply valid_container; auto.
     apply valid_fs_list; auto.
      match goal with
    | H :  hole_free  _ = true |- _
      => inversion H; subst; auto;
           match goal with
           | H : (if hole_free _ then hole_free _ else false) = true |- _
             => apply hole_free_if in H; destruct H
           end
      end.
      unfold hole_free; fold hole_free.
      rewrite H2; auto.  
      
      intro contra; inversion contra.
     try (
         match goal with
    | H :  valid_syntax (_ _ _) |- _
      => inversion H; subst; auto
    | H :  valid_syntax (_ _ _ _) |- _
      => inversion H; subst; auto
        end; auto).
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

  (* valid_config (Config ct (Container (FieldWrite v1 f v2) fs lb sf) ctns0 h0) *)  
   -  match goal with
    | H : valid_ctn _ _ _ |- _
      => inversion H; subst; auto 
      end.
      inversion H7; subst; auto.
     apply valid_conf; auto.
     apply valid_container; auto.
     intro. intro contra.
     rewrite contra in H5;
       inversion H5; subst; auto.
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
     inversion H6; subst; auto.
     destruct H24 as [F'].
     destruct H2 as [lo'].
     destruct H2 as [ll'].
     rewrite H2 in H; inversion H; subst; auto.
     rewrite <- H18 in H5; inversion H5; subst; auto. 
     
     apply valid_conf; auto.
     destruct H16 as [field_defs].
     destruct H4 as [method_defs].
     eauto using field_write_preserve_wfe_heap.

     destruct H16 as [field_defs].
     destruct H4 as [method_defs].
     eauto using field_write_preserve_wfe_heap. 

     (*field write normal opa*)
   - inversion H20; subst; auto.
     apply config_typing_lead_to_tm_typing in H_typing.
     destruct H_typing as [T'].
     destruct H0 as [gamma].
     inversion H0; subst; auto.
     inversion H6; subst; auto.
     inversion H8; subst; auto. 
     destruct H28 as [F'].
     destruct H2 as [lo'].
     destruct H2 as [ll'].
     rewrite H2 in H; inversion H; subst; auto.
     rewrite <- H18 in H13; inversion H13; subst; auto. 
     
     apply valid_conf; auto.
     destruct H27 as [field_defs].
     destruct H4 as [method_defs].
     eauto using field_write_preserve_wfe_heap.

     destruct H27 as [field_defs].
     destruct H4 as [method_defs].
     eauto using field_write_preserve_wfe_heap. 
     
 (* (Config ct (Container guard (If hole s1 s2 :: fs) lb sf) ctns0 h0) *)    
   -  match goal with
    | H : valid_ctn _ _ _ |- _
      => inversion H; subst; auto 
      end.
     apply valid_conf; auto.
     apply valid_container; auto.
     apply valid_fs_list; auto.
     inversion H8; subst; auto.
     intro contra; inversion contra. 
     inversion H8; subst; auto.
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
     inversion H6; subst; auto.
     apply Valid_if3; auto.
     inversion H6; subst; auto.
     inversion H2; subst; auto.
     inversion H6; subst; auto.
     inversion H2; subst; auto. 
     
     intro. intro contra; subst; auto.
     inversion H6; subst; auto.
     inversion H4; subst; auto.

     unfold hole_free. fold hole_free.
     inversion H6; subst; auto.
     inversion H2; subst; auto.

     + inversion H12.
     +
       apply surface_syntax_is_hole_free in H11.
       apply surface_syntax_is_hole_free in H12.
       rewrite H17. rewrite H11. rewrite H12. auto.
     + inversion H12. 

   (* valid_config (Config ct (Container (If guard s1 s2) fs (join_label lb ell) sf) ctns0 h0) *)
  -  match goal with
    | H : valid_ctn _ _ _ |- _
      => inversion H; subst; auto 
      end.
    apply valid_conf; auto.
    apply valid_container; auto.
    inversion H8; subst; auto.
    inversion H3; subst; auto.
    inversion H3; subst; auto.       

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
       inversion H8; subst; auto.
       apply valid_container; auto.
       apply valid_fs_list; auto.  
     try (
         match goal with
    | H :  valid_syntax (_ _ _) |- _
      => inversion H; subst; auto
    | H :  valid_syntax (_ _ _ _) |- _
      => inversion H; subst; auto
         end; auto).     
     intro contra; inversion contra.  
     intro contra; inversion contra.
     intros. intro contra; inversion contra.
     inversion H17.
     inversion H8; subst; auto. 

 (* valid_config (Config ct (Container (Sequence v e2) fs lb sf) ctns0 h0) *)    
   -
     match goal with
    | H : valid_ctn _ _ _ |- _
      => inversion H; subst; auto 
       end.
     apply valid_conf; auto.
     apply valid_container; auto.
     inversion H6; subst; auto.
     inversion H6; subst; auto.
     inversion H2; subst; auto.

     intros. intro contra; subst; auto.
     inversion H6; subst; auto.
     inversion H4; subst; auto.
     inversion H6; subst; auto.
     inversion H2; subst; auto.
     inversion H11. unfold hole_free. fold hole_free.
     apply value_is_hole_free in H. rewrite H. apply surface_syntax_is_hole_free in H1; auto.
     inversion H12.      
     

 (* (Config ct (Container e fs lb sf) ctns0 h0) *)
   -   match goal with
    | H : valid_ctn _ _ _ |- _
      => inversion H; subst; auto 
       end.
       apply valid_conf; auto.
       apply valid_container; auto.
       inversion H8; subst; auto.

       inversion H8; subst; auto.
       
   (*(Config ct (Container (v_opa_l v lb) fs' lb' sf') ctns' h0)*)

   -   match goal with
    | H : valid_ctn _ _ _ |- _
      => inversion H; subst; auto 
       end.       
       inversion H14; subst; auto.
       inversion H4; subst; auto.       
       apply valid_conf; auto.
       apply valid_container; auto.
       apply Valid_v_opa_l; auto.
       intros. intro contra; subst; auto.
       destruct H0 with v0 lb0; auto. inversion H;auto. 
       
   -   match goal with
    | H : valid_ctn _ _ _ |- _
      => inversion H; subst; auto 
       end.
       inversion H12; subst; auto.
       inversion H2; subst; auto. 
       apply valid_conf; auto.
       apply valid_container; auto.       
       apply Valid_v_opa_l; auto.
       inversion H7; subst; auto.
       inversion H7; subst; auto. 
Qed.  Hint Resolve valid_config_preservation. 


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
    induction H0; auto;
      try (eauto using tm_has_type).

    destruct H2 as [F].
    destruct H2 as [lo].
    destruct H2 as [ll].
    assert (lookup_heap_obj
                 (add_heap_obj h (get_fresh_oid h) ho) o
               = Some  (Heap_OBJ cls_def F lo ll)).
    apply extend_heap_lookup_eq; auto.
    apply lookup_extend_heap_fresh_oid with CT (Heap_OBJ cls_def F lo ll); auto.
    apply T_ObjId with cls_def; auto.
    exists F. exists lo. exists ll. auto.
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
    eauto using T_fs_hole. 
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
                                               cls_def clsT field_defs method_defs ll ll',
      wfe_heap ct h ->
      tm_has_type ct Gamma h t T ->
      Some (Heap_OBJ cls_def F lb ll) = lookup_heap_obj h o ->
      cls_def = class_def clsT field_defs method_defs ->
      Some cls_def = ct clsT ->
      tm_has_type ct Gamma (update_heap_obj h o (Heap_OBJ cls_def F' lb' ll')) t T.
  Proof with eauto.
    intros.
    induction H0; auto; try (eauto using tm_has_type).

    destruct H5 as [F0].
    destruct H5 as [lo'].
    destruct H5 as [ll0'].
    remember ( (update_heap_obj h o (Heap_OBJ cls_def F' lb' ll'))) as h'.
    case_eq (beq_oid o0 o); intro.
    apply beq_oid_equal in H6.
    
    assert (Some (Heap_OBJ cls_def F' lb' ll') = lookup_heap_obj h' o0).
    apply lookup_updated with h (Heap_OBJ cls_def F lb ll); auto;
      subst; auto.
    subst; auto.
    rewrite H5 in H1; inversion H1; subst; auto.
    apply T_ObjId with (class_def clsT field_defs method_defs); auto.
    exists F'. exists lb'. exists ll'.  auto.

    assert (Some (Heap_OBJ cls_def0 F0 lo' ll0') = lookup_heap_obj h' o0).
    apply lookup_updated_not_affected with o  (Heap_OBJ cls_def F' lb' ll') h; auto.
    intro contra; subst; auto.
    pose proof (beq_oid_same o); try (inconsist).
    apply T_ObjId with cls_def0; auto.
    exists F0. exists lo'. exists ll0'. auto.
  Qed. Hint Resolve field_write_preserve_typed_tm.

Check tm_hole_has_type. 
  Lemma field_write_preserve_typed_hole_tm : forall ct h t Gamma o F lb F' lb' T
                                               cls_def clsT field_defs method_defs ll ll',
      wfe_heap ct h ->
      tm_hole_has_type ct Gamma h t T ->
      Some (Heap_OBJ cls_def F lb ll) = lookup_heap_obj h o ->
      cls_def = class_def clsT field_defs method_defs ->
      Some cls_def = ct clsT ->
      tm_hole_has_type ct Gamma (update_heap_obj h o (Heap_OBJ cls_def F' lb' ll')) t T.
  Proof with eauto.
    intros.
    induction H0; subst; auto.
    - 
      try (eauto using tm_hole_has_type; fail).
    -
      try (eauto using tm_hole_has_type; fail).
    - 
      try (eauto using tm_hole_has_type; fail).
    -
      try (eauto using tm_hole_has_type; fail).
    - 
      try (eauto using tm_hole_has_type; fail).
    - 
      try (eauto using tm_hole_has_type; fail).
    - apply  T_hole_labelData2; auto.
      apply field_write_preserve_typed_tm with  F lb clsT field_defs method_defs ll; auto.       
    -  eauto using field_write_preserve_typed_tm.  
    - try (eauto using tm_hole_has_type; fail).
    - 
      try (eauto using tm_hole_has_type; fail).
    -
      try (eauto using tm_hole_has_type; fail).
    -
      try (eauto using tm_hole_has_type; fail).
    -
      try (eauto using tm_hole_has_type; fail).
    -
      try (eauto using tm_hole_has_type; fail).   
  Qed. Hint Resolve  field_write_preserve_typed_hole_tm.



   Lemma field_write_preserve_typed_fs : forall ct h fs Gamma o F lb F' lb' T T0
                                                cls_def clsT field_defs method_defs ll ll',
      wfe_heap ct h ->
      fs_has_type ct Gamma h fs (ArrowTy T T0) ->
      Some (Heap_OBJ cls_def F lb ll) = lookup_heap_obj h o ->
      cls_def = class_def clsT field_defs method_defs ->
      Some cls_def = ct clsT ->
      fs_has_type ct Gamma (update_heap_obj h o (Heap_OBJ cls_def F' lb' ll')) fs (ArrowTy T T0).
  Proof with eauto.
    intros. generalize dependent T. generalize dependent T0.
    induction fs; intros; auto.
    inversion H0; auto.
    inversion H0; subst; auto.
    eauto using T_fs_hole. 
  Qed. Hint Resolve field_write_preserve_typed_fs.


  Lemma field_write_preserve_typed_sf : forall ct h sf Gamma o F lb F' lb'
                                                cls_def clsT field_defs method_defs ll ll',
      wfe_heap ct h ->
      well_typed_stack_frame ct Gamma sf h ->
      Some (Heap_OBJ cls_def F lb ll) = lookup_heap_obj h o ->
      cls_def = class_def clsT field_defs method_defs ->
      Some cls_def = ct clsT ->
      well_typed_stack_frame ct Gamma sf (update_heap_obj h o (Heap_OBJ cls_def F' lb' ll')).
  Proof with eauto.
    intros.     
    inversion H0; subst; auto.
    apply well_typed_sf; auto; intros.
    destruct H4 with x T; auto. destruct H5.
    rename x0 into v. 
    exists v; split; auto.
    eauto using field_write_preserve_typed_tm . 
  Qed. Hint Resolve field_write_preserve_typed_sf.

  Lemma field_write_preserve_typed_ctn : forall ct h ctn Gamma o F lb F' lb' T T0
                                                cls_def clsT field_defs method_defs ll ll',
      wfe_heap ct h ->
      ctn_has_type ct Gamma h ctn (ArrowTy T T0) ->
      Some (Heap_OBJ cls_def F lb ll) = lookup_heap_obj h o ->
      cls_def = class_def clsT field_defs method_defs ->
      Some cls_def = ct clsT ->
      ctn_has_type ct Gamma (update_heap_obj h o (Heap_OBJ cls_def F' lb' ll')) ctn (ArrowTy T T0).
  Proof with eauto.
    intros.
    induction H0; subst; auto.
    eauto using T_ctn_type. 
  Qed. Hint Resolve field_write_preserve_typed_ctn.
  
  
  Lemma field_write_preserve_typed_ctns : forall ct h ctns Gamma o F lb F' lb' T T0
                                                cls_def clsT field_defs method_defs ll ll',
      wfe_heap ct h ->
     ctn_list_has_type ct Gamma h ctns (ArrowTy T T0) ->
      Some (Heap_OBJ cls_def F lb ll) = lookup_heap_obj h o ->
      cls_def = class_def clsT field_defs method_defs ->
      Some cls_def = ct clsT ->
      ctn_list_has_type ct Gamma (update_heap_obj h o (Heap_OBJ cls_def F' lb' ll')) ctns (ArrowTy T T0).
  Proof with eauto.
    intros.
    induction H0; subst; auto.
    apply T_ctn_list with T2 Gamma'; auto.
    eauto using field_write_preserve_typed_ctn; auto.
  Qed. Hint Resolve field_write_preserve_typed_ctns.

  Hint Resolve lookup_updated. 
  Lemma change_obj_label_preserve_typed_tm : forall ct h t Gamma o F lo lo' T
                                               cls_def clsT field_defs method_defs ll ll',
      wfe_heap ct h ->
      tm_has_type ct Gamma h t T ->
      Some (Heap_OBJ cls_def F lo ll) = lookup_heap_obj h o ->
      cls_def = class_def clsT field_defs method_defs ->
      Some cls_def = ct clsT ->
      tm_has_type ct Gamma (update_heap_obj h o (Heap_OBJ cls_def F lo' ll')) t T.
  Proof with eauto.
    intros.
    inversion  H0; subst; auto.
    - try (eauto using tm_has_type).
    - try (eauto using tm_has_type).
    - try (eauto using tm_has_type).
    - try (eauto using tm_has_type).
    - try (eauto using tm_has_type).
    - try (eauto using tm_has_type).
    - try (eauto using tm_has_type).
    - try (eauto using tm_has_type).
    - try (eauto using tm_has_type).
    - try (eauto using tm_has_type).
    - try (eauto using tm_has_type).
    - try (eauto using tm_has_type).
    - try (eauto using tm_has_type).
    - case_eq (beq_oid o o0); intro.
      apply beq_oid_equal in H2; subst; auto. 
      destruct H5 as [field_defs'].
      destruct H2 as [method_defs'].
      destruct H6 as [F'].
      destruct H5 as [lo1].
      destruct H5 as [ll1].
      rewrite H5 in H1; inversion H1; subst; auto.
      inversion H7; subst; auto.
      apply  T_ObjId with  (class_def cls_name field_defs' method_defs') ; auto.
      exists field_defs'. exists method_defs'. auto.
      exists F'. exists lo'. exists ll'; auto.
      assert (Some (Heap_OBJ (class_def cls_name field_defs' method_defs') F' lo' ll') = lookup_heap_obj
                                                                                           (update_heap_obj h o0 (Heap_OBJ (class_def cls_name field_defs' method_defs') F' lo' ll')) o0).
      apply lookup_updated with h (Heap_OBJ (class_def cls_name field_defs' method_defs') F' lo1 ll1); auto.
      auto.

      destruct H5 as [field_defs'].
      destruct H5 as [method_defs'].
      destruct H6 as [F'].
      destruct H6 as [lo1].
      destruct H6 as [ll1].
      apply  T_ObjId with cls_def0; auto.
      exists field_defs'. exists method_defs'. auto.
      exists F'. exists lo1. exists ll1.
      assert (Some (Heap_OBJ cls_def0 F' lo1 ll1) = lookup_heap_obj (update_heap_obj h o (Heap_OBJ (class_def clsT field_defs method_defs) F lo' ll')) o0).
      apply lookup_updated_not_affected with o (Heap_OBJ (class_def clsT field_defs method_defs) F lo' ll') h   ; auto.
      intro contra; subst; auto. assert (beq_oid o o = true).
      apply beq_oid_same. rewrite H2 in H5 ; inversion H5; auto.
      auto.      
      
    - try (eauto using tm_has_type).
    - try (eauto using tm_has_type).
Qed. Hint Resolve    change_obj_label_preserve_typed_tm.          

  Lemma change_obj_label_preserve_typed_hole_tm : forall ct h t Gamma o F lo lo' T
                                               cls_def clsT field_defs method_defs ll ll',
      wfe_heap ct h ->
      tm_hole_has_type ct Gamma h t T ->
      Some (Heap_OBJ cls_def F lo ll) = lookup_heap_obj h o ->
      cls_def = class_def clsT field_defs method_defs ->
      Some cls_def = ct clsT ->
      tm_hole_has_type ct Gamma (update_heap_obj h o (Heap_OBJ cls_def F lo' ll')) t T.
  Proof with eauto.
    intros.
    induction H0; subst; auto.
    - apply T_EqCmp1 with e1; auto;
      eauto using field_write_preserve_typed_tm; auto. 
    - apply T_EqCmp2 with e2; auto;
      eauto using field_write_preserve_typed_tm; auto. 
    - apply T_hole_FieldAccess with cls_def0 (find_fields cls_def0); auto;
      eauto using field_write_preserve_typed_tm; auto.
    -
      eauto using T_hole_MethodCall1.
    -    eauto using T_hole_MethodCall2.
    - eauto using tm_hole_has_type ; auto.     
    - apply  T_hole_labelData2; auto.
      apply change_obj_label_preserve_typed_tm with lo clsT field_defs
                                                    method_defs ll
      ; auto.
    - eauto using tm_hole_has_type ; auto.
    - eauto using tm_hole_has_type ; auto.
    - eauto using tm_hole_has_type ; auto.
    - eauto using tm_hole_has_type ; auto.
    - eauto using tm_hole_has_type ; auto.
    - eauto using tm_hole_has_type ; auto.
    - eauto using tm_hole_has_type ; auto.
  Qed. Hint Resolve  change_obj_label_preserve_typed_hole_tm.



   Lemma change_obj_label_preserve_typed_fs : forall ct h fs Gamma o F lo lo' T T0
                                                cls_def clsT field_defs method_defs ll ll',
      wfe_heap ct h ->
      fs_has_type ct Gamma h fs (ArrowTy T T0) ->
      Some (Heap_OBJ cls_def F lo ll) = lookup_heap_obj h o ->
      cls_def = class_def clsT field_defs method_defs ->
      Some cls_def = ct clsT ->
      fs_has_type ct Gamma (update_heap_obj h o (Heap_OBJ cls_def F lo' ll')) fs (ArrowTy T T0).
  Proof with eauto.
    intros. generalize dependent T. generalize dependent T0.
    induction fs; intros; auto.
    inversion H0; auto.
    inversion H0; subst; auto.
    eauto using T_fs_hole. 
  Qed. Hint Resolve change_obj_label_preserve_typed_fs.


  Lemma change_obj_label_preserve_typed_sf : forall ct h sf Gamma o F lo lo'
                                                cls_def clsT field_defs method_defs ll ll',
      wfe_heap ct h ->
      well_typed_stack_frame ct Gamma sf h ->
      Some (Heap_OBJ cls_def F lo ll) = lookup_heap_obj h o ->
      cls_def = class_def clsT field_defs method_defs ->
      Some cls_def = ct clsT ->
      well_typed_stack_frame ct Gamma sf (update_heap_obj h o (Heap_OBJ cls_def F lo' ll')).
  Proof with eauto.
    intros.     
    inversion H0; subst; auto.
    apply well_typed_sf; auto; intros.
    destruct H4 with x T; auto. destruct H5.
    rename x0 into v. 
    exists v; split; auto.
    eauto using field_write_preserve_typed_tm. 
  Qed. Hint Resolve change_obj_label_preserve_typed_sf.

  Lemma change_obj_label_preserve_typed_ctn : forall ct h ctn Gamma o F lo lo' T T0
                                                     cls_def clsT field_defs method_defs ll ll',
      wfe_heap ct h ->
      ctn_has_type ct Gamma h ctn (ArrowTy T T0) ->
      Some (Heap_OBJ cls_def F lo ll) = lookup_heap_obj h o ->
      cls_def = class_def clsT field_defs method_defs ->
      Some cls_def = ct clsT ->
      ctn_has_type ct Gamma (update_heap_obj h o (Heap_OBJ cls_def F lo' ll')) ctn (ArrowTy T T0).
  Proof with eauto.
    intros.
    induction H0; subst; auto.
    eauto using T_ctn_type. 
  Qed. Hint Resolve change_obj_label_preserve_typed_ctn.
  
  
  Lemma change_obj_label_preserve_typed_ctns : forall ct h ctns Gamma o F lo lo' T T0
                                                cls_def clsT field_defs method_defs ll ll',
      wfe_heap ct h ->
     ctn_list_has_type ct Gamma h ctns (ArrowTy T T0) ->
      Some (Heap_OBJ cls_def F lo ll) = lookup_heap_obj h o ->
      cls_def = class_def clsT field_defs method_defs ->
      Some cls_def = ct clsT ->
      ctn_list_has_type ct Gamma (update_heap_obj h o (Heap_OBJ cls_def F lo' ll')) ctns (ArrowTy T T0).
  Proof with eauto.
    intros.
    induction H0; subst; auto.
    apply T_ctn_list with T2 Gamma'; auto.
    eauto using field_write_preserve_typed_ctn; auto.
  Qed. Hint Resolve change_obj_label_preserve_typed_ctns.



  
  
                                                       
    
  
Theorem typing_preservation : forall T ct
                                   ctn ctns h
                                   ctn' ctns' h',
    well_typed_class_table ct ->  
    config_has_type ct empty_context (Config ct ctn ctns h) T ->
    valid_config (Config ct  ctn ctns h) ->
    Config ct ctn ctns h
           ==> Config ct ctn' ctns' h' ->
    config_has_type ct empty_context (Config ct ctn' ctns' h') T.
Proof with eauto.
  intros T ct ctn ctns h ctn' ctns' h'.
  intro H_wfe_ct. 
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

   match goal with
    | H : ctn_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
   end.
  match goal with
    | H : tm_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
  end.
  inversion H14; subst; auto. 
  assert (tm_has_type ct Gamma' h' v T1 ).
  destruct H0 with id T1; auto.
  destruct H1; subst; auto. 
  rewrite H1 in H; inversion H; subst; auto.
  eauto using config_has_type.

     
(* (Container e1 (EqCmp hole e2 :: fs) lb sf) *)
-  inversion H_typing; subst; auto.
   match goal with
    | H : ctn_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
   end.
  match goal with
    | H : tm_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
  end.
   apply T_config_ctns with T0   (classTy clsT) Gamma'; auto.
   apply T_ctn_type; auto.
   eauto using T_fs_hole. 


(*(Container (EqCmp v e2)*)
- inversion H_typing; subst; auto.
   match goal with
    | H : ctn_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
   end.
  match goal with
    | H : fs_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
  end.
  match goal with
    | H : tm_hole_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
  end.

   + apply T_config_ctns with T0 boolTy Gamma'; auto.
     apply T_ctn_type; auto.
     eauto using tm_has_type.
   +
     inversion H20; subst; auto.
     inversion H2. 

(* e2 (EqCmp v hole :: fs) *)
-  inversion H_typing; subst; auto.
   match goal with
    | H : ctn_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
   end.
  match goal with
    | H : tm_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
  end.
   apply T_config_ctns with T0   (classTy clsT) Gamma'; auto.
   apply T_ctn_type; auto.
   apply  T_fs_hole with boolTy; auto.
   unfold hole_free. fold hole_free.
   case_eq (hole_free v); intro; auto.    
   eauto using T_fs_hole.

    
(*(Container (EqCmp v1 v2)*)
- inversion H_typing; subst; auto.
  match goal with
    | H : ctn_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
   end.
  match goal with
    | H : fs_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
  end.
  match goal with
    | H : tm_hole_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
  end.
   + apply T_config_ctns with T0 boolTy Gamma'; auto.
     apply T_ctn_type; auto.
     eauto using tm_has_type.
   +
     apply T_config_ctns with T0 boolTy Gamma'; auto.
     apply T_ctn_type; auto.
     eauto using tm_has_type.

- (* (Container result fs lb sf)  *)
  inversion H_typing; subst; auto.
  match goal with
    | H : ctn_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
   end.
  match goal with
    | H : tm_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
  end. 
  apply T_config_ctns with T0 boolTy Gamma'; auto.
  apply T_ctn_type; auto.
  pose proof (exclude_middle_runtime_val v1 v2 H H0).
  destruct H3.
  apply H1 in H3; subst; auto.
  apply H2 in H3; subst; auto.

  (* (Container e (FieldAccess hole f :: fs) lb sf) *)
-
  inversion H_typing; subst; auto.
  match goal with
    | H : ctn_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
   end.
  match goal with
    | H : tm_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
  end.
  apply T_config_ctns with T0   (classTy clsT) Gamma'; auto.
  apply T_ctn_type; auto.
  eauto using T_fs_hole.

          
  (*field access return v to hole *)
- inversion H_typing; subst; auto.
     match goal with
    | H : ctn_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
   end.
  match goal with
    | H : fs_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
  end.
  match goal with
    | H : tm_hole_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
  end.
   apply T_config_ctns with T0 (classTy cls') Gamma'; auto.
   apply T_ctn_type; auto.
   eauto using tm_has_type.

  (*(Container v fs (join_label lo lb) sf)*)
  - inversion H_typing; subst; auto.

      match goal with
    | H : ctn_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
   end.
  match goal with
    | H : tm_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
  end.
  inversion H3; subst; auto. 
    destruct H18 as [F0].
    destruct H1 as [lo0].
    destruct H1 as [ll0].
    rewrite H1 in H; inversion H; subst; auto.
    rewrite <- H5 in H4; inversion H4; subst; auto.
    apply T_config_ctns with (classTy cls') (classTy cls') Gamma'; auto.
    apply T_ctn_type; auto.  
    destruct H14 as [field_defs].
    destruct H2 as [method_defs].
    assert (v = null \/
             (exists
                (o' : oid) (field_defs0 : list field) (method_defs0 : 
                                                       list method_def) 
              (field_cls_def : CLASS) (F' : FieldMap) (lo : Label) ll,
                v = ObjId o' /\
                field_cls_def =
                class_def cls' field_defs0 method_defs0 /\
                lookup_heap_obj h' o'  = Some (Heap_OBJ field_cls_def F' lo ll) /\
                ct cls' = Some field_cls_def)
           ).
    inversion H_valid_config; subst; auto.
    eauto using field_consist_typing. 

    destruct H8; subst; auto.
    destruct H8 as [o'].
    destruct H2 as [field_defs0]. 
    destruct H2 as [method_defs0].
    destruct H2 as [field_cls_def].
    destruct H2 as [FF].
    destruct H2 as [loF].
    destruct H2 as [llF].
    destruct H2.
    destruct H8. destruct H12. subst;auto.
    apply T_ObjId with  (class_def cls' field_defs0 method_defs0); auto.
    exists field_defs0. exists method_defs0. auto. 
    exists FF. exists loF. exists llF. auto.

    apply T_ctn_list with  T0 Gamma'; auto.

    

  (*(Container v fs (join_label lo lb) sf)*)
  -
    inversion H_typing; subst; auto.
    match goal with
    | H : ctn_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
   end.
    match goal with
    | H : tm_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
  end.
    inversion H3; subst; auto. 
    inversion H8; subst; auto.
    destruct H22 as [F0].
    destruct H1 as [lo0].
    destruct H1 as [ll0].
    rewrite H1 in H; inversion H; subst; auto.
    rewrite <- H12 in H4; inversion H4; subst; auto.
    apply T_config_ctns with (classTy cls') (classTy cls') Gamma'; auto.
    apply T_ctn_type; auto.  
    destruct H21 as [field_defs].
    destruct H2 as [method_defs].
    assert (v = null \/
             (exists
                (o' : oid) (field_defs0 : list field) (method_defs0 : 
                                                       list method_def) 
              (field_cls_def : CLASS) (F' : FieldMap) (lo : Label) ll,
                v = ObjId o' /\
                field_cls_def =
                class_def cls' field_defs0 method_defs0 /\
                lookup_heap_obj h' o'  = Some (Heap_OBJ field_cls_def F' lo ll) /\
                ct cls' = Some field_cls_def)
           ).
    inversion H_valid_config; subst; auto.
    eauto using field_consist_typing. 

    destruct H13; subst; auto.
    destruct H13 as [o'].
    destruct H2 as [field_defs0]. 
    destruct H2 as [method_defs0].
    destruct H2 as [field_cls_def].
    destruct H2 as [FF].
    destruct H2 as [loF].
    destruct H2 as [llF].
    destruct H2.
    destruct H13. destruct H14. subst;auto.
    apply T_ObjId with  (class_def cls' field_defs0 method_defs0); auto.
    exists field_defs0. exists method_defs0. auto. 
    exists FF. exists loF. exists llF. auto.
    apply T_ctn_list with  T0 Gamma'; auto.
    
  (* method call context *)
  -  inversion H_typing; subst; auto.
     match goal with
    | H : ctn_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
   end.
  match goal with
    | H : tm_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
  end.
     apply T_config_ctns with T0 (classTy T2) Gamma'; auto.
     apply T_ctn_type; auto.
     eauto using T_fs_hole.

(*(MethodCall t id0 e2) *)
  - inversion H_typing; subst; auto.
    inversion H6; subst; auto.
    inversion H15; subst; auto.
    inversion H13; subst; auto.
   + apply T_config_ctns with T0 T' Gamma'; auto.
     apply T_ctn_type; auto.
     eauto using tm_has_type.
   + 
     inversion H_valid_config; subst; auto.
     inversion H22; subst; auto.
     inversion H11; subst; auto.
     inversion H2; subst; auto; try (inconsist_hole_free).

(* config_has_type ct empty_context (Config ct (Container e2 (MethodCall v id hole :: fs) lb sf) ctns' h')
   T *)
  -
    inversion H_typing; subst; auto.
    inversion H8; subst; auto.
    inversion H12; subst; auto. 
    apply T_config_ctns with T0 arguT Gamma'; auto.
    apply T_ctn_type; auto.
    apply T_fs_hole with T1; auto.
    unfold hole_free; fold hole_free.
    case_eq (hole_free v); intro; auto.
    eauto using tm_hole_has_type. 
         
    
 (*(MethodCall v1 id v2) *)   
  - inversion H_typing; subst; auto.
    inversion H7; subst; auto.
    inversion H16; subst; auto.
    inversion H14; subst; auto.
    + inversion H19.
    + apply T_config_ctns with T0 T' Gamma'; auto.
     apply T_ctn_type; auto.
     eauto using tm_has_type.

(* config_has_type ct empty_context (Config ct (Container body nil lb (sf_update empty_stack_frame arg_id v)) (Container return_hole fs lb sf :: ctns0) h') T *)

  - inversion H_typing; subst; auto.
    match goal with
    | H : ctn_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
   end.
    match goal with
    | H : tm_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
  end.
    inversion H5; subst; auto.
    destruct H21 as [F0].
    destruct H2 as [lo0].
    destruct H2 as [ll0].    
    rewrite H2 in H; inversion H; subst; auto.
    rewrite <- H4 in H15; inversion H15; subst; auto.
    rewrite H19 in H0; inversion H0; subst; auto.
    
    remember ( (update_typing empty_context arg_id0 arguT)) as gamma0.
    apply T_config_ctns with T1 T1 gamma0; auto.
    inversion H_wfe_ct; subst; auto.
    assert (tm_has_type ct (update_typing empty_context arg_id0 arguT) h' body0 T1).
    destruct H18 as [field_defs'].
    destruct H9 as [method_defs'].
    apply H3 with T2 cls_def0 field_defs' method_defs' meth arguT arg_id0; auto.
    apply T_ctn_type; auto.
(*well typed stack frame*)
    apply well_typed_sf;auto.
    intros.
    case_eq (beq_id arg_id0 x);intro;
      unfold sf_update. rewrite H14;
    exists v; split; auto.
    subst; auto. unfold update_typing in H13; rewrite H14 in H13.
    inversion H13; subst; auto. 
    apply value_typing_invariant_gamma with Gamma';auto.

    rewrite H14.
    subst; auto. unfold update_typing in H13; rewrite H14 in H13.
    inversion H13.

    apply T_ctn_list with T0 Gamma'; auto.  
     
  - inversion H_typing; subst; auto.  
    match goal with
    | H : ctn_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
   end.
    match goal with
    | H : tm_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
    end.
    inversion H5; subst; auto.
    inversion H8; subst; auto. 

    destruct H25 as [F0].
    destruct H2 as [lo0].
    destruct H2 as [ll0].    
    rewrite H2 in H; inversion H; subst; auto.
    rewrite <- H13 in H15; inversion H15; subst; auto.
    rewrite H19 in H0; inversion H0; subst; auto.
    
    remember ( (update_typing empty_context arg_id0 arguT)) as gamma0.
    apply T_config_ctns with T1 T1 gamma0; auto.
    inversion H_wfe_ct; subst; auto.
    assert (tm_has_type ct (update_typing empty_context arg_id0 arguT) h' body0 T1).
    destruct H24 as [field_defs'].
    destruct H14 as [method_defs'].
    apply H3 with T2 cls_def0 field_defs' method_defs' meth arguT arg_id0; auto.
    apply T_ctn_type; auto.
(*well typed stack frame*)
    apply well_typed_sf;auto.
    intros.
    case_eq (beq_id arg_id0 x);intro;
      unfold sf_update. rewrite H22;
    exists v; split; auto.
    subst; auto. unfold update_typing in H18; rewrite H22 in H18.
    inversion H18; subst; auto. 
    apply value_typing_invariant_gamma with Gamma';auto.

    rewrite H22.
    subst; auto. unfold update_typing in H18; rewrite H22 in H18.
    inversion H18.
    apply T_ctn_list with T0 Gamma'; auto.  
  
(*new expression*)
- inversion H_typing; subst;auto.
    match goal with
    | H : ctn_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
   end.
    match goal with
    | H : tm_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
    end.

  destruct H4 as [cls_def0].
  destruct H0 as [field_defs0].
  destruct H0 as [method_defs0].
  destruct H0.         

  apply T_config_ctns with T0 (classTy cls_name) Gamma'; auto;
    try (intro contra; inversion contra).
  apply T_ctn_type.
  apply T_ObjId with cls_def0; auto.
  exists field_defs0. exists method_defs0. auto.

  pose proof (extend_heap_lookup_new h0
                (Heap_OBJ (class_def cls_name field_defs method_defs )
                          (init_field_map
                             (find_fields (class_def cls_name field_defs method_defs))
                             empty_field_map) lb lb)).
  rewrite H0 in H. inversion H; subst; auto.
  inversion H4; subst; auto.
  exists ((init_field_map (find_fields (class_def cls_name field_defs method_defs))
               empty_field_map)).
  exists lb. exists lb.  auto.  
   
  apply expand_heap_preserve_typed_sf;auto.
  inversion H_valid_config ; auto. 

  apply expand_heap_preserve_typed_fs ; auto.
  inversion H_valid_config ; auto. 

  apply expand_heap_preserve_typed_ctns; auto. 
  inversion H_valid_config ; auto. 
       
(* labelData context rules*)
-  inversion H_typing; subst; auto.
    match goal with
    | H : ctn_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
   end.
    match goal with
    | H : tm_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
    end.
   apply T_config_ctns with T0 T2 Gamma'; auto.
   apply T_ctn_type; auto.
   eauto using T_fs_hole. 

- inversion H_typing; subst; auto.
      match goal with
    | H : ctn_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
   end.
    match goal with
    | H : fs_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
    end.
        match goal with
    | H : tm_hole_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
   end.

        

   + apply T_config_ctns with T0 (LabelelTy T1) Gamma'; auto.
   +
     inversion H11; subst; auto.

(* e2 (labelData v hole :: fs) *)
-  inversion H_typing; subst; auto.
    match goal with
    | H : ctn_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
   end.
    match goal with
    | H : tm_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
    end.
   apply T_config_ctns with T0 LabelTy Gamma'; auto.
   apply T_ctn_type; auto.
   apply  T_fs_hole with (LabelelTy T2); auto.
   unfold hole_free. fold hole_free.
   case_eq (hole_free v); intro; auto.    
    
(*(Container (labelData v1 v2)*)
- inversion H_typing; subst; auto.
  match goal with
    | H : ctn_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
   end.
    match goal with
    | H : fs_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
    end.
    match goal with
    | H : tm_hole_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
   end.
  + inversion H5.
  +
    apply T_config_ctns with T0 (LabelelTy T2) Gamma'; auto.

- (* v_l v lo *)
  inversion H_typing; subst; auto.
      match goal with
    | H : ctn_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
   end.
    match goal with
    | H : tm_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
    end.
  apply T_config_ctns with T0 (LabelelTy T2 ) Gamma'; auto.

- (* v_l v lo *)
  inversion H_typing; subst; auto.
    match goal with
    | H : ctn_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
   end.
    match goal with
    | H : tm_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
    end.
  apply T_config_ctns with T0 (LabelelTy T2 ) Gamma'; auto.


(* unlabel context rules*)
-  inversion H_typing; subst; auto.
       match goal with
    | H : ctn_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
   end.
    match goal with
    | H : tm_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
    end.
   apply T_config_ctns with T0 (LabelelTy T1) Gamma'; auto.
   apply T_ctn_type; auto.
   eauto using T_fs_hole. 

- inversion H_typing; subst; auto.
    match goal with
    | H : ctn_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
   end.
    match goal with
    | H : fs_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
    end.
        match goal with
    | H : tm_hole_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
   end.

   eauto using T_config_ctns.
   
- (*   (join_label lb0 lo)   *)
  inversion H_typing; subst; auto.
   match goal with
    | H : ctn_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
   end.
   match goal with
    | H : tm_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
   end.
   inversion H4; subst; auto. 
   eauto using T_config_ctns.
   
- (* (Config ct (Container (unlabel v) fs (join_label lb ell) sf) ctns' h')  *)
  inversion H_typing; subst; auto.
  match goal with
    | H : ctn_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
   end.
  match goal with
    | H : tm_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
   end.
   inversion H4; subst; auto. 
   eauto using T_config_ctns.

(* labelOf context rule*)   
-  inversion H_typing; subst; auto.
   match goal with
    | H : ctn_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
   end.
  match goal with
    | H : tm_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
  end.
  eauto using T_config_ctns.

- inversion H_typing; subst; auto.
   match goal with
    | H : ctn_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
   end.
  match goal with
    | H : fs_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
  end.
  match goal with
    | H : tm_hole_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
  end.
  eauto using T_config_ctns.   

- (* l lo *)
  inversion H_typing; subst; auto.
  match goal with
    | H : ctn_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
  end.
   match goal with
    | H : tm_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
  end.
  eauto using T_config_ctns.

(*(Config ct (Container (labelOf v) fs (join_label lb ell) sf) ctns' h') T*)
- inversion H_typing; subst; auto.
  match goal with
    | H : ctn_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
  end.
   match goal with
    | H : tm_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
   end.
   inversion H4; subst; auto. 
   eauto using T_config_ctns.

(* objectLabelOf context rule*)   
-  inversion H_typing; subst; auto.
   match goal with
    | H : ctn_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
   end.
  match goal with
    | H : tm_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
  end.
  eauto using T_config_ctns.

- inversion H_typing; subst; auto.
   match goal with
    | H : ctn_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
   end.
  match goal with
    | H : fs_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
  end.
  match goal with
    | H : tm_hole_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
  end.
  eauto using T_config_ctns.


- (* l lo *)
  inversion H_typing; subst; auto.
  match goal with
    | H : ctn_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
  end.
   match goal with
    | H : tm_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
  end.
   eauto using T_config_ctns.

- (* l lo opa *)
  inversion H_typing; subst; auto.
  match goal with
    | H : ctn_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
  end.
   match goal with
    | H : tm_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
  end.
   eauto using T_config_ctns.
  
(* (Config ct (Container e (raiseLabel hole lo :: fs) lb sf) ctns' h') *)
-  inversion H_typing; subst; auto.
   match goal with
    | H : ctn_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
   end.
  match goal with
    | H : tm_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
  end.
  eauto using T_config_ctns.

- inversion H_typing; subst; auto.
   match goal with
    | H : ctn_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
   end.
  match goal with
    | H : fs_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
  end.
  match goal with
    | H : tm_hole_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
  end.
  + eauto using T_config_ctns. 
  + match goal with
    | H : valid_config _ |- _
      => inversion H; subst; auto 
    end.
    match goal with
    | H : valid_ctn _ _ _ |- _
      => inversion H; subst; auto 
    end.
    match goal with
    | H : valid_fs _ |- _
      => inversion H; subst; auto 
    end.
    match goal with
    | H : valid_syntax (raiseLabel hole hole) |- _
      => inversion H; subst; auto 
    end;
    try (match goal with
    | H : surface_syntax hole = true |- _
      => inversion H; subst; auto 
         end);
    try (match goal with
    | H : value hole |- _
      => inversion H; subst; auto 
    end).

(* (Config ct (Container e2 (raiseLabel v hole :: fs) lb sf) ctns' h') *)
-  inversion H_typing; subst; auto.
   match goal with
    | H : ctn_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
   end.
   match goal with
    | H : tm_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
   end.
   apply T_config_ctns with T0 LabelTy Gamma'; auto.
   apply T_ctn_type ; auto.
   apply T_fs_hole with (classTy clsT); auto.
   unfold hole_free; fold hole_free;
   case_eq (hole_free v); intro; auto. 

- inversion H_typing; subst; auto.
   match goal with
    | H : ctn_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
   end.
  match goal with
    | H : fs_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
  end.
  match goal with
    | H : tm_hole_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
  end.
  + match goal with
    | H : tm_has_type _ _ _ hole _ |- _
      => inversion H; subst; auto 
   end.
  + eauto using T_config_ctns. 

-  (*(Container (raiseLabel (ObjId o) lo') fs lb sf)*)
  inversion H_typing; subst; auto.
  match goal with
    | H : ctn_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
  end.
  match goal with
    | H : tm_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
  end.
  destruct H15 as [cls_def].
  destruct H2 as [field_defs].
  destruct H2 as [method_defs].
  destruct H2.  
  apply T_config_ctns with T0 (classTy clsT) Gamma'; auto.
  + apply T_ctn_type; auto.
    
    ++
      apply heap_preserve_typing with h0; auto.
    intros.
    case_eq (beq_oid o0 o); intro.
    apply beq_oid_equal in H6; subst; auto.
    assert (Some (Heap_OBJ cls F lo' ll) =
          lookup_heap_obj (update_heap_obj h0 o (Heap_OBJ cls F lo' ll)) o).
    apply lookup_updated with h0 ((Heap_OBJ cls F lo ll)); auto.
    exists F. exists lo'. exists ll. 
    rewrite H5 in H; inversion H; subst; auto. 

    assert (Some  (Heap_OBJ cls_def0 F0 lo0 ll0) =
          lookup_heap_obj (update_heap_obj h0 o (Heap_OBJ cls F lo' ll)) o0).
    apply lookup_updated_not_affected with o (Heap_OBJ cls F lo' ll) h0; auto.
    intro contra; subst; auto.
    assert (beq_oid o o = true).
    apply beq_oid_same. try(inconsist); auto. 
    exists F0. exists lo0.  exists ll0. auto. 

    ++
      apply well_typed_sf; auto.
    intros.
    inversion H16; subst; auto.
    apply H6 in H5; auto.
    destruct H5 as [v]. destruct H3.
    exists v. split; auto.

    apply heap_preserve_typing with h0; auto.
    intros.
    case_eq (beq_oid o0 o); intro.
    apply beq_oid_equal in H14; subst; auto.
    assert (Some (Heap_OBJ cls F lo' ll) =
          lookup_heap_obj (update_heap_obj h0 o (Heap_OBJ cls F lo' ll)) o).
    apply lookup_updated with h0 ((Heap_OBJ cls F lo ll)); auto.
    exists F. exists lo'. exists ll. 
    rewrite H9 in H; inversion H; subst; auto. 

    assert (Some  (Heap_OBJ cls_def F0 lo0 ll0) =
          lookup_heap_obj (update_heap_obj h0 o (Heap_OBJ cls F lo' ll)) o0).
    apply lookup_updated_not_affected with o (Heap_OBJ cls F lo' ll) h0; auto.
    intro contra; subst; auto.
    assert (beq_oid o o = true).
    apply beq_oid_same. try(inconsist).
    exists F0. exists lo0.  exists ll0. auto.

    ++ inversion H13; subst; auto.
       destruct H20 as [F0].
       destruct H3 as [lo0].
       destruct H3 as [ll0].
       rewrite H3 in H; inversion H; subst; auto.
       apply change_obj_label_preserve_typed_fs with lo0 clsT field_defs
                                                     method_defs ll0; auto.
       inversion H_valid_config; subst; auto.
       destruct H19 as [field_defs'].
       destruct H5 as [method_defs'].
       subst; auto.
       rewrite H2 in H9; inversion H9; subst; auto.
  +
    inversion H13; subst; auto.
    destruct H20 as [F0].
    destruct H3 as [lo0].
    destruct H3 as [ll0].
    rewrite H3 in H; inversion H; subst; auto.
    apply change_obj_label_preserve_typed_ctns with lo0 clsT field_defs
                                                  method_defs ll0; auto.
    inversion H_valid_config; subst; auto. 
    destruct H19 as [field_defs'].
    destruct H5 as [method_defs'].
    subst; auto.
    rewrite H2 in H9; inversion H9; subst; auto.


(* (Config ct (Container (ObjId o) fs (join_label lb ell) sf) ctns' *)
-  (*(Container (raiseLabel (ObjId o) lo') fs lb sf)*)
  inversion H_typing; subst; auto.
  match goal with
    | H : ctn_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
  end.
  match goal with
    | H : tm_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
  end.
  inversion H13; subst; auto.
  destruct H19 as [F0].
  destruct H2 as [lo0].
  destruct H2 as [ll0].
  rewrite H2 in H; inversion H; subst; auto.
  destruct H15 as [cls_def'].
  destruct H3 as [field_defs].
  destruct H3 as [method_defs].
  destruct H3.
  rewrite H3 in H5; inversion H5; subst; auto.
  apply T_config_ctns with T0 (classTy clsT) Gamma'; auto.
  + apply T_ctn_type; auto.
    ++
      apply heap_preserve_typing with h0; auto.
      intros.
      case_eq (beq_oid o0 o); intro.
      +++ 
      apply beq_oid_equal in H9; subst; auto.
      rewrite H6 in H2; inversion H2; subst; auto. 
      remember (class_def clsT field_defs method_defs)  as cls. 
      assert (Some (Heap_OBJ cls F0 lo' ll0) =
          lookup_heap_obj (update_heap_obj h0 o (Heap_OBJ cls F0 lo' ll0)) o).
      apply lookup_updated with h0 ((Heap_OBJ cls F0 lo0 ll0)); auto.
      exists F0. exists lo'. exists ll0. auto.

      +++
        remember (class_def clsT field_defs method_defs)  as cls. 
        assert (Some  (Heap_OBJ cls_def F lo ll) =
          lookup_heap_obj (update_heap_obj h0 o (Heap_OBJ cls F0 lo' ll0)) o0).
        apply lookup_updated_not_affected with o (Heap_OBJ cls F0 lo' ll0) h0; auto.
        intro contra; subst; auto.
        assert (beq_oid o o = true).
        apply beq_oid_same. try(inconsist); auto. 
        exists F. exists lo.  exists ll. auto. 

    ++
      apply well_typed_sf; auto.
      intros.
      inversion H16; subst; auto.
      apply H9 in H6; auto.
      destruct H6 as [v]. destruct H6.
      exists v. split; auto.

      apply heap_preserve_typing with h0; auto.
      intros.
      case_eq (beq_oid o0 o); intro.
      +++ 
      apply beq_oid_equal in H19; subst; auto.
      rewrite H15 in H2; inversion H2; subst; auto. 
      remember (class_def clsT field_defs method_defs)  as cls. 
      assert (Some (Heap_OBJ cls F0 lo' ll0) =
          lookup_heap_obj (update_heap_obj h0 o (Heap_OBJ cls F0 lo' ll0)) o).
      apply lookup_updated with h0 ((Heap_OBJ cls F0 lo0 ll0)); auto.
      exists F0. exists lo'. exists ll0. auto.
      +++
        remember (class_def clsT field_defs method_defs)  as cls. 
        assert (Some  (Heap_OBJ cls_def F lo ll) =
          lookup_heap_obj (update_heap_obj h0 o (Heap_OBJ cls F0 lo' ll0)) o0).
        apply lookup_updated_not_affected with o (Heap_OBJ cls F0 lo' ll0) h0; auto.
        intro contra; subst; auto.
        assert (beq_oid o o = true).
        apply beq_oid_same. try(inconsist); auto. 
        exists F. exists lo.  exists ll. auto. 

    ++ apply change_obj_label_preserve_typed_fs with lo0 clsT field_defs
                                                     method_defs ll0; auto.
       inversion H_valid_config; subst; auto.
  +
    inversion H13; subst; auto.
    destruct H22 as [F1].
    destruct H6 as [lo1].
    destruct H6 as [ll1].
    rewrite H6 in H2; inversion H2; subst; auto.
    apply change_obj_label_preserve_typed_ctns with lo0 clsT field_defs
                                                  method_defs ll0; auto.
    inversion H_valid_config; subst; auto. 


- (* (Config ct (Container (ObjId o) fs lb sf) ctns' (update_heap_obj h0 o (Heap_OBJ cls F lo' ll)) *)
  inversion H_typing; subst; auto.
  match goal with
    | H : ctn_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
  end.
  match goal with
    | H : tm_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
  end.
  inversion H13; subst; auto.
  inversion H6; subst; auto. 
  destruct H23 as [F0].
  destruct H2 as [lo0].
  destruct H2 as [ll0].
  rewrite H2 in H; inversion H; subst; auto.
  destruct H15 as [cls_def'].
  destruct H3 as [field_defs].
  destruct H3 as [method_defs].
  destruct H3.
  rewrite H3 in H9; inversion H9; subst; auto.
  apply T_config_ctns with T0 (classTy clsT) Gamma'; auto.
  + apply T_ctn_type; auto.
    ++
      apply heap_preserve_typing with h0; auto.
      intros.
      case_eq (beq_oid o0 o); intro.
      +++ 
      apply beq_oid_equal in H15; subst; auto.
      rewrite H14 in H2; inversion H2; subst; auto. 
      remember (class_def clsT field_defs method_defs)  as cls. 
      assert (Some (Heap_OBJ cls F0 lo' ll0) =
          lookup_heap_obj (update_heap_obj h0 o (Heap_OBJ cls F0 lo' ll0)) o).
      apply lookup_updated with h0 ((Heap_OBJ cls F0 lo0 ll0)); auto.
      exists F0. exists lo'. exists ll0. auto.

      +++
        remember (class_def clsT field_defs method_defs)  as cls. 
        assert (Some  (Heap_OBJ cls_def F lo ll) =
          lookup_heap_obj (update_heap_obj h0 o (Heap_OBJ cls F0 lo' ll0)) o0).
        apply lookup_updated_not_affected with o (Heap_OBJ cls F0 lo' ll0) h0; auto.
        intro contra; subst; auto.
        assert (beq_oid o o = true).
        apply beq_oid_same. try(inconsist); auto. 
        exists F. exists lo.  exists ll. auto. 

    ++
      apply well_typed_sf; auto.
      intros.
      inversion H16; subst; auto.
      apply H15 in H14; auto.
      destruct H14 as [v]. destruct H14.
      exists v. split; auto.

      apply heap_preserve_typing with h0; auto.
      intros.
      case_eq (beq_oid o0 o); intro.
      +++ 
      apply beq_oid_equal in H23; subst; auto.
      rewrite H20 in H2; inversion H2; subst; auto. 
      remember (class_def clsT field_defs method_defs)  as cls. 
      assert (Some (Heap_OBJ cls F0 lo' ll0) =
          lookup_heap_obj (update_heap_obj h0 o (Heap_OBJ cls F0 lo' ll0)) o).
      apply lookup_updated with h0 ((Heap_OBJ cls F0 lo0 ll0)); auto.
      exists F0. exists lo'. exists ll0. auto.
      +++
        remember (class_def clsT field_defs method_defs)  as cls. 
        assert (Some  (Heap_OBJ cls_def F lo ll) =
          lookup_heap_obj (update_heap_obj h0 o (Heap_OBJ cls F0 lo' ll0)) o0).
        apply lookup_updated_not_affected with o (Heap_OBJ cls F0 lo' ll0) h0; auto.
        intro contra; subst; auto.
        assert (beq_oid o o = true).
        apply beq_oid_same. try(inconsist); auto. 
        exists F. exists lo.  exists ll. auto. 

    ++ apply change_obj_label_preserve_typed_fs with lo0 clsT field_defs
                                                     method_defs ll0; auto.
       inversion H_valid_config; subst; auto.
  +
    inversion H6; subst; auto.
    destruct H26 as [F1].
    destruct H14 as [lo1].
    destruct H14 as [ll1].
    rewrite H14 in H2; inversion H2; subst; auto.
    apply change_obj_label_preserve_typed_ctns with lo0 clsT field_defs
                                                  method_defs ll0; auto.
    inversion H_valid_config; subst; auto. 


- (* (Config ct (Container (ObjId o) fs lb sf) ctns' (update_heap_obj h0 o (Heap_OBJ cls F lo' ll)) *)
  inversion H_typing; subst; auto.
  match goal with
    | H : ctn_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
  end.
  match goal with
    | H : tm_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
  end.
  inversion H13; subst; auto.
  inversion H6; subst; auto. 
  destruct H23 as [F0].
  destruct H2 as [lo0].
  destruct H2 as [ll0].
  rewrite H2 in H; inversion H; subst; auto.
  destruct H15 as [cls_def'].
  destruct H3 as [field_defs].
  destruct H3 as [method_defs].
  destruct H3.
  rewrite H3 in H9; inversion H9; subst; auto.
  apply T_config_ctns with T0 (classTy clsT) Gamma'; auto.
  + apply T_ctn_type; auto.
    ++
      apply heap_preserve_typing with h0; auto.
      intros.
      case_eq (beq_oid o0 o); intro.
      +++ 
      apply beq_oid_equal in H15; subst; auto.
      rewrite H14 in H2; inversion H2; subst; auto. 
      remember (class_def clsT field_defs method_defs)  as cls. 
      assert (Some (Heap_OBJ cls F0 lo' ll0) =
          lookup_heap_obj (update_heap_obj h0 o (Heap_OBJ cls F0 lo' ll0)) o).
      apply lookup_updated with h0 ((Heap_OBJ cls F0 lo0 ll0)); auto.
      exists F0. exists lo'. exists ll0. auto.

      +++
        remember (class_def clsT field_defs method_defs)  as cls. 
        assert (Some  (Heap_OBJ cls_def F lo ll) =
          lookup_heap_obj (update_heap_obj h0 o (Heap_OBJ cls F0 lo' ll0)) o0).
        apply lookup_updated_not_affected with o (Heap_OBJ cls F0 lo' ll0) h0; auto.
        intro contra; subst; auto.
        assert (beq_oid o o = true).
        apply beq_oid_same. try(inconsist); auto. 
        exists F. exists lo.  exists ll. auto. 

    ++
      apply well_typed_sf; auto.
      intros.
      inversion H16; subst; auto.
      apply H15 in H14; auto.
      destruct H14 as [v]. destruct H14.
      exists v. split; auto.

      apply heap_preserve_typing with h0; auto.
      intros.
      case_eq (beq_oid o0 o); intro.
      +++ 
      apply beq_oid_equal in H23; subst; auto.
      rewrite H20 in H2; inversion H2; subst; auto. 
      remember (class_def clsT field_defs method_defs)  as cls. 
      assert (Some (Heap_OBJ cls F0 lo' ll0) =
          lookup_heap_obj (update_heap_obj h0 o (Heap_OBJ cls F0 lo' ll0)) o).
      apply lookup_updated with h0 ((Heap_OBJ cls F0 lo0 ll0)); auto.
      exists F0. exists lo'. exists ll0. auto.
      +++
        remember (class_def clsT field_defs method_defs)  as cls. 
        assert (Some  (Heap_OBJ cls_def F lo ll) =
          lookup_heap_obj (update_heap_obj h0 o (Heap_OBJ cls F0 lo' ll0)) o0).
        apply lookup_updated_not_affected with o (Heap_OBJ cls F0 lo' ll0) h0; auto.
        intro contra; subst; auto.
        assert (beq_oid o o = true).
        apply beq_oid_same. try(inconsist); auto. 
        exists F. exists lo.  exists ll. auto. 

    ++ apply change_obj_label_preserve_typed_fs with lo0 clsT field_defs
                                                     method_defs ll0; auto.
       inversion H_valid_config; subst; auto.
  +
    inversion H6; subst; auto.
    destruct H26 as [F1].
    destruct H14 as [lo1].
    destruct H14 as [ll1].
    rewrite H14 in H2; inversion H2; subst; auto.
    apply change_obj_label_preserve_typed_ctns with lo0 clsT field_defs
                                                  method_defs ll0; auto.
    inversion H_valid_config; subst; auto. 
    
(* tolabeled context rule*)
-  inversion H_typing; subst; auto.
   match goal with
    | H : ctn_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
   end.
   match goal with
    | H : tm_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
   end.
   apply T_config_ctns with T0 LabelTy Gamma'; auto.
   apply T_ctn_type ; auto.
   apply T_fs_hole with  (LabelelTy T2) ; auto.
   unfold hole_free; fold hole_free;
   case_eq (hole_free e1); intro; auto. 

- inversion H_typing; subst; auto.
   match goal with
    | H : ctn_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
   end.
  match goal with
    | H : fs_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
  end.
  match goal with
    | H : tm_hole_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
  end.
  eauto using T_config_ctns. 

- (* (Config ct (Container e1 (labelData hole (l lo) :: nil) lb sf)
      (Container (toLabeled e1 (l lo)) fs lb sf :: ctns0) h') T  *)
  inversion H_typing; subst; auto.
   match goal with
    | H : ctn_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
   end.
   match goal with
    | H : tm_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
   end.
   apply T_config_ctns with (LabelelTy T2) T2 Gamma'; auto.
   apply T_ctn_type ; auto.
   apply T_fs_hole with  (LabelelTy T2) ; auto.
   eauto using T_ctn_list. 
    
  (*toLabeled e1 v *)
  - inversion H_typing; subst; auto.
    match goal with
    | H : ctn_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
   end.
    match goal with
    | H : tm_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
    end.
    inversion H7; subst; auto. 
    eauto using T_config_ctns.
  
  - (*  getCurrentLevel  *)
    inversion H_typing; subst; auto.
    match goal with
    | H : ctn_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
   end.
    match goal with
    | H : tm_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
    end.
    eauto using T_config_ctns.

(* assignment context rules*)
  - inversion H_typing; subst; auto.
   match goal with
    | H : ctn_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
   end.
   match goal with
    | H : tm_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
   end.
   eauto using T_config_ctns. 

- inversion H_typing; subst; auto.
   match goal with
    | H : ctn_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
   end.
  match goal with
    | H : fs_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
  end.
  match goal with
    | H : tm_hole_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
  end.
  eauto using T_config_ctns.        

(*(Assignment id0 t)*)
- inversion H_typing; subst; auto.
  match goal with
    | H : ctn_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
   end.
   match goal with
    | H : tm_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
   end.
   apply T_config_ctns with T0 T1 Gamma'; auto.
   apply T_ctn_type; auto.
   apply well_typed_sf; auto; intros.
   case_eq (beq_id id x);intro.
   unfold sf_update.
   rewrite H1.
   exists v; split; auto.
   apply beq_equal in H1.
   subst; auto.
   rewrite H0 in H7; inversion H7; subst; auto.
   unfold sf_update. rewrite H1.
   inversion H14; subst; auto.

(* fieldWrite context rules*)

- inversion H_typing; subst; auto.
   match goal with
    | H : ctn_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
   end.
   match goal with
    | H : tm_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
   end.
   eauto using T_config_ctns. 

- inversion H_typing; subst; auto.
   match goal with
    | H : ctn_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
   end.
  match goal with
    | H : fs_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
  end.
  match goal with
    | H : tm_hole_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
  end.
  eauto using T_config_ctns.
  match goal with
    | H : valid_config _ |- _
      => inversion H; subst; auto 
    end.
  match goal with
    | H : valid_ctn _ _ _ |- _
      => inversion H; subst; auto 
  end.
  match goal with
    | H : valid_fs _ |- _
      => inversion H; subst; auto 
  end.
  match goal with
    | H : valid_syntax (FieldWrite hole _ hole) |- _
      => inversion H; subst; auto 
  end;
    try (match goal with
    | H : surface_syntax hole = true |- _
      => inversion H; subst; auto 
         end);
    try (match goal with
    | H : value hole |- _
      => inversion H; subst; auto 
    end).

- inversion H_typing; subst; auto.
   match goal with
    | H : ctn_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
   end.
   match goal with
    | H : tm_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
   end.
   apply T_config_ctns with T0  (classTy cls') Gamma'; auto.
   apply T_ctn_type; auto.
   apply T_fs_hole with (classTy cls'); auto.
   unfold hole_free; fold hole_free; case_eq (hole_free v); intro; auto. 
   eauto using tm_hole_has_type.   

- inversion H_typing; subst; auto.
   match goal with
    | H : ctn_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
   end.
  match goal with
    | H : fs_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
  end.
  match goal with
    | H : tm_hole_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
  end.
  + match goal with
    | H : valid_config _ |- _
      => inversion H; subst; auto 
    end.
  match goal with
    | H : valid_ctn _ _ _ |- _
      => inversion H; subst; auto 
  end.
  match goal with
    | H : valid_fs _ |- _
      => inversion H; subst; auto 
  end.
  match goal with
    | H : valid_syntax (FieldWrite hole _ hole) |- _
      => inversion H; subst; auto 
  end;
    try (match goal with
    | H : surface_syntax hole = true |- _
      => inversion H; subst; auto 
         end);
    try (match goal with
    | H : value hole |- _
      => inversion H; subst; auto 
    end).
  + eauto using T_config_ctns.

(* field write normal*)
  -
    inversion H_typing; subst; auto.
    match goal with
    | H : ctn_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
   end.
   match goal with
    | H : tm_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
   end.
    inversion H5; subst; auto.
    destruct H20 as [F0].
    destruct H0 as [lo0].
    destruct H15 as [field_defs0].
    destruct H2 as [method_defs0].
    destruct H0 as [ll0].
    
    rewrite H0 in H; inversion H; subst; auto.
    inversion H_valid_config; subst; auto.

    apply T_config_ctns with T0 (classTy cls') Gamma'; auto.   
    apply T_ctn_type; auto.
    apply field_write_preserve_typed_tm with F0 lo0 clsT field_defs0
                                             method_defs0 ll0; auto.
    eauto using field_write_preserve_typed_tm.
    eauto using field_write_preserve_typed_sf.
    eauto using field_write_preserve_typed_fs.

(* field write opaque *)
  -
    inversion H_typing; subst; auto.
    match goal with
    | H : ctn_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
   end.
   match goal with
    | H : tm_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
   end.
   inversion H5; subst; auto.
   inversion H6; subst; auto. 
   destruct H24 as [F0].
   destruct H0 as [lo0].
   destruct H23 as [field_defs0].
   destruct H2 as [method_defs0].
   destruct H0 as [ll0].
    
   rewrite H0 in H; inversion H; subst; auto.
   inversion H_valid_config; subst; auto.

    apply T_config_ctns with T0 (classTy cls') Gamma'; auto.   
    apply T_ctn_type; auto.
    apply field_write_preserve_typed_tm with F0 lo0 clsT field_defs0
                                             method_defs0 ll0; auto.
    eauto using field_write_preserve_typed_sf.
    eauto using field_write_preserve_typed_fs.
    eauto using field_write_preserve_typed_ctns. 
    
  (* if context rules*)
 - inversion H_typing; subst; auto.
   match goal with
    | H : ctn_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
   end.
   match goal with
    | H : tm_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
   end.
   eauto using T_config_ctns. 

- inversion H_typing; subst; auto.
   match goal with
    | H : ctn_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
   end.
  match goal with
    | H : fs_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
  end.
  match goal with
    | H : tm_hole_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
  end.
  eauto using T_config_ctns.        


(* (Container (If guard s1 s2) fs (join_label lb ell) sf) *)
- inversion H_typing; subst; auto.
  match goal with
    | H : ctn_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
   end.
   match goal with
    | H : tm_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
   end.
   inversion H11; subst; auto.
   eauto using T_config_ctns. 
  
- (*   B_true   *)
  inversion H_typing; subst; auto.
  match goal with
    | H : ctn_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
   end.
   match goal with
    | H : tm_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
   end.
    eauto using T_config_ctns. 

- (*   B_false   *)
  inversion H_typing; subst; auto.
  match goal with
    | H : ctn_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
   end.
   match goal with
    | H : tm_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
   end.
    eauto using T_config_ctns. 

(*sequence context rules *)       
- inversion H_typing; subst; auto.
    inversion H_typing; subst; auto.
  match goal with
    | H : ctn_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
   end.
   match goal with
    | H : tm_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
   end.
   eauto using T_config_ctns.

   
- inversion H_typing; subst; auto.
  match goal with
    | H : ctn_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
  end.
  match goal with
    | H : fs_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
  end.
  match goal with
    | H : tm_hole_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
  end.
  eauto using T_config_ctns.        

 - inversion H_typing; subst; auto.
  match goal with
    | H : ctn_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
  end.
  match goal with
    | H : tm_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
   end.
  eauto using T_config_ctns.


(* config_has_type ct empty_context (Config ct (Container (v_opa_l v lb) fs' lb' sf') ctns' h') T *)
 - inversion H_typing; subst; auto.
   match goal with
    | H : ctn_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
   end.
   match goal with
    | H : fs_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
   end.
   inversion H9; subst; auto.
   inversion H12; subst; auto.
   
   apply T_config_ctns with T2 T0  Gamma'0; auto.
   apply T_ctn_type; auto.
   assert (tm_has_type ct Gamma'0 h' v T0).
   apply value_typing_invariant_gamma with Gamma';auto.   
   inversion H1; subst; auto;
   apply T_v_opa_l ; auto;
     try (eauto using T_v_opa_l;
          intros; intro contra; inversion contra; auto).
   destruct H0 with v0 lb0; auto. 
      
(* (Config ct (Container (v_opa_l v (join_label ell lb)) fs' lb' sf') ctns' h') *)
 - inversion H_typing; subst; auto.
    match goal with
    | H : ctn_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
    end.
    match goal with
    | H : fs_has_type _ _ _ _ _ |- _
      => inversion H; subst; auto 
   end.
    inversion H7; subst; auto.
    inversion H10; subst; auto.
    inversion H9; subst; auto. 
    apply T_config_ctns with T2 T0  Gamma'0; auto.
    apply T_ctn_type; auto.
    assert (tm_has_type ct Gamma'0 h' v T0).
   apply value_typing_invariant_gamma with Gamma';auto.   
   inversion H; subst; auto;
   apply T_v_opa_l ; auto;
     try (eauto using T_v_opa_l;
          intros; intro contra; inversion contra; auto).
Qed. 
Hint Resolve typing_preservation. 



    





  