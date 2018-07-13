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
Require Import simulation_full.


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

      intros. inversion H; subst; auto.
      apply stack_val_opa_labeled; auto.
      apply IHvalue with T0; auto.
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

(*
Lemma expand_heap_preserve_valid_ctns_wfe : forall ctns ho h ct,
         wfe_heap ct h ->
         wfe_ctn_list ct h ctns ->
         wfe_ctn_list ct (add_heap_obj h (get_fresh_oid h) ho) ctns.
Proof with eauto.
        intros.
        
        induction ctns; auto.
        apply wfe_ctns_nil; auto.
        inversion H0; subst; auto. 
        apply wfe_ctns_list with  t fs lb sf ctns'; auto.
        inversion H1; subst; auto.
Qed. Hint Resolve expand_heap_preserve_valid_ctns_wfe.
  *)  
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


  - inversion H18; subst; auto.
    apply valid_conf; auto.
    apply valid_container; auto.
    apply valid_fs_list; auto.
    intro contra. inversion contra. 
    intro contra. inversion contra.
    inversion H9; subst; auto.
    intros. intro contra.
    inversion contra.
    intros. intro contra.
    inversion contra.
    inversion H19.
    apply hole_free_if in H3.
    destruct H3. rewrite H2.  auto.

  - inversion H20; subst; auto.
    apply config_typing_lead_to_tm_typing in H_typing.
    destruct H_typing as [T'].
    destruct H3 as [gamma].
    inversion H3; subst; auto.
    inversion H8; subst; auto.
    destruct H26 as [F0].
    destruct H4 as [lo0].
    rewrite H4 in H; inversion H; subst; auto.
    rewrite <- H6 in H15. inversion H15; subst; auto.
    rewrite H16 in H0; inversion H0; subst; auto.
    apply valid_conf; auto.
    apply valid_container; auto.
    intros. intro contra. inversion contra.
    intros. intro contra. inversion contra.
    apply stack_frame_wfe; auto.
    intros.
    case_eq (beq_id arg_id0 x);intro.
    unfold sf_update in H5. rewrite H18 in H5.
    inversion H5; subst; auto.
    split; auto.
    induction H1; inversion H11; subst; auto.
    destruct H32 as [F'].
    destruct H1 as [lo'].
    destruct H31 as [field_defs].
    destruct H19 as [method_defs].
    subst; auto. 
    apply stack_val_object with arguT F' lo'
                                field_defs method_defs; auto.
    unfold sf_update in H5. rewrite H18 in H5.
    inversion H5.

  - inversion H21; subst; auto.
    apply config_typing_lead_to_tm_typing in H_typing.
    destruct H_typing as [T'].
    destruct H0 as [gamma].
    inversion H0; subst; auto.
    inversion H8; subst; auto.
    destruct H26 as [F0].
    destruct H1 as [lo0].
    rewrite H1 in H; inversion H; subst; auto.
    rewrite <- H6 in H15; inversion H15; subst; auto.
    rewrite H16 in H4; inversion H4; subst; auto.
    apply valid_conf; auto.
    apply valid_container; auto.
    intros. intro contra. inversion contra.
    intros. intro contra. inversion contra.
    apply stack_frame_wfe; auto.
    intros.
    case_eq (beq_id arg_id0 x);intro.
    unfold sf_update in H5. rewrite H17 in H5.
    inversion H5; subst; auto.
    split; auto.
    inversion H11; subst; auto.
    inversion H30; subst; auto.
    induction H35; inversion H34; subst; auto. 
    destruct H36 as [F'].
    destruct H19 as [lo'].
    destruct H35 as [field_defs].
    destruct H20 as [method_defs].
    subst; auto. 
    apply stack_val_object with arguT F' lo'
                                field_defs method_defs; auto.
    unfold sf_update in H5. rewrite H17 in H5.
    inversion H5.
    
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
    rewrite H3; auto.  rewrite H2; auto.

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

apply valid_conf; auto.
destruct H18 as [field_defs].
destruct H4 as [method_defs].
apply field_write_preserve_wfe_heap with o h0 f F' (fields_update F' f v)
                                              cls_def cls' lo' lo' clsT
                                              field_defs method_defs; auto. 



     
     apply valid_container; auto.
     intro. intro contra.

     
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
     
   -  match goal with
    | H : valid_ctn _ _ _ |- _
      => inversion H; subst; auto 
      end.
      inversion H4; subst; auto.
      
      inversion H_typing; subst; auto.
      inversion H21; subst; auto.
      inversion H26; subst; auto.
      inversion H22. inversion H23. inversion H27.

      induction H; subst; auto; inversion H24.
      subst; auto.
      apply valid_conf; auto.
      apply valid_container; auto.
      inversion H2; subst; auto.
      intro. intro contra.
      rewrite contra in H3; inversion H3; subst; auto.
      intro. intro contra.
      rewrite contra in H3; inversion H3; subst; auto.
      inversion H2; subst; auto. inversion H12. 
      unfold hole_free. fold hole_free.
      apply surface_syntax_is_hole_free in H1.
      apply surface_syntax_is_hole_free in H12.
      rewrite H1. rewrite H12. auto.

      subst; auto.
      apply valid_conf; auto.
      apply valid_container; auto.
      inversion H2; subst; auto.
      intro. intro contra.
      rewrite contra in H3; inversion H3; subst; auto.
      inversion H2; subst; auto. inversion H12.
      intro. intro contra.
      rewrite contra in H3; inversion H3; subst; auto.
      unfold hole_free. fold hole_free.
      inversion H2; subst; auto.
      inversion H12. 
      apply surface_syntax_is_hole_free in H1.
      apply surface_syntax_is_hole_free in H12.
      rewrite H1. rewrite H12. auto.

      subst; auto. 
      apply valid_conf; auto.
      apply valid_container; auto.
      inversion H2; subst; auto.
      intro. intro contra.
      rewrite contra in H3; inversion H3; subst; auto.
      inversion H2; subst; auto. inversion H12.
      intro. intro contra.
      rewrite contra in H3; inversion H3; subst; auto.
      unfold hole_free. fold hole_free.
      inversion H2; subst; auto.
      inversion H12. 
      apply surface_syntax_is_hole_free in H1.
      apply surface_syntax_is_hole_free in H12.
      rewrite H1. rewrite H12. auto.      
      
      inversion H25. subst; auto. inversion H23.
      inversion H20. 
      subst; auto.
      inversion H28; subst; auto.
      inversion H24.   inversion H25.
      inversion H29. 

      apply valid_conf; auto.
      apply valid_container; auto.
      inversion H2; subst; auto.
      inversion H14. 

      induction H; subst; auto; inversion H26.
      intro. intro contra.
      rewrite contra in H3; inversion H3; subst; auto.
      intro. intro contra.
      rewrite contra in H3; inversion H3; subst; auto.
      inversion H2; subst; auto. inversion H14. 
      unfold hole_free. fold hole_free.
      apply surface_syntax_is_hole_free in H12.
      apply surface_syntax_is_hole_free in H14.
      rewrite H14. rewrite H12. auto. rewrite H17. auto. 

      subst; auto.
      apply valid_conf; auto.
      apply valid_container; auto.
      inversion H27; subst; auto.
      inversion H25.
      inversion H27; subst; auto.  inversion H25.
      inversion H27; subst; auto. inversion H25.
      inversion H27; subst; auto. inversion H25. 


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
       inversion H_typing;subst; auto.
       inversion H11; subst; auto.
       inversion H19; subst; auto.
       inversion H20; subst; auto.

       inversion H7; subst; auto.
       inversion H21; subst; auto.
       inversion H22; subst; auto. 

   -   match goal with
    | H : valid_ctn _ _ _ |- _
      => inversion H; subst; auto 
       end.
       inversion H13; subst; auto.
       inversion H3; subst; auto.
Qed. Hint Resolve 
       
       


       
       intro. intro contra.
       inversion H3; subst; auto.
       inversion H12; subst; auto.

       intro. intro contra.
      
       inversion H3; subst; auto.
       inversion H12; subst; auto. 
       
       rewrite contra in H2; inversion H2;
         subst; auto.
       intro. intro contra.
       rewrite contra in H2; inversion H2;
         subst; auto.
       inversion H_typing;subst; auto.
       inversion H11; subst; auto.
       inversion H20; subst; auto.
       inversion H21; subst; auto.

       inversion H7; subst; auto.
       inversion H22; subst; auto.
       inversion H23; subst; auto. 

       
       
       


       
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
          






     







    
Hint Resolve valid_config_preservation.

Lemma typing_preservation : forall T ct
                                   ctn ctns h
                                   ctn' ctns' h',
    config_has_type ct empty_context (Config ct ctn ctns h) T ->
    valid_config (Config ct  ctn ctns h) ->
    Config ct ctn ctns h
           ==> Config ct ctn' ctns' h' ->
    config_has_type ct empty_context (Config ct ctn' ctns' h') T.
Proof with eauto.
Admitted.
Hint Resolve typing_preservation.

