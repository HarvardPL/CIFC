Require Import Coq.Lists.List.
Require Import Language Types.
Require Import preservation. 
Require Import Lemmas. 


 Ltac solve_by_invert_non_value :=
   match goal with
   | H : ?T |- _ =>
     match T with
     | value _  => solve [inversion H; subst]
     end end.

 Ltac solve_by_FT :=
   match goal with
   | H : false = true |- _ =>
     inversion H
   end.

 Ltac solve_by_hole_free :=
   match goal with
    | H :  hole_free  _ = true |- _
      => inversion H; subst; auto                                                                                                                           end.

(*
    match goal with
    | H :  hole_free  _ = true |- _
      => inversion H; subst; auto                                                                                                                           end.
    match goal with
    | H : (if hole_free ?T then false else false) = true |- _
      => case_eq (hole_free T); intro Hy; rewrite Hy in H; try (solve_by_FT)
    end. 

*)
 

Theorem deterministic: forall ct ctn ctns h
                              ctn1 ctns1 h1
                              ctn2 ctns2 h2, 
     Config ct ctn ctns h ==>
            (Config ct ctn1 ctns1 h1)  ->
     Config ct ctn ctns h ==>
           (Config ct ctn2 ctns2 h2) ->
     ctn1 = ctn2 /\ ctns1 = ctns2 /\ h1 = h2 .
Proof with eauto.
  intros ct ctn ctns h ctn1 ctns1 h1 ctn2 ctns2 h2. intro Hy1. intro Hy2.
  remember (Config ct ctn1 ctns1 h1) as t1_config.
  generalize dependent ctn1.      generalize dependent ctn2.
  generalize dependent ctns1.      generalize dependent ctns2.
  generalize dependent h1.      generalize dependent h2.

  
  induction Hy1; intros; inversion Heqt1_config; subst; auto;
    try (inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition); subst; auto;
         try (assert (value (ObjId o)); auto; contradiction);
         try (match goal with
              | H :  hole_free  _ = true |- _
                => inversion H; subst; auto                                                                                                                           end);
         fail).
 
  
  - inversion Hy2; subst; auto; try (solve_by_invert_non_value).
    rewrite <- H in H1; inversion H1; subst; auto.
  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition).

    match goal with
    | H :  hole_free  _ = true |- _
      => inversion H; subst; auto                                                                                                                           end.
     match goal with
    | H : (if hole_free ?T then false else false) = true |- _
      => case_eq (hole_free T); intro Hy; rewrite Hy in H; try (solve_by_FT)
    end. 

  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition); subst; auto;
    try (assert (result = B_true);  auto;
         assert (result0 = B_true);  auto; subst; auto; fail
        ).
    destruct H3. destruct H3.  destruct H3.  destruct H3. destruct H3; subst; intuition.
    assert (result = B_false). apply H2. intro Hy; inversion Hy.
    assert (result0 = B_false). apply H19. intro Hy; inversion Hy.
    subst; auto. 

    destruct H3. destruct H3.  destruct H3.  destruct H3. destruct H3; subst; intuition.
    assert (result = B_false). apply H2. intro Hy; inversion Hy.
    assert (result0 = B_false). apply H19. intro Hy; inversion Hy.
    subst; auto. 

    destruct H5. destruct H3.  destruct H3.  destruct H3. destruct H3; subst; intuition.
    assert (result = B_false). apply H2. intro Hy; inversion Hy.
    assert (result0 = B_false). apply H19. intro Hy; inversion Hy.
    subst; auto.

    destruct H5. destruct H3.  destruct H3.  destruct H3. destruct H3; subst; intuition.
    assert (result = B_false). apply H2. intro Hy; inversion Hy.
    assert (result0 = B_false). apply H19. intro Hy; inversion Hy.
    subst; auto.
    
    destruct H3. destruct H3.  destruct H3.  destruct H3. destruct H3; subst; intuition.
    assert (result = B_false). apply H2. intro Hy; inversion Hy.
    assert (result0 = B_false). apply H19. intro Hy; inversion Hy.
    subst; auto. 

    destruct H3. destruct H3.  destruct H3.  destruct H3. destruct H3; subst; intuition.
    inversion H3.

    pose proof (exclude_middle_val_eq v1 v2 H H0).
    destruct H7; subst; auto. 
    assert (result = B_true); auto.
    assert (result0 = B_true); auto.
    subst; auto.
    assert (result = B_false); auto.
    assert (result0 = B_false); auto.
    subst; auto.

  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition); subst; auto. assert (value (ObjId o)). auto. contradiction. 
    
    rewrite <- H in H4; inversion H4; subst; auto.
    rewrite <- H13 in H0; inversion H0; subst; auto.

  -
    inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition); subst; auto.
    match goal with
    | H :  hole_free  _ = true |- _
      => inversion H; subst; auto                                                                                                                           end.
     match goal with
    | H : (if hole_free ?T then false else false) = true |- _
      => case_eq (hole_free T); intro Hy; rewrite Hy in H; try (solve_by_FT)
    end. 
    
  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    destruct H with e0; auto.
    destruct H with (v_opa_l v0 lx); auto.

  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    destruct H6 with e2; auto.
    assert (value (v_opa_l v lx)). auto. intuition.     

  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
        match goal with
    | H :  hole_free  _ = true |- _
      => inversion H; subst; auto                                                                                                                           end.
     match goal with
    | H : (if hole_free ?T then false else false) = true |- _
      => case_eq (hole_free T); intro Hy; rewrite Hy in H; try (solve_by_FT)
    end. 

  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    assert (value (ObjId o)). auto. intuition.
    rewrite <- H8 in H; inversion H; subst; auto.
    rewrite <- H16 in H0; inversion H0; subst; auto.

  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    assert (value (ObjId o)). auto. intuition.

    destruct H7 with (v_opa_l v lx); auto.
    assert (value (v_opa_l v lx)). auto. intuition.     

    rewrite <- H9 in H; inversion H; subst; auto.
    rewrite <- H21 in H4; inversion H4; subst; auto.

  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    split; auto. split; auto.
    rewrite H5 in H; inversion H; subst; auto.

  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    assert (value (v_l v lo)). auto. intuition.

  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    assert (value (v_l v lo)). auto. intuition.

  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    assert (value (v_l v lo)). auto. intuition.


  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    assert (value (v_l v lo)). auto. intuition.

  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    assert (value (v_opa_l v lo)). auto. intuition.

  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    assert (value (v_opa_l v lo)). auto. intuition.

    
  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    assert (value (ObjId o)). auto. intuition.
    rewrite <- H in H6; inversion H6; subst; auto. 

  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    destruct H with e0; auto.
    destruct H19; subst; auto.
    assert (value null). auto. intuition. 
    destruct H3. destruct H3. destruct H3. destruct H3. destruct H3. destruct H4; subst; auto.
    assert (value (ObjId x)); auto.
    intuition. 

    destruct H19; subst; auto.
    destruct H with (v_opa_l null lx); auto. 

    destruct H3. destruct H3. destruct H3. destruct H3. destruct H3. destruct H4; subst; auto.
    destruct H with (v_opa_l (ObjId x) lx); auto. 


  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
        match goal with
    | H :  hole_free  _ = true |- _
      => inversion H; subst; auto                                                                                                                           end.
     match goal with
    | H : (if hole_free ?T then false else false) = true |- _
      => case_eq (hole_free T); intro Hy; rewrite Hy in H; try (solve_by_FT)
    end. 
   
    
  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    destruct H6 with e2; auto.
    destruct H18. inversion H2.
    destruct H2. destruct H2.  destruct H2. destruct H2.
    destruct H2. inversion H2. 

    destruct H18; subst; auto.
    assert (value (v_opa_l null lx)); auto.
    intuition. 

    destruct H2. destruct H2.  destruct H2. destruct H2.
    destruct H2. inversion H3; subst; auto. 
    assert ( value (v_opa_l (ObjId x) lx)); auto.
    intuition. 
    

  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
            match goal with
    | H :  hole_free  _ = true |- _
      => inversion H; subst; auto                                                                                                                           end.
     match goal with
    | H : (if hole_free ?T then false else false) = true |- _
      => case_eq (hole_free T); intro Hy; rewrite Hy in H; try (solve_by_FT)
    end. 

  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    assert (value v).
    destruct H3; subst; auto.
    destruct H0. destruct H0. destruct H0. destruct H0. destruct H0.
    subst; auto.
    assert (value (ObjId o)); auto.
    intuition.

    destruct H3. subst; auto. assert (value null); auto. intuition. 
    destruct H0. destruct H0. destruct H0. destruct H0. destruct H0.
    subst; auto.  assert (value (ObjId x)); auto. intuition. 

    destruct H3.  inversion H0.

    destruct H0. destruct H0. destruct H0. destruct H0. destruct H0.
    inversion H0.

    rewrite <- H in H7; inversion H7; subst; auto.
    destruct H3. inversion H0.
    destruct H0. destruct H0. destruct H0. destruct H0. destruct H0.
    inversion H0.


  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    assert (value (ObjId o)); auto.
    intuition.
    destruct H6 with (v_opa_l v lx); auto.

    assert ( value (v_opa_l v lx)); auto.
    destruct H3; subst; auto.

    destruct H0. destruct H0. destruct H0. destruct H0. destruct H0. subst; auto.
    intuition.

    destruct H18. inversion H0.
    destruct H0. destruct H0. 
    destruct H0. destruct H0. destruct H0. inversion H0. 

    rewrite <- H in H7; inversion H7; subst; auto. 


  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    assert (value B_true); auto; intuition. 
    assert (value B_false); auto; intuition. 


  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    assert (value B_true); auto; intuition. 

  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    assert (value B_false); auto; intuition. 
    
  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    try (inversion H0; 
    match goal with
    | H :  hole_free  _ = true |- _
      => inversion H; subst; auto
    end;
    match goal with
    | H : (if hole_free ?T then false else false) = true |- _
      => case_eq (hole_free T); intro Hy; rewrite Hy in H; try (solve_by_FT)
    end).
    inversion H0.
    try (inversion H0; 
    match goal with
    | H :  hole_free  _ = true |- _
      => inversion H; subst; auto
    end;
    match goal with
    | H : (if hole_free ?T then false else false) = true |- _
      => case_eq (hole_free T); intro Hy; rewrite Hy in H; try (solve_by_FT)
    end).
    inversion H0.
        try (inversion H0; 
    match goal with
    | H :  hole_free  _ = true |- _
      => inversion H; subst; auto
    end;
    match goal with
    | H : (if hole_free ?T then false else false) = true |- _
      => case_eq (hole_free T); intro Hy; rewrite Hy in H; try (solve_by_FT)
    end).

    try (inversion H0; 
    match goal with
    | H :  hole_free  _ = true |- _
      => inversion H; subst; auto
    end;
    match goal with
    | H : (if hole_free ?T then false else false) = true |- _
      => case_eq (hole_free T); intro Hy; rewrite Hy in H; try (solve_by_FT)
    end).

    try (inversion H0; 
    match goal with
    | H :  hole_free  _ = true |- _
      => inversion H; subst; auto
    end;
    match goal with
    | H : (if hole_free ?T then false else false) = true |- _
      => case_eq (hole_free T); intro Hy; rewrite Hy in H; try (solve_by_FT)
    end).

    try (inversion H0; 
    match goal with
    | H :  hole_free  _ = true |- _
      => inversion H; subst; auto
    end;
    match goal with
    | H : (if hole_free ?T then false else false) = true |- _
      => case_eq (hole_free T); intro Hy; rewrite Hy in H; try (solve_by_FT)
    end).

    try (inversion H0; 
    match goal with
    | H :  hole_free  _ = true |- _
      => inversion H; subst; auto
    end;
    match goal with
    | H : (if hole_free ?T then false else false) = true |- _
      => case_eq (hole_free T); intro Hy; rewrite Hy in H; try (solve_by_FT)
    end).

    try (inversion H0; 
    match goal with
    | H :  hole_free  _ = true |- _
      => inversion H; subst; auto
    end;
    match goal with
    | H : (if hole_free ?T then false else false) = true |- _
      => case_eq (hole_free T); intro Hy; rewrite Hy in H; try (solve_by_FT)
    end).

    try (inversion H0; 
    match goal with
    | H :  hole_free  _ = true |- _
      => inversion H; subst; auto
    end;
    match goal with
    | H : (if hole_free ?T then false else false) = true |- _
      => case_eq (hole_free T); intro Hy; rewrite Hy in H; try (solve_by_FT)
    end).

    try (inversion H0; 
    match goal with
    | H :  hole_free  _ = true |- _
      => inversion H; subst; auto
    end;
    match goal with
    | H : (if hole_free ?T then false else false) = true |- _
      => case_eq (hole_free T); intro Hy; rewrite Hy in H; try (solve_by_FT)
    end).

    try (inversion H0; 
    match goal with
    | H :  hole_free  _ = true |- _
      => inversion H; subst; auto
    end;
    match goal with
    | H : (if hole_free ?T then false else false) = true |- _
      => case_eq (hole_free T); intro Hy; rewrite Hy in H; try (solve_by_FT)
    end).

    try (inversion H0; 
    match goal with
    | H :  hole_free  _ = true |- _
      => inversion H; subst; auto
    end;
    match goal with
    | H : (if hole_free ?T then false else false) = true |- _
      => case_eq (hole_free T); intro Hy; rewrite Hy in H; try (solve_by_FT)
    end).

    try (inversion H0; 
    match goal with
    | H :  hole_free  _ = true |- _
      => inversion H; subst; auto
    end;
    match goal with
    | H : (if hole_free ?T then false else false) = true |- _
      => case_eq (hole_free T); intro Hy; rewrite Hy in H; try (solve_by_FT)
    end).

    try (inversion H0; 
    match goal with
    | H :  hole_free  _ = true |- _
      => inversion H; subst; auto
    end;
    match goal with
    | H : (if hole_free ?T then false else false) = true |- _
      => case_eq (hole_free T); intro Hy; rewrite Hy in H; try (solve_by_FT)
    end).

    try (inversion H0; 
    match goal with
    | H :  hole_free  _ = true |- _
      => inversion H; subst; auto
    end;
    match goal with
    | H : (if hole_free ?T then false else false) = true |- _
      => case_eq (hole_free T); intro Hy; rewrite Hy in H; try (solve_by_FT)
    end).
Qed. Hint Resolve deterministic.     


Theorem deterministic_prime: forall ct ctn ctns h
                              ctn1 ctns1 h1
                              config', 
     Config ct ctn ctns h ==>
            (Config ct ctn1 ctns1 h1)  ->
     Config ct ctn ctns h ==>config'  ->
     (Config ct ctn1 ctns1 h1) = config'.
Proof with eauto.
  intros ct ctn ctns h ctn1 ctns1 h1 config'. intro Hy1. intro Hy2.
  remember (Config ct ctn1 ctns1 h1) as t1_config.
  generalize dependent ctn1. 
  generalize dependent ctns1.   
  generalize dependent h1.      
  induction Hy1; intros; inversion Heqt1_config; subst; auto;
    try (inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition); subst; auto;
         try (assert (value (ObjId o)); auto; contradiction);
         try (match goal with
              | H :  hole_free  _ = true |- _
                => inversion H; subst; auto                                                                                                                           end);
         fail).
 
  
  - inversion Hy2; subst; auto; try (solve_by_invert_non_value).
    rewrite <- H in H8; inversion H8; subst; auto.

  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition).
    match goal with
    | H :  hole_free  _ = true |- _
      => inversion H; subst; auto                                                                                                                           end.
     match goal with
    | H : (if hole_free ?T then false else false) = true |- _
      => case_eq (hole_free T); intro Hy; rewrite Hy in H; try (solve_by_FT)
    end. 

  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition); subst; auto;
    try (assert (result = B_true);  auto;
         assert (result0 = B_true);  auto; subst; auto; fail
        ).
    destruct H3. destruct H3.  destruct H3.  destruct H3. destruct H3; subst; intuition.
    assert (result = B_false). apply H2. intro Hy; inversion Hy.
    assert (result0 = B_false). apply H17. intro Hy; inversion Hy.
    subst; auto. 

    destruct H3. destruct H3.  destruct H3.  destruct H3. destruct H3; subst; intuition.
    assert (result = B_false). apply H2. intro Hy; inversion Hy.
    assert (result0 = B_false). apply H17. intro Hy; inversion Hy.
    subst; auto. 

    destruct H5. destruct H4.  destruct H4.  destruct H4. destruct H4; subst; intuition.
    assert (result = B_false). apply H2. intro Hy; inversion Hy.
    assert (result0 = B_false). apply H17. intro Hy; inversion Hy.
    subst; auto.

    destruct H3. destruct H3.  destruct H3.  destruct H3. destruct H3; subst; intuition.
    inversion H3.

    destruct H4. destruct H3.  destruct H3.  destruct H3. destruct H3; subst; intuition.
    inversion H3.

    destruct H5. destruct H5.  destruct H5.  destruct H5. destruct H5; subst; intuition.
    inversion H5.

    pose proof (exclude_middle_val_eq v1 v2 H H0).
    destruct H7; subst; auto. 
    assert (result = B_true); auto.
    assert (result0 = B_true); auto.
    subst; auto.
    assert (result = B_false); auto.
    assert (result0 = B_false); auto.
    subst; auto.


    destruct H3. destruct H3.  destruct H3.  destruct H3. destruct H3; subst; intuition.
    inversion H3.
    
    destruct H3. destruct H3.  destruct H3.  destruct H3. destruct H3; subst; intuition.
    inversion H3.

    destruct H3. destruct H3.  destruct H3.  destruct H3. destruct H3; subst; intuition.

    destruct H4. destruct H4.  destruct H4.  destruct H4. destruct H4; subst; intuition.
    inversion H4; subst; auto.
    rewrite <- H3 in H7; inversion H7; subst; auto.
    try (inconsist).
    
    destruct H3. destruct H3.  destruct H3.  destruct H3. destruct H3; subst; intuition.
    inversion H3. 

    destruct H3. destruct H3.  destruct H3.  destruct H3. destruct H3; subst; intuition.
    inversion H3. 

    destruct H3. destruct H3.  destruct H3.  destruct H3. destruct H3; subst; intuition.
    destruct H5. destruct H4.  destruct H4.  destruct H4. destruct H4; subst; intuition.
    inversion H4; subst; auto.
    rewrite <- H3 in H7; inversion H7; subst; auto.
    try (inconsist). 

    pose proof (exclude_middle_val_eq v1 v2 H H0).
    destruct H6; subst; auto.
    destruct H3. destruct H3.  destruct H3.  destruct H3. destruct H3; subst; intuition.
    destruct H5. destruct H1.  destruct H1.  destruct H1. destruct H1; subst; intuition.
    inversion H1; subst; auto.
    rewrite <- H6 in H3; inversion H3; subst; auto. try (inconsist).


    destruct H3. destruct H3.  destruct H3.  destruct H3. destruct H3; subst; intuition.
    destruct H4. destruct H2.  destruct H2.  destruct H2. destruct H2; subst; intuition.
    inversion H2; subst; auto.
    rewrite <- H7 in H3; inversion H3; subst; auto. try (inconsist).

    destruct H3. destruct H3.  destruct H3.  destruct H3. destruct H3; subst; intuition.
    destruct H5. destruct H5.  destruct H5.  destruct H5. destruct H5; subst; intuition.
    inversion H5; subst; auto.
    rewrite <- H8 in H3; inversion H3; subst; auto. try (inconsist).

  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition); subst; auto.
    assert (value (ObjId o)). auto. contradiction.

    assert (value null); auto. contradiction.
    
 - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition); subst; auto.
    assert (value (ObjId o)). auto. contradiction.
    
    rewrite <- H in H10; inversion H10; subst; auto.
    rewrite <- H11 in H0; inversion H0; subst; auto.

 - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition); subst; auto;
     try (assert (value (ObjId o)); auto; contradiction).
   assert (value null); auto. contradiction.
   
 - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition); subst; auto.
    match goal with
    | H :  hole_free  _ = true |- _
      => inversion H; subst; auto                                                                                                                           end.
     match goal with
    | H : (if hole_free ?T then false else false) = true |- _
      => case_eq (hole_free T); intro Hy; rewrite Hy in H; try (solve_by_FT)
    end. 
    
  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    destruct H with e0; auto.
    destruct H with (v_opa_l v0 lx); auto.
    destruct H with (v_opa_l v0 lx); auto.
    destruct H with null. auto.     

  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    destruct H12 with e2; auto.
    assert (value (v_opa_l v lx)). auto. intuition.
    assert (value (v_opa_l v lx)). auto. intuition.
    assert (value null). auto. intuition.   

  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
        match goal with
    | H :  hole_free  _ = true |- _
      => inversion H; subst; auto                                                                                                                           end.
     match goal with
    | H : (if hole_free ?T then false else false) = true |- _
      => case_eq (hole_free T); intro Hy; rewrite Hy in H; try (solve_by_FT)
    end. 

  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    assert (value (ObjId o)). auto. intuition.
    rewrite <- H13 in H; inversion H; subst; auto.
    rewrite <- H14 in H0; inversion H0; subst; auto.

    rewrite <- H13 in H; inversion H; subst; auto.
    try (inconsist).    

  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    assert (value (ObjId o)). auto. intuition.

    destruct H13 with (v_opa_l v lx); auto.
    assert (value (v_opa_l v lx)). auto. intuition.     

    rewrite <- H14 in H; inversion H; subst; auto.
    rewrite <- H19 in H4; inversion H4; subst; auto.

    rewrite <- H14 in H; inversion H; subst; auto.
    try (inconsist).    

  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    rewrite H in H8; inversion H8; subst; auto.

  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    assert (value null). auto. intuition.  
    
  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    assert (value (v_l v lo)). auto. intuition.
    assert (value null). auto. intuition.  

  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    assert (value (v_l v lo)). auto. intuition.

  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    assert (value (v_l v lo)). auto. intuition.
    assert (value null). auto. intuition.  

  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    assert (value (v_l v lo)). auto. intuition.

  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    assert (value (v_opa_l v lo)). auto. intuition.
    assert (value null). auto. intuition.  

  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    assert (value (v_opa_l v lo)). auto. intuition.
    
  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    assert (value (ObjId o)). auto. intuition.
    assert (value null). auto. intuition.  
    assert (value (ObjId o)). auto. intuition.
    
  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    assert (value (ObjId o)). auto. intuition.
    rewrite <- H in H11; inversion H11; subst; auto.
    rewrite <- H11 in H; inversion H; subst; auto. 
    destruct H12; try (inconsist).    

  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto;
    try (assert (value (ObjId o)); auto; intuition).
    assert (value null). auto. intuition.
  
    
  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    destruct H with e0; auto.
    destruct H17; subst; auto.
    assert (value null). auto. intuition. 
    destruct H3. destruct H3. destruct H3. destruct H3. destruct H3. destruct H4; subst; auto.
    assert (value (ObjId x)); auto.
    intuition. 

    destruct H17; subst; auto.
    destruct H with (v_opa_l null lx); auto. 

    destruct H3. destruct H3. destruct H3. destruct H3. destruct H3. destruct H4; subst; auto.
    destruct H with (v_opa_l (ObjId x) lx); auto.

    destruct H with (v_opa_l v0 lx); auto.

    destruct H with null; auto. 


  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
        match goal with
    | H :  hole_free  _ = true |- _
      => inversion H; subst; auto                                                                                                                           end.
     match goal with
    | H : (if hole_free ?T then false else false) = true |- _
      => case_eq (hole_free T); intro Hy; rewrite Hy in H; try (solve_by_FT)
    end.    
    
  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    destruct H12 with e2; auto.
    destruct H16. inversion H2.
    destruct H2. destruct H2.  destruct H2. destruct H2.
    destruct H2. inversion H2. 

    destruct H16; subst; auto.
    assert (value (v_opa_l null lx)); auto.
    intuition. 

    destruct H2. destruct H2.  destruct H2. destruct H2.
    destruct H2. inversion H3; subst; auto. 
    assert ( value (v_opa_l (ObjId x) lx)); auto.
    intuition.

    assert ( value (v_opa_l v0 lx)); auto.
    intuition.

    assert (value null); auto.
    intuition. 

  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
            match goal with
    | H :  hole_free  _ = true |- _
      => inversion H; subst; auto                                                                                                                           end.
     match goal with
    | H : (if hole_free ?T then false else false) = true |- _
      => case_eq (hole_free T); intro Hy; rewrite Hy in H; try (solve_by_FT)
    end. 

  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    assert (value v).
    destruct H3; subst; auto.
    destruct H0. destruct H0. destruct H0. destruct H0. destruct H0.
    subst; auto.
    assert (value (ObjId o)); auto.
    intuition.

    destruct H3. subst; auto. assert (value null); auto. intuition. 
    destruct H0. destruct H0. destruct H0. destruct H0. destruct H0.
    subst; auto.  assert (value (ObjId x)); auto. intuition. 

    destruct H3.  inversion H0.

    destruct H0. destruct H0. destruct H0. destruct H0. destruct H0.
    inversion H0.

    rewrite <- H in H12; inversion H12; subst; auto.
    destruct H13. rewrite <- H12 in H; inversion H; subst; auto. try (inconsist).
    
    destruct H3. 
    destruct H0. destruct H0. destruct H0. destruct H0. destruct H0. destruct H3; subst; auto. 
    inversion H0.

    rewrite <- H in H12; inversion H12; subst; auto.
    destruct H2. destruct H2.     destruct H2. destruct H2.     destruct H2. destruct H3.
    destruct H0. destruct H0.     destruct H0. destruct H0.     destruct H0. destruct H5.
    subst; auto.  inversion H0; subst; auto.
    rewrite <- H3 in H5; inversion H5; subst; auto.  try (inconsist).

    destruct H3. inversion H0. 
    destruct H0. destruct H0.     destruct H0. destruct H0.     destruct H0. inversion H0.

    destruct H3. inversion H0. 
    destruct H0. destruct H0.     destruct H0. destruct H0.     destruct H0. inversion H0.

    destruct H3. inversion H0. 
    destruct H0. destruct H0.     destruct H0. destruct H0.     destruct H0. inversion H0.    


  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    assert (value (ObjId o)); auto.
    intuition.
    destruct H12 with (v_opa_l v lx); auto.
    assert ( value (v_opa_l v lx)); auto.
    
    destruct H3; subst; auto.
    destruct H0. destruct H0. destruct H0. destruct H0. destruct H0. subst; auto.
    intuition.
    

    destruct H16. inversion H0.
    destruct H0. destruct H0. 
    destruct H0. destruct H0. destruct H0. inversion H0. 

    rewrite <- H in H13; inversion H13; subst; auto. 

    rewrite <- H in H13; inversion H13; subst; auto.
    destruct H14.
    try (inconsist).
    destruct H0. destruct H0. destruct H0. destruct H0. destruct H0. destruct H2.  subst; auto.
    destruct H3. inversion H0. 
    destruct H0. destruct H0. destruct H0. destruct H0. destruct H0.  destruct H3. subst; auto.

    inversion H0; subst; auto. rewrite <- H2 in H3; inversion H3; subst; auto.
    try (inconsist).    

  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    assert (value B_true); auto; intuition. 
    assert (value B_false); auto; intuition.
    assert (value null); auto. intuition. 

  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    assert (value B_true); auto; intuition. 

  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    assert (value B_false); auto; intuition. 
    
  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    try (inversion H0; 
    match goal with
    | H :  hole_free  _ = true |- _
      => inversion H; subst; auto
    end;
    match goal with
    | H : (if hole_free ?T then false else false) = true |- _
      => case_eq (hole_free T); intro Hy; rewrite Hy in H; try (solve_by_FT)
    end).
    inversion H0.
    try (inversion H0; 
    match goal with
    | H :  hole_free  _ = true |- _
      => inversion H; subst; auto
    end;
    match goal with
    | H : (if hole_free ?T then false else false) = true |- _
      => case_eq (hole_free T); intro Hy; rewrite Hy in H; try (solve_by_FT)
    end).
    inversion H0.
        try (inversion H0; 
    match goal with
    | H :  hole_free  _ = true |- _
      => inversion H; subst; auto
    end;
    match goal with
    | H : (if hole_free ?T then false else false) = true |- _
      => case_eq (hole_free T); intro Hy; rewrite Hy in H; try (solve_by_FT)
    end).

    try (inversion H0; 
    match goal with
    | H :  hole_free  _ = true |- _
      => inversion H; subst; auto
    end;
    match goal with
    | H : (if hole_free ?T then false else false) = true |- _
      => case_eq (hole_free T); intro Hy; rewrite Hy in H; try (solve_by_FT)
    end).

    try (inversion H0; 
    match goal with
    | H :  hole_free  _ = true |- _
      => inversion H; subst; auto
    end;
    match goal with
    | H : (if hole_free ?T then false else false) = true |- _
      => case_eq (hole_free T); intro Hy; rewrite Hy in H; try (solve_by_FT)
    end).

    try (inversion H0; 
    match goal with
    | H :  hole_free  _ = true |- _
      => inversion H; subst; auto
    end;
    match goal with
    | H : (if hole_free ?T then false else false) = true |- _
      => case_eq (hole_free T); intro Hy; rewrite Hy in H; try (solve_by_FT)
    end).

    try (inversion H0; 
    match goal with
    | H :  hole_free  _ = true |- _
      => inversion H; subst; auto
    end;
    match goal with
    | H : (if hole_free ?T then false else false) = true |- _
      => case_eq (hole_free T); intro Hy; rewrite Hy in H; try (solve_by_FT)
    end).

    try (inversion H0; 
    match goal with
    | H :  hole_free  _ = true |- _
      => inversion H; subst; auto
    end;
    match goal with
    | H : (if hole_free ?T then false else false) = true |- _
      => case_eq (hole_free T); intro Hy; rewrite Hy in H; try (solve_by_FT)
    end).

    try (inversion H0; 
    match goal with
    | H :  hole_free  _ = true |- _
      => inversion H; subst; auto
    end;
    match goal with
    | H : (if hole_free ?T then false else false) = true |- _
      => case_eq (hole_free T); intro Hy; rewrite Hy in H; try (solve_by_FT)
    end).

    try (inversion H0; 
    match goal with
    | H :  hole_free  _ = true |- _
      => inversion H; subst; auto
    end;
    match goal with
    | H : (if hole_free ?T then false else false) = true |- _
      => case_eq (hole_free T); intro Hy; rewrite Hy in H; try (solve_by_FT)
    end).

    try (inversion H0; 
    match goal with
    | H :  hole_free  _ = true |- _
      => inversion H; subst; auto
    end;
    match goal with
    | H : (if hole_free ?T then false else false) = true |- _
      => case_eq (hole_free T); intro Hy; rewrite Hy in H; try (solve_by_FT)
    end).

    try (inversion H0; 
    match goal with
    | H :  hole_free  _ = true |- _
      => inversion H; subst; auto
    end;
    match goal with
    | H : (if hole_free ?T then false else false) = true |- _
      => case_eq (hole_free T); intro Hy; rewrite Hy in H; try (solve_by_FT)
    end).

    try (inversion H0; 
    match goal with
    | H :  hole_free  _ = true |- _
      => inversion H; subst; auto
    end;
    match goal with
    | H : (if hole_free ?T then false else false) = true |- _
      => case_eq (hole_free T); intro Hy; rewrite Hy in H; try (solve_by_FT)
    end).

    try (inversion H0; 
    match goal with
    | H :  hole_free  _ = true |- _
      => inversion H; subst; auto
    end;
    match goal with
    | H : (if hole_free ?T then false else false) = true |- _
      => case_eq (hole_free T); intro Hy; rewrite Hy in H; try (solve_by_FT)
    end).

    try (inversion H0; 
    match goal with
    | H :  hole_free  _ = true |- _
      => inversion H; subst; auto
    end;
    match goal with
    | H : (if hole_free ?T then false else false) = true |- _
      => case_eq (hole_free T); intro Hy; rewrite Hy in H; try (solve_by_FT)
    end).
Qed. Hint Resolve deterministic_prime. 