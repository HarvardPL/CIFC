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
     
  - 
    inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    split; auto.
    pose proof (exclude_middle_runtime_val v1 v2 H H0).
    destruct H3. 
    assert (result = B_true); auto.
    assert (result0 = B_true); auto.
    subst; auto.

    assert (result = B_false); auto.
    assert (result0 = B_false); auto.
    subst; auto. 

    
  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition); subst; auto.
    assert (value (ObjId o)). auto. contradiction.
    assert (value (ObjId o)). auto. contradiction. 
    assert (value (v_opa_l (ObjId o) ell)).
    apply v_opa_labeled; auto. intros. intro contra; inversion contra. 
    auto. contradiction.

    assert (value (v_opa_l (ObjId o) ell)).
    apply v_opa_labeled; auto. intros. intro contra; inversion contra. 
    auto. contradiction.

  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition); subst; auto.
    assert (value (ObjId o)). auto. contradiction.
    assert (value (ObjId o)). auto. contradiction.
    rewrite <- H4 in H; inversion H; subst; auto.
    rewrite <- H13 in H0; inversion H0; subst; auto.     

  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition); subst; auto.
    assert (value (v_opa_l (ObjId o) ell)).
    apply v_opa_labeled; auto. intros. intro contra; inversion contra. 
    contradiction.
    assert (value (v_opa_l (ObjId o) ell)).
    apply v_opa_labeled; auto. intros. intro contra; inversion contra. 
    contradiction.
    rewrite <- H4 in H; inversion H; subst; auto.
    rewrite <- H14 in H0; inversion H0; subst; auto.     

  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition); subst; auto.
    assert (value (ObjId o)). auto. contradiction.
    assert (value (ObjId o)). auto. contradiction.
    assert (value (v_opa_l (ObjId o) ell)).
    apply v_opa_labeled; auto. intros. intro contra; inversion contra. 
    auto. contradiction.

    assert (value (v_opa_l (ObjId o) ell)).
    apply v_opa_labeled; auto. intros. intro contra; inversion contra. 
    auto. contradiction.       
    
  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    assert (value (ObjId o)). auto. contradiction.
    rewrite <- H6 in H; inversion H; subst; auto.

    rewrite <- H15 in H0; inversion H0; subst; auto.     

    
  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    assert (value (v_opa_l (ObjId o) ell)).
    apply v_opa_labeled; auto.
    intros. intro contra; inversion contra. 
    auto. contradiction.   
    rewrite <- H7 in H; inversion H; subst;  auto.
    rewrite <- H16 in H0; inversion H0; subst; auto. 

  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    rewrite H5 in H; inversion H; subst; auto.
    
  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    assert (value (l lo)). auto. contradiction.
    assert (value (v_opa_l (l lo) ell)). apply v_opa_labeled; auto.
    intros. intro contra; inversion contra. contradiction.

  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    assert (value (l lo)). auto. contradiction.

  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
     assert (value (v_opa_l (l lo) ell)). apply v_opa_labeled; auto.
    intros. intro contra; inversion contra. contradiction.

  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    assert (value (v_l v lo)). auto. contradiction.

  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    assert (value (v_l v lo)). auto. contradiction.

  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    assert (value (v_l v lo)). auto. contradiction.

  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    assert (value (v_l v lo)). auto. contradiction.    

   - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    assert (value (ObjId o)). auto. contradiction.
    assert (value (v_opa_l (ObjId o) ell)).
    apply v_opa_labeled; auto. intros. intro contra; inversion contra. 
    auto. contradiction.

   - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
     assert (value (ObjId o)). auto. contradiction.
     rewrite <- H in H1; inversion H1; subst; auto.

   - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    assert (value (v_opa_l (ObjId o) ell)).
    apply v_opa_labeled; auto. intros. intro contra; inversion contra. 
    auto. contradiction.
    rewrite <- H in H2; inversion H2; subst; auto.
         
 
    
  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    assert (value (ObjId o)). auto. intuition.
    assert (value (ObjId o)). auto. intuition.

    assert (value (v_opa_l (ObjId o) ell)).
    apply v_opa_labeled; auto. intros. intro contra; inversion contra. 
    contradiction.

    assert (value (v_opa_l (ObjId o) ell)).
    apply v_opa_labeled; auto. intros. intro contra; inversion contra. 
    contradiction.

    
  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    assert (value (l lo')). auto. intuition.
    assert (value (v_opa_l (l lo') ell)).
    apply v_opa_labeled; auto. intros. intro contra; inversion contra. 
    contradiction.

    assert (value (l lo')). auto. intuition.
    assert (value (v_opa_l (l lo') ell')).
    apply v_opa_labeled; auto. intros. intro contra; inversion contra. 
    contradiction.


  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    assert (value (ObjId o)). auto. contradiction.
    assert (value (l lo')). auto. intuition.
     rewrite <- H in H6; inversion H6; subst; auto.

   - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    assert (value (ObjId o)). auto. contradiction.
    assert (value (v_opa_l (l lo') ell)).
     apply v_opa_labeled; auto. intros. intro contra; inversion contra. 
    contradiction.

    rewrite <- H in H6; inversion H6; subst; auto.    

  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    assert (value  (v_opa_l (ObjId o) ell)).
    apply v_opa_labeled; auto. intros. intro contra; inversion contra. 
    auto. contradiction.
    
    assert (value (l lo')). auto. intuition.
     rewrite <- H in H6; inversion H6; subst; auto.

- inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    assert (value  (v_opa_l (ObjId o) ell)).
    apply v_opa_labeled; auto. intros. intro contra; inversion contra. 
    auto. contradiction.
    
    assert (value (v_opa_l (l lo') ell')).
     apply v_opa_labeled; auto. intros. intro contra; inversion contra. 
     contradiction.
     rewrite <- H in H6; inversion H6; subst; auto.
    
(*  Container (toLabeled e1 v) fs lb sf = ctn2 /\ ctns1 = ctns2 /\ h1 = h2 *)

  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    assert (value (l lo)); auto. intuition.

- inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    assert (value (l lo)); auto. intuition.
    
  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    assert (value (ObjId o)). auto. contradiction.
    assert (value (v_opa_l (ObjId o) ell)).
    apply v_opa_labeled; auto. intros. intro contra; inversion contra. 
    contradiction.
    
  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    assert (value (ObjId o)). auto. intuition.
    split; auto. split; auto.
    rewrite <- H7 in H; inversion H; subst; auto.
 
  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    assert (value (v_opa_l (ObjId o) ell)).
    apply v_opa_labeled; auto. intros. intro contra; inversion contra. 
    contradiction.
    split; auto. split; auto.
    rewrite <- H7 in H; inversion H; subst; auto.

  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    assert (value B_true); auto.
    contradiction.
    assert (value B_false); auto.
    contradiction.


  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    assert (value B_true); auto.
    contradiction.
    
 
  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    assert (value B_false); auto.
    contradiction.

  (* Container (v_opa_l v lb) fs' lb' sf' = ctn2 /\ ctns1 = ctns2 /\ h1 = h2 *)
  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    destruct H0 with v0 ell; auto. inversion H; subst; auto.


  (* Container (v_opa_l v (join_label ell lb)) fs' lb' sf' = ctn2 /\ ctns1 = ctns2 /\ h1 = h2 *)
  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    destruct H13 with v ell; auto. inversion H1; subst; auto.     
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

  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    pose proof (exclude_middle_runtime_val v1 v2 H H0).
    destruct H3. 
    assert (result = B_true); auto.
    assert (result0 = B_true); auto.
    subst; auto.

    assert (result = B_false); auto.
    assert (result0 = B_false); auto.
    subst; auto. 
      

    
  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition); subst; auto.
    assert (value (ObjId o)). auto. contradiction.
    assert (value (v_opa_l (ObjId o) ell)).
    apply v_opa_labeled; auto. intros. intro contra; inversion contra. 
    auto. contradiction.
    
    assert (value null). auto. 
    contradiction.

    assert (value (v_opa_l null ell)).
    apply v_opa_labeled; auto. intros. intro contra; inversion contra. 
    contradiction.

  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition); subst; auto.
    assert (value (ObjId o)). auto. 
    contradiction.
    rewrite <- H10 in H; inversion H; subst; auto.
    rewrite <- H11 in H0; inversion H0; subst; auto.     

  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition); subst; auto.
    assert (value (v_opa_l (ObjId o) ell)).
    apply v_opa_labeled; auto. intros. intro contra; inversion contra. 
    contradiction.
    rewrite <- H11 in H; inversion H; subst; auto.
    rewrite <- H12 in H0; inversion H0; subst; auto.     

  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition); subst; auto.
    assert (value (ObjId o)). auto. contradiction.
    assert (value (v_opa_l (ObjId o) ell)).
    apply v_opa_labeled; auto. intros. intro contra; inversion contra. 
    auto. contradiction.

    assert (value null). auto. contradiction.

    assert (value (v_opa_l null ell)).
    apply v_opa_labeled; auto. intros. intro contra; inversion contra. 
    contradiction.   

  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    assert (value (ObjId o)). auto. contradiction.
    rewrite <- H12 in H; inversion H; subst; auto.
    rewrite <- H13 in H0; inversion H0; subst; auto.

  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    assert (value (v_opa_l (ObjId o) ell)).
    apply v_opa_labeled; auto.
    intros. intro contra; inversion contra. 
    auto. contradiction.   
    rewrite <- H13 in H; inversion H; subst;  auto.
    rewrite <- H14 in H0; inversion H0; subst; auto. 

  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    rewrite H8 in H; inversion H; subst; auto. 

  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
     assert (value (l lo)). auto.
     contradiction.

     assert (value (v_opa_l (l lo) ell)).
    apply v_opa_labeled; auto.
    intros. intro contra; inversion contra. 
    auto. contradiction.   

    assert (value (l lo)). auto.
    contradiction.

     assert (value (v_opa_l (l lo) ell)).
    apply v_opa_labeled; auto.
    intros. intro contra; inversion contra. 
    auto. contradiction.

   - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
     assert (value (l lo)). auto.
     contradiction.

     rewrite H0 in H11; inversion H11. 

  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.    
     assert (value (v_opa_l (l lo) ell)).
    apply v_opa_labeled; auto.
    intros. intro contra; inversion contra. 
    auto. contradiction.
    
    rewrite H0 in H12; inversion H12. 

  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    assert (value (v_l v lo)). auto. contradiction.
    assert (value null). auto.
    contradiction. 

  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    assert (value (v_l v lo)). auto. contradiction.

  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    assert (value (v_l v lo)). auto. contradiction.
    assert (value null). auto. contradiction.    

  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    assert (value (v_l v lo)). auto. contradiction.



    (* start objectLabelOf*)

  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    + assert (value (ObjId o)). auto. contradiction.
    +  assert (value (v_opa_l (ObjId o) ell)).
       apply v_opa_labeled; auto. intros. intro contra; inversion contra. 
       auto. contradiction.
    +  assert (value null). auto. contradiction.
    +  assert (value (v_opa_l null ell)). apply v_opa_labeled; auto.
       intros. intro contra; inversion contra.  contradiction.

  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    + assert (value (ObjId o)). auto. contradiction.
    + rewrite <- H in H8; inversion H8; subst; auto.

  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    + assert (value (v_opa_l (ObjId o) ell)).
      apply v_opa_labeled; auto. intros. intro contra; inversion contra. contradiction.
    + rewrite <- H in H9; inversion H9; subst; auto. 

    (* end objectLabelOf*)

      
  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    assert (value (ObjId o)). auto. contradiction.
    assert (value (ObjId o)). auto. contradiction.
    
    assert (value (v_opa_l (ObjId o) ell)).
    apply v_opa_labeled; auto. intros. intro contra; inversion contra. 
    auto. contradiction.

    assert (value (v_opa_l (ObjId o) ell)).
    apply v_opa_labeled; auto. intros. intro contra; inversion contra. 
    auto. contradiction.
    
    assert (value null). auto. contradiction.
    assert (value (v_opa_l null ell)).
    apply v_opa_labeled; auto. intros. intro contra; inversion contra. 
    auto. contradiction.
    assert (value (ObjId o)). auto. contradiction.
    assert (value (v_opa_l (ObjId o) ell)).
    apply v_opa_labeled; auto. intros. intro contra; inversion contra. 
    auto. contradiction.

    assert (value (ObjId o)). auto. contradiction.
      assert (value (v_opa_l (ObjId o) ell)).
    apply v_opa_labeled; auto. intros. intro contra; inversion contra. 
    auto. contradiction.

  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    assert (value (l lo')). auto. contradiction.
    assert (value (v_opa_l (l lo') ell)).
    apply v_opa_labeled; auto. intros. intro contra; inversion contra. 
    auto. contradiction.

    assert (value (l lo')). auto. contradiction.
    assert (value (v_opa_l (l lo') ell')).
    apply v_opa_labeled; auto. intros. intro contra; inversion contra. 
    auto. contradiction.

    assert (value (l lo')). auto. contradiction.
    assert (value (l lo')). auto. contradiction.
        
    assert (value (v_opa_l (l lo') ell)).
    apply v_opa_labeled; auto. intros. intro contra; inversion contra. 
    auto. contradiction.

    assert (value (v_opa_l (l lo') ell')).
    apply v_opa_labeled; auto. intros. intro contra; inversion contra. 
    auto. contradiction.

  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
     assert (value (ObjId o)). auto. intuition.
     assert (value (l lo')). auto. contradiction.
     rewrite <- H11 in H; inversion H; subst; auto.
     rewrite <- H11 in H; inversion H; subst; auto.
     destruct H12.
     rewrite H2 in H0; inversion H0.
     rewrite H2 in H1; inversion H1.


  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
     assert (value (ObjId o)). auto. intuition.     
    assert (value (v_opa_l (l lo') ell)).
    apply v_opa_labeled; auto. intros. intro contra; inversion contra. 
    auto. contradiction.
    rewrite <- H12 in H; inversion H; subst; auto.
    rewrite <- H12 in H; inversion H; subst; auto.
    destruct H13.
    rewrite H2 in H0; inversion H0.
    rewrite H2 in H1; inversion H1.

  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    assert (value (v_opa_l (ObjId o) ell)).
    apply v_opa_labeled; auto. intros. intro contra; inversion contra. 
    auto. contradiction.

    assert (value (l lo')). auto. contradiction.
    rewrite <- H12 in H; inversion H; subst; auto.
    rewrite <- H12 in H; inversion H; subst; auto.
    destruct H13.
    rewrite H2 in H0; inversion H0.
    rewrite H2 in H1; inversion H1.

  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    assert (value (v_opa_l (ObjId o) ell)).
    apply v_opa_labeled; auto. intros. intro contra; inversion contra. 
    auto. contradiction.

    assert (value (v_opa_l (l lo') ell')).
    apply v_opa_labeled; auto. intros. intro contra; inversion contra. 
    auto. contradiction.

    rewrite <- H13 in H; inversion H; subst; auto.
    rewrite <- H13 in H; inversion H; subst; auto.
    destruct H14.
    rewrite H2 in H0; inversion H0.
    rewrite H2 in H1; inversion H1.
    
     
  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    assert (value (l lo)); auto. intuition.
    assert (value null); auto. intuition. 

  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    assert (value (l lo)); auto. intuition.
    
  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    assert (value (ObjId o)). auto. intuition.
    assert (value (v_opa_l (ObjId o) ell)).
    apply v_opa_labeled; auto. intros. intro contra; inversion contra. 
    contradiction.
    assert (value (ObjId o)). auto. intuition.
    assert (value (v_opa_l (ObjId o) ell)).
    apply v_opa_labeled; auto. intros. intro contra; inversion contra. 
    auto. contradiction.
    assert (value null). auto. intuition.

    assert (value (v_opa_l null ell)).
    apply v_opa_labeled; auto. intros. intro contra; inversion contra. 
    contradiction.

  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    assert (value (ObjId o)). auto. intuition.
    rewrite <- H12 in H; inversion H; subst; auto.
    rewrite <- H12 in H; inversion H; subst; auto.
    try (inconsist).
     
  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    assert (value (v_opa_l (ObjId o) ell)).
    apply v_opa_labeled; auto. intros. intro contra; inversion contra. 
    contradiction.

    rewrite <- H13 in H; inversion H; subst; auto.
    rewrite <- H13 in H; inversion H; subst; auto.
    rewrite H1 in H14; inversion H14.     
    
  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    assert (value B_true); auto.
    contradiction.
    assert (value B_false); auto.
    contradiction.
    assert (value null); auto.
    contradiction.    

  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    assert (value B_true); auto.
    contradiction.    
 
  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    assert (value B_false); auto.
    contradiction.

    
  (* Container (v_opa_l v lb) fs' lb' sf' = ctn2 /\ ctns1 = ctns2 /\ h1 = h2 *)
  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    destruct H0 with v0 ell; auto. inversion H; subst; auto.


  (* Container (v_opa_l v (join_label ell lb)) fs' lb' sf' = ctn2 /\ ctns1 = ctns2 /\ h1 = h2 *)
  - inversion Hy2; subst; auto; try (solve_by_invert_non_value); try (intuition; fail); subst; auto.
    destruct H11 with v ell; auto.
    inversion H10; subst; auto. 
Qed. Hint Resolve deterministic_prime. 