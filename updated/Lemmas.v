Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.

Require Import Label.
Require Import Language Types.


Lemma ct_consist : forall ct ctn ctns h ct' ctn' ctns' h', 
  (Config ct ctn ctns h) ==> (Config ct' ctn' ctns' h') -> ct = ct'. 
 Proof.
   intros. remember (Config ct ctn ctns h) as config. 
remember (Config ct' ctn' ctns' h') as config'.  
 induction H; inversion Heqconfig; inversion Heqconfig';  subst; auto.
  Qed.

Lemma empty_fields : forall fields F cls', 
  F = init_field_map fields empty_field_map ->
  (forall f, type_of_field fields f = Some cls' ->
  F f = Some null).
Proof.
  intro. intro. intro. intro. generalize dependent F.  
  induction fields. 
  - intros.   inversion H0.
  - intro F. intro Hy. 
     induction a. intro f. intro. rewrite Hy.
     case_eq (beq_id i f). intro.
     unfold init_field_map. rewrite H0. auto. 
     intro. unfold init_field_map. rewrite H0. fold init_field_map. 
     apply IHfields with (F:=(init_field_map fields empty_field_map))(f:=f).
     auto.   unfold type_of_field in H. rewrite H0 in H. fold type_of_field in H.
    auto.  
Qed.  

Lemma value_is_valid_syntax : forall v, 
  value v -> valid_syntax v.
Proof with eauto. intros. inversion H; auto.   Qed.
Hint Resolve value_is_valid_syntax.

Lemma surface_syntax_if : forall t1 t2,
    (if surface_syntax t1 then surface_syntax t2 else false)
    = true -> surface_syntax t1 = true /\ surface_syntax t2 = true.
Proof.
  intros.
  case_eq (surface_syntax t1).
  intro. case_eq (surface_syntax t2). intro. auto.
  intro. rewrite H0 in H. rewrite H1 in H. intuition. intro. rewrite H0 in H. intuition.
Qed.
Hint Resolve surface_syntax_if. 

Lemma surface_syntax_triple : forall t1 t2 t3,
    (if surface_syntax t1
     then if surface_syntax t2 then surface_syntax t3 else false
     else false) = true ->
    surface_syntax t1 = true /\ surface_syntax t2 = true /\ surface_syntax t3 = true.
Proof with eauto.
  intros.
  case_eq (surface_syntax t1); intro.
  rewrite H0 in H.
  apply surface_syntax_if in H.
  destruct H. auto.
  rewrite H0 in H. intuition. 
Qed.
Hint Resolve surface_syntax_triple.
    
Lemma surface_syntax_is_valid_syntax : forall t,
  surface_syntax t = true -> valid_syntax t.
Proof with eauto.
  intros.
  induction t; auto;
  try (inversion H; auto;
  apply  surface_syntax_if in H1; destruct H1; auto).
  inversion H; auto.
  apply surface_syntax_triple in H1. destruct H1. destruct H1. auto. 
Qed.
Hint Resolve surface_syntax_is_valid_syntax.

Lemma surface_syntax_is_hole_free : forall t, 
  surface_syntax t = true -> hole_free t = true. 
Proof.
  intros.
  induction t; auto;
    try (apply surface_syntax_if in H; destruct H; apply IHt1 in H; apply IHt2 in H0; 
         unfold hole_free; fold hole_free); try (rewrite H); auto;
      try (unfold surface_syntax in H; inversion H).
  fold surface_syntax. fold surface_syntax in H. fold surface_syntax in H1.
  apply surface_syntax_triple in H1. destruct H1. destruct H1. auto.
  rewrite H0. rewrite H1.        rewrite H2.
  auto.
  unfold hole_free. fold hole_free.
  apply IHt1 in H0. apply IHt2 in H1. apply IHt3 in H2.
  rewrite H0. rewrite H1. rewrite H2.  auto. 
Qed. 
Hint Resolve surface_syntax_is_hole_free. 

Lemma value_is_hole_free : forall v, 
  value v -> hole_free v = true. 
Proof. intro v. intro H_v. induction H_v; subst; auto. Qed.  
Hint Resolve value_is_hole_free. 

Lemma beq_oid_equal : forall x x', beq_oid x x' = true -> x = x'.
Proof.
   intros. unfold beq_oid in H.
   destruct x. destruct x'. f_equal. 
   case_eq (n =? n0). intro. 
   apply beq_nat_true with (n:=n) (m:=n0). auto. 

   intro. rewrite H0 in H. inversion H.
Qed. Hint Resolve  beq_oid_equal.

Lemma beq_oid_same : forall o, beq_oid o o = true. 
Proof with auto. 
  intro o. unfold beq_oid. destruct o. induction n. reflexivity.
  simpl. auto. 
Qed. 

Lemma exclude_middle_label_eq : forall lb1 lb2 ,
    l lb1 = l lb2 \/ l lb1 <> l lb2.
Proof with eauto.
  intros.  pose proof (exclude_middle_label lb1 lb2).
  destruct H; subst; auto.
  right. intro contra; inversion contra; subst; auto.
Qed. Hint Resolve exclude_middle_label_eq.

Lemma exclude_middle_val_eq : forall (v1:tm) (v2:tm),
    value v1 -> value v2 ->
    v1 = v2 \/ v1 <> v2.
Proof with eauto.
  intros.
  generalize dependent v2.
  induction v1; inversion H; intros;
  induction v2; inversion H0; intros; auto;
    try (right; intro contra; inversion contra; fail); subst; auto.
  case_eq (beq_oid o o1); intro.
  apply beq_oid_equal in H1.
  subst; auto.
  right. intro contra; inversion contra. subst; auto.
  pose proof (beq_oid_same o1). rewrite H1 in H2; inversion H2.

  pose proof ( exclude_middle_label_eq l l0).
  assert (v1 = v2 \/ v1 <> v2); auto. apply IHv1; auto.
  inversion H3; auto.
  destruct H2.
  destruct H0. inversion H0. 
  left; auto. subst; auto.
  right. intro contra; inversion contra; subst; auto.
  right. intro contra; inversion contra; subst; auto.
  
  pose proof ( exclude_middle_label_eq l l0).
  assert (v1 = v2 \/ v1 <> v2); auto. apply IHv1; auto.
  inversion H3; auto.
  destruct H2.
  destruct H0. inversion H0. 
  left; auto. subst; auto.
  right. intro contra; inversion contra; subst; auto.
  right. intro contra; inversion contra; subst; auto.
Qed. Hint Resolve exclude_middle_val_eq.


Lemma value_progress : forall CT v fs lb sf ctns h T, 
config_has_type CT empty_context (Config CT (Container v fs lb sf) ctns h) T ->
valid_config (Config CT (Container v fs lb sf) ctns h) ->
value v ->
terminal_state (Config CT (Container v fs lb sf) ctns h) \/
(exists config' : config,
   Config CT (Container v fs lb sf) ctns h ==> config').
Proof.
  intros CT v fs lb sf ctns h T.
  intro H_typing. intro H_config. intro Hv.
  destruct fs.
  destruct ctns.
  auto.
  inversion H_typing; subst; auto.
  destruct H8 with c ctns; auto.
  destruct H as [lb0].
  destruct H as [sf0].
  rename x into fs0.
  right. subst; auto.
  exists (Config CT (Container (v_opa_l v lb) fs0 lb0 sf0) ctns h). auto.
destruct t; right. 
  - exists (Config CT (Container (Tvar i) fs lb sf) ctns h); auto.
    (*null*)
  - exists (Config CT (Container (null) fs lb sf) ctns h); auto.
    (*eq comparison*)
  - inversion H_config. inversion H7.  subst.
    inversion H15. inversion H1; subst; auto.  
    + assert (surface_syntax (EqCmp t1 t2) = true).
      unfold surface_syntax. fold surface_syntax. 
      rewrite H12. rewrite H13.  auto. 
      apply surface_syntax_is_hole_free in H. 
      exists (Config CT (Container (EqCmp t1 t2)  fs lb sf) ctns h); auto.
    + subst. exists (Config CT (Container (EqCmp v t2) fs lb sf) ctns h); auto.
    + apply value_is_hole_free in H12.  apply surface_syntax_is_hole_free in H13.
      assert (hole_free (EqCmp t1 t2) = true). unfold hole_free. fold hole_free.
      rewrite H12. rewrite H13. auto. 
      exists (Config CT (Container (EqCmp t1 t2) fs lb sf) ctns h); auto.
    + exists (Config CT (Container (EqCmp t1 v) fs lb sf) ctns h); auto.
    + apply value_is_hole_free in H12.  apply  value_is_hole_free in H13.
      assert (hole_free (EqCmp t1 t2) = true). unfold hole_free. fold hole_free.
      rewrite H12. rewrite H13. auto. 
      exists (Config CT (Container (EqCmp t1 t2) fs lb sf) ctns h); auto.
  - inversion H_config. inversion H7.  subst. inversion H15. inversion H1. subst.
+ assert (surface_syntax (FieldAccess t i) = true). auto. apply surface_syntax_is_hole_free in H. 
exists (Config CT (Container (FieldAccess t i) fs lb sf) ctns h); auto.
+ subst. exists (Config CT (Container (FieldAccess v i) fs lb sf) ctns h). auto. 
+ subst. apply value_is_hole_free in H11. 
exists (Config CT (Container (FieldAccess t i) fs lb sf) ctns h); auto.
- inversion H_config. inversion H7.  subst. inversion H15. inversion H1. subst.  
  + subst.  assert (surface_syntax (MethodCall t1 i t2) = true). unfold surface_syntax.
    fold surface_syntax. 
    rewrite H12. rewrite H14.  auto. 
    apply surface_syntax_is_hole_free in H. 
    exists (Config CT (Container (MethodCall t1 i t2)  fs lb sf) ctns h); auto.
  + subst. exists (Config CT (Container (MethodCall v i t2) fs lb sf) ctns h). auto. 
  + subst. apply value_is_hole_free in H12.  apply surface_syntax_is_hole_free in H14.
  assert (hole_free (MethodCall t1 i t2) = true). unfold hole_free. fold hole_free. rewrite H12.
  rewrite H14. auto.
  exists (Config CT (Container (MethodCall t1 i t2) fs lb sf) ctns h); auto.
+ subst. exists (Config CT (Container (MethodCall t1 i v)  fs lb sf) ctns h); auto.
+ subst. apply value_is_hole_free in H12. apply value_is_hole_free in H14. 
  assert (hole_free (MethodCall t1 i t2) = true). unfold hole_free. fold hole_free.
  rewrite H12. rewrite H14. auto.
  exists (Config CT (Container (MethodCall t1 i t2) fs lb sf) ctns h); auto.
+ subst; auto. exists (Config CT (Container (MethodCall t1 i (unlabelOpaque v)) fs lb sf) ctns h); auto.
  (*newly added rule*)
+ subst; auto. exists (Config CT (Container (MethodCall t1 i (unlabelOpaque v2)) fs lb sf) ctns h); auto.
  apply ST_val; auto. unfold hole_free. fold hole_free.
  apply value_is_hole_free in H12.
  apply value_is_hole_free in H14.
  rewrite H12. rewrite H14.  auto. 
  
  
- exists (Config CT (Container (NewExp c) fs lb sf) ctns h); auto.
- inversion H_config. inversion H7.  subst. inversion H15. inversion H1. subst.
  exists  (Config CT (Container B_true fs lb sf) ctns h); auto.
- inversion H_config. inversion H7.  subst. inversion H15. inversion H1. subst.
  exists  (Config CT (Container B_false fs lb sf) ctns h); auto.   
- exists (Config CT (Container (Language.l l) fs lb sf) ctns h); auto.
- inversion H_config. inversion H7.  subst. inversion H15. inversion H1. subst.  
+ subst. assert (surface_syntax (labelData t l) = true). unfold surface_syntax. fold surface_syntax. auto.  
apply surface_syntax_is_hole_free in H. 
exists (Config CT (Container (labelData t l) fs lb sf) ctns h); auto.
+ subst. exists (Config CT (Container (labelData v l) fs lb sf) ctns h); auto.
+ subst.  assert (hole_free t = true). apply value_is_hole_free. auto. 
assert (hole_free (labelData t l) = true). unfold hole_free. fold hole_free. auto. 
exists (Config CT (Container (labelData t l) fs lb sf) ctns h); auto.
- inversion H_config. inversion H7.  subst. inversion H15. inversion H1. subst.  
+ subst. assert (surface_syntax (unlabel t) = true). unfold surface_syntax. fold surface_syntax. auto.  
apply surface_syntax_is_hole_free in H.  
exists (Config CT (Container (unlabel t) fs lb sf) ctns h); auto.
+ subst. exists (Config CT (Container (unlabel v ) fs lb sf) ctns h); auto.
+ subst. assert (hole_free t = true). apply value_is_hole_free. auto. 
assert (hole_free (unlabel t) = true). unfold hole_free. fold hole_free. auto. 
exists (Config CT (Container (unlabel t) fs lb sf) ctns h); auto.
- inversion H_config. inversion H7.  subst. inversion H15. inversion H1. subst.  
  + subst.
    assert (surface_syntax (labelOf t) = true).
    unfold surface_syntax. fold surface_syntax. auto.  
    apply surface_syntax_is_hole_free in H.  
    exists (Config CT (Container (labelOf t) fs lb sf) ctns h); auto.
+ subst. exists (Config CT (Container (labelOf v ) fs lb sf) ctns h); auto.
+ subst. assert (hole_free t = true). apply value_is_hole_free. auto. 
assert (hole_free (labelOf t) = true). unfold hole_free. fold hole_free. auto. 
exists (Config CT (Container (labelOf t) fs lb sf) ctns h); auto.
- inversion H_config. inversion H7.  subst. inversion H15. inversion H1. subst.  
+ subst. assert (surface_syntax (unlabelOpaque t) = true). unfold surface_syntax. fold surface_syntax. auto.  
apply surface_syntax_is_hole_free in H.  
exists (Config CT (Container (unlabelOpaque t) fs lb sf) ctns h); auto.
+ subst. exists (Config CT (Container (unlabelOpaque v ) fs lb sf) ctns h); auto.
+ subst. assert (hole_free t = true). apply value_is_hole_free. auto. 
assert (hole_free (unlabelOpaque t) = true). unfold hole_free. fold hole_free. auto. 
exists (Config CT (Container (unlabelOpaque t) fs lb sf) ctns h); auto.
- exists (Config CT (Container Skip fs lb sf) ctns h); auto.
- inversion H_config. inversion H7.  subst. inversion H15. inversion H1. subst.  
+ subst. assert (surface_syntax (Assignment i t) = true). unfold surface_syntax. fold surface_syntax. auto.  
apply surface_syntax_is_hole_free in H.  
exists (Config CT (Container (Assignment i t) fs lb sf) ctns h); auto.
+ subst. exists (Config CT (Container (Assignment i v) fs lb sf) ctns h); auto.
+ subst. assert (hole_free t = true). apply value_is_hole_free. auto. 
assert (hole_free (Assignment i t) = true). unfold hole_free. fold hole_free. auto. 
exists (Config CT (Container (Assignment i t) fs lb sf) ctns h); auto.
- inversion H_config. inversion H7.  subst. inversion H15. inversion H1. subst.  
+ subst.  assert (surface_syntax (FieldWrite t1 i t2) = true). unfold surface_syntax. fold surface_syntax. 
rewrite H12. rewrite H14.  auto. 
apply surface_syntax_is_hole_free in H. 
exists (Config CT (Container (FieldWrite t1 i t2)  fs lb sf) ctns h); auto.
+ subst. apply value_is_hole_free in H12.  apply surface_syntax_is_hole_free in H14.
assert (hole_free (FieldWrite t1 i t2) = true). unfold hole_free. fold hole_free. rewrite H12. rewrite H14. auto.
exists (Config CT (Container (FieldWrite t1 i t2) fs lb sf) ctns h); auto.
+ subst. exists (Config CT (Container (FieldWrite v i t2) fs lb sf) ctns h); auto. 
+ subst. subst. apply value_is_hole_free in H12.  apply value_is_hole_free in H14.
  assert (hole_free (FieldWrite t1 i t2) = true). unfold hole_free. fold hole_free.
  rewrite H12. rewrite H14. auto.
exists (Config CT (Container (FieldWrite t1 i t2)  fs lb sf) ctns h); auto.
+ subst. exists (Config CT (Container (FieldWrite t1 i v) fs lb sf) ctns h); auto.
+ subst; auto.  exists (Config CT (Container (FieldWrite t1 i (unlabelOpaque v)) fs lb sf) ctns h); auto.
  (*newly added rule*)
+ subst; auto. exists (Config CT (Container (FieldWrite  t1 i (unlabelOpaque v2)) fs lb sf) ctns h); auto.
  apply ST_val; auto. unfold hole_free. fold hole_free.
  apply value_is_hole_free in H12.
  apply value_is_hole_free in H14.
  rewrite H12. rewrite H14.  auto. 
- inversion H_config. inversion H7.  subst.
  inversion H15. inversion H1. subst.
  +  assert (surface_syntax (If t1 t2 t3) = true).
     unfold surface_syntax. fold surface_syntax.
     rewrite H13. rewrite H14. rewrite H16. auto. 
  exists (Config CT (Container (If t1 t2 t3) fs lb sf) ctns h); auto.
  + subst. exists (Config CT (Container (If v t2 t3) fs lb sf) ctns h). auto.

- inversion H_config. inversion H7.  subst. inversion H15. inversion H1. subst.  
  apply surface_syntax_is_hole_free in H12.   apply surface_syntax_is_hole_free in H13.
  assert (hole_free (Sequence t1 t2) = true). unfold  hole_free. fold hole_free.
  rewrite H12. rewrite H13.  auto. 
  exists (Config CT (Container (Sequence t1 t2) fs lb sf) ctns h); auto.
- assert (value (ObjId o)). auto. 
  apply value_is_hole_free in H. 
  assert (hole_free (ObjId o) = true). unfold  hole_free. fold hole_free. auto. 
  exists (Config CT (Container (ObjId o) fs lb sf) ctns h); auto.
- inversion H_config. inversion H7.  subst. inversion H15. inversion H1. subst.  
  apply value_is_hole_free in H11. 
  assert (hole_free (v_l t l) = true). unfold  hole_free. fold hole_free. auto. 
  exists (Config CT (Container (v_l t l) fs lb sf) ctns h); auto.
- inversion H_config. inversion H7.  subst. inversion H15. inversion H1. subst.  
  apply value_is_hole_free in H11. 
  assert (hole_free (v_opa_l t l) = true). unfold  hole_free. fold hole_free. auto. 
  exists (Config CT (Container (v_opa_l t l) fs lb sf) ctns h); auto.
-   inversion H_config. inversion H7. subst. destruct H19 with fs. auto. 
-   inversion H_config. inversion H7. subst. destruct H20 with fs. auto.
Qed. 
Hint Resolve value_progress. 

Lemma excluded_middle_value : forall t,
  (value t) \/ ~ value t.
Proof with eauto.
  intros.
  induction t; try (left; auto; fail); try (right; intro contra; inversion contra;fail).
  destruct IHt. left; auto. right. intro contra. inversion contra. intuition. 
  destruct IHt. left; auto. right. intro contra. inversion contra. intuition. 
Qed.
Hint Resolve excluded_middle_value.
  
Lemma exclude_middle_unlabelOpaque : (forall t, ((exists v, value v /\ t = unlabelOpaque v) 
        \/ (forall v, t <> unlabelOpaque v) 
          \/ (exists t', t = unlabelOpaque t' /\ ~ value t'))).
Proof with eauto.
  intro t. induction t; try (right; left; intro v0; intro contra; inversion contra; fail).
  pose proof (excluded_middle_value t). destruct H. left. exists t. auto.
  right. right. exists t. auto.
Qed. Hint Resolve exclude_middle_unlabelOpaque.

Lemma heap_consist_ct : forall h o ct cls F lo ,
  wfe_heap ct h -> 
  lookup_heap_obj h o = Some (Heap_OBJ cls F lo) ->
  exists cn field_defs method_defs, ct cn = Some cls /\ cls = (class_def cn field_defs method_defs).
Proof with auto.
  intros. induction H. 
  - inversion H0.
  - unfold lookup_heap_obj in H0.
     case_eq (beq_oid o o0).   intros. rewrite H in H0.  rewrite H6 in H0. inversion H0. 
      rewrite -> H8 in H3. inversion H3.   
      exists cn. exists  field_defs. exists method_defs. 
      split. auto. auto. intro. rewrite H in H0. rewrite H6 in H0.
      fold lookup_heap_obj in H0. apply IHwfe_heap. auto. 
Qed.
Hint Resolve heap_consist_ct.

Lemma field_val_of_heap_obj : forall h o CT cls_def F lo cls' fields,
  field_wfe_heap CT h -> 
  wfe_heap CT h ->
  lookup_heap_obj h o  = Some (Heap_OBJ cls_def F lo) ->
  fields = (find_fields cls_def) ->
  forall f, type_of_field fields f = Some cls' -> exists v, F(f) = Some v.

Proof with auto.
  intros. inversion H. 
  assert (exists cn field_defs method_defs, CT cn = Some cls_def 
                    /\ cls_def = (class_def cn field_defs method_defs)).

apply heap_consist_ct with (h:=h) (o:=o) (ct:=CT) 
        (cls:=cls_def) (F:=F) (lo:=lo). auto. auto.
destruct H7 as [cls_name]. destruct H7 as [field_defs]. 
destruct H7 as [method_defs]. destruct H7. 

destruct H4 with (o:=o) (cls_def:=cls_def) (lo:=lo)
    (method_defs:=method_defs) (field_defs:=field_defs) 
    (f:=f) (cls':=cls') (F:=F) (cls_name:=cls_name).
auto. auto. auto.  auto. rewrite H8 in H2. unfold find_fields in H2.
rewrite H2 in H3. auto. exists x. apply H9.
Qed.
Hint Resolve field_val_of_heap_obj.

Lemma field_consist_typing : forall CT v h o cls_def F f lb field_cls_name cls_name field_defs method_defs,
  wfe_heap CT h ->
  field_wfe_heap CT h -> 
  lookup_heap_obj h o = Some (Heap_OBJ cls_def F lb) -> 
  cls_def = class_def cls_name field_defs method_defs ->
  type_of_field field_defs f = Some field_cls_name ->
  F f = Some v ->
     ( v = null \/ 
          ( exists o' field_defs0 method_defs0 field_cls_def F' lo, 
           v = (ObjId o') 
          /\ field_cls_def = (class_def field_cls_name field_defs0 method_defs0) 
          /\ lookup_heap_obj h o' = Some (Heap_OBJ field_cls_def F' lo) 
          /\ CT field_cls_name = Some field_cls_def 
          )
      ).
Proof with auto. 
  intros. inversion H0.
  assert (exists v : tm,
       F f = Some v /\
       (v = null \/
        (exists
           (o' : oid) (F' : FieldMap) (lx : Label) (field_defs0 : list field) 
         (method_defs0 : list method_def),
           v = ObjId o' /\
           lookup_heap_obj h o' =
           Some (Heap_OBJ (class_def field_cls_name field_defs0 method_defs0) F' lx) /\
           CT field_cls_name = Some (class_def field_cls_name field_defs0 method_defs0)))).
  apply H5 with (o:=o) (cls_def:=cls_def) (F:=F) (cls_name:=cls_name)
       (lo:=lb) (method_defs:=method_defs) (field_defs:=field_defs); auto. 

assert (exists cn field_defs method_defs, CT cn = Some cls_def /\ cls_def = (class_def cn field_defs method_defs)).
apply heap_consist_ct with (h:=h) (o:=o) (ct:=CT) (cls:=cls_def) (F:=F) (lo:=lb). 
auto. auto. 
destruct H8 as [cls_name0]. destruct H8 as [field_defs0]. destruct H8 as [method_defs0]. destruct H8. 
rewrite H2 in H9. inversion H9. auto.
destruct H8 as [v']. destruct H8. rewrite H4 in H8. inversion H8. 
destruct H9. left. auto. right. 
destruct H9 as [o']. destruct H9 as [F']. destruct H9 as [lx]. 
destruct H9 as [field_defs0]. destruct H9 as [method_defs0].
remember  (class_def field_cls_name field_defs0 method_defs0) as field_cls_def.
exists o'.  exists field_defs0. exists method_defs0. exists field_cls_def. exists F'. exists lx. 
destruct H9.  split; auto. 
Qed.
Hint Resolve  field_consist_typing.


Lemma value_typing_invariant_gamma : forall CT gamma h v T gamma', 
  value v ->
  tm_has_type CT gamma h v T -> 
  tm_has_type CT gamma' h v T .
Proof with eauto. 
 intros CT gamma h v T gamma'. intro H_v. intro typing. generalize dependent T. 
 induction H_v; intro T; intro typing; try (inversion typing; auto; fail).
 -  inversion typing.   
 apply T_ObjId with (cls_def:=cls_def); auto.
Qed.
Hint Resolve value_typing_invariant_gamma. 


Lemma compare_oid_nat : forall n1 n2, 
  compare_oid (OID n1) (OID n2) = true ->
  n1 > n2.
Proof. 
    intros. unfold compare_oid in H.
  destruct n1. destruct n2. 
  - inversion H.
  - inversion H. 
  - case_eq (gt_dec (S n1) n2 ).
      + intros. auto. 
      + intros. rewrite H0 in H. inversion H.
Qed.
Hint Resolve compare_oid_nat. 

Lemma beq_OID_not_equal : forall n n1, n <> n1 -> beq_oid (OID n) (OID n1) = false.
Proof. 
  intro n.   unfold beq_oid. 
    induction n. destruct n1. 
    - intuition. 
    - intuition.
    - intros. destruct n1. intuition. 
       simpl in H. simpl. apply IHn. 
       intro contra.  rewrite contra in H. intuition. 
Qed. 
Hint Resolve beq_OID_not_equal. 

Lemma oid_trans : forall n1 n2 n3, 
  n1 > n2 ->
  compare_oid (OID n2) (OID n3) = true -> 
  n1 > n3. 
Proof. 
  intros. apply compare_oid_nat in H0. intuition. 
Qed.
Hint Resolve  oid_trans.

Lemma fresh_heap : forall h h' CT  n0 ho0, 
    wfe_heap CT h ->
    h = ((OID n0) , ho0) :: h' ->
    (forall n, n > n0 -> lookup_heap_obj h (OID n) = None).
  Proof.
    intros. generalize dependent h'. generalize dependent n.  
        generalize dependent n0.     generalize dependent ho0.
    induction h. intros.  inversion H0.
    intros. inversion H. inversion H0. 
    unfold  lookup_heap_obj. 
     assert (beq_oid (OID n) (OID n0) = false).
    apply beq_OID_not_equal with (n:=n) (n1:=n0) .
    intro contra.  rewrite contra in H1. intuition. rewrite H10.
    fold lookup_heap_obj. rewrite <- H12. 
    destruct H3. inversion H2. rewrite H3. auto.
    destruct H3 as [o']. destruct H3 as [ho']. destruct H3 as [h''].
   induction o'.
    apply IHh with (ho0:=ho') (n0:=n1) (h':=h''). inversion H2. apply H4. auto.
    inversion H2. rewrite H11 in H14. inversion H14. destruct H3. 
    rewrite <- H16 in H13. 
    apply oid_trans with (n1:=n) (n2:=n0) (n3:=n1). auto. auto. auto.
    destruct H3. inversion H2. auto.
  Qed.
Hint Resolve fresh_heap.  

Lemma heap_lookup : forall h h' CT o ho, 
    wfe_heap CT h ->
    h = (o, ho) :: h' ->
    lookup_heap_obj h' o = None.
  Proof.
    intros. induction o. inversion H. rewrite <- H2 in H0. inversion H0.
    subst.  inversion H1. subst. rename h0 into h. destruct H2. 
    rewrite H0. auto. 
    destruct H0 as [o']. destruct H0 as [ho']. destruct H0 as [h'']. destruct H0.  induction o'. 
    apply compare_oid_nat in H2. apply fresh_heap with h'' CT n0 ho'; auto. 
  Qed.
  Hint Resolve heap_lookup.
  



Lemma lookup_updated_heap_none : forall h o1 o ho,
      o <> o1 ->
      lookup_heap_obj h o1 = None ->
      lookup_heap_obj (update_heap_obj h o ho) o1 = None.
Proof.
  intros.
  induction h.
  unfold update_heap_obj. unfold lookup_heap_obj. auto. 
  induction a. case_eq (beq_oid o o0). intro. unfold update_heap_obj. rewrite H1. 
  unfold lookup_heap_obj in H0. apply beq_oid_equal in H1. 
  unfold lookup_heap_obj. rewrite <- H1 in H0. 
  case_eq (beq_oid o1 o). intro. rewrite H2 in H0. inversion H0.
  intro. rewrite H2 in H0. fold lookup_heap_obj. fold lookup_heap_obj in H0. auto. 
  intro. unfold update_heap_obj. rewrite H1. 
  fold update_heap_obj. unfold lookup_heap_obj in H0. 
  case_eq ( beq_oid o1 o0). intro. rewrite H2 in H0. inversion H0.
  intro.  rewrite H2 in H0. fold lookup_heap_obj in H0. apply IHh in H0. 
  unfold lookup_heap_obj.  rewrite H2. fold lookup_heap_obj. auto. 
Qed. Hint Resolve  lookup_updated_heap_none.



Lemma lookup_updated_heap_equal : forall cls F lb o h cls1 F1 lb1 F' o1 lb',
    lookup_heap_obj h o = Some (Heap_OBJ cls F lb) ->
    lookup_heap_obj h o1 = Some (Heap_OBJ cls1 F1 lb1) -> 
    (lookup_heap_obj
       (update_heap_obj h o (Heap_OBJ cls F' lb')) o1  = 
     Some (Heap_OBJ cls1 F1 lb1)) \/ 
    (lookup_heap_obj (update_heap_obj h o (Heap_OBJ cls F' lb')) o1  = 
     Some (Heap_OBJ cls F' lb') /\ beq_oid o1 o = true).
Proof.
  intros.
  induction h. 
  unfold lookup_heap_obj in H0. inversion H0.  induction a.
  case_eq (beq_oid o o0). intro.
  unfold  update_heap_obj. rewrite H1.
  case_eq (beq_oid o1 o). intro.
  unfold lookup_heap_obj. rewrite H2.
  unfold lookup_heap_obj in H0. apply beq_oid_equal in H2. rewrite H2 in H0.
  rewrite H1 in H0.
  unfold lookup_heap_obj in H. rewrite H1 in H. rewrite H0 in H. inversion H. subst.  
  right. auto. 
  intro. unfold lookup_heap_obj. rewrite H2. fold lookup_heap_obj.
  unfold lookup_heap_obj in H0. apply beq_oid_equal in H1. rewrite <-H1 in H0.
  rewrite H2 in H0. fold lookup_heap_obj in H0. rewrite H0. 
  left. auto.
  intro. 
  case_eq (beq_oid o1 o0). intro.
  unfold update_heap_obj. rewrite H1. fold update_heap_obj.
  unfold lookup_heap_obj. rewrite H2.
  unfold lookup_heap_obj in H0.    rewrite H2 in H0. rewrite H0.
  left. auto. 
  intro.  unfold lookup_heap_obj in H. 
  unfold lookup_heap_obj in H0. 
  rewrite H1 in H. fold lookup_heap_obj in H.
  rewrite H2 in H0. fold lookup_heap_obj in H0.
  unfold update_heap_obj.
  unfold lookup_heap_obj.  rewrite H1. rewrite H2. 
  fold lookup_heap_obj.
  fold update_heap_obj. apply IHh; auto.
Qed. Hint Resolve lookup_updated_heap_equal. 



Lemma lookup_heap_obj_two_cases : forall h o, 
  ((exists cls F lb, lookup_heap_obj h o = Some (Heap_OBJ cls F lb) ) 
      \/ (lookup_heap_obj h o = None)).
Proof.
  intro h0.
  induction h0.  right. unfold lookup_heap_obj. auto. 
  intro o0. induction a. case_eq ( beq_oid o0 o). unfold lookup_heap_obj.  intro. unfold lookup_heap_obj. rewrite H.
  rename h into ho. induction ho.
  left. exists c. exists f. exists l. auto. 
  intro. unfold lookup_heap_obj. rewrite H.
  fold lookup_heap_obj. apply IHh0.
Qed. Hint Resolve  lookup_heap_obj_two_cases.


  
Lemma field_value : forall h o cls F lb f t' CT cls' gamma,  
    wfe_heap CT h -> field_wfe_heap CT h ->
    Some (Heap_OBJ cls F lb) = lookup_heap_obj h o ->
    F f = Some t' ->
    tm_has_type CT gamma h (FieldAccess (ObjId o) f)
                (classTy cls') ->
    ( t' = null \/ exists o',  t' = ObjId o').
Proof.
  intros h o cls F lb f t' CT cls' gamma. intro H_wfe_heap. intro H_wfe_fields. 
  intro Hy. intro Hy_Field. intro H_typing.  inversion H_typing. inversion H2. 
  subst.  destruct H16 as [F']. destruct H as [lo]. rewrite H in Hy. inversion Hy. subst.
  destruct H15 as [field_defs]. destruct H0 as [method_defs].
  rewrite <- H6 in H11. inversion H11. subst.
  inversion H_wfe_fields. subst.
  destruct H0 with o (class_def clsT field_defs method_defs) F' clsT lo method_defs field_defs
                 f cls'; auto. destruct H1. rewrite H1 in Hy_Field. inversion Hy_Field. subst. 
  destruct H3. left. auto. 
  destruct H3 as [o']. destruct H3 as [F0]. destruct H3 as [lx].
  destruct H3. destruct H3. destruct H3. right. exists o'. auto.
Qed. Hint Resolve   field_value. 


Lemma fs_pro_double : forall (t1 : tm) (t2 : tm) (fs : list tm),
  t1 :: t2 :: fs <> fs.
Proof. intros t1 t2 fs.  generalize dependent t1. generalize dependent t2. induction fs. 
  intros.  intro contra. inversion contra. 
  intros.  intro contra. inversion contra. assert (t2 :: a :: fs <> fs). apply IHfs.
subst. rewrite H1 in H. auto. Qed. 

Lemma fs_pro_double_false : forall (t1 : tm) (t2 : tm) (fs : list tm),
  fs = t1 :: t2 :: fs -> False.
Proof. intros t1 t2 fs.  generalize dependent t1. generalize dependent t2. induction fs. 
  intros.  inversion H. 
  intros.  assert (fs = t2 :: a :: fs -> False). apply IHfs. inversion H. subst. apply H0 in H3. 
 auto. Qed. 


Lemma string_eq : forall n1 n2, n1 = n2 -> Id n1 = Id n2.
Proof with eauto.
  intros. rewrite -> H. auto.
Qed. 

Theorem beq_nat_true: forall n m,
  beq_nat n m = true -> n = m.
Proof.
  intros n. induction n.
    intros. destruct m. 
      reflexivity.  inversion H.
    intros. destruct m. 
      inversion H. simpl in H. apply f_equal. apply IHn in H. apply H.
Qed. 






Lemma beq_equal_oid : forall x x', x = x' -> beq_oid x x' = true.
Proof.
   intros. 
   destruct x. destruct x'. rewrite H.
  apply beq_oid_same.
Qed.

Lemma beq_equal : forall x x', beq_id x x' = true -> x' = x.
Proof.
   intros. unfold beq_id in H. 
  destruct x. destruct x'.  f_equal.
 case_eq (string_dec s s0). 
  - intros. rewrite -> e. auto.
  - intro. intro. rewrite -> H0 in H. inversion H. 
Qed.


Lemma beq_oid_not_equal : forall o o', o <> o' -> beq_oid o o' = false.
  Proof. 
      intros. destruct o. destruct o'.
      assert (n <> n0). intro contra. 
      rewrite contra in H. intuition. 
      apply beq_OID_not_equal.
      auto. 
  Qed.  


Lemma fresh_heap_nil : forall h CT h' n0 ho0, 
    wfe_heap CT h ->
    h = ((OID n0) , ho0) :: h' ->
    h' = nil ->
    forall n, n > n0 -> lookup_heap_obj h (OID n) = None.
Proof.
   intros. unfold  lookup_heap_obj. rewrite H0. 
     assert (beq_oid (OID n) (OID n0) = false).
    apply beq_OID_not_equal with (n:=n) (n1:=n0) .
    intro contra.  rewrite contra in H2. intuition. rewrite H1.  rewrite H3. auto.  
Qed. 


Lemma nat_compare_oid : forall n1 n2, 
  n1 > n2 -> compare_oid (OID n1) (OID n2) = true.
Proof. 
  intros. unfold compare_oid.
  destruct n1. destruct n2. 
  - inversion H.
  - inversion H. 
  - case_eq (gt_dec (S n1) n2 ).
      + intros. auto. 
      + intros. intuition.
Qed. 


Lemma gt_trans : forall n1 n2 n3, 
  n1 > n2 ->
  n2 > n3 ->
  n1 > n3. 
Proof. 
  intros. intuition.
Qed.  



Lemma fresh_oid_heap : forall h CT o,
    wfe_heap CT h ->
    o = (get_fresh_oid h) -> 
    lookup_heap_obj h o = None.
Proof. intros. generalize dependent h. induction h. 
           - unfold get_fresh_oid. auto.
           - intros. unfold get_fresh_oid in H0. 
              induction a. induction o0.   
              rewrite H0.
              apply fresh_heap with (h:=((OID n, h0) :: h)) (h':=h) (CT:=CT)
                         (n0:=n) (ho0:=h0).
              auto. auto. intuition. 
Qed. 


Lemma some_eq : forall cls_def F lo cls_def' F' lo',
  Some (Heap_OBJ cls_def F lo) = Some (Heap_OBJ cls_def' F' lo') ->
  cls_def = cls_def' /\ F = F'.
Proof with auto. 
  intros. inversion H. auto. 
Qed.  




Lemma nil_heap_no_obj : forall ho h o,
  nil = update_heap_obj h o ho ->
  h = nil.
Proof.
  intros. induction h. auto. inversion H. 
  case a in H1. 
  case_eq (beq_oid o o0).  intro.  rewrite H0 in H1. inversion H1. 
   intro.  rewrite H0 in H1. inversion H1. 
Qed. 


(*well organized heap is preserved when the heap is extended with a fresh oid*)
Lemma extend_heap_preserve_order : forall CT h h' o c field_defs method_defs lb,
    wfe_heap CT h->
    o = get_fresh_oid h ->
    lookup_heap_obj h o = None -> 
    Some (class_def c field_defs method_defs) = CT c ->
     h' = add_heap_obj h o (Heap_OBJ (class_def c field_defs method_defs)
          (init_field_map field_defs empty_field_map)
          lb) ->  wfe_heap CT h'.
  Proof.
    intros. 
    remember (class_def c field_defs method_defs) as cls_def.
    remember  (init_field_map field_defs empty_field_map) as F.
    apply heap_wfe with (h:=h) (o:=o) 
        (cls_def:=cls_def) (F:=F) (cn:=c) (ho:=(Heap_OBJ cls_def F lb))
        (lo:=lb) (method_defs:=method_defs) (field_defs:=field_defs) ;auto.
        intros. induction h. left. auto. right.
        unfold  get_fresh_oid in H0. 
        induction a. induction o0. 
        exists (OID n). exists h0. exists h. 
        rewrite H0. split. auto. apply nat_compare_oid. intuition. 
  Qed.  

Lemma extend_heap_preserve_field_wfe : forall CT h h' o c field_defs method_defs lb,
    field_wfe_heap CT h -> 
    o = get_fresh_oid h ->
    lookup_heap_obj h o = None -> 
    Some (class_def c field_defs method_defs) = CT c ->  
     h' = add_heap_obj h o (Heap_OBJ (class_def c field_defs method_defs)
          (init_field_map field_defs empty_field_map)
          lb) ->  field_wfe_heap CT h'.
  Proof. 
    intros. 
    remember (class_def c field_defs method_defs) as cls_def.
    remember  (init_field_map field_defs empty_field_map) as F.
    auto.

    assert (        (forall o cls_def F cls_name lo method_defs field_defs,
        lookup_heap_obj  h' o = Some (Heap_OBJ cls_def F lo) ->
        Some cls_def  = CT cls_name ->
        cls_def = class_def cls_name field_defs method_defs ->
        (forall f cls', type_of_field field_defs f = Some cls' -> 
                exists v, F(f) = Some v
                 /\ (v= null  \/ 
                          ( exists o' F' lx field_defs0 method_defs0, v = ObjId o' 
                                  /\ lookup_heap_obj  h' o' = Some (Heap_OBJ (class_def cls' field_defs0 method_defs0) F' lx)
                                    /\ CT cls' = Some (class_def cls' field_defs0 method_defs0)
                          ) ) 
        ))).
      intros. 
   destruct h'. intros. inversion H4. 
   induction h0. 
    unfold add_heap_obj in H3.  inversion H3. 
  case_eq (beq_oid o0 o1).
  intro. 
  unfold  lookup_heap_obj in H4. rewrite H8 in H4. inversion H4. 
  rewrite H10 in H13. inversion H13. rewrite <-H15. 
  exists null. split. 
  assert (forall f, type_of_field field_defs f = Some cls' ->
  F f = Some null).
  apply empty_fields. auto. apply H12. 
  rewrite <- H14 in H6.  rewrite Heqcls_def in H6. inversion H6. auto. 
  left. auto. 
  intro.  
     unfold  lookup_heap_obj in H4. rewrite H8 in H4. fold  lookup_heap_obj in H4.

    inversion H. destruct H12 with (o:=o0) (cls_def:=cls_def0) (F:=F0) (cls_name:=cls_name)
          (lo:=lo) (method_defs:=method_defs0) (field_defs:=field_defs0) (f:=f) (cls':=cls').
   rewrite <- H11. auto. auto. auto. auto. auto. exists x.
   destruct H15. split. auto. destruct H16. auto. right. 
   destruct H16 as [o'].    destruct H16 as [F'].    destruct H16 as [lx]. 
   destruct H16 as [field_defs'].    destruct H16 as [method_defs']. 
   exists o'. exists F'. exists lx. exists field_defs'. exists method_defs'.
  destruct H16. split. auto. destruct H17. 
   assert (o' <> o). intro contra. rewrite <- contra in H1. 
   rewrite H1 in H17. inversion H17.  apply beq_oid_not_equal  in H19.
  unfold lookup_heap_obj.  rewrite H19. fold lookup_heap_obj. auto. auto.
  apply heap_wfe_fields. auto.
Qed. 


Lemma object_write_preserve_heap_order : 
  forall CT o h h' h'' F F' cls_def lb lb'  o0 ho0,
  wfe_heap CT h ->
  h = (o0 , ho0) :: h' ->
  Some (Heap_OBJ cls_def F lb) = lookup_heap_obj h' o ->
  h'' = (update_heap_obj h' o
           (Heap_OBJ cls_def F' lb')) ->
  (h'' = nil \/ (exists o1 ho1 h1, h'' = (o1 , ho1) :: h1 /\ compare_oid o0 o1= true) ).
Proof. 
  intros. generalize dependent ho0. generalize dependent o0.  generalize dependent h'.
generalize dependent h''.
induction h. 
  intros. inversion H0.
  destruct h'. intros. 
  unfold update_heap_obj in H2.  left. auto. 
  right. 
  induction a. induction h0. 

case_eq (beq_oid o o2). intro. 
unfold update_heap_obj in H2.  rewrite H3 in H2. 
exists o. exists (Heap_OBJ cls_def F' lb'). exists h'. 
split; auto. inversion H. destruct H5. inversion H4.
rewrite H15 in H0. rewrite H5 in H0. inversion H0.

inversion H0. subst. inversion H4. 
destruct H5 as [o']. destruct H2 as [ho']. destruct H2 as [h''].
destruct H2. rewrite H2 in H10. inversion H10.
apply beq_oid_equal in H3. subst. auto.   

(*beq_oid o o2 = false*)
intro. unfold update_heap_obj in H2. rewrite H3 in H2. fold update_heap_obj in H2. 
unfold lookup_heap_obj in H1.  rewrite H3 in H1. fold lookup_heap_obj in H1. 

destruct IHh with (h'':=update_heap_obj h' o (Heap_OBJ cls_def F' lb')) 
    (h':=h') (o0:= o2) (ho0:=h0). inversion H. inversion H4. auto. 
auto. auto.  inversion H0. auto. exists o2. exists h0. exists (update_heap_obj h' o (Heap_OBJ cls_def F' lb')).
split. auto. assert (h'=nil). apply nil_heap_no_obj with (ho:=(Heap_OBJ cls_def F' lb')) (o:=o).
auto. rewrite H5 in H1. inversion H1. 

exists  o2. exists h0. exists (update_heap_obj h' o (Heap_OBJ cls_def F' lb')). split. auto. 
inversion H0. rewrite <- H6. inversion H.  inversion H5. destruct H9.
rewrite H19 in H8.  rewrite H9 in H8. inversion H8. 

destruct H9 as [o']. destruct H9 as [ho']. destruct H9. destruct H9.
rewrite H19 in H8. rewrite H8 in H9.  inversion H9. auto. 
Qed. 


Lemma field_write_preserve_wfe_heap : 
  forall CT o h h' i F F' cls_def cls' lb lb' clsT field_defs method_defs,
  wfe_heap CT h ->
(*  wfe_stack CT gamma h s -> *)
  Some (Heap_OBJ cls_def F lb) = lookup_heap_obj h o ->
  type_of_field (find_fields cls_def) i = Some cls' ->
  cls_def = class_def clsT field_defs method_defs ->
  Some cls_def = CT clsT ->
  h' = (update_heap_obj h o
           (Heap_OBJ cls_def F' lb')) ->
  wfe_heap CT h'.

Proof.
  intros CT o h h' i F F' cls_def cls' lb lb' clsT field_defs method_defs.
  intro wfe_h.  intro Ho. intro Htyf. intro Hcls_def. intro Hct.
  intro Hy.

generalize dependent h.  induction h'. 
intros. 
apply nil_heap_no_obj with (ho:=(Heap_OBJ cls_def F' lb')) (h:=h) (o:=o) in Hy.
rewrite Hy in Ho. inversion Ho.

intros. destruct h.  inversion Ho. 
induction a. induction h.
case_eq (beq_oid o o1). 
(*beq_oid o o1 = true  *)
unfold update_heap_obj in Hy. intro. rewrite H in Hy. inversion Hy. 
inversion wfe_h.
apply heap_wfe with (h':= ((o, (Heap_OBJ cls_def F' lb')) :: h0)) 
        (o:=o) (cls_def:=cls_def0) (F:=F') (cn:=cn) 
        (h:=h0) 
        (ho:=(Heap_OBJ cls_def F' lb'))
        (lo:=lb') (method_defs:=method_defs0) (field_defs:=field_defs0); auto.
inversion H0. auto. apply beq_oid_equal in H. rewrite H. rewrite H12. auto.
inversion H0. auto.
unfold lookup_heap_obj in Ho. rewrite H in Ho. fold lookup_heap_obj in Ho. inversion Ho.
inversion H0. rewrite <- H12 in H14. rewrite H6 in H14. inversion H14. auto.
(*beq_oid o o1 = false  *)
unfold update_heap_obj in Hy. intro. rewrite H in Hy. fold update_heap_obj in Hy.  inversion Hy. 
inversion wfe_h.
apply heap_wfe with (h':=((o1, h) :: update_heap_obj h0 o (Heap_OBJ cls_def F' lb'))) 
        (o:=o1) (cls_def:=cls_def0) (F:=F0) (cn:=cn) 
        (h:=update_heap_obj h0 o (Heap_OBJ cls_def F' lb')) 
        (ho:=h) (lo:=lo) (method_defs:=method_defs0) (field_defs:=field_defs0).
auto. inversion H0. destruct H4. rewrite H4. left. auto. right.
destruct H4 as [o']. destruct H4 as [ho']. destruct H4 as [h'']. destruct H4. 
remember (update_heap_obj h2 o (Heap_OBJ cls_def F' lb')) as h3. 
assert (  (h3 = nil \/ (exists o1 ho1 h1, h3 = (o1 , ho1) :: h1 /\ compare_oid o0 o1= true) )).
rewrite H1.  rewrite H12. 
apply object_write_preserve_heap_order with (CT:=CT) (o:=o) 
    (h:=(o2, ho) :: h2) (h':=h2) (h'':=h3) (F:=F) (F':=F') 
    (cls_def:=cls_def) (lb:=lb) (lb':=lb')  (o0:=o2) (ho0:=ho).
rewrite <-H0. auto. auto. 
unfold  lookup_heap_obj in Ho. rewrite H in Ho. fold  lookup_heap_obj in Ho. 
rewrite <- H14. auto. auto. destruct H15.  rewrite H15 in  Heqh3.
apply nil_heap_no_obj in Heqh3. 
unfold  lookup_heap_obj in Ho. rewrite H in Ho. fold  lookup_heap_obj in Ho. 
rewrite H14 in Ho. rewrite Heqh3 in Ho. inversion Ho. auto. 
rewrite <- H12. rewrite <- H1. auto.   

rewrite <- H3. 
apply IHh' with (h:=h0). inversion H0. auto. 
unfold lookup_heap_obj in Ho. rewrite H in Ho. fold lookup_heap_obj in Ho. auto.
auto. inversion H0. auto. auto. auto. 
Qed.  


Lemma  lookup_updated : forall o ho h h' ho',
    h' = update_heap_obj h o ho ->
    Some ho' = lookup_heap_obj h o ->
    Some ho = lookup_heap_obj h' o. 
  Proof. 
    intros. generalize dependent h. induction h'.
   - intros. apply nil_heap_no_obj in H. rewrite H in H0. inversion H0.
   - intro h. intro.  intro. induction a.
      destruct h. inversion H0. 
      induction h. 
      case_eq (beq_oid o o1).  intro.  
      unfold  update_heap_obj in H. rewrite H1 in H. inversion H.
      unfold lookup_heap_obj.       
      assert (beq_oid o o=true). apply beq_oid_same. rewrite H2.  auto.

      intro. unfold  update_heap_obj in H. rewrite H1 in H. fold update_heap_obj in H.  
      inversion H. 
      unfold lookup_heap_obj.        rewrite H1.  fold lookup_heap_obj.
      rewrite <- H5.  apply IHh' with (h:=h1). auto. 
      unfold lookup_heap_obj in H0.        rewrite H1 in H0.  fold lookup_heap_obj in H0. auto.
Qed. 

Lemma  lookup_updated_not_affected : forall o ho h h' o' ho',
    h' = update_heap_obj h o ho ->
    o' <> o ->
    Some ho' = lookup_heap_obj h o' ->
    Some ho' = lookup_heap_obj h' o'.
  Proof. 
    intros. generalize dependent h. induction h'.
   - intros. apply nil_heap_no_obj in H. rewrite H in H1. inversion H1.
   - intro h. intro.  intro. induction a.
      destruct h. inversion H. 
      induction h. 
      case_eq (beq_oid o o1).  intro.  
      unfold  update_heap_obj in H. rewrite H2 in H. inversion H.
      unfold lookup_heap_obj.
      assert (beq_oid o' o = false).  apply beq_oid_not_equal. auto. 
      rewrite H3.       fold lookup_heap_obj. 
      unfold  lookup_heap_obj in H1. apply beq_oid_equal in H2. rewrite H2 in H3. 
      rewrite H3 in H1. fold lookup_heap_obj in H1. auto.  

      intro. unfold update_heap_obj in H. rewrite H2 in H. fold update_heap_obj in H.  
      case_eq (beq_oid o' o1).
      intro. unfold lookup_heap_obj in H1. rewrite H3 in H1.  
      inversion H. unfold lookup_heap_obj. rewrite H3. auto. 

      intro. unfold lookup_heap_obj in H1. rewrite H3 in H1.  fold lookup_heap_obj in H1.
      inversion H.   unfold lookup_heap_obj. rewrite H3.  fold lookup_heap_obj.
   
      rewrite <- H7. apply IHh' with (h:=h1). auto. auto.  
Qed. 

Lemma  lookup_updated_not_affected_reverse : forall o ho h h' o' ho',
    h' = update_heap_obj h o ho ->
    o' <> o ->
    Some ho' = lookup_heap_obj h' o' ->
    Some ho' = lookup_heap_obj h o'.
  Proof. 
    intros. generalize dependent h. induction h'.
   - intros. apply nil_heap_no_obj in H. inversion H1.
   - intro h. intro.  induction a.
      destruct h. inversion H. 
      induction h. 
      case_eq (beq_oid o o1).  intro.  
      unfold  update_heap_obj in H. rewrite H2 in H. inversion H.
      unfold lookup_heap_obj.
      assert (beq_oid o' o = false).  apply beq_oid_not_equal. auto.
      apply beq_oid_equal in H2. rewrite H2 in H3.   
      rewrite H3.       fold lookup_heap_obj. 
      unfold  lookup_heap_obj in H1. rewrite <-H2 in H3. rewrite H4 in H1. 
      rewrite H3 in H1. fold lookup_heap_obj in H1. rewrite <-H6. auto.  

      intro. unfold update_heap_obj in H. rewrite H2 in H. fold update_heap_obj in H.  
      case_eq (beq_oid o' o1).
      intro. unfold lookup_heap_obj in H1. 
       inversion H. rewrite H5 in H1.  rewrite H3 in H1.    
       unfold lookup_heap_obj. rewrite H3. rewrite <- H6. auto. 

      intro. unfold lookup_heap_obj in H1. inversion H. rewrite H5 in H1. rewrite H3 in H1.  fold lookup_heap_obj in H1.
      unfold lookup_heap_obj. rewrite H3.  fold lookup_heap_obj.
   
      apply IHh' with (h:=h1). auto. auto.  
Qed. 


  Lemma field_write_preserve_field_wfe : forall CT gamma h h' o field_defs method_defs lb lb' v i F cls_def clsT cls',
    field_wfe_heap CT h -> 
    value v ->
    Some (Heap_OBJ cls_def F lb) = lookup_heap_obj h o ->
    type_of_field (find_fields cls_def) i = Some cls' ->
    cls_def = class_def clsT field_defs method_defs ->
    tm_has_type CT gamma h v (classTy cls') ->
    Some cls_def = CT clsT ->
    h' = (update_heap_obj h o
           (Heap_OBJ cls_def (fields_update F i v) lb')) ->
    field_wfe_heap CT h'.
Proof. 

    intros. 
    remember  (fields_update F i v) as F'. 

    assert (        (forall o cls_def F cls_name lo method_defs field_defs,
        lookup_heap_obj  h' o = Some (Heap_OBJ cls_def F lo) ->
        Some cls_def  = CT cls_name ->
        cls_def = class_def cls_name field_defs method_defs ->
        (forall f cls', type_of_field field_defs f = Some cls' -> 
                exists v, F(f) = Some v
                 /\ (v= null  \/ 
                          ( exists o' F' lx field_defs0 method_defs0, v = ObjId o' 
                                  /\ lookup_heap_obj  h' o' = Some (Heap_OBJ (class_def cls' field_defs0 method_defs0) F' lx)
                                    /\ CT cls' = Some (class_def cls' field_defs0 method_defs0)
                          ) ) 
        ))).
      intros. 
   destruct h'. intros. apply nil_heap_no_obj in H6. rewrite H6 in H1.  inversion H1.
  destruct h. inversion H1. induction h. induction h0. 

   assert (Some (Heap_OBJ cls_def F' lb') = lookup_heap_obj ((o2, h0) :: h') o).
   apply lookup_updated with (o:=o) (ho':= (Heap_OBJ cls_def F lb))
                                (ho:=(Heap_OBJ cls_def F' lb')) (h:=((o1, h) :: h1)) 
                                (h':=(o2, h0) :: h' ).
   auto. auto.
  (*if this is the element we updated*)
   case_eq (beq_oid o0 o). intro. apply beq_oid_equal in H12. 
   rewrite H12 in H7. 
   rewrite <- H11 in H7. inversion H7. rewrite <- H15. 
   unfold fields_update in HeqF'. rewrite HeqF'.
   (*If this is the field we updating*)
   case_eq (beq_id i f).  intro. 
   exists v. split. auto.
   inversion H0.
   rewrite <- H17 in H4. inversion H4. 
   right. 
   exists o3. 
   destruct H25 as [F'']. destruct H25 as [lx]. 
  destruct H24 as [field_defs''].   destruct H24 as [method_defs''].
  case_eq (beq_oid o3 o).  intro.
  apply beq_oid_equal in H26. rewrite H26.
  exists F'. exists lb'.  exists field_defs0. exists method_defs0.
  split. auto. split. auto. 
  inversion H7.  rewrite <- H28 in H9. rewrite H3 in H9. inversion H9.
  rewrite <- H32 in H10. rewrite H3 in H2. unfold find_fields in H2.
  apply beq_equal in H13. rewrite H13 in H10. rewrite H10 in H2.
  inversion H2. 
  rewrite H26 in H25. rewrite <- H1 in H25. inversion H25.
  rewrite <- H35 in H24. rewrite H3 in H24. inversion H24.
  rewrite <- H11. rewrite H3. rewrite H38. rewrite H33. 
  rewrite H32. rewrite H29. rewrite <- H30.  auto.

  inversion H7.  rewrite <- H28 in H9. rewrite H3 in H9. inversion H9.
  rewrite <- H32 in H10. rewrite H3 in H2. unfold find_fields in H2.
  apply beq_equal in H13. rewrite H13 in H10. rewrite H10 in H2.
  inversion H2.
  rewrite H26 in H25. rewrite <- H1 in H25. inversion H25.
  rewrite <- H35 in H24. rewrite H3 in H24. inversion H24.
  rewrite <- H38. rewrite H3 in H5. 
  rewrite <- H33. rewrite <- H32. auto.

  intro.
  assert (Some (Heap_OBJ cls_def1 F'' lx) = lookup_heap_obj ((o2, h0) :: h') o3).
  apply lookup_updated_not_affected with (h:=((o1, h) :: h1)) 
                  (h':=((o2, h0) :: h')) (ho:= (Heap_OBJ cls_def F' lb'))
                  (o':=o3) (o:=o) (ho':=(Heap_OBJ cls_def1 F'' lx)).
  auto.
  intro contra. rewrite contra in H26. 
   assert (beq_oid o o = true). apply beq_oid_same. rewrite H27 in H26.
  inversion H26. auto.
  exists F''. exists lx. exists field_defs''. exists method_defs''. split; auto.

  rewrite <- H14 in H9. rewrite H3 in H9.  inversion H9.
  apply beq_equal in H13. rewrite H13 in H10. 
  rewrite <- H30 in H10.  rewrite H3 in H2. unfold find_fields in H2. 
  rewrite H10 in H2. inversion H2. rewrite H24 in H27. 
  split; auto. rewrite H24 in H20. auto.

  rewrite <-H17 in H4. inversion H4.
  left. auto.
  rewrite <-H17 in H4. inversion H4.
  rewrite <-H18 in H4. inversion H4.
  rewrite <-H18 in H4. inversion H4. auto.


  subst; auto.
  inversion H4.
  subst; auto. 
  inversion H4. 
  
   (*If this is not the field we updating*)
  intro. 

  inversion H. destruct H17 with (o:=o) (cls_def:=cls_def) (F:=F)
                      (cls_name:=clsT) (lo:=lb) (method_defs:=method_defs)
                      (field_defs:=field_defs) (f:=f) (cls':=cls'0); auto. 
  rewrite <- H14  in H9. rewrite H3 in H9. inversion H9. auto.
  exists x. destruct H20. split; auto. destruct H21. left. auto. right.
  destruct H21 as [o'].   destruct H21 as [F'']. destruct H21 as [lx]. 
  destruct H21 as [field_defs''].   destruct H21 as [method_defs''].

  exists o'.
  case_eq (beq_oid o' o).  intro.
  destruct H21. destruct H23.
  apply beq_oid_equal in H22. rewrite H22 in H23. rewrite H23 in H1.
  inversion H1.
  exists F'. exists lb'. exists field_defs''. exists method_defs''. split; auto. 
  split. rewrite <- H26. rewrite H22. auto. auto.

  intro.
  assert (Some (Heap_OBJ (class_def cls'0 field_defs'' method_defs'') F'' lx)
                 = lookup_heap_obj ((o2, h0) :: h') o').
   apply lookup_updated_not_affected with (h:=((o1, h) :: h1)) 
                  (h':=((o2, h0) :: h')) (ho:= (Heap_OBJ cls_def F' lb'))
                  (o':=o') (o:=o) (ho':=(Heap_OBJ (class_def cls'0 field_defs'' method_defs'') F'' lx) ); auto.
   intro contra. rewrite contra in H22. assert (beq_oid o o = true). apply beq_oid_same.
   rewrite H23 in H22. inversion H22. destruct H21. destruct H23. auto.

  exists F''. exists lx. exists field_defs''. exists method_defs''. destruct H21.
  split; auto. destruct H24. auto. 

  (*if this is not the element we updated*)
  intro. inversion H. destruct H13 with (o:=o0) (cls_def:=cls_def0) (F:=F0)
                      (cls_name:=cls_name) (lo:=lo) (method_defs:=method_defs0)
                      (field_defs:=field_defs0) (f:=f) (cls':=cls'0); auto.
  assert (Some (Heap_OBJ cls_def0 F0 lo) = lookup_heap_obj ((o1, h) :: h1) o0).
  apply lookup_updated_not_affected_reverse with (o:=o) (o':=o0) (ho:=(Heap_OBJ cls_def F' lb'))
                    (h:=((o1, h) :: h1)) (h':=(o2, h0) :: h') (ho':=(Heap_OBJ cls_def0 F0 lo)). 
  auto. intro contra. rewrite contra in H12. assert (beq_oid o o = true). apply beq_oid_same. 
  rewrite H16 in H12. inversion H12. auto.  auto. 
  exists x. destruct H16.  destruct H17. split; auto.  split; auto. right. 

  destruct H17 as [o'].   destruct H17 as [F'']. destruct H17 as [lx]. 
  destruct H17 as [field_defs''].   destruct H17 as [method_defs'']. 

  exists o'.
  case_eq (beq_oid o' o).  intro.
  destruct H17. destruct H19.
  apply beq_oid_equal in H18. rewrite H18 in H19. rewrite H19 in H1.
  inversion H1.
  exists F'. exists lb'. exists field_defs''. exists method_defs''. split; auto. 
  split. rewrite <- H22. rewrite H18. auto. auto.

  intro.
  assert (Some (Heap_OBJ (class_def cls'0 field_defs'' method_defs'') F'' lx)
                 = lookup_heap_obj ((o2, h0) :: h') o').
   apply lookup_updated_not_affected with (h:=((o1, h) :: h1)) 
                  (h':=((o2, h0) :: h')) (ho:= (Heap_OBJ cls_def F' lb'))
                  (o':=o') (o:=o) (ho':=(Heap_OBJ (class_def cls'0 field_defs'' method_defs'') F'' lx) ); auto.
   intro contra. rewrite contra in H18. assert (beq_oid o o = true). apply beq_oid_same.
   rewrite H19 in H18. inversion H18. destruct H17. destruct H19. auto.
  exists F''. exists lx. exists field_defs''. exists method_defs''. destruct H17.
  split; auto. destruct H20. auto.   

   apply heap_wfe_fields. apply H7.
Qed.
Hint Resolve field_write_preserve_field_wfe.



(*  
Lemma wfe_oid : forall o ct gamma s h sigma cls_def cn, 
  sigma = SIGMA s h ->
  wfe_stack ct h s ->
  (tm_has_type ct gamma h (ObjId o) (classTy cn)) -> ct cn = Some cls_def 
    -> exists fieldsMap lb, lookup_heap_obj h o = Some (Heap_OBJ cls_def fieldsMap lb).
Proof with auto. 
  intros. inversion H1. rewrite H2 in H5. inversion H5. 
  rewrite <- H12. auto.
Qed.
*)

Lemma excluded_middle_opaqueLabel : forall e, (exists t, e = unlabelOpaque t) \/ (forall t, ~ (e = unlabelOpaque t)).
Proof with eauto.
  intros. case e; try (right; intro;  intros contra; inversion contra; fail). left. exists t. auto. 
Qed.


(* every value in the stack should be well-formed, which means that all values should point to null or valid Obj Id*)
(*
Lemma wfe_stack_value : forall gamma CT s h sigma v clsT, 
    sigma = SIGMA s h ->  wfe_heap CT h -> wfe_stack CT h s 
      -> (has_type CT gamma h v (classTy clsT))
      -> value v -> (v = null \/ 
                 ( exists o, v = ObjId o 
                              /\ (exists F lo field_defs method_defs , 
                                      lookup_heap_obj h o = Some (Heap_OBJ (class_def clsT field_defs method_defs) F lo)
                                      /\ (CT clsT = Some (class_def clsT field_defs method_defs))
                                   )
                  )    ).
Proof. 
    intros gamma CT s h sigma v clsT. intro. intro. intro.  intro. intro. 
    induction H3. right. exists o. split. auto. inversion H2. 
    destruct H10 as [F].     destruct H10 as [lo].    
    destruct H9 as [field_defs].    destruct H9 as [method_defs]. 
    exists F. exists lo. exists field_defs. exists method_defs.  
    split. rewrite <-H9. rewrite <- H10. auto. rewrite <- H9. auto.
    
    inversion H2. 

    left. auto. 
    inversion H2. inversion H2.  inversion H2. 
Qed.   
*)
(*
Lemma change_label_preserve_wfe : forall CT s h lb,
    wfe_heap CT h -> wfe_stack CT h s ->
    wfe_stack CT h (update_current_label s lb).
Proof. 
   intros. inversion H0. 
    - unfold update_current_label. apply main_stack_wfe with (s:=s) (lb:=lb1); auto.
    - subst.  unfold update_current_label. apply stack_wfe with (s':=s') (lb:=lb) (sf:=sf); auto.
        inversion H4.  apply stack_frame_wfe with (sf:=sf) (lb:=lb); auto. inversion H1. auto.
Qed.
*)



Lemma extend_heap_preserve_heap_wfe : forall CT h h' o c field_defs method_defs lb,
    wfe_heap CT h -> 
    o = get_fresh_oid h ->
    lookup_heap_obj h o = None -> 
    Some (class_def c field_defs method_defs) = CT c ->  
     h' = add_heap_obj h o (Heap_OBJ (class_def c field_defs method_defs)
          (init_field_map field_defs empty_field_map)
          lb) -> wfe_heap CT h'.
  Proof. 
    intros. 
    remember (class_def c field_defs method_defs) as cls_def.
    remember  (init_field_map field_defs empty_field_map) as F.
    apply heap_wfe with (h:=h) (o:=o) 
        (cls_def:=cls_def) (F:=F) (cn:=c) (ho:=(Heap_OBJ cls_def F lb))
        (lo:=lb) (method_defs:=method_defs) (field_defs:=field_defs) ;auto.
        intros. induction h. left. auto. right.
        unfold  get_fresh_oid in H0. 
        induction a. induction o0. 
        exists (OID n). exists h0. exists h. 
        rewrite H0. split. auto. apply nat_compare_oid. intuition. 
Qed.

(*
Lemma extend_heap_preserve_stack_wfe : forall CT s h h' o heap_obj,
    wfe_heap CT h -> 
    wfe_stack CT h s ->
    o = get_fresh_oid h ->
    h' = add_heap_obj h o heap_obj -> 
    wfe_heap CT h' -> 
    wfe_stack CT h' s.
Proof.

  intros. induction H0.

  apply main_stack_wfe with (s:=s) (lb:=lb). 
  auto.  auto. auto. auto.
  apply stack_wfe with (s:=s) (ct:=ct) 
                  (s':=s') (lb:=lb) (sf:=sf) (h:=h').
  auto. auto. auto. auto. auto.
  apply stack_frame_wfe with (sf:=sf) (lb:=lb). auto.
  inversion H6. auto. inversion H7.
  intros. destruct H8 with (x:=x) as [v]. exists v. intro.  
  destruct H12. auto.  left. auto. 
  right. destruct H12 as [cls_name]. destruct H12 as [o'].
  exists cls_name. exists o'. destruct H12. split.  auto.
  destruct H16 as [F]. destruct H16 as [lo]. 
  destruct H16 as [field_defs].   destruct H16 as [method_defs]. 
  destruct H16.
  exists F. exists lo. exists field_defs. exists method_defs. 
  rewrite H2. unfold add_heap_obj. unfold lookup_heap_obj.
  assert (lookup_heap_obj h o = None). apply fresh_oid_heap with (CT:=ct); auto.
  assert (o' <> o). intro contra. rewrite contra in H16. rewrite H16 in H18. inversion H18. 

  apply beq_oid_not_equal in H19. rewrite H19. fold lookup_heap_obj. auto. 
Qed. 
 *)


  
(*field write changes the objects in the heap, such field write should preserve the wfe of stack *)
(*
  Lemma update_field_preserve_stack_wfe : 
  forall CT o s h h' F F' cls_def lb lb' clsT field_defs method_defs,
  wfe_stack CT h s ->
  wfe_heap CT h ->
  wfe_heap CT h' ->
  Some (Heap_OBJ cls_def F lb) = lookup_heap_obj h o ->
  cls_def = class_def clsT field_defs method_defs ->
  Some cls_def = CT clsT ->
  h' = (update_heap_obj h o
           (Heap_OBJ cls_def F' lb')) ->
  wfe_stack CT h' s.
Proof with auto. 

  intros CT o s h h' F F' cls_def lb lb' clsT field_defs method_defs.
  intro wfe_s. intro wfe_h. intro wfe_h'. intro Ho. intro Hcls_def. intro Hct.
  intro Hy. 

  induction wfe_s. 

  (*s=nil*)
  apply main_stack_wfe with (s:=(Labeled_frame lb1 empty_stack_frame :: nil)) (lb:=lb1). 
  auto.  auto. auto. 

  apply stack_wfe with (s':=s')  (lb:=lb0) (sf:=sf) ; auto.
  inversion H1. 
  apply stack_frame_wfe with (h:=h') (lsf:= (Labeled_frame lb0 sf)) (sf:=sf) (lb:=lb0) (ct:=ct).
  auto. intros.  destruct H3 with (x:=x) . auto. inversion H2. 
  exists x0. intro.  destruct H7. auto. left. auto.  
  destruct H7 as [cls_name]. destruct H7 as [o'].  right. 
  exists cls_name. exists o'. destruct H7. split. auto. 
  case_eq (beq_oid o' o).   intro. 
  apply beq_oid_equal in H12. rewrite H12. 
exists F'. exists lb'. exists field_defs. exists method_defs. split;auto.  
  destruct H11 as [F0]. destruct H11 as [lo0]. destruct H11 as [field_defs0].
  destruct H11 as [method_defs0]. destruct H11.
  rewrite H12 in H11. rewrite H11 in Ho. inversion Ho. rewrite Hcls_def in H15.
  inversion H15.   
  assert (Some (Heap_OBJ cls_def F' lb') = lookup_heap_obj h' o).
  apply lookup_updated with (o:=o) (ho:=(Heap_OBJ cls_def F' lb')) 
          (ho':=(Heap_OBJ (class_def cls_name field_defs0 method_defs0) F0 lo0))
          (h':=h') (h:=h); auto. rewrite <-Hcls_def in H15. rewrite <- H15. auto.  

  destruct H11 as [F0]. destruct H11 as [lo0]. destruct H11 as [field_defs0].
  destruct H11 as [method_defs0]. destruct H11.
  rewrite H12 in H11. rewrite H11 in Ho. inversion Ho. rewrite Hcls_def in H15.
  inversion H15. auto. 

  intro.
  destruct H11 as [F0]. destruct H11 as [lo0]. destruct H11 as [field_defs0].
  destruct H11 as [method_defs0]. destruct H11.
  exists F0. exists lo0. exists field_defs0. exists method_defs0. split;auto.  
  assert (Some (Heap_OBJ (class_def cls_name field_defs0 method_defs0) F0 lo0) = lookup_heap_obj h' o').
  apply lookup_updated_not_affected with (o:=o) 
        (ho':=(Heap_OBJ (class_def cls_name field_defs0 method_defs0) F0 lo0))
        (h:=h) (h':=h') (o':=o') (ho:=(Heap_OBJ cls_def F' lb') ); auto. 
  intro contra. rewrite contra in H12. 
  assert (beq_oid o o = true). apply beq_oid_same. rewrite H12 in H14. inversion H14.
  auto.  
Qed. 
*)

  
Lemma heap_preserve_typing : forall h h' t T CT gamma,
(forall o cls_def F lo, lookup_heap_obj h o = Some  (Heap_OBJ cls_def F lo) 
                              -> exists F' lo', lookup_heap_obj h' o = Some  (Heap_OBJ cls_def F' lo') )
 -> tm_has_type CT gamma h t T -> tm_has_type CT gamma h' t T.
Proof. 
  intros h h' t T CT gamma.
  intro Hyh.
  intro Hy.  
  induction Hy. 
  + apply T_Var. auto.
  + eauto using tm_has_type.  
  + apply T_null.
  + apply T_FieldAccess with (cls_def:=cls_def) (clsT:=clsT) 
            (fields_def:=fields_def); auto. 
  + apply T_MethodCall with (T:=T) (cls_def:=cls_def) (body:=body) (arg_id:=arg_id)
        (arguT:=arguT) (Gamma':=Gamma'); auto.
  + apply T_NewExp with (cls_name:=cls_name). auto.
  + auto.
  + auto. 
  + apply T_label.
  + apply T_labelData; auto.
  + apply T_unlabel; auto.
  + apply T_labelOf with (T:=T); auto. 
  + apply T_unlabelOpaque; auto.
  + apply T_skip.
  + apply T_assignment with (T:=T); auto. (*(lsf:=lsf) (s':=s') (lb:=lb) (sf:=sf); auto. *)
  + apply T_FieldWrite with (cls_def:=cls_def) (clsT:=clsT) (cls':=cls'); auto. 
  + auto.
  + apply T_sequence with (T:=T); auto.
  
  + apply T_ObjId with (cls_def:=cls_def). 
    auto. destruct H1 as [F]. destruct H1 as [lo].
    destruct Hyh with (o:=o) (cls_def:=cls_def) (F:=F) (lo:=lo).
    auto. destruct H2 as [lx]. auto.
    auto. destruct H1 as [F]. destruct H1 as [lo].
    destruct Hyh with (o:=o) (cls_def:=cls_def) (F:=F) (lo:=lo).
    auto. exists x.  auto. 
  + apply T_v_l; auto.
  + apply T_v_opa_l; auto.
  + auto. 
Qed. Hint Resolve heap_preserve_typing.
(*
Lemma reduction_preserve_heap_pointer : forall t s s' h h', 
     forall CT T, has_type CT empty_context h t T ->
     wfe_heap CT h -> wfe_stack CT h s ->    field_wfe_heap CT h -> 
     forall t', reduction (Config CT t (SIGMA s h)) (Config CT t' (SIGMA s' h')) -> 
     (forall o cls_def F lo, lookup_heap_obj h o = Some  (Heap_OBJ cls_def F lo) 
                              -> exists F' lo', lookup_heap_obj h' o = Some  (Heap_OBJ cls_def F' lo') ).
Proof with eauto.
     intros  t s s' h h'.
     intros CT.
     induction t; intro T; intro typing; intro wfe_h; intro wfe_s; intro wfe_fields; intro t'; intro step; inversion step; inversion typing; auto. 
     + intuition. exists F. exists lo. auto.  
     + apply IHt with (classTy clsT) e'; auto.
     + inversion H10. auto. 
          inversion H5. auto.  intuition. exists F. exists lo. auto. 
     + apply IHt1 with (classTy T0) e'; auto.
     + apply IHt2 with (classTy arguT) e'; auto.
     + inversion H14. auto.  intuition. exists F. exists lo. auto.
     + inversion H14. auto.   intuition. exists F. exists lo. auto.  
     + inversion H11. rewrite H10. unfold add_heap_obj.
        intros.  
        case_eq (beq_oid o0 o). intro. apply beq_oid_equal in H21. 
        rewrite H21 in H18. assert (lookup_heap_obj h o = None). 
        apply fresh_oid_heap with (h:=h) (CT:=CT) (o:=o).
        auto. inversion H5. auto. rewrite H22 in H18. inversion H18.

        intro.  unfold lookup_heap_obj. 
        rewrite H21. fold lookup_heap_obj.  inversion H5. 
        rewrite <- H24. exists F0. exists lo. auto. 
     + apply IHt with T0 e'; auto. 
     + auto.  intuition. exists F. exists lo. auto.  
     + apply IHt with  (LabelelTy T) e'; auto. 
     + inversion H7. auto.  intuition. exists F. exists lo. auto.   
     + apply IHt with (LabelelTy T0) e'; auto. 
     + auto.  intuition. exists F. exists lo. auto.  
     + apply IHt with (OpaqueLabeledTy T) e'; auto. 
     + inversion H7. auto.  intuition. exists F. exists lo. auto.   
     + apply IHt with  T0 e'; auto.
     + auto.  intuition. exists F. exists lo. subst. inversion H6. inversion H8.  subst. auto.  
     + apply IHt1 with (classTy clsT) e1'; auto.
     + apply IHt2 with  (classTy cls') e2'; auto.
     + inversion H11. rewrite H10. inversion H6.  intros.
        case_eq (beq_oid o0 o). intro. 
        assert (Some (Heap_OBJ cls F' l') = lookup_heap_obj (update_heap_obj h0 o (Heap_OBJ cls F' l')) o).
        apply lookup_updated with (o:=o) (ho:=(Heap_OBJ cls F' l'))
                  (ho':=(Heap_OBJ cls F lb)) (h:=h0) (h':=(update_heap_obj h0 o (Heap_OBJ cls F' l'))); auto.
        apply beq_oid_equal in H29. rewrite H29. 
        exists F'. exists l'. auto. rewrite H29 in H24. rewrite <- H7 in H24. inversion H24. 
       rewrite <- H32. auto. 
       intro. 
       assert (Some (Heap_OBJ cls_def0 F0 lo) = lookup_heap_obj (update_heap_obj h0 o (Heap_OBJ cls F' l')) o0).
       apply lookup_updated_not_affected with (o:=o) (ho:=(Heap_OBJ cls F' l'))
                 (h:=h0) (h':=(update_heap_obj h0 o (Heap_OBJ cls F' l'))) (o':=o0) 
              (ho':=(Heap_OBJ cls_def0 F0 lo)); auto. 
      intro contra. rewrite contra in H29. 
      assert (beq_oid o o = true). apply beq_oid_same. 
      rewrite H30 in H29. inversion H29.
      exists F0. exists lo. auto.
     + inversion H12. rewrite H11. inversion H7.  intros.
        case_eq (beq_oid o0 o). intro. 
        assert (Some (Heap_OBJ cls F' l') = lookup_heap_obj (update_heap_obj h0 o (Heap_OBJ cls F' l')) o).
        apply lookup_updated with (o:=o) (ho:=(Heap_OBJ cls F' l'))
                  (ho':=(Heap_OBJ cls F lo)) (h:=h0) (h':=(update_heap_obj h0 o (Heap_OBJ cls F' l'))); auto.
        apply beq_oid_equal in H30. rewrite H30. 
        exists F'. exists l'. auto. rewrite H30 in H25. rewrite <- H8 in H25. inversion H25. 
       rewrite <- H33. auto. 
       intro. 
       assert (Some (Heap_OBJ cls_def0 F0 lo0) = lookup_heap_obj (update_heap_obj h0 o (Heap_OBJ cls F' l')) o0).
       apply lookup_updated_not_affected with (o:=o) (ho:=(Heap_OBJ cls F' l'))
                 (h:=h0) (h':=(update_heap_obj h0 o (Heap_OBJ cls F' l'))) (o':=o0) 
              (ho':=(Heap_OBJ cls_def0 F0 lo0)); auto. 
      intro contra. rewrite contra in H30. 
      assert (beq_oid o o = true). apply beq_oid_same. 
      rewrite H31 in H30. inversion H30.
      exists F0. exists lo0. auto.
     + intuition. exists F. exists lo. auto. 
     + intuition. exists F. exists lo. auto.
     + apply IHt1 with T0 s1'; auto.
     + intuition. exists F. exists lo. auto. 
     +  apply IHt with T0 e'; auto. subst. 
      apply    extend_stack_reduction_preservation with T0; auto. 
     + intuition. exists F. exists lo. inversion H10. inversion H5. inversion H9. subst. auto. 
Qed.
 *)

Lemma lookup_extended_heap_none : forall h o ho,
     lookup_heap_obj
          (add_heap_obj h (get_fresh_oid h) ho)
          o = None ->
     lookup_heap_obj h o = None.
Proof. intros.
       unfold add_heap_obj  in H. unfold lookup_heap_obj in H. case_eq (beq_oid o (get_fresh_oid h)); intro.
       rewrite H0 in H.
       inversion H.
       rewrite H0 in H. fold lookup_heap_obj in H. auto. Qed.
Hint Resolve  lookup_extended_heap_none.

Lemma extend_heap_lookup_eq : forall h o ho n_ho,
    lookup_heap_obj h o = Some ho ->
    o <> (get_fresh_oid h) ->
    lookup_heap_obj
          (add_heap_obj h (get_fresh_oid h) n_ho) o =
    Some ho.
Proof with eauto. intros.
                  unfold   add_heap_obj. unfold lookup_heap_obj.
                    apply beq_oid_not_equal in H0 .  rewrite H0.
                    fold lookup_heap_obj. auto. 
Qed.
Hint Resolve extend_heap_lookup_eq.

Lemma extend_heap_lookup_new : forall h  ho,
    lookup_heap_obj (add_heap_obj h (get_fresh_oid h) ho) (get_fresh_oid h) = Some ho.
Proof with eauto.
  intros.
  unfold   lookup_heap_obj. unfold add_heap_obj .
  assert (beq_oid (get_fresh_oid h) (get_fresh_oid h) = true) by (apply beq_oid_same; auto).
  rewrite H.
  auto.
Qed.
Hint Resolve extend_heap_lookup_new.


Lemma initilized_fields_empty : forall field_defs fname,
    init_field_map field_defs  empty_field_map fname = Some null \/
    init_field_map field_defs empty_field_map fname = None.
Proof with eauto. intros.
                  induction field_defs. auto.
                  destruct a. destruct fname. 
                  unfold init_field_map.
                  case_eq (beq_id i (Id s)); intro. auto.
                  fold init_field_map. auto. 
Qed. 
Hint Resolve     initilized_fields_empty.              

Lemma lookup_extend_heap_fresh_oid :forall h o CT ho, 
    wfe_heap CT h ->
    lookup_heap_obj h o = Some ho ->
    o <> get_fresh_oid h.
Proof with eauto.
  intros. intro contra.
  rewrite contra in H0.
  assert (lookup_heap_obj h o = None).
  apply fresh_oid_heap  with CT; auto.
  subst. rewrite H1 in H0. inversion H0. 
Qed.
Hint Resolve lookup_extend_heap_fresh_oid .

Lemma all_obj_are_value : forall o,
    ~ value (ObjId o) -> False. 
Proof. auto.     
Qed.
Hint Resolve all_obj_are_value.
                                          
   
Lemma lookup_updated_heap_new_obj : forall h1 cls1 cls F1 lb0 F' lo o1 o,
      Some (Heap_OBJ cls1 F1 lb0) =
      lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls F' lo)) o1 ->
      beq_oid o1 o = true  ->
      Some (Heap_OBJ cls1 F1 lb0) = Some (Heap_OBJ cls F' lo).
  Proof with eauto.
    intros.
    induction h1. unfold update_heap_obj in H. inversion H.
    destruct a.
    case_eq (beq_oid o o0); intro.
    unfold update_heap_obj in H. rewrite H1 in H.
    apply beq_oid_equal in H1. subst; auto.
    unfold lookup_heap_obj in H. rewrite H0 in H. fold lookup_heap_obj in H.
    unfold lookup_heap_obj. auto.
    
    case_eq (beq_oid o1 o0); intro.
    unfold update_heap_obj in H. rewrite H1 in H. fold update_heap_obj in H.
    unfold lookup_heap_obj in H. rewrite H2 in H.
    unfold lookup_heap_obj. apply beq_oid_equal in H2.
    apply beq_oid_equal in H0. subst; auto. assert (beq_oid o0 o0 = true).
    apply beq_oid_same.  rewrite H0 in H1. inversion H1. 

    unfold update_heap_obj in H. rewrite H1 in H. fold update_heap_obj in H.
    unfold lookup_heap_obj in H. rewrite H2 in H. fold lookup_heap_obj in H.
    unfold lookup_heap_obj.  auto.
Qed. Hint Resolve lookup_updated_heap_new_obj.


  Lemma lookup_updated_heap_old_obj : forall h1 cls1 cls F1 lb0 F' lo o1 o,
      Some (Heap_OBJ cls1 F1 lb0) =
      lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls F' lo)) o1 ->
      beq_oid o1 o = false ->
      Some (Heap_OBJ cls1 F1 lb0) = lookup_heap_obj h1 o1.
  Proof with eauto.
    intros.
    induction h1. unfold update_heap_obj in H. inversion H.
    destruct a.
    case_eq (beq_oid o o0); intro.
    unfold update_heap_obj in H. rewrite H1 in H.
    apply beq_oid_equal in H1. subst; auto.
    unfold lookup_heap_obj in H. rewrite H0 in H. fold lookup_heap_obj in H.
    unfold lookup_heap_obj. rewrite H0. fold lookup_heap_obj. auto.

    case_eq (beq_oid o1 o0); intro.
    unfold update_heap_obj in H. rewrite H1 in H. fold update_heap_obj in H.
    unfold lookup_heap_obj in H. rewrite H2 in H.
    unfold lookup_heap_obj. rewrite H2. auto.

    unfold update_heap_obj in H. rewrite H1 in H. fold update_heap_obj in H.
    unfold lookup_heap_obj in H. rewrite H2 in H. fold lookup_heap_obj in H.
    unfold lookup_heap_obj. rewrite H2. auto.
Qed. Hint Resolve lookup_updated_heap_old_obj.
  
Lemma reduction_determinacy : forall c c1 c2,
    c ==> c1 -> c ==> c2 ->
    c1 = c2.
Proof. Admitted.
Hint Resolve    reduction_determinacy.

Lemma lookup_extend_heap_for_existing : forall h cls F lo o
  cls0 F0 lb,
    lookup_heap_obj (add_heap_obj h (get_fresh_oid h)
                                  (Heap_OBJ cls F lo)) o =
    Some (Heap_OBJ cls0 F0 lb) ->
    beq_oid o (get_fresh_oid h) = false ->
    lookup_heap_obj h o = Some (Heap_OBJ cls0 F0 lb).
Proof with eauto.
  intros.
  unfold lookup_heap_obj in H. unfold add_heap_obj in H.
  rewrite H0 in H. fold lookup_heap_obj in H. auto. 
Qed. Hint Resolve   lookup_extend_heap_for_existing.



Lemma lookup_updated_heap_must_none : forall h o ho o0,
     lookup_heap_obj
       (update_heap_obj h o ho) o0 = None->
     lookup_heap_obj h o0 = None.
Proof. intros.       
       induction h. auto.
       destruct a.
       unfold lookup_heap_obj.
       case_eq (beq_oid o0 o1); intro.
       unfold update_heap_obj  in H. unfold lookup_heap_obj in H.
       case_eq (beq_oid o o1); intro.
       rewrite H1 in H.
       apply beq_oid_equal in H0.
       apply beq_oid_equal in H1. subst; auto.
       assert (beq_oid o1 o1 = true) by (apply beq_oid_same).
       rewrite H0 in H. inversion H.

       rewrite H1 in H.
       rewrite H0 in H.  inversion H.

       case_eq (beq_oid o o1); intro.
       unfold update_heap_obj  in H. unfold lookup_heap_obj in H.
       rewrite H1 in H. assert (beq_oid o0 o = false).
       apply beq_oid_equal in H1. rewrite <- H1 in H0.
       rewrite H0 in H. auto. rewrite H2 in H.
       fold update_heap_obj  in H. fold lookup_heap_obj in H.
       fold lookup_heap_obj. auto.
       unfold update_heap_obj  in H. unfold lookup_heap_obj in H.
       rewrite H1 in H.  rewrite H0 in H.
       fold update_heap_obj  in H. fold lookup_heap_obj in H.
       fold lookup_heap_obj. apply IHh. auto. 
Qed. Hint Resolve   lookup_updated_heap_must_none.      