Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.

Add LoadPath "/Users/llama_jian/Develop/HarvardPLCIFC".

Require Import Label. 
Require Import Lang. 


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

Inductive wfe_stack_frame : Class_table -> heap -> labeled_stack_frame -> Prop :=
  | stack_frame_wfe : forall h lsf sf lb ct,
        lsf = Labeled_frame lb sf ->
         (forall x, exists v, sf x = Some v  ->
               (
               v = null \/ 
                 ( exists cls_name o, v = ObjId o 
                              /\ (exists F lo field_defs method_defs , lookup_heap_obj h o = Some (Heap_OBJ (class_def cls_name field_defs method_defs) F lo)
                                      /\ (ct cls_name = Some (class_def cls_name field_defs method_defs))
                                   ) 
                  )    )  ) ->
        wfe_stack_frame ct h lsf. 


Inductive wfe_stack : Class_table -> heap -> stack -> Prop :=
  | main_stack_wfe : forall ct s h lb,
        wfe_heap ct h -> 
        s = cons (Labeled_frame lb empty_stack_frame) nil ->
        forall lb, wfe_stack ct h (cons (Labeled_frame lb empty_stack_frame) nil)
  | stack_wfe : forall s ct s' lb sf h, 
        s = cons (Labeled_frame lb sf) s'->
        wfe_stack ct h s' ->
        wfe_heap ct h ->
        wfe_stack_frame ct h (Labeled_frame lb sf) ->
        wfe_stack ct h s.



(*lemma*)

Lemma string_eq : forall n1 n2, n1 = n2 -> Id n1 = Id n2.
Proof with eauto.
  intros. rewrite -> H. auto.
Qed. 

Lemma beq_nat_true: forall n m,
  beq_nat n m = true -> n = m.
Proof.
  intros n. induction n.
    intros. destruct m. 
      reflexivity.  inversion H.
    intros. destruct m. 
      inversion H. simpl in H. apply f_equal. apply IHn in H. apply H.
Qed. 


Lemma beq_oid_equal : forall x x', beq_oid x x' = true -> x = x'.
Proof.
   intros. unfold beq_oid in H.
   destruct x. destruct x'. f_equal. 
   case_eq (n =? n0). intro. 
   apply beq_nat_true with (n:=n) (m:=n0). auto. 

   intro. rewrite H0 in H. inversion H.
Qed.

Lemma beq_oid_same : forall o, beq_oid o o = true. 
Proof with auto. 
  intro o. unfold beq_oid. destruct o. induction n. reflexivity.
  simpl. auto. 
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

Lemma gt_trans : forall n1 n2 n3, 
  n1 > n2 ->
  n2 > n3 ->
  n1 > n3. 
Proof. 
  intros. intuition.
Qed.  

Lemma oid_trans : forall n1 n2 n3, 
  n1 > n2 ->
  compare_oid (OID n2) (OID n3) = true -> 
  n1 > n3. 
Proof. 
  intros. apply compare_oid_nat in H0. intuition. 
Qed. 

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
    has_type CT gamma h v (classTy cls') ->
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
  rewrite <-H18 in H4. inversion H4.
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

Lemma wfe_oid : forall o ct gamma s h sigma cls_def cn, 
  sigma = SIGMA s h ->
  wfe_stack ct h s ->
  (has_type ct gamma h (ObjId o) (classTy cn)) -> ct cn = Some cls_def 
    -> exists fieldsMap lb, lookup_heap_obj h o = Some (Heap_OBJ cls_def fieldsMap lb).
Proof with auto. 
  intros. inversion H1. rewrite H2 in H5. inversion H5. 
  rewrite <- H12. auto.
Qed.


Lemma excluded_middle_opaqueLabel : forall e, (exists t, e = unlabelOpaque t) \/ (forall t, ~ (e = unlabelOpaque t)).
Proof with eauto.
  intros. case e; try (right; intro;  intros contra; inversion contra; fail). left. exists t. auto. 
Qed.

Lemma excluded_middle_returnT : forall e, (exists t, e = Return t) \/ (forall t, ~ (e = Return t)).
Proof with eauto.
  intros. case e; try (right; intro;  intros contra; inversion contra; fail). left. exists t.  auto. 
Qed.

Lemma stack_not_nil : forall sigma CT s h, 
  sigma = SIGMA s h ->  wfe_heap CT h -> wfe_stack CT h s -> exists lsf s', s = cons lsf s'.
Proof with auto.
  intros. inversion H1. exists (Labeled_frame lb0 empty_stack_frame). exists nil. auto. 
  exists (Labeled_frame lb sf). exists s'. auto. 
Qed.

(* every value in the stack should be well-formed, which means that all values should point to null or valid Obj Id*)
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


Lemma change_label_preserve_wfe : forall CT s h lb,
    wfe_heap CT h -> wfe_stack CT h s ->
    wfe_stack CT h (update_current_label s lb).
Proof. 
   intros. inversion H0. 
    - unfold update_current_label. apply main_stack_wfe with (s:=s) (lb:=lb1); auto.
    - subst.  unfold update_current_label. apply stack_wfe with (s':=s') (lb:=lb) (sf:=sf); auto.
        inversion H4.  apply stack_frame_wfe with (sf:=sf) (lb:=lb); auto. inversion H1. auto.
Qed.




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

(*field write changes the objects in the heap, such field write should preserve the wfe of stack *)
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

(* reduction preserve well-form of stack and heap *)
Theorem reduction_preserve_wfe : forall CT s s' h h' sigma sigma',
    sigma = SIGMA s h ->  wfe_heap CT h -> wfe_stack CT h s ->     field_wfe_heap CT h -> 
     sigma' = SIGMA s' h' -> 
    forall t T, has_type CT empty_context h t T -> 
     forall t',  Config CT t sigma ==> Config CT t' sigma' ->
    wfe_heap CT h' /\ wfe_stack CT h' s' /\  field_wfe_heap CT h'.
Proof with auto.

    intros CT s s' h h' sigma sigma'.
    intro H_sigma. intro H_wfe_heap. intro H_wfe_stack. intro H_field_wfe.  
    induction t. (*induction on the terms *)
  (* (Tvar i) *)
  + intro T. intro typing. intro t'.  intro step. inversion step.
      rewrite H_sigma in H4. rewrite H in H4. inversion H4. 
      rewrite <- H10. rewrite <- H11.
      split; auto. 

  (* null *)
  + intro T. intro typing. intro t'.  intro step. inversion step.
  (* field access *)
  + intro T. intro typing. intro t'.  intro step. 
      inversion step.  inversion typing.
      apply IHt with (T:=(classTy clsT)) (t':=e'). auto. auto.
      (*subgoal#2 *)      
      inversion typing. subst. inversion H11. inversion H6. 
      split. rewrite <- H3. auto.
      split. rewrite <- H3. rewrite <- H2. 
      remember (join_label lb (current_label (SIGMA s h))) as lb'.
      unfold update_current_label.
      inversion H_wfe_stack. apply main_stack_wfe with (s:=s1) (lb:=lb0). auto. auto. auto. auto.  
      rewrite H. 

      apply stack_wfe with (s':=s'0) 
                                                      (lb:=lb') (sf:=sf) ; auto.
      inversion H9. apply stack_frame_wfe with (lb:=lb') (sf:=sf); auto.
      inversion H16. apply H17. 
    
      rewrite <- H3. auto.  

  (* method call *)
  + 
      intro T. intro typing. intro t'.  intro step. 
      inversion step.  
      (*subgoal 1*)
      inversion typing. apply IHt1 with (T:=(classTy T0)) (t':=e'); auto.
     
      (*subgoal 2*)
      inversion typing. apply IHt2 with (T:=(classTy arguT)) (t':=e'); auto.
      (*subgoal 3*)
      subst. inversion H15. split. auto. split.
      apply stack_wfe with (s':=s0) 
            (lb:=(current_label (SIGMA s h))) 
            (sf:=(sf_update empty_stack_frame arg_id t2)) ; auto.
      inversion H7. rewrite <- H2. rewrite <- H3. auto.  
      apply stack_frame_wfe with      (lb:=(current_label (SIGMA s h)))
                                                     (sf:=(sf_update empty_stack_frame arg_id t2)) ; auto.
      intros x. exists t2.
      case_eq (beq_id arg_id x). intro. 
      unfold sf_update. rewrite H. intro. 
      inversion typing.
      assert 
      (t2 = null \/ 
                 ( exists o, t2 = ObjId o 
                              /\ (exists F lo field_defs method_defs , 
                                      lookup_heap_obj h o = Some (Heap_OBJ (class_def arguT field_defs method_defs) F lo)
                                      /\ (CT arguT = Some (class_def arguT field_defs method_defs))
                                   )
                  )    ).
      apply wfe_stack_value with (gamma:=empty_context) (s:=s) (sigma:=(SIGMA s h) ); auto. 
      destruct H22. left. auto.  destruct H22 as [o']. right. exists arguT. exists o'. auto.

      intro.  unfold sf_update. rewrite H. intro. inversion H2. auto.  
      
      (*subgoal 4*)
      subst. inversion H15. split. auto. split.
      apply stack_wfe with (s':=s0) 
            (lb:=(join_label lb (current_label (SIGMA s h)))) 
            (sf:=(sf_update empty_stack_frame arg_id v)) ; auto.
      inversion H7. rewrite <- H2. rewrite <- H3. auto.  
      apply stack_frame_wfe with      (lb:=(join_label lb (current_label (SIGMA s h))))
                                                     (sf:=(sf_update empty_stack_frame arg_id v)) ; auto.
      intros x. exists v.
      case_eq (beq_id arg_id x). intro. 
      unfold sf_update. rewrite H. intro. 
      inversion typing.
      assert 
      (v = null \/ 
                 ( exists o, v = ObjId o 
                              /\ (exists F lo field_defs method_defs , 
                                      lookup_heap_obj h o = Some (Heap_OBJ (class_def arguT field_defs method_defs) F lo)
                                      /\ (CT arguT = Some (class_def arguT field_defs method_defs))
                                   )
                  )    ).
      apply wfe_stack_value with (gamma:=empty_context) (s:=s) (sigma:=(SIGMA s h) ); auto.
      inversion H9. inversion H26. auto.  
      destruct H22. left. auto.  destruct H22 as [o']. right. exists arguT. exists o'. auto.

      intro.  unfold sf_update. rewrite H. intro. inversion H2. auto.  

(* new expression *)
+ intro T. intro typing. intro t'.  intro step. inversion step. 
    subst. inversion typing. 
    remember (class_def c field_defs method_defs) as cls_def.
(*
    assert (CT c = Some cls_def).
    apply H5 with (field_defs:=field_defs) (method_defs:=method_defs) (cls_def:=cls_def).
    auto. 
*)
    inversion H6. inversion H12.
    rewrite <- H11. split.  
    remember (current_label (SIGMA s h)) as lb. 
    apply extend_heap_preserve_heap_wfe with (h:=h) (o:=(get_fresh_oid h0))
                          (c:=c) (field_defs:=field_defs)
                          (method_defs:=method_defs) (lb:=lb).
   auto.  rewrite H9. auto. apply fresh_oid_heap with (CT:=CT) .
   auto. rewrite H9. auto. rewrite <- Heqcls_def. auto. auto.
   rewrite  H9. auto. rewrite  Heqcls_def in H11. auto.
  split. 
 (* extend heap with new object preserve wfe *) 
    rewrite <- H8.
    remember (Heap_OBJ cls_def
           (init_field_map (find_fields cls_def) empty_field_map)
           (current_label (SIGMA s h))) as heap_obj.
    apply extend_heap_preserve_stack_wfe with (h:=h0) (o:= (get_fresh_oid h0))
                         (heap_obj:=heap_obj).
     rewrite <- H9.  auto.       rewrite <- H9.  auto.  auto. auto. 
     
     apply extend_heap_preserve_heap_wfe with (h:=h0) (o:=(get_fresh_oid h0)) 
                (c:=c) (field_defs:=field_defs) (method_defs:=method_defs) (lb:=(current_label (SIGMA s h))).
     rewrite <- H9.  auto.       rewrite <- H9.  auto.
     apply fresh_oid_heap with (CT:=CT).  
     rewrite <- H9.  auto.       rewrite <- H9.  auto.
     (*destruct H5 with (field_defs:=field_defs) (method_defs:=method_defs) (cls_def:= (class_def c field_defs method_defs)).*)
     auto. auto. 
     rewrite <- Heqcls_def. auto.
    rewrite Heqheap_obj in H11. 
      rewrite Heqcls_def in H11. unfold find_fields in H11. auto. 

    
    apply extend_heap_preserve_field_wfe with (CT:=CT) (h:=h0) (h':=h') (o:=(get_fresh_oid h0))   
                      (c:=c) (field_defs:=field_defs) (method_defs:=method_defs) (lb:=(current_label (SIGMA s h))).

    rewrite <- H9. auto.  auto. rewrite <- H9. auto. apply fresh_oid_heap with (CT:=CT) . 
    auto. auto.  rewrite Heqcls_def in H5. auto. rewrite <-Heqcls_def. 
    rewrite Heqcls_def in H11.  rewrite Heqcls_def. unfold find_fields in H11.  auto. 

(* label value*)
+ intro T. intro typing. intro t'.  intro step. inversion step. 

(* label data *)
+ intro T. intro typing. intro t'.  intro step. 
    inversion step. inversion typing.
    apply IHt with (T:=T0) (t':=e'); auto.

    subst. inversion H6. rewrite <- H0. rewrite <- H2.
    intuition.

(* unlabel *)
+ intro T. intro typing. intro t'.  intro step. 
    inversion step. inversion typing.
    apply IHt with (T:=(LabelelTy T)) (t':=e'); auto.

    subst. inversion H8. split. auto. 
    inversion H5. rewrite <- H2. rewrite <- H3.
    split.  
    apply change_label_preserve_wfe; auto.
    auto. 

(* label of *)
+ intro T. intro typing. intro t'.  intro step. 
    inversion step. inversion typing.
    apply IHt with (T:=(LabelelTy T0)) (t':=e'); auto.

    subst. inversion H5. rewrite <- H0. rewrite <- H1. 
    split; auto.

(* unlabelopaque *)
+ intro T. intro typing. intro t'.  intro step. 
    inversion step. inversion typing.
    apply IHt with (T:=(OpaqueLabeledTy T)) (t':=e'); auto.

    rewrite H_sigma in H8. rewrite H in H8. unfold get_heap in H8.
    inversion H8. split. auto.
   split.
    rewrite H7.
    rewrite H_sigma in H5. inversion H5. rewrite <- H12. rewrite <- H13.
    apply change_label_preserve_wfe; auto. 
    auto.

(* opaque call *)
+ intro T. intro typing. intro t'.  intro step. 
    inversion step. 
    (*subgoal 1*)
    inversion typing. apply IHt with (T:=T0) (t':=e'); auto.
     (*subgoal 2*)
    inversion typing. apply IHt with (T:=T0) (t':=Return e'); auto. rewrite <- H2.
    apply ST_return1 in H1. auto.  

     (*subgoal 3*)
      rewrite H_sigma in H5. rewrite H in H5.  inversion H5.
      rewrite <- H8 . rewrite <- H9. auto. 
     (*subgoal 4*)

    
     rewrite H in H9. inversion H9. rewrite H_sigma in H5. 
     inversion H5. rewrite <- H15. split. auto.
    split. 
     rewrite H14 in H_wfe_stack. rewrite H6 in H_wfe_stack. inversion H_wfe_stack; auto.  
     rewrite <- H16 in H7. intuition. auto. inversion H11. auto. auto. 
     
(* skip *)
+ intro T. intro typing. intro t'.  intro step. 
    inversion step.

(* assignment *)
+ intro T. intro typing. intro t'.  intro step. 
    inversion step. inversion typing.
    apply IHt with (T:=T0) (t':=e'). auto. auto.

   rewrite H_sigma in H7. rewrite H in H9.  inversion H7. inversion H9. 
    rewrite <- H12. split. auto. 
    rewrite H11 in H_wfe_stack.    inversion typing. split. inversion H19.
(*    apply update_stack_preserve_wfe with (s:=s0) (i:=i) (v:=t) (T:=T0) (gamma:=empty_context).*)
   auto.

(* field write *)
+ intro T. intro typing. intro t'.  intro step. 

    inversion step. 
     (*subgoal 1*)
    inversion typing.    apply IHt1 with (T:=(classTy clsT)) (t':=e1'); auto.
    (*subgoal 2*)
    inversion typing.    apply IHt2 with (T:=(classTy cls')) (t':=e2'); auto.  
    (*subgoal 3*)
    (*wfe_stack CT gamma h *)
    assert (wfe_heap CT h' ).
    inversion typing. rewrite H_sigma in H7. inversion H7. 
    rewrite <- H1 in H17. inversion H17. 
    rewrite <- H27 in H8.
    destruct H34 as [F0]. destruct H34 as [lo0].
    rewrite H34 in H8. inversion H8. rewrite <- H23 in H29. inversion H29.
    destruct H33 as [field_defs]. destruct H33 as [method_defs].
    apply field_write_preserve_wfe_heap with (CT:=CT) (o:=o) 
           (h:=h0) (h':=h') (i:=i) (F:=F) (F':=F') (cls_def:=cls)
              (cls':=cls') (lb:=lb) (lb':=l')  (clsT:=clsT) (field_defs:=field_defs) (method_defs:=method_defs).
   rewrite <- H27. auto. rewrite <- H34 in H8. rewrite <- H27. auto.
   rewrite H36. rewrite H39. auto.
   rewrite <- H36 in H33. auto.
   rewrite H36. rewrite H39. auto.
   rewrite H in H12. inversion H12. auto. 
   split; auto. 

   (*wfe_stack CT gamma h' s'*)
   split. rewrite H in H12. inversion H12. rewrite <- H17. 
   inversion typing. rewrite H_sigma in H7. inversion H7. rewrite <- H29. 
    rewrite <- H1 in H20. inversion H20. 
   destruct H37 as [F0]. destruct H37 as [lo0]. 
   destruct H36 as [field_defs0]. destruct H36 as [method_defs0].
   rewrite <- H26 in  H32. inversion H32. 
   apply update_field_preserve_stack_wfe with (CT:=CT) (o:=o)  
          (s:=s) (h:=h) (h':=h') (F:=F) (F':=F') (cls_def:=cls_def) (lb:=lb) (lb':=l') 
          (clsT:=clsT) (field_defs:=field_defs0) (method_defs:=method_defs0); auto.
  rewrite <- H30 in H8. rewrite H37 in H8. inversion H8. rewrite <- H39. auto. 
  rewrite <- H39. auto.  rewrite <- H17 in H11. rewrite <- H30 in H11. 
  rewrite <- H30 in H8. rewrite H37 in H8. inversion H8. 
  rewrite <- H39. rewrite <- H40. auto.  
  assert (field_wfe_heap CT h').
  rewrite H in H12. inversion H12. rewrite <- H17. 
   inversion typing. rewrite H_sigma in H7. inversion H7. 
    rewrite <- H1 in H20. inversion H20. 
   destruct H37 as [F0]. destruct H37 as [lo0]. 
   destruct H36 as [field_defs0]. destruct H36 as [method_defs0].

    apply field_write_preserve_field_wfe with (CT:=CT) (gamma:=empty_context)  (h:=h) 
          (h':=h') (o:=o) (field_defs:=field_defs0) (method_defs:=method_defs0) 
          (lb:=lo0) (lb':=l') (v:=v) (i:=i) (F:=F0) (cls_def:=cls_def0) (clsT:=clsT) 
          (cls':=cls'); auto. 
   rewrite H3. auto.
   assert (cls_def=cls_def0). 
   rewrite <- H32 in H26. inversion H26.  auto. 
  rewrite <- H38. auto. 
   rewrite <- H3 in H24. auto. 
  
rewrite <- H30 in H8. rewrite H37 in H8. inversion H8. 
  rewrite <- H39. rewrite <- H40. rewrite H3. rewrite <-H9. 
  rewrite <- H30 in H11. rewrite <- H17 in H11.  auto.  auto. 
(*subgoal 4 v=unlabelOpaque (v_opa_l v lb)*)
assert (wfe_heap CT h' ).
    inversion typing. rewrite H_sigma in H8. inversion H8. 
    rewrite <- H1 in H18. inversion H18. 
    rewrite <- H28 in H9.
    destruct H35 as [F0]. destruct H35 as [lo0].
    rewrite H35 in H9. inversion H9. rewrite <- H24 in H30. inversion H30.
    destruct H34 as [field_defs]. destruct H34 as [method_defs].
    apply field_write_preserve_wfe_heap with (CT:=CT) (o:=o) 
           (h:=h0) (h':=h') (i:=i) (F:=F) (F':=F') (cls_def:=cls)
              (cls':=cls') (lb:=lo) (lb':=l')  (clsT:=clsT) (field_defs:=field_defs) (method_defs:=method_defs).
   rewrite <- H28. auto. rewrite <- H35 in H9. rewrite <- H28. auto.
   rewrite H37. rewrite H40. auto.
   rewrite <- H37 in H34. auto.
   rewrite H37. rewrite H40. auto.
   rewrite H in H13. inversion H13. auto. 
   split; auto. 

   (*wfe_stack CT gamma h' s'*)
   split. rewrite H in H13. inversion H13. rewrite <- H18. 
   inversion typing. rewrite H_sigma in H8. inversion H8. rewrite <- H30. 
    rewrite <- H1 in H21. inversion H21. 
   destruct H38 as [F0]. destruct H38 as [lo0]. 
   destruct H37 as [field_defs0]. destruct H37 as [method_defs0].
   rewrite <- H27 in  H33. inversion H33. 
   apply update_field_preserve_stack_wfe with (CT:=CT) (o:=o)  
          (s:=s) (h:=h) (h':=h') (F:=F) (F':=F') (cls_def:=cls_def) (lb:=lo) (lb':=l') 
          (clsT:=clsT) (field_defs:=field_defs0) (method_defs:=method_defs0); auto.
  rewrite <- H31 in H9. rewrite H38 in H9. inversion H9. rewrite <- H40. auto. 
  rewrite <- H40. auto.  rewrite <- H18 in H12. rewrite <- H31 in H12. 
  rewrite <- H31 in H9. rewrite H38 in H9. inversion H9. 
  rewrite <- H40. rewrite <- H41. auto.  
  assert (field_wfe_heap CT h').
  rewrite H in H13. inversion H13. rewrite <- H18. 
   inversion typing. rewrite H_sigma in H8. inversion H8. 
    rewrite <- H1 in H21. inversion H21. 
   destruct H38 as [F0]. destruct H38 as [lo0]. 
   destruct H37 as [field_defs0]. destruct H37 as [method_defs0].

    apply field_write_preserve_field_wfe with (CT:=CT) (gamma:=empty_context)  (h:=h) 
          (h':=h') (o:=o) (field_defs:=field_defs0) (method_defs:=method_defs0) 
          (lb:=lo0) (lb':=l') (v:=v) (i:=i) (F:=F0) (cls_def:=cls_def0) (clsT:=clsT) 
          (cls':=cls'); auto. 
   assert (cls_def=cls_def0). 
   rewrite <- H33 in H27. inversion H27.  auto. 
  rewrite <- H39. auto. 
   rewrite H7 in H25. inversion H25. inversion H43. auto.
   
  rewrite <- H31 in H9. rewrite H38 in H9. inversion H9. 
  rewrite <- H40. rewrite <- H41. rewrite <-H10. 
  rewrite <- H31 in H12. rewrite <- H18 in H12.  auto.  auto. 


(* if *)
+ intro T. intro typing. intro t'.  intro step. 
    inversion step. rewrite H_sigma in H8. rewrite H in H8.
    inversion H8. rewrite <- H13. rewrite <- H14.
    split; auto.
    rewrite H_sigma in H8. rewrite H in H8.
    inversion H8. rewrite <- H13. rewrite <- H14.
    split; auto. 

(* sequence *)
+ intro T. intro typing. intro t'.  intro step. 
    inversion step. inversion typing.
    apply IHt1 with (T:=T0) (t':=s1'); auto.

    rewrite H_sigma in H6. rewrite H in H6. inversion H6.
    rewrite <- H8. rewrite <- H9.
    split;auto.

(* return *)
+ intro T. intro typing. intro t'.  intro step. 
    inversion step. inversion typing.
    apply IHt with (T:=T) (t':=e'); auto.

    split. rewrite H_sigma in H6.  rewrite H in H11. 
    inversion H6.  inversion H11. rewrite <- H14. auto.

    split. rewrite H_sigma in H6. inversion H6. 
    rewrite <- H13 in H7. rewrite H7 in H_wfe_stack. inversion H_wfe_stack.
    rewrite <- H15 in H8. intuition. 
    inversion H12.  rewrite H in H11. inversion H11. 
    rewrite H10. apply change_label_preserve_wfe; auto. 
    rewrite <- H14. auto.     rewrite <- H14. rewrite H23.  auto. 

    rewrite H_sigma in H6. inversion H6. 
    rewrite H in H11. inversion H11.  rewrite <- H14. auto. 

(* obj id *)
+ intro T. intro typing. intro t'.  intro step. 
    inversion step.

(* runtime labeled *)
+ intro T. intro typing. intro t'.  intro step. 
    inversion step. 

(* runtime opaque labeled *)
+ intro T. intro typing. intro t'.  intro step. 
    inversion step. 
Qed.

Lemma ct_consist : forall CT CT' t t' sigma sigma', 
  Config CT t sigma ==> Config CT' t' sigma' -> CT = CT'. 
 Proof.
   intros. induction t; inversion H; auto. 
  Qed. 


Lemma value_typing_invariant_gamma : forall CT gamma h v T gamma', 
  value v ->
  has_type CT gamma h v T -> 
  has_type CT gamma' h v T.
Proof. 
 intros CT gamma h v T gamma'. intro H_v. intro typing. generalize dependent T. 
 induction H_v; intro T; intro typing. 
 -  inversion typing.   
 apply T_ObjId with (cls_def:=cls_def); auto.
 - inversion typing. apply T_skip.
 - apply T_null. 
 - inversion typing. apply T_label.
 - inversion typing. apply T_v_l. apply T_label. apply IHH_v. auto. auto. 
 - inversion typing. apply T_v_opa_l. apply T_label. apply IHH_v. auto. auto. 
Qed. 


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


Lemma heap_preserve_typing : forall h h' t T CT gamma,
(forall o cls_def F lo, lookup_heap_obj h o = Some  (Heap_OBJ cls_def F lo) 
                              -> exists F' lo', lookup_heap_obj h' o = Some  (Heap_OBJ cls_def F' lo') )
 -> has_type CT gamma h t T -> has_type CT gamma h' t T.
Proof. 
  intros h h' t T CT gamma.
  intro Hyh.
  intro Hy.  
  induction Hy. 
  + apply T_Var. auto. 
  + apply T_null.
  + apply T_FieldAccess with (cls_def:=cls_def) (clsT:=clsT) 
            (fields_def:=fields_def); auto. 
  + apply T_MethodCall with (T:=T) (cls_def:=cls_def) (body:=body) (arg_id:=arg_id)
        (arguT:=arguT) (Gamma':=Gamma'); auto.
  + apply T_NewExp with (cls_name:=cls_name). auto. 
  + apply T_label.
  + apply T_labelData; auto.
  + apply T_unlabel; auto.
  + apply T_labelOf with (T:=T); auto. 
  + apply T_unlabelOpaque. auto.
  + apply T_opaqueCall. auto.
  + apply T_skip.
  + apply T_assignment with (T:=T); auto. (*(lsf:=lsf) (s':=s') (lb:=lb) (sf:=sf); auto. *)
  + apply T_FieldWrite with (cls_def:=cls_def) (clsT:=clsT) (cls':=cls'); auto. 
  + apply T_if with (T:=T); auto.
  + apply T_sequence with (T:=T); auto.
  + apply T_return . auto. auto.
  + apply T_ObjId with (cls_def:=cls_def). 
    auto. destruct H1 as [F]. destruct H1 as [lo].
    
    destruct Hyh with (o:=o) (cls_def:=cls_def) (F:=F) (lo:=lo).
    auto. destruct H2 as [lx]. auto.
    auto. destruct H1 as [F]. destruct H1 as [lo].
    destruct Hyh with (o:=o) (cls_def:=cls_def) (F:=F) (lo:=lo).
    auto. exists x.  auto. 
  + apply T_v_l; auto.
  + apply T_v_opa_l; auto.
Qed. 



Lemma reduction_preserve_heap_pointer : forall t s s' h h', 
     forall CT gamma T, has_type CT gamma h t T ->
     wfe_heap CT h ->
     forall t', reduction (Config CT t (SIGMA s h)) (Config CT t' (SIGMA s' h')) -> 
     (forall o cls_def F lo, lookup_heap_obj h o = Some  (Heap_OBJ cls_def F lo) 
                              -> exists F' lo', lookup_heap_obj h' o = Some  (Heap_OBJ cls_def F' lo') ).
Proof.
     intros  t s s' h h'.
     intros CT.
     induction t; intro gamma; intro T; intro typing; intro wfe_h; intro t'; intro step; inversion step; inversion typing. 
     + intuition. exists F. exists lo. auto.  
     + apply IHt with (gamma) (classTy clsT) e'; auto.
     + inversion H10. auto. 
          inversion H5. auto.  intuition. exists F. exists lo. auto. 
     + apply IHt1 with gamma (classTy T0) e'; auto.
     + apply IHt2 with (gamma) (classTy arguT) e'; auto.
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
     + apply IHt with (gamma) T0 e'; auto. 
     + auto.  intuition. exists F. exists lo. auto.  
     + apply IHt with (gamma) (LabelelTy T) e'; auto. 
     + inversion H7. auto.  intuition. exists F. exists lo. auto.   
     + apply IHt with (gamma) (LabelelTy T0) e'; auto. 
     + auto.  intuition. exists F. exists lo. auto.  
     + apply IHt with (gamma) (OpaqueLabeledTy T) e'; auto. 
     + inversion H7. auto.  intuition. exists F. exists lo. auto.   
     + apply IHt with (gamma) T0 e'; auto. 
     + subst.  apply IHt with (gamma) T0 (Return e'). auto. auto. apply ST_return1. auto.
     + auto.  intuition. exists F. exists lo. auto.  
     + subst. inversion H4. inversion H8. auto.  intuition. exists F. exists lo. auto.   
     + apply IHt with (gamma) T0 e'; auto. 
     + inversion H6. inversion H8. auto.  intuition. exists F. exists lo. auto.   
     + apply IHt1 with (gamma) (classTy clsT) e1'; auto.
     + apply IHt2 with (gamma)  (classTy cls') e2'; auto.
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
     + apply IHt1 with (gamma) T0 s1'; auto.
     + intuition. exists F. exists lo. auto. 
     +  apply IHt with gamma  T e'; auto.
     + intuition. exists F. exists lo. inversion H10. inversion H5. rewrite <-H23. auto. 
Qed.


