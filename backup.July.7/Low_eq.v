Require Import Label.
Require Import Language.
Require Import Lemmas.
Require Import Coq.Lists.List.
Require Import bijection.
Require Import decision. 


Fixpoint erasure_heap (h:heap) : heap := 
  match h with 
  | nil => nil
  | h1 :: t =>
    match h1 with 
    | ( o0 , ho )
      => match ho with 
         | Heap_OBJ cls F lb
           => if (flow_to lb L_Label)
              then
                ( o0 , ho) :: (erasure_heap t) 
              else (erasure_heap t) 
         end
    end
  end.



Inductive L_equivalence_tm : tm -> heap -> tm -> heap ->  (bijection oid oid )->  Prop :=
  | L_equivalence_tm_eq_Tvar : forall id1 id2 h1 h2  φ , 
      id1 = id2 -> L_equivalence_tm (Tvar id1) h1 (Tvar id2) h2  φ
  | L_equivalence_tm_eq_null : forall h1 h2  φ,  
      L_equivalence_tm null h1 null h2 φ
  | L_equivalence_tm_eq_fieldaccess : forall e1 e2 f h1 h2 φ,
      L_equivalence_tm e1 h1 e2 h2 φ->
      L_equivalence_tm (FieldAccess e1 f) h1 (FieldAccess e2 f) h2  φ
  | L_equivalence_tm_eq_methodcall : forall e1 e2 a1 a2 meth h1 h2  φ,
      L_equivalence_tm e1 h1 e2 h2  φ->
      L_equivalence_tm a1 h1 a2 h2  φ->
      L_equivalence_tm (MethodCall e1 meth a1) h1 (MethodCall e2 meth a2) h2  φ
  | L_equivalence_tm_eq_newexp : forall cls1 cls2 h1 h2  φ,
      cls1 = cls2 ->
      L_equivalence_tm (NewExp cls1) h1 (NewExp cls2) h2  φ
  | L_equivalence_tm_eq_ture : forall h1 h2  φ,
      L_equivalence_tm B_true h1 B_true h2  φ
  | L_equivalence_tm_eq_false : forall h1 h2  φ,    
      L_equivalence_tm B_false h1 B_false h2  φ
  | L_equivalence_tm_eq_label : forall l1 l2 h1 h2  φ, 
      l1 = l2 ->
      L_equivalence_tm (l l1) h1 (l l2) h2  φ
  | L_equivalence_tm_eq_labelData : forall e1 e2 l1 l2 h1 h2  φ,
      L_equivalence_tm e1 h1 e2 h2  φ->
      l1 = l2 ->
      L_equivalence_tm (labelData e1 l1) h1 (labelData e2 l2) h2  φ
  | L_equivalence_tm_eq_unlabel : forall e1 e2 h1 h2  φ,
      L_equivalence_tm e1 h1 e2 h2  φ->
      L_equivalence_tm (unlabel e1) h1 (unlabel e2) h2 φ
  | L_equivalence_tm_eq_labelOf : forall e1 e2 h1 h2  φ,
      L_equivalence_tm e1 h1 e2 h2  φ->
      L_equivalence_tm (labelOf e1) h1 (labelOf e2) h2  φ
  | L_equivalence_tm_eq_unlabelOpaque : forall e1 e2 h1 h2 φ,
      L_equivalence_tm e1 h1 e2 h2  φ->
      L_equivalence_tm (unlabelOpaque e1) h1 (unlabelOpaque e2) h2  φ
  | L_equivalence_tm_eq_skip : forall h1 h2 φ ,
      L_equivalence_tm Skip h1 Skip h2 φ
  | L_equivalence_tm_eq_Assignment : forall e1 e2 x1 x2 h1 h2 φ, 
      L_equivalence_tm e1 h1 e2 h2 φ->
      x1 = x2->
      L_equivalence_tm (Assignment x1 e1) h1 (Assignment x2 e2) h2 φ
  | L_equivalence_tm_eq_FieldWrite : forall e1 e2 f1 f2 e1' e2' h1 h2 φ,
      L_equivalence_tm e1 h1 e2 h2 φ->
      f1 = f2 ->
      L_equivalence_tm e1' h1 e2' h2 φ ->
      L_equivalence_tm (FieldWrite e1 f1 e1') h1 (FieldWrite e2 f2 e2') h2 φ
  | L_equivalence_tm_eq_if : forall s1 s2 s1' s2' g g' h1 h2 φ,
      L_equivalence_tm g h1 g' h2 φ ->
      L_equivalence_tm s1 h1 s1' h2 φ->
      L_equivalence_tm s2 h1 s2' h2 φ->
      L_equivalence_tm (If g s1 s2) h1 (If g' s1' s2') h2 φ
  | L_equivalence_tm_eq_Sequence : forall s1 s2 s1' s2' h1 h2 φ, 
      L_equivalence_tm s1 h1 s1' h2 φ->
      L_equivalence_tm s2 h1 s2' h2 φ->
      L_equivalence_tm (Sequence s1 s2) h1 (Sequence s1' s2') h2 φ
  | L_equivalence_tm_eq_object_L : forall o1 o2 h1 h2 cls1 F1 lb1 cls2 F2 lb2 φ, 
      left φ o1 = Some o2 ->
      Some (Heap_OBJ cls1 F1 lb1) = lookup_heap_obj h1 o1 ->
      flow_to lb1 L_Label = true ->
      Some (Heap_OBJ cls2 F2 lb2) = lookup_heap_obj h2 o2 ->
      flow_to lb2 L_Label = true ->
      L_equivalence_tm (ObjId o1) h1 (ObjId o2) h2 φ
  | L_equivalence_tm_eq_object_H : forall o1 o2 h1 h2 cls1 cls2 F1 lb1 F2 lb2 φ, 
      Some (Heap_OBJ cls1 F1 lb1) = lookup_heap_obj h1 o1 ->
      flow_to lb1 L_Label = false  ->
      Some (Heap_OBJ cls2 F2 lb2) = lookup_heap_obj h2 o2 ->
      flow_to lb2 L_Label = false  ->
      L_equivalence_tm (ObjId o1) h1 (ObjId o2) h2 φ                     
  | L_equivalence_tm_eq_v_l_L : forall lb e1 e2 h1 h2 φ, 
      flow_to lb L_Label = true ->
      L_equivalence_tm e1 h1 e2 h2 φ->
      (* modification here *)
      value e1 -> value e2 ->
      L_equivalence_tm (v_l e1 lb) h1 (v_l e2 lb) h2 φ
  | L_equivalence_tm_eq_v_l_H : forall e1 e2 l1 l2 h1 h2 φ, 
      flow_to l1 L_Label = false ->
      flow_to l2 L_Label = false ->
       value e1 -> value e2 ->
      L_equivalence_tm (v_l e1 l1) h1 (v_l e2 l2) h2 φ
  | L_equivalence_tm_eq_v_opa_l_L : forall lb e1 e2 h1 h2 φ, 
      flow_to lb L_Label = true ->
      value e1 -> value e2 ->
      L_equivalence_tm e1 h1 e2 h2 φ->
      L_equivalence_tm (v_opa_l e1 lb) h1 (v_opa_l e2 lb) h2 φ
  | L_equivalence_tm_eq_v_opa_l_H : forall e1 e2 l1 l2 h1 h2 φ, 
      flow_to l1 L_Label = false ->
      flow_to l2 L_Label = false ->
      value e1 -> value e2 ->
      L_equivalence_tm (v_opa_l e1 l1) h1 (v_opa_l e2 l2) h2 φ
  (*
  | L_equivalence_tm_eq_dot : forall h1 h2 φ,
      L_equivalence_tm (dot) h1 (dot) h2 φ *)
  | L_equivalence_tm_eq_hole : forall h1 h2 φ,
      L_equivalence_tm (hole) h1 (hole) h2 φ
  | L_equivalence_tm_eq_return_hole : forall h1 h2 φ,
      L_equivalence_tm (return_hole) h1 (return_hole) h2 φ.
Hint Constructors L_equivalence_tm.

Inductive L_equivalence_object : oid -> heap -> oid -> heap -> (bijection oid oid )-> Prop :=
(*
   | object_same : forall o h, 
        L_equivalence_object o h o h
   | object_equal_H : forall o1 o2 h1 h2 lb1 lb2 cls1 cls2 F1 F2,
        Some (Heap_OBJ cls1 F1 lb1) = lookup_heap_obj h1 o1 -> 
        Some (Heap_OBJ cls2 F2 lb2) = lookup_heap_obj h2 o2 ->
        flow_to lb1 L_Label = false ->
        flow_to lb2 L_Label = false ->
        L_equivalence_object o1 h1 o2 h2*)
   | object_equal_L : forall o1 o2 h1 h2 lb1 lb2 cls1 cls2 F1 F2 φ,
        Some (Heap_OBJ cls1 F1 lb1) = lookup_heap_obj h1 o1 -> 
        Some (Heap_OBJ cls2 F2 lb2) = lookup_heap_obj h2 o2 ->
        flow_to lb1 L_Label = true ->
        flow_to lb2 L_Label = true ->
        ((cls1 = cls2) /\ (lb1 = lb2) /\ 
            (forall fname, F1 fname = None <-> F2 fname = None )  /\
            (forall fname, F1 fname = Some null <-> F2 fname = Some null ) /\
            (forall fname fo1 fo2, F1 fname = Some (ObjId fo1) -> F2 fname = Some (ObjId fo2) ->
           (exists hof1 hof2,  lookup_heap_obj h1 fo1 = Some hof1 /\ (lookup_heap_obj h2 fo2 = Some hof2) /\  
              left φ fo1 = Some fo2))
        )-> L_equivalence_object o1 h1 o2 h2 φ.
Hint Constructors L_equivalence_object.


Inductive L_equivalence_store : stack_frame -> heap -> stack_frame -> heap ->  (bijection oid oid ) -> Prop :=
| L_equivalence_store_L : forall sf1 sf2 h1 h2  φ,
      (forall x o1 cls1 F1 lb1 ,
          sf1 x = Some (ObjId o1) ->
          Some (Heap_OBJ cls1 F1 lb1) = lookup_heap_obj h1 o1 ->
          flow_to lb1 L_Label = true ->
          exists o2, sf2 x = Some (ObjId o2) /\ L_equivalence_tm (ObjId o1) h1 (ObjId o2) h2 φ) ->
      (forall x o2 cls2 F2 lb2 ,
          sf2 x = Some (ObjId o2) ->
          Some (Heap_OBJ cls2 F2 lb2) = lookup_heap_obj h2 o2 ->
          flow_to lb2 L_Label = true ->
          exists o1 ,
            sf1 x = Some (ObjId o1) /\ L_equivalence_tm (ObjId o1) h1 (ObjId o2) h2 φ) ->
      (*
       
      (forall x lb,
          sf1 x = Some (l lb) <-> sf2 x = Some (l lb) ) ->*)
      (forall x lb v1,
          sf1 x = Some (v_l v1 lb) ->
          flow_to lb L_Label = true ->
          exists v2, sf2 x = Some (v_l v2 lb) /\ L_equivalence_tm v1 h1 v2 h2 φ) ->
      (forall x lb v2,
          sf2 x = Some (v_l v2 lb) ->
          flow_to lb L_Label = true ->
          exists v1, sf1 x = Some (v_l v1 lb) /\ L_equivalence_tm v1 h1 v2 h2 φ) ->
      (forall x lb v1,
          sf1 x = Some (v_opa_l v1 lb) ->
          flow_to lb L_Label = true ->
          exists v2, sf2 x = Some (v_opa_l v2 lb) /\ L_equivalence_tm v1 h1 v2 h2 φ) ->
      (forall x lb v2,
          sf2 x = Some (v_opa_l v2 lb) ->
          flow_to lb L_Label = true ->
          exists v1, sf1 x = Some (v_opa_l v1 lb) /\ L_equivalence_tm v1 h1 v2 h2 φ) ->
      (forall x,
          sf1 x = Some null <-> sf2 x = Some null ) ->

    L_equivalence_store sf1 h1 sf2 h2 φ. 
Hint Constructors L_equivalence_store.




Inductive L_equivalence_heap : heap -> heap ->  (bijection oid oid ) -> Prop :=
  | L_eq_heap : forall h1 h2 φ ,
      (forall o1 o2, left φ o1 = Some o2 ->
                     L_equivalence_object o1 h1 o2 h2 φ) ->
      (forall o, lookup_heap_obj h1 o = None ->
                 left φ o = None) ->
       (forall o, lookup_heap_obj h2 o = None ->
                 right φ o = None) ->
      (forall o cls F lb, lookup_heap_obj h1 o = Some (Heap_OBJ cls F lb)->
                 flow_to lb L_Label = false ->
                 left φ o = None) ->
      (forall o cls F lb, lookup_heap_obj h2 o = Some (Heap_OBJ cls F lb)->
                 flow_to lb L_Label = false ->
                 right φ o = None) ->
                              L_equivalence_heap h1 h2 φ.
Hint Constructors L_equivalence_heap.

Lemma oid_decision : forall a1 a2 : oid, Decision (a1 = a2).
  intros. 
  unfold Decision.
  case_eq (beq_oid a1 a2); intro. 
  apply beq_oid_equal in H. auto.
  assert (a1 <> a2). intro contra.
  apply  beq_equal_oid in contra. rewrite contra in H. inversion H.
  auto. 
Defined.
Hint Resolve oid_decision.

Lemma extend_heap_preserve_l_eq_heap : forall t1 h1 h1' t2 h2 h2'  lb2 cls_def ct φ ,
  wfe_heap ct h2 ->  wfe_heap ct h1 -> 
  L_equivalence_tm t1 h1 t2 h2 φ ->
  L_equivalence_heap h1 h2 φ ->
  flow_to lb2 L_Label = true ->
  h1' = (add_heap_obj h1 (get_fresh_oid h1) 
        (Heap_OBJ  cls_def (init_field_map (find_fields cls_def) empty_field_map) lb2)) ->
  h2' = (add_heap_obj h2 (get_fresh_oid h2) 
        (Heap_OBJ  cls_def (init_field_map (find_fields cls_def) empty_field_map) lb2)) ->
  exists φ', L_equivalence_heap h1' h2' φ'.
  Proof with eauto. 
  intros  t1 h1 h1' t2 h2 h2' lb2 cls_def ct φ. 
  intros.
  inversion H2.  subst; auto.
  remember (add_heap_obj h1 (get_fresh_oid h1) 
        (Heap_OBJ  cls_def (init_field_map (find_fields cls_def) empty_field_map) lb2)) as h1'.
  remember (add_heap_obj h2 (get_fresh_oid h2) 
                         (Heap_OBJ  cls_def (init_field_map (find_fields cls_def) empty_field_map) lb2)) as h2'.
    assert (lookup_heap_obj h1 (get_fresh_oid h1)  = None). 
  apply fresh_oid_heap with ct; auto.   
  assert (lookup_heap_obj h2 (get_fresh_oid h2)  = None). 
  apply fresh_oid_heap with ct; auto. 
  apply H7 in H4. apply H8 in H5.
  assert (forall a1 a2 : oid, Decision (a1 = a2)). auto.
  Check extend_bijection.
  remember (get_fresh_oid h1) as  o3.
  remember (get_fresh_oid h2) as o4. 
  exists  (extend_bijection φ o3 o4 H4 H5).
  assert ( beq_oid (get_fresh_oid h1) (get_fresh_oid h1) = true) by (apply beq_oid_same).
  assert ( beq_oid (get_fresh_oid h2) (get_fresh_oid h2) = true) by (apply beq_oid_same).
  apply  L_eq_heap.
  intros.
  
  destruct (oid_decision o3 o1). subst; auto. simpl in H14.
  destruct (decide (get_fresh_oid h1 = get_fresh_oid h1) ) in H14. inversion H14; subst; auto. 

  remember (add_heap_obj h1 (get_fresh_oid h1) 
        (Heap_OBJ  cls_def (init_field_map (find_fields cls_def) empty_field_map) lb2)) as h1'.
  remember (add_heap_obj h2 (get_fresh_oid h2) 
                         (Heap_OBJ  cls_def (init_field_map (find_fields cls_def) empty_field_map) lb2)) as h2'.
  assert (lookup_heap_obj h1' (get_fresh_oid h1) = Some (Heap_OBJ  cls_def (init_field_map (find_fields cls_def) empty_field_map) lb2) ).
  subst; auto.
    assert (lookup_heap_obj h2' (get_fresh_oid h2) = Some (Heap_OBJ  cls_def (init_field_map (find_fields cls_def) empty_field_map) lb2) ).
  subst; auto.
  apply object_equal_L with lb2 lb2 cls_def cls_def (init_field_map (find_fields cls_def) empty_field_map) (init_field_map (find_fields cls_def) empty_field_map); auto.
  split; auto. 
  split; auto. split; auto.  split; auto.
  split; auto. split; auto.  
  intros.  
  pose proof (initilized_fields_empty (find_fields cls_def) fname).
  
  destruct H19;
    rewrite H19 in H18; inversion H18.
  intuition.  
   assert (left (extend_bijection φ o3 o4 H4 H5)  o1 = 
           left φ o1) by (apply left_extend_bijection_neq; auto).
   rewrite H14 in H15. assert (left φ o1 = Some o2). auto.
   apply H6 in H16. inversion H16; subst; auto.
   destruct H21; subst; auto. destruct H22; subst; auto. 

  
  assert ( lookup_heap_obj
     (add_heap_obj h1 (get_fresh_oid h1)
       (Heap_OBJ cls_def
          (init_field_map (find_fields cls_def) empty_field_map) lb2)) o1 = Some (Heap_OBJ cls2 F1 lb0) ).
  apply extend_heap_lookup_eq; auto. 

  destruct (oid_decision (get_fresh_oid h2) o2 ).
   assert (lookup_heap_obj h2 (get_fresh_oid h2)  = None). 
   apply fresh_oid_heap with ct; auto.  rewrite e in H23.
   rewrite H23 in H18. inversion H18.
   
   assert ( lookup_heap_obj
     (add_heap_obj h2 (get_fresh_oid h2)
       (Heap_OBJ cls_def
          (init_field_map (find_fields cls_def) empty_field_map) lb2)) o2 = Some (Heap_OBJ cls2 F2 lb0) ).
   apply extend_heap_lookup_eq; auto.

   apply object_equal_L with lb0 lb0 cls2 cls2 F1 F2; auto. split; auto. split; auto. intros.
   destruct H22. destruct H24.     
   split; auto. split; auto.
   intros.
   destruct H25 with fname fo1 fo2; auto. rename x into hof1.
   destruct H28 as [hof2]. destruct H28. destruct H29.
   exists hof1. exists hof2.
   split; auto. 
   apply extend_heap_lookup_eq; auto. 
   apply lookup_extend_heap_fresh_oid with ct hof1 ; auto. 
   split; auto. 
   apply extend_heap_lookup_eq; auto. 
   apply lookup_extend_heap_fresh_oid with ct hof2 ; auto. 
   assert (fo1 <> get_fresh_oid h1  ).
   apply lookup_extend_heap_fresh_oid with ct hof1 ; auto.
   assert (left (extend_bijection φ (get_fresh_oid h1) (get_fresh_oid h2) H4 H5)  fo1 = 
         left φ fo1) by (apply left_extend_bijection_neq; auto).
   rewrite H32.   auto.
   
   
   intros. subst; auto.  destruct (oid_decision (get_fresh_oid h1) o). subst; auto.
   unfold  lookup_heap_obj in H14. unfold add_heap_obj in H14.
   
   rewrite H12 in H14. inversion H14.
   remember (extend_bijection φ (get_fresh_oid h1) (get_fresh_oid h2) H4 H5) as φ'.
   rewrite   Heqφ'.
   assert (left (extend_bijection φ (get_fresh_oid h1) (get_fresh_oid h2) H4 H5)  o = 
           left φ o) by (apply left_extend_bijection_neq; auto).
   assert ( lookup_heap_obj h1 o = None) by (apply lookup_extended_heap_none with
                                                 (Heap_OBJ cls_def (init_field_map (find_fields cls_def)
                                                                                   empty_field_map) lb2) ; auto).
   rewrite H15.  apply H7 in H16. auto.
   rewrite   Heqh2'. intros. subst. 
   destruct (oid_decision (get_fresh_oid h2) o). subst; auto.
   unfold  lookup_heap_obj in H14. unfold add_heap_obj in H14.
   rewrite H13 in H14. inversion H14.

   assert (right (extend_bijection φ (get_fresh_oid h1) (get_fresh_oid h2) H4 H5)  o = 
           right φ o). (apply right_extend_bijection_neq; auto).
   assert ( lookup_heap_obj h2 o = None) by (apply lookup_extended_heap_none with
                                                 (Heap_OBJ cls_def (init_field_map (find_fields cls_def)
                                                                                   empty_field_map) lb2) ; auto).
   rewrite H15. apply H8 in H16. auto.
   intros.
   destruct (oid_decision o3 o). subst; auto. simpl in H14.
   rewrite H12 in H14. inversion H14. subst; auto. rewrite H3 in H15. inversion H15.
   subst; auto.

   unfold lookup_heap_obj in H14. unfold add_heap_obj in H14.
   assert (o <> get_fresh_oid h1) by (auto). apply  beq_oid_not_equal in H16. rewrite H16 in H14.
   fold lookup_heap_obj in H14. apply H9 in H14.
   assert (left (extend_bijection φ (get_fresh_oid h1) (get_fresh_oid h2) H4 H5)  o = 
           left φ o) by (apply left_extend_bijection_neq; auto). rewrite H17; auto. auto. 


   intros.
   destruct (oid_decision o4 o). subst; auto. simpl in H14.
   rewrite H13 in H14. inversion H14. subst; auto. rewrite H3 in H15. inversion H15.
   subst; auto.

   unfold lookup_heap_obj in H14. unfold add_heap_obj in H14.
   assert (o <> get_fresh_oid h2) by (auto). apply  beq_oid_not_equal in H16. rewrite H16 in H14.
   fold lookup_heap_obj in H14. apply H10 in H14.
   assert (right (extend_bijection φ (get_fresh_oid h1) (get_fresh_oid h2) H4 H5)  o = 
           right φ o) by (apply right_extend_bijection_neq; auto). rewrite H17; auto. auto. 
Qed. Hint Resolve extend_heap_preserve_l_eq_heap.   
   

Inductive L_equivalence_fs : list tm -> heap -> list tm -> heap -> (bijection oid oid ) -> Prop:=
  | L_equal_fs_nil : forall h1 h2 φ,
    L_equivalence_fs nil h1 nil h2 φ
  | L_equal_fs : forall fs1 fs2 h1 h2 top1 top2 φ, 
    L_equivalence_tm top1 h1 top2 h2 φ-> 
    L_equivalence_fs fs1 h1 fs2 h2 φ->
    L_equivalence_fs (top1 :: fs1) h1 (top2 :: fs2) h2 φ.
Hint Constructors L_equivalence_fs.




Inductive L_eq_container : container -> heap -> container -> heap -> (bijection oid oid ) -> Prop :=
  (*
  | L_eq_same : forall ctn h φ, 
      L_eq_container ctn h ctn h φ *)
  | L_eq_ctn : forall t1 t2 lb1 lb2 sf1 sf2 h1 h2 fs1 fs2 φ,
      flow_to lb1 L_Label = true ->
      flow_to lb2 L_Label = true ->
      L_equivalence_tm t1 h1 t2 h2 φ->
      L_equivalence_fs fs1 h1 fs2 h2 φ ->
      L_equivalence_store sf1 h1 sf2 h2 φ ->
    L_eq_container (Container t1 fs1 lb1 sf1) h1 (Container t2 fs2 lb2 sf2) h2 φ.
Hint Constructors L_eq_container. 

Inductive L_eq_ctns : list container -> heap -> list container -> heap -> (bijection oid oid ) ->Prop :=
  | L_eq_ctns_nil : forall h1 h2  φ,
      L_eq_ctns nil h1 nil h2  φ
  | L_eq_ctns_list : forall ctn1 ctns1 ctn2 ctns2 h1 h2  φ,
      L_eq_container ctn1 h1 ctn2 h2 φ ->
      L_eq_ctns ctns1 h1 ctns2 h2 φ ->
       L_eq_ctns (ctn1 :: ctns1) h1 (ctn2 :: ctns2) h2  φ.
Hint Constructors L_eq_ctns. 

(* only called on configs with high containers at top *)
Fixpoint low_component (ct : Class_table) (ctn : container) (ctns_stack : list container) (h : heap) : config :=
match ctn with 
 | (Container t fs lb sf) =>
       if (flow_to lb L_Label) then (Config ct (Container t fs lb sf) ctns_stack h) 
          else match ctns_stack with 
                | nil => (Config ct (Container null nil L_Label empty_stack_frame) nil h) 
                | ctn :: ctns' => low_component ct ctn ctns' h
                end
end.
Hint Unfold low_component.

Inductive L_equivalence_config : config -> config -> (bijection oid oid ) -> Prop :=
  | L_equivalence_config_L : forall ct t1 fs1 lb1 lb2 sf1 t2 fs2 sf2 ctns1 ctns2 h1 h2 φ, 
      flow_to lb1 L_Label = true ->
      flow_to lb2 L_Label = true ->
      L_eq_container  (Container t1 fs1 lb1 sf1) h1 (Container t2 fs2 lb2 sf2) h2 φ->
      L_eq_ctns ctns1 h1 ctns2 h2 φ ->
      L_equivalence_config (Config ct (Container t1 fs1 lb1 sf1) ctns1 h1) (Config ct (Container t2 fs2 lb2 sf2) ctns2 h2)  φ
  | L_equivalence_config_H : forall ct t1 fs1 lb1 sf1 t2 fs2 lb2 sf2 ctns1 ctns2 h1 h2  φ, 
      flow_to lb1 L_Label = false ->
      flow_to lb2 L_Label = false ->
       L_equivalence_config (low_component ct (Container t1 fs1 lb1 sf1) ctns1 h1)
      (low_component ct (Container t2 fs2 lb2 sf2) ctns2 h2) φ  ->
      L_equivalence_config (Config ct (Container t1 fs1 lb1 sf1) ctns1 h1) (Config ct (Container t2 fs2 lb2 sf2) ctns2 h2)  φ.  
Hint Constructors L_equivalence_config.

(*
Lemma same_config_L_eq : forall ctn ctns ct h,
     L_equivalence_config (Config ct ctn ctns h)  (Config ct ctn ctns h).
Proof with eauto. intros. destruct ctn. case_eq (flow_to l L_Label); intro. 
                  apply L_equivalence_config_L; auto.
apply L_equivalence_config_H; auto. 
generalize dependent t. generalize dependent f.
generalize dependent l. generalize dependent s.
induction ctns; subst; auto. intros. unfold low_component. rewrite H; auto.
intros. destruct a. unfold low_component. rewrite H; auto. 
auto.  fold low_component. case_eq (flow_to l0 L_Label); intro.
destruct ctns; auto. unfold low_component.
rewrite H0; auto. destruct c.  unfold low_component.
rewrite H0; auto.
destruct ctns; auto.
Qed. 
Hint Resolve  same_config_L_eq.
*)

Lemma L_eq_config_transitive : forall c1 c2 c3  φ, 
  L_equivalence_config c1 c2  φ ->
  L_equivalence_config c2 c3  φ ->
  L_equivalence_config c1 c3  φ. 
Proof. Admitted.

Require Import My_tactics. 


Lemma value_L_eq : forall e v h1 h2  φ, 
  value v ->
  L_equivalence_tm e h1 v h2  φ ->
  value e.
Proof. intros. generalize dependent e. 
       induction v; subst; inversion H; auto;
         intros;  inversion H0; subst; auto.
       inversion H3; subst. auto. auto.
       inversion H3; subst. auto. auto.
Qed. Hint Resolve       value_L_eq .  

Lemma value_L_eq2 : forall e v h1 h2  φ, 
  value v ->
  L_equivalence_tm v h1 e h2  φ ->
  value e.
Proof. intros. generalize dependent e.
       induction v; subst; inversion H; auto;
         intros;  inversion H0; subst; auto.
       inversion H3; subst; auto.
       inversion H3; subst; auto.
       
Qed. 
Hint Resolve value_L_eq2.

(*
Lemma value_L_eq : forall e v h1 h2 T1 T2 ct  φ, 
  tm_has_type ct empty_context h1 e T1 -> 
  tm_has_type ct empty_context h2 v T2 -> 
  value v ->
  L_equivalence_tm e h1 v h2  φ ->
  value e.
Proof. intros. generalize dependent e. generalize dependent T1. generalize dependent T2.
       induction v; subst; inversion H1; auto;
         intros;  inversion H2; subst; auto.  inversion H3; subst. auto.
inversion H3; subst; auto.  inversion H5; subst; auto. inversion H4. subst;auto. 
inversion H4. subst;auto.  inversion H5; subst; auto. inversion H4. subst;auto. 
inversion H4. subst;auto.
Qed. 
Hint Resolve value_L_eq.



Lemma value_L_eq2 : forall e v h1 h2 T1 T2 ct  φ, 
  tm_has_type ct empty_context h2 e T2 -> 
  tm_has_type ct empty_context h1 v T1 -> 
  value v ->
  L_equivalence_tm v h1 e h2  φ ->
  value e.
Proof. intros. generalize dependent e. generalize dependent T1. generalize dependent T2.   induction v; subst; inversion H1; auto;
intros;  inversion H2; subst; auto.  inversion H3; subst. auto. 
inversion H3; subst; auto.  inversion H5; subst; auto. inversion H4. subst;auto. 
inversion H4. subst;auto.  inversion H5; subst; auto. inversion H4. subst;auto. 
inversion H4. subst;auto.
Qed. 
Hint Resolve value_L_eq2.
 *)


Require Import My_tactics. 

Lemma lookup_extended_heap : forall h o cls F lb ct ho,
  wfe_heap ct h ->  
  lookup_heap_obj h o =  Some (Heap_OBJ cls F lb) ->
  lookup_heap_obj h o =
     lookup_heap_obj (add_heap_obj h (get_fresh_oid h) ho) o.
Proof. intros. 
  assert (o <> (get_fresh_oid h) ).
  intro contra. assert (lookup_heap_obj h (get_fresh_oid h) = None). 
  apply fresh_oid_heap with ct; auto. rewrite <- contra in H1. rewrite H1 in H0. 
  inversion H0. 
  unfold  lookup_heap_obj. unfold add_heap_obj.
  assert (beq_oid o (get_fresh_oid h) = false).  apply beq_oid_not_equal. auto. 
  rewrite H2.  fold lookup_heap_obj. auto. Qed.
Hint Resolve lookup_extended_heap. 


  

Lemma cls_def_eq : forall o o0 cls fields lx cls0 fields0 lx0 h1' h2'  φ,
    Some (Heap_OBJ cls fields lx) = lookup_heap_obj h1' o ->
    Some (Heap_OBJ cls0 fields0 lx0) = lookup_heap_obj h2' o0 ->
    bijection.left φ o = Some o0 ->
    L_equivalence_heap h1' h2' φ ->
    cls = cls0.
Proof with eauto.
  intros. inversion H2; subst; auto.
  destruct H3 with o o0; auto. rewrite <- H8 in H.  inversion H; subst; auto.
  rewrite <- H9 in H0.  inversion H0; subst; auto.
  apply H12. Qed.
Hint Resolve  cls_def_eq.


Lemma surface_syntax_L_equal : forall body h1 h2 φ, 
    surface_syntax body = true ->
    L_equivalence_heap h1 h2 φ ->
    L_equivalence_tm body h1 body h2 φ.
Proof with eauto. 
  intros.
  induction body; subst;  inversion H; auto;
    try (apply surface_syntax_if in H2; destruct H2; apply IHbody1 in H1; 
         apply IHbody2 in H2; auto).
  apply surface_syntax_triple in H2. destruct H2.
  destruct H2. auto. 
Qed.  
Hint Resolve surface_syntax_L_equal.

Lemma extend_bijection_preserve_tm_eq  {DecOid : forall a1 a2 : oid, Decision (a1 = a2)} :
  forall  φ o o' H1 H2 h1 h2 t1 t2,
     L_equivalence_tm t1 h1 t2 h2  φ ->
     L_equivalence_tm t1 h1 t2  h2 (bijection.extend_bijection φ o o' H1 H2).
Proof with eauto.
  intros.
  induction H; subst; auto.  
  apply L_equivalence_tm_eq_object_L with cls1 F1 lb1 cls2 F2 lb2; auto.
  
  assert (left (extend_bijection φ o o' H1 H2)  o1 = 
          left φ o1).
  apply left_extend_bijection_neq; auto.
  intro contra. subst; auto. rewrite H in H1. inversion H1. 
  rewrite H6. auto.
  apply L_equivalence_tm_eq_object_H with cls1 cls2  F1 lb1  F2 lb2; auto.
Qed.
Hint Resolve  extend_bijection_preserve_tm_eq.


Lemma extend_bijection_preserve_fs_eq  {DecOid : forall a1 a2 : oid, Decision (a1 = a2)} :
  forall  φ o o' H1 H2 h1 h2 fs1 fs2,
    L_equivalence_fs fs1 h1 fs2 h2  φ ->
    L_equivalence_fs fs1 h1 fs2 h2 (bijection.extend_bijection φ o o' H1 H2).
Proof with eauto.
  intros.
  induction H. auto.
  auto.
Qed. Hint Resolve extend_bijection_preserve_fs_eq.

Lemma sf_decision :
  forall (sf: stack_frame) x ,  (exists v,  sf x = Some v) \/ sf x = None.
Proof with eauto.
  intros.
  destruct sf.
  left; exists t; auto.
  right. auto.    
Defined.
Hint Resolve sf_decision.

Lemma extend_bijection_preserve_store_eq  {DecOid : forall a1 a2 : oid, Decision (a1 = a2)} :
  forall  φ o o' H1 H2 h1 h2 sf1 sf2,
    L_equivalence_store sf1 h1 sf2 h2  φ ->
    L_equivalence_store sf1 h1 sf2 h2 (bijection.extend_bijection φ o o' H1 H2).
Proof with eauto.
  intros.
  induction H. auto.
  apply L_equivalence_store_L; auto.

  intros.  destruct H with x o1 cls1 F1 lb1; auto.
  rename x0 into o2. 
  exists o2. destruct H11.
  split; auto.
  
  intros. destruct H0 with x o2 cls2 F2 lb2; auto.
  rename x0 into o1. 
  exists o1. destruct H11.
  split; auto.

  intros. destruct H3 with x lb v1; auto.
  rename x0 into v2.
  exists v2. destruct H10.
  split; auto. 

  intros. destruct H4 with x lb v2; auto.
  rename x0 into v1.
  exists v1. destruct H10.
  split; auto.

  intros. destruct H5 with x lb v1; auto.
  rename x0 into v2.
  exists v2. destruct H10.
  split; auto.

  intros. destruct H6 with x lb v2; auto.
  rename x0 into v1.
  exists v1. destruct H10.
  split; auto.
  
Qed. Hint Resolve  extend_bijection_preserve_store_eq.


Lemma extend_bijection_preserve_ctn_eq  {DecOid : forall a1 a2 : oid, Decision (a1 = a2)} :
  forall  φ o o' H1 H2 h1 h2 ctn1 ctn2,
    L_eq_container ctn1 h1 ctn2 h2 φ ->
    L_eq_container ctn1 h1 ctn2 h2 (bijection.extend_bijection φ o o' H1 H2).
Proof with eauto.
  intros.
  induction H; subst; auto.
  Qed. Hint Resolve extend_bijection_preserve_ctn_eq.

Lemma extend_bijection_preserve_stack_eq  {DecOid : forall a1 a2 : oid, Decision (a1 = a2)} :
  forall  φ o o' H1 H2 h1 h2 ctns_stack1 ctns_stack2,
    L_eq_ctns ctns_stack1 h1 ctns_stack2 h2  φ ->
    L_eq_ctns ctns_stack1 h1 ctns_stack2 h2 (bijection.extend_bijection φ o o' H1 H2).
Proof with eauto.
  intros.
  induction H. auto.
  subst; auto.
Qed. Hint Resolve extend_bijection_preserve_stack_eq.

Lemma extend_heap_preserve_L_eq_tm {DecOid : forall a1 a2 : oid, Decision (a1 = a2)} : forall t1 h1  t2 h2  lb2 cls_def ct  (φ:bijection oid oid)  φ'  (H1: (left φ (get_fresh_oid h1)  = None)) ( H2: (right φ (get_fresh_oid h2)  = None)) ,
  wfe_heap ct h2 ->  wfe_heap ct h1 -> 
  L_equivalence_tm t1 h1 t2 h2 φ ->
  L_equivalence_heap h1 h2 φ ->
  φ' = (extend_bijection φ (get_fresh_oid h1)(get_fresh_oid h2) H1 H2) ->
  (L_equivalence_tm t1 (add_heap_obj h1 (get_fresh_oid h1) 
                                     (Heap_OBJ  cls_def (init_field_map (find_fields cls_def) empty_field_map) lb2))
                    t2 (add_heap_obj h2 (get_fresh_oid h2)
                      (Heap_OBJ  cls_def (init_field_map (find_fields cls_def) empty_field_map) lb2)) φ').
Proof.
  intros t1 h1  t2 h2  lb2 cls_def ct φ φ' H1 H2.
  intros.
  generalize dependent t2. 
  induction t1; intros; inversion H3; subst; auto.

  apply L_equivalence_tm_eq_object_L with cls1 F1 lb1 cls2 F2 lb0; auto.
  assert (left (extend_bijection φ ( get_fresh_oid h1) ( get_fresh_oid h2) H1 H2)  o = 
          left φ o).
  apply left_extend_bijection_neq; auto.
  intro contra. subst; auto. rewrite H7 in H1. inversion H1. 
  rewrite H5. auto.
  assert (o <> get_fresh_oid h1).
  apply lookup_extend_heap_fresh_oid with
      ct
      (Heap_OBJ cls1 F1 lb1); auto.
  apply beq_oid_not_equal in H5; auto.
  unfold lookup_heap_obj. unfold add_heap_obj.
  rewrite H5. fold lookup_heap_obj. auto.

  assert (o2 <> get_fresh_oid h2).
  apply lookup_extend_heap_fresh_oid with
      ct
      (Heap_OBJ cls2 F2 lb0); auto.
  apply beq_oid_not_equal in H5; auto.
  unfold lookup_heap_obj. unfold add_heap_obj.
  rewrite H5. fold lookup_heap_obj. auto.

  apply L_equivalence_tm_eq_object_H with cls1 cls2  F1 lb1 F2 lb0; auto.

    assert (o <> get_fresh_oid h1).
  apply lookup_extend_heap_fresh_oid with
      ct
      (Heap_OBJ cls1 F1 lb1); auto.
  apply beq_oid_not_equal in H5; auto.
  unfold lookup_heap_obj. unfold add_heap_obj.
  rewrite H5. fold lookup_heap_obj. auto.

  assert (o2 <> get_fresh_oid h2).
  apply lookup_extend_heap_fresh_oid with
      ct
      (Heap_OBJ cls2 F2 lb0); auto.
  apply beq_oid_not_equal in H5; auto.
  unfold lookup_heap_obj. unfold add_heap_obj.
  rewrite H5. fold lookup_heap_obj. auto.
Qed.
Hint Resolve  extend_heap_preserve_L_eq_tm.

Lemma extend_heap_preserve_L_eq_fs {DecOid : forall a1 a2 : oid, Decision (a1 = a2)} : forall fs1 h1  fs2 h2  lb2 cls_def ct  (φ:bijection oid oid)  φ'  (H1: (left φ (get_fresh_oid h1)  = None)) ( H2: (right φ (get_fresh_oid h2)  = None)) ,
  wfe_heap ct h2 ->  wfe_heap ct h1 -> 
  L_equivalence_fs fs1 h1 fs2 h2 φ ->
  L_equivalence_heap h1 h2 φ ->
  φ' = (extend_bijection φ (get_fresh_oid h1)(get_fresh_oid h2) H1 H2) ->
  (L_equivalence_fs fs1 (add_heap_obj h1 (get_fresh_oid h1) 
                                     (Heap_OBJ  cls_def (init_field_map (find_fields cls_def) empty_field_map) lb2))
                    fs2 (add_heap_obj h2 (get_fresh_oid h2)
                      (Heap_OBJ  cls_def (init_field_map (find_fields cls_def) empty_field_map) lb2)) φ').
Proof.
  intros fs1 h1  fs2 h2  lb2 cls_def ct φ φ' H1 H2.
  intros.
  generalize dependent fs2. 
  induction fs1; intros; inversion H3; subst; auto.
  apply  L_equal_fs; auto.
  apply extend_heap_preserve_L_eq_tm with ct φ H1 H2; auto. 
Qed. Hint Resolve  extend_heap_preserve_L_eq_fs.

Lemma extend_heap_preserve_L_eq_store {DecOid : forall a1 a2 : oid, Decision (a1 = a2)} : forall sf1 h1  sf2 h2  lb2 cls_def ct  (φ:bijection oid oid)  φ'  (H1: (left φ (get_fresh_oid h1)  = None)) ( H2: (right φ (get_fresh_oid h2)  = None)) ,
  wfe_heap ct h2 ->  wfe_heap ct h1 -> 
  L_equivalence_store sf1 h1 sf2 h2 φ ->
  L_equivalence_heap h1 h2 φ ->
  wfe_stack_frame ct h1 sf1 ->
   wfe_stack_frame ct h2 sf2 ->
  φ' = (extend_bijection φ (get_fresh_oid h1)(get_fresh_oid h2) H1 H2) ->
  (L_equivalence_store sf1 (add_heap_obj h1 (get_fresh_oid h1) 
                                     (Heap_OBJ  cls_def (init_field_map (find_fields cls_def) empty_field_map) lb2))
                    sf2 (add_heap_obj h2 (get_fresh_oid h2)
                      (Heap_OBJ  cls_def (init_field_map (find_fields cls_def) empty_field_map) lb2)) φ').
Proof.
  intros sf1 h1  sf2 h2  lb2 cls_def ct φ φ' H1 H2.
  intros.
  inversion H4; subst; auto.
  apply L_equivalence_store_L; auto.
  intros. inversion H5; subst; auto.

  assert (wfe_stack_val ct h1 (ObjId o1)).
  apply  H15 in H7; auto.
  inversion H7; subst; auto.
  inversion H16; subst; auto. 
  assert (o1 <> get_fresh_oid h1).
  apply lookup_extend_heap_fresh_oid with
      ct
      (Heap_OBJ (class_def cls_name field_defs method_defs) F lo); auto.
  apply beq_oid_not_equal in H17; auto.
  unfold lookup_heap_obj in H13. unfold add_heap_obj  in H13.
  rewrite H17 in H13. fold lookup_heap_obj in H13.

  inversion H3; subst; auto.   
  destruct H20 with x o1 cls1 F1 lb1; auto. rename x0 into o2.
  exists o2.
  destruct H28. split; auto. 
  apply extend_heap_preserve_L_eq_tm with ct φ H1 H2; auto. 

  intros.  inversion H6; subst; auto.

  assert (wfe_stack_val ct h2 (ObjId o2)).
  apply  H15 in H7; auto.
  inversion H7; subst; auto.
  inversion H16; subst; auto. 
  assert (o2 <> get_fresh_oid h2).
  apply lookup_extend_heap_fresh_oid with
      ct
      (Heap_OBJ (class_def cls_name field_defs method_defs) F lo); auto.
  apply beq_oid_not_equal in H17; auto.
  unfold lookup_heap_obj in H13. unfold add_heap_obj  in H13.
  rewrite H17 in H13. fold lookup_heap_obj in H13.

  inversion H3; subst; auto.   
  destruct H21 with x o2 cls2 F2 lb0; auto. rename x0 into o1.
  exists o1. destruct H28. split; auto. 
  apply extend_heap_preserve_L_eq_tm with ct φ H1 H2; auto.

  (*(v_l v1 lb) left to right*)
  intros.
  inversion H3; subst; auto.
  destruct H16 with x lb v1; auto.
  rename x0 into v2.
  destruct H21.
  exists v2; split; auto. 
  apply extend_heap_preserve_L_eq_tm with ct φ H1 H2; auto.

  (*(v_l v1 lb) right to left *)
  intros.
  inversion H3; subst; auto.
  destruct H17 with x lb v2; auto.
  rename x0 into v1.
  destruct H21.
  exists v1; split; auto. 
  apply extend_heap_preserve_L_eq_tm with ct φ H1 H2; auto.

  (*(v_opa_l v1 lb) left to right*)
  intros.
  inversion H3; subst; auto.
  destruct H18 with x lb v1; auto.
  rename x0 into v2.
  destruct H21.
  exists v2; split; auto. 
  apply extend_heap_preserve_L_eq_tm with ct φ H1 H2; auto.

  (*(v_opa_l v1 lb) right to left *)
  intros.
  inversion H3; subst; auto.
  destruct H19 with x lb v2; auto.
  rename x0 into v1.
  destruct H21.
  exists v1; split; auto. 
  apply extend_heap_preserve_L_eq_tm with ct φ H1 H2; auto.

  (*null*)
  intros. inversion H3; subst; auto.
  
Qed. Hint Resolve  extend_heap_preserve_L_eq_store. 



Lemma extend_heap_preserve_L_eq_ctn {DecOid : forall a1 a2 : oid, Decision (a1 = a2)} :
  forall h1  h2  lb cls_def ct  (φ:bijection oid oid)  φ'
         (H1: (left φ (get_fresh_oid h1)  = None)) ( H2: (right φ (get_fresh_oid h2)  = None))
  ctn1 ctn2,
    wfe_heap ct h2 ->  wfe_heap ct h1 ->
    valid_ctn ct ctn1 h1 -> valid_ctn ct ctn2 h2  ->
  L_eq_container ctn1 h1 ctn2 h2 φ ->
  L_equivalence_heap h1 h2 φ ->
  φ' = (extend_bijection φ (get_fresh_oid h1)(get_fresh_oid h2) H1 H2) ->
  (L_eq_container ctn1 (add_heap_obj h1 (get_fresh_oid h1) 
                                     (Heap_OBJ  cls_def (init_field_map (find_fields cls_def) empty_field_map) lb))
                    ctn2 (add_heap_obj h2 (get_fresh_oid h2)
                      (Heap_OBJ  cls_def (init_field_map (find_fields cls_def) empty_field_map) lb)) φ').
Proof.
  intros h1  h2  lb cls_def ct φ  φ' H1 H2 ctn1 ctn2.
  intros.
  
  generalize dependent ctn2. 
  induction ctn1; intros;subst; auto;
  inversion H5; subst; auto.
  apply  L_eq_ctn; auto. 
  apply extend_heap_preserve_L_eq_tm with ct φ H1 H2; auto.
  apply extend_heap_preserve_L_eq_fs with ct φ H1 H2; auto.
  apply extend_heap_preserve_L_eq_store with ct φ H1 H2; auto.
  inversion H3; auto. inversion H4; auto. 
Qed. Hint Resolve extend_heap_preserve_L_eq_ctn. 

Lemma extend_heap_preserve_L_eq_ctns {DecOid : forall a1 a2 : oid, Decision (a1 = a2)} : forall ctns1 h1  ctns2 h2  lb2 cls_def ct  (φ:bijection oid oid)  φ'  (H1: (left φ (get_fresh_oid h1)  = None)) ( H2: (right φ (get_fresh_oid h2)  = None)) ,
  wfe_heap ct h2 ->  wfe_heap ct h1 -> 
  L_eq_ctns ctns1 h1 ctns2 h2 φ ->
  L_equivalence_heap h1 h2 φ ->
  valid_ctns ct ctns1 h1 ->
  valid_ctns ct ctns2 h2 -> 
  φ' = (extend_bijection φ (get_fresh_oid h1)(get_fresh_oid h2) H1 H2) ->
  (L_eq_ctns ctns1 (add_heap_obj h1 (get_fresh_oid h1) 
                                     (Heap_OBJ  cls_def (init_field_map (find_fields cls_def) empty_field_map) lb2))
                    ctns2 (add_heap_obj h2 (get_fresh_oid h2)
                      (Heap_OBJ  cls_def (init_field_map (find_fields cls_def) empty_field_map) lb2)) φ').
Proof.
  intros ctns1 h1 ctns2 h2  lb2 cls_def ct φ φ' H1 H2.
  intros.
  generalize dependent ctns2.  
  induction ctns1; intros; inversion H3; subst; auto.
  apply L_eq_ctns_list; auto.  
  apply extend_heap_preserve_L_eq_ctn with ct φ H1 H2; auto.
  inversion H5; auto. inversion H6; auto.
  apply   IHctns1; auto. 
  inversion H5; auto. inversion H6; auto.
Qed. Hint Resolve extend_heap_preserve_L_eq_ctns.


Lemma low_component_with_L_Label : forall ct t fs lb sf ctns h,
    flow_to lb L_Label = true ->
    low_component ct (Container t fs lb sf) ctns h =
    Config ct (Container t fs lb sf) ctns h.
Proof.
  intros .     
  induction ctns.
  unfold low_component.  rewrite H. auto.
  unfold low_component.  rewrite H. auto.
Qed. Hint Resolve low_component_with_L_Label.

  
Lemma low_component_irrelevant : forall ctn1 ctn2 ctns1 ctns2 h1 h2 φ ct,
      L_eq_container ctn1 h1 ctn2 h2 φ ->
      L_eq_ctns ctns1 h1 ctns2 h2 φ ->
      L_equivalence_config (low_component ct ctn1 ctns1 h1) (low_component ct ctn2 ctns2 h2) φ.
Proof with eauto.
  intros. destruct ctn1. destruct ctn2.
  inversion H; subst; auto.
  case_eq (flow_to l0 L_Label); intro.
  generalize dependent ctns2. 
   induction ctns1. intros. 
   inversion H0; subst; auto. unfold low_component. rewrite H1; auto.
   intros.
   rewrite H12. auto. 

   intros. 
   inversion H0; subst; auto. unfold low_component. rewrite H1; auto.
   rewrite H12; auto. rewrite H13 in H1. inversion H1. 
   
(*
   generalize dependent t0. generalize dependent f0.
   generalize dependent l0. generalize dependent s0. 
   generalize dependent ctns2. 
  induction ctns1. intros. inversion H0; subst; auto.
  unfold low_component. rewrite H1; auto.
  
  intros. inversion H0; subst; auto. 
  unfold low_component. rewrite H1; auto. fold low_component.
  destruct a. destruct ctn2. inversion H4; subst; auto.
  case_eq (flow_to l1 L_Label); intro.
  assert ((low_component ct (Container t1 f1 l1 s1) ctns1 h2) =
          Config ct (Container t1 f1 l1 s1) ctns1 h2 ).
  apply low_component_with_L_Label. auto. rewrite H3.
  assert ((low_component ct (Container t1 f1 l1 s1) ctns3 h2) =
          Config ct (Container t1 f1 l1 s1) ctns3 h2 ).
  apply low_component_with_L_Label. auto. rewrite H6.
  auto.
  apply IHctns1; auto. 

  assert ((low_component ct (Container t f l s) ctns1 h2) =
          Config ct (Container t f l s) ctns1 h2 ).
  apply low_component_with_L_Label. auto. rewrite H2.
  assert ((low_component ct (Container t1 f1 l1 s1) ctns3 h2) =
          Config ct (Container t1 f1 l1 s1) ctns3 h2 ).
  apply low_component_with_L_Label. auto. rewrite H3.
  auto.

  assert ((low_component ct (Container t f l s) ctns1 h1) =
          Config ct (Container t f l s) ctns1 h1 ).
  apply low_component_with_L_Label. auto. rewrite H1.
  assert ((low_component ct (Container t0 f0 l0 s0) ctns2 h2) =
          Config ct (Container t0 f0 l0 s0) ctns2 h2 ).
  apply low_component_with_L_Label. auto. rewrite H2.
  auto.*)
Qed.
Hint Resolve low_component_irrelevant.


             
Ltac inconsist_label :=
  match goal with
  | H1 : flow_to ?T ?X  = true |- _
    => match goal with
       | H2 : flow_to ?T ?X  = false |- _                        
         => solve [rewrite H1 in H2; inversion H2]
       end
  end.       

Ltac inconsist :=
  match goal with
  | H1 : ?T  = true |- _
    => match goal with
       | H2 : ?T  = false |- _                        
         => solve [rewrite H1 in H2; inversion H2]
       end
  end.     

Lemma update_field_preserve_L_eq_tm {DecOid : forall a1 a2 : oid, Decision (a1 = a2)} :
  forall  (φ:bijection oid oid) h1 h2 ct cls F lo o lb1 lx
          cls0 F0 lo0 o0 lb2 lx0 t1 t2 v v0 f0,
  wfe_heap ct h2 ->  wfe_heap ct h1 -> 
  L_equivalence_heap h1 h2 φ ->
  L_equivalence_tm t1 h1 t2 h2 φ ->
  Some (Heap_OBJ cls F lo) = lookup_heap_obj h1 o ->
  flow_to lo (join_label lb1 lx) = true ->
  Some (Heap_OBJ cls0 F0 lo0) = lookup_heap_obj h2 o0 ->
  flow_to lo0 (join_label lb2 lx0) = true ->
  L_equivalence_tm (ObjId o) h1 (ObjId o0) h2 φ ->
  L_equivalence_tm (v_opa_l v lx) h1 (v_opa_l v0 lx0) h2 φ ->
  flow_to lb1 L_Label = true ->
  flow_to lb2 L_Label = true ->
  value v ->
  value v0 ->
  L_equivalence_tm t1 (update_heap_obj h1 o (Heap_OBJ cls (fields_update F f0 v) lo))
                    t2 (update_heap_obj h2 o0 (Heap_OBJ cls0 (fields_update F0 f0 v0) lo0)) φ.
Proof with eauto. 
  intros φ h1 h2 ct cls F lo o lb1 lx cls0 F0 lo0 o0 lb2 lx0 t1 t2 v v0 f0.
  intros.
  inversion H8; subst; auto.
  assert ( flow_to (join_label lb1 lx0) L_Label = true).
  apply join_L_label_flow_to_L; auto.
  apply L_Label_flow_to_L in H13. rewrite H13 in H4. 

  assert ( flow_to (join_label lb2 lx0) L_Label = true).
  apply join_L_label_flow_to_L; auto.
  apply L_Label_flow_to_L in H14. rewrite H14 in H6. 

  generalize dependent t2.  
  induction t1; intros;inversion H2; subst; auto.

  case_eq (beq_oid o1 o); intro.
  apply beq_oid_equal in H15.
  remember (update_heap_obj h1 o (Heap_OBJ cls (fields_update F f0 v) lo))  as h'.
  assert (Some  (Heap_OBJ cls (fields_update F f0 v) lo) = lookup_heap_obj h' o).
  apply lookup_updated with h1 (Heap_OBJ cls1 F1 lb0) ; rewrite <- H15; subst;  auto.
  case_eq (beq_oid o3 o0); intro.
  apply beq_oid_equal in H26.
  remember (update_heap_obj h2 o0 (Heap_OBJ cls0 (fields_update F0 f0 v0) lo0))  as h2'.
  assert (Some   (Heap_OBJ cls0 (fields_update F0 f0 v0) lo0)  = lookup_heap_obj h2' o0).
  apply lookup_updated with h2 (Heap_OBJ cls2 F2 lb3) ; rewrite <- H26; subst;  auto.
  apply L_equivalence_tm_eq_object_L with cls (fields_update F f0 v) lo cls0
                                          (fields_update F0 f0 v0) lo0; subst; auto.
  remember (update_heap_obj h2 o0 (Heap_OBJ cls0 (fields_update F0 f0 v0) lo0))  as h2'.
  assert (Some (Heap_OBJ cls2 F2 lb3) = lookup_heap_obj h2' o3).
  apply lookup_updated_not_affected with  o0 (Heap_OBJ cls0 (fields_update F0 f0 v0) lo0) h2; auto. intro contra. rewrite contra in H26. pose proof (beq_oid_same o0).
  rewrite H27 in H26. inversion H26.
  apply L_equivalence_tm_eq_object_L with cls (fields_update F f0 v) lo cls2
                                          F2 lb3; subst; auto.

  remember (update_heap_obj h1 o (Heap_OBJ cls (fields_update F f0 v) lo))  as h'.
  assert (  Some (Heap_OBJ cls1 F1 lb0)  = lookup_heap_obj h' o1).
  apply lookup_updated_not_affected with  o (Heap_OBJ cls (fields_update F f0 v) lo) h1; auto.
  intro contra. rewrite contra in H15. pose proof (beq_oid_same o).
  rewrite H25 in H15. inversion H15.
  case_eq (beq_oid o3 o0); intro.
  apply beq_oid_equal in H26.
  remember (update_heap_obj h2 o0 (Heap_OBJ cls0 (fields_update F0 f0 v0) lo0))  as h2'.
  assert (Some   (Heap_OBJ cls0 (fields_update F0 f0 v0) lo0)  = lookup_heap_obj h2' o0).
  apply lookup_updated with h2 (Heap_OBJ cls2 F2 lb3) ; rewrite <- H26; subst;  auto.
  apply L_equivalence_tm_eq_object_L with cls1 F1 lb0 cls0
                                          (fields_update F0 f0 v0) lo0; subst; auto.
  remember (update_heap_obj h2 o0 (Heap_OBJ cls0 (fields_update F0 f0 v0) lo0))  as h2'.
  assert (Some (Heap_OBJ cls2 F2 lb3) = lookup_heap_obj h2' o3).
  apply lookup_updated_not_affected with  o0 (Heap_OBJ cls0 (fields_update F0 f0 v0) lo0) h2; auto. intro contra. rewrite contra in H26. pose proof (beq_oid_same o0).
  rewrite H27 in H26. inversion H26.
  apply L_equivalence_tm_eq_object_L with cls1 F1 lb0 cls2
                                          F2 lb3; subst; auto.


  case_eq (beq_oid o1 o); intro.
  apply beq_oid_equal in H15. rewrite H15 in H16.
  rewrite <- H16 in H3; inversion H3; subst; auto. rewrite H18 in H4; inversion H4.
  
  case_eq (beq_oid o3 o0); intro.
  apply beq_oid_equal in H24.
  rewrite H24 in H20. rewrite <- H20 in H5; inversion H5; subst; auto.
  rewrite H21 in H6; inversion H6. 
  
  remember (update_heap_obj h2 o0 (Heap_OBJ cls0 (fields_update F0 f0 v0) lo0))  as h2'.
  assert (Some (Heap_OBJ cls2 F2 lb3) = lookup_heap_obj h2' o3).
  apply lookup_updated_not_affected with  o0 (Heap_OBJ cls0 (fields_update F0 f0 v0) lo0) h2; auto. intro contra. rewrite contra in H24. pose proof (beq_oid_same o0).
  rewrite H25 in H24. inversion H24.

  remember (update_heap_obj h1 o (Heap_OBJ cls (fields_update F f0 v) lo))  as h'.
  assert (  Some (Heap_OBJ cls1 F1 lb0)  = lookup_heap_obj h' o1).
  apply lookup_updated_not_affected with  o (Heap_OBJ cls (fields_update F f0 v) lo) h1; auto.
  intro contra. rewrite contra in H15. pose proof (beq_oid_same o).
  try (inconsist).
   apply L_equivalence_tm_eq_object_H with cls1 cls2  F1 lb0  
                                          F2 lb3; subst; auto.
 
  
  assert ( flow_to (join_label lb1 lx) L_Label = false).
  apply flow_join_label with lx lb1; auto. 
  assert ( flow_to (join_label lb2 lx0) L_Label = false).
  apply flow_join_label with lx0 lb2; auto. 

  
  assert (flow_to lo L_Label = false).
  apply flow_transitive with (join_label lb1 lx); auto. 
  assert (flow_to lo0 L_Label = false).
  apply flow_transitive with (join_label lb2 lx0); auto.


  generalize dependent t2.  
  induction t1; intros;inversion H2; subst; auto.

  case_eq (beq_oid o1 o); intro.
  apply beq_oid_equal in H18.
  rewrite H18 in H21. rewrite <- H21 in H3; inversion H3; subst; auto.
  rewrite H24 in H15; inversion H15. 

  case_eq (beq_oid o3 o0); intro.
  apply beq_oid_equal in H27.
  rewrite H27 in H25. rewrite <- H25 in H5; inversion H5; subst; auto.
  try (inconsist_label).

  remember (update_heap_obj h1 o (Heap_OBJ cls (fields_update F f0 v) lo))  as h'.
  assert (  Some (Heap_OBJ cls1 F1 lb0)  = lookup_heap_obj h' o1).
  apply lookup_updated_not_affected with  o (Heap_OBJ cls (fields_update F f0 v) lo) h1; auto.
  intro contra. rewrite contra in H18.  pose proof (beq_oid_same o).
  rewrite H28 in H18. inversion H18.

  remember (update_heap_obj h2 o0 (Heap_OBJ cls0 (fields_update F0 f0 v0) lo0))  as h2'.
  assert (Some (Heap_OBJ cls2 F2 lb3) = lookup_heap_obj h2' o3).
  apply lookup_updated_not_affected with  o0 (Heap_OBJ cls0 (fields_update F0 f0 v0) lo0) h2; auto.
  intro contra. rewrite contra in H27. pose proof (beq_oid_same o0).
  rewrite H29 in H27. inversion H27.
  apply L_equivalence_tm_eq_object_L with cls1 F1 lb0 cls2
                                          F2 lb3; subst; auto.


  case_eq (beq_oid o1 o); intro.
  apply beq_oid_equal in H18.
  remember (update_heap_obj h1 o (Heap_OBJ cls (fields_update F f0 v) lo))  as h'.
  assert (Some  (Heap_OBJ cls (fields_update F f0 v) lo) = lookup_heap_obj h' o).
  apply lookup_updated with h1 (Heap_OBJ cls1 F1 lb0) ; rewrite <- H18; subst;  auto.
  case_eq (beq_oid o3 o0); intro.
  apply beq_oid_equal in H27.
  subst; auto.
  rewrite <- H24 in H5; inversion H5; subst; auto. 
  rewrite <- H20 in H3; inversion H3; subst; auto.
  remember (update_heap_obj h2 o0 (Heap_OBJ cls2 (fields_update F2 f0 v0) lb3))  as h2'.
  assert (Some (Heap_OBJ cls2 (fields_update F2 f0 v0) lb3)  = lookup_heap_obj h2' o0).
  apply lookup_updated with h2  (Heap_OBJ cls2 F2 lb3) ;  subst;  auto.
  
  apply L_equivalence_tm_eq_object_H with cls1 cls2 (fields_update F1 f0 v) lb0
                                          (fields_update F2 f0 v0) lb3; subst; auto.
  subst; auto.
  rewrite <- H20 in H3; inversion H3; subst; auto.
  remember (update_heap_obj h2 o0 (Heap_OBJ cls0 (fields_update F0 f0 v0) lo0))  as h2'.
  
  assert (Some (Heap_OBJ cls2 F2 lb3)  = lookup_heap_obj h2' o3).
  apply lookup_updated_not_affected with  o0 (Heap_OBJ cls0 (fields_update F0 f0 v0) lo0) h2; auto.
  intro contra. rewrite contra in H27. pose proof (beq_oid_same o0).
  try (inconsist).
  apply L_equivalence_tm_eq_object_H with cls1 cls2 (fields_update F1 f0 v) lb0 
                                          F2 lb3; subst; auto.
  
 remember ((update_heap_obj h1 o (Heap_OBJ cls (fields_update F f0 v) lo)))  as h'.
  assert (  Some (Heap_OBJ cls1 F1 lb0)  = lookup_heap_obj h' o1).
  apply lookup_updated_not_affected with  o (Heap_OBJ cls (fields_update F f0 v) lo) h1; auto.
  intro contra. rewrite contra in H18. pose proof (beq_oid_same o).
  try (inconsist).
  case_eq (beq_oid o3 o0); intro.  
  apply beq_oid_equal in H27.
  subst; auto.
  rewrite <- H24 in H5; inversion H5; subst; auto.   
  remember ((update_heap_obj h2 o0 (Heap_OBJ cls2 (fields_update F2 f0 v0) lb3)))  as h2'.
  assert (Some (Heap_OBJ cls2 (fields_update F2 f0 v0) lb3)  = lookup_heap_obj h2' o0).
  apply lookup_updated with h2 (Heap_OBJ cls2 F2 lb3); subst;  auto.
  apply L_equivalence_tm_eq_object_H with cls1 cls2 F1 lb0 
                                          (fields_update F2 f0 v0) lb3; subst; auto.
  remember (update_heap_obj h2 o0 (Heap_OBJ cls0 (fields_update F0 f0 v0) lo0))  as h2'.
  
  assert (Some (Heap_OBJ cls2 F2 lb3) = lookup_heap_obj h2' o3).
  apply lookup_updated_not_affected with  o0 (Heap_OBJ cls0 (fields_update F0 f0 v0) lo0) h2; auto.
  intro contra.
  rewrite contra in H27. pose proof (beq_oid_same o0).
  try (inconsist).
  apply L_equivalence_tm_eq_object_H with cls1 cls2 F1 lb0
                                          F2 lb3; subst; auto.
Qed.  Hint Resolve  update_field_preserve_L_eq_tm.



Lemma update_field_preserve_L_eq_fs {DecOid : forall a1 a2 : oid, Decision (a1 = a2)} :
  forall  (φ:bijection oid oid) h1 h2 ct cls F lo o lb1 lx
          cls0 F0 lo0 o0 lb2 lx0 fs1 fs2  v v0 f0,
  wfe_heap ct h2 ->  wfe_heap ct h1 -> 
  L_equivalence_heap h1 h2 φ ->
  L_equivalence_fs fs1 h1 fs2 h2 φ ->
  Some (Heap_OBJ cls F lo) = lookup_heap_obj h1 o ->
  flow_to lo (join_label lb1 lx) = true ->
  Some (Heap_OBJ cls0 F0 lo0) = lookup_heap_obj h2 o0 ->
  flow_to lo0 (join_label lb2 lx0) = true ->
  L_equivalence_tm (ObjId o) h1 (ObjId o0) h2 φ ->
  L_equivalence_tm (v_opa_l v lx) h1 (v_opa_l v0 lx0) h2 φ ->
  flow_to lb1 L_Label = true ->
  flow_to lb2 L_Label = true ->
  value v ->
  value v0 ->
  L_equivalence_fs fs1 (update_heap_obj h1 o (Heap_OBJ cls (fields_update F f0 v) lo))
                    fs2 (update_heap_obj h2 o0 (Heap_OBJ cls0 (fields_update F0 f0 v0) lo0)) φ.
Proof with eauto. 
  intros φ h1 h2 ct cls F lo o lb1 lx cls0 F0 lo0 o0 lb2 lx0 fs1 fs2 v v0 f0.
  intros.
  generalize dependent fs2. 
  induction fs1; intros; inversion H2; subst; auto.
  apply  L_equal_fs; auto.
  apply update_field_preserve_L_eq_tm with ct lb1 lx lb2 lx0; auto. 
Qed. Hint Resolve update_field_preserve_L_eq_fs.


Lemma update_field_preserve_L_eq_store {DecOid : forall a1 a2 : oid, Decision (a1 = a2)} :
  forall  (φ:bijection oid oid) h1 h2 ct cls F lo o lb1 lx
          cls0 F0 lo0 o0 lb2 lx0 sf1 sf2  v v0 f0,
    wfe_heap ct h2 ->  wfe_heap ct h1 ->
    wfe_stack_frame ct h1 sf1 -> wfe_stack_frame ct h2 sf2 ->
  L_equivalence_heap h1 h2 φ ->
  L_equivalence_store sf1 h1 sf2 h2 φ ->
  Some (Heap_OBJ cls F lo) = lookup_heap_obj h1 o ->
  flow_to lo (join_label lb1 lx) = true ->
  Some (Heap_OBJ cls0 F0 lo0) = lookup_heap_obj h2 o0 ->
  flow_to lo0 (join_label lb2 lx0) = true ->
  L_equivalence_tm (ObjId o) h1 (ObjId o0) h2 φ ->
  L_equivalence_tm (v_opa_l v lx) h1 (v_opa_l v0 lx0) h2 φ ->
  flow_to lb1 L_Label = true ->
  flow_to lb2 L_Label = true ->
  value v ->
  value v0 ->
  L_equivalence_store sf1 (update_heap_obj h1 o (Heap_OBJ cls (fields_update F f0 v) lo))
                    sf2 (update_heap_obj h2 o0 (Heap_OBJ cls0 (fields_update F0 f0 v0) lo0)) φ.
Proof with eauto. 
  intros φ h1 h2 ct cls F lo o lb1 lx cls0 F0 lo0 o0 lb2 lx0 sf1 sf2 v v0 f0.
  intros.

  inversion H3; subst; auto.
  
  intros. inversion H10; subst; auto.
  inversion H4; subst; auto.
  apply L_equivalence_store_L; auto. intros. 
  
  case_eq (beq_oid o1 o); intros.
  apply beq_oid_equal in H34. rewrite <- H34 in H5.
  destruct H20 with x o1 cls F lo; auto.
  assert (flow_to (join_label lb1 lx0) L_Label = true).
  apply join_L_label_flow_to_L; auto.
  apply L_Label_flow_to_L in H35.
  rewrite H35 in H6. auto.
  
  rename x0 into o2. 
  exists o2. destruct H35. split; auto.
  apply update_field_preserve_L_eq_tm with ct lb1 lx0 lb2 lx0 ; auto.
  rewrite H34 in H5; auto.
  
  assert ( Some (Heap_OBJ cls1 F1 lb0) = lookup_heap_obj h1 o1).
  apply lookup_updated_heap_old_obj with cls (fields_update F f0 v) lo o; auto. 
  destruct H20 with x o1 cls1 F1 lb0; auto.
  rename x0 into o2. destruct H36; subst; auto. 
  exists o2. split; auto.
  apply update_field_preserve_L_eq_tm with ct lb1 lx0 lb2 lx0 ; auto.

  intros. 
  case_eq (beq_oid o2 o0); intro.
  apply beq_oid_equal in H34. rewrite <- H34 in H7.
  destruct H21 with x o2 cls0 F0 lo0; auto.
  assert (flow_to (join_label lb2 lx0) L_Label = true).
  apply join_L_label_flow_to_L; auto.
  apply L_Label_flow_to_L in H35.
  rewrite H35 in H8. auto.
  
  rename x0 into o1. 
  exists o1. destruct H35. split; auto.
  apply update_field_preserve_L_eq_tm with ct lb1 lx0 lb2 lx0 ; auto.
  rewrite H34 in H7; auto.
  
  assert ( Some (Heap_OBJ cls2 F2 lb0) = lookup_heap_obj h2 o2).
  apply lookup_updated_heap_old_obj with cls0 (fields_update F0 f0 v0) lo0 o0; auto. 
  destruct H21 with x o2 cls2 F2 lb0; auto.
  rename x0 into o1. destruct H36; subst; auto. 
  exists o1. split; auto.
  apply update_field_preserve_L_eq_tm with ct lb1 lx0 lb2 lx0 ; auto.

  (* (v_l v1 lb)*)
  intros.
  inversion H4; subst; auto.
  destruct H35 with x lb v1; auto.
  destruct H40.
  rename x0 into v2.
  exists v2; split; auto. 
  apply update_field_preserve_L_eq_tm with ct lb1 lx0 lb2 lx0 ; auto.

  intros.
  inversion H4; subst; auto.
  destruct H36 with x lb v2; auto.
  destruct H40.
  rename x0 into v1.
  exists v1; split; auto. 
  apply update_field_preserve_L_eq_tm with ct lb1 lx0 lb2 lx0 ; auto.
  
  (* (v_opa_l v1 lb)*)
  intros.
  inversion H4; subst; auto.
  destruct H37 with x lb v1; auto.
  destruct H40.
  rename x0 into v2.
  exists v2; split; auto. 
  apply update_field_preserve_L_eq_tm with ct lb1 lx0 lb2 lx0 ; auto.

  intros.
  inversion H4; subst; auto.
  destruct H38 with x lb v2; auto.
  destruct H40.
  rename x0 into v1.
  exists v1; split; auto. 
  apply update_field_preserve_L_eq_tm with ct lb1 lx0 lb2 lx0 ; auto.
  

  apply L_equivalence_store_L; auto. intros.
  
  case_eq (beq_oid o1 o); intro.
  assert ( Some (Heap_OBJ cls1 F1 lb0) = Some (Heap_OBJ cls (fields_update F f0 v) lo)).
  apply lookup_updated_heap_new_obj with h1 o1 o; auto.
  
  inversion H25. subst. auto.

  assert (flow_to (join_label lb1 lx) L_Label = false).
  apply flow_join_label with lx lb1; auto.

  assert (flow_to lo L_Label = false).
  apply  flow_transitive with (join_label lb1 lx) ; auto.
  try (inconsist_label).
  
  assert ( Some (Heap_OBJ cls1 F1 lb0) = lookup_heap_obj h1 o1).
  apply lookup_updated_heap_old_obj with cls (fields_update F f0 v) lo o; auto.

  inversion H4; subst; auto.
  destruct H27 with x o1 cls1 F1 lb0; auto.
  rename x0 into o2. destruct H36; subst; auto. 
  exists o2. split; auto.
  apply update_field_preserve_L_eq_tm with ct lb1 lx lb2 lx0 ; auto.

  intros.
  
  case_eq (beq_oid o2 o0); intro.
  assert ( Some (Heap_OBJ cls2 F2 lb0) = Some (Heap_OBJ cls0 (fields_update F0 f0 v0) lo0)).
  apply lookup_updated_heap_new_obj with h2 o2 o0; auto.
  inversion H25. subst; auto.

  assert (flow_to (join_label lb2 lx0) L_Label = false).
  apply flow_join_label with lx0 lb2; auto.

  assert (flow_to lo0 L_Label = false).
  apply  flow_transitive with (join_label lb2 lx0) ; auto.
  try (inconsist_label).
  
  assert ( Some (Heap_OBJ cls2 F2 lb0) = lookup_heap_obj h2 o2).
  apply lookup_updated_heap_old_obj with cls0 (fields_update F0 f0 v0) lo0 o0; auto.

  inversion H4; subst; auto.
  destruct H28 with x o2 cls2 F2 lb0; auto.
  rename x0 into o1. destruct H36; subst; auto. 
  exists o1. split; auto.
  apply update_field_preserve_L_eq_tm with ct lb1 lx lb2 lx0 ; auto.
  
  (* (v_l v1 lb)*)
  intros.
  inversion H4; subst; auto.
  destruct H25 with x lb v1; auto.
  destruct H33.
  rename x0 into v2.
  exists v2; split; auto. 
  apply update_field_preserve_L_eq_tm with ct lb1 lx lb2 lx0 ; auto.

  intros.
  inversion H4; subst; auto.
  destruct H27 with x lb v2; auto.
  destruct H33.
  rename x0 into v1.
  exists v1; split; auto. 
  apply update_field_preserve_L_eq_tm with ct lb1 lx lb2 lx0 ; auto.
  
  (* (v_opa_l v1 lb)*)
  intros.
  inversion H4; subst; auto.
  destruct H28 with x lb v1; auto.
  destruct H33.
  rename x0 into v2.
  exists v2; split; auto. 
  apply update_field_preserve_L_eq_tm with ct lb1 lx lb2 lx0 ; auto.

  intros.
  inversion H4; subst; auto.
  destruct H31 with x lb v2; auto.
  destruct H33.
  rename x0 into v1.
  exists v1; split; auto. 
  apply update_field_preserve_L_eq_tm with ct lb1 lx lb2 lx0 ; auto.

  inversion H4; subst; auto. 
Qed. 
Hint Resolve update_field_preserve_L_eq_store.




Lemma update_field_preserve_L_eq_ctn {DecOid : forall a1 a2 : oid, Decision (a1 = a2)} :
  forall  (φ:bijection oid oid) h1 h2 ct cls F lo o lb1 lx
          cls0 F0 lo0 o0 lb2 lx0 ctn1 ctn2 v v0 f0,
  wfe_heap ct h2 ->  wfe_heap ct h1 -> 
  L_equivalence_heap h1 h2 φ ->
  L_eq_container ctn1 h1 ctn2 h2 φ ->
  Some (Heap_OBJ cls F lo) = lookup_heap_obj h1 o ->
  flow_to lo (join_label lb1 lx) = true ->
  Some (Heap_OBJ cls0 F0 lo0) = lookup_heap_obj h2 o0 ->
  flow_to lo0 (join_label lb2 lx0) = true ->
  L_equivalence_tm (ObjId o) h1 (ObjId o0) h2 φ ->
  L_equivalence_tm (v_opa_l v lx) h1 (v_opa_l v0 lx0) h2 φ ->
  flow_to lb1 L_Label = true ->
  flow_to lb2 L_Label = true ->
  value v ->
  value v0 ->
  valid_ctn ct ctn1 h1 ->   valid_ctn ct ctn2 h2 ->
  L_eq_container ctn1 (update_heap_obj h1 o (Heap_OBJ cls (fields_update F f0 v) lo))
                    ctn2 (update_heap_obj h2 o0 (Heap_OBJ cls0 (fields_update F0 f0 v0) lo0)) φ.
Proof with eauto.
  intros.
  inversion H2; subst; auto.
  apply L_eq_ctn; auto.
  auto. 
  apply update_field_preserve_L_eq_tm with ct lb1 lx lb2 lx0; auto.
  apply update_field_preserve_L_eq_fs with ct lb1 lx lb2 lx0; auto.
  apply update_field_preserve_L_eq_store with ct lb1 lx lb2 lx0; auto.
  inversion H13; auto. inversion H14; auto. 
Qed. Hint Resolve update_field_preserve_L_eq_ctn.
  
Lemma update_field_preserve_L_eq_ctns {DecOid : forall a1 a2 : oid, Decision (a1 = a2)} :
  forall  (φ:bijection oid oid) h1 h2 ct cls F lo o lb1 lx
          cls0 F0 lo0 o0 lb2 lx0 ctns1 ctns2 v v0 f0,
  wfe_heap ct h2 ->  wfe_heap ct h1 -> 
  L_equivalence_heap h1 h2 φ ->
  L_eq_ctns ctns1 h1 ctns2 h2 φ ->
  Some (Heap_OBJ cls F lo) = lookup_heap_obj h1 o ->
  flow_to lo (join_label lb1 lx) = true ->
  Some (Heap_OBJ cls0 F0 lo0) = lookup_heap_obj h2 o0 ->
  flow_to lo0 (join_label lb2 lx0) = true ->
  L_equivalence_tm (ObjId o) h1 (ObjId o0) h2 φ ->
  L_equivalence_tm (v_opa_l v lx) h1 (v_opa_l v0 lx0) h2 φ ->
  flow_to lb1 L_Label = true ->
  flow_to lb2 L_Label = true ->
  value v ->
  value v0 ->
  valid_ctns ct ctns1 h1 ->   valid_ctns ct ctns2 h2 ->
  L_eq_ctns ctns1 (update_heap_obj h1 o (Heap_OBJ cls (fields_update F f0 v) lo))
                    ctns2 (update_heap_obj h2 o0 (Heap_OBJ cls0 (fields_update F0 f0 v0) lo0)) φ.
Proof with eauto.
  intros.
  generalize dependent ctns2.
  induction ctns1; intros; inversion H2; subst; auto.  
  apply L_eq_ctns_list; auto.  
  apply update_field_preserve_L_eq_ctn with ct lb1 lx lb2 lx0; auto.
  inversion H13; auto. 
  inversion H14; auto. 
  apply   IHctns1; auto. 
  inversion H13; auto. 
  inversion H14; auto. 
  
Qed. Hint Resolve update_field_preserve_L_eq_ctns.

(*
Lemma value_L_eq_ : forall e v h1 h2 T1 T2 ct  φ gamma1 gamma2, 
  tm_has_type ct gamma1 h1 e T1 -> 
  tm_has_type ct gamma2 h2 v T2 -> 
  value v ->
  L_equivalence_tm e h1 v h2  φ ->
  value e.
Proof. intros. generalize dependent e. generalize dependent T1. generalize dependent T2.   induction v; subst; inversion H1; auto;
intros;  inversion H2; subst; auto.  inversion H3; subst. auto. 
inversion H3; subst; auto.  inversion H5; subst; auto. inversion H4. subst;auto. 
inversion H4. subst;auto.  inversion H5; subst; auto. inversion H4. subst;auto. 
inversion H4. subst;auto.
Qed. 
Hint Resolve value_L_eq_.

Lemma value_L_eq2_ : forall e v h1 h2 T1 T2 ct  φ gamma2 gamma1, 
  tm_has_type ct gamma2 h2 e T2 -> 
  tm_has_type ct gamma1 h1 v T1 -> 
  value v ->
  L_equivalence_tm v h1 e h2  φ ->
  value e.
Proof. intros. generalize dependent e. generalize dependent T1. generalize dependent T2.   induction v; subst; inversion H1; auto;
intros;  inversion H2; subst; auto.  inversion H3; subst. auto. 
inversion H3; subst; auto.  inversion H5; subst; auto. inversion H4. subst;auto. 
inversion H4. subst;auto.  inversion H5; subst; auto. inversion H4. subst;auto. 
inversion H4. subst;auto.
Qed. 
Hint Resolve value_L_eq2.
*)

Lemma config_typing_lead_to_tm_typing : forall h ct t fs lb sf ctns T, 
    config_has_type ct empty_context (Config ct (Container t fs lb sf) ctns h) T ->
    exists T' gamma , tm_has_type ct gamma  h t T'.
Proof with eauto.
  intros.
  inversion H; subst;  auto. inversion H6; subst; auto; exists T0; exists empty_context;  auto.

  inversion H6; subst; auto.
  exists T1. exists Gamma'. auto. 
  exists T1. exists Gamma'. auto.
  inversion H16; subst; auto.
  remember (update_typing empty_context arg_id (classTy arguT)) as gamma. 
  exists T1. exists gamma. auto. 
  remember (update_typing empty_context arg_id (classTy arguT)) as gamma. 
  exists T1. exists gamma. auto.   
Qed.
Hint Resolve config_typing_lead_to_tm_typing.

(*

Inductive eq_φ : (bijection.bijection oid oid) -> heap -> Prop :=
| same_mapping : forall h φ, 
    (forall o  cls F lb,
    lookup_heap_obj h o = Some (Heap_OBJ cls F lb) ->
    flow_to lb L_Label = true ->
    bijection.left φ o = Some o) ->
    eq_φ φ h.                             
Hint Constructors eq_φ.                       

Lemma same_tm_L_eq : forall ct t h gamma  φ,
    eq_φ φ h -> 
    forall T, tm_has_type ct gamma h  t T ->
    L_equivalence_tm t h t h φ.
Proof with eauto.
  intros.
  generalize dependent T. 
  induction t; subst; auto; intros; inversion H0; subst; auto;
  try ( apply IHt in H5; auto).
  try ( apply IHt in H3; auto).
  apply IHt1 in H4. 
  apply IHt2 in H5. auto. 
  apply IHt in H9. auto. 
  apply IHt in H7. auto.
  apply IHt1 in H4. 
  apply IHt2 in H8. auto. 
  apply IHt1 in H7.
  apply IHt2 in H9.
  apply IHt3 in H10. auto. 
  apply IHt1 in H6. apply IHt2 in H8. auto.
  destruct H7 as [F]. destruct H1 as [lo].
  case_eq (flow_to lo L_Label); intro.
  apply L_equivalence_tm_eq_object_L with cls_def F lo cls_def F
lo; auto. 
  inversion H; subst; auto.
  apply H5 with cls_def F lo; auto.
  apply L_equivalence_tm_eq_object_H with cls_def F lo cls_def F
                                          lo; auto.
  apply IHt in H7; auto. case_eq (flow_to l L_Label); intro; auto.   
  apply IHt in H7; auto. case_eq (flow_to l L_Label); intro; auto. 
Qed. Hint Resolve  same_tm_L_eq.   

Lemma same_fs_L_eq : forall ct h gamma fs φ,
    eq_φ φ h -> 
    forall T, fs_has_type ct gamma h fs T ->
    L_equivalence_fs fs h fs h φ.
Proof with eauto.
  induction fs; intros. auto.
  apply  L_equal_fs; auto.
  inversion H0; subst;  auto; 
    try (apply same_tm_L_eq with ct gamma T0; auto).
  (apply same_tm_L_eq with ct gamma (OpaqueLabeledTy (classTy returnT)); auto).
  inversion H3; subst; auto.
  remember ( (update_typing empty_context arg_id0 (classTy arguT0))) as Gamma'.
  apply T_MethodCall with Gamma' T cls_def0 body0 arg_id0 arguT0; auto.

  (apply same_tm_L_eq with ct gamma (OpaqueLabeledTy (classTy returnT)); auto).
  inversion H3; subst; auto.
  remember ( (update_typing empty_context arg_id0 (classTy arguT0))) as Gamma'.
  apply T_MethodCall with Gamma' T cls_def0 body0 arg_id0 arguT0; auto. 

  (apply same_tm_L_eq with ct gamma voidTy; auto).
  (apply same_tm_L_eq with ct gamma voidTy; auto).
  inversion H0; subst; auto;  try (apply   IHfs with (ArrowTy T0 T'); auto; fail);
    try (apply   IHfs with (ArrowTy T1 T'); auto; fail).
  apply IHfs with (ArrowTy  (classTy cls') T'); auto.
  apply IHfs with  (ArrowTy (OpaqueLabeledTy (classTy returnT)) T'); auto.
  apply IHfs with (ArrowTy (OpaqueLabeledTy (classTy returnT)) T'); auto.
  apply IHfs with (ArrowTy (LabelelTy T0) T'); auto.
  apply IHfs with (ArrowTy LabelTy T'); auto.
  apply IHfs with (ArrowTy voidTy T'); auto.
  apply IHfs with (ArrowTy voidTy T'); auto.
  apply IHfs with (ArrowTy voidTy T'); auto.
Qed. Hint Resolve same_fs_L_eq. 


Lemma same_val_L_eq : forall ct h v φ,
    eq_φ φ h ->
    wfe_stack_val ct h v ->
    L_equivalence_tm v h v h φ.
Proof with eauto.
  intros. induction H0; auto.
  remember (class_def cls_name field_defs method_defs) as cls. 
  case_eq (flow_to lo L_Label); intro. 
  apply L_equivalence_tm_eq_object_L with cls F lo cls F lo; auto.
  inversion H; subst; auto.
  remember (class_def cls_name field_defs method_defs) as cls.
  apply H3 with cls F lo; auto. 
  apply L_equivalence_tm_eq_object_H with cls F lo cls F lo; auto.

  case_eq (flow_to lb L_Label); intro.
  apply L_equivalence_tm_eq_v_l_L; auto.
  apply L_equivalence_tm_eq_v_l_H; auto.  

  case_eq (flow_to lb L_Label); intro.
  apply L_equivalence_tm_eq_v_opa_l_L; auto.
  apply L_equivalence_tm_eq_v_opa_l_H; auto.    
Qed. Hint Resolve  same_val_L_eq.

  
Lemma same_store_L_eq : forall ct h sf φ,
    eq_φ φ h ->
    wfe_stack_frame ct h sf ->
    L_equivalence_store sf h sf h φ.
Proof with eauto.
  intros.
  inversion H0; subst; auto. 
  apply  L_equivalence_store_L.

  intros. exists o1; split; auto.
  apply same_val_L_eq with ct; auto.
  apply H1 with x; auto. 

  intros. exists o2; split; auto.
  apply same_val_L_eq with ct; auto.
  apply H1 with x; auto. 

  intros. exists v1; split; auto.
  apply same_val_L_eq with ct; auto.
  assert ( wfe_stack_val ct h (v_l v1 lb)).
  apply H1 with x; auto.
  inversion H4; subst; auto. 

  intros. exists v2; split; auto.
  apply same_val_L_eq with ct; auto.
  assert ( wfe_stack_val ct h (v_l v2 lb)).
  apply H1 with x; auto.
  inversion H4; subst; auto. 

  intros. exists v1; split; auto.
  apply same_val_L_eq with ct; auto.
  assert ( wfe_stack_val ct h (v_opa_l v1 lb)).
  apply H1 with x; auto.
  inversion H4; subst; auto. 

  intros. exists v2; split; auto.
  apply same_val_L_eq with ct; auto.
  assert ( wfe_stack_val ct h (v_opa_l v2 lb)).
  apply H1 with x; auto.
  inversion H4; subst; auto. 
Qed. Hint Resolve same_store_L_eq.

Lemma same_ctn_L_eq : forall ct h T t fs lb sf  φ gamma,
    eq_φ φ h ->
    valid_ctn ct (Container t fs lb sf) h ->
    ctn_has_type ct gamma h (Container t fs lb sf) T ->
    flow_to lb L_Label = true ->
    L_eq_container (Container t fs lb sf) h (Container t fs lb sf) h φ.
Proof with eauto.
  intros.
  apply L_eq_ctn; auto. auto.
  inversion H1; subst; auto.
  apply same_tm_L_eq with ct gamma T0; auto. 
  apply same_tm_L_eq with ct gamma T0; auto. 

  inversion H1; subst; auto.
  apply  same_fs_L_eq with ct gamma (ArrowTy T0 T'); auto. 
  apply  same_fs_L_eq with ct gamma (ArrowTy T1 T'); auto
  apply same_store_L_eq with ct; auto.
  inversion H0; auto.
Qed. Hint Resolve  same_ctn_L_eq. 
 *)


Lemma extend_h1_with_H_preserve_bijection : forall ct h1 h2 φ cls lo F,
    wfe_heap ct h1 ->
    L_equivalence_heap h1 h2 φ ->
    flow_to lo L_Label = false ->   
  L_equivalence_heap (add_heap_obj h1 (get_fresh_oid h1)
                                   (Heap_OBJ cls F lo)) h2 φ.
Proof with eauto.
  intros.
  inversion H0; subst; auto.
  apply L_eq_heap; auto.
  - intros. apply H2 in H7. inversion H7; subst; auto.
    apply object_equal_L with lb1 lb2 cls1 cls2 F1 F2; auto.

    assert (lookup_heap_obj (add_heap_obj h1 (get_fresh_oid h1)
                                   (Heap_OBJ cls F lo)) o1 = Some (Heap_OBJ cls1 F1 lb1)).
    apply extend_heap_lookup_eq; auto.
    apply lookup_extend_heap_fresh_oid with ct  (Heap_OBJ cls1 F1 lb1) ; auto.
    auto. destruct H12. destruct H13. destruct H14.
    destruct H15.
    split; auto. split; auto. split; auto. split; auto.
    intros.
    destruct H16 with fname fo1 fo2; auto.
    destruct H19 as [hof2]. rename x into hof1.
    exists hof1. exists hof2.
    destruct H19; auto.  destruct H20. 
    split; auto.
    apply extend_heap_lookup_eq; auto.
    apply lookup_extend_heap_fresh_oid with ct hof1 ; auto.
  - intros.
    apply lookup_extended_heap_none in H7; auto.
  - intros. 
    case_eq (beq_oid o (get_fresh_oid h1)); intro.
    assert (lookup_heap_obj h1 o = None).
    apply fresh_oid_heap with ct; auto.
    apply H3 in H10. auto.
    apply lookup_extend_heap_for_existing in H7; auto.
    apply H5 in H7; auto. 
Qed.  Hint Resolve   extend_h1_with_H_preserve_bijection.

Lemma extend_h2_with_H_preserve_bijection : forall ct h1 h2 φ cls lo F,
    wfe_heap ct h2 ->
    L_equivalence_heap h1 h2 φ ->
    flow_to lo L_Label = false ->   
  L_equivalence_heap h1 (add_heap_obj h2 (get_fresh_oid h2)
                                   (Heap_OBJ cls F lo)) φ.
Proof with eauto.
  intros.
  inversion H0; subst; auto.
  apply L_eq_heap; auto.
  - intros. apply H2 in H7. inversion H7; subst; auto.
    apply object_equal_L with lb1 lb2 cls1 cls2 F1 F2; auto.

    assert (lookup_heap_obj (add_heap_obj h2 (get_fresh_oid h2)
                                   (Heap_OBJ cls F lo)) o2 = Some (Heap_OBJ cls2 F2 lb2)).
    apply extend_heap_lookup_eq; auto.
    apply lookup_extend_heap_fresh_oid with ct  (Heap_OBJ cls2 F2 lb2) ; auto.
    auto.
    destruct H12.
    destruct H13. destruct H14. destruct H15. 
    split; auto. split; auto. split; auto. split; auto.
    
    intros.
    destruct H16 with fname fo1 fo2; auto.
    destruct H19 as [hof2]. rename x into hof1.
    exists hof1. exists hof2.
    destruct H19; auto.  destruct H20. 
    split; auto. split; auto. 
    apply extend_heap_lookup_eq; auto.
    apply lookup_extend_heap_fresh_oid with ct hof2 ; auto.
  - intros.
    apply lookup_extended_heap_none in H7; auto.
  - intros. 
    case_eq (beq_oid o (get_fresh_oid h2)); intro.
    assert (lookup_heap_obj h2 o = None).
    apply fresh_oid_heap with ct; auto.
    apply H4 in H10. auto.
    apply lookup_extend_heap_for_existing in H7; auto.
    apply H6 in H7; auto. 
Qed.  Hint Resolve  extend_h2_with_H_preserve_bijection.
  

Lemma extend_h1_with_H_preserve_tm_eq : forall t1 t2 ct h1 h2 φ cls lo F,
     wfe_heap ct h1 ->
     flow_to lo L_Label = false ->
     L_equivalence_tm t1 h1 t2 h2 φ ->
     L_equivalence_tm t1 (add_heap_obj h1 (get_fresh_oid h1) (Heap_OBJ cls F lo)) t2 h2 φ.
Proof with eauto.
  intros.
  generalize dependent t2. 
  induction t1; intros; inversion H1; subst; auto.
  apply L_equivalence_tm_eq_object_L with cls1 F1 lb1 cls2 F2 lb2; auto.
  assert (lookup_heap_obj (add_heap_obj h1 (get_fresh_oid h1)
                                   (Heap_OBJ cls F lo)) o = Some (Heap_OBJ cls1 F1 lb1)).
  apply extend_heap_lookup_eq; auto.
  apply lookup_extend_heap_fresh_oid with ct  (Heap_OBJ cls1 F1 lb1) ; auto.
  auto.


  apply L_equivalence_tm_eq_object_H with cls1 cls2 F1 lb1  F2 lb2; auto.
  assert (lookup_heap_obj (add_heap_obj h1 (get_fresh_oid h1)
                                   (Heap_OBJ cls F lo)) o = Some (Heap_OBJ cls1 F1 lb1)).
  apply extend_heap_lookup_eq; auto.
  apply lookup_extend_heap_fresh_oid with ct  (Heap_OBJ cls1 F1 lb1) ; auto.
  auto.
Qed. Hint Resolve extend_h1_with_H_preserve_tm_eq.   


Lemma extend_h2_with_H_preserve_tm_eq : forall t1 t2 ct h1 h2 φ cls lo F,
     wfe_heap ct h2 ->
     flow_to lo L_Label = false ->
     L_equivalence_tm t1 h1 t2 h2 φ ->
     L_equivalence_tm t1 h1  t2 (add_heap_obj h2 (get_fresh_oid h2) (Heap_OBJ cls F lo)) φ.
Proof with eauto.
  intros.
  generalize dependent t2. 
  induction t1; intros; inversion H1; subst; auto.
  apply L_equivalence_tm_eq_object_L with cls1 F1 lb1 cls2 F2 lb2; auto.
  assert (lookup_heap_obj (add_heap_obj h2 (get_fresh_oid h2)
                                   (Heap_OBJ cls F lo)) o2 = Some (Heap_OBJ cls2 F2 lb2)).
  apply extend_heap_lookup_eq; auto.
  apply lookup_extend_heap_fresh_oid with ct  (Heap_OBJ cls2 F2 lb2) ; auto.
  auto.


  apply L_equivalence_tm_eq_object_H with cls1 cls2 F1 lb1  F2 lb2; auto.
  assert (lookup_heap_obj (add_heap_obj h2 (get_fresh_oid h2)
                                   (Heap_OBJ cls F lo)) o2 = Some (Heap_OBJ cls2 F2 lb2)).
  apply extend_heap_lookup_eq; auto.
  apply lookup_extend_heap_fresh_oid with ct  (Heap_OBJ cls2 F2 lb2) ; auto.
  auto.
Qed. Hint Resolve extend_h2_with_H_preserve_tm_eq.   


Lemma extend_h1_with_H_preserve_fs_eq : forall fs1 fs2 ct h1 h2 φ cls lo F,
     wfe_heap ct h1 ->
     flow_to lo L_Label = false ->
     L_equivalence_fs fs1 h1 fs2 h2 φ ->
     L_equivalence_fs fs1 (add_heap_obj h1 (get_fresh_oid h1) (Heap_OBJ cls F lo)) fs2 h2 φ.
Proof with eauto.
  intros.
  generalize dependent fs2. 
  induction fs1; intros; inversion H1; subst; auto.
  apply L_equal_fs; auto.
  apply  extend_h1_with_H_preserve_tm_eq with ct; auto. 
Qed. Hint Resolve extend_h1_with_H_preserve_fs_eq.

Lemma extend_h2_with_H_preserve_fs_eq : forall fs1 fs2 ct h1 h2 φ cls lo F,
     wfe_heap ct h2 ->
     flow_to lo L_Label = false ->
     L_equivalence_fs fs1 h1 fs2 h2 φ ->
     L_equivalence_fs fs1 h1 fs2 (add_heap_obj h2 (get_fresh_oid h2) (Heap_OBJ cls F lo)) φ.
Proof with eauto.
  intros.
  generalize dependent fs2. 
  induction fs1; intros; inversion H1; subst; auto.
  apply L_equal_fs; auto.
  apply  extend_h2_with_H_preserve_tm_eq with ct; auto. 
Qed. Hint Resolve extend_h2_with_H_preserve_fs_eq.


Lemma extend_h1_with_H_preserve_sf_eq : forall sf1 sf2 ct h1 h2 φ cls lo F,
    wfe_heap ct h1 ->
    wfe_heap ct h2 ->
    wfe_stack_frame ct h1 sf1 ->
    wfe_stack_frame ct h2 sf2 ->
     flow_to lo L_Label = false ->
     L_equivalence_store sf1 h1 sf2 h2 φ ->
     L_equivalence_store sf1 (add_heap_obj h1 (get_fresh_oid h1) (Heap_OBJ cls F lo)) sf2 h2 φ.
Proof with eauto.
  intros.
  inversion H1; subst; auto.
  inversion H2; subst; auto.
  apply  L_equivalence_store_L; auto.
- inversion H4; subst; auto.
  intros.
  assert (wfe_stack_val ct h1 (ObjId o1) ). apply H5 with x; auto. 
  inversion H17; subst; auto.
  destruct H7 with x o1 (class_def cls_name field_defs method_defs) F0 lo0 in H13; subst; auto. 

  assert (lookup_heap_obj (add_heap_obj h1 (get_fresh_oid h1) (Heap_OBJ cls F lo)) o1  =
          Some (Heap_OBJ (class_def cls_name field_defs method_defs) F0 lo0)).
  apply extend_heap_lookup_eq; auto.
  apply lookup_extend_heap_fresh_oid with ct (Heap_OBJ (class_def cls_name field_defs method_defs) F0 lo0); auto.
  rewrite <- H15 in H18. inversion H18; subst; auto.
  destruct H18; auto. rename x0 into o2. 
  exists o2.  auto. split; auto. 
  apply extend_h1_with_H_preserve_tm_eq with ct; auto.

 -  inversion H4; subst; auto.
  intros.
  assert (wfe_stack_val ct h2 (ObjId o2) ). apply H6 with x; auto. 
  inversion H17; subst; auto.
  destruct H8 with x o2 (class_def cls_name field_defs method_defs) F0 lo0 in H13; subst; auto. 

  assert (lookup_heap_obj (add_heap_obj h2 (get_fresh_oid h2) (Heap_OBJ cls F lo)) o2  =
          Some (Heap_OBJ (class_def cls_name field_defs method_defs) F0 lo0)).
  apply extend_heap_lookup_eq; auto.
  apply lookup_extend_heap_fresh_oid with ct (Heap_OBJ (class_def cls_name field_defs method_defs) F0 lo0); auto.
  rewrite <- H15 in H19. inversion H19; subst; auto.
  destruct H18; auto. rename x0 into o1. 
  exists o1.  auto. split; auto. 
  apply extend_h1_with_H_preserve_tm_eq with ct; auto.

 - intros. inversion H4; subst; auto.
   destruct H11 with x lb v1; auto. destruct H16. rename x0 into v2.
   exists v2; split; auto.
   apply extend_h1_with_H_preserve_tm_eq with ct; auto.

 - intros. inversion H4; subst; auto.
   destruct H12 with x lb v2; auto. destruct H16. rename x0 into v1.
   exists v1; split; auto.
   apply extend_h1_with_H_preserve_tm_eq with ct; auto.

 - intros. inversion H4; subst; auto.
   destruct H13 with x lb v1; auto. destruct H16. rename x0 into v2.
   exists v2; split; auto.
   apply extend_h1_with_H_preserve_tm_eq with ct; auto.

 - intros. inversion H4; subst; auto.
   destruct H14 with x lb v2; auto. destruct H16. rename x0 into v1.
   exists v1; split; auto.
   apply extend_h1_with_H_preserve_tm_eq with ct; auto.

 - inversion H4; auto. 
 Qed. Hint Resolve extend_h1_with_H_preserve_sf_eq.


Lemma extend_h2_with_H_preserve_sf_eq : forall sf1 sf2 ct h1 h2 φ cls lo F,
    wfe_heap ct h1 ->
    wfe_heap ct h2 ->
    wfe_stack_frame ct h1 sf1 ->
    wfe_stack_frame ct h2 sf2 ->
     flow_to lo L_Label = false ->
     L_equivalence_store sf1 h1 sf2 h2 φ ->
     L_equivalence_store sf1 h1 sf2 (add_heap_obj h2 (get_fresh_oid h2) (Heap_OBJ cls F lo)) φ.
Proof with eauto.
  intros.
  inversion H1; subst; auto.
  inversion H2; subst; auto.
  apply  L_equivalence_store_L; auto.
- inversion H4; subst; auto.
  intros.
  assert (wfe_stack_val ct h1 (ObjId o1) ). apply H5 with x; auto. 
  inversion H17; subst; auto.
  destruct H7 with x o1 cls1 F1 lb1 in H13; subst; auto.
   destruct H18; auto. rename x0 into o2. 
   exists o2.  auto. split; auto.
   apply extend_h2_with_H_preserve_tm_eq with ct; auto.

 -  inversion H4; subst; auto.
  intros.
  assert (wfe_stack_val ct h2 (ObjId o2) ). apply H6 with x; auto. 
  inversion H17; subst; auto.
  destruct H8 with x o2 (class_def cls_name field_defs method_defs) F0 lo0 in H13; subst; auto. 

  assert (lookup_heap_obj (add_heap_obj h2 (get_fresh_oid h2) (Heap_OBJ cls F lo)) o2  =
          Some (Heap_OBJ (class_def cls_name field_defs method_defs) F0 lo0)).
  apply extend_heap_lookup_eq; auto.
  apply lookup_extend_heap_fresh_oid with ct (Heap_OBJ (class_def cls_name field_defs method_defs) F0 lo0); auto.
  rewrite <- H15 in H18. inversion H18; subst; auto.
  destruct H18; auto. rename x0 into o1. 
  exists o1.  auto. split; auto. 
  apply extend_h2_with_H_preserve_tm_eq with ct; auto.

 - intros. inversion H4; subst; auto.
   destruct H11 with x lb v1; auto. destruct H16. rename x0 into v2.
   exists v2; split; auto.
   apply extend_h2_with_H_preserve_tm_eq with ct; auto.

 - intros. inversion H4; subst; auto.
   destruct H12 with x lb v2; auto. destruct H16. rename x0 into v1.
   exists v1; split; auto.
   apply extend_h2_with_H_preserve_tm_eq with ct; auto.

 - intros. inversion H4; subst; auto.
   destruct H13 with x lb v1; auto. destruct H16. rename x0 into v2.
   exists v2; split; auto.
   apply extend_h2_with_H_preserve_tm_eq with ct; auto.

 - intros. inversion H4; subst; auto.
   destruct H14 with x lb v2; auto. destruct H16. rename x0 into v1.
   exists v1; split; auto.
   apply extend_h2_with_H_preserve_tm_eq with ct; auto.

 - inversion H4; auto. 
 Qed. Hint Resolve extend_h2_with_H_preserve_sf_eq.

Lemma extend_h1_with_H_preserve_ctn_eq : forall ct
    t1 fs1 lb1 sf1
    t2 fs2 lb2 sf2
    h1 h2 φ cls lo F,
    wfe_heap ct h1 ->
    wfe_heap ct h2 ->
    valid_ctn ct ((Container t1 fs1 lb1 sf1)) h1  ->
    valid_ctn ct ((Container t2 fs2 lb2 sf2)) h2  ->
    L_equivalence_heap h1 h2 φ ->
    L_eq_container (Container t1 fs1 lb1 sf1) h1
                   (Container t2 fs2 lb2 sf2) h2 φ ->
    flow_to lo L_Label = false  ->
    L_eq_container (Container t1 fs1 lb1 sf1)
    (add_heap_obj h1 (get_fresh_oid h1) (Heap_OBJ cls F lo))  
    (Container t2 fs2 lb2 sf2) h2 φ.
Proof with eauto.
  intros.
  inversion H1; subst; auto.
  inversion H2; subst; auto.
  inversion H4; subst; auto. 
  apply L_eq_ctn; auto.
  apply extend_h1_with_H_preserve_tm_eq with ct; auto.
  apply extend_h1_with_H_preserve_fs_eq with ct; auto.
  apply extend_h1_with_H_preserve_sf_eq with ct; auto.
Qed. Hint Resolve   extend_h1_with_H_preserve_ctn_eq.

Lemma extend_h2_with_H_preserve_ctn_eq : forall ct
    t1 fs1 lb1 sf1
    t2 fs2 lb2 sf2
    h1 h2 φ cls lo F,
    wfe_heap ct h1 ->
    wfe_heap ct h2 ->
    valid_ctn ct ((Container t1 fs1 lb1 sf1)) h1  ->
    valid_ctn ct ((Container t2 fs2 lb2 sf2)) h2  ->
    L_equivalence_heap h1 h2 φ ->
    L_eq_container (Container t1 fs1 lb1 sf1) h1
                   (Container t2 fs2 lb2 sf2) h2 φ ->
    flow_to lo L_Label = false  ->
    L_eq_container (Container t1 fs1 lb1 sf1)
                   h1
                   (Container t2 fs2 lb2 sf2)
                   (add_heap_obj h2 (get_fresh_oid h2) (Heap_OBJ cls F lo))   φ.
Proof with eauto.
  intros.
  inversion H1; subst; auto.
  inversion H2; subst; auto.
  inversion H4; subst; auto. 
  apply L_eq_ctn; auto.
  apply extend_h2_with_H_preserve_tm_eq with ct; auto.
  apply extend_h2_with_H_preserve_fs_eq with ct; auto.
  apply extend_h2_with_H_preserve_sf_eq with ct; auto.
Qed. Hint Resolve   extend_h2_with_H_preserve_ctn_eq.

Lemma extend_h1_with_H_preserve_ctns_eq : forall ct ctns1 ctns2
    h1 h2 φ cls lo F,
    valid_ctns ct ctns1 h1 ->   valid_ctns ct ctns2 h2 ->
    wfe_heap ct h1 -> wfe_heap ct h2 ->
     L_equivalence_heap h1 h2 φ ->
    L_eq_ctns  ctns1  h1 ctns2 h2 φ ->
    flow_to lo L_Label = false  ->
    L_eq_ctns  ctns1 (add_heap_obj h1 (get_fresh_oid h1) (Heap_OBJ cls F lo))
     ctns2  h2  φ.
Proof with eauto.
  intros.
  generalize dependent ctns2.
  induction ctns1; subst; auto.
  intros. inversion H4; subst; auto. 
  intros. inversion H4; subst; auto. 
  apply L_eq_ctns_list; auto. 

  inversion H; subst; auto.
  inversion H0; subst; auto. 
  destruct a. destruct ctn2. 
  apply extend_h1_with_H_preserve_ctn_eq with ct; auto.
  apply   IHctns1; auto.   
  inversion H; subst; auto.
  inversion H0; subst; auto. 
Qed.  Hint Resolve  extend_h1_with_H_preserve_ctns_eq.

Lemma extend_h2_with_H_preserve_ctns_eq : forall ct ctns1 ctns2
    h1 h2 φ cls lo F,
    valid_ctns ct ctns1 h1 ->   valid_ctns ct ctns2 h2 ->
    wfe_heap ct h1 -> wfe_heap ct h2 ->
     L_equivalence_heap h1 h2 φ ->
    L_eq_ctns  ctns1  h1 ctns2 h2 φ ->
    flow_to lo L_Label = false  ->
    L_eq_ctns  ctns1 h1
     ctns2  (add_heap_obj h2 (get_fresh_oid h2) (Heap_OBJ cls F lo))  φ.
Proof with eauto.
  intros.
  generalize dependent ctns2.
  induction ctns1; subst; auto.
  intros. inversion H4; subst; auto. 
  intros. inversion H4; subst; auto. 
  apply L_eq_ctns_list; auto. 

  inversion H; subst; auto.
  inversion H0; subst; auto. 
  destruct a. destruct ctn2. 
  apply extend_h2_with_H_preserve_ctn_eq with ct; auto.
  apply   IHctns1; auto.   
  inversion H; subst; auto.
  inversion H0; subst; auto. 
Qed.  Hint Resolve  extend_h2_with_H_preserve_ctns_eq.

Lemma low_component_transitive : forall ct t1 fs1 lb1 sf1 t2 fs2 lb2 sf2 h ctns,
    flow_to lb1 L_Label = false ->
    flow_to lb2 L_Label = false ->
    low_component ct (Container t1 fs1 lb1 sf1) ctns h =
    low_component ct (Container t2 fs2 lb2 sf2) ctns h.
Proof with eauto.
  intros.
  unfold low_component.  destruct ctns; rewrite H; rewrite H0; auto.  
Qed. Hint Resolve low_component_transitive .

  
Lemma low_component_lead_to_L : forall ct1 t fs lb sf  h1 ct2 ctn2 ctns1 ctns2 h2,  
    Config ct1 (Container t fs lb sf) ctns1 h1 = low_component ct2 ctn2 ctns2 h2 ->
    ct1 = ct2 /\ h1 = h2 /\ flow_to lb L_Label = true.
Proof with eauto.
  intros.
  destruct ctn2.
  case_eq (flow_to l L_Label); intro.
  unfold low_component in H.

  + induction ctns2.
    rewrite H0 in H.
    inversion H; subst; auto.

    rewrite H0 in H.
    inversion H; subst;auto. 

  + induction ctns2.
    unfold low_component in H.
    rewrite H0 in H.
    inversion H; subst; auto.

    unfold low_component in H.
    rewrite H0 in H.
    fold low_component in H.
     destruct a.
    case_eq (flow_to l0 L_Label); intro.
    unfold low_component in H.
    destruct ctns2. 
    rewrite H1 in H.
    inversion H; subst;auto.
    rewrite H1 in H.
    inversion H; subst;auto.

    assert (low_component ct2 (Container t1 f0 l0 s0) ctns2 h2 =
            low_component ct2 (Container t0 f l s) ctns2 h2).
    apply low_component_transitive; auto.
    rewrite H2 in H. auto. 
Qed. Hint Resolve     low_component_lead_to_L.


Lemma low_component_irrelevant_to_heap :  forall ct1 t fs lb sf  h1 ct2 ctn2 ctns1 ctns2 h2 ,  
    Config ct1 (Container t fs lb sf) ctns1 h1 = low_component ct2 ctn2 ctns2 h1 ->
    Config ct1 (Container t fs lb sf) ctns1 h2 = low_component ct2 ctn2 ctns2 h2.
Proof with eauto.
  intros.
  
  generalize dependent ctn2.   induction ctns2; intros. 
  - unfold low_component in H.
    destruct ctn2. 
    case_eq (flow_to l L_Label); intro.
    rewrite H0 in H. inversion H;subst; auto.
    unfold low_component. rewrite H0. inversion H; subst; auto.

    rewrite H0 in H.  inversion H; subst; auto.
    unfold low_component. rewrite H0. auto. 
  - unfold low_component in H.
    destruct ctn2. 
    case_eq (flow_to l L_Label); intro.
    rewrite H0 in H. inversion H; subst; auto.
    unfold low_component. rewrite H0. inversion H; subst; auto.

    rewrite H0 in H. fold low_component in H.
    destruct a.
    case_eq (flow_to l0 L_Label); intro.
    unfold low_component. rewrite H0. fold low_component. auto.
    unfold low_component. rewrite H0. fold low_component. auto.
Qed. Hint Resolve low_component_irrelevant_to_heap.

                                              
    

Lemma valid_preservation_low_component : forall ct ctn ctns h
                                                ctn' ctns' h', 
    Config ct ctn' ctns' h' =
    low_component ct ctn ctns h ->
    valid_ctn ct ctn h ->
    valid_ctns ct ctns h ->
    valid_ctn ct ctn' h' /\ valid_ctns ct ctns' h'.
Proof with eauto.
  intros.
  generalize dependent ctn.   induction ctns; intros.
  destruct ctn.
  case_eq (flow_to l L_Label); intro.
  unfold low_component in H.
  rewrite H2 in H. inversion H; subst; auto.
  split; auto.
  unfold low_component in H.
  rewrite H2 in H. inversion H; subst; auto.
  apply valid_container; auto.
  intro. intro contra; inversion contra.
  intro. intro contra; inversion contra.
  apply stack_frame_wfe; auto; intros; inversion H3.
  

 
  unfold low_component in H.
  rewrite H2 in H. inversion H; subst; auto.

  destruct ctn.
  case_eq (flow_to l L_Label); intro.
  
  unfold low_component in H.
  rewrite H2 in H. inversion H; subst; auto.

  unfold low_component in H.
  rewrite H2 in H. fold low_component in H.

  apply IHctns with a; auto .
  inversion H1; auto.
  inversion H1; auto. 
Qed. Hint Resolve   valid_preservation_low_component.
  

Lemma extend_h1_with_H_preserve_config_eq : forall ct ctns1 ctns2
    ctn1 ctn2
    h1 h2 φ cls lo F,
    valid_config (Config ct ctn1 ctns1  h1)  ->
    valid_config (Config ct ctn2 ctns2  h2)  ->
    L_equivalence_heap h1 h2 φ ->
    L_equivalence_config (Config ct ctn1 ctns1  h1)
                   (Config ct ctn2 ctns2  h2) φ ->
    flow_to lo L_Label = false  ->
    L_equivalence_config
    (Config ct ctn1 ctns1 (add_heap_obj h1 (get_fresh_oid h1) (Heap_OBJ cls F lo)))
    (Config ct ctn2 ctns2  h2) φ.
Proof with eauto.
  intros.
  
  remember (Config ct ctn1 ctns1 h1) as config1.
  remember (Config ct ctn2 ctns2 h2) as config2.
  generalize dependent ctn1. generalize dependent ctn2.
  generalize dependent ctns1. generalize dependent ctns2. 
  induction H2; subst; intros; inversion Heqconfig1; inversion Heqconfig2; subst; auto.
  apply L_equivalence_config_L; auto.
  inversion H; auto. inversion H0; auto. 
  apply extend_h1_with_H_preserve_ctn_eq with ct; auto.
  inversion H; auto. inversion H0; auto. 
  apply extend_h1_with_H_preserve_ctns_eq with ct; auto.
  
  induction ctns3. induction ctns0.
  apply L_equivalence_config_H; auto.
  unfold low_component.  
  rewrite H2; rewrite H4.
  apply L_equivalence_config_L; auto.

  inversion H. inversion H0. subst; auto. 
  apply extend_h1_with_H_preserve_ctn_eq with ct ;  auto.
  apply valid_container; auto. intros.
  intro contra. inversion contra.
  intro. intro contra; inversion contra.
  apply stack_frame_wfe; auto.
  intros.      inversion H6.
  apply valid_container; auto.
  intro. intro contra; inversion contra.
  intro. intro contra; inversion contra.
  apply stack_frame_wfe; auto.
  intros.      inversion H6.

  +  apply L_eq_ctn; auto.
     apply L_equivalence_store_L; auto; intros; try (inversion H6).
     split; auto.
     
  +  apply L_equivalence_config_H; auto.
     remember (low_component ct (Container t2 fs2 lb2 sf2) (a :: ctns0) h2)
       as conf.
     destruct conf. destruct c0.
     assert (c = ct /\ h = h2 /\ flow_to l0 L_Label = true ).
     apply low_component_lead_to_L with t f s (Container t2 fs2 lb2 sf2)
                                       l (a :: ctns0); auto.
     destruct H6.  destruct H7; subst; auto.
     assert (valid_ctn ct (Container t f l0 s)  h2 /\ valid_ctns ct l h2).
     apply valid_preservation_low_component with (Container t2 fs2 lb2 sf2)
                                                 (a :: ctns0)
                                                 h2  ; auto.
     inversion H0; auto. inversion H0; auto. 
     unfold low_component.  rewrite H2. 
     unfold low_component in H5. rewrite H2 in H5.
     inversion H5; subst; auto.
     apply L_equivalence_config_L; auto.    
     apply extend_h1_with_H_preserve_ctn_eq with ct; auto.
     inversion H; auto. inversion H0; auto.
     apply valid_container; auto.
     intro. intro contra; inversion contra.
     intro. intro contra; inversion contra.
     apply stack_frame_wfe; auto; intros; inversion H7.

     apply H6.
     apply extend_h1_with_H_preserve_ctns_eq with ct; auto.
     apply H6.
     inversion H; auto.  inversion H0; auto.
     try (inconsist_label).
     inversion H5. inversion H5.     
  + apply L_equivalence_config_H; auto.
  remember (low_component ct (Container t1 fs1 lb1 sf1) (a :: ctns3) h1) as conf1.
  remember ((low_component ct (Container t2 fs2 lb2 sf2) ctns0 h2)) as conf2.
  destruct conf1. destruct conf2.
  destruct c0. 
  assert (c = ct /\ h = h1 /\ flow_to l1 L_Label = true).
  apply low_component_lead_to_L with t f s (Container t1 fs1 lb1 sf1) l (a :: ctns3)  ; auto. 

  destruct c2. 
  assert (c1 = ct /\ h0 = h2 /\ flow_to l2 L_Label = true).
  apply low_component_lead_to_L with t0 f0 s0 (Container t2 fs2 lb2 sf2) l0 ctns0  ; auto.
  destruct H6. destruct H8.
  destruct H7. destruct H10.     subst. auto.
  inversion H; subst; auto. inversion H0; subst; auto. 
  assert (valid_ctn ct (Container t f l1 s)  h1 /\ valid_ctns ct l h1).
  apply valid_preservation_low_component with (Container t1 fs1 lb1 sf1)
                                                 (a :: ctns3)
                                                 h1  ; auto.
  assert (valid_ctn ct (Container t0 f0 l2 s0)  h2 /\ valid_ctns ct l0 h2).
  apply valid_preservation_low_component with (Container t2 fs2 lb2 sf2)
                                                 ctns0
                                                 h2  ; auto.
  
  assert (Config ct (Container t f l1 s) l (add_heap_obj h1 (get_fresh_oid h1) (Heap_OBJ cls F lo))
          = (low_component ct (Container t1 fs1 lb1 sf1) (a :: ctns3)
                          (add_heap_obj h1 (get_fresh_oid h1) (Heap_OBJ cls F lo)))
         ).
  eauto using low_component_irrelevant_to_heap. rewrite <- H8.  
  apply   L_equivalence_config_L; auto.
  apply extend_h1_with_H_preserve_ctn_eq with ct; auto.
  inversion H; auto. inversion H0; auto.
  apply H6.
  apply H7.
  inversion H5; subst; auto.
  rewrite H9 in H38; inversion H38.
  inversion H5; subst; auto.
  apply extend_h1_with_H_preserve_ctns_eq with ct; auto.
  apply H6. apply H7.

  try (inconsist_label).
  inversion H5.  inversion H5.

  inversion H5.
  inversion H5.  
Qed. Hint Resolve  extend_h1_with_H_preserve_config_eq.


Lemma extend_h2_with_H_preserve_config_eq : forall ct ctns1 ctns2
    ctn1 ctn2
    h1 h2 φ cls lo F,
    valid_config (Config ct ctn1 ctns1  h1)  ->
    valid_config (Config ct ctn2 ctns2  h2)  ->
    L_equivalence_heap h1 h2 φ ->
    L_equivalence_config (Config ct ctn1 ctns1  h1)
                   (Config ct ctn2 ctns2  h2) φ ->
    flow_to lo L_Label = false  ->
    L_equivalence_config
    (Config ct ctn1 ctns1 h1)
    (Config ct ctn2 ctns2  (add_heap_obj h2 (get_fresh_oid h2) (Heap_OBJ cls F lo))) φ.
Proof with eauto.
  intros.
  
  remember (Config ct ctn1 ctns1 h1) as config1.
  remember (Config ct ctn2 ctns2 h2) as config2.
  generalize dependent ctn1. generalize dependent ctn2.
  generalize dependent ctns1. generalize dependent ctns2. 
  induction H2; subst; intros; inversion Heqconfig1; inversion Heqconfig2; subst; auto.
  apply L_equivalence_config_L; auto.
  inversion H; auto. inversion H0; auto. 
  apply extend_h2_with_H_preserve_ctn_eq with ct; auto.
  inversion H; auto. inversion H0; auto. 
  apply extend_h2_with_H_preserve_ctns_eq with ct; auto.
  
  induction ctns3. induction ctns0.
  apply L_equivalence_config_H; auto.
  unfold low_component.  
  rewrite H2; rewrite H4.
  apply L_equivalence_config_L; auto.

  inversion H. inversion H0. subst; auto. 
  apply extend_h2_with_H_preserve_ctn_eq with ct ;  auto.
  apply valid_container; auto. intros.
  intro contra. inversion contra.
  intro. intro contra; inversion contra.
  apply stack_frame_wfe; auto.
  intros.      inversion H6.
  apply valid_container; auto.
  intro. intro contra; inversion contra.
  intro. intro contra; inversion contra.
  apply stack_frame_wfe; auto.
  intros.      inversion H6.

  +  apply L_eq_ctn; auto.
     apply L_equivalence_store_L; auto; intros; try (inversion H6) .
     try (split; auto).
     

  +  apply L_equivalence_config_H; auto.
     remember
       ((low_component ct (Container t2 fs2 lb2 sf2) (a :: ctns0) h2)) as conf.
     destruct conf. destruct c0.
     assert (c = ct /\
             h = h2 /\
             flow_to l0 L_Label = true ).
     apply low_component_lead_to_L with t f s (Container t2 fs2 lb2 sf2)
                                       l (a :: ctns0); auto.
     destruct H6.  destruct H7; subst; auto.

     assert (Config ct (Container t f l0 s) l
                    (add_heap_obj h2 (get_fresh_oid h2) (Heap_OBJ cls F lo))
          = (low_component ct (Container t2 fs2 lb2 sf2) (a :: ctns0)
                          (add_heap_obj h2 (get_fresh_oid h2) (Heap_OBJ cls F lo)))
         ).
     apply low_component_irrelevant_to_heap with h2;auto.  rewrite <- H6.
     assert (valid_ctn ct (Container t f l0 s)
                       h2
             /\ valid_ctns ct l h2).
     apply valid_preservation_low_component with (Container t2 fs2 lb2 sf2)
                                                 (a :: ctns0)
                                                 h2  ; auto.
     inversion H0; auto.  inversion H0. auto. 

     inversion H5; subst; auto. 
     unfold low_component.  rewrite H2. 
     unfold low_component in H5. rewrite H2 in H5.
     apply L_equivalence_config_L; auto.    
     apply extend_h2_with_H_preserve_ctn_eq with ct; auto.
     inversion H; auto. inversion H0; auto.
      apply valid_container; auto.
     intro. intro contra; inversion contra.
     intro. intro contra; inversion contra.
     apply stack_frame_wfe; auto; intros; inversion H10.
     apply H7.
     rewrite H2 in H9. inversion H9; subst; auto.  
     apply extend_h2_with_H_preserve_ctns_eq with ct; auto.     
     apply H7.
     inversion H; auto. inversion H0; auto.
     rewrite H2 in H9. inversion H9; subst; auto.
     try (inconsist_label).

     inversion H5. inversion H5. 
     
  + apply L_equivalence_config_H; auto.
  remember (low_component ct (Container t1 fs1 lb1 sf1) (a :: ctns3) h1) as conf1.
  remember ((low_component ct (Container t2 fs2 lb2 sf2) ctns0 h2)) as conf2.
  destruct conf1. destruct conf2.
  destruct c0. 
  assert (c = ct /\ h = h1 /\ flow_to l1 L_Label = true).
  apply low_component_lead_to_L with t f s (Container t1 fs1 lb1 sf1) l (a :: ctns3)  ; auto. 

  destruct c2. 
  assert (c1 = ct /\ h0 = h2 /\ flow_to l2 L_Label = true).
  apply low_component_lead_to_L with t0 f0 s0 (Container t2 fs2 lb2 sf2) l0 ctns0  ; auto.
  destruct H6. destruct H8.
  destruct H7. destruct H10.     subst. auto.
  inversion H; subst; auto. inversion H0; subst; auto. 
  assert (valid_ctn ct (Container t f l1 s)  h1 /\ valid_ctns ct l h1).
  apply valid_preservation_low_component with (Container t1 fs1 lb1 sf1)
                                                 (a :: ctns3)
                                                 h1  ; auto.
  assert (valid_ctn ct (Container t0 f0 l2 s0)  h2 /\ valid_ctns ct l0 h2).
  apply valid_preservation_low_component with (Container t2 fs2 lb2 sf2)
                                                 ctns0
                                                 h2  ; auto.
  
  assert (Config ct (Container t0 f0 l2 s0) l0
                 (add_heap_obj h2 (get_fresh_oid h2) (Heap_OBJ cls F lo))
          = (low_component ct (Container t2 fs2 lb2 sf2) ctns0
                          (add_heap_obj h2 (get_fresh_oid h2) (Heap_OBJ cls F lo)))
         ).
  eauto using low_component_irrelevant_to_heap. rewrite <- H8.  
  apply   L_equivalence_config_L; auto.
  apply extend_h2_with_H_preserve_ctn_eq with ct; auto.
  inversion H; auto. inversion H0; auto.
  apply H6.
  apply H7.
  inversion H5; subst; auto.
  rewrite H9 in H38; inversion H38.
  inversion H5; subst; auto.
  apply extend_h2_with_H_preserve_ctns_eq with ct; auto.
  apply H6. apply H7.

  try (inconsist_label).
  inversion H5.  inversion H5.

  inversion H5.
  inversion H5.  
Qed. Hint Resolve  extend_h2_with_H_preserve_config_eq.



Lemma update_h1_with_H_preserve_bijection : forall ct h1 h2 φ cls lo F f v o lb1
  lx,
    wfe_heap ct h1 ->
    L_equivalence_heap h1 h2 φ ->
    Some (Heap_OBJ cls F lo) = lookup_heap_obj h1 o ->
    flow_to lo (join_label lb1 lx) = true ->
    flow_to lb1 L_Label = false ->
    L_equivalence_heap
    (update_heap_obj h1 o (Heap_OBJ cls (fields_update F f v) lo)) h2 φ.
    
Proof with eauto.
  intros. 
  assert ( flow_to (join_label lb1 lx) L_Label = false).
  apply flow_join_label with lb1 lx; auto.
  apply  join_label_commutative; auto.
  
  inversion H0; subst; auto.
  apply L_eq_heap; auto.
  - intros. apply H5 in H10. inversion H10; subst; auto.
    case_eq (beq_oid o1 o); intro. apply beq_oid_equal in H16.
    rewrite H16 in H11. rewrite <- H11 in H1. inversion H1; subst.
    assert (flow_to lb0 (join_label lb1 lx) = false).
    apply  flow_no_H_to_L; auto. 
    try (inconsist_label).    
    apply object_equal_L with lb0 lb2 cls1 cls2 F1 F2; auto.    
    assert ( Some (Heap_OBJ cls1 F1 lb0)
      = lookup_heap_obj
          (update_heap_obj h1 o (Heap_OBJ cls (fields_update F f v) lo)) o1).
    apply lookup_updated_not_affected with o (Heap_OBJ cls (fields_update F f v) lo) h1; auto.
    intro contra. rewrite contra in H16.
    assert (beq_oid o o = true).
    apply beq_oid_same. rewrite H16 in H17; inversion H17.

    auto. destruct H15.
    destruct H17. destruct H18. destruct H19.
   
    split; auto.
    split; auto. split; auto. split;auto. 

    intros. 
    destruct H20 with fname fo1 fo2; auto.
    destruct H23 as [hof2]. rename x into hof1.
    exists hof1. exists hof2.
    destruct H23; auto.  destruct H24. 
    split; auto.
    assert ( Some  hof1
      = lookup_heap_obj
          (update_heap_obj h1 o (Heap_OBJ cls (fields_update F f v) lo)) fo1).
    apply lookup_updated_not_affected with o (Heap_OBJ cls (fields_update F f v) lo) h1; auto.
    intro contra. apply H5 in H25. inversion H25. subst; auto.
    rewrite <- H1 in H26. inversion H26. subst; auto. 

    assert (flow_to lo L_Label  = false).
    apply  flow_transitive with (join_label lb1 lx); auto.
    try (inconsist_label). auto. 
  - intros.
    apply lookup_updated_heap_must_none in H10.
    auto. 
  - intros.
    case_eq (beq_oid o0 o); intro.
    apply beq_oid_equal in H12.
    rewrite <- H12 in H1. apply H8 with cls F lo; auto.
    apply flow_transitive with (join_label lb1 lx); auto.

    assert (Some (Heap_OBJ cls0 F0 lb) = lookup_heap_obj h1 o0).
    apply lookup_updated_not_affected_reverse
      with o (Heap_OBJ cls (fields_update F f v) lo)
           (update_heap_obj h1 o (Heap_OBJ cls (fields_update F f v) lo)); auto.
    intro contra. rewrite contra in H12.
    assert (beq_oid o o = true). apply beq_oid_same.
    rewrite H12 in H13. inversion H13.
    apply H8 with cls0 F0 lb; auto. 
Qed. Hint Resolve  update_h1_with_H_preserve_bijection.   


Lemma update_h2_with_H_preserve_bijection : forall ct h1 h2 φ cls lo F f v o lb1
  lx,
    wfe_heap ct h1 ->
    L_equivalence_heap h1 h2 φ ->
    Some (Heap_OBJ cls F lo) = lookup_heap_obj h2 o ->
    flow_to lo (join_label lb1 lx) = true ->
    flow_to lb1 L_Label = false ->
    L_equivalence_heap h1
    (update_heap_obj h2 o (Heap_OBJ cls (fields_update F f v) lo)) φ.
    
Proof with eauto.
  intros. 
  assert ( flow_to (join_label lb1 lx) L_Label = false).
  apply flow_join_label with lb1 lx; auto.
  apply  join_label_commutative; auto.
  
  inversion H0; subst; auto.
  apply L_eq_heap; auto.
  - intros. apply H5 in H10. inversion H10; subst; auto.
    case_eq (beq_oid o2 o); intro. apply beq_oid_equal in H16.
    rewrite H16 in H12. rewrite <- H12 in H1. inversion H1; subst.
    assert (flow_to lb2 (join_label lb1 lx) = false).
    apply  flow_no_H_to_L; auto. 
    try (inconsist_label).
    apply object_equal_L with lb0 lb2 cls1 cls2 F1 F2; auto.    

    apply lookup_updated_not_affected with o (Heap_OBJ cls (fields_update F f v) lo) h2; auto.
    intro contra. rewrite contra in H16.
    assert (beq_oid o o = true).
    apply beq_oid_same. rewrite H16 in H17; inversion H17.

    auto. destruct H15.
    destruct H17. destruct H18. destruct H19.
   
    split; auto.
    split; auto. split; auto. split;auto. 

    intros. 
    destruct H20 with fname fo1 fo2; auto.
    destruct H23 as [hof2]. rename x into hof1.
    exists hof1. exists hof2.
    destruct H23; auto.  destruct H24. 
    split; auto.
    assert ( Some  hof2
      = lookup_heap_obj
          (update_heap_obj h2 o (Heap_OBJ cls (fields_update F f v) lo)) fo2).
    apply lookup_updated_not_affected with o (Heap_OBJ cls (fields_update F f v) lo) h2; auto.
    intro contra. apply H5 in H25. inversion H25. subst; auto.
    rewrite <- H1 in H27. inversion H27. subst; auto. 

    assert (flow_to lo L_Label  = false).
    apply  flow_transitive with (join_label lb1 lx); auto.
    try (inconsist_label). auto. 
  - intros.
    apply lookup_updated_heap_must_none in H10.
    auto. 
  - intros.
    case_eq (beq_oid o0 o); intro.
    apply beq_oid_equal in H12.
    rewrite <- H12 in H1. apply H9 with cls F lo; auto.
    apply flow_transitive with (join_label lb1 lx); auto.

    assert (Some (Heap_OBJ cls0 F0 lb) = lookup_heap_obj h2 o0).
    apply lookup_updated_not_affected_reverse
      with o (Heap_OBJ cls (fields_update F f v) lo)
           (update_heap_obj h2 o (Heap_OBJ cls (fields_update F f v) lo)); auto.
    intro contra. rewrite contra in H12.
    assert (beq_oid o o = true). apply beq_oid_same.
    rewrite H12 in H13. inversion H13.
    apply H9 with cls0 F0 lb; auto. 
Qed. Hint Resolve  update_h2_with_H_preserve_bijection.   






Lemma update_field_h1_preserve_L_eq_tm {DecOid : forall a1 a2 : oid, Decision (a1 = a2)} :
  forall  φ h1 h2 ct cls F lo o lb1 lx
          t1 t2 v f ,
  wfe_heap ct h2 ->  wfe_heap ct h1 -> 
  L_equivalence_heap h1 h2 φ ->
  L_equivalence_tm t1 h1 t2 h2 φ ->
  Some (Heap_OBJ cls F lo) = lookup_heap_obj h1 o ->
  flow_to lo (join_label lb1 lx) = true ->
  flow_to lb1 L_Label = false ->
  value v ->
  (*tm_has_type ct gamma h1 ((FieldWrite (ObjId o) f (unlabelOpaque (v_opa_l v lx)))) T ->*)
  L_equivalence_tm t1 (update_heap_obj h1 o (Heap_OBJ cls (fields_update F f v) lo))
                    t2 h2 φ.
Proof with eauto. 
  intros φ h1 h2 ct cls F lo o lb1 lx t1 t2 v f.
  intros.
  assert ( flow_to (join_label lb1 lx) L_Label = false).
  apply flow_join_label with lb1 lx; auto.
  apply  join_label_commutative; auto.

  assert (flow_to lo L_Label = false).
  apply flow_transitive with (join_label lb1 lx); auto. 

  generalize dependent t2.  
  induction t1; intros;inversion H2; subst; auto.

  apply L_equivalence_tm_eq_object_L  with cls1 F1 lb0 cls2 F2 lb2; subst; auto.
  apply lookup_updated_not_affected with o (Heap_OBJ cls (fields_update F f v) lo) h1; auto.
  intro contra. rewrite contra in H11. rewrite <- H11 in H3. inversion H3; subst; auto.
  try (inconsist_label).

  case_eq (beq_oid o0 o); intro.
  apply beq_oid_equal in H9. subst; auto.
  rewrite <- H10 in H3; inversion H3; subst; auto. 
  apply L_equivalence_tm_eq_object_H  with cls1 cls2 (fields_update F1 f v) lb0  F2 lb2; subst; auto.
  apply lookup_updated with h1 ((Heap_OBJ cls1 F1 lb0) ); auto.

  apply L_equivalence_tm_eq_object_H  with cls1 cls2  F1 lb0  F2 lb2; subst; auto.
  apply lookup_updated_not_affected with o (Heap_OBJ cls (fields_update F f v) lo) h1; auto.
  intro contra.  rewrite contra in H9. pose proof (beq_oid_same o).
  rewrite H9 in H14; inversion H14. 
Qed. Hint Resolve   update_field_h1_preserve_L_eq_tm.




Lemma update_field_h2_preserve_L_eq_tm {DecOid : forall a1 a2 : oid, Decision (a1 = a2)} :
  forall  φ h1 h2 ct cls F lo o lb1 lx
          t1 t2 v f ,
  wfe_heap ct h2 ->  wfe_heap ct h1 -> 
  L_equivalence_heap h1 h2 φ ->
  L_equivalence_tm t1 h1 t2 h2 φ ->
  Some (Heap_OBJ cls F lo) = lookup_heap_obj h2 o ->
  flow_to lo (join_label lb1 lx) = true ->
  flow_to lb1 L_Label = false ->
  value v ->
  L_equivalence_tm t1 h1
                    t2 (update_heap_obj h2 o (Heap_OBJ cls (fields_update F f v) lo)) φ.
Proof with eauto. 
  intros φ h1 h2 ct cls F lo o lb1 lx t1 t2 v f.
  intros.
  assert ( flow_to (join_label lb1 lx) L_Label = false).
  apply flow_join_label with lb1 lx; auto.
  apply  join_label_commutative; auto.

  assert (flow_to lo L_Label = false).
  apply flow_transitive with (join_label lb1 lx); auto. 

  generalize dependent t2.  
  induction t1; intros;inversion H2; subst; auto.

  apply L_equivalence_tm_eq_object_L  with cls1 F1 lb0 cls2 F2 lb2; subst; auto.
  apply lookup_updated_not_affected with o (Heap_OBJ cls (fields_update F f v) lo) h2; auto.
  intro contra. rewrite contra in H13. rewrite <- H13 in H3. inversion H3; subst; auto.
  try (inconsist_label).

  case_eq (beq_oid o2 o); intro.
  apply beq_oid_equal in H9. subst; auto.
  rewrite <- H12 in H3; inversion H3; subst; auto. 
  apply L_equivalence_tm_eq_object_H  with cls1 cls2 F1 lb0 (fields_update F2 f v) lb2; subst; auto.
  apply lookup_updated with h2 ((Heap_OBJ cls2 F2 lb2) ); auto.

  apply L_equivalence_tm_eq_object_H  with cls1 cls2 F1 lb0 F2 lb2; subst; auto.
  apply lookup_updated_not_affected with o (Heap_OBJ cls (fields_update F f v) lo) h2; auto.
  intro contra.  rewrite contra in H9. pose proof (beq_oid_same o).
  rewrite H9 in H14; inversion H14. 
Qed. Hint Resolve   update_field_h2_preserve_L_eq_tm.


Lemma update_field_h1_preserve_L_eq_fs {DecOid : forall a1 a2 : oid, Decision (a1 = a2)} :
  forall  φ h1 h2 ct cls F lo o lb1 lx
          fs1 fs2 v f ,
  wfe_heap ct h2 ->  wfe_heap ct h1 -> 
  L_equivalence_heap h1 h2 φ ->
  L_equivalence_fs fs1 h1 fs2 h2 φ ->
  Some (Heap_OBJ cls F lo) = lookup_heap_obj h1 o ->
  flow_to lo (join_label lb1 lx) = true ->
  flow_to lb1 L_Label = false ->
  value v ->
  L_equivalence_fs fs1 (update_heap_obj h1 o (Heap_OBJ cls (fields_update F f v) lo))
                    fs2 h2 φ.
Proof with eauto. 
  intros φ h1 h2 ct cls F lo o lb1 lx fs1 fs2 v f.
  intros.
  generalize dependent fs2.
  induction fs1; intros; inversion H2; subst; auto.

  apply L_equal_fs; auto.
  apply update_field_h1_preserve_L_eq_tm with ct lb1 lx; auto.
Qed. Hint Resolve update_field_h1_preserve_L_eq_fs.


Lemma update_field_h2_preserve_L_eq_fs {DecOid : forall a1 a2 : oid, Decision (a1 = a2)} :
  forall  φ h1 h2 ct cls F lo o lb1 lx
          fs1 fs2 v f ,
  wfe_heap ct h2 ->  wfe_heap ct h1 -> 
  L_equivalence_heap h1 h2 φ ->
  L_equivalence_fs fs1 h1 fs2 h2 φ ->
  Some (Heap_OBJ cls F lo) = lookup_heap_obj h2 o ->
  flow_to lo (join_label lb1 lx) = true ->
  flow_to lb1 L_Label = false ->
  value v ->
  L_equivalence_fs fs1 h1
                    fs2 (update_heap_obj h2 o (Heap_OBJ cls (fields_update F f v) lo)) φ.
Proof with eauto. 
  intros φ h1 h2 ct cls F lo o lb1 lx fs1 fs2 v f.
  intros.
  generalize dependent fs2.
  induction fs1; intros; inversion H2; subst; auto.

  apply L_equal_fs; auto.
  apply update_field_h2_preserve_L_eq_tm with ct lb1 lx; auto.
Qed. Hint Resolve update_field_h2_preserve_L_eq_fs.


Lemma update_field_h1_preserve_L_eq_store {DecOid : forall a1 a2 : oid, Decision (a1 = a2)} :
  forall  φ h1 h2 ct cls F lo o lb1 lx
          sf1 sf2 v f ,
  wfe_heap ct h2 ->  wfe_heap ct h1 -> 
  L_equivalence_heap h1 h2 φ ->
  L_equivalence_store sf1 h1 sf2 h2 φ ->
  Some (Heap_OBJ cls F lo) = lookup_heap_obj h1 o ->
  flow_to lo (join_label lb1 lx) = true ->
  flow_to lb1 L_Label = false ->
  value v ->
  L_equivalence_store sf1 (update_heap_obj h1 o (Heap_OBJ cls (fields_update F f v) lo))
                    sf2 h2 φ.
Proof with eauto.
  intros  φ h1 h2 ct cls F lo o lb1 lx
          sf1 sf2 v f.
  intros.
  assert ( flow_to (join_label lb1 lx) L_Label = false).
  apply flow_join_label with lb1 lx; auto.
  apply  join_label_commutative; auto.

  assert (flow_to lo L_Label = false).
  apply flow_transitive with (join_label lb1 lx); auto. 

  inversion H2; subst; auto. 
  apply L_equivalence_store_L; auto.
  intros.
  - apply H9 with x o1 cls1 F1 lb0 in H16; auto.
    destruct H16 as [o2]. destruct H16.
    exists o2. split; auto.
    apply update_field_h1_preserve_L_eq_tm with ct lb1 lx; auto.
    apply lookup_updated_not_affected_reverse
      with o (Heap_OBJ cls (fields_update F f v) lo)
           (update_heap_obj h1 o (Heap_OBJ cls (fields_update F f v) lo)); auto.
    intro contra. rewrite contra in H16.
    assert (Some (Heap_OBJ cls (fields_update F f v) lo)
            =
            lookup_heap_obj
              (update_heap_obj h1 o (Heap_OBJ cls (fields_update F f v) lo)) o
           ).
    apply lookup_updated with h1 (Heap_OBJ cls F lo); auto.
    rewrite contra in H17.
    rewrite <- H17 in H19.
    inversion H19. subst; auto.
    try (inconsist_label).
  - intros.
    apply H10 with x o2 cls2 F2 lb2 in H17; auto.
    destruct H17 as [o1].
    destruct H17.
    exists o1. split; auto.
    apply update_field_h1_preserve_L_eq_tm with ct lb1 lx; auto.

  - intros.
    apply H11 in H16; auto.
    destruct H16 as [v2]. destruct H16.
    exists v2. split; auto.
    apply update_field_h1_preserve_L_eq_tm with ct lb1 lx; auto.

  - intros.
    apply H12 in H16; auto.
    destruct H16 as [v1]. destruct H16.
    exists v1. split; auto.
    apply update_field_h1_preserve_L_eq_tm with ct lb1 lx; auto.
    
  - intros.
    apply H13 in H16; auto.
    destruct H16 as [v2]. destruct H16.
    exists v2. split; auto.
    apply update_field_h1_preserve_L_eq_tm with ct lb1 lx; auto.

  - intros.
    apply H14 in H16; auto.
    destruct H16 as [v1]. destruct H16.
    exists v1. split; auto.
    apply update_field_h1_preserve_L_eq_tm with ct lb1 lx; auto.
Qed. Hint Resolve update_field_h1_preserve_L_eq_store.



Lemma update_field_h2_preserve_L_eq_store {DecOid : forall a1 a2 : oid, Decision (a1 = a2)} :
  forall  φ h1 h2 ct cls F lo o lb1 lx
          sf1 sf2 v f ,
  wfe_heap ct h2 ->  wfe_heap ct h1 -> 
  L_equivalence_heap h1 h2 φ ->
  L_equivalence_store sf1 h1 sf2 h2 φ ->
  Some (Heap_OBJ cls F lo) = lookup_heap_obj h2 o ->
  flow_to lo (join_label lb1 lx) = true ->
  flow_to lb1 L_Label = false ->
  value v ->
  L_equivalence_store sf1 h1
                    sf2 (update_heap_obj h2 o (Heap_OBJ cls (fields_update F f v) lo)) φ.
Proof with eauto.
  intros  φ h1 h2 ct cls F lo o lb1 lx
          sf1 sf2 v f.
  intros.
  assert ( flow_to (join_label lb1 lx) L_Label = false).
  apply flow_join_label with lb1 lx; auto.
  apply  join_label_commutative; auto.

  assert (flow_to lo L_Label = false).
  apply flow_transitive with (join_label lb1 lx); auto. 

  inversion H2; subst; auto. 
  apply L_equivalence_store_L; auto.
  intros.
  - apply H9 with x o1 cls1 F1 lb0 in H16; auto.
    destruct H16 as [o2]. destruct H16.
    exists o2. split; auto.
    apply update_field_h2_preserve_L_eq_tm with ct lb1 lx; auto.
(*
    apply lookup_updated_not_affected_reverse
      with o (Heap_OBJ cls (fields_update F f v) lo)
           (update_heap_obj h2 o (Heap_OBJ cls (fields_update F f v) lo)); auto.
    intro contra. rewrite contra in H16.
    assert (Some (Heap_OBJ cls (fields_update F f v) lo)
            =
            lookup_heap_obj
              (update_heap_obj h1 o (Heap_OBJ cls (fields_update F f v) lo)) o
           ).
    apply lookup_updated with h1 (Heap_OBJ cls F lo); auto.
    rewrite <- H16 in H18.
    inversion H18. subst; auto.
    try (inconsist_label). *)
  - intros.
    apply H10 with x o2 cls2 F2 lb2 in H16; auto.
    destruct H16 as [o1].
    destruct H16.
    exists o1. split; auto.
    apply update_field_h2_preserve_L_eq_tm with ct lb1 lx; auto.
    apply lookup_updated_not_affected_reverse
      with o (Heap_OBJ cls (fields_update F f v) lo)
           (update_heap_obj h2 o (Heap_OBJ cls (fields_update F f v) lo)); auto.
    intro contra. rewrite contra in H16.
    assert (Some (Heap_OBJ cls (fields_update F f v) lo)
            =
            lookup_heap_obj
              (update_heap_obj h2 o (Heap_OBJ cls (fields_update F f v) lo)) o
           ).
    apply lookup_updated with h2 (Heap_OBJ cls F lo); auto.
    rewrite contra in H17. 
    rewrite <- H17 in H19.
    inversion H19. subst; auto.
    try (inconsist_label). 

  - intros.
    apply H11 in H16; auto.
    destruct H16 as [v2]. destruct H16.
    exists v2. split; auto.
    apply update_field_h2_preserve_L_eq_tm with ct lb1 lx; auto.

  - intros.
    apply H12 in H16; auto.
    destruct H16 as [v1]. destruct H16.
    exists v1. split; auto.
    apply update_field_h2_preserve_L_eq_tm with ct lb1 lx; auto.
    
  - intros.
    apply H13 in H16; auto.
    destruct H16 as [v2]. destruct H16.
    exists v2. split; auto.
    apply update_field_h2_preserve_L_eq_tm with ct lb1 lx; auto.

  - intros.
    apply H14 in H16; auto.
    destruct H16 as [v1]. destruct H16.
    exists v1. split; auto.
    apply update_field_h2_preserve_L_eq_tm with ct lb1 lx; auto.
Qed. Hint Resolve update_field_h2_preserve_L_eq_store.
    



Lemma update_field_h1_preserve_L_eq_ctn {DecOid : forall a1 a2 : oid, Decision (a1 = a2)} :
  forall  φ h1 h2 ct cls F lo o lb1 lx
          ctn1 ctn2 v f ,
   wfe_heap ct h2 ->  wfe_heap ct h1 -> 
  L_equivalence_heap h1 h2 φ ->
  L_eq_container ctn1 h1 ctn2 h2 φ ->
  Some (Heap_OBJ cls F lo) = lookup_heap_obj h1 o ->
  flow_to lo (join_label lb1 lx) = true ->
  flow_to lb1 L_Label = false ->
  value v ->
  L_eq_container ctn1 (update_heap_obj h1 o (Heap_OBJ cls (fields_update F f v) lo))
                    ctn2 h2 φ.
Proof with eauto. 
  intros φ h1 h2 ct cls F lo o lb1 lx ctn1 ctn2 v f.
  intros.
  generalize dependent ctn2.
  induction ctn1; intros; inversion H2; subst; auto.
  apply  L_eq_ctn; auto.
  apply update_field_h1_preserve_L_eq_tm with ct lb1 lx; auto.
  apply update_field_h1_preserve_L_eq_fs with ct lb1 lx; auto.
  apply update_field_h1_preserve_L_eq_store with ct lb1 lx; auto.
Qed. Hint Resolve update_field_h1_preserve_L_eq_ctn. 



Lemma update_field_h2_preserve_L_eq_ctn {DecOid : forall a1 a2 : oid, Decision (a1 = a2)} :
  forall  φ h1 h2 ct cls F lo o lb1 lx
          ctn1 ctn2 v f ,
   wfe_heap ct h2 ->  wfe_heap ct h1 -> 
  L_equivalence_heap h1 h2 φ ->
  L_eq_container ctn1 h1 ctn2 h2 φ ->
  Some (Heap_OBJ cls F lo) = lookup_heap_obj h2 o ->
  flow_to lo (join_label lb1 lx) = true ->
  flow_to lb1 L_Label = false ->
  value v ->
  L_eq_container ctn1 h1
                    ctn2 (update_heap_obj h2 o (Heap_OBJ cls (fields_update F f v) lo)) φ.
Proof with eauto. 
  intros φ h1 h2 ct cls F lo o lb1 lx ctn1 ctn2 v f.
  intros.
  generalize dependent ctn2.
  induction ctn1; intros; inversion H2; subst; auto.
  apply  L_eq_ctn; auto.
  apply update_field_h2_preserve_L_eq_tm with ct lb1 lx; auto.
  apply update_field_h2_preserve_L_eq_fs with ct lb1 lx; auto.
  apply update_field_h2_preserve_L_eq_store with ct lb1 lx; auto.
Qed. Hint Resolve update_field_h2_preserve_L_eq_ctn.

  

Lemma update_field_h1_preserve_L_eq_ctns {DecOid : forall a1 a2 : oid, Decision (a1 = a2)} :
  forall  φ h1 h2 ct cls F lo o lb1 lx
          ctns1 ctns2 v f ,
   wfe_heap ct h2 ->  wfe_heap ct h1 -> 
  L_equivalence_heap h1 h2 φ ->
  L_eq_ctns ctns1 h1 ctns2 h2 φ ->
  Some (Heap_OBJ cls F lo) = lookup_heap_obj h1 o ->
  flow_to lo (join_label lb1 lx) = true ->
  flow_to lb1 L_Label = false ->
  value v ->
  L_eq_ctns ctns1 (update_heap_obj h1 o (Heap_OBJ cls (fields_update F f v) lo))
                    ctns2 h2 φ.
Proof with eauto. 
  intros φ h1 h2 ct cls F lo o lb1 lx ctns1 ctns2 v f.
  intros.
  generalize dependent ctns2.
  induction ctns1; intros; inversion H2; subst; auto.
  apply  L_eq_ctns_list; auto.
  apply update_field_h1_preserve_L_eq_ctn with ct lb1 lx; auto.
Qed. Hint Resolve update_field_h1_preserve_L_eq_ctns.


Lemma update_field_h2_preserve_L_eq_ctns {DecOid : forall a1 a2 : oid, Decision (a1 = a2)} :
  forall  φ h1 h2 ct cls F lo o lb1 lx
          ctns1 ctns2 v f ,
   wfe_heap ct h2 ->  wfe_heap ct h1 -> 
  L_equivalence_heap h1 h2 φ ->
  L_eq_ctns ctns1 h1 ctns2 h2 φ ->
  Some (Heap_OBJ cls F lo) = lookup_heap_obj h2 o ->
  flow_to lo (join_label lb1 lx) = true ->
  flow_to lb1 L_Label = false ->
  value v ->
  L_eq_ctns ctns1 h1
                    ctns2 (update_heap_obj h2 o (Heap_OBJ cls (fields_update F f v) lo)) φ.
Proof with eauto. 
  intros φ h1 h2 ct cls F lo o lb1 lx ctns1 ctns2 v f.
  intros.
  generalize dependent ctns1.
  induction ctns2; intros; inversion H2; subst; auto.
  apply  L_eq_ctns_list; auto.
  apply update_field_h2_preserve_L_eq_ctn with ct lb1 lx; auto.
Qed. Hint Resolve update_field_h2_preserve_L_eq_ctns.


Lemma update_field_h1_preserve_config_eq {DecOid : forall a1 a2 : oid, Decision (a1 = a2)}:
  forall  φ h1 h2 ct cls F lo o lb1 lx
          ctn1 ctn2 ctns1 ctns2 v f,
    wfe_heap ct h2 ->  wfe_heap ct h1 -> 
    L_equivalence_heap h1 h2 φ ->
    L_equivalence_config (Config ct ctn1 ctns1  h1)
                         (Config ct ctn2 ctns2  h2) φ ->

    Some (Heap_OBJ cls F lo) = lookup_heap_obj h1 o ->
    flow_to lo (join_label lb1 lx) = true ->
    flow_to lb1 L_Label = false ->
    value v ->
    L_equivalence_config
      (Config ct ctn1 ctns1 (update_heap_obj h1 o (Heap_OBJ cls (fields_update F f v) lo)))
      (Config ct ctn2 ctns2  h2)  φ.
Proof with eauto.
  intros.
  
  remember (Config ct ctn1 ctns1 h1) as config1.
  remember (Config ct ctn2 ctns2 h2) as config2.
  generalize dependent ctn1. generalize dependent ctn2.
  generalize dependent ctns1. generalize dependent ctns2. 
  induction H2; subst; intros; inversion Heqconfig1; inversion Heqconfig2; subst; auto.
  apply L_equivalence_config_L; auto.
  apply update_field_h1_preserve_L_eq_ctn with ct lb1 lx; auto.
  apply update_field_h1_preserve_L_eq_ctns with ct lb1 lx; auto.

  
  induction ctns3. induction ctns0.
  apply L_equivalence_config_H; auto.
  unfold low_component.  
  rewrite H2; rewrite H7.
  apply L_equivalence_config_L; auto.
  apply L_eq_ctn; auto.
  apply L_equivalence_store_L; auto; intros; try (inversion H9).
  split; auto. 


  apply L_equivalence_config_H; auto.
  unfold low_component.  
  rewrite H2; rewrite H7.
  fold low_component.
  unfold low_component  in H8.
  rewrite H2 in H8. rewrite H7 in H8.
  fold low_component  in H8.

  assert (  L_equivalence_config
    (Config ct (Container hole nil L_Label empty_stack_frame) nil
       (update_heap_obj h1 o (Heap_OBJ cls (fields_update F f v) lo)))
    (Config ct (Container hole nil L_Label empty_stack_frame) nil h1)  φ).
  apply L_equivalence_config_L; auto.
  apply L_eq_ctn; auto.
  apply L_equivalence_store_L; auto; intros;try (inversion H9).
  split; auto.  

  
  remember ((low_component ct a ctns0 h2)) as conf.
  destruct conf. destruct c0. 
  assert (c = ct /\ h = h2 /\ flow_to l0 L_Label = true).
  apply low_component_lead_to_L with t f0 s a 
                                       l  ctns0; auto.
  destruct H10. destruct H11. subst; auto. 
  apply L_equivalence_config_L; auto.
  apply update_field_h1_preserve_L_eq_ctn with ct lb1 lx; auto.
  inversion H8; subst;  auto. 
  try (inconsist_label).
  inversion H8; subst;  auto.  
  inversion H29; subst;  auto. 
  try (inconsist_label).
  inversion H8. inversion H8. 

  + apply L_equivalence_config_H; auto.
  remember (low_component ct (Container t1 fs1 lb0 sf1) (a :: ctns3) h1) as conf1.
  remember ((low_component ct (Container t2 fs2 lb2 sf2) ctns0 h2)) as conf2.
  destruct conf1. destruct conf2.
  destruct c0. 
  assert (c = ct /\ h = h1 /\ flow_to l1 L_Label = true).
  apply low_component_lead_to_L with t f0 s (Container t1 fs1 lb0 sf1) l (a :: ctns3)  ; auto. 

  destruct c2. 
  assert (c1 = ct /\ h0 = h2 /\ flow_to l2 L_Label = true).
  apply low_component_lead_to_L with t0 f1 s0 (Container t2 fs2 lb2 sf2) l0 ctns0  ; auto.
  destruct H9. destruct H11.
  destruct H10. destruct H13.     subst. auto.
 (*
  inversion H; subst; auto. inversion H0; subst; auto. 
  assert (valid_ctn ct (Container t f l1 s)  h1 /\ valid_ctns ct l h1).
  apply valid_preservation_low_component with (Container t1 fs1 lb1 sf1)
                                                 (a :: ctns3)
                                                 h1  ; auto.
  assert (valid_ctn ct (Container t0 f0 l2 s0)  h2 /\ valid_ctns ct l0 h2).
  apply valid_preservation_low_component with (Container t2 fs2 lb2 sf2)
                                                 ctns0
                                                 h2  ; auto.
  *)
  assert (Config ct (Container t f0 l1 s) l (update_heap_obj h1 o (Heap_OBJ cls (fields_update F f v) lo))
          = (low_component ct (Container t1 fs1 lb0 sf1) (a :: ctns3)
                           (update_heap_obj h1 o (Heap_OBJ cls (fields_update F f v) lo)))
         ).
  apply low_component_irrelevant_to_heap with h1; auto.  
  rewrite <- H9.  
  apply   L_equivalence_config_L; auto.
  apply update_field_h1_preserve_L_eq_ctn  with ct lb1 lx; auto.
  inversion H8; subst; auto. 
  try (inconsist_label).
  apply update_field_h1_preserve_L_eq_ctns  with ct lb1 lx; auto.
  inversion H8; subst; auto. 
  try (inconsist_label).
  inversion H8.  inversion H8.
  inversion H8. inversion H8. 
Qed. Hint Resolve update_field_h1_preserve_config_eq.


Lemma update_field_h2_preserve_config_eq {DecOid : forall a1 a2 : oid, Decision (a1 = a2)}:
  forall  φ h1 h2 ct cls F lo o lb1 lx
          ctn1 ctn2 ctns1 ctns2 v f,
    wfe_heap ct h2 ->  wfe_heap ct h1 -> 
    L_equivalence_heap h1 h2 φ ->
    L_equivalence_config (Config ct ctn1 ctns1  h1)
                         (Config ct ctn2 ctns2  h2) φ ->

    Some (Heap_OBJ cls F lo) = lookup_heap_obj h2 o ->
    flow_to lo (join_label lb1 lx) = true ->
    flow_to lb1 L_Label = false ->
    value v ->
    L_equivalence_config
      (Config ct ctn1 ctns1 h1)
      (Config ct ctn2 ctns2  (update_heap_obj h2 o (Heap_OBJ cls (fields_update F f v) lo)))  φ.
Proof with eauto.
  intros.
  
  remember (Config ct ctn1 ctns1 h1) as config1.
  remember (Config ct ctn2 ctns2 h2) as config2.
  generalize dependent ctn1. generalize dependent ctn2.
  generalize dependent ctns1. generalize dependent ctns2. 
  induction H2; subst; intros; inversion Heqconfig1; inversion Heqconfig2; subst; auto.
  apply L_equivalence_config_L; auto.
  apply update_field_h2_preserve_L_eq_ctn with ct lb1 lx; auto.
  apply update_field_h2_preserve_L_eq_ctns with ct lb1 lx; auto.

  
  induction ctns3. induction ctns0.
  apply L_equivalence_config_H; auto.
  unfold low_component.  
  rewrite H2; rewrite H7.
  apply L_equivalence_config_L; auto.
  apply L_eq_ctn; auto.
  apply L_equivalence_store_L; auto; intros; try (inversion H9).
  split; auto.  


  apply L_equivalence_config_H; auto.
  unfold low_component.  
  rewrite H2; rewrite H7.
  fold low_component.
  unfold low_component  in H8.
  rewrite H2 in H8. rewrite H7 in H8.
  fold low_component  in H8.

  
  assert (  L_equivalence_config
    (Config ct (Container hole nil L_Label empty_stack_frame) nil
       h1 )
    (Config ct (Container hole nil L_Label empty_stack_frame) nil
    (update_heap_obj h2 o (Heap_OBJ cls (fields_update F f v) lo)))  φ).
  apply L_equivalence_config_L; auto.
  apply L_eq_ctn; auto.
  apply L_equivalence_store_L; auto; intros; try (inversion H9).
  split; auto. 

  
  remember ((low_component ct a ctns0 h2)) as conf.
  destruct conf. destruct c0. 
  assert (c = ct /\ h = h2 /\ flow_to l0 L_Label = true).
  apply low_component_lead_to_L with t f0 s a 
                                     l  ctns0; auto.  
  destruct H10. destruct H11. subst; auto.

  assert (Config ct (Container t f0 l0 s) l
                 (update_heap_obj h2 o (Heap_OBJ cls (fields_update F f v) lo)) 
          = (low_component ct a ctns0 (update_heap_obj h2 o (Heap_OBJ cls (fields_update F f v) lo)))).
  apply low_component_irrelevant_to_heap with h2; auto. rewrite <- H10.  
  apply L_equivalence_config_L; auto.
  apply update_field_h2_preserve_L_eq_ctn with ct lb1 lx; auto.
  inversion H8; subst;  auto.  
  try (inconsist_label).
  inversion H8; subst;  auto.
  apply update_field_h2_preserve_L_eq_ctns with ct lb1 lx; auto.
  try (inconsist_label).
  inversion H8.
  inversion H8. 


  + apply L_equivalence_config_H; auto.
  remember (low_component ct (Container t1 fs1 lb0 sf1) (a :: ctns3) h1) as conf1.
  remember ((low_component ct (Container t2 fs2 lb2 sf2) ctns0 h2)) as conf2.
  destruct conf1. destruct conf2.
  destruct c0. 
  assert (c = ct /\ h = h1 /\ flow_to l1 L_Label = true).
  apply low_component_lead_to_L with t f0 s (Container t1 fs1 lb0 sf1) l (a :: ctns3)  ; auto. 

  destruct c2. 
  assert (c1 = ct /\ h0 = h2 /\ flow_to l2 L_Label = true).
  apply low_component_lead_to_L with t0 f1 s0 (Container t2 fs2 lb2 sf2) l0 ctns0  ; auto.
  destruct H9. destruct H11.
  destruct H10. destruct H13.     subst; auto.
  assert (Config ct (Container t0 f1 l2 s0) l0 (update_heap_obj h2 o (Heap_OBJ cls (fields_update F f v) lo))
          = (low_component ct (Container t2 fs2 lb2 sf2)  ctns0
                           (update_heap_obj h2 o (Heap_OBJ cls (fields_update F f v) lo)))
         ).
  apply low_component_irrelevant_to_heap with h2; auto.  
  rewrite <- H9.  
  apply   L_equivalence_config_L; auto.
  apply update_field_h2_preserve_L_eq_ctn  with ct lb1 lx; auto.
  inversion H8; subst; auto. 
  try (inconsist_label).
  apply update_field_h2_preserve_L_eq_ctns  with ct lb1 lx; auto.
  inversion H8; subst; auto. 
  try (inconsist_label).
  inversion H8.  inversion H8.
  inversion H8. inversion H8. 
Qed. Hint Resolve update_field_h2_preserve_config_eq.

