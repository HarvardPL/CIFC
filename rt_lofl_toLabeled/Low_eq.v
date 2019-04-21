Require Import Label.
Require Import Language Types.
Require Import Lemmas.
Require Import Coq.Lists.List.
Require Import bijection.
Require Import decision. 
Require Import Coq.Bool.Bool. 



Inductive L_equivalence_tm : tm -> heap -> tm -> heap ->  (bijection oid oid )->  Prop :=
  | L_equivalence_tm_eq_Tvar : forall id1 id2 h1 h2  φ , 
      id1 = id2 -> L_equivalence_tm (Tvar id1) h1 (Tvar id2) h2  φ
  | L_equivalence_tm_eq_eq_cmp : forall e1 e2 a1 a2 h1 h2  φ,
      L_equivalence_tm e1 h1 e2 h2  φ->
      L_equivalence_tm a1 h1 a2 h2  φ->
      L_equivalence_tm (EqCmp e1 a1) h1 (EqCmp e2 a2) h2  φ
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
  | L_equivalence_tm_eq_objectLabelOf : forall e1 e2 h1 h2  φ,
      L_equivalence_tm e1 h1 e2 h2  φ->
      L_equivalence_tm (objectLabelOf e1) h1 (objectLabelOf e2) h2  φ
  | L_equivalence_tm_eq_raiseLabel : forall e1 e2 h1 h2 l1 l2 φ,
      L_equivalence_tm e1 h1 e2 h2  φ->
      l1 = l2 ->
      L_equivalence_tm (raiseLabel e1 l1) h1 (raiseLabel e2 l2) h2  φ
  | L_equivalence_tm_eq_toLabeled : forall e1 e2 l1 l2 h1 h2  φ,
      L_equivalence_tm e1 h1 e2 h2  φ->
      L_equivalence_tm l1 h1 l2 h2  φ->
      L_equivalence_tm (toLabeled e1 l1) h1 (toLabeled e2 l2) h2  φ
  | L_equivalence_tm_eq_getCurrentLevel : forall h1 h2 φ ,
      L_equivalence_tm getCurrentLevel h1 getCurrentLevel h2 φ                     
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
  | L_equivalence_tm_eq_object_L : forall o1 o2 h1 h2 cls1 F1 lo cls2 F2  φ ll, 
      left φ o1 = Some o2 ->
      Some (Heap_OBJ cls1 F1 lo ll) = lookup_heap_obj h1 o1 ->
      flow_to ll L_Label = true ->
      Some (Heap_OBJ cls2 F2 lo ll) = lookup_heap_obj h2 o2 ->
      L_equivalence_tm (ObjId o1) h1 (ObjId o2) h2 φ
  | L_equivalence_tm_eq_object_H : forall o1 o2 h1 h2 cls1 cls2 F1 lo1 F2 lo2 φ ll1 ll2, 
      Some (Heap_OBJ cls1 F1 lo1 ll1) = lookup_heap_obj h1 o1 ->
      Some (Heap_OBJ cls2 F2 lo2 ll2) = lookup_heap_obj h2 o2 ->
      flow_to ll1 L_Label = false  ->
      flow_to ll2 L_Label = false  ->
      L_equivalence_tm (ObjId o1) h1 (ObjId o2) h2 φ                     
  | L_equivalence_tm_eq_v_l_L : forall lb e1 e2 h1 h2 φ, 
      flow_to lb L_Label = true ->
      L_equivalence_tm e1 h1 e2 h2 φ->
      value e1 -> value e2 ->
      L_equivalence_tm (v_l e1 lb) h1 (v_l e2 lb) h2 φ
  | L_equivalence_tm_eq_v_l_H : forall e1 e2 lb h1 h2 φ, 
      flow_to lb L_Label = false ->
       value e1 -> value e2 ->
      L_equivalence_tm (v_l e1 lb) h1 (v_l e2 lb) h2 φ
  | L_equivalence_tm_eq_v_opa_l_L : forall lb e1 e2 h1 h2 φ, 
      flow_to lb L_Label = true ->
      value (v_opa_l e1 lb) ->
      value (v_opa_l e2 lb) ->
      L_equivalence_tm e1 h1 e2 h2 φ->
      L_equivalence_tm (v_opa_l e1 lb) h1 (v_opa_l e2 lb) h2 φ
  | L_equivalence_tm_eq_v_opa_l_H : forall e1 e2 l1 l2 h1 h2 φ, 
      flow_to l1 L_Label = false ->
      flow_to l2 L_Label = false ->
      value (v_opa_l e1 l1) ->
      value (v_opa_l e2 l2) ->
      L_equivalence_tm (v_opa_l e1 l1) h1 (v_opa_l e2 l2) h2 φ
  | L_equivalence_tm_eq_hole : forall h1 h2 φ,
      L_equivalence_tm (hole) h1 (hole) h2 φ
  | L_equivalence_tm_eq_return_hole : forall h1 h2 φ,
      L_equivalence_tm (return_hole) h1 (return_hole) h2 φ.
Hint Constructors L_equivalence_tm.

Inductive L_equivalence_object : oid -> heap -> oid -> heap -> (bijection oid oid )-> Prop :=
   | object_equal_H : forall o1 o2 h1 h2 lb cls1 cls2 F1 F2 ll φ,
        Some (Heap_OBJ cls1 F1 lb ll) = lookup_heap_obj h1 o1 -> 
        Some (Heap_OBJ cls2 F2 lb ll) = lookup_heap_obj h2 o2 ->
        flow_to ll L_Label = true ->
        flow_to lb L_Label = false ->
        (cls1 = cls2) ->
        L_equivalence_object o1 h1 o2 h2 φ
   | object_equal_L : forall o1 o2 h1 h2 lb cls1 cls2 F1 F2 φ ll,
        Some (Heap_OBJ cls1 F1 lb ll) = lookup_heap_obj h1 o1 -> 
        Some (Heap_OBJ cls2 F2 lb ll) = lookup_heap_obj h2 o2 ->
        flow_to lb L_Label = true ->
        flow_to ll L_Label = true ->
        ((cls1 = cls2) /\  
            (forall fname, F1 fname = None <-> F2 fname = None )  /\
            (forall fname, F1 fname = Some null <-> F2 fname = Some null ) /\
            (forall fname fo1 fo2,
                F1 fname = Some (ObjId fo1)
                -> F2 fname = Some (ObjId fo2) ->
                (exists cls_f1 cls_f2 lof1 lof2 FF1 FF2 llf1 llf2,
                    lookup_heap_obj h1 fo1 = Some (Heap_OBJ cls_f1 FF1 lof1 llf1)
                 /\ lookup_heap_obj h2 fo2 = Some (Heap_OBJ cls_f2 FF2 lof2 llf2)
                 /\ (
                   ( left φ fo1 = Some fo2
                     /\ lof1 = lof2
                     /\ (flow_to llf1 L_Label = true /\ flow_to llf2 L_Label = true)
                     /\ cls_f1 = cls_f2 /\ llf1 = llf2)  \/
                    ( flow_to llf1 L_Label = false
                     /\ flow_to llf2 L_Label = false)
            )))
        )-> L_equivalence_object o1 h1 o2 h2 φ.
Hint Constructors L_equivalence_object.


Inductive L_equivalence_store : stack_frame -> heap -> stack_frame -> heap ->  (bijection oid oid ) -> Prop :=
| L_equivalence_store_L : forall  sf1 sf2 h1 h2  φ ,
    (forall v1 v2 x,
      sf1 x = Some v1 ->
    value v1 ->
    sf2 x = Some v2 ->
    value v2 -> 
    L_equivalence_tm v1 h1 v2 h2  φ ) /\
    (sf1 = empty_stack_frame <->
     sf2 = empty_stack_frame
    ) ->
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
      (forall o cls F lb ll, lookup_heap_obj h1 o = Some (Heap_OBJ cls F lb ll)->
                 flow_to ll L_Label = false ->
                 left φ o = None) ->
      (forall o cls F lb ll, lookup_heap_obj h2 o = Some (Heap_OBJ cls F lb ll)->
                 flow_to ll L_Label = false ->
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
        (Heap_OBJ  cls_def (init_field_map (find_fields cls_def) empty_field_map) lb2 lb2)) ->
  h2' = (add_heap_obj h2 (get_fresh_oid h2) 
        (Heap_OBJ  cls_def (init_field_map (find_fields cls_def) empty_field_map) lb2 lb2)) ->
  exists φ', L_equivalence_heap h1' h2' φ'.
  Proof with eauto. 
  intros  t1 h1 h1' t2 h2 h2' lb2 cls_def ct φ. 
  intros.
  inversion H2.  subst; auto.
  remember (add_heap_obj h1 (get_fresh_oid h1) 
        (Heap_OBJ  cls_def (init_field_map (find_fields cls_def) empty_field_map) lb2 lb2)) as h1'.
  remember (add_heap_obj h2 (get_fresh_oid h2) 
                         (Heap_OBJ  cls_def (init_field_map (find_fields cls_def) empty_field_map) lb2 lb2)) as h2'.
  assert (lookup_heap_obj h1 (get_fresh_oid h1)  = None). 
  apply fresh_oid_heap with ct; auto.   
  assert (lookup_heap_obj h2 (get_fresh_oid h2)  = None). 
  apply fresh_oid_heap with ct; auto. 
  apply H7 in H4. apply H8 in H5.
  assert (forall a1 a2 : oid, Decision (a1 = a2)). auto.
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
        (Heap_OBJ  cls_def (init_field_map (find_fields cls_def) empty_field_map) lb2 lb2)) as h1'.
  remember (add_heap_obj h2 (get_fresh_oid h2) 
                         (Heap_OBJ  cls_def (init_field_map (find_fields cls_def) empty_field_map) lb2 lb2)) as h2'.
  assert (lookup_heap_obj h1' (get_fresh_oid h1) = Some (Heap_OBJ  cls_def (init_field_map (find_fields cls_def) empty_field_map) lb2 lb2) ).
  subst; auto.
    assert (lookup_heap_obj h2' (get_fresh_oid h2) = Some (Heap_OBJ  cls_def (init_field_map (find_fields cls_def) empty_field_map) lb2 lb2) ).
    subst; auto.

    apply object_equal_L with lb2 cls_def cls_def (init_field_map (find_fields cls_def) empty_field_map) (init_field_map (find_fields cls_def) empty_field_map) lb2; auto.
  split; auto. 
  split; auto. split; auto. split; auto.    
  split; auto.   
  intros.  
  pose proof (initilized_fields_empty (find_fields cls_def) fname).  
  
  destruct H19;
    rewrite H19 in H18; inversion H18.
  intuition.  
   assert (left (extend_bijection φ o3 o4 H4 H5)  o1 = 
           left φ o1) by (apply left_extend_bijection_neq; auto).
   rewrite H14 in H15. assert (left φ o1 = Some o2). auto.
   apply H6 in H16. inversion H16; subst; auto.
  
  assert ( lookup_heap_obj
     (add_heap_obj h1 (get_fresh_oid h1)
       (Heap_OBJ cls_def
          (init_field_map (find_fields cls_def) empty_field_map) lb2 lb2)) o1 = Some (Heap_OBJ cls2 F1 lb ll) ).
  apply extend_heap_lookup_eq; auto. 

  destruct (oid_decision (get_fresh_oid h2) o2 ).
   assert (lookup_heap_obj h2 (get_fresh_oid h2)  = None). 
   apply fresh_oid_heap with ct; auto.  rewrite e in H22.
   rewrite H22 in H18; inversion H18.  
   
   assert ( lookup_heap_obj
     (add_heap_obj h2 (get_fresh_oid h2)
       (Heap_OBJ cls_def
          (init_field_map (find_fields cls_def) empty_field_map) lb2 lb2)) o2 = Some (Heap_OBJ cls2 F2 lb ll) ).
   apply extend_heap_lookup_eq; auto.
   eauto using object_equal_H.

   assert ( lookup_heap_obj
     (add_heap_obj h1 (get_fresh_oid h1)
       (Heap_OBJ cls_def
          (init_field_map (find_fields cls_def) empty_field_map) lb2 lb2)) o1 = Some (Heap_OBJ cls1 F1 lb ll) ).
   apply extend_heap_lookup_eq; auto.

   assert ( lookup_heap_obj
     (add_heap_obj h2 (get_fresh_oid h2)
       (Heap_OBJ cls_def
          (init_field_map (find_fields cls_def) empty_field_map) lb2 lb2)) o2 = Some (Heap_OBJ cls2 F2 lb ll) ).
   apply extend_heap_lookup_eq; auto.
   eauto using fresh_oid_heap.    
   apply object_equal_L with lb cls1 cls2 F1 F2 ll; auto.

   destruct H21. destruct H24. destruct H25. 
   split; auto. split; auto.  
   split; auto.    
   intros.
   destruct H26 with fname fo1 fo2; auto. rename x into cls_f1.
   destruct H29 as [cls_f2].
   destruct H29 as [lof1].    destruct H29 as [lof2].
   destruct H29 as [FF1].    destruct H29 as [FF2].
   destruct H29 as [llf1].    destruct H29 as [llf2]. 

   destruct H29. destruct H30. 
   destruct H31. destruct H31. destruct H32.   destruct H33. 
   
   exists cls_f1. exists cls_f2.
   exists lof1. exists lof2.
   exists FF1. exists FF2.
   exists llf1. exists llf2.  
   split; auto. 
   apply extend_heap_lookup_eq; auto.
   eauto using lookup_extend_heap_fresh_oid. 
   split; auto. 
   apply extend_heap_lookup_eq; auto.
   eauto using lookup_extend_heap_fresh_oid. 
   assert (fo1 <> get_fresh_oid h1  ).
   eauto using lookup_extend_heap_fresh_oid.
   assert (left (extend_bijection φ (get_fresh_oid h1) (get_fresh_oid h2) H4 H5)  fo1 = 
           left φ fo1) by (apply left_extend_bijection_neq; auto).
   left. split; auto. 
   rewrite H36; auto.




   exists cls_f1. exists cls_f2.
   exists lof1. exists lof2.
   exists FF1. exists FF2.
   exists llf1. exists llf2.  
   split; auto. 
   apply extend_heap_lookup_eq; auto.
   eauto using lookup_extend_heap_fresh_oid.
   split; auto. 
   apply extend_heap_lookup_eq; auto.
   eauto using lookup_extend_heap_fresh_oid.    
   
   intros. subst; auto.  destruct (oid_decision (get_fresh_oid h1) o). subst; auto.
   unfold  lookup_heap_obj in H14. unfold add_heap_obj in H14.
   
   rewrite H12 in H14. inversion H14.
   remember (extend_bijection φ (get_fresh_oid h1) (get_fresh_oid h2) H4 H5) as φ'.
   rewrite   Heqφ'.
   assert (left (extend_bijection φ (get_fresh_oid h1) (get_fresh_oid h2) H4 H5)  o = 
           left φ o) by (apply left_extend_bijection_neq; auto).
   assert ( lookup_heap_obj h1 o = None) by (apply lookup_extended_heap_none with
                                                 (Heap_OBJ cls_def (init_field_map (find_fields cls_def)
                                                                                   empty_field_map) lb2 lb2) ; auto).
   rewrite H15.  apply H7 in H16. auto.
   rewrite   Heqh2'. intros. subst. 
   destruct (oid_decision (get_fresh_oid h2) o). subst; auto.
   unfold  lookup_heap_obj in H14. unfold add_heap_obj in H14.
   rewrite H13 in H14. inversion H14.

   assert (right (extend_bijection φ (get_fresh_oid h1) (get_fresh_oid h2) H4 H5)  o = 
           right φ o). (apply right_extend_bijection_neq; auto).
   assert ( lookup_heap_obj h2 o = None) by (apply lookup_extended_heap_none with
                                                 (Heap_OBJ cls_def (init_field_map (find_fields cls_def)
                                                                                   empty_field_map) lb2 lb2) ; auto).
   rewrite H15. apply H8 in H16. auto.
   intros.
   destruct (oid_decision o3 o). subst; auto. simpl in H14.
   rewrite H12 in H14. inversion H14. subst; auto.

   assert (flow_to (join_label ll ll) L_Label = true).
   apply join_L_label_flow_to_L; auto.
   try (inconsist).

   subst; auto. 
   unfold lookup_heap_obj in H14. unfold add_heap_obj in H14.
   assert (o <> get_fresh_oid h1) by (auto). apply  beq_oid_not_equal in H16. rewrite H16 in H14.
   fold lookup_heap_obj in H14. apply H9 in H14.
   assert (left (extend_bijection φ (get_fresh_oid h1) (get_fresh_oid h2) H4 H5)  o = 
           left φ o) by (apply left_extend_bijection_neq; auto). rewrite H17; auto. auto. 


   intros.
   destruct (oid_decision o4 o). subst; auto. simpl in H14.
   rewrite H13 in H14. inversion H14. subst; auto.
   assert (flow_to (join_label ll ll) L_Label = true).
   apply join_L_label_flow_to_L; auto.
   try (inconsist).
   
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
  | L_eq_ctn : forall t1 t2 lb sf1 sf2 h1 h2 fs1 fs2 φ,
      flow_to lb L_Label = true ->
      L_equivalence_tm t1 h1 t2 h2 φ->
      L_equivalence_fs fs1 h1 fs2 h2 φ ->
      L_equivalence_store sf1 h1 sf2 h2 φ ->
    L_eq_container (Container t1 fs1 lb sf1) h1 (Container t2 fs2 lb sf2) h2 φ.
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
  | L_equivalence_config_L : forall ct t1 fs1 lb sf1 t2 fs2 sf2 ctns1 ctns2 h1 h2 φ, 
      flow_to lb L_Label = true ->
      L_eq_container  (Container t1 fs1 lb sf1) h1 (Container t2 fs2 lb sf2) h2 φ->
      L_eq_ctns ctns1 h1 ctns2 h2 φ ->
      L_equivalence_config (Config ct (Container t1 fs1 lb sf1) ctns1 h1) (Config ct (Container t2 fs2 lb sf2) ctns2 h2)  φ
  | L_equivalence_config_H : forall ct t1 fs1 lb1 sf1 t2 fs2 lb2 sf2 ctns1 ctns2 h1 h2  φ, 
      flow_to lb1 L_Label = false ->
      flow_to lb2 L_Label = false ->
       L_equivalence_config (low_component ct (Container t1 fs1 lb1 sf1) ctns1 h1)
      (low_component ct (Container t2 fs2 lb2 sf2) ctns2 h2) φ  ->
      L_equivalence_config (Config ct (Container t1 fs1 lb1 sf1) ctns1 h1) (Config ct (Container t2 fs2 lb2 sf2) ctns2 h2)  φ.  
Hint Constructors L_equivalence_config.


Lemma value_L_eq : forall e v h1 h2  φ, 
  value v ->
  L_equivalence_tm e h1 v h2  φ ->
  value e.
Proof. intros. generalize dependent e. 
       induction v; subst; inversion H; auto;
         intros;  inversion H0; subst; auto.
       inversion H3; subst. auto. auto.
       inversion H4; subst; auto.       
Qed. Hint Resolve       value_L_eq .  

Lemma value_L_eq2 : forall e v h1 h2  φ, 
  value v ->
  L_equivalence_tm v h1 e h2  φ ->
  value e.
Proof. intros. generalize dependent e.
       induction v; subst; inversion H; auto;
         intros;  inversion H0; subst; auto.
       inversion H3; subst; auto.
       inversion H4; subst; auto.       
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

Lemma lookup_extended_heap : forall h o cls F lb ct ho ll,
  wfe_heap ct h ->  
  lookup_heap_obj h o =  Some (Heap_OBJ cls F lb ll) ->
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


  

Lemma cls_def_eq : forall o o0 cls fields lx cls0 fields0 lx0 h1' h2'  φ llx llx0,
    Some (Heap_OBJ cls fields lx llx) = lookup_heap_obj h1' o ->
    Some (Heap_OBJ cls0 fields0 lx0 llx0) = lookup_heap_obj h2' o0 ->
    bijection.left φ o = Some o0 ->
    L_equivalence_heap h1' h2' φ ->
    cls = cls0.
Proof with eauto.
  intros. inversion H2; subst; auto.
  apply H3 in H1. inversion H1; subst; auto;
  rewrite <- H8 in H;  inversion H; subst; auto;
    rewrite <- H9 in H0;  inversion H0; subst; auto.
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

  case_eq ((surface_syntax body1 && assignment_free body1)%bool); intro;
  rewrite H1 in H2.
  apply andb_true_iff  in H1. destruct H1.
  apply   IHbody1 in H1.  apply  IHbody2 in H2. auto.
  inversion H2.   
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
  apply L_equivalence_tm_eq_object_L with cls1 F1 lo cls2 F2 ll; auto.
  
  assert (left (extend_bijection φ o o' H1 H2)  o1 = 
          left φ o1).
  apply left_extend_bijection_neq; auto.
  intro contra. subst; auto. rewrite H in H1. inversion H1. 
  rewrite H5. auto.
  eauto using L_equivalence_tm_eq_object_H. 
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
  inversion H; subst;auto.
  apply L_equivalence_store_L; auto.
  split; auto. destruct H0.
  intros.
  assert (L_equivalence_tm v1 h1 v2 h2 φ).
  apply H0 with x; auto.
  apply extend_bijection_preserve_tm_eq ; auto.
  destruct H0; auto. 
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
                                     (Heap_OBJ cls_def (init_field_map (find_fields cls_def) empty_field_map) lb2 lb2))
                    t2 (add_heap_obj h2 (get_fresh_oid h2)
                      (Heap_OBJ  cls_def (init_field_map (find_fields cls_def) empty_field_map) lb2 lb2)) φ').
Proof.
  intros t1 h1  t2 h2  lb2 cls_def ct φ φ' H1 H2.
  intros.
  generalize dependent t2. 
  induction t1; intros; inversion H3; subst; auto.

  apply L_equivalence_tm_eq_object_L with cls1 F1 lo cls2 F2 ll; auto.
  assert (left (extend_bijection φ ( get_fresh_oid h1) ( get_fresh_oid h2) H1 H2)  o = 
          left φ o).
  apply left_extend_bijection_neq; auto.
  intro contra. subst; auto. rewrite H7 in H1. inversion H1. 
  rewrite H5. auto.
  assert (o <> get_fresh_oid h1).
  eauto using lookup_extend_heap_fresh_oid. 
  apply beq_oid_not_equal in H5; auto.
  unfold lookup_heap_obj. unfold add_heap_obj.
  rewrite H5. fold lookup_heap_obj. auto.

  assert (o2 <> get_fresh_oid h2).
  eauto using lookup_extend_heap_fresh_oid. 
  apply beq_oid_not_equal in H5; auto.
  unfold lookup_heap_obj. unfold add_heap_obj.
  rewrite H5. fold lookup_heap_obj. auto.

  apply L_equivalence_tm_eq_object_H with cls1 cls2  F1 lo1 F2 lo2 ll1 ll2 ; auto.

  assert (o <> get_fresh_oid h1).
  eauto using lookup_extend_heap_fresh_oid. 
  apply beq_oid_not_equal in H5; auto.
  unfold lookup_heap_obj. unfold add_heap_obj.
  rewrite H5. fold lookup_heap_obj. auto.

  assert (o2 <> get_fresh_oid h2).
  eauto using lookup_extend_heap_fresh_oid. 
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
                                     (Heap_OBJ  cls_def (init_field_map (find_fields cls_def) empty_field_map) lb2 lb2))
                    fs2 (add_heap_obj h2 (get_fresh_oid h2)
                      (Heap_OBJ  cls_def (init_field_map (find_fields cls_def) empty_field_map) lb2 lb2)) φ').
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
                                     (Heap_OBJ  cls_def (init_field_map (find_fields cls_def) empty_field_map) lb2 lb2))
                    sf2 (add_heap_obj h2 (get_fresh_oid h2)
                      (Heap_OBJ  cls_def (init_field_map (find_fields cls_def) empty_field_map) lb2 lb2)) φ').
Proof.
  intros sf1 h1  sf2 h2  lb2 cls_def ct φ φ' H1 H2.
  intros.
  inversion H4; subst; auto.
  inversion H3; subst; auto. 
  apply L_equivalence_store_L; auto.
  intros. destruct H7.
  split; auto. intros. 
  assert (L_equivalence_tm v1 h1 v2 h2 φ).
  apply H7 with x; auto.  
  apply extend_heap_preserve_L_eq_tm with ct φ H1 H2; auto.
  
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
                                     (Heap_OBJ  cls_def (init_field_map (find_fields cls_def) empty_field_map) lb lb))
                    ctn2 (add_heap_obj h2 (get_fresh_oid h2)
                      (Heap_OBJ  cls_def (init_field_map (find_fields cls_def) empty_field_map) lb lb)) φ').
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
                                     (Heap_OBJ  cls_def (init_field_map (find_fields cls_def) empty_field_map) lb2 lb2))
                    ctns2 (add_heap_obj h2 (get_fresh_oid h2)
                      (Heap_OBJ  cls_def (init_field_map (find_fields cls_def) empty_field_map) lb2 lb2)) φ').
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
   inversion H0; subst; auto. unfold low_component. rewrite H1; auto.
   try (inconsist).
Qed.
Hint Resolve low_component_irrelevant.

Lemma update_field_preserve_L_eq_tm {DecOid : forall a1 a2 : oid, Decision (a1 = a2)} :
  forall  (φ:bijection oid oid) h1 h2 ct cls F lo o lb1 lx
          cls0 F0 lo0 o0 lb2 lx0 t1 t2 v v0 f0 ll ll0,
  wfe_heap ct h2 ->  wfe_heap ct h1 -> 
  L_equivalence_heap h1 h2 φ ->
  L_equivalence_tm t1 h1 t2 h2 φ ->
  Some (Heap_OBJ cls F lo ll) = lookup_heap_obj h1 o ->
  flow_to (join_label lb1 lx) (join_label lo ll)  = true ->
  Some (Heap_OBJ cls0 F0 lo0 ll0) = lookup_heap_obj h2 o0 ->
  flow_to (join_label lb2 lx0) (join_label lo0 ll0) = true ->
  L_equivalence_tm (ObjId o) h1 (ObjId o0) h2 φ ->
  L_equivalence_tm (v_opa_l v lx) h1 (v_opa_l v0 lx0) h2 φ ->
  flow_to lb1 L_Label = true ->
  flow_to lb2 L_Label = true ->
  value v ->
  value v0 ->
  L_equivalence_tm t1 (update_heap_obj h1 o (Heap_OBJ cls (fields_update F f0 v) lo ll))
                    t2 (update_heap_obj h2 o0 (Heap_OBJ cls0 (fields_update F0 f0 v0) lo0 ll0)) φ.
Proof with eauto. 
  intros φ h1 h2 ct cls F lo o lb1 lx cls0 F0 lo0 o0 lb2 lx0 t1 t2 v v0 f0 ll ll0.
  intros.
  
  inversion H8; subst; auto.
  assert ( flow_to (join_label lb1 lx0) L_Label = true).
  apply join_L_label_flow_to_L; auto.
  (* apply L_Label_flow_to_L in H13. rewrite H13 in H4. *) 

  assert ( flow_to (join_label lb2 lx0) L_Label = true).
  apply join_L_label_flow_to_L; auto.
(*  apply L_Label_flow_to_L in H14. rewrite H14 in H6.  *)

  generalize dependent t2;  
    induction t1; intros;     inversion H2; subst; auto.  

  + 
    case_eq (beq_oid o1 o); intro.
    ++
  apply beq_oid_equal in H15.
  remember (update_heap_obj h1 o (Heap_OBJ cls (fields_update F f0 v) lo ll))  as h'.
  assert (Some  (Heap_OBJ cls (fields_update F f0 v) lo ll) = lookup_heap_obj h' o).
  apply lookup_updated with h1 (Heap_OBJ cls1 F1 lo1 ll1); rewrite <- H15; subst;  auto.
  case_eq (beq_oid o3 o0); intro.
  +++
  apply beq_oid_equal in H25.
  remember (update_heap_obj h2 o0 (Heap_OBJ cls0 (fields_update F0 f0 v0) lo0 ll0))  as h2'.
  assert (Some   (Heap_OBJ cls0 (fields_update F0 f0 v0) lo0 ll0)  = lookup_heap_obj h2' o0).
  apply lookup_updated with h2 (Heap_OBJ cls2 F2 lo1 ll1) ; rewrite <- H25; subst;  auto.
  inversion H7; subst; auto. 
  apply L_equivalence_tm_eq_object_L with cls (fields_update F f0 v) lo cls0
                                          (fields_update F0 f0 v0) ll; subst; auto.
  try (rewrite_lookup).
  try (rewrite_lookup).
  rewrite <- H3 in H18; inversion H18; subst; auto.
  rewrite <- H21 in H33; inversion H33; subst; auto. 
  try (rewrite_lookup).
  try (rewrite_lookup).
  +++ 
  subst; auto.
  apply L_equivalence_tm_eq_object_L with cls (fields_update F f0 v) lo cls2
                                          F2 ll; subst; auto.
  try (rewrite_lookup).
  rewrite <- H3 in H18; inversion H18; subst; auto.

  remember (update_heap_obj h2 o0 (Heap_OBJ cls0 (fields_update F0 f0 v0) lo0 ll0))  as h2'.
  assert (Some (Heap_OBJ cls2 F2 lo ll) = lookup_heap_obj h2' o3).
  apply lookup_updated_not_affected with  o0 (Heap_OBJ cls0 (fields_update F0 f0 v0) lo0 ll0) h2; auto.
  intro contra. rewrite contra in H25. pose proof (beq_oid_same o0).
  try (inconsist). auto. 

  ++
    case_eq (beq_oid o3 o0); intro.
  +++  
    apply beq_oid_equal in H24.
    remember (update_heap_obj h2 o0 (Heap_OBJ cls0 (fields_update F0 f0 v0) lo0 ll1))  as h2'.
    assert (Some   (Heap_OBJ cls0 (fields_update F0 f0 v0) lo0 ll1)  = lookup_heap_obj h2' o0).
    apply lookup_updated with h2 (Heap_OBJ cls2 F2 lo1 ll1) ; rewrite <- H24; subst;  auto.
    inversion H7; subst; auto.
    ++++ 
    apply L_equivalence_tm_eq_object_L with cls1 F1 lo1 cls0
                                            (fields_update F0 f0 v0) ll1; subst; auto.
    apply lookup_updated_not_affected with o (Heap_OBJ cls (fields_update F f0 v) lo ll) h1  ; auto.
    intro contra. subst; auto.
    assert (beq_oid o o =true). apply beq_oid_same. try (inconsist).
    rewrite <- H5 in H32; inversion H32; subst; auto.
    rewrite <- H3 in H29; inversion H29; subst; auto. 
    
    try (rewrite_lookup).

    ++++
      rewrite <- H3 in H28; inversion H28; subst; auto.
      rewrite <- H5 in H29; inversion H29; subst; auto. 
      rewrite <- H5 in H21; inversion H21; subst; auto. try (inconsist).
  +++       
    remember (update_heap_obj h2 o0 (Heap_OBJ cls0 (fields_update F0 f0 v0) lo0 ll0))  as h2'.
    assert (Some (Heap_OBJ cls2 F2 lo1 ll1) = lookup_heap_obj h2' o3).
    apply lookup_updated_not_affected with  o0 (Heap_OBJ cls0 (fields_update F0 f0 v0) lo0 ll0) h2; auto.
    intro contra.
    try (beq_oid_inconsist).

    remember (update_heap_obj h1 o (Heap_OBJ cls (fields_update F f0 v) lo ll))  as h'.
    assert (Some (Heap_OBJ cls1 F1 lo1 ll1) = lookup_heap_obj h' o1).
    apply lookup_updated_not_affected with o (Heap_OBJ cls (fields_update F f0 v) lo ll) h1; auto.
    intro contra.
    try (beq_oid_inconsist).
    
    apply L_equivalence_tm_eq_object_L with cls1 F1 lo1 cls2
                                          F2 ll1; subst; auto.
  +
    case_eq (beq_oid o1 o); intro.
    ++
    apply beq_oid_equal in H15. rewrite H15 in H16.
    rewrite <- H16 in H3; inversion H3; subst; auto. 
    remember (update_heap_obj h1 o (Heap_OBJ cls1 (fields_update F1 f0 v) lo1 ll1))  as h'.
    assert (Some (Heap_OBJ cls1 (fields_update F1 f0 v) lo1 ll1) = lookup_heap_obj h' o).
    apply lookup_updated with h1 (Heap_OBJ cls1 F1 lo1 ll1); auto. 
    case_eq (beq_oid o3 o0); intro.
    +++ 
      apply beq_oid_equal in H24.
      remember (update_heap_obj h2 o0 (Heap_OBJ cls0 (fields_update F0 f0 v0) lo0 ll0))  as h2'.
      assert (Some   (Heap_OBJ cls0 (fields_update F0 f0 v0) lo0 ll0)  = lookup_heap_obj h2' o0).
      apply lookup_updated with h2 (Heap_OBJ cls2 F2 lo2 ll2) ; rewrite <- H24; subst;  auto.
      
      apply L_equivalence_tm_eq_object_H with cls1 cls0 (fields_update F1 f0 v) lo1
                                          (fields_update F0 f0 v0) lo0 ll1 ll2; subst; auto.
      try (rewrite_lookup).
    +++      
      remember (update_heap_obj h2 o0 (Heap_OBJ cls0 (fields_update F0 f0 v0) lo0 ll0))  as h2'.
      assert (Some (Heap_OBJ cls2 F2 lo2 ll2) = lookup_heap_obj h2' o3).
      apply lookup_updated_not_affected with  o0 (Heap_OBJ cls0 (fields_update F0 f0 v0) lo0 ll0) h2; auto.
      intro contra.  try (beq_oid_inconsist).
      eauto using L_equivalence_tm_eq_object_H. 
    ++
      remember ((update_heap_obj h1 o (Heap_OBJ cls (fields_update F f0 v) lo ll)))  as h'.
      assert (  Some (Heap_OBJ cls1 F1 lo1 ll1)  = lookup_heap_obj h' o1).
      apply lookup_updated_not_affected with  o (Heap_OBJ cls (fields_update F f0 v) lo ll) h1; auto.
      intro contra.
      try (beq_oid_inconsist).
      case_eq (beq_oid o3 o0); intro.
      +++
       apply beq_oid_equal in H25.
       rewrite H25 in H18. rewrite <- H18 in H5; inversion H5; subst; auto.
       remember ((update_heap_obj h2 o0 (Heap_OBJ cls2 (fields_update F2 f0 v0) lo2 ll2)))  as h2'.
       assert (Some (Heap_OBJ cls2 (fields_update F2 f0 v0) lo2 ll2)  = lookup_heap_obj h2' o0).
       apply lookup_updated with h2 (Heap_OBJ cls2 F2 lo2 ll2); subst;  auto.
       eauto using L_equivalence_tm_eq_object_H. 
      +++
        remember (update_heap_obj h2 o0 (Heap_OBJ cls0 (fields_update F0 f0 v0) lo0 ll0))  as h2'.  
        assert (Some (Heap_OBJ cls2 F2 lo2 ll2) = lookup_heap_obj h2' o3).
        apply lookup_updated_not_affected with  o0 (Heap_OBJ cls0 (fields_update F0 f0 v0) lo0 ll0) h2; auto.
        intro contra;  try (beq_oid_inconsist).
         eauto using L_equivalence_tm_eq_object_H. 
  +
    assert ( flow_to (join_label lb1 lx) L_Label = false).
    apply flow_join_label with lx lb1; auto. 
    assert ( flow_to (join_label lb2 lx0) L_Label = false).
    apply flow_join_label with lx0 lb2; auto.
    
    assert (flow_to (join_label lo ll) L_Label = false).
    apply flow_transitive with (join_label lb1 lx); auto.
    assert (flow_to (join_label lo0 ll0) L_Label = false).
    apply flow_transitive with (join_label lb2 lx0); auto.

    generalize dependent t2.  
    induction t1; intros;inversion H2; subst; auto.
    ++ 
      case_eq (beq_oid o1 o); intro.
      +++ 
      apply beq_oid_equal in H18.
      rewrite H18 in H21. rewrite <- H21 in H3; inversion H3; subst; auto.
      case_eq (beq_oid o3 o0); intro.
      ++++
        remember ( (update_heap_obj h1 o (Heap_OBJ cls1 (fields_update F1 f0 v) lo1 ll1)))  as h1'.  
        assert (Some (Heap_OBJ cls1 (fields_update F1 f0 v) lo1 ll1)  = lookup_heap_obj h1' o).
        apply lookup_updated with h1 (Heap_OBJ cls1 F1 lo1 ll1);  auto.
        apply beq_oid_equal in H18.
        rewrite H18 in H25. rewrite <- H25 in H5; inversion H5;  auto.        

        remember (update_heap_obj h2 o0 (Heap_OBJ cls2 (fields_update F2 f0 v0) lo1 ll1))  as h2'.  
        assert (Some (Heap_OBJ cls2 (fields_update F2 f0 v0) lo1 ll1)  = lookup_heap_obj h2' o0).
        apply lookup_updated with h2 (Heap_OBJ cls2 F2 lo1 ll1);  auto.
        apply L_equivalence_tm_eq_object_L with cls1  (fields_update F1 f0 v) lo1 cls2
                                                  (fields_update F2 f0 v0) ll1; subst; auto.
      ++++
        remember (update_heap_obj h2 o0 (Heap_OBJ cls0 (fields_update F0 f0 v0) lo0 ll0))  as h'.
        assert (  Some (Heap_OBJ cls2 F2 lo1 ll1)  = lookup_heap_obj h' o3).
        apply lookup_updated_not_affected with  o0 (Heap_OBJ cls0 (fields_update F0 f0 v0) lo0 ll0) h2; auto.
        intro contra.
        try (beq_oid_inconsist).

        remember ( (update_heap_obj h1 o (Heap_OBJ cls1 (fields_update F1 f0 v) lo1 ll1)))  as h1'.  
        assert (Some (Heap_OBJ cls1 (fields_update F1 f0 v) lo1 ll1)  = lookup_heap_obj h1' o).
        apply lookup_updated with h1 (Heap_OBJ cls1 F1 lo1 ll1);  auto.
        eauto using  L_equivalence_tm_eq_object_L. 

      +++
        case_eq (beq_oid o3 o0); intro.
        ++++ 
          apply beq_oid_equal in H26.
          rewrite H26 in H25.
          subst; auto. rewrite <- H25 in H5; inversion H5; subst; auto.  
          assert (Some (Heap_OBJ cls1 F1 lo1 ll1)  =
                  lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls (fields_update F f0 v) lo ll)) o1).
          apply lookup_updated_not_affected with o (Heap_OBJ cls (fields_update F f0 v) lo ll) h1; auto.
          intro contra; try (beq_oid_inconsist).

          assert (Some  (Heap_OBJ cls2 (fields_update F2 f0 v0) lo1 ll1) =
                  lookup_heap_obj (update_heap_obj h2 o0 (Heap_OBJ cls2 (fields_update F2 f0 v0) lo1 ll1)) o0).          
          eauto using lookup_updated. 
          eauto using  L_equivalence_tm_eq_object_L. 
        ++++
          assert (Some (Heap_OBJ cls1 F1 lo1 ll1)  =
                  lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls (fields_update F f0 v) lo ll)) o1).
          apply lookup_updated_not_affected with o (Heap_OBJ cls (fields_update F f0 v) lo ll) h1; auto.
          intro contra; try (beq_oid_inconsist).

          assert (Some (Heap_OBJ cls2 F2 lo1 ll1)  =
                  lookup_heap_obj (update_heap_obj h2 o0 (Heap_OBJ cls0 (fields_update F0 f0 v0) lo0 ll0)) o3).
          apply lookup_updated_not_affected with o0 (Heap_OBJ cls0 (fields_update F0 f0 v0) lo0 ll0) h2; auto.
          intro contra; try (beq_oid_inconsist).
          eauto using L_equivalence_tm_eq_object_L . 
          
    ++
        case_eq (beq_oid o1 o); intro.
        +++ 
          apply beq_oid_equal in H18.
          remember (update_heap_obj h1 o (Heap_OBJ cls (fields_update F f0 v) lo ll))  as h'.
          assert (Some  (Heap_OBJ cls (fields_update F f0 v) lo ll) = lookup_heap_obj h' o).
          apply lookup_updated with h1 (Heap_OBJ cls1 F1 lo1 ll1) ; rewrite <- H18; subst;  auto.
          case_eq (beq_oid o3 o0); intro.
          ++++ 
            apply beq_oid_equal in H27.
            subst; auto.
            rewrite <- H21 in H5; inversion H5; subst; auto. 
            rewrite <- H20 in H3; inversion H3; subst; auto.
            remember (update_heap_obj h2 o0 (Heap_OBJ cls2 (fields_update F2 f0 v0) lo2 ll2))  as h2'.
            assert (Some (Heap_OBJ cls2 (fields_update F2 f0 v0) lo2 ll2)  = lookup_heap_obj h2' o0).
            apply lookup_updated with h2  (Heap_OBJ cls2 F2 lo2 ll2) ;  subst;  auto.
            eauto using L_equivalence_tm_eq_object_H .
            ++++ 
              subst; auto.
              rewrite <- H20 in H3; inversion H3; subst; auto.
              remember (update_heap_obj h2 o0 (Heap_OBJ cls0 (fields_update F0 f0 v0) lo0 ll0))  as h2'.
              assert (Some (Heap_OBJ cls2 F2 lo2 ll2)  = lookup_heap_obj h2' o3).
              apply lookup_updated_not_affected with  o0 (Heap_OBJ cls0 (fields_update F0 f0 v0) lo0 ll0) h2; auto.
              intro contra. rewrite contra in H27. pose proof (beq_oid_same o0).
              try (inconsist).
              eauto using L_equivalence_tm_eq_object_H .
        +++
          remember ((update_heap_obj h1 o (Heap_OBJ cls (fields_update F f0 v) lo ll)))  as h'.
          assert (  Some (Heap_OBJ cls1 F1 lo1 ll1)  = lookup_heap_obj h' o1).
          apply lookup_updated_not_affected with  o (Heap_OBJ cls (fields_update F f0 v) lo ll) h1; auto.
          intro contra. rewrite contra in H18. pose proof (beq_oid_same o).
          try (inconsist).
          case_eq (beq_oid o3 o0); intro.
          ++++
            apply beq_oid_equal in H27.
            subst; auto.
            rewrite <- H21 in H5; inversion H5; subst; auto.   
            remember ((update_heap_obj h2 o0 (Heap_OBJ cls2 (fields_update F2 f0 v0) lo2 ll2)))  as h2'.
            assert (Some (Heap_OBJ cls2 (fields_update F2 f0 v0) lo2 ll2)  = lookup_heap_obj h2' o0).
            apply lookup_updated with h2 (Heap_OBJ cls2 F2 lo2 ll2); subst;  auto.
            eauto using L_equivalence_tm_eq_object_H .
          ++++
            remember (update_heap_obj h2 o0 (Heap_OBJ cls0 (fields_update F0 f0 v0) lo0 ll0))  as h2'.
            assert (Some (Heap_OBJ cls2 F2 lo2 ll2) = lookup_heap_obj h2' o3).
            apply lookup_updated_not_affected with  o0 (Heap_OBJ cls0 (fields_update F0 f0 v0) lo0 ll0) h2; auto.
            intro contra.
            rewrite contra in H27. pose proof (beq_oid_same o0).
            try (inconsist).
            eauto using L_equivalence_tm_eq_object_H .
Qed.  Hint Resolve  update_field_preserve_L_eq_tm.



Lemma update_field_preserve_L_eq_fs {DecOid : forall a1 a2 : oid, Decision (a1 = a2)} :
  forall  (φ:bijection oid oid) h1 h2 ct cls F lo o lb1 lx
          cls0 F0 lo0 o0 lb2 lx0 fs1 fs2  v v0 f0 ll ll0,
  wfe_heap ct h2 ->  wfe_heap ct h1 -> 
  L_equivalence_heap h1 h2 φ ->
  L_equivalence_fs fs1 h1 fs2 h2 φ ->
  Some (Heap_OBJ cls F lo ll) = lookup_heap_obj h1 o ->
  flow_to (join_label lb1 lx) (join_label lo ll) = true ->
  Some (Heap_OBJ cls0 F0 lo0 ll0) = lookup_heap_obj h2 o0 ->
  flow_to (join_label lb2 lx0) (join_label lo0 ll0) = true ->
  L_equivalence_tm (ObjId o) h1 (ObjId o0) h2 φ ->
  L_equivalence_tm (v_opa_l v lx) h1 (v_opa_l v0 lx0) h2 φ ->
  flow_to lb1 L_Label = true ->
  flow_to lb2 L_Label = true ->
  value v ->
  value v0 ->
  L_equivalence_fs fs1 (update_heap_obj h1 o (Heap_OBJ cls (fields_update F f0 v) lo ll))
                    fs2 (update_heap_obj h2 o0 (Heap_OBJ cls0 (fields_update F0 f0 v0) lo0 ll0)) φ.
Proof with eauto. 
  intros φ h1 h2 ct cls F lo o lb1 lx cls0 F0 lo0 o0 lb2 lx0 fs1 fs2 v v0 f0 ll ll0.
  intros.
  generalize dependent fs2. 
  induction fs1; intros; inversion H2; subst; auto.
  apply  L_equal_fs; auto.
  apply update_field_preserve_L_eq_tm with ct lb1 lx lb2 lx0; auto.
  
Qed. Hint Resolve update_field_preserve_L_eq_fs.


Lemma update_field_preserve_L_eq_store {DecOid : forall a1 a2 : oid, Decision (a1 = a2)} :
  forall  (φ:bijection oid oid) h1 h2 ct cls F lo o lb1 lx
          cls0 F0 lo0 o0 lb2 lx0 sf1 sf2  v v0 f0 ll ll0,
    wfe_heap ct h2 ->  wfe_heap ct h1 ->
    wfe_stack_frame ct h1 sf1 -> wfe_stack_frame ct h2 sf2 ->
  L_equivalence_heap h1 h2 φ ->
  L_equivalence_store sf1 h1 sf2 h2 φ ->
  Some (Heap_OBJ cls F lo ll) = lookup_heap_obj h1 o ->
  flow_to  (join_label lb1 lx) (join_label lo ll) = true ->
  Some (Heap_OBJ cls0 F0 lo0 ll0) = lookup_heap_obj h2 o0 ->
  flow_to  (join_label lb2 lx0) (join_label lo0 ll0) = true ->
  L_equivalence_tm (ObjId o) h1 (ObjId o0) h2 φ ->
  L_equivalence_tm (v_opa_l v lx) h1 (v_opa_l v0 lx0) h2 φ ->
  flow_to lb1 L_Label = true ->
  flow_to lb2 L_Label = true ->
  value v ->
  value v0 ->
  L_equivalence_store sf1 (update_heap_obj h1 o (Heap_OBJ cls (fields_update F f0 v) lo ll))
                    sf2 (update_heap_obj h2 o0 (Heap_OBJ cls0 (fields_update F0 f0 v0) lo0 ll0)) φ.
Proof with eauto. 
  intros φ h1 h2 ct cls F lo o lb1 lx cls0 F0 lo0 o0 lb2 lx0 sf1 sf2 v v0 f0.
  intros.

  inversion H3; subst; auto.
  
  intros. inversion H10; subst; auto.
  inversion H4; subst; auto.
  apply L_equivalence_store_L; auto.
  intros. destruct H20.
  split; auto. intros. 
  assert (L_equivalence_tm v1 h1 v2 h2 φ).
  apply H20 with x; auto.  
  apply  update_field_preserve_L_eq_tm with ct lb1 lx0 lb2 lx0; auto. 


  inversion H4; subst; auto. 
  apply L_equivalence_store_L; auto.
  destruct H20.
  split; auto. intros. 
  assert (L_equivalence_tm v1 h1 v2 h2 φ).
  apply H20 with x; auto.  
  apply  update_field_preserve_L_eq_tm with ct lb1 lx lb2 lx0; auto. 
Qed. 
Hint Resolve update_field_preserve_L_eq_store.




Lemma update_field_preserve_L_eq_ctn {DecOid : forall a1 a2 : oid, Decision (a1 = a2)} :
  forall  (φ:bijection oid oid) h1 h2 ct cls F lo o lb1 lx
          cls0 F0 lo0 o0 lb2 lx0 ctn1 ctn2 v v0 f0 ll ll0,
  wfe_heap ct h2 ->  wfe_heap ct h1 -> 
  L_equivalence_heap h1 h2 φ ->
  L_eq_container ctn1 h1 ctn2 h2 φ ->
  Some (Heap_OBJ cls F lo ll) = lookup_heap_obj h1 o ->
  flow_to (join_label lb1 lx) (join_label lo ll)  = true ->
  Some (Heap_OBJ cls0 F0 lo0 ll0) = lookup_heap_obj h2 o0 ->
  flow_to (join_label lb2 lx0) (join_label lo0 ll0) = true ->
  L_equivalence_tm (ObjId o) h1 (ObjId o0) h2 φ ->
  L_equivalence_tm (v_opa_l v lx) h1 (v_opa_l v0 lx0) h2 φ ->
  flow_to lb1 L_Label = true ->
  flow_to lb2 L_Label = true ->
  value v ->
  value v0 ->
  valid_ctn ct ctn1 h1 ->   valid_ctn ct ctn2 h2 ->
  L_eq_container ctn1 (update_heap_obj h1 o (Heap_OBJ cls (fields_update F f0 v) lo ll))
                    ctn2 (update_heap_obj h2 o0 (Heap_OBJ cls0 (fields_update F0 f0 v0) lo0 ll0)) φ.
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
          cls0 F0 lo0 o0 lb2 lx0 ctns1 ctns2 v v0 f0 ll ll0,
  wfe_heap ct h2 ->  wfe_heap ct h1 -> 
  L_equivalence_heap h1 h2 φ ->
  L_eq_ctns ctns1 h1 ctns2 h2 φ ->
  Some (Heap_OBJ cls F lo ll) = lookup_heap_obj h1 o ->
  flow_to  (join_label lb1 lx) (join_label lo ll) = true ->
  Some (Heap_OBJ cls0 F0 lo0 ll0) = lookup_heap_obj h2 o0 ->
  flow_to (join_label lb2 lx0) (join_label lo0 ll0) = true ->
  L_equivalence_tm (ObjId o) h1 (ObjId o0) h2 φ ->
  L_equivalence_tm (v_opa_l v lx) h1 (v_opa_l v0 lx0) h2 φ ->
  flow_to lb1 L_Label = true ->
  flow_to lb2 L_Label = true ->
  value v ->
  value v0 ->
  valid_ctns ct ctns1 h1 ->   valid_ctns ct ctns2 h2 ->
  L_eq_ctns ctns1 (update_heap_obj h1 o (Heap_OBJ cls (fields_update F f0 v) lo ll))
                    ctns2 (update_heap_obj h2 o0 (Heap_OBJ cls0 (fields_update F0 f0 v0) lo0 ll0)) φ.
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
                                   (Heap_OBJ cls F lo lo)) h2 φ.
Proof with eauto.
  intros.
  inversion H0; subst; auto.
  apply L_eq_heap; auto.
  - intros. apply H2 in H7. inversion H7; subst; auto.
    apply object_equal_H with lb cls2 cls2 F1 F2 ll; auto.

    assert (lookup_heap_obj (add_heap_obj h1 (get_fresh_oid h1)
                                   (Heap_OBJ cls F lo lo)) o1 = Some (Heap_OBJ cls2 F1 lb ll)).
    apply extend_heap_lookup_eq; auto.
    eauto using lookup_extend_heap_fresh_oid. auto. 

    destruct H12. destruct H13. destruct H14.
    apply object_equal_L with lb cls1 cls2 F1 F2 ll; auto.
    assert (lookup_heap_obj (add_heap_obj h1 (get_fresh_oid h1)
                                   (Heap_OBJ cls F lo lo)) o1 = Some (Heap_OBJ cls1 F1 lb ll)).
    apply extend_heap_lookup_eq; auto.
    eauto using lookup_extend_heap_fresh_oid. auto.

    split; auto. split; auto. split; auto.
    intros.
    destruct H15 with fname fo1 fo2; auto.
    destruct H18 as [cls_f2]. rename x into cls_f1.
    destruct H18 as [lof1]. destruct H18 as [lof2].
    destruct H18 as [FF1]. destruct H18 as [FF2].
    destruct H18 as [llf1]. destruct H18 as [llf2].
    destruct H18; auto.
    destruct H19. 
    exists cls_f1.     exists cls_f2.
    exists lof1. exists lof2.
    exists FF1. exists FF2.
    exists llf1. exists llf2.
    split; auto.
    apply extend_heap_lookup_eq; auto.
    eauto using lookup_extend_heap_fresh_oid.  
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
                                   (Heap_OBJ cls F lo lo)) φ.
Proof with eauto.
  intros.
  inversion H0; subst; auto.
  apply L_eq_heap; auto.
  - intros. apply H2 in H7. inversion H7; subst; auto.
    apply object_equal_H with lb cls2 cls2 F1 F2 ll; auto.
    assert (lookup_heap_obj (add_heap_obj h2 (get_fresh_oid h2)
                                   (Heap_OBJ cls F lo lo)) o2 = Some (Heap_OBJ cls2 F2 lb ll)).
    apply extend_heap_lookup_eq; auto.
    eauto using lookup_extend_heap_fresh_oid. auto. 

    apply object_equal_L with lb cls1 cls2 F1 F2 ll; auto.
    assert (lookup_heap_obj (add_heap_obj h2 (get_fresh_oid h2)
                                   (Heap_OBJ cls F lo lo)) o2 = Some (Heap_OBJ cls2 F2 lb ll)).
    apply extend_heap_lookup_eq; auto.
    eauto using lookup_extend_heap_fresh_oid. auto.
    
    destruct H12. destruct H13.   destruct H14. 
    split; auto. split; auto. split; auto.
    intros.
    destruct H15 with fname fo1 fo2; auto.
    destruct H18 as [cls_f2]. rename x into cls_f1.
    destruct H18 as [lof1]. destruct H18 as [lof2].
    destruct H18 as [FF1]. destruct H18 as [FF2].
    destruct H18 as [llf1].  destruct H18 as [llf2]. 
    destruct H18; auto.
    destruct H19. 
    exists cls_f1.     exists cls_f2.
    exists lof1. exists lof2.
    exists FF1. exists FF2.
    exists llf1. exists llf2. 
    split; auto. split; auto. 
    apply extend_heap_lookup_eq; auto.
    eauto using lookup_extend_heap_fresh_oid.
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
     L_equivalence_tm t1 (add_heap_obj h1 (get_fresh_oid h1) (Heap_OBJ cls F lo lo)) t2 h2 φ.
Proof with eauto.
  intros.
  generalize dependent t2. 
  induction t1; intros; inversion H1; subst; auto.
  apply L_equivalence_tm_eq_object_L with cls1 F1 lo0 cls2 F2 ll; auto.
  assert (lookup_heap_obj (add_heap_obj h1 (get_fresh_oid h1)
                                   (Heap_OBJ cls F lo lo)) o = Some (Heap_OBJ cls1 F1 lo0 ll)).
  apply extend_heap_lookup_eq; auto.
  eauto using lookup_extend_heap_fresh_oid .
  auto.

  apply L_equivalence_tm_eq_object_H with cls1 cls2 F1 lo1  F2 lo2 ll1 ll2; auto.
  assert (lookup_heap_obj (add_heap_obj h1 (get_fresh_oid h1)
                                   (Heap_OBJ cls F lo lo)) o = Some (Heap_OBJ cls1 F1 lo1 ll1)).
  apply extend_heap_lookup_eq; auto.
  eauto using lookup_extend_heap_fresh_oid .
  auto.
Qed. Hint Resolve extend_h1_with_H_preserve_tm_eq.   


Lemma extend_h2_with_H_preserve_tm_eq : forall t1 t2 ct h1 h2 φ cls lo F,
     wfe_heap ct h2 ->
     flow_to lo L_Label = false ->
     L_equivalence_tm t1 h1 t2 h2 φ ->
     L_equivalence_tm t1 h1  t2 (add_heap_obj h2 (get_fresh_oid h2) (Heap_OBJ cls F lo lo)) φ.
Proof with eauto.
  intros.
  generalize dependent t2. 
  induction t1; intros; inversion H1; subst; auto.
  apply L_equivalence_tm_eq_object_L with cls1 F1 lo0 cls2 F2 ll; auto.
  assert (lookup_heap_obj (add_heap_obj h2 (get_fresh_oid h2)
                                   (Heap_OBJ cls F lo lo)) o2 = Some (Heap_OBJ cls2 F2 lo0 ll)).
  apply extend_heap_lookup_eq; auto.
  eauto using lookup_extend_heap_fresh_oid .
  auto.


  apply L_equivalence_tm_eq_object_H with cls1 cls2 F1 lo1  F2 lo2 ll1 ll2; auto.
  assert (lookup_heap_obj (add_heap_obj h2 (get_fresh_oid h2)
                                   (Heap_OBJ cls F lo lo)) o2 = Some (Heap_OBJ cls2 F2 lo2 ll2)).
  apply extend_heap_lookup_eq; auto.
  eauto using lookup_extend_heap_fresh_oid .
  auto.
Qed. Hint Resolve extend_h2_with_H_preserve_tm_eq.   


Lemma extend_h1_with_H_preserve_fs_eq : forall fs1 fs2 ct h1 h2 φ cls lo F,
     wfe_heap ct h1 ->
     flow_to lo L_Label = false ->
     L_equivalence_fs fs1 h1 fs2 h2 φ ->
     L_equivalence_fs fs1 (add_heap_obj h1 (get_fresh_oid h1) (Heap_OBJ cls F lo lo)) fs2 h2 φ.
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
     L_equivalence_fs fs1 h1 fs2 (add_heap_obj h2 (get_fresh_oid h2) (Heap_OBJ cls F lo lo)) φ.
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
     L_equivalence_store sf1 (add_heap_obj h1 (get_fresh_oid h1) (Heap_OBJ cls F lo lo)) sf2 h2 φ.
Proof with eauto.
  intros.
  inversion H1; subst; auto.
  inversion H2; subst; auto.
  inversion H4; subst; auto. 
  
  apply  L_equivalence_store_L; auto.
  intros. destruct H7.
  split; auto. intros. 
  assert (L_equivalence_tm v1 h1 v2 h2 φ).
  apply H7 with x; auto.  
 
  apply extend_h1_with_H_preserve_tm_eq with ct ; auto. 
 Qed. Hint Resolve extend_h1_with_H_preserve_sf_eq.


Lemma extend_h2_with_H_preserve_sf_eq : forall sf1 sf2 ct h1 h2 φ cls lo F,
    wfe_heap ct h1 ->
    wfe_heap ct h2 ->
    wfe_stack_frame ct h1 sf1 ->
    wfe_stack_frame ct h2 sf2 ->
     flow_to lo L_Label = false ->
     L_equivalence_store sf1 h1 sf2 h2 φ ->
     L_equivalence_store sf1 h1 sf2 (add_heap_obj h2 (get_fresh_oid h2) (Heap_OBJ cls F lo lo)) φ.
Proof with eauto.
  intros.
  inversion H1; subst; auto.
  inversion H2; subst; auto.
  inversion H4; subst; auto.
  apply  L_equivalence_store_L; auto.
  intros. destruct H7.
  split; auto. intros. 
  assert (L_equivalence_tm v1 h1 v2 h2 φ).
  apply H7 with x; auto.  
  apply extend_h2_with_H_preserve_tm_eq with ct ; auto. 
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
    (add_heap_obj h1 (get_fresh_oid h1) (Heap_OBJ cls F lo lo))  
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
                   (add_heap_obj h2 (get_fresh_oid h2) (Heap_OBJ cls F lo lo))   φ.
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
    L_eq_ctns  ctns1 (add_heap_obj h1 (get_fresh_oid h1) (Heap_OBJ cls F lo lo))
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
     ctns2  (add_heap_obj h2 (get_fresh_oid h2) (Heap_OBJ cls F lo lo))  φ.
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
    (Config ct ctn1 ctns1 (add_heap_obj h1 (get_fresh_oid h1) (Heap_OBJ cls F lo lo)))
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

  apply L_eq_ctn; auto.
  apply L_equivalence_store_L; auto.
  split; auto; intros.  inversion H6.
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
  
  assert (Config ct (Container t f l1 s) l (add_heap_obj h1 (get_fresh_oid h1) (Heap_OBJ cls F lo lo))
          = (low_component ct (Container t1 fs1 lb1 sf1) (a :: ctns3)
                          (add_heap_obj h1 (get_fresh_oid h1) (Heap_OBJ cls F lo lo)))
         ).
  eauto using low_component_irrelevant_to_heap.

  rewrite <- H8.
  inversion H5; subst; auto.  inversion H37; subst; auto.
  apply   L_equivalence_config_L; auto.
  apply extend_h1_with_H_preserve_ctn_eq with ct; auto.
  apply H6. 
  apply H7.
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
    (Config ct ctn2 ctns2  (add_heap_obj h2 (get_fresh_oid h2) (Heap_OBJ cls F lo lo))) φ.
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

  +  
  apply L_eq_ctn; auto.
  apply L_equivalence_store_L; auto.
  split; auto; intros.  inversion H6.
  split; auto.  
     

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
                    (add_heap_obj h2 (get_fresh_oid h2) (Heap_OBJ cls F lo lo))
          = (low_component ct (Container t2 fs2 lb2 sf2) (a :: ctns0)
                          (add_heap_obj h2 (get_fresh_oid h2) (Heap_OBJ cls F lo lo)))
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
     inversion H5; subst; auto.      
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

     unfold low_component.  rewrite H2. 
     unfold low_component in H5. rewrite H2 in H5.
     inversion H5; subst; auto.      
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

     inversion H5.
     inversion H5. 
     
     
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
                 (add_heap_obj h2 (get_fresh_oid h2) (Heap_OBJ cls F lo lo))
          = (low_component ct (Container t2 fs2 lb2 sf2) ctns0
                          (add_heap_obj h2 (get_fresh_oid h2) (Heap_OBJ cls F lo lo)))
         ).
  eauto using low_component_irrelevant_to_heap. rewrite <- H8.
  inversion H5; subst; auto. inversion H37; subst; auto.    
  apply   L_equivalence_config_L; auto.  
  apply extend_h2_with_H_preserve_ctn_eq with ct; auto.
  apply H6.
  apply H7.
  apply extend_h2_with_H_preserve_ctns_eq with ct; auto.
  apply H6.
  apply H7.
  try (inconsist_label).
  inversion H5; subst; auto.
  inversion H5.  inversion H5.  inversion H5.  
Qed. Hint Resolve  extend_h2_with_H_preserve_config_eq.



Lemma update_h1_with_H_preserve_bijection : forall ct h1 h2 φ cls lo F f v o lb1
  lx ll,
    wfe_heap ct h1 ->
    L_equivalence_heap h1 h2 φ ->
    Some (Heap_OBJ cls F lo ll) = lookup_heap_obj h1 o ->
    flow_to (join_label lb1 lx) (join_label lo ll) = true ->
    flow_to lb1 L_Label = false ->
    L_equivalence_heap
    (update_heap_obj h1 o (Heap_OBJ cls (fields_update F f v) lo ll)) h2 φ.
    
Proof with eauto.
  intros. 
  assert ( flow_to (join_label lb1 lx) L_Label = false).
  apply flow_join_label with lb1 lx; auto.
  apply  join_label_commutative; auto.
  
  inversion H0; subst; auto.
  apply L_eq_heap; auto.
  - intros. apply H5 in H10. inversion H10; subst; auto.
    + 
    case_eq (beq_oid o1 o); intro.
    ++ apply beq_oid_equal in H15.
      rewrite H15 in H11. rewrite <- H11 in H1; inversion H1; subst.
      assert ( Some (Heap_OBJ cls2 (fields_update F1 f v) lb ll0) = 
               lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls2 (fields_update F1 f v) lb ll0)) o).
      eauto using lookup_updated.
      apply object_equal_H with lb cls2 cls2 (fields_update F1 f v) F2 ll0; auto.

    ++
      assert ( Some (Heap_OBJ cls2 F1 lb ll0)  = 
               lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls (fields_update F f v) lo ll)) o1).
      apply lookup_updated_not_affected with o (Heap_OBJ cls (fields_update F f v) lo ll) h1 ; auto.
      intro contra. try (beq_oid_inconsist).
      eauto using object_equal_H. 
    +
      case_eq (beq_oid o1 o); intro.
      ++ apply beq_oid_equal in H16.
      rewrite H16 in H11; rewrite <- H11 in H1; inversion H1; subst.

      assert (flow_to (join_label lb1 lx) (join_label lb ll0) = false).
      apply flow_no_H_to_L; auto.
      apply  join_L_label_flow_to_L; auto.
      try (inconsist).

      ++
        assert ( Some (Heap_OBJ cls1 F1 lb ll0)  = 
               lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls (fields_update F f v) lo ll)) o1).
        apply lookup_updated_not_affected with o (Heap_OBJ cls (fields_update F f v) lo ll) h1 ; auto.
        intro contra. try (beq_oid_inconsist).
        apply object_equal_L with lb cls1 cls2 F1 F2 ll0; auto.
        
        destruct H15.
        destruct H18.
        destruct H19.
        split; auto.
        split; auto.
        split; auto.
        
        intros. 
        destruct H20 with fname fo1 fo2; auto.
        destruct H23 as [cls_f2]. rename x into cls_f1.
        destruct H23 as [lof1]. destruct H23 as [lof2].
        destruct H23 as [FF1]. destruct H23 as [FF2].
        destruct H23 as [llf1].  destruct H23 as [llf2].
        
        destruct H23; auto.
        destruct H24. 
    
        case_eq (beq_oid fo1 o); intro.
        +++ 
          apply beq_oid_equal in H26; subst; auto.
          assert (Some (Heap_OBJ cls (fields_update F f v) lo ll)
            = lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls (fields_update F f v) lo ll)) o).
          eauto using lookup_updated; auto.
          destruct H25.
          ++++
            destruct H25.  destruct H26. destruct H27. rewrite H23 in H1; inversion H1; subst; auto. 
            exists cls_f1. exists cls_f2.
            exists lof2. exists lof2.
            exists (fields_update FF1 f v). exists FF2.
            exists llf1. exists llf2.   

            split; auto. 
            split; auto.

          ++++
            rewrite H23 in H1; inversion H1; subst; auto.
            destruct H25.  destruct H26.

            exists cls_f1. exists cls_f2.
            exists lof1. exists lof2.
            exists (fields_update FF1 f v). exists FF2.
            exists llf1. exists llf2.   
            split; auto.

        +++
          exists cls_f1. exists cls_f2.
          exists lof1. exists lof2.
          exists FF1. exists FF2.
          exists llf1. exists llf2.   
          split; auto.
          assert ( Some   (Heap_OBJ cls_f1 FF1 lof1 llf1)
                   = lookup_heap_obj
                       (update_heap_obj h1 o (Heap_OBJ cls (fields_update F f v) lo ll)) fo1).
          apply lookup_updated_not_affected with o (Heap_OBJ cls (fields_update F f v) lo ll) h1; auto.
          intro contra. try (beq_oid_inconsist). auto. 
    
  - intros.
    apply lookup_updated_heap_must_none in H10.
    auto. 
  - intros. 
    case_eq (beq_oid o0 o); intro.
    + 
      apply beq_oid_equal in H12; subst; auto.
      apply H8 with cls F lo ll; auto . 
      assert (Some (Heap_OBJ cls (fields_update F f v) lo ll)
            = lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls (fields_update F f v) lo ll)) o).
      eauto using lookup_updated; auto.
      rewrite <- H12 in H10; inversion H10; subst; auto.
    + assert (Some (Heap_OBJ cls0 F0 lb ll0) = lookup_heap_obj h1 o0).
    apply lookup_updated_not_affected_reverse
      with o (Heap_OBJ cls (fields_update F f v) lo ll)
           (update_heap_obj h1 o (Heap_OBJ cls (fields_update F f v) lo ll)); auto.
    intro contra. rewrite contra in H12.
    assert (beq_oid o o = true). apply beq_oid_same.
    rewrite H12 in H13. inversion H13.
    apply H8 with cls0 F0 lb ll0; auto.  
Qed. Hint Resolve  update_h1_with_H_preserve_bijection.   


Lemma update_h2_with_H_preserve_bijection : forall ct h1 h2 φ cls lo F f v o lb1
  lx ll,
    wfe_heap ct h1 ->
    L_equivalence_heap h1 h2 φ ->
    Some (Heap_OBJ cls F lo ll) = lookup_heap_obj h2 o ->
    flow_to (join_label lb1 lx) (join_label lo ll) = true ->
    flow_to lb1 L_Label = false ->
    L_equivalence_heap h1
    (update_heap_obj h2 o (Heap_OBJ cls (fields_update F f v) lo ll)) φ.
    
Proof with eauto.
intros. 
  assert ( flow_to (join_label lb1 lx) L_Label = false).
  apply flow_join_label with lb1 lx; auto.
  apply  join_label_commutative; auto.
  
  inversion H0; subst; auto.
  apply L_eq_heap; auto.
  - intros. apply H5 in H10. inversion H10; subst; auto.
    + 
    case_eq (beq_oid o2 o); intro.
    ++ apply beq_oid_equal in H15.
      rewrite H15 in H12. rewrite <- H12 in H1; inversion H1; subst.
      assert ( Some (Heap_OBJ cls2 (fields_update F2 f v) lb ll0) = 
               lookup_heap_obj (update_heap_obj h2 o (Heap_OBJ cls2 (fields_update F2 f v) lb ll0)) o).
      eauto using lookup_updated.
      eauto using object_equal_H.
    ++
      assert ( Some (Heap_OBJ cls2 F2 lb ll0)  = 
               lookup_heap_obj (update_heap_obj h2 o (Heap_OBJ cls (fields_update F f v) lo ll)) o2).
      apply lookup_updated_not_affected with o (Heap_OBJ cls (fields_update F f v) lo ll) h2 ; auto.
      intro contra. try (beq_oid_inconsist).
      eauto using object_equal_H. 
    +
      case_eq (beq_oid o2 o); intro.
      ++ apply beq_oid_equal in H16.
      rewrite H16 in H12; rewrite <- H12 in H1; inversion H1; subst.

      assert (flow_to (join_label lb1 lx) (join_label lb ll0) = false).
      apply flow_no_H_to_L; auto.
      apply  join_L_label_flow_to_L; auto.
      try (inconsist).

      ++
        assert ( Some (Heap_OBJ cls2 F2 lb ll0)  = 
               lookup_heap_obj (update_heap_obj h2 o (Heap_OBJ cls (fields_update F f v) lo ll)) o2).
        apply lookup_updated_not_affected with o (Heap_OBJ cls (fields_update F f v) lo ll) h2 ; auto.
        intro contra. try (beq_oid_inconsist).
        apply object_equal_L with lb cls1 cls2 F1 F2 ll0; auto.
        
        destruct H15.
        destruct H18.
        destruct H19.
        split; auto.
        split; auto.
        split; auto.
        
        intros. 
        destruct H20 with fname fo1 fo2; auto.
        destruct H23 as [cls_f2]. rename x into cls_f1.
        destruct H23 as [lof1]. destruct H23 as [lof2].
        destruct H23 as [FF1]. destruct H23 as [FF2].
        destruct H23 as [llf1]. destruct H23 as [llf2].
        
        destruct H23; auto.
        destruct H24. 
    
        case_eq (beq_oid fo2 o); intro.
        +++ 
          apply beq_oid_equal in H26; subst; auto.
          assert (Some (Heap_OBJ cls (fields_update F f v) lo ll)
            = lookup_heap_obj (update_heap_obj h2 o (Heap_OBJ cls (fields_update F f v) lo ll)) o).
          eauto using lookup_updated; auto.
          destruct H25.
          ++++
            destruct H25.  destruct H26. destruct H27.
            rewrite H24 in H1; inversion H1; subst; auto. 
            exists cls_f1. exists cls_f2.
            exists lof2. exists lof2.
            exists FF1. exists (fields_update FF2 f v). 
            exists llf1. exists llf2.   

            split; auto. 
            split; auto.

          ++++
            rewrite H24 in H1; inversion H1; subst; auto.
            destruct H25.  destruct H26.

            exists cls_f1. exists cls_f2.
            exists lof1. exists lof2.
            exists FF1. exists (fields_update FF2 f v).
            exists llf1. exists llf2.  
            split; auto.

        +++
          exists cls_f1. exists cls_f2.
          exists lof1. exists lof2.
          exists FF1. exists FF2.
          exists llf1. exists llf2.   
          split; auto.
          assert ( Some   (Heap_OBJ cls_f2 FF2 lof2 llf2)
                   = lookup_heap_obj
                       (update_heap_obj h2 o (Heap_OBJ cls (fields_update F f v) lo ll)) fo2).
          apply lookup_updated_not_affected with o (Heap_OBJ cls (fields_update F f v) lo ll) h2; auto.
          intro contra. try (beq_oid_inconsist). auto. 
    
  - intros.
    apply lookup_updated_heap_must_none in H10.
    auto. 
  - intros. 
    case_eq (beq_oid o0 o); intro.
    + 
      apply beq_oid_equal in H12; subst; auto.
      apply H9 with cls F lo ll; auto . 
      assert (Some (Heap_OBJ cls (fields_update F f v) lo ll)
            = lookup_heap_obj (update_heap_obj h2 o (Heap_OBJ cls (fields_update F f v) lo ll)) o).
      eauto using lookup_updated; auto.
      rewrite <- H12 in H10; inversion H10; subst; auto.
    + assert (Some (Heap_OBJ cls0 F0 lb ll0) = lookup_heap_obj h2 o0).
      apply lookup_updated_not_affected_reverse
      with o (Heap_OBJ cls (fields_update F f v) lo ll)
           (update_heap_obj h2 o (Heap_OBJ cls (fields_update F f v) lo ll)); auto.
      intro contra. rewrite contra in H12.
      assert (beq_oid o o = true). apply beq_oid_same.
      rewrite H12 in H13. inversion H13.
      apply H9 with cls0 F0 lb ll0; auto.   
Qed. Hint Resolve  update_h2_with_H_preserve_bijection.   






Lemma update_field_h1_preserve_L_eq_tm  :
  forall  φ h1 h2 ct cls F lo o lb1 lx
          t1 t2 v f ll,
  wfe_heap ct h2 ->  wfe_heap ct h1 -> 
  L_equivalence_heap h1 h2 φ ->
  L_equivalence_tm t1 h1 t2 h2 φ ->
  Some (Heap_OBJ cls F lo ll) = lookup_heap_obj h1 o ->
  flow_to (join_label lb1 lx)  (join_label lo ll) = true ->
  flow_to lb1 L_Label = false ->
  value v ->
  (*tm_has_type ct gamma h1 ((FieldWrite (ObjId o) f (unlabelOpaque (v_opa_l v lx)))) T ->*)
  L_equivalence_tm t1 (update_heap_obj h1 o (Heap_OBJ cls (fields_update F f v) lo ll))
                    t2 h2 φ.
Proof with eauto. 
  intros φ h1 h2 ct cls F lo o lb1 lx t1 t2 v f ll.
  intros.
  assert ( flow_to (join_label lb1 lx) L_Label = false).
  apply flow_join_label with lb1 lx; auto.
  apply  join_label_commutative; auto.

  
  assert (flow_to (join_label lo ll)  L_Label = false).
  apply flow_transitive with (join_label lb1 lx); auto. 

  generalize dependent t2.  
  induction t1; intros;inversion H2; subst; auto.

  + case_eq (beq_oid o0 o); intro.
    ++
      apply beq_oid_equal in H9. subst; auto.
      rewrite <- H11 in H3; inversion H3; subst; auto.
      apply L_equivalence_tm_eq_object_L  with cls1 (fields_update F1 f v)  lo0 cls2 F2 ll0; subst; auto.
      eauto using lookup_updated.
    ++
      apply L_equivalence_tm_eq_object_L  with cls1 F1 lo0 cls2 F2 ll0; subst; auto.
      apply lookup_updated_not_affected with o (Heap_OBJ cls (fields_update F f v) lo ll) h1; auto.
      intro contra. try (beq_oid_inconsist).


  +
    case_eq (beq_oid o0 o); intro.
    ++
    apply beq_oid_equal in H9. subst; auto.
    rewrite <- H10 in H3; inversion H3; subst; auto. 
    apply L_equivalence_tm_eq_object_H  with cls1 cls2 (fields_update F1 f v) lo1  F2 lo2 ll1 ll2; subst; auto.
    apply lookup_updated with h1 ((Heap_OBJ cls1 F1 lo1 ll1) ); auto.
    ++
    apply L_equivalence_tm_eq_object_H  with cls1 cls2  F1 lo1  F2 lo2 ll1 ll2; subst; auto.
    apply lookup_updated_not_affected with o (Heap_OBJ cls (fields_update F f v) lo ll) h1; auto.
    intro contra.  rewrite contra in H9. pose proof (beq_oid_same o).
    try (inconsist).
Qed. Hint Resolve   update_field_h1_preserve_L_eq_tm.


Lemma update_field_h2_preserve_L_eq_tm  :
  forall  φ h1 h2 ct cls F lo o lb1 lx
          t1 t2 v f ll,
  wfe_heap ct h2 ->  wfe_heap ct h1 -> 
  L_equivalence_heap h1 h2 φ ->
  L_equivalence_tm t1 h1 t2 h2 φ ->
  Some (Heap_OBJ cls F lo ll) = lookup_heap_obj h2 o ->
  flow_to (join_label lb1 lx) (join_label lo ll)   = true ->
  flow_to lb1 L_Label = false ->
  value v ->
  L_equivalence_tm t1 h1
                    t2 (update_heap_obj h2 o (Heap_OBJ cls (fields_update F f v) lo ll)) φ.
Proof with eauto. 
  intros φ h1 h2 ct cls F lo o lb1 lx t1 t2 v f ll.
  intros.
  assert ( flow_to (join_label lb1 lx) L_Label = false).
  apply flow_join_label with lb1 lx; auto.
  apply  join_label_commutative; auto.

  assert (flow_to (join_label lo ll) L_Label = false).
  apply flow_transitive with (join_label lb1 lx); auto. 

  generalize dependent t2.  
  induction t1; intros;inversion H2; subst; auto.

  + case_eq (beq_oid o2 o); intro.
    ++
      apply beq_oid_equal in H9. subst; auto.
      rewrite <- H13 in H3; inversion H3; subst; auto.
      apply L_equivalence_tm_eq_object_L  with cls1 F1  lo0 cls2 (fields_update F2 f v) ll0; subst; auto.
      eauto using lookup_updated.
    ++
      apply L_equivalence_tm_eq_object_L  with cls1 F1 lo0 cls2 F2 ll0; subst; auto.
      apply lookup_updated_not_affected with o (Heap_OBJ cls (fields_update F f v) lo ll) h2; auto.
      intro contra. try (beq_oid_inconsist).

  +
    case_eq (beq_oid o2 o); intro.
    ++
    apply beq_oid_equal in H9. subst; auto.
    rewrite <- H11 in H3; inversion H3; subst; auto. 
    apply L_equivalence_tm_eq_object_H  with cls1 cls2 F1 lo1 (fields_update F2 f v)  lo2 ll1 ll2; subst; auto.
    eauto using lookup_updated.
    ++
    apply L_equivalence_tm_eq_object_H  with cls1 cls2  F1 lo1  F2 lo2 ll1 ll2; subst; auto.
    apply lookup_updated_not_affected with o (Heap_OBJ cls (fields_update F f v) lo ll) h2; auto.
    intro contra.  rewrite contra in H9. pose proof (beq_oid_same o).
    try (inconsist).
Qed. Hint Resolve   update_field_h2_preserve_L_eq_tm.


Lemma update_field_h1_preserve_L_eq_fs  :
  forall  φ h1 h2 ct cls F lo o lb1 lx
          fs1 fs2 v f ll,
  wfe_heap ct h2 ->  wfe_heap ct h1 -> 
  L_equivalence_heap h1 h2 φ ->
  L_equivalence_fs fs1 h1 fs2 h2 φ ->
  Some (Heap_OBJ cls F lo ll) = lookup_heap_obj h1 o ->
  flow_to (join_label lb1 lx) (join_label lo ll)  = true ->
  flow_to lb1 L_Label = false ->
  value v ->
  L_equivalence_fs fs1 (update_heap_obj h1 o (Heap_OBJ cls (fields_update F f v) lo ll))
                    fs2 h2 φ.
Proof with eauto. 
  intros φ h1 h2 ct cls F lo o lb1 lx fs1 fs2 v f ll.
  intros.
  generalize dependent fs2.
  induction fs1; intros; inversion H2; subst; auto.

  apply L_equal_fs; auto.
  apply update_field_h1_preserve_L_eq_tm with ct lb1 lx; auto.
Qed. Hint Resolve update_field_h1_preserve_L_eq_fs.


Lemma update_field_h2_preserve_L_eq_fs :
  forall  φ h1 h2 ct cls F lo o lb1 lx
          fs1 fs2 v f ll,
  wfe_heap ct h2 ->  wfe_heap ct h1 -> 
  L_equivalence_heap h1 h2 φ ->
  L_equivalence_fs fs1 h1 fs2 h2 φ ->
  Some (Heap_OBJ cls F lo ll) = lookup_heap_obj h2 o ->
  flow_to (join_label lb1 lx) (join_label lo ll) = true ->
  flow_to lb1 L_Label = false ->
  value v ->
  L_equivalence_fs fs1 h1
                    fs2 (update_heap_obj h2 o (Heap_OBJ cls (fields_update F f v) lo ll)) φ.
Proof with eauto. 
  intros φ h1 h2 ct cls F lo o lb1 lx fs1 fs2 v f ll.
  intros.
  generalize dependent fs2.
  induction fs1; intros; inversion H2; subst; auto.

  apply L_equal_fs; auto.
  apply update_field_h2_preserve_L_eq_tm with ct lb1 lx; auto.
Qed. Hint Resolve update_field_h2_preserve_L_eq_fs.


Lemma update_field_h1_preserve_L_eq_store :
  forall  φ h1 h2 ct cls F lo o lb1 lx
          sf1 sf2 v f ll,
  wfe_heap ct h2 ->  wfe_heap ct h1 -> 
  L_equivalence_heap h1 h2 φ ->
  L_equivalence_store sf1 h1 sf2 h2 φ ->
  Some (Heap_OBJ cls F lo ll) = lookup_heap_obj h1 o ->
  flow_to (join_label lb1 lx) (join_label lo ll) = true ->
  flow_to lb1 L_Label = false ->
  value v ->
  L_equivalence_store sf1 (update_heap_obj h1 o (Heap_OBJ cls (fields_update F f v) lo ll))
                    sf2 h2 φ.
Proof with eauto.
  intros  φ h1 h2 ct cls F lo o lb1 lx
          sf1 sf2 v f ll.
  intros.
  assert ( flow_to (join_label lb1 lx) L_Label = false).
  apply flow_join_label with lb1 lx; auto.
  apply  join_label_commutative; auto.

  assert (flow_to (join_label lo ll) L_Label = false).
  apply flow_transitive with (join_label lb1 lx); auto. 

  inversion H2; subst; auto. 
  apply L_equivalence_store_L; auto.
  destruct H9.
  split; auto; intros.
  apply update_field_h1_preserve_L_eq_tm with ct lb1 lx; auto.
  apply  H9 with x; auto. 
Qed. Hint Resolve update_field_h1_preserve_L_eq_store.



Lemma update_field_h2_preserve_L_eq_store  :
  forall  φ h1 h2 ct cls F lo o lb1 lx
          sf1 sf2 v f ll,
  wfe_heap ct h2 ->  wfe_heap ct h1 -> 
  L_equivalence_heap h1 h2 φ ->
  L_equivalence_store sf1 h1 sf2 h2 φ ->
  Some (Heap_OBJ cls F lo ll) = lookup_heap_obj h2 o ->
  flow_to (join_label lb1 lx) (join_label lo ll) = true ->
  flow_to lb1 L_Label = false ->
  value v ->
  L_equivalence_store sf1 h1
                    sf2 (update_heap_obj h2 o (Heap_OBJ cls (fields_update F f v) lo ll)) φ.
Proof with eauto.
  intros  φ h1 h2 ct cls F lo o lb1 lx
          sf1 sf2 v f ll.
  intros.
  assert ( flow_to (join_label lb1 lx) L_Label = false).
  apply flow_join_label with lb1 lx; auto.
  apply  join_label_commutative; auto.

  assert (flow_to (join_label lo ll) L_Label = false).
  apply flow_transitive with (join_label lb1 lx); auto. 

  inversion H2; subst; auto. 
  apply L_equivalence_store_L; auto.
  intros.
  destruct H9; auto.
  split; auto.
  intros.
  apply update_field_h2_preserve_L_eq_tm with ct lb1 lx; auto.
  apply H9 with x; auto. 
Qed. Hint Resolve update_field_h2_preserve_L_eq_store.
    



Lemma update_field_h1_preserve_L_eq_ctn :
  forall  φ h1 h2 ct cls F lo o lb1 lx
          ctn1 ctn2 v f ll,
   wfe_heap ct h2 ->  wfe_heap ct h1 -> 
  L_equivalence_heap h1 h2 φ ->
  L_eq_container ctn1 h1 ctn2 h2 φ ->
  Some (Heap_OBJ cls F lo ll) = lookup_heap_obj h1 o ->
  flow_to  (join_label lb1 lx) (join_label lo ll) = true ->
  flow_to lb1 L_Label = false ->
  value v ->
  L_eq_container ctn1 (update_heap_obj h1 o (Heap_OBJ cls (fields_update F f v) lo ll))
                    ctn2 h2 φ.
Proof with eauto. 
  intros φ h1 h2 ct cls F lo o lb1 lx ctn1 ctn2 v f ll.
  intros.
  generalize dependent ctn2.
  induction ctn1; intros; inversion H2; subst; auto.
  apply  L_eq_ctn; auto.
  apply update_field_h1_preserve_L_eq_tm with ct lb1 lx; auto.
  apply update_field_h1_preserve_L_eq_fs with ct lb1 lx; auto.
  apply update_field_h1_preserve_L_eq_store with ct lb1 lx; auto.
Qed. Hint Resolve update_field_h1_preserve_L_eq_ctn. 



Lemma update_field_h2_preserve_L_eq_ctn:
  forall  φ h1 h2 ct cls F lo o lb1 lx
          ctn1 ctn2 v f ll,
   wfe_heap ct h2 ->  wfe_heap ct h1 -> 
  L_equivalence_heap h1 h2 φ ->
  L_eq_container ctn1 h1 ctn2 h2 φ ->
  Some (Heap_OBJ cls F lo ll) = lookup_heap_obj h2 o ->
  flow_to (join_label lb1 lx) (join_label lo ll) = true ->
  flow_to lb1 L_Label = false ->
  value v ->
  L_eq_container ctn1 h1
                    ctn2 (update_heap_obj h2 o (Heap_OBJ cls (fields_update F f v) lo ll)) φ.
Proof with eauto. 
  intros φ h1 h2 ct cls F lo o lb1 lx ctn1 ctn2 v f ll.
  intros.
  generalize dependent ctn2.
  induction ctn1; intros; inversion H2; subst; auto.
  apply  L_eq_ctn; auto.
  apply update_field_h2_preserve_L_eq_tm with ct lb1 lx; auto.
  apply update_field_h2_preserve_L_eq_fs with ct lb1 lx; auto.
  apply update_field_h2_preserve_L_eq_store with ct lb1 lx; auto.
Qed. Hint Resolve update_field_h2_preserve_L_eq_ctn.

  

Lemma update_field_h1_preserve_L_eq_ctns :
  forall  φ h1 h2 ct cls F lo o lb1 lx
          ctns1 ctns2 v f ll ,
   wfe_heap ct h2 ->  wfe_heap ct h1 -> 
  L_equivalence_heap h1 h2 φ ->
  L_eq_ctns ctns1 h1 ctns2 h2 φ ->
  Some (Heap_OBJ cls F lo ll) = lookup_heap_obj h1 o ->
  flow_to (join_label lb1 lx) (join_label lo ll) = true ->
  flow_to lb1 L_Label = false ->
  value v ->
  L_eq_ctns ctns1 (update_heap_obj h1 o (Heap_OBJ cls (fields_update F f v) lo ll))
                    ctns2 h2 φ.
Proof with eauto. 
  intros φ h1 h2 ct cls F lo o lb1 lx ctns1 ctns2 v f ll.
  intros.
  generalize dependent ctns2.
  induction ctns1; intros; inversion H2; subst; auto.
  apply  L_eq_ctns_list; auto.
  apply update_field_h1_preserve_L_eq_ctn with ct lb1 lx; auto.
Qed. Hint Resolve update_field_h1_preserve_L_eq_ctns.


Lemma update_field_h2_preserve_L_eq_ctns :
  forall  φ h1 h2 ct cls F lo o lb1 lx
          ctns1 ctns2 v f ll ,
   wfe_heap ct h2 ->  wfe_heap ct h1 -> 
  L_equivalence_heap h1 h2 φ ->
  L_eq_ctns ctns1 h1 ctns2 h2 φ ->
  Some (Heap_OBJ cls F lo ll) = lookup_heap_obj h2 o ->
  flow_to (join_label lb1 lx) (join_label lo ll)  = true ->
  flow_to lb1 L_Label = false ->
  value v ->
  L_eq_ctns ctns1 h1
                    ctns2 (update_heap_obj h2 o (Heap_OBJ cls (fields_update F f v) lo ll)) φ.
Proof with eauto. 
  intros φ h1 h2 ct cls F lo o lb1 lx ctns1 ctns2 v f ll.
  intros.
  generalize dependent ctns1.
  induction ctns2; intros; inversion H2; subst; auto.
  apply  L_eq_ctns_list; auto.
  apply update_field_h2_preserve_L_eq_ctn with ct lb1 lx; auto.
Qed. Hint Resolve update_field_h2_preserve_L_eq_ctns.


Lemma update_field_h1_preserve_config_eq :
  forall  φ h1 h2 ct cls F lo o lb1 lx
          ctn1 ctn2 ctns1 ctns2 v f ll,
    wfe_heap ct h2 ->  wfe_heap ct h1 -> 
    L_equivalence_heap h1 h2 φ ->
    L_equivalence_config (Config ct ctn1 ctns1  h1)
                         (Config ct ctn2 ctns2  h2) φ ->

    Some (Heap_OBJ cls F lo ll) = lookup_heap_obj h1 o ->
    flow_to  (join_label lb1 lx) (join_label lo ll) = true ->
    flow_to lb1 L_Label = false ->
    value v ->
    L_equivalence_config
      (Config ct ctn1 ctns1 (update_heap_obj h1 o (Heap_OBJ cls (fields_update F f v) lo ll)))
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
  intros; inversion H9.
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
       (update_heap_obj h1 o (Heap_OBJ cls (fields_update F f v) lo ll)))
    (Config ct (Container hole nil L_Label empty_stack_frame) nil h1)  φ).
  apply L_equivalence_config_L; auto.
  apply L_eq_ctn; auto.
  apply L_equivalence_store_L; auto; intros;
    try (inversion H9).
  intros. split; auto.
  intros. inversion H9. 
  split; auto.  

  
  remember ((low_component ct a ctns0 h2)) as conf.
  destruct conf. destruct c0. 
  assert (c = ct /\ h = h2 /\ flow_to l0 L_Label = true).
  apply low_component_lead_to_L with t f0 s a 
                                     l  ctns0; auto. 
  
  destruct H10. destruct H11. subst; auto.
  inversion H8; subst; auto.
  inversion H27; subst; auto. 
  apply L_equivalence_config_L; auto.
  eauto using update_field_h1_preserve_L_eq_ctn. 
  eauto using update_field_h1_preserve_L_eq_ctns. 
  try (inconsist_label).

  inversion H8; subst;  auto. 
  inversion H8; subst;  auto.
  

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
  assert (Config ct (Container t f0 l1 s) l (update_heap_obj h1 o (Heap_OBJ cls (fields_update F f v) lo ll))
          = (low_component ct (Container t1 fs1 lb0 sf1) (a :: ctns3)
                           (update_heap_obj h1 o (Heap_OBJ cls (fields_update F f v) lo ll)))
         ).
  apply low_component_irrelevant_to_heap with h1; auto.  
  rewrite <- H9.
  inversion H8; subst; auto. 
  apply L_equivalence_config_L; auto.
  eauto using update_field_h1_preserve_L_eq_ctn. 
  eauto using update_field_h1_preserve_L_eq_ctns. 
  try (inconsist_label).
  inversion H8; subst; auto. 
  inversion H8; subst; auto.
  inversion H8; subst; auto. 
  inversion H8; subst; auto. 
Qed. Hint Resolve update_field_h1_preserve_config_eq.


Lemma update_field_h2_preserve_config_eq :
  forall  φ h1 h2 ct cls F lo o lb1 lx
          ctn1 ctn2 ctns1 ctns2 v f ll,
    wfe_heap ct h2 ->  wfe_heap ct h1 -> 
    L_equivalence_heap h1 h2 φ ->
    L_equivalence_config (Config ct ctn1 ctns1  h1)
                         (Config ct ctn2 ctns2  h2) φ ->

    Some (Heap_OBJ cls F lo ll) = lookup_heap_obj h2 o ->
    flow_to  (join_label lb1 lx) (join_label lo ll) = true ->
    flow_to lb1 L_Label = false ->
    value v ->
    L_equivalence_config
      (Config ct ctn1 ctns1 h1)
      (Config ct ctn2 ctns2  (update_heap_obj h2 o (Heap_OBJ cls (fields_update F f v) lo ll)))  φ.
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
  apply L_equivalence_store_L; auto; intros; try (empty_sf).
  split; auto.
  intros; try (empty_sf).
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
    (update_heap_obj h2 o (Heap_OBJ cls (fields_update F f v) lo ll)))  φ).
  apply L_equivalence_config_L; auto.
  apply L_eq_ctn; auto.
  apply L_equivalence_store_L; auto; intros; try (empty_sf).
  split; auto.
  intros; try (empty_sf).
  split; auto. 

  
  remember ((low_component ct a ctns0 h2)) as conf.
  destruct conf. destruct c0. 
  assert (c = ct /\ h = h2 /\ flow_to l0 L_Label = true).
  apply low_component_lead_to_L with t f0 s a 
                                     l  ctns0; auto.  
  destruct H10. destruct H11. subst; auto.

  assert (Config ct (Container t f0 l0 s) l
                 (update_heap_obj h2 o (Heap_OBJ cls (fields_update F f v) lo ll)) 
          = (low_component ct a ctns0 (update_heap_obj h2 o (Heap_OBJ cls (fields_update F f v) lo ll)))).
  apply low_component_irrelevant_to_heap with h2; auto. rewrite <- H10.

  inversion H8; subst; auto. 
  inversion H28; subst; auto. 
  apply L_equivalence_config_L; auto.
  eauto using update_field_h2_preserve_L_eq_ctn. 
  eauto using update_field_h2_preserve_L_eq_ctns. 
  try (inconsist_label).

  inversion H8; subst;  auto. 
  inversion H8; subst;  auto.

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
  assert (Config ct (Container t0 f1 l2 s0) l0 (update_heap_obj h2 o (Heap_OBJ cls (fields_update F f v) lo ll))
          = (low_component ct (Container t2 fs2 lb2 sf2)  ctns0
                           (update_heap_obj h2 o (Heap_OBJ cls (fields_update F f v) lo ll)))
         ).
  apply low_component_irrelevant_to_heap with h2; auto.  
  rewrite <- H9.
  inversion H8; subst; auto. 
  apply L_equivalence_config_L; auto.
  eauto using update_field_h2_preserve_L_eq_ctn. 
  eauto using update_field_h2_preserve_L_eq_ctns. 
  try (inconsist_label).
  inversion H8; subst; auto. 
  inversion H8; subst; auto.
  inversion H8; subst; auto. 
  inversion H8; subst; auto. 
Qed. Hint Resolve update_field_h2_preserve_config_eq.



Lemma value_of_fields : forall h o cls F lb f ct gamma T v ll,  
    wfe_heap ct h -> field_wfe_heap ct h ->
    Some (Heap_OBJ cls F lb ll) = lookup_heap_obj h o ->
    tm_has_type ct gamma h (FieldWrite (ObjId o) f v) T ->
    F f = Some null \/ exists o', F f = Some (ObjId o').
Proof.
  intros  h o cls F lb f ct gamma T v ll.
  intro H_wfe_heap. intro H_wfe_fields. 
  intro Hy. intro H_typing.  inversion H_typing. inversion H2;subst; auto. 
  destruct H17 as [F']. destruct H as [lo].  destruct H as [ll'].
  rewrite H in Hy. inversion Hy. subst.
  destruct H16 as [field_defs]. destruct H0 as [method_defs].
  rewrite <- H8 in H12. inversion H12. subst.
  inversion H_wfe_fields. subst.
  destruct H0 with o (class_def clsT field_defs method_defs) F' clsT lo method_defs field_defs ll'
                   f cls' ; auto. destruct H1.
  destruct H3. left. subst; auto. 
  destruct H3 as [o']. destruct H3 as [F0]. destruct H3 as [lx]. 
  destruct H3. destruct H3. destruct H3. destruct H3. right.
  exists o'.  subst; auto.
Qed. Hint Resolve  value_of_fields. 



(* heap bijection preservation *)
(*
Lemma update_field_preserve_bijection : forall ct h1 h2 φ cls F lo
                                                 cls0 F0 lo0
                                                 lx lx0 v v0 f0
                                                 o o0 lb1 lb2
                                                 ll ll0,
    
    (v = null \/
       (exists (o0 : oid) (cls0 : CLASS) (F0 : FieldMap) (lo0 : Label) ll0,
          v = ObjId o0 /\ Some (Heap_OBJ cls0 F0 lo0 ll0) = lookup_heap_obj h1 o0 /\ flow_to lo0 lo = true)) ->
    (v0 = null \/
        (exists (o0 : oid) (cls0 : CLASS) (F0 : FieldMap) (lo1 : Label) ll1,
           v0 = ObjId o0 /\ Some (Heap_OBJ cls0 F0 lo1 ll1) = lookup_heap_obj h2 o0 /\ flow_to lo1 lo0 = true) ) ->
    wfe_heap ct h1 -> field_wfe_heap ct h1 ->
      wfe_heap ct h2 -> field_wfe_heap ct h2 ->
      
      L_equivalence_heap h1 h2 φ ->
    Some (Heap_OBJ cls F lo ll) = lookup_heap_obj h1 o ->
    Some (Heap_OBJ cls0 F0 lo0 ll0) = lookup_heap_obj h2 o0 ->
    flow_to (join_label lb1 lx) (join_label lo ll) = true ->
    flow_to (join_label lb2 lx0) (join_label lo0 ll0) = true ->
    L_equivalence_tm (ObjId o) h1 (ObjId o0) h2 φ ->
    flow_to lb1 L_Label = true ->
    flow_to lb2 L_Label = true ->
    L_equivalence_tm (v_opa_l v lx) h1 (v_opa_l v0 lx0) h2 φ ->
    L_equivalence_heap (update_heap_obj h1 o (Heap_OBJ cls (fields_update F f0 v) lo ll))
                       (update_heap_obj h2 o0 (Heap_OBJ cls0 (fields_update F0 f0 v0) lo0 ll0)) φ.
    
Proof with eauto.
  intros ct h1 h2 φ cls F lo
         cls0 F0 lo0
         lx lx0 v v0 f0
         o o0 lb1 lb2 ll ll0.
        
  intros H_v. intro H_v0. intros.   
  inversion H8; subst; auto.
  rewrite <- H15 in H4; inversion H4; subst; auto.
  rewrite <- H19 in H5; inversion H5; subst; auto.
  inversion H11; subst; auto.
  (* opa_l has low label*)
  inversion H3; subst; auto.
  apply L_eq_heap; auto.
  
  - intros.
    assert (L_equivalence_object o1 h1 o2 h2 φ) as H_eq_o1_o2.          
    apply H12; auto. 
    inversion H_eq_o1_o2; subst; auto. 
    case_eq (beq_oid o1 o); intro.
    + 
    apply beq_oid_equal in H33.
    rewrite H33 in H25; rewrite <- H25 in H15; inversion H15; subst.
    assert ( Some  (Heap_OBJ cls0 (fields_update F0 f0 v) lb0 ll)  =
      lookup_heap_obj  (update_heap_obj h1 o (Heap_OBJ cls0 (fields_update F0 f0 v) lb0 ll))  o).
    apply lookup_updated with h1  (Heap_OBJ cls0 F0 lb0 ll); auto.

    case_eq (beq_oid o2 o0); intro.
    ++ 
    apply beq_oid_equal in H34.
    rewrite H34 in H28. rewrite <- H28 in H19; inversion H19; subst; auto.  

    assert ( Some  (Heap_OBJ cls3 (fields_update F3 f0 v0) lb3 ll)  =
      lookup_heap_obj  (update_heap_obj h2 o0 (Heap_OBJ cls3 (fields_update F3 f0 v0) lb3 ll))  o0).
    apply lookup_updated with h2  (Heap_OBJ cls3 F3 lb3 ll); auto.
    apply object_equal_L with lb3 lb3 cls0 cls3
                              (fields_update F0 f0 v)
                              (fields_update F3 f0 v0) ll; auto.
    destruct H32. destruct H35. destruct H36. destruct H37 as [tmp].
    split; auto.
    split; auto. split; auto. 
    intro. split; auto.
    intro. unfold  fields_update in H38.
    case_eq (beq_id f0 fname); intro.
    rewrite H39 in H38; inversion H38. 
    rewrite H39 in H38.  apply H36 in H38. 
    unfold  fields_update. rewrite H39. auto.

    intro. unfold  fields_update in H38.
    case_eq (beq_id f0 fname); intro.
    rewrite H39 in H38.  inversion H38.
    rewrite H39 in H38.  destruct H36 with fname.
    apply H41 in H38. 
    unfold  fields_update. rewrite H39. auto.

    split; auto.
    intro. split; auto.
    intro. unfold  fields_update in H38.
    (* case_eq (beq_id f0 fname) *)
    case_eq (beq_id f0 fname); intro.
    rewrite H39 in H38.  inversion H38.
    rewrite H41 in H27; inversion H27; auto. 
    unfold  fields_update. rewrite H39. auto.

    rewrite H39 in H38. apply tmp in H38. 
    unfold  fields_update. rewrite H39. auto.

    intro. unfold  fields_update in H38.
    case_eq (beq_id f0 fname); intro.
    rewrite H39 in H38.  inversion H38.
    rewrite H41 in H27; inversion H27; auto. 
    unfold  fields_update. rewrite H39. auto.

    rewrite H39 in H38. destruct tmp with fname.
    apply H41 in H38. 
    unfold  fields_update. rewrite H39. auto.

    intros. unfold  fields_update in H38. 
    unfold  fields_update in H39.
    case_eq (beq_id f0 fname); intro.
    rewrite H40 in H38. rewrite H40 in H39.
    inversion H38. inversion H39. 

    case_eq (beq_oid fo1 o); intro.
    apply beq_oid_equal in H41.
    rewrite <- H41 in H25. 
    assert (Some (Heap_OBJ cls0 (fields_update F0 f0 (ObjId fo1)) lb3 ll)
            = lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls0 (fields_update F0 f0 (ObjId fo1)) lb3 ll)) fo1).
    apply lookup_updated with h1 (Heap_OBJ cls0 F0 lb3 ll); auto.
    rewrite H41. auto.

    
    case_eq (beq_oid fo2 o0); intro.
    apply beq_oid_equal in H45.
    rewrite <- H45 in H28. 
    assert (Some (Heap_OBJ cls3 (fields_update F3 f0 (ObjId fo2)) lb3 ll)
            = lookup_heap_obj (update_heap_obj h2 o0 (Heap_OBJ cls3 (fields_update F3 f0 (ObjId fo2)) lb3 ll)) fo2).
    apply lookup_updated with h2 (Heap_OBJ cls3 F3 lb3 ll); auto.
    rewrite H45. auto.
    exists cls0. exists cls3. exists lb3. exists lb3.
    exists (fields_update F0 f0 (ObjId fo1)).
    exists (fields_update F3 f0 (ObjId fo2)).
    exists ll. exists ll. 
    split; auto. split; auto.
    subst; auto.
    left. split; auto. 

    (* if fo1 = o, then fo2 must be equal to o2*)
    subst; auto.
    inversion H27; subst; auto.
    rewrite H42 in H24; inversion H24; subst; auto. 
    pose proof (beq_oid_same o0).
    try (inconsist).

    assert (flow_to (join_label lb0 ll1) L_Label = true).
    apply join_L_label_flow_to_L; auto.
    try (rewrite_lookup).
    try (rewrite_lookup).
    try (inconsist).

    (* beq_oid fo1 o = false*)
    subst; auto. 
    inversion H27; subst; auto.
    +++ 
      case_eq (beq_oid fo2 o0); intro.
      ++++ 

        (* inconsist assumption *)
    apply beq_oid_equal in H32.
    subst; auto.
    apply right_left in H14.
    apply right_left in H43.
    rewrite H43 in H14.
    inversion H14; subst; auto. 
    pose proof (beq_oid_same o).
    try (inconsist).
    
      ++++
    (* beq_oid fo2 o0 = false*)
    assert (Some (Heap_OBJ cls1 F1 lo ll0) =
            lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls3 (fields_update F0 f0 (ObjId fo1)) lb3 ll)) fo1 
           ).
    apply lookup_updated_not_affected with o (Heap_OBJ cls3 (fields_update F0 f0 (ObjId fo1)) lb3 ll)  h1; auto.
    intro contra. rewrite contra in H41.
    pose proof (beq_oid_same o). try (inconsist).

    assert (Some (Heap_OBJ cls2 F2 lo ll0) =
           lookup_heap_obj (update_heap_obj h2 o0 (Heap_OBJ cls3 (fields_update F3 f0 (ObjId fo2)) lb3 ll)) fo2
           ).
    apply lookup_updated_not_affected with o0 (Heap_OBJ cls3 (fields_update F3 f0 (ObjId fo2)) lb3 ll) h2; auto.
    intro contra. rewrite contra in H32.
    pose proof (beq_oid_same o0). try (inconsist).

    exists cls1. exists cls2.
    exists lo. exists lo.
    exists F1. exists F2.
    exists ll0. exists ll0. 
    split; auto. split; auto.
    left. split; auto.   split; auto. split; auto.
    split; auto. split; auto. 
    
    apply H12 in H43; inversion H43; subst; auto.
    rewrite <- H49 in H44; inversion H44; subst; auto.
    rewrite <- H50 in H48; inversion H48; subst; auto.
    apply H54. 
    

    +++ 
    (*cannot assign H objects to L objects*)
      destruct H_v.
      ++++
        inversion H32.
      ++++
        destruct H32 as [o'].
    destruct H32 as [cls'].
    destruct H32 as [F'].
    destruct H32 as [lo'].
    destruct H32 as [ll'].
    destruct H32.
    inversion H32; subst; auto.
    destruct H42.
    rewrite <- H43 in H42; inversion H42; subst; auto.

    assert (flow_to lb0 L_Label = true).
    case_eq (flow_to lb0 L_Label); intro.
    auto. assert (flow_to lb3 L_Label = false). apply flow_transitive with lb0; auto .  try (inconsist).
    
    assert (Some (Heap_OBJ cls1 F1 lb0 ll1)
            = lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls3 (fields_update F0 f0 (ObjId o')) lb3 ll)) o').
    apply lookup_updated_not_affected with o (Heap_OBJ cls3 (fields_update F0 f0 (ObjId o')) lb3 ll) h1; auto.
    intro contra. rewrite contra in H41.
    assert (beq_oid o o = true). apply beq_oid_same. try(inconsist).
    case_eq (beq_oid fo2 o0); intro.
    +++++ apply beq_oid_equal in H50. subst; auto.
    rewrite <- H45 in H28; inversion H28; subst; auto.
    assert (flow_to (join_label lb4 ll2) L_Label = true). apply  join_L_label_flow_to_L; auto. try(inconsist).

    +++++ 
      assert (Some  (Heap_OBJ cls2 F2 lb4 ll2)
              = lookup_heap_obj (update_heap_obj h2 o0 (Heap_OBJ cls3 (fields_update F3 f0 (ObjId fo2)) lb3 ll)) fo2).
    apply lookup_updated_not_affected with o0 (Heap_OBJ cls3 (fields_update F3 f0 (ObjId fo2)) lb3 ll) h2; auto.
    intro contra. rewrite contra in H50. assert (beq_oid o0 o0 =true). apply beq_oid_same. try (inconsist).
    exists cls1. exists cls2.
    exists lb0. exists lb4.
    exists F1. exists F2.
    exists ll1. exists ll2.
    split; auto. 

    +++
    rewrite H40 in H38. rewrite H40 in H39.
    destruct H37 with fname fo1 fo2; auto.
    destruct H41 as [cls_f2]. rename x into cls_f1.
    destruct H41 as [lof1]. destruct H41 as [lof2].
    destruct H41 as [FF1]. destruct H41 as [FF2].
    destruct H41 as [llf1]. destruct H41 as [llf2].
    destruct H41. destruct H42.
    
    case_eq (beq_oid fo1 o); intro.
    ++++ 
    apply beq_oid_equal in H44.
    rewrite <- H44 in H25.
    assert (Some (Heap_OBJ cls0 (fields_update F0 f0 v) lb3 ll)
            = lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls0 (fields_update F0 f0 v) lb3 ll)) fo1).
    apply lookup_updated with h1 (Heap_OBJ cls0 F0 lb3 ll); auto.
    rewrite H44; auto.
    
    case_eq (beq_oid fo2 o0); intro.
    apply beq_oid_equal in H46.
    rewrite <- H46 in H28. 
    assert (Some (Heap_OBJ cls3 (fields_update F3 f0 v0) lb3 ll)
            = lookup_heap_obj (update_heap_obj h2 o0 (Heap_OBJ cls3 (fields_update F3 f0 v0) lb3 ll)) fo2).
    apply lookup_updated with h2 (Heap_OBJ cls3 F3 lb3 ll); auto.
    rewrite H46; auto.
    exists cls0. exists cls3.
    exists lb3. exists lb3.
    exists (fields_update F0 f0 v). exists (fields_update F3 f0 v0).
    exists ll. exists ll. 
    split; auto.
    split; auto.
    destruct H43. 
    left; split; auto.  apply H43.
    subst; auto.
    destruct H43. 
    right. rewrite H41 in H25; inversion H25; subst; auto.

    (* assert (flow_to (join_label lof1 llf1) L_Label = true). apply  join_L_label_flow_to_L; auto. try(inconsist).
     *)
    
    (* if fo1 = o, then fo2 must be equal to o2*)
    subst; auto.
    destruct H43. destruct H32. 
    rewrite  H32 in H14; inversion H14; subst; auto.
    pose proof (beq_oid_same o0).
    try (inconsist).

    destruct H32.
    rewrite H41 in H25; inversion H25; subst; auto.
    assert (flow_to (join_label lof1 llf1) L_Label = true). apply  join_L_label_flow_to_L; auto. try(inconsist).

    ++++
    (* beq_oid fo1 o = false*)
    case_eq (beq_oid fo2 o0); intro.
    
    (* inconsist assumption *)
    apply beq_oid_equal in H45.
    subst; auto.
    apply right_left in H14.
    
    destruct H43. destruct H32. 
    apply right_left in H32.
    rewrite H32 in H14.
    inversion H14; subst; auto. 
    pose proof (beq_oid_same o).
    try (inconsist).

    rewrite H42 in H28; inversion H28; subst; auto.
    destruct H32.
    assert (flow_to (join_label lof2 llf2) L_Label = true). apply  join_L_label_flow_to_L; auto. try(inconsist).    

    (* beq_oid fo2 o0 = false*)
    assert (Some (Heap_OBJ cls_f1 FF1 lof1 llf1) =
            lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls0 (fields_update F0 f0 v) lb3 ll)) fo1 
           ).
    apply lookup_updated_not_affected with o (Heap_OBJ cls0 (fields_update F0 f0 v) lb3 ll)  h1; auto.
    intro contra. rewrite contra in H44.
    pose proof (beq_oid_same o). try (inconsist).

    assert (Some  (Heap_OBJ cls_f2 FF2 lof2 llf2) =
           lookup_heap_obj (update_heap_obj h2 o0 (Heap_OBJ cls3 (fields_update F3 f0 v0) lb3 ll)) fo2
           ).
    apply lookup_updated_not_affected with o0 (Heap_OBJ cls3 (fields_update F3 f0 v0) lb3 ll) h2; auto.
    intro contra. rewrite contra in H45.
    pose proof (beq_oid_same o0). try (inconsist).

    exists  cls_f1. exists cls_f2.
    exists lof1. exists lof2.
    exists FF1. exists FF2.
    exists llf1. exists llf2. 
    split; auto.

    ++ 
    rewrite H14 in H24; inversion H24; subst; auto.
    pose proof (beq_oid_same o2).
    try (inconsist).

    +
    (*beq_oid o2 o0 = true*)
     case_eq (beq_oid o2 o0); intro.
     ++ 
       apply beq_oid_equal in H34.
       subst; auto. 
       apply right_left in H14.
       apply right_left in H24.
       rewrite H14 in H24; inversion H24; subst; auto.
       pose proof (beq_oid_same o1).
       try (inconsist).

     ++
     assert (Some  (Heap_OBJ cls0 F0 lb0 ll)  =
           lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls1 (fields_update F1 f0 v) lo1 ll1))  o1
           ).
    apply lookup_updated_not_affected with o (Heap_OBJ cls1 (fields_update F1 f0 v) lo1 ll1) h1; auto.
    intro contra. rewrite contra in H33.    pose proof (beq_oid_same o).    try (inconsist).

    assert (Some  (Heap_OBJ cls3 F3 lb3 ll)  =
           lookup_heap_obj (update_heap_obj h2 o0 (Heap_OBJ cls2 (fields_update F2 f0 v0) lo1 ll1))  o2
           ).
    apply lookup_updated_not_affected with o0  (Heap_OBJ cls2 (fields_update F2 f0 v0) lo1 ll1)  h2; auto.
    intro contra. rewrite contra in H34.    pose proof (beq_oid_same o0).    try (inconsist).
    
    apply  object_equal_L with lb0 lb3 cls0 cls3 F0 F3 ll; auto.

    destruct H32. destruct H37. destruct H38. destruct H39 as [tmp].
    split; auto. split; auto. split; auto. split; auto. 

    intros.
    destruct H39 with fname fo1 fo2; auto.
    rename x into cls_f1. destruct H42 as [cls_f2].
    destruct H42 as [lof1]. destruct H42 as [lof2].
    destruct H42 as [FF1]. destruct H42 as [FF2].
    destruct H42 as [llf1]. destruct H42 as [llf2].
    destruct H42.   destruct H43.
    
    case_eq (beq_oid fo1 o); intro.
    +++
    apply beq_oid_equal in H45.
    subst; auto.
    rewrite H14 in H44. destruct H44.
    ++++
      destruct H32. 
    inversion H32; subst; auto. 
    assert (Some (Heap_OBJ cls1 (fields_update F1 f0 v) lo1 ll1)
            = lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls1 (fields_update F1 f0 v) lo1 ll1)) o).
    apply lookup_updated with h1 (Heap_OBJ cls_f1 FF1 lof1 llf1); auto.

    assert (Some (Heap_OBJ cls2  (fields_update F2 f0 v0) lo1 ll1)
            = lookup_heap_obj (update_heap_obj h2 fo2 (Heap_OBJ cls2 (fields_update F2 f0 v0) lo1 ll1)) fo2).
    apply lookup_updated with h2 (Heap_OBJ cls_f2 FF2 lof2 llf2); auto.
    exists cls1. exists cls2.
    exists lo1. exists lo1.
    exists (fields_update F1 f0 v).
    exists (fields_update F2 f0 v0).
    exists ll1. exists ll1. 
    split; auto.
    split; auto.
    left; auto.
    split; auto.
    split; auto. split; auto. split; auto. split; auto. 
    rewrite H42 in H15; inversion H15; subst; auto.
    rewrite H43 in H19; inversion H19; subst; auto.
    apply H37. 

    ++++
    (*flow_to lof2 L_Label = false /\ flow_to lof1 L_Label = false*)
    rewrite H42 in H15; inversion H15; subst; auto.
    destruct H32.
    assert (flow_to (join_label lof1 llf1) L_Label = true).  apply  join_L_label_flow_to_L; auto. try(inconsist).    
    

    +++
    (*beq_oid fo1 o = false*)        
      case_eq (beq_oid fo2 o0); intro.
      ++++
    apply beq_oid_equal in H46.
    rewrite H46 in H44.
    destruct H44.
    destruct H44.
    apply right_left in H44.
    apply right_left in H14.
    rewrite H44 in H14; inversion H14; subst; auto.
    pose proof (beq_oid_same o).
    try (inconsist).

        (* fo2 = o0 *)
    subst; auto.
    rewrite H43 in H19; inversion H19; subst; auto.
    destruct H44.
    assert (flow_to (join_label lof2 llf2) L_Label = true). apply  join_L_label_flow_to_L; auto. try(inconsist).    

      ++++
    (* beq_oid fo2 o0 = false*)
    assert (Some (Heap_OBJ cls_f1 FF1 lof1 llf1) =
            lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls1 (fields_update F1 f0 v) lo1 ll1)) fo1
           ).
    apply lookup_updated_not_affected with o (Heap_OBJ cls1 (fields_update F1 f0 v) lo1 ll1)  h1; auto.
    intro contra. rewrite contra in H45.
    pose proof (beq_oid_same o); try (inconsist).


    subst; auto.
    assert (Some  (Heap_OBJ cls_f2 FF2 lof2 llf2) =
           lookup_heap_obj (update_heap_obj h2 o0 (Heap_OBJ cls2 (fields_update F2 f0 v0) lo1 ll1)) fo2
           ).
    apply lookup_updated_not_affected with o0 (Heap_OBJ cls2 (fields_update F2 f0 v0) lo1 ll1) h2; auto.
    subst; auto. 
    intro contra. rewrite contra in H46.
    pose proof (beq_oid_same o0). try (inconsist).

    exists cls_f1. exists cls_f2.
    exists lof1. exists lof2.
    exists FF1. exists FF2.
    exists llf1. exists llf2. 
    split; auto.

  - (* None -> left φ o1 = None *)
    intros. apply lookup_updated_heap_must_none in H24.
    apply H13 in H24. auto. 

  - (* o1 = None -> right φ o1 = None *)
    intros. apply lookup_updated_heap_must_none in H24.
    apply H18 in H24. auto.

  - (*  flow_to (join_label lb ll) L_Label = false *)
    intros.
    case_eq (beq_oid o1 o); intro.
    assert ( Some (Heap_OBJ cls F lb ll) = lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls1 (fields_update F1 f0 v) lo1 ll1)) o1 ). auto.
    apply lookup_updated_heap_new_obj in H29; auto.  
    inversion H29; subst; auto.
    assert (flow_to (join_label lo1 ll1) L_Label = true).  apply  join_L_label_flow_to_L; auto. try(inconsist).    
    
    assert (Some (Heap_OBJ cls F lb ll) =
            lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls1 (fields_update F1 f0 v) lo1 ll1)) o1
           ). auto.
    apply lookup_updated_heap_old_obj in H29; auto.
    assert ( lookup_heap_obj h1 o1 = Some (Heap_OBJ cls F lb ll) ); auto.
    apply H20 in H30; auto. 

  - (*flow_to lb L_Label = false -> right φ o1 = None *)
    intros.
    case_eq (beq_oid o1 o0); intro.
    assert ( Some (Heap_OBJ cls F lb ll) = lookup_heap_obj (update_heap_obj h2 o0 (Heap_OBJ cls2 (fields_update F2 f0 v0) lo1 ll1)) o1 ). auto.
    apply lookup_updated_heap_new_obj in H29; auto.
    inversion H29; subst; auto.
    assert (flow_to (join_label lo1 ll1) L_Label = true).  apply  join_L_label_flow_to_L; auto. try(inconsist).  
    
    assert (Some (Heap_OBJ cls F lb ll) =
            lookup_heap_obj (update_heap_obj h2 o0 (Heap_OBJ cls2 (fields_update F2 f0 v0) lo1 ll1)) o1
           ). auto.
    apply lookup_updated_heap_old_obj in H29; auto.
    assert ( lookup_heap_obj h2 o1 = Some (Heap_OBJ cls F lb ll) ); auto.
    apply H22 in H30; auto.

  - (*cannot happen *)
    assert (flow_to (join_label lb2 lx0) L_Label = false).
    apply flow_join_label with lx0 lb2; auto.
    assert (flow_to (join_label lo1 ll1) L_Label = false).
    apply flow_transitive with (join_label lb2 lx0); auto.  
    assert (flow_to (join_label lo1 ll1) L_Label = true).
    apply join_L_label_flow_to_L; auto. 
    try (inconsist_label).  

    
    
  - (* object with h label *)
    intros.
    rewrite <- H14 in H4; inversion H4; subst; auto.
    rewrite <- H16 in H5; inversion H5; subst; auto.

    inversion H3; subst; auto. 
    apply  L_eq_heap; auto.
    + intros. assert ( L_equivalence_object o1 h1 o2 h2 φ). 
      apply H12. auto.  inversion H22; subst; auto.
      case_eq (beq_oid o1 o); intro.
      (*impossible*)
      apply beq_oid_equal in H29.
      rewrite H29 in H23.
      rewrite <- H23 in H14; inversion H14; subst; auto.
      assert ( flow_to (join_label lb4 ll) L_Label = true). apply  join_L_label_flow_to_L; auto. try(inconsist).  

      case_eq (beq_oid o2 o0); intro.
      apply beq_oid_equal in H30.
      rewrite H30 in H24.
      rewrite <- H24 in H16; inversion H16; subst; auto.
      assert ( flow_to (join_label lb5 ll) L_Label = true). apply  join_L_label_flow_to_L; auto. try(inconsist).  

      assert (Some (Heap_OBJ cls0 F0 lb4 ll) =
            lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls1 (fields_update F1 f0 v) lb0 ll1)) o1
           ).
      apply lookup_updated_not_affected with o (Heap_OBJ cls1 (fields_update F1 f0 v) lb0 ll1)  h1; auto.
      intro contra. rewrite contra in H29.
      pose proof (beq_oid_same o). try (inconsist).

      assert (Some (Heap_OBJ cls3 F3 lb5 ll) =
            lookup_heap_obj (update_heap_obj h2 o0 (Heap_OBJ cls2 (fields_update F2 f0 v0) lb3 ll2)) o2
             ).
      apply lookup_updated_not_affected with o0 (Heap_OBJ cls2 (fields_update F2 f0 v0) lb3 ll2)  h2; auto.
      intro contra. rewrite contra in H30.
      pose proof (beq_oid_same o0). try (inconsist).

      apply object_equal_L with lb4 lb5 cls0 cls3 F0 F3 ll; auto.
      destruct H28. destruct H33. destruct H34. destruct H35 as [tmp]. 
      split; auto. split; auto. split; auto. split; auto. 

      intros.
      destruct H35 with fname fo1 fo2; auto.
      destruct H38 as [cls_f2]. rename x into cls_f1.
      destruct H38 as [lof1]. destruct H38 as [lof2].
      destruct H38 as [FF1]. destruct H38 as [FF2].
      destruct H38 as [llf1]. destruct H38 as [llf2].
      destruct H38.  destruct H39.

      destruct H40. destruct H40.
      assert (L_equivalence_object fo1 h1 fo2 h2 φ).
      apply H12; auto. 
      inversion H42; subst; auto.

      case_eq (beq_oid fo1 o); intro.
      apply beq_oid_equal in H28.
      rewrite H28 in H43. rewrite <- H43 in H14; inversion H14; subst; auto.
      assert ( flow_to (join_label lb6 ll0) L_Label = true). apply  join_L_label_flow_to_L; auto. try(inconsist).  
    
      case_eq (beq_oid fo2 o0); intro.
      apply beq_oid_equal in H33.
      rewrite H33 in H44. rewrite <- H44 in H16; inversion H16; subst; auto.
      assert ( flow_to (join_label lb7 ll0) L_Label = true). apply  join_L_label_flow_to_L; auto. try(inconsist).  

      assert (Some  (Heap_OBJ cls4 F4 lb6 ll0) =
              lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls1 (fields_update F1 f0 v) lb0 ll1)) fo1
             ).
      apply lookup_updated_not_affected with o (Heap_OBJ cls1 (fields_update F1 f0 v) lb0 ll1)  h1; auto.
      intro contra. rewrite contra in H28.
      pose proof (beq_oid_same o). try (inconsist).

      assert (Some  (Heap_OBJ cls5 F5 lb7 ll0) =
           lookup_heap_obj (update_heap_obj h2 o0 (Heap_OBJ cls2 (fields_update F2 f0 v0) lb3 ll2)) fo2
           ).
      apply lookup_updated_not_affected with o0 (Heap_OBJ cls2 (fields_update F2 f0 v0) lb3 ll2) h2; auto.
      intro contra. rewrite contra in H33.
      pose proof (beq_oid_same o0). try (inconsist).


      exists cls4. exists cls5.
      exists lb6. exists lb7.
      exists F4. exists F5.
      exists ll0. exists ll0. 
      split; auto.
      split; auto.
      left; auto.
      split; auto.  split; auto. split; auto. split; auto. split; auto. apply H48.

      subst; auto.
      case_eq (beq_oid fo1 o); intro.
      ++
      apply beq_oid_equal in H28.
      subst; auto.
      assert (Some (Heap_OBJ cls1 (fields_update F1 f0 v) lb0 ll1) =
              lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls1 (fields_update F1 f0 v) lb0 ll1)) o).
      apply lookup_updated with h1 (Heap_OBJ cls_f1 FF1 lof1 llf1); auto.

      case_eq (beq_oid fo2 o0); intro.
      apply beq_oid_equal in H33.      
      subst; auto. 
      assert (Some (Heap_OBJ cls2 (fields_update F2 f0 v0) lb3 ll2)  =
              lookup_heap_obj (update_heap_obj h2 o0 (Heap_OBJ cls2 (fields_update F2 f0 v0) lb3 ll2)) o0).
      apply lookup_updated with h2 (Heap_OBJ cls_f2 FF2 lof2 llf2); auto.
      
      exists cls1. exists cls2.
      exists lb0. exists lb3.
      exists (fields_update F1 f0 v). exists (fields_update F2 f0 v0).
      exists ll1. exists ll2. 
      split; auto.

      assert (Some (Heap_OBJ cls_f2 FF2 lof2 llf2)  =
              lookup_heap_obj (update_heap_obj h2 o0 (Heap_OBJ cls2 (fields_update F2 f0 v0) lb3 ll2)) fo2).
      apply lookup_updated_not_affected with o0 (Heap_OBJ cls2 (fields_update F2 f0 v0) lb3 ll2) h2; auto.
      intro contra. rewrite contra in H33.
      assert (beq_oid o0 o0 = true). apply beq_oid_same. try (inconsist).

      exists cls1. exists cls_f2.
      exists lb0. exists lof2.
      exists (fields_update F1 f0 v). exists FF2.
      exists ll1. exists llf2.  
      split; auto. split; auto.
      right. split; auto. apply H40. 
       

      ++
      case_eq (beq_oid fo2 o0); intro.
      apply beq_oid_equal in H33.     
      subst; auto. 
      assert (Some (Heap_OBJ cls2 (fields_update F2 f0 v0) lb3 ll2)  =
              lookup_heap_obj (update_heap_obj h2 o0 (Heap_OBJ cls2 (fields_update F2 f0 v0) lb3 ll2)) o0).
      apply lookup_updated with h2 (Heap_OBJ cls_f2 FF2 lof2 llf2); auto.

      assert (Some  (Heap_OBJ cls_f1 FF1 lof1 llf1) =
              lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls1 (fields_update F1 f0 v) lb0 ll1)) fo1).
      apply lookup_updated_not_affected with o (Heap_OBJ cls1 (fields_update F1 f0 v) lb0 ll1) h1; auto.
      intro contra. rewrite contra in H28.
      assert (beq_oid o o = true). apply beq_oid_same. try (inconsist).      
      
      exists cls_f1. exists cls2.
      exists lof1. exists lb3.
      exists FF1. exists (fields_update F2 f0 v0).
      exists llf1. exists ll2. 
      split; auto. split; auto.
      right; auto.  split; auto. apply H40. 


      assert (Some (Heap_OBJ cls_f2 FF2 lof2 llf2)  =
              lookup_heap_obj (update_heap_obj h2 o0 (Heap_OBJ cls2 (fields_update F2 f0 v0) lb3 ll2)) fo2).
      apply lookup_updated_not_affected with o0 (Heap_OBJ cls2 (fields_update F2 f0 v0) lb3 ll2) h2; auto.
      intro contra. rewrite contra in H33.
      assert (beq_oid o0 o0 = true). apply beq_oid_same. try (inconsist).

      assert (Some  (Heap_OBJ cls_f1 FF1 lof1 llf1) =
              lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls1 (fields_update F1 f0 v) lb0 ll1)) fo1).
      apply lookup_updated_not_affected with o (Heap_OBJ cls1 (fields_update F1 f0 v) lb0 ll1) h1; auto.
      intro contra. rewrite contra in H28.
      assert (beq_oid o o = true). apply beq_oid_same. try (inconsist).      

      exists cls_f1. exists cls_f2.
      exists lof1. exists lof2.
      exists FF1. exists FF2.
      exists llf1. exists llf2. 
      split; auto. 
    + intros.
      apply lookup_updated_heap_must_none in H21.
      apply H13 in H21. auto. 

    + intros. 
      apply lookup_updated_heap_must_none in H21.
      apply H17 in H21. auto.

    + intros.
      case_eq (beq_oid o1 o); intro.
      apply  beq_oid_equal in H23.
      subst; auto.
      apply H19 with cls1 F1 lb0 ll1; auto. 

      assert (Some (Heap_OBJ cls F lb ll) =
              lookup_heap_obj h1 o1
             ).
      subst; auto.
      eauto using lookup_updated_heap_old_obj.
      destruct H19 with o1 cls F lb ll; auto. 

    + intros.
      case_eq (beq_oid o1 o0); intro.
      apply  beq_oid_equal in H23.
      rewrite <- H23 in H16.
      subst; auto. 
      destruct H20 with o0 cls2 F2 lb3 ll2 ; auto.

      assert (Some (Heap_OBJ cls F lb ll) =
              lookup_heap_obj h2 o1
             ).
      eauto using lookup_updated_heap_old_obj.
      destruct H20 with o1 cls F lb ll; auto. 
Qed.
Hint Resolve update_field_preserve_bijection. 
*)

Lemma change_obj_lbl_h1_with_H_preserve_bijection : forall ct h1 h2 φ cls lo lo' F o lb1
  lx ll,
    wfe_heap ct h1 ->
    L_equivalence_heap h1 h2 φ ->
    Some (Heap_OBJ cls F lo ll) = lookup_heap_obj h1 o ->
    flow_to (join_label lb1 lx) ll  = true ->
    flow_to lb1 L_Label = false ->
    flow_to lo lo' = true ->
    L_equivalence_heap
    (update_heap_obj h1 o (Heap_OBJ cls F lo' ll)) h2 φ.
    
Proof with eauto.
  intros. 
  assert ( flow_to (join_label lb1 lx) L_Label = false).
  apply flow_join_label with lb1 lx; auto.
  apply  join_label_commutative; auto.
  assert (flow_to ll L_Label  = false).
  apply  flow_transitive with (join_label lb1 lx); auto.
  
  inversion H0; subst; auto.
  apply L_eq_heap; auto.
  - intros. apply H7 in H12. inversion H12; subst; auto.
    + 
      case_eq (beq_oid o1 o); intro.
      ++
        apply beq_oid_equal in H17.
        rewrite H17 in H13; rewrite <- H13 in H1; inversion H1; subst.
        try (inconsist_label).
      ++
        apply object_equal_H with lb cls2 cls2 F1 F2 ll0; auto.
        assert ( Some (Heap_OBJ cls2 F1 lb ll0) =
                 lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls F lo'  ll)) o1).
        apply lookup_updated_not_affected with o (Heap_OBJ cls F lo' ll) h1; auto.
        intro contra.
        try (beq_oid_inconsist).
        auto.
    +
      case_eq (beq_oid o1 o); intro.
      ++
        apply beq_oid_equal in H18.
        rewrite H18 in H13; rewrite <- H13 in H1; inversion H1; subst.
        try (inconsist_label).
      ++
        apply object_equal_L with lb cls1 cls2 F1 F2 ll0; auto.
        assert ( Some (Heap_OBJ cls1 F1 lb ll0) =
                 lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls F lo'  ll)) o1).
        apply lookup_updated_not_affected with o (Heap_OBJ cls F lo' ll) h1; auto.
        intro contra.
        try (beq_oid_inconsist).
        auto.

        destruct H17.
        destruct H19. destruct H20. 
   
        split; auto.
        split; auto. split; auto.  

        intros. 
        destruct H21 with fname fo1 fo2; auto.
        destruct H24 as [cls_f2]. rename x into cls_f1.
        destruct H24 as [lof1]. destruct H24 as [lof2].
        destruct H24 as [FF1]. destruct H24 as [FF2].
        destruct H24 as [llf1].        destruct H24 as [llf2].
        
        destruct H24; auto.  destruct H25.
        case_eq (beq_oid fo1 o); intro.
        +++
          apply beq_oid_equal in H27; subst; auto.
          rewrite H24 in H1 ; inversion H1; subst; auto.
          destruct H26.          
          ++++
            destruct H17. destruct H26. destruct H27. destruct H27. 
            try (inconsist).
          ++++
            assert (Some (Heap_OBJ cls_f1 FF1 lo' llf1)
            = lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls_f1 FF1 lo' llf1)) o).
            eauto using lookup_updated.
            
            exists cls_f1. exists cls_f2.
            exists lo'. exists lof2.
            exists FF1. exists FF2.
            exists llf1. exists llf2.   
            split; auto.
            
        +++
          exists cls_f1. exists cls_f2.
          exists lof1. exists lof2.
          exists FF1. exists FF2.
          exists llf1. exists llf2.  
          split; auto.
          assert (Some (Heap_OBJ cls_f1 FF1 lof1 llf1)
                  = lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls F lo' ll)) fo1).          
          apply lookup_updated_not_affected with o (Heap_OBJ cls F lo' ll) h1; auto.
          intro contra. subst; auto.
          assert (beq_oid o o = true). apply beq_oid_same.
          try (inconsist).    auto. 
    
  - intros.
    apply lookup_updated_heap_must_none in H12.
    auto. 
  - intros.
    case_eq (beq_oid o0 o); intro.
    + 
    apply beq_oid_equal in H14.
    rewrite <- H14 in H1. apply H10  with cls F lo ll; auto.
    +
      assert (Some (Heap_OBJ cls0 F0 lb ll0) = lookup_heap_obj h1 o0).
    apply lookup_updated_not_affected_reverse
      with o (Heap_OBJ cls F lo' ll)
           (update_heap_obj h1 o (Heap_OBJ cls F lo' ll)); auto.
    intro contra. rewrite contra in H14.
    assert (beq_oid o o = true). apply beq_oid_same. try (inconsist).
    apply H10 with cls0 F0 lb ll0; auto.     
Qed. Hint Resolve  change_obj_lbl_h1_with_H_preserve_bijection.



Lemma change_obj_lbl_h2_with_H_preserve_bijection : forall ct h1 h2 φ cls lo lo' F o lb1
  lx ll,
    wfe_heap ct h1 ->
    L_equivalence_heap h1 h2 φ ->
    Some (Heap_OBJ cls F lo ll) = lookup_heap_obj h2 o ->
    flow_to (join_label lb1 lx) ll = true ->
    flow_to lb1 L_Label = false ->
    flow_to lo lo' = true ->
    L_equivalence_heap h1
    (update_heap_obj h2 o (Heap_OBJ cls F lo' ll)) φ.    
Proof with eauto.
    intros. 
  assert ( flow_to (join_label lb1 lx) L_Label = false).
  apply flow_join_label with lb1 lx; auto.
  apply  join_label_commutative; auto.
  assert (flow_to ll L_Label  = false).
  apply  flow_transitive with (join_label lb1 lx); auto.
  
  inversion H0; subst; auto.
  apply L_eq_heap; auto.
  - intros. apply H7 in H12. inversion H12; subst; auto.
    + 
      case_eq (beq_oid o2 o); intro.
      ++
        apply beq_oid_equal in H17.
        rewrite H17 in H14; rewrite <- H14 in H1; inversion H1; subst.
        try (inconsist_label).
      ++
        apply object_equal_H with lb cls2 cls2 F1 F2 ll0; auto.
        assert ( Some (Heap_OBJ cls2 F2 lb ll0) =
                 lookup_heap_obj (update_heap_obj h2 o (Heap_OBJ cls F lo'  ll)) o2).
        apply lookup_updated_not_affected with o (Heap_OBJ cls F lo' ll) h2; auto.
        intro contra.
        try (beq_oid_inconsist).
        auto.
    +
      case_eq (beq_oid o2 o); intro.
      ++
        apply beq_oid_equal in H18.
        rewrite H18 in H14; rewrite <- H14 in H1; inversion H1; subst.
        try (inconsist_label).
      ++
        apply object_equal_L with lb cls1 cls2 F1 F2 ll0; auto.
        assert ( Some (Heap_OBJ cls2 F2 lb ll0) =
                 lookup_heap_obj (update_heap_obj h2 o (Heap_OBJ cls F lo'  ll)) o2).
        apply lookup_updated_not_affected with o (Heap_OBJ cls F lo' ll) h2; auto.
        intro contra.
        try (beq_oid_inconsist).
        auto.

        destruct H17.
        destruct H19. destruct H20. 
   
        split; auto.
        split; auto. split; auto.  

        intros. 
        destruct H21 with fname fo1 fo2; auto.
        destruct H24 as [cls_f2]. rename x into cls_f1.
        destruct H24 as [lof1]. destruct H24 as [lof2].
        destruct H24 as [FF1]. destruct H24 as [FF2].
        destruct H24 as [llf1]. destruct H24 as [llf2].
        
        destruct H24; auto.  destruct H25.
        case_eq (beq_oid fo2 o); intro.
        +++
          apply beq_oid_equal in H27; subst; auto.
          rewrite H25 in H1 ; inversion H1; subst; auto.
          destruct H26.          
          ++++
            destruct H17. destruct H26. destruct H27. destruct H27. 
            try (inconsist).
          ++++
            assert (Some (Heap_OBJ cls_f2 FF2 lo' llf2)
            = lookup_heap_obj (update_heap_obj h2 o (Heap_OBJ cls_f2 FF2 lo' llf2)) o).
            eauto using lookup_updated.
            
            exists cls_f1. exists cls_f2.
            exists lof1. exists lo'.
            exists FF1. exists FF2.
            exists llf1. exists llf2.   
            split; auto.
        +++
          exists cls_f1. exists cls_f2.
          exists lof1. exists lof2.
          exists FF1. exists FF2.
          exists llf1. exists llf2.  
          split; auto.
          assert (Some (Heap_OBJ cls_f2 FF2 lof2 llf2)
                  = lookup_heap_obj (update_heap_obj h2 o (Heap_OBJ cls F lo' ll)) fo2).          
          apply lookup_updated_not_affected with o (Heap_OBJ cls F lo' ll) h2; auto.
          intro contra. subst; auto.
          assert (beq_oid o o = true). apply beq_oid_same.
          try (inconsist).    auto. 
    
  - intros.
    apply lookup_updated_heap_must_none in H12.
    auto. 
  - intros.
    case_eq (beq_oid o0 o); intro.
    + 
    apply beq_oid_equal in H14.
    rewrite <- H14 in H1. apply H11  with cls F lo ll; auto.
    +
      assert (Some (Heap_OBJ cls0 F0 lb ll0) = lookup_heap_obj h2 o0).
    apply lookup_updated_not_affected_reverse
      with o (Heap_OBJ cls F lo' ll)
           (update_heap_obj h2 o (Heap_OBJ cls F lo' ll)); auto.
    intro contra. rewrite contra in H14.
    assert (beq_oid o o = true). apply beq_oid_same. try (inconsist).
    apply H11 with cls0 F0 lb ll0; auto. 
Qed. Hint Resolve change_obj_lbl_h2_with_H_preserve_bijection.   





Lemma change_obj_lbl_h1_preserve_L_eq_tm  :
  forall  φ h1 h2 ct cls F lo lo' o lb1 lx
          t1 t2 ll,
  wfe_heap ct h2 ->  wfe_heap ct h1 -> 
  L_equivalence_heap h1 h2 φ ->
  L_equivalence_tm t1 h1 t2 h2 φ ->
  Some (Heap_OBJ cls F lo ll) = lookup_heap_obj h1 o ->
  flow_to (join_label lb1 lx) ll = true ->
  flow_to lb1 L_Label = false ->
  flow_to lo lo' = true ->
  L_equivalence_tm t1 (update_heap_obj h1 o (Heap_OBJ cls F lo' ll))
                    t2 h2 φ.
Proof with eauto. 
  intros φ h1 h2 ct cls F lo lo' o lb1 lx
          t1 t2 ll.
  intros.
  assert ( flow_to (join_label lb1 lx) L_Label = false).
  apply flow_join_label with lb1 lx; auto.
  apply  join_label_commutative; auto.
  
  assert (flow_to ll L_Label = false).
  apply flow_transitive with (join_label lb1 lx); auto. 

  generalize dependent t2.  
  induction t1; intros;inversion H2; subst; auto.

  -  case_eq (beq_oid o0 o); intro.
     + 
     apply beq_oid_equal in H9. subst; auto.
     rewrite <- H11 in H3; inversion H3; subst; auto.
     try (inconsist).
     +
       apply L_equivalence_tm_eq_object_L with cls1 F1 lo0 cls2 F2 ll0; subst; auto.
       apply lookup_updated_not_affected with o (Heap_OBJ cls F lo' ll) h1; auto.
       intro contra. subst; auto. pose proof (beq_oid_same o). try (inconsist).

  -
    case_eq (beq_oid o0 o); intro.
    + 
      apply beq_oid_equal in H9. subst; auto.
      rewrite <- H10 in H3; inversion H3; subst; auto.
      apply L_equivalence_tm_eq_object_H  with cls1 cls2  F1 lo'  F2 lo2 ll1 ll2 ; subst; auto.
      eauto using lookup_updated .

    +  apply L_equivalence_tm_eq_object_H  with cls1 cls2 F1 lo1 F2 lo2 ll1 ll2; subst; auto.
       apply lookup_updated_not_affected with o (Heap_OBJ cls F lo' ll) h1; auto.
       intro contra.  rewrite contra in H9. pose proof (beq_oid_same o). try (inconsist).  
  Qed. Hint Resolve  change_obj_lbl_h1_preserve_L_eq_tm.




Lemma change_obj_lbl_h2_preserve_L_eq_tm :
  forall φ h1 h2 ct cls F lo lo' o lb1 lx
          t1 t2 ll,
  wfe_heap ct h2 ->  wfe_heap ct h1 -> 
  L_equivalence_heap h1 h2 φ ->
  L_equivalence_tm t1 h1 t2 h2 φ ->
  Some (Heap_OBJ cls F lo ll) = lookup_heap_obj h2 o ->
  flow_to (join_label lb1 lx) ll  = true ->
  flow_to lb1 L_Label = false ->
  flow_to lo lo' = true ->
  L_equivalence_tm t1 h1
                    t2 (update_heap_obj h2 o (Heap_OBJ cls F lo' ll)) φ.
Proof with eauto. 
  intros φ h1 h2 ct cls F lo lo' o lb1 lx
          t1 t2 ll.
  intros.
  assert ( flow_to (join_label lb1 lx) L_Label = false).
  apply flow_join_label with lb1 lx; auto.
  apply  join_label_commutative; auto.
  
  assert (flow_to ll L_Label = false).
  apply flow_transitive with (join_label lb1 lx); auto. 

  generalize dependent t2.  
  induction t1; intros;inversion H2; subst; auto.

  -  case_eq (beq_oid o2 o); intro.
     + 
     apply beq_oid_equal in H9. subst; auto.
     rewrite <- H13 in H3; inversion H3; subst; auto.
     try (inconsist).
     +
       apply L_equivalence_tm_eq_object_L with cls1 F1 lo0 cls2 F2 ll0; subst; auto.
       apply lookup_updated_not_affected with o (Heap_OBJ cls F lo' ll) h2; auto.
       intro contra. subst; auto. pose proof (beq_oid_same o). try (inconsist).
  -
    case_eq (beq_oid o2 o); intro.
    + 
      apply beq_oid_equal in H9. subst; auto.
      rewrite <- H11 in H3; inversion H3; subst; auto.
      apply L_equivalence_tm_eq_object_H  with cls1 cls2  F1 lo1  F2 lo' ll1 ll2 ; subst; auto.
      eauto using lookup_updated .
    +  apply L_equivalence_tm_eq_object_H  with cls1 cls2 F1 lo1 F2 lo2 ll1 ll2; subst; auto.
       apply lookup_updated_not_affected with o (Heap_OBJ cls F lo' ll) h2; auto.
       intro contra.  rewrite contra in H9. pose proof (beq_oid_same o). try (inconsist).  
Qed. Hint Resolve change_obj_lbl_h2_preserve_L_eq_tm.


Lemma change_obj_lbl_h1_preserve_L_eq_fs  :
  forall   φ h1 h2 ct cls F lo lo' o lb1 lx
           fs1 fs2 ll,
  wfe_heap ct h2 ->  wfe_heap ct h1 -> 
  L_equivalence_heap h1 h2 φ ->
  L_equivalence_fs fs1 h1 fs2 h2 φ ->
  Some (Heap_OBJ cls F lo ll) = lookup_heap_obj h1 o ->
  flow_to (join_label lb1 lx) ll = true ->
  flow_to lb1 L_Label = false ->
  flow_to lo lo' = true ->
  L_equivalence_fs fs1 (update_heap_obj h1 o (Heap_OBJ cls F lo' ll))
                    fs2 h2 φ.
Proof with eauto. 
  intros  φ h1 h2 ct cls F lo lo' o lb1 lx
           fs1 fs2 ll.
  intros.
  generalize dependent fs2.
  induction fs1; intros; inversion H2; subst; auto.

  apply L_equal_fs; auto.
  eauto using change_obj_lbl_h1_preserve_L_eq_tm.
Qed. Hint Resolve change_obj_lbl_h1_preserve_L_eq_fs.


Lemma change_obj_lbl_h2_preserve_L_eq_fs  :
  forall  φ h1 h2 ct cls F lo lo' o lb1 lx
           fs1 fs2 ll,
  wfe_heap ct h2 ->  wfe_heap ct h1 -> 
  L_equivalence_heap h1 h2 φ ->
  L_equivalence_fs fs1 h1 fs2 h2 φ ->
  Some (Heap_OBJ cls F lo ll) = lookup_heap_obj h2 o ->
  flow_to (join_label lb1 lx) ll = true ->
  flow_to lb1 L_Label = false ->
  flow_to lo lo' = true ->
  L_equivalence_fs fs1 h1
                    fs2 (update_heap_obj h2 o (Heap_OBJ cls F lo' ll)) φ.
Proof with eauto. 
  intros φ h1 h2 ct cls F lo lo' o lb1 lx
           fs1 fs2 ll.
  intros.
  generalize dependent fs2.
  induction fs1; intros; inversion H2; subst; auto.

  apply L_equal_fs; auto.
  eauto using change_obj_lbl_h2_preserve_L_eq_tm.
Qed. Hint Resolve change_obj_lbl_h2_preserve_L_eq_fs.


Lemma  change_obj_lbl_h1_preserve_L_eq_store  :
  forall  φ h1 h2 ct cls F lo lo' o lb1 lx
          sf1 sf2 ll,
  wfe_heap ct h2 ->  wfe_heap ct h1 -> 
  L_equivalence_heap h1 h2 φ ->
  L_equivalence_store sf1 h1 sf2 h2 φ ->
  Some (Heap_OBJ cls F lo ll) = lookup_heap_obj h1 o ->
  flow_to (join_label lb1 lx) ll = true ->
  flow_to lb1 L_Label = false ->
  flow_to lo lo' = true ->
  L_equivalence_store sf1 (update_heap_obj h1 o (Heap_OBJ cls F lo' ll))
                    sf2 h2 φ.
Proof with eauto.
  intros   φ h1 h2 ct cls F lo lo' o lb1 lx
          sf1 sf2 ll.
  intros.
  assert ( flow_to (join_label lb1 lx) L_Label = false).
  apply flow_join_label with lb1 lx; auto.
  apply  join_label_commutative; auto.

  assert (flow_to ll L_Label = false).
  apply flow_transitive with (join_label lb1 lx); auto. 

  inversion H2; subst; auto. 
  apply L_equivalence_store_L; auto.
  destruct H9.
  split; auto; intros.
  eauto using change_obj_lbl_h1_preserve_L_eq_tm.
Qed. Hint Resolve  change_obj_lbl_h1_preserve_L_eq_store.



Lemma  change_obj_lbl_h2_preserve_L_eq_store :
  forall  φ h1 h2 ct cls F lo lo' o lb1 lx
          sf1 sf2 ll,
  wfe_heap ct h2 ->  wfe_heap ct h1 -> 
  L_equivalence_heap h1 h2 φ ->
  L_equivalence_store sf1 h1 sf2 h2 φ ->
  Some (Heap_OBJ cls F lo ll) = lookup_heap_obj h2 o ->
  flow_to (join_label lb1 lx) ll = true ->
  flow_to lb1 L_Label = false ->
  flow_to lo lo' = true ->
  L_equivalence_store sf1 h1
                    sf2 (update_heap_obj h2 o (Heap_OBJ cls F lo' ll)) φ.
Proof with eauto.
  intros  φ h1 h2 ct cls F lo lo' o lb1 lx
          sf1 sf2 ll.
  intros.
  assert ( flow_to (join_label lb1 lx) L_Label = false).
  apply flow_join_label with lb1 lx; auto.
  apply  join_label_commutative; auto.

  assert (flow_to  ll L_Label = false).
  apply flow_transitive with (join_label lb1 lx); auto. 

  inversion H2; subst; auto. 
  apply L_equivalence_store_L; auto.
  intros.
  destruct H9; auto.
  split; auto.
  intros.
  eauto using change_obj_lbl_h2_preserve_L_eq_tm.
Qed. Hint Resolve  change_obj_lbl_h2_preserve_L_eq_store.
    



Lemma change_obj_lbl_h1_preserve_L_eq_ctn :
  forall  φ h1 h2 ct cls F lo lo' o lb1 lx
          ctn1 ctn2 ll,
   wfe_heap ct h2 ->  wfe_heap ct h1 -> 
  L_equivalence_heap h1 h2 φ ->
  L_eq_container ctn1 h1 ctn2 h2 φ ->
  Some (Heap_OBJ cls F lo ll) = lookup_heap_obj h1 o ->
  flow_to  (join_label lb1 lx) ll = true ->
  flow_to lb1 L_Label = false ->
  flow_to lo lo' = true ->
  L_eq_container ctn1 (update_heap_obj h1 o (Heap_OBJ cls F lo' ll))
                    ctn2 h2 φ.
Proof with eauto. 
  intros φ h1 h2 ct cls F lo lo' o lb1 lx
          ctn1 ctn2 ll.
  intros.
  generalize dependent ctn2.
  induction ctn1; intros; inversion H2; subst; auto.
  apply  L_eq_ctn; auto.
  eauto using change_obj_lbl_h1_preserve_L_eq_tm.
  eauto using change_obj_lbl_h1_preserve_L_eq_fs.
  eauto using change_obj_lbl_h1_preserve_L_eq_store.
Qed. Hint Resolve change_obj_lbl_h1_preserve_L_eq_ctn. 



Lemma change_obj_lbl_h2_preserve_L_eq_ctn:
  forall  φ h1 h2 ct cls F lo lo' o lb1 lx
          ctn1 ctn2 ll ,
   wfe_heap ct h2 ->  wfe_heap ct h1 -> 
  L_equivalence_heap h1 h2 φ ->
  L_eq_container ctn1 h1 ctn2 h2 φ ->
  Some (Heap_OBJ cls F lo ll) = lookup_heap_obj h2 o ->
  flow_to (join_label lb1 lx) ll = true ->
  flow_to lb1 L_Label = false ->
  flow_to lo lo' = true ->
  L_eq_container ctn1 h1
                    ctn2 (update_heap_obj h2 o (Heap_OBJ cls F lo' ll)) φ.
Proof with eauto. 
  intros φ h1 h2 ct cls F lo lo' o lb1 lx
          ctn1 ctn2 ll.
  intros.
  generalize dependent ctn2.
  induction ctn1; intros; inversion H2; subst; auto.
  apply  L_eq_ctn; auto.
  eauto using change_obj_lbl_h2_preserve_L_eq_tm.
  eauto using change_obj_lbl_h2_preserve_L_eq_fs.
  eauto using change_obj_lbl_h2_preserve_L_eq_store.
Qed. Hint Resolve change_obj_lbl_h2_preserve_L_eq_ctn.

  

Lemma change_obj_lbl_h1_preserve_L_eq_ctns  :
  forall  φ h1 h2 ct cls F lo lo' o lb1 lx
          ctns1 ctns2 ll,
   wfe_heap ct h2 ->  wfe_heap ct h1 -> 
  L_equivalence_heap h1 h2 φ ->
  L_eq_ctns ctns1 h1 ctns2 h2 φ ->
  Some (Heap_OBJ cls F lo ll) = lookup_heap_obj h1 o ->
  flow_to (join_label lb1 lx) ll = true ->
  flow_to lb1 L_Label = false ->
  flow_to lo lo' = true ->
  L_eq_ctns ctns1 (update_heap_obj h1 o (Heap_OBJ cls F lo' ll))
                    ctns2 h2 φ.
Proof with eauto. 
  intros φ h1 h2 ct cls F lo lo' o lb1 lx
          ctns1 ctns2 l.
  intros.
  generalize dependent ctns2.
  induction ctns1; intros; inversion H2; subst; auto.
  apply  L_eq_ctns_list; auto.
  eauto using  change_obj_lbl_h2_preserve_L_eq_ctn.
Qed. Hint Resolve change_obj_lbl_h1_preserve_L_eq_ctns.


Lemma change_obj_lbl_h2_preserve_L_eq_ctns :
  forall  φ h1 h2 ct cls F lo lo' o lb1 lx
          ctns1 ctns2 ll,
   wfe_heap ct h2 ->  wfe_heap ct h1 -> 
  L_equivalence_heap h1 h2 φ ->
  L_eq_ctns ctns1 h1 ctns2 h2 φ ->
  Some (Heap_OBJ cls F lo ll) = lookup_heap_obj h2 o ->
  flow_to (join_label lb1 lx) ll  = true ->
  flow_to lb1 L_Label = false ->
  flow_to lo lo' = true ->
  L_eq_ctns ctns1 h1
                    ctns2 (update_heap_obj h2 o (Heap_OBJ cls F lo' ll)) φ.
Proof with eauto. 
  intros φ h1 h2 ct cls F lo lo' o lb1 lx
          ctns1 ctns2.
  intros.
  generalize dependent ctns1.
  induction ctns2; intros; inversion H2; subst; auto.
  apply  L_eq_ctns_list; auto.
  eauto using  change_obj_lbl_h2_preserve_L_eq_ctn.
Qed. Hint Resolve change_obj_lbl_h2_preserve_L_eq_ctns.


Lemma change_obj_lbl_h1_preserve_config_eq :
  forall  φ h1 h2 ct cls F lo lo' o lb1 lx
          ctn1 ctn2 ctns1 ctns2 ll,
    wfe_heap ct h2 ->  wfe_heap ct h1 -> 
    L_equivalence_heap h1 h2 φ ->
    L_equivalence_config (Config ct ctn1 ctns1  h1)
                         (Config ct ctn2 ctns2  h2) φ ->

    Some (Heap_OBJ cls F lo ll) = lookup_heap_obj h1 o ->
    flow_to  (join_label lb1 lx) ll = true ->
    flow_to lb1 L_Label = false ->
    flow_to lo lo' = true ->
    L_equivalence_config
      (Config ct ctn1 ctns1 (update_heap_obj h1 o (Heap_OBJ cls F lo' ll)))
      (Config ct ctn2 ctns2  h2)  φ.
Proof with eauto.
  intros.
  
  remember (Config ct ctn1 ctns1 h1) as config1.
  remember (Config ct ctn2 ctns2 h2) as config2.
  generalize dependent ctn1. generalize dependent ctn2.
  generalize dependent ctns1. generalize dependent ctns2. 
  induction H2; subst; intros; inversion Heqconfig1; inversion Heqconfig2; subst; auto.
  apply L_equivalence_config_L; auto.
  eauto using change_obj_lbl_h2_preserve_L_eq_ctn.
  eauto using change_obj_lbl_h2_preserve_L_eq_ctns.

  
  induction ctns3. induction ctns0.
  apply L_equivalence_config_H; auto.
  unfold low_component.  
  rewrite H2; rewrite H7.
  apply L_equivalence_config_L; auto.
  apply L_eq_ctn; auto.
  apply L_equivalence_store_L; auto; intros; try (inversion H9).
  split; auto.
  intros; inversion H9.
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
       (update_heap_obj h1 o (Heap_OBJ cls F lo' ll)))
    (Config ct (Container hole nil L_Label empty_stack_frame) nil h1)  φ).
  apply L_equivalence_config_L; auto.
  apply L_eq_ctn; auto.
  apply L_equivalence_store_L; auto; intros;
    try (inversion H9).
  intros. split; auto.
  intros. inversion H9. 
  split; auto.  

  
  remember ((low_component ct a ctns0 h2)) as conf.
  destruct conf. destruct c0. 
  assert (c = ct /\ h = h2 /\ flow_to l0 L_Label = true).
  eauto using low_component_lead_to_L.
  
  destruct H10. destruct H11. subst; auto.


  inversion H8; subst; auto. 
  apply L_equivalence_config_L; auto.
  eauto using update_field_h1_preserve_L_eq_ctn. 
  eauto using update_field_h1_preserve_L_eq_ctns. 
  try (inconsist_label).
  inversion H8; subst; auto. 
  inversion H8; subst; auto.

  + apply L_equivalence_config_H; auto.
  remember (low_component ct (Container t1 fs1 lb0 sf1) (a :: ctns3) h1) as conf1.
  remember ((low_component ct (Container t2 fs2 lb2 sf2) ctns0 h2)) as conf2.
  destruct conf1. destruct conf2.
  destruct c0. 
  assert (c = ct /\ h = h1 /\ flow_to l1 L_Label = true).
  eauto using low_component_lead_to_L. 

  destruct c2. 
  assert (c1 = ct /\ h0 = h2 /\ flow_to l2 L_Label = true).
  eauto using low_component_lead_to_L. 
  destruct H9. destruct H11.
  destruct H10. destruct H13.     subst. auto.

  assert (Config ct (Container t f l1 s) l (update_heap_obj h1 o (Heap_OBJ cls F lo' ll))
          = (low_component ct (Container t1 fs1 lb0 sf1) (a :: ctns3)
                           (update_heap_obj h1 o (Heap_OBJ cls F lo' ll)))
         ).
  apply low_component_irrelevant_to_heap with h1; auto.
  rewrite <- H9.
  inversion H8; subst; auto.
  inversion H28; subst; auto. 
    
  apply L_equivalence_config_L; auto.
  eauto using update_field_h1_preserve_L_eq_ctn. 
  eauto using update_field_h1_preserve_L_eq_ctns.
  try (inconsist_label).
  inversion H8; subst;  auto.
  inversion H8; subst;  auto.  
  inversion H8; subst;  auto.  
  inversion H8; subst;  auto.  
Qed. Hint Resolve change_obj_lbl_h1_preserve_config_eq.


Lemma change_obj_lbl_h2_preserve_config_eq:
  forall  φ h1 h2 ct cls F lo lo' o lb1 lx
          ctn1 ctn2 ctns1 ctns2 ll,
    wfe_heap ct h2 ->  wfe_heap ct h1 -> 
    L_equivalence_heap h1 h2 φ ->
    L_equivalence_config (Config ct ctn1 ctns1  h1)
                         (Config ct ctn2 ctns2  h2) φ ->

    Some (Heap_OBJ cls F lo ll) = lookup_heap_obj h2 o ->
    flow_to  (join_label lb1 lx)  ll = true ->
    flow_to lb1 L_Label = false ->
    flow_to lo lo' = true ->
    L_equivalence_config
      (Config ct ctn1 ctns1 h1)
      (Config ct ctn2 ctns2  (update_heap_obj h2 o (Heap_OBJ cls F lo' ll)))  φ.
Proof with eauto.
  intros.
  
  remember (Config ct ctn1 ctns1 h1) as config1.
  remember (Config ct ctn2 ctns2 h2) as config2.
  generalize dependent ctn1. generalize dependent ctn2.
  generalize dependent ctns1. generalize dependent ctns2. 
  induction H2; subst; intros; inversion Heqconfig1; inversion Heqconfig2; subst; auto.
  apply L_equivalence_config_L; auto.
  eauto using change_obj_lbl_h2_preserve_L_eq_ctn.
  eauto using change_obj_lbl_h2_preserve_L_eq_ctns.

  
  induction ctns3. induction ctns0.
  apply L_equivalence_config_H; auto.
  unfold low_component.  
  rewrite H2; rewrite H7.
  apply L_equivalence_config_L; auto.
  apply L_eq_ctn; auto.
  apply L_equivalence_store_L; auto; intros; try (empty_sf).
  split; auto.
  intros; try (empty_sf).
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
    (update_heap_obj h2 o (Heap_OBJ cls F lo' ll)))  φ).
  apply L_equivalence_config_L; auto.
  apply L_eq_ctn; auto.
  apply L_equivalence_store_L; auto; intros; try (empty_sf).
  split; auto.
  intros; try (empty_sf).
  split; auto. 

  
  remember ((low_component ct a ctns0 h2)) as conf.
  destruct conf. destruct c0. 
  assert (c = ct /\ h = h2 /\ flow_to l0 L_Label = true).
  eauto using low_component_lead_to_L. 
  destruct H10. destruct H11. subst; auto.

  assert (Config ct (Container t f l0 s) l
                 (update_heap_obj h2 o (Heap_OBJ cls F lo' ll)) 
          = (low_component ct a ctns0 (update_heap_obj h2 o (Heap_OBJ cls F lo' ll)))).
  apply low_component_irrelevant_to_heap with h2; auto. rewrite <- H10.

  inversion H8; subst; auto.
  inversion H28; subst; auto. 
  apply L_equivalence_config_L; auto.
  eauto using update_field_h2_preserve_L_eq_ctn. 
  eauto using update_field_h2_preserve_L_eq_ctns.
  try (inconsist_label).
  inversion H8; subst;  auto.
  inversion H8; subst;  auto.  

  + apply L_equivalence_config_H; auto.
  remember (low_component ct (Container t1 fs1 lb0 sf1) (a :: ctns3) h1) as conf1.
  remember ((low_component ct (Container t2 fs2 lb2 sf2) ctns0 h2)) as conf2.
  destruct conf1. destruct conf2.
  destruct c0. 
  assert (c = ct /\ h = h1 /\ flow_to l1 L_Label = true).
  apply low_component_lead_to_L with t f s (Container t1 fs1 lb0 sf1) l (a :: ctns3)  ; auto. 

  destruct c2. 
  assert (c1 = ct /\ h0 = h2 /\ flow_to l2 L_Label = true).
  eauto using low_component_lead_to_L.
  destruct H9. destruct H11.
  destruct H10. destruct H13.     subst; auto.
  assert (Config ct (Container t0 f0 l2 s0) l0 (update_heap_obj h2 o (Heap_OBJ cls F lo' ll))
          = (low_component ct (Container t2 fs2 lb2 sf2)  ctns0
                           (update_heap_obj h2 o (Heap_OBJ cls F lo' ll)))
         ).
  apply low_component_irrelevant_to_heap with h2; auto.  
  rewrite <- H9.
  inversion H8; subst; auto.
  inversion H28; subst; auto. 
    
  apply L_equivalence_config_L; auto.
  eauto using update_field_h1_preserve_L_eq_ctn. 
  eauto using update_field_h1_preserve_L_eq_ctns.
  try (inconsist_label).
  inversion H8; subst;  auto.
  inversion H8; subst;  auto.  
  inversion H8; subst;  auto.  
  inversion H8; subst;  auto.
Qed. Hint Resolve change_obj_lbl_h2_preserve_config_eq.


  (* heap bijection preservation *)
Lemma change_obj_preserve_bijection : forall  ct h1 h2 φ lo lo0 lo' F F0 o o0 lb1 lb2 cls cls0 ll ll0
                                                 ,
    wfe_heap ct h1 -> field_wfe_heap ct h1 ->
    wfe_heap ct h2 -> field_wfe_heap ct h2 ->  
    L_equivalence_heap h1 h2 φ ->
    Some (Heap_OBJ cls F lo ll) = lookup_heap_obj h1 o ->
    Some (Heap_OBJ cls0 F0 lo0 ll0) = lookup_heap_obj h2 o0 ->
    L_equivalence_tm (ObjId o) h1 (ObjId o0) h2 φ ->
    flow_to lb1 L_Label = true ->
    flow_to lb2 L_Label = true ->
    flow_to lb1 ll = true ->
    flow_to lb2 ll0 = true ->
    flow_to lo lo' = true ->
    flow_to lo0 lo' = true ->
      L_equivalence_heap
        (update_heap_obj h1 o (Heap_OBJ cls F lo' ll))
        (update_heap_obj h2 o0 (Heap_OBJ cls0 F0 lo' ll0)) φ.
    
Proof with eauto.
  intros ct h1 h2 φ lo lo0 lo' F F0 o o0 lb1 lb2 cls cls0 ll ll0.
  intros.   
  inversion H6; subst; auto.
  - 
    rewrite <- H16 in H4; inversion H4; subst; auto.
    rewrite <- H19 in H5; inversion H5; subst; auto.
    inversion H3; subst; auto.

    apply  L_eq_heap; auto.
    + 
    intros.
    assert (L_equivalence_object o1 h1 o2 h2 φ) as H_eq_o1_o2.          
    apply H13; auto. 
    inversion H_eq_o1_o2; subst; auto.
    ++ 
      case_eq (beq_oid o1 o); intro.
      +++
    apply beq_oid_equal in H27.
    rewrite H27 in H23. rewrite <- H23 in H16; inversion H16; subst.
    assert ( Some  (Heap_OBJ cls3 F0 lo' ll)  =
      lookup_heap_obj  (update_heap_obj h1 o (Heap_OBJ cls3 F0 lo' ll))  o).
    apply lookup_updated with h1  (Heap_OBJ cls3 F0 lb ll); auto.

    case_eq (beq_oid o2 o0); intro.
    ++++
    apply beq_oid_equal in H28.
    rewrite H28 in H24. rewrite <- H24 in H19; inversion H19; subst; auto.  

    assert ( Some  (Heap_OBJ cls3 F3 lo' ll)  =
      lookup_heap_obj  (update_heap_obj h2 o0 (Heap_OBJ cls3 F3 lo' ll))  o0).
    apply lookup_updated with h2  (Heap_OBJ cls3 F3 lb ll) ; auto.
    case_eq (flow_to lo' L_Label); intro.
    +++++
    apply object_equal_L with lo' cls3 cls3
                              F0 F3 ll
    ; auto.
      assert (flow_to lo' L_Label = false).
    apply flow_transitive with lb; auto.  try (inconsist).
    +++++
      eauto using object_equal_H.
    ++++
      (* beq_oid o2 o0 = false cannot happen *)
      rewrite H15 in H22; inversion H22; subst; auto. 
      pose proof beq_oid_same o2. try (inconsist).

      +++
        assert ( Some  (Heap_OBJ cls3 F0 lb ll)  =
                 lookup_heap_obj  (update_heap_obj h1 o (Heap_OBJ cls1 F1 lo' ll1))  o1).
        apply lookup_updated_not_affected with o  (Heap_OBJ cls1 F1 lo' ll1) h1 ; auto.
        intro contra; subst; auto. pose proof beq_oid_same o. try (inconsist).

        case_eq (beq_oid o2 o0); intro.
        ++++
          apply beq_oid_equal in H29.
          rewrite H29 in H24; rewrite <- H24 in H19; inversion H19; subst; auto.
          apply right_left in H22.
          apply right_left in H15.
          rewrite H15 in H22; inversion H22; subst; auto.
          (* cannot happen*)
          pose proof beq_oid_same o1. try (inconsist).
        ++++
        assert ( Some  (Heap_OBJ cls3 F3 lb ll)  =
                 lookup_heap_obj  (update_heap_obj h2 o0 (Heap_OBJ cls2 F2 lo' ll1))  o2).
        apply lookup_updated_not_affected with o0 (Heap_OBJ cls2 F2 lo' ll1) h2 ; auto.
        intro contra; subst; auto. pose proof beq_oid_same o0. try (inconsist).
        eauto using object_equal_H. 
    ++
      case_eq (beq_oid o1 o); intro.
      +++
        apply beq_oid_equal in H28.
        rewrite H28 in H23. rewrite <- H23 in H16; inversion H16; subst.
        assert ( Some  (Heap_OBJ cls0 F0 lo' ll)  =
      lookup_heap_obj  (update_heap_obj h1 o (Heap_OBJ cls0 F0 lo' ll))  o).
        apply lookup_updated with h1  (Heap_OBJ cls0 F0 lb ll); auto.

        case_eq (beq_oid o2 o0); intro.
        ++++
          apply beq_oid_equal in H29.
          rewrite H29 in H24. rewrite <- H24 in H19; inversion H19; subst; auto.  

          assert ( Some  (Heap_OBJ cls3 F3 lo' ll)  =
                   lookup_heap_obj  (update_heap_obj h2 o0 (Heap_OBJ cls3 F3 lo' ll))  o0).
          apply lookup_updated with h2  (Heap_OBJ cls3 F3 lb ll) ; auto.
          case_eq (flow_to lo' L_Label); intro.
          +++++
            apply object_equal_L with lo' cls0 cls3
                              F0 F3 ll
          ; auto.
          destruct H27. destruct H31. destruct H32. 
          split; auto. split; auto. split; auto. 

          intros.
          destruct H33 with fname fo1 fo2; auto. rename x into cls_f1.
          destruct H36 as [cls_f2]. destruct H36 as [lof1].
          destruct H36 as [lof2]. destruct H36 as [FF1]. destruct H36 as [FF2].
          destruct H36 as [llf1]. destruct H36 as [llf2].

          destruct H36. destruct H37.  destruct H38.
   
          ++++++

    (* fields are both L *)
            case_eq (beq_oid fo1 o); intro.
          *
          apply beq_oid_equal in H39.
          rewrite <- H39 in H23. 
          assert (Some (Heap_OBJ cls0 F0 lo' ll)
            = lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls0 F0 lo' ll)) fo1).
          apply lookup_updated with h1 (Heap_OBJ cls0 F0 lb ll); auto.
          rewrite H39; auto.
    
          case_eq (beq_oid fo2 o0); intro.
          **
          apply beq_oid_equal in H41.
          rewrite <- H41 in H24. 
          assert (Some (Heap_OBJ cls3 F3 lo' ll)
            = lookup_heap_obj (update_heap_obj h2 o0 (Heap_OBJ cls3 F3 lo' ll)) fo2).
          apply lookup_updated with h2 (Heap_OBJ cls3 F3 lb ll); auto.
          rewrite H41; auto.
    
          exists cls0. exists cls3.
          exists lo'. exists lo'.
          exists F0. exists F3.
          exists ll. exists ll. 

          split; auto. split; auto.
          subst; auto. left; auto. 
          **
            (* if fo1 = o, then fo2 must be equal to o2*)
            subst; auto.
            destruct H38. rewrite H27 in H22; inversion H22; subst; auto.
            pose proof (beq_oid_same o0).
            try (inconsist).
          *
            (* beq_oid fo1 o = false*)
            subst; auto.
            case_eq (beq_oid fo2 o0); intro.
          **
            (* inconsist assumption *)
            apply beq_oid_equal in H27.
            subst; auto.
            apply right_left in H15.
            destruct H38. 
            apply right_left in H27.
            rewrite H27 in H15.
            inversion H15; subst; auto. 
            pose proof (beq_oid_same o).    try (inconsist).
          **
            (* beq_oid fo2 o0 = false*)
            assert (Some (Heap_OBJ cls_f1 FF1 lof1 llf1) =
            lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls3 F0 lo' ll)) fo1 
           ).
            apply lookup_updated_not_affected with o (Heap_OBJ cls3 F0 lo' ll)  h1; auto.
            intro contra. rewrite contra in H39.
            pose proof (beq_oid_same o). try (inconsist).

            assert (Some (Heap_OBJ cls_f2 FF2 lof2 llf2) =
           lookup_heap_obj (update_heap_obj h2 o0  (Heap_OBJ cls3 F3 lo' ll)) fo2
           ).
            apply lookup_updated_not_affected with o0 (Heap_OBJ cls3 F3 lo' ll) h2; auto.
            intro contra. rewrite contra in H27.
            pose proof (beq_oid_same o0). try (inconsist).

            exists cls_f1. exists cls_f2.
            exists lof1. exists lof2.
            exists FF1. exists FF2.
            exists llf1. exists llf2.   
            split; auto.
            ++++++
              (* fields are both H *)
              case_eq (beq_oid fo1 o); intro.
            (*inconsistency fo1 and o cannot equal*)
            apply beq_oid_equal in H39.
            rewrite <- H39 in H23. 
            assert (Some (Heap_OBJ cls0 F0 lo' ll)
            = lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls0 F0 lo' ll)) fo1).
            apply lookup_updated with h1 (Heap_OBJ cls0 F0 lb ll); auto.
            rewrite H39; auto.
            subst; auto.
            rewrite H36 in H23; inversion H23; subst; auto.
            destruct H38. 
            try (inconsist).
    
            case_eq (beq_oid fo2 o0); intro.
            *
            (*inconsistency fo2 and o0 cannot equal*)
            apply beq_oid_equal in H40.
            subst; auto. 
            rewrite H37 in H24; inversion H24; subst; auto.
            destruct H38.  
            try (inconsist).
            *
              (* fo1 <> o and fo2 <> o0 *)
              assert (Some (Heap_OBJ cls_f1 FF1 lof1 llf1) =
                      lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls0 F0 lo' ll)) fo1 
                     ).
              apply lookup_updated_not_affected with o (Heap_OBJ cls0 F0 lo' ll)  h1; auto.
              intro contra. rewrite contra in H39.
              pose proof (beq_oid_same o). try (inconsist).
              assert (Some (Heap_OBJ cls_f2 FF2 lof2 llf2) =
                      lookup_heap_obj (update_heap_obj h2 o0  (Heap_OBJ cls3 F3 lo' ll)) fo2
                     ).
              apply lookup_updated_not_affected with o0 (Heap_OBJ cls3 F3 lo' ll)  h2; auto.
              intro contra. rewrite contra in H40.
              pose proof (beq_oid_same o0). try (inconsist).
    
              exists cls_f1. exists cls_f2. exists lof1. exists lof2.
              exists FF1.              exists FF2.
              exists llf1. exists llf2. 
              split; auto.
              +++++
                destruct H27. 
                eauto using object_equal_H.
              ++++    

                (* (beq_oid o1 o) = true and beq_oid o2 o0 = false *)
                rewrite H15 in H22; inversion H22; subst; auto.
                assert (beq_oid o2 o2 = true). apply beq_oid_same.
                try (inconsist).
              +++
                (*beq_oid o1 o = false *)    
                assert ( Some (Heap_OBJ cls0 F0 lb ll)  =
                         lookup_heap_obj  (update_heap_obj h1 o (Heap_OBJ cls1 F1 lo' ll1))  o1).
                apply lookup_updated_not_affected with o (Heap_OBJ cls1 F1 lo' ll1) h1; auto.
                intro contra. rewrite contra in H28.
                assert (beq_oid o o = true). apply beq_oid_same.
                try (inconsist).
                case_eq (beq_oid o2 o0); intro.
                *
                  (* cannot happen *)
                  apply beq_oid_equal in H30.
                  subst; auto.
                  apply right_left in H15.
                  apply right_left in H22.
                  rewrite H22 in H15. inversion H15; subst; auto.
                  assert (beq_oid o o = true). apply beq_oid_same.
                  try (inconsist).
                *
                  assert ( Some (Heap_OBJ cls3 F3 lb ll)  =
                           lookup_heap_obj  (update_heap_obj h2 o0 (Heap_OBJ cls2 F2 lo' ll1))  o2).
                  apply lookup_updated_not_affected with o0 (Heap_OBJ cls2 F2 lo' ll1) h2; auto.
                  intro contra. rewrite contra in H30.
                  pose proof (beq_oid_same o0). try (inconsist).

                  apply object_equal_L with lb cls0 cls3
                              F0 F3 ll
                              ; auto.
                  destruct H27. destruct H32. destruct H33.  
                  split; auto. split; auto.
                  split; auto.
                  intros.
                  destruct H34 with fname fo1 fo2; auto. rename x into cls_f1.
                  destruct H37 as [cls_f2]. destruct H37 as [lof1].
                  destruct H37 as [lof2]. destruct H37 as [FF1]. destruct H37 as [FF2].
                  destruct H37 as [llf1]. destruct H37 as [llf2]. 
                  destruct H37. destruct H38.  destruct H39. 

                  **
                    (* fields are both L *)
                    case_eq (beq_oid fo1 o); intro.
                    apply beq_oid_equal in H40.
                    subst; auto. 
                    assert (Some (Heap_OBJ cls1 F1 lo' ll1)
                            = lookup_heap_obj (update_heap_obj h1 o  (Heap_OBJ cls1 F1 lo' ll1)) o).
                    apply lookup_updated with h1 (Heap_OBJ cls_f1 FF1 lof1 llf1); auto.
                    
                    case_eq (beq_oid fo2 o0); intro.
                    apply beq_oid_equal in H40.
                    subst; auto. 
                    assert (Some (Heap_OBJ cls2 F2 lo' ll1)
                            = lookup_heap_obj (update_heap_obj h2 o0 (Heap_OBJ cls2 F2 lo' ll1)) o0).
                    apply lookup_updated with h2 (Heap_OBJ cls2 F2 lo1 ll1); auto.
                    
                    exists cls1. exists cls2. exists lo'. exists lo'.
                    exists F1.
                    exists F2.
                    exists ll1. exists ll1. 
                    split; auto. split; auto.
                    left; auto. split; auto.
                    split; auto. split; auto. 
                    rewrite H38 in H19; inversion H19; subst; auto.
                    rewrite H37 in H16; inversion H16; subst; auto.
                    apply H39. 

                    (* beq_oid fo2 o0 = false*)

                    assert (Some (Heap_OBJ cls_f2 FF2 lof2 llf2) =
                            lookup_heap_obj (update_heap_obj h2 o0  (Heap_OBJ cls2 F2 lo' ll1)) fo2
                           ).
                    apply lookup_updated_not_affected with o0 (Heap_OBJ cls2 F2 lo' ll1)  h2; auto.
                    intro contra. rewrite contra in H38.
                    pose proof (beq_oid_same o0). subst; auto. try (inconsist).

                    destruct H39. rewrite H39 in H15; inversion H15; subst; auto.
                    pose proof (beq_oid_same o0). subst; auto. try (inconsist).

                    (* beq_oid fo1 o = false *)
                    subst; auto.
                    case_eq (beq_oid fo2 o0); intro.
                    
                    (* inconsist assumption *)
                    apply beq_oid_equal in H27.
                    subst; auto.
                    apply right_left in H15.
                    destruct H39.
                    
                    apply right_left in H27.
                    rewrite H27 in H15.
                    inversion H15; subst; auto. 
                    pose proof (beq_oid_same o).
                    try (inconsist).

                    (* beq_oid fo1 o = false /\ beq_oid fo2 o0 = false*)

                    assert (Some (Heap_OBJ cls_f2 FF2 lof2 llf2) =
                            lookup_heap_obj (update_heap_obj h2 o0 (Heap_OBJ cls2 F2 lo' ll1)) fo2
                           ).
                    apply lookup_updated_not_affected with o0 (Heap_OBJ cls2 F2 lo' ll1) h2; auto.
                    intro contra. rewrite contra in H27.
                    pose proof (beq_oid_same o0). try (inconsist).

                    assert (Some (Heap_OBJ cls_f1 FF1 lof1 llf1) =
                            lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls1 F1 lo' ll1)) fo1 
                           ).
                    apply lookup_updated_not_affected with o (Heap_OBJ cls1 F1 lo' ll1)  h1; auto.
                    intro contra. rewrite contra in H40.
                    pose proof (beq_oid_same o). try (inconsist).

                    exists cls_f1. exists cls_f2.
                    exists lof1. exists lof2.
                    exists FF1. exists FF2.
                    exists llf1. exists llf2.  
                    split; auto.

                  **
                    (* fields are both H *)
                    case_eq (beq_oid fo1 o); intro.
                    ***
                    (*inconsistency fo1 and o cannot equal*)
                    apply beq_oid_equal in H40.
                    subst; auto.
                    rewrite H37 in H16; inversion H16; subst; auto.
                    destruct H39. try (inconsist).
                    ***
                      
                    (*beq_oid fo1 o = false *)
                    assert (Some (Heap_OBJ cls_f1 FF1 lof1 llf1) =
                            lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls1 F1 lo' ll1)) fo1 
                           ).
                    apply lookup_updated_not_affected with o (Heap_OBJ cls1 F1 lo' ll1)  h1; auto.
                    intro contra. rewrite contra in H40.
                    pose proof (beq_oid_same o). try (inconsist).
                    
                    case_eq (beq_oid fo2 o0); intro.
                    ****
                    (*inconsistency fo2 and o0 cannot equal*)
                    apply beq_oid_equal in H42.
                    subst; auto. 
                    rewrite H38 in H19; inversion H19; subst; auto.
                    destruct H39. try (inconsist).

                    ****
                    (* only the case fo1 <> o and fo2 <> o0 is feasible  *)
                    assert (Some (Heap_OBJ cls_f2 FF2 lof2 llf2) =
                            lookup_heap_obj (update_heap_obj h2 o0  (Heap_OBJ cls2 F2 lo' ll1)) fo2
                           ).
                    apply lookup_updated_not_affected with o0 (Heap_OBJ cls2 F2 lo' ll1)  h2; auto.
                    intro contra. rewrite contra in H42.
                    pose proof (beq_oid_same o0). try (inconsist).
                    
                    exists cls_f1. exists cls_f2. exists lof1. exists lof2.
                    exists FF1.
                    exists FF2.
                    exists llf1. exists llf2.  
                    split; auto.

    +
      (* None -> left φ o1 = None *)
      intros. 
      intros. apply lookup_updated_heap_must_none in H22.
      apply H14 in H22; auto.
      
    + (* o1 = None -> right φ o1 = None *)
      intros. apply lookup_updated_heap_must_none in H22.
      apply H18 in H22; auto.

    + (* flow_to (join_label lb ll) L_Label = false  *)
      intros.
      case_eq (beq_oid o1 o); intro.
      assert ( Some (Heap_OBJ cls F lb ll) = lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls1 F1 lo' ll1)) o1 ). auto.
      apply lookup_updated_heap_new_obj in H25; auto.
      inversion H25; subst; auto.
      try (inconsist).
    
      assert (Some (Heap_OBJ cls F lb ll) =
            lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls1 F1 lo' ll1)) o1
           ). auto.
      apply lookup_updated_heap_old_obj in H25; auto.
      assert ( lookup_heap_obj h1 o1 = Some (Heap_OBJ cls F lb ll) ); auto.
      apply H20 in H26; auto. 

    + (*flow_to lb L_Label = false -> right φ o1 = None *)
      intros.
      case_eq (beq_oid o1 o0); intro.
      assert ( Some (Heap_OBJ cls F lb ll) = lookup_heap_obj (update_heap_obj h2 o0 (Heap_OBJ cls2 F2 lo' ll1)) o1 ). auto.
      apply lookup_updated_heap_new_obj in H25; auto.
      inversion H25; subst; auto. try (inconsist).
    
      assert (Some (Heap_OBJ cls F lb ll) =
            lookup_heap_obj (update_heap_obj h2 o0 (Heap_OBJ cls2 F2 lo' ll1)) o1
           ). auto.
      apply lookup_updated_heap_old_obj in H25; auto.
      assert ( lookup_heap_obj h2 o1 = Some (Heap_OBJ cls F lb ll) ); auto.
      apply H21 in H26; auto.

      (* flow_to ll1 L_Label = false /\ flow_to lo1 L_Label = false  /\ flow_to lo2 L_Label = false*) 
  - 
    rewrite <- H15 in H4; inversion H4; subst; auto.
    rewrite <- H16 in H5; inversion H5; subst; auto.
    inversion H3; subst; auto. 
    apply  L_eq_heap; auto.
    + intros. assert ( L_equivalence_object o1 h1 o2 h2 φ). 
      apply H13; auto.  inversion H23; subst; auto.
      case_eq (beq_oid o1 o); intro.
      (*impossible*)
      ++
        apply beq_oid_equal in H28.
        rewrite H28 in H24.
        rewrite <- H24 in H15; inversion H15; subst; auto.
        try (inconsist).
      ++
        case_eq (beq_oid o2 o0); intro.
        apply beq_oid_equal in H29.
        rewrite H29 in H25.
        rewrite <- H25 in H16; inversion H16; subst; auto.
        try (inconsist).

        assert (Some (Heap_OBJ cls3 F0 lb ll) =
            lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls1 F1 lo' ll1)) o1
           ).
        apply lookup_updated_not_affected with o (Heap_OBJ cls1 F1 lo' ll1)  h1; auto.
        intro contra; subst; auto. pose proof (beq_oid_same o); try (inconsist).
        assert (Some (Heap_OBJ cls3 F3 lb ll) =
            lookup_heap_obj (update_heap_obj h2 o0 (Heap_OBJ cls2 F2 lo' ll2)) o2
             ).
        apply lookup_updated_not_affected with o0 (Heap_OBJ cls2 F2 lo' ll2)  h2; auto.
        intro contra; subst; auto. pose proof (beq_oid_same o0); try (inconsist).
        apply object_equal_H with lb cls3 cls3 F0 F3 ll; auto. 
        
      ++
        destruct H28. destruct H29. destruct H30.
        case_eq (beq_oid o1 o); intro.
      (*impossible*)
        *
        apply beq_oid_equal in H32.
        rewrite H32 in H24.
        rewrite <- H24 in H15; inversion H15; subst; auto.
        try (inconsist).
        *
        case_eq (beq_oid o2 o0); intro.
        apply beq_oid_equal in H33.
        rewrite H33 in H25.
        rewrite <- H25 in H16; inversion H16; subst; auto.
        try (inconsist).

        assert (Some (Heap_OBJ cls0 F0 lb ll) =
            lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls1 F1 lo' ll1)) o1
           ).
        apply lookup_updated_not_affected with o (Heap_OBJ cls1 F1 lo' ll1)  h1; auto.
        intro contra; subst; auto. pose proof (beq_oid_same o); try (inconsist).
        assert (Some (Heap_OBJ cls3 F3 lb ll) =
            lookup_heap_obj (update_heap_obj h2 o0 (Heap_OBJ cls2 F2 lo' ll2)) o2
             ).
        apply lookup_updated_not_affected with o0 (Heap_OBJ cls2 F2 lo' ll2)  h2; auto.
        intro contra; subst; auto. pose proof (beq_oid_same o0); try (inconsist).
        apply object_equal_L with lb cls0 cls3 F0 F3 ll; auto. 
        split; auto. split; auto. split; auto.  
        intros.
        destruct H31 with fname fo1 fo2; auto.
        destruct H38 as [cls_f2]. rename x into cls_f1.
        destruct H38 as [lof1]. destruct H38 as [lof2].
        destruct H38 as [FF1]. destruct H38 as [FF2].
        destruct H38 as [llf1]. destruct H38 as [llf2]. 
        destruct H38. destruct H39. destruct H40.
        **
          case_eq (beq_oid fo1 o); intro.
          apply beq_oid_equal in H41.
          rewrite H41 in H38. rewrite H38 in H15; inversion H15; subst; auto.
          destruct H40. destruct H40. destruct H41. destruct H41.  
          try (inconsist).
          
          case_eq (beq_oid fo2 o0); intro.
          apply beq_oid_equal in H42.
          rewrite H42 in H39. rewrite H39 in H16; inversion H16; subst; auto.
          destruct H40. destruct H40. destruct H42. destruct H42. 
          try (inconsist).

          assert (Some  (Heap_OBJ cls_f1 FF1 lof1 llf1) =
                  lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls1 F1 lo' ll1)) fo1
                 ).
          apply lookup_updated_not_affected with o (Heap_OBJ cls1 F1 lo' ll1)   h1; auto.
          intro contra. subst; auto. pose proof (beq_oid_same o). try (inconsist).
          
          assert (Some  (Heap_OBJ cls_f2 FF2 lof2 llf2) =
                  lookup_heap_obj (update_heap_obj h2 o0 (Heap_OBJ cls2 F2 lo' ll2)) fo2
                 ).
          apply lookup_updated_not_affected with o0 (Heap_OBJ cls2 F2 lo' ll2) h2; auto.
          intro contra. subst; auto. pose proof (beq_oid_same o0). try (inconsist).         

          exists cls_f1. exists cls_f2.
          exists lof1. exists lof2.
          exists FF1. exists FF2.
          exists llf1. exists llf2. 
          split; auto.  
        **
          subst; auto.
          case_eq (beq_oid fo1 o); intro.
          apply beq_oid_equal in H28.
          subst; auto.
          assert (Some (Heap_OBJ cls1 F1 lo' ll1)  =
                  lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls1 F1 lo' ll1)) o).
          apply lookup_updated with h1 (Heap_OBJ cls_f1 FF1 lof1 llf1); auto.
          ***
          case_eq (beq_oid fo2 o0); intro.
          apply beq_oid_equal in H41.
          ****
          subst; auto. 
          assert (Some (Heap_OBJ cls2 F2 lo' ll2)  =
                  lookup_heap_obj (update_heap_obj h2 o0 (Heap_OBJ cls2 F2 lo' ll2)) o0).
          apply lookup_updated with h2 (Heap_OBJ cls_f2 FF2 lof2 llf2); auto.
          
          exists cls1. exists cls2.
          exists lo'. exists lo'.
          exists F1. exists F2.
          exists ll1. exists ll2. 
          split; auto.
          ****
          assert (Some (Heap_OBJ cls_f2 FF2 lof2 llf2)  =
                  lookup_heap_obj (update_heap_obj h2 o0 (Heap_OBJ cls2 F2 lo' ll2)) fo2).
          apply lookup_updated_not_affected with o0 (Heap_OBJ cls2 F2 lo' ll2) h2; auto.
          intro contra. subst; auto. pose proof (beq_oid_same o0). try (inconsist).        
          exists cls1. exists cls_f2.
          exists lo'. exists lof2.
          exists F1. exists FF2.
          exists ll1. exists llf2. 
          split; auto. split; auto.
          rewrite H38 in H15; inversion H15; subst; auto.

          ***
            (* beq_oid fo1 o = false *)
            assert (Some  (Heap_OBJ cls_f1 FF1 lof1 llf1) =
              lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls1 F1 lo' ll1)) fo1).
            apply lookup_updated_not_affected with o (Heap_OBJ cls1 F1 lo' ll1) h1; auto.
            intro contra. subst; auto. pose proof (beq_oid_same o). try (inconsist).        
      
            case_eq (beq_oid fo2 o0); intro.
            ****
            apply beq_oid_equal in H42.      
            subst; auto. 
            assert (Some (Heap_OBJ cls2 F2 lo' ll2)  =
                    lookup_heap_obj (update_heap_obj h2 o0 (Heap_OBJ cls2 F2 lo' ll2)) o0).
            apply lookup_updated with h2 (Heap_OBJ cls_f2 FF2 lof2 llf2); auto.
            
            exists cls_f1. exists cls2.
            exists lof1. exists lo'.
            exists FF1. exists F2.
            exists llf1. exists ll2. 
            split; auto. split; auto.             
            rewrite H39 in H16; inversion H16; subst; auto.
            ****
              assert (Some (Heap_OBJ cls_f2 FF2 lof2 llf2)  =
              lookup_heap_obj (update_heap_obj h2 o0 (Heap_OBJ cls2 F2 lo' ll2)) fo2).
              apply lookup_updated_not_affected with o0 (Heap_OBJ cls2 F2 lo' ll2) h2; auto.
              intro contra. subst; auto. pose proof (beq_oid_same o0). try (inconsist).        

              exists cls_f1. exists cls_f2.
              exists lof1. exists lof2.
              exists FF1. exists FF2.
              exists llf1. exists llf2.   
              split; auto. 
    + intros.
      apply lookup_updated_heap_must_none in H22.
      apply H14 in H22; auto. 
    + intros. 
      apply lookup_updated_heap_must_none in H22.
      apply H18 in H22; auto.

    + intros.
      case_eq (beq_oid o1 o); intro.
      ++ 
      apply  beq_oid_equal in H24.
      rewrite <- H24 in H15.
      destruct H20 with o1 cls1 F1 lo1 ll1; auto.
      ++
      assert (Some (Heap_OBJ cls F lb ll) =
              lookup_heap_obj h1 o1
             ).
      apply lookup_updated_heap_old_obj with  cls1 F1 lo' o ll1; auto.
      destruct H20 with o1 cls F lb ll; auto. 

    + intros.
      case_eq (beq_oid o1 o0); intro.
      ++
        apply  beq_oid_equal in H24.
        rewrite <- H24 in H16.
        destruct H21 with o1 cls2 F2 lo2 ll2; auto.
      ++
      assert (Some (Heap_OBJ cls F lb ll) =
              lookup_heap_obj h2 o1
             ).
      apply lookup_updated_heap_old_obj with  cls2 F2 lo' o0 ll2; auto.
      destruct H21 with o1 cls F lb ll; auto. 
Qed. Hint Resolve change_obj_preserve_bijection.

Check change_obj_preserve_bijection.

(*
  (* heap bijection preservation *)
Lemma lbl_L_change_obj_both_lbl_preserve_bijection : forall  ct h1 h2 φ lo lo0 lo' F F0 o o0 lb1 lb2 cls cls0 ll ll0,
    flow_to (join_label lo' ll) L_Label = true ->
    wfe_heap ct h1 -> field_wfe_heap ct h1 ->
    wfe_heap ct h2 -> field_wfe_heap ct h2 ->  
    L_equivalence_heap h1 h2 φ ->
    Some (Heap_OBJ cls F lo ll) = lookup_heap_obj h1 o ->
    Some (Heap_OBJ cls0 F0 lo0 ll0) = lookup_heap_obj h2 o0 ->
    L_equivalence_tm (ObjId o) h1 (ObjId o0) h2 φ ->
    flow_to lb1 L_Label = true ->
    flow_to lb2 L_Label = true ->
    flow_to lb1 ll = true ->
    flow_to lb2 ll0 = true ->
    flow_to lo lo' = true ->
    flow_to lo0 lo' = true ->
      L_equivalence_heap
        (update_heap_obj h1 o (Heap_OBJ cls F lo' ll))
        (update_heap_obj h2 o0 (Heap_OBJ cls0 F0 lo' ll0)) φ.
    
Proof with eauto.
  intros ct h1 h2 φ lo lo0 lo' F F0 o o0 lb1 lb2 cls cls0 ll ll0.
  intros.   
  inversion H7; subst; auto.
  rewrite <- H17 in H5; inversion H5; subst; auto.
  rewrite <- H21 in H6; inversion H6; subst; auto.

  inversion H4; subst; auto.
  apply  L_eq_heap; auto.
  
  - intros.
    assert (L_equivalence_object o1 h1 o2 h2 φ) as H_eq_o1_o2.          
    apply H14; auto. 
    inversion H_eq_o1_o2; subst; auto. 
    case_eq (beq_oid o1 o); intro.
    apply beq_oid_equal in H31.
    rewrite H31 in H25. rewrite <- H25 in H17; inversion H17; subst.
    assert ( Some  (Heap_OBJ cls0 F0 lo' ll)  =
      lookup_heap_obj  (update_heap_obj h1 o (Heap_OBJ cls0 F0 lo' ll))  o).
    apply lookup_updated with h1  (Heap_OBJ cls0 F0 lb0 ll ); auto.

    case_eq (beq_oid o2 o0); intro.
    apply beq_oid_equal in H32.
    rewrite H32 in H26. rewrite <- H26 in H21; inversion H21; subst; auto.  

    assert ( Some  (Heap_OBJ cls3 F3 lo' ll)  =
      lookup_heap_obj  (update_heap_obj h2 o0 (Heap_OBJ cls3 F3 lo' ll))  o0).
    apply lookup_updated with h2  (Heap_OBJ cls3 F3 lb3 ll); auto.
    apply object_equal_L with lo' lo' cls0 cls3
                              F0 F3 ll
    ; auto.

    apply flow_dist in H; apply H; auto.
    apply flow_dist in H; apply H; auto.

    destruct H30. destruct H33. destruct H34. destruct H35 as [tmp]. 
    split; auto. split; auto. split; auto. 
    split; auto. 
    intros.

    destruct H35 with fname fo1 fo2; auto. rename x into cls_f1.
    destruct H38 as [cls_f2]. destruct H38 as [lof1].
    destruct H38 as [lof2]. destruct H38 as [FF1]. destruct H38 as [FF2].
    destruct H38 as [llf1]. destruct H38 as [llf2].
    destruct H38. destruct H39.  destruct H40. 

    (* fields are both L *)
    case_eq (beq_oid fo1 o); intro.
    apply beq_oid_equal in H41.
    rewrite <- H41 in H25. 
    assert (Some (Heap_OBJ cls0 F0 lo' ll)
            = lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls0 F0 lo' ll)) fo1).
    apply lookup_updated with h1 (Heap_OBJ cls0 F0 lb3 ll); auto.
    rewrite H41; auto.

    
    case_eq (beq_oid fo2 o0); intro.
    apply beq_oid_equal in H43.
    rewrite <- H43 in H26. 
    assert (Some (Heap_OBJ cls3 F3 lo' ll)
            = lookup_heap_obj (update_heap_obj h2 o0 (Heap_OBJ cls3 F3 lo' ll)) fo2).
    apply lookup_updated with h2 (Heap_OBJ cls3 F3 lb3 ll); auto.
    rewrite H43. auto.
    
    exists cls0. exists cls3. exists lo'. exists lo'.
    exists F0.
    exists F3.
    exists ll. exists ll. 
    split; auto. split; auto.
    subst; auto. left; auto.
    split; auto.
    apply flow_dist in H; destruct H; auto.


    (* if fo1 = o, then fo2 must be equal to o2*)
    subst; auto.
    destruct H40. rewrite H30 in H24; inversion H24; subst; auto.
    pose proof (beq_oid_same o0).
    try (inconsist).

    (* beq_oid fo1 o = false*)
    subst; auto.
    case_eq (beq_oid fo2 o0); intro.
    
    (* inconsist assumption *)
    apply beq_oid_equal in H30.
    subst; auto.
    apply right_left in H16.
    destruct H40. 
    apply right_left in H30.
    rewrite H30 in H16.
    inversion H16; subst; auto. 
    pose proof (beq_oid_same o).
    try (inconsist).

    (* beq_oid fo2 o0 = false*)
    assert (Some (Heap_OBJ cls_f1 FF1 lof1 llf1) =
            lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls3 F0 lo' ll)) fo1 
           ).
    apply lookup_updated_not_affected with o (Heap_OBJ cls3 F0 lo' ll)  h1; auto.

    assert (Some (Heap_OBJ cls_f2 FF2 lof2 llf2) =
           lookup_heap_obj (update_heap_obj h2 o0  (Heap_OBJ cls3 F3 lo' ll)) fo2
           ).
    apply lookup_updated_not_affected with o0 (Heap_OBJ cls3 F3 lo' ll) h2; auto.

    exists cls_f1. exists cls_f2.
    exists lof1. exists lof2.
    exists FF1. exists FF2.
    exists llf1. exists llf2. 
    split; auto.


(* fields are both H *)
    case_eq (beq_oid fo1 o); intro.
    (*inconsistency fo1 and o cannot equal*)
    apply beq_oid_equal in H41.
    rewrite <- H41 in H25. 
    assert (Some (Heap_OBJ cls0 F0 lo' ll)
            = lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls0 F0 lo' ll)) fo1).
    apply lookup_updated with h1 (Heap_OBJ cls0 F0 lb3 ll); auto.
    rewrite H41. auto.
    subst; auto.
    rewrite H38 in H25; inversion H25; subst; auto.
    destruct H40.
    assert (flow_to (join_label lof1 llf1) L_Label = true). apply join_L_label_flow_to_L; auto. 
    try (inconsist).
    
    case_eq (beq_oid fo2 o0); intro.
    (*inconsistency fo2 and o0 cannot equal*)
    apply beq_oid_equal in H42.
    subst; auto. 
    rewrite H39 in H26; inversion H26; subst; auto.
    destruct H40.
    assert (flow_to (join_label lof2 llf2) L_Label = true). apply join_L_label_flow_to_L; auto. try (inconsist).

    (* fo1 <> o and fo2 <> o0 *)
    assert (Some (Heap_OBJ cls_f1 FF1 lof1 llf1) =
            lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls0 F0 lo' ll)) fo1 
           ).
    apply lookup_updated_not_affected with o (Heap_OBJ cls0 F0 lo' ll)  h1; auto.

    assert (Some (Heap_OBJ cls_f2 FF2 lof2 llf2) =
           lookup_heap_obj (update_heap_obj h2 o0  (Heap_OBJ cls3 F3 lo' ll)) fo2
           ).
    apply lookup_updated_not_affected with o0 (Heap_OBJ cls3 F3 lo' ll)  h2; auto.

    
    exists cls_f1. exists cls_f2. exists lof1. exists lof2.
    exists FF1.
    exists FF2.
    exists llf1. exists llf2. 
    split; auto.

    assert (Some (Heap_OBJ cls3 F3 lb3 ll) =
           lookup_heap_obj (update_heap_obj h2 o0 (Heap_OBJ cls2 F2 lo' ll)) o2
           ).
    apply lookup_updated_not_affected with o0 (Heap_OBJ cls2 F2 lo' ll) h2; auto.    

    (* (beq_oid o1 o) = true and beq_oid o2 o0 = false *)
    apply object_equal_L with lo' lb3 cls0 cls3
                              F0 F3 ll; auto.
    apply flow_dist in H; destruct H; auto.

    destruct H30. destruct H34. destruct H35. destruct H36 as [tmp].
    rewrite H24 in H16; inversion H16; subst; auto.
    assert ( beq_oid o0 o0 = true). apply beq_oid_same. try (inconsist).
    
    (*beq_oid o1 o = false *)
    
    assert ( Some (Heap_OBJ cls0 F0 lb0 ll)  =
      lookup_heap_obj  (update_heap_obj h1 o (Heap_OBJ cls1 F1 lo' ll1))  o1).
    apply lookup_updated_not_affected with o (Heap_OBJ cls1 F1 lo' ll1) h1; auto.

    case_eq (beq_oid o2 o0); intro.
    (* cannot happen *)
    apply beq_oid_equal in H33.
    subst; auto.
    apply right_left in H16.
    apply right_left in H24.
    rewrite H24 in H16. inversion H16; subst; auto.
    assert (beq_oid o o = true). apply beq_oid_same.
    try (inconsist).

    assert ( Some (Heap_OBJ cls3 F3 lb3 ll)  =
      lookup_heap_obj  (update_heap_obj h2 o0 (Heap_OBJ cls2 F2 lo' ll1))  o2).
    apply lookup_updated_not_affected with o0 (Heap_OBJ cls2 F2 lo' ll1) h2; auto.

    
    apply object_equal_L with lb0 lb3 cls0 cls3
                              F0 F3 ll
                              ; auto.
    destruct H30. destruct H35. destruct H36. destruct H37 as [tmp].
    split; auto. split; auto.
    split; auto. split; auto. 
    intros.

    destruct H37 with fname fo1 fo2; auto. rename x into cls_f1.
    destruct H40 as [cls_f2]. destruct H40 as [lof1].
    destruct H40 as [lof2]. destruct H40 as [FF1]. destruct H40 as [FF2].
    destruct H40 as [llf1]. destruct H40 as [llf2].
    destruct H40. destruct H41.  destruct H42. 

    (* fields are both L *)
    case_eq (beq_oid fo1 o); intro.
    apply beq_oid_equal in H43.
    subst; auto. 
    assert (Some (Heap_OBJ cls1 F1 lo' ll1)
            = lookup_heap_obj (update_heap_obj h1 o  (Heap_OBJ cls1 F1 lo' ll1)) o).
    apply lookup_updated with h1 (Heap_OBJ cls_f1 FF1 lof1 llf1); auto.
    
    case_eq (beq_oid fo2 o0); intro.
    apply beq_oid_equal in H35.
    subst; auto. 
    assert (Some (Heap_OBJ cls2 F2 lo' ll1)
            = lookup_heap_obj (update_heap_obj h2 o0 (Heap_OBJ cls2 F2 lo' ll1)) o0).
    apply lookup_updated with h2 (Heap_OBJ cls2 F2 lo1 ll1); auto.
    
    exists cls1. exists cls2. exists lo'. exists lo'.
    exists F1.
    exists F2.
    exists ll1. exists ll1. 
    split; auto. split; auto.
    left; auto. split; auto.
    apply flow_dist in H; destruct H; auto.
    split; auto. split; auto. split; auto. split; auto. 
    rewrite H40 in H17; inversion H17; subst; auto.
    rewrite H41 in H21; inversion H21; subst; auto.
    apply H42. 

    (* beq_oid fo2 o0 = false*)

    assert (Some (Heap_OBJ cls_f2 FF2 lof2 llf2) =
           lookup_heap_obj (update_heap_obj h2 o0  (Heap_OBJ cls2 F2 lo' ll1)) fo2
           ).
    apply lookup_updated_not_affected with o0 (Heap_OBJ cls2 F2 lo' ll1) h2; auto.
    
    exists cls1. exists cls_f2.
    exists lo'. exists lof2.
    exists F1. exists FF2.
    exists ll1. exists llf2.  
    split; auto. split; auto.
    left; auto.
    split; auto. apply H42.
    split; auto. apply H42.
    split; auto.
    apply flow_dist in H; destruct H; auto.
    rewrite H40 in H17;inversion H17; subst; auto.
    apply H42.

    (* beq_oid fo1 o = false *)
    subst; auto.
    case_eq (beq_oid fo2 o0); intro.
    
    (* inconsist assumption *)
    apply beq_oid_equal in H30.
    subst; auto.
    apply right_left in H16.
    destruct H42.
     
    apply right_left in H30.
    rewrite H30 in H16.
    inversion H16; subst; auto. 
    pose proof (beq_oid_same o).
    try (inconsist).

    (* beq_oid fo2 o0 = false*)

    assert (Some (Heap_OBJ cls_f2 FF2 lof2 llf2) =
           lookup_heap_obj (update_heap_obj h2 o0 (Heap_OBJ cls2 F2 lo' ll1)) fo2
           ).
    apply lookup_updated_not_affected with o0 (Heap_OBJ cls2 F2 lo' ll1) h2; auto.

    assert (Some (Heap_OBJ cls_f1 FF1 lof1 llf1) =
            lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls1 F1 lo' ll1)) fo1 
           ).
    apply lookup_updated_not_affected with o (Heap_OBJ cls1 F1 lo' ll1)  h1; auto.

    exists cls_f1. exists cls_f2.
    exists lof1. exists lof2.
    exists FF1. exists FF2.
    exists llf1. exists llf2. 
    split; auto.



(* fields are both H *)
    case_eq (beq_oid fo1 o); intro.
    (*inconsistency fo1 and o cannot equal*)
    apply beq_oid_equal in H43.
    subst; auto.
    rewrite H40 in H17; inversion H17; subst; auto.
    destruct H42.
    assert (flow_to (join_label lof1 llf1) L_Label = true). apply join_L_label_flow_to_L; auto. try(inconsist).

    (*beq_oid fo1 o = false *)
    assert (Some (Heap_OBJ cls_f1 FF1 lof1 llf1) =
            lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls1 F1 lo' ll1)) fo1 
           ).
    apply lookup_updated_not_affected with o (Heap_OBJ cls1 F1 lo' ll1)  h1; auto.
    
    case_eq (beq_oid fo2 o0); intro.
    (*inconsistency fo2 and o0 cannot equal*)
    apply beq_oid_equal in H45.
    subst; auto. 
    rewrite H41 in H21; inversion H21; subst; auto.
    destruct H42.
    assert (flow_to (join_label lof2 llf2) L_Label = true). apply join_L_label_flow_to_L; auto. try(inconsist).

    (* only the case fo1 <> o and fo2 <> o0 is feasible  *)
    assert (Some (Heap_OBJ cls_f2 FF2 lof2 llf2) =
           lookup_heap_obj (update_heap_obj h2 o0  (Heap_OBJ cls2 F2 lo' ll1)) fo2
           ).
    apply lookup_updated_not_affected with o0 (Heap_OBJ cls2 F2 lo' ll1)  h2; auto.
    
    exists cls_f1. exists cls_f2. exists lof1. exists lof2.
    exists FF1.
    exists FF2.
    exists llf1. exists llf2. 
    split; auto.

  - (* None -> left φ o1 = None *)
    intros. apply lookup_updated_heap_must_none in H24.
    apply H15 in H24. auto. 

  - (* o1 = None -> right φ o1 = None *)
    intros. apply lookup_updated_heap_must_none in H24.
    apply H20 in H24. auto.

  - (* flow_to lb L_Label = false  *)
    intros.
    case_eq (beq_oid o1 o); intro.
    assert ( Some (Heap_OBJ cls F lb ll) = lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls1 F1 lo' ll1)) o1 ). auto.
    apply lookup_updated_heap_new_obj in H27; auto.
    inversion H27; subst; auto.
    assert (flow_to (join_label lo' ll1) L_Label = true). apply join_L_label_flow_to_L; auto. try(inconsist).    try(inconsist).    
    
    assert (Some (Heap_OBJ cls F lb ll) =
            lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls1 F1 lo' ll1)) o1
           ). auto.
    apply lookup_updated_heap_old_obj in H27; auto.
    assert ( lookup_heap_obj h1 o1 = Some (Heap_OBJ cls F lb ll) ); auto.
    apply H22 in H28; auto. 

  - (*flow_to lb L_Label = false -> right φ o1 = None *)
    intros.
    case_eq (beq_oid o1 o0); intro.
    assert ( Some (Heap_OBJ cls F lb ll) = lookup_heap_obj (update_heap_obj h2 o0 (Heap_OBJ cls2 F2 lo' ll1)) o1 ). auto.
    apply lookup_updated_heap_new_obj in H27; auto.
    inversion H27; subst; auto.
    assert (flow_to (join_label lo' ll1) L_Label = true). apply join_L_label_flow_to_L; auto. try(inconsist).   try(inconsist).    
    
    assert (Some (Heap_OBJ cls F lb ll) =
            lookup_heap_obj (update_heap_obj h2 o0 (Heap_OBJ cls2 F2 lo' ll1)) o1
           ). auto.
    apply lookup_updated_heap_old_obj in H27; auto.
    assert ( lookup_heap_obj h2 o1 = Some (Heap_OBJ cls F lb ll) ); auto.
    apply H23 in H28; auto.

  - (*flow_to lo' L_Label = false *)
    rewrite <- H16 in H5. inversion H5; subst; auto.
    rewrite <- H18 in H6; inversion H6; subst; auto.
    apply flow_dist in H; destruct H; auto.
    case_eq (flow_to lb0 L_Label); intro.
    assert ( flow_to (join_label lb0 ll1) L_Label = true).
    apply join_L_label_flow_to_L ; auto. try (inconsist). 

    assert (flow_to lo' L_Label = false). eauto using flow_transitive.
    try (inconsist). 
Qed. Hint Resolve lbl_L_change_obj_both_lbl_preserve_bijection . 


(*
  (* heap bijection preservation *)
Lemma lbl_L_change_obj_both_lbl_preserve_bijection : forall  ct h1 h2 φ lo lo0 lo' F F0 o o0 lb1 lb2 cls cls0 ll ll0,
    flow_to lo' L_Label = true ->
    wfe_heap ct h1 -> field_wfe_heap ct h1 ->
    wfe_heap ct h2 -> field_wfe_heap ct h2 ->  
    L_equivalence_heap h1 h2 φ ->
    Some (Heap_OBJ cls F lo ll) = lookup_heap_obj h1 o ->
    Some (Heap_OBJ cls0 F0 lo0 ll0) = lookup_heap_obj h2 o0 ->
    L_equivalence_tm (ObjId o) h1 (ObjId o0) h2 φ ->
    flow_to lb1 L_Label = true ->
    flow_to lb2 L_Label = true ->
    flow_to lb1 ll = true ->
    flow_to lb2 ll0 = true ->
    flow_to lo lo' = true ->
    flow_to lo0 lo' = true ->
      L_equivalence_heap
        (update_heap_obj h1 o (Heap_OBJ cls F lo' ll))
        (update_heap_obj h2 o0 (Heap_OBJ cls0 F0 lo' ll0)) φ.
    
Proof with eauto.
  intros ct h1 h2 φ lo lo0 lo' F F0 o o0 lb1 lb2 cls cls0 ll ll0.
  intros.   
  inversion H7; subst; auto.
  rewrite <- H17 in H5; inversion H5; subst; auto.
  rewrite <- H21 in H6; inversion H6; subst; auto.

  inversion H4; subst; auto.
  apply  L_eq_heap; auto.
  
  - intros.
    assert (L_equivalence_object o1 h1 o2 h2 φ) as H_eq_o1_o2.          
    apply H14; auto. 
    inversion H_eq_o1_o2; subst; auto. 
    case_eq (beq_oid o1 o); intro.
    apply beq_oid_equal in H31.
    rewrite H31 in H25. rewrite <- H25 in H17; inversion H17; subst.
    assert ( Some  (Heap_OBJ cls0 F0 lo' ll)  =
      lookup_heap_obj  (update_heap_obj h1 o (Heap_OBJ cls0 F0 lo' ll))  o).
    apply lookup_updated with h1  (Heap_OBJ cls0 F0 lb0 ll ); auto.

    case_eq (beq_oid o2 o0); intro.
    apply beq_oid_equal in H32.
    rewrite H32 in H26. rewrite <- H26 in H21; inversion H21; subst; auto.  

    assert ( Some  (Heap_OBJ cls3 F3 lo' ll)  =
      lookup_heap_obj  (update_heap_obj h2 o0 (Heap_OBJ cls3 F3 lo' ll))  o0).
    apply lookup_updated with h2  (Heap_OBJ cls3 F3 lb3 ll); auto.
    apply object_equal_L with lo' lo' cls0 cls3
                              F0 F3 ll
                              ; auto.
    destruct H30. destruct H33. destruct H34. 
    split; auto. split; auto.
    split; auto. 
    intros.

    destruct H35 with fname fo1 fo2; auto. rename x into cls_f1.
    destruct H38 as [cls_f2]. destruct H38 as [lof1].
    destruct H38 as [lof2]. destruct H38 as [FF1]. destruct H38 as [FF2].
    destruct H38 as [llf1]. destruct H38 as [llf2].
    destruct H38. destruct H39.  destruct H40. 

    (* fields are both L *)
    case_eq (beq_oid fo1 o); intro.
    apply beq_oid_equal in H41.
    rewrite <- H41 in H25. 
    assert (Some (Heap_OBJ cls0 F0 lo' ll)
            = lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls0 F0 lo' ll)) fo1).
    apply lookup_updated with h1 (Heap_OBJ cls0 F0 lb3 ll); auto.
    rewrite H41; auto.

    
    case_eq (beq_oid fo2 o0); intro.
    apply beq_oid_equal in H43.
    rewrite <- H43 in H26. 
    assert (Some (Heap_OBJ cls3 F3 lo' ll)
            = lookup_heap_obj (update_heap_obj h2 o0 (Heap_OBJ cls3 F3 lo' ll)) fo2).
    apply lookup_updated with h2 (Heap_OBJ cls3 F3 lb3 ll); auto.
    rewrite H43. auto.
    
    exists cls0. exists cls3. exists lo'. exists lo'.
    exists F0.
    exists F3.
    exists ll. exists ll. 
    split; auto. split; auto.
    subst; auto. left; auto.
    split; auto. 

    (* if fo1 = o, then fo2 must be equal to o2*)
    subst; auto.
    destruct H40. rewrite H30 in H24; inversion H24; subst; auto.
    pose proof (beq_oid_same o0).
    try (inconsist).

    (* beq_oid fo1 o = false*)
    subst; auto.
    case_eq (beq_oid fo2 o0); intro.
    
    (* inconsist assumption *)
    apply beq_oid_equal in H30.
    subst; auto.
    apply right_left in H16.
    destruct H40. 
    apply right_left in H30.
    rewrite H30 in H16.
    inversion H16; subst; auto. 
    pose proof (beq_oid_same o).
    try (inconsist).

    (* beq_oid fo2 o0 = false*)
    assert (Some (Heap_OBJ cls_f1 FF1 lof1 llf1) =
            lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls3 F0 lo' ll)) fo1 
           ).
    apply lookup_updated_not_affected with o (Heap_OBJ cls3 F0 lo' ll)  h1; auto.

    assert (Some (Heap_OBJ cls_f2 FF2 lof2 llf2) =
           lookup_heap_obj (update_heap_obj h2 o0  (Heap_OBJ cls3 F3 lo' ll)) fo2
           ).
    apply lookup_updated_not_affected with o0 (Heap_OBJ cls3 F3 lo' ll) h2; auto.

    exists cls_f1. exists cls_f2.
    exists lof1. exists lof2.
    exists FF1. exists FF2.
    exists llf1. exists llf2. 
    split; auto.


(* fields are both H *)
    case_eq (beq_oid fo1 o); intro.
    (*inconsistency fo1 and o cannot equal*)
    apply beq_oid_equal in H41.
    rewrite <- H41 in H25. 
    assert (Some (Heap_OBJ cls0 F0 lo' ll)
            = lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls0 F0 lo' ll)) fo1).
    apply lookup_updated with h1 (Heap_OBJ cls0 F0 lb3 ll); auto.
    rewrite H41. auto.
    subst; auto.
    rewrite H38 in H25; inversion H25; subst; auto.
    destruct H40.
    assert (flow_to (join_label lof1 llf1) L_Label = true). apply join_L_label_flow_to_L; auto. 
    try (inconsist).
    
    case_eq (beq_oid fo2 o0); intro.
    (*inconsistency fo2 and o0 cannot equal*)
    apply beq_oid_equal in H42.
    subst; auto. 
    rewrite H39 in H26; inversion H26; subst; auto.
    destruct H40.
    assert (flow_to (join_label lof2 llf2) L_Label = true). apply join_L_label_flow_to_L; auto. try (inconsist).

    (* fo1 <> o and fo2 <> o0 *)
    assert (Some (Heap_OBJ cls_f1 FF1 lof1 llf1) =
            lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls0 F0 lo' ll)) fo1 
           ).
    apply lookup_updated_not_affected with o (Heap_OBJ cls0 F0 lo' ll)  h1; auto.

    assert (Some (Heap_OBJ cls_f2 FF2 lof2 llf2) =
           lookup_heap_obj (update_heap_obj h2 o0  (Heap_OBJ cls3 F3 lo' ll)) fo2
           ).
    apply lookup_updated_not_affected with o0 (Heap_OBJ cls3 F3 lo' ll)  h2; auto.

    
    exists cls_f1. exists cls_f2. exists lof1. exists lof2.
    exists FF1.
    exists FF2.
    exists llf1. exists llf2. 
    split; auto.

    assert (Some (Heap_OBJ cls3 F3 lb3 ll) =
           lookup_heap_obj (update_heap_obj h2 o0 (Heap_OBJ cls2 F2 lo' ll)) o2
           ).
    apply lookup_updated_not_affected with o0 (Heap_OBJ cls2 F2 lo' ll) h2; auto.    

    (* (beq_oid o1 o) = true and beq_oid o2 o0 = false *)
    apply object_equal_L with lo' lb3 cls0 cls3
                              F0 F3 ll; auto.   
    destruct H30. destruct H34. destruct H35. 
    split; auto. split; auto.
    split; auto.
    
    intros.
    destruct H36 with fname fo1 fo2; auto. rename x into cls_f1.
    destruct H39 as [cls_f2]. destruct H39 as [lof1].
    destruct H39 as [lof2]. destruct H39 as [FF1]. destruct H39 as [FF2].
    destruct H39 as [llf1]. destruct H39 as [llf2].
    destruct H39.  destruct H40. 

    
    (* fields are both L *)
    case_eq (beq_oid fo1 o); intro.
    apply beq_oid_equal in H42.
    rewrite <- H42 in H25. 
    assert (Some (Heap_OBJ cls0 F0 lo' ll)
            = lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls0 F0 lo' ll)) fo1).
    apply lookup_updated with h1 (Heap_OBJ cls0 F0 lb0 ll); auto.
    rewrite H42; auto.
    
    case_eq (beq_oid fo2 o0); intro.
    apply beq_oid_equal in H44.
    assert (Some (Heap_OBJ cls2 F2 lo' ll)
            = lookup_heap_obj (update_heap_obj h2 o0 (Heap_OBJ cls2 F2 lo' ll)) fo2).
    apply lookup_updated with h2  (Heap_OBJ cls_f2 FF2 lof2 llf2); auto.
    rewrite H44. auto.
    
    exists cls0. exists cls2. exists lo'. exists lo'.
    exists F0.
    exists F2.
    exists ll. exists ll. 
    split; auto. split; auto.
    subst; auto.

    destruct H41. destruct H30.
    rewrite H24 in H30. inversion H30. rewrite H44 in H32.
    assert (beq_oid o0 o0 = true).
    apply beq_oid_same.  try (inconsist).
    rewrite H40 in H21. inversion H21; subst; auto.
    destruct H30.
    assert (flow_to (join_label lof2 llf2) L_Label = true). apply join_L_label_flow_to_L; auto. try (inconsist).


    (* beq_oid fo2 o0 = false 
       beq_oid o2 o0 = false
       o = o1 
       fo1 = o *)    
    
    (* if fo1 = o, then fo2 must be equal to o2*)
    subst; auto.
    destruct H41. destruct H30. rewrite H30 in H16; inversion H16; subst; auto.
    pose proof (beq_oid_same o0).
    try (inconsist).


    rewrite H16 in H24; inversion H24; subst; auto. 
    pose proof (beq_oid_same o2).
    try (inconsist).

    (* beq_oid fo1 o = false*)
    subst; auto.
    case_eq (beq_oid fo2 o0); intro.
    
    (* inconsist assumption *)
    apply beq_oid_equal in H30.
    subst; auto.
    apply right_left in H16.
    destruct H41.
    
    destruct H30. 
    apply right_left in H30.
    rewrite H30 in H16.
    inversion H16; subst; auto. 
    pose proof (beq_oid_same o).
    try (inconsist).

    apply left_right in H16.
    rewrite H24 in H16; inversion H16; subst; auto.
    rewrite H40 in H21; inversion H21; subst; auto.
    destruct H30.
    assert (flow_to (join_label lof2 llf2) L_Label = true). apply join_L_label_flow_to_L; auto. try (inconsist).

    (* beq_oid fo2 o0 = false*)
    assert (Some (Heap_OBJ cls_f2 FF2 lof2 llf2) =
           lookup_heap_obj (update_heap_obj h2 o0 (Heap_OBJ cls2 F2 lo' ll)) fo2
           ).
    apply lookup_updated_not_affected with o0 (Heap_OBJ cls2 F2 lo' ll) h2; auto.
    
    assert (Some (Heap_OBJ cls_f1 FF1 lof1 llf1) =
            lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls3 F0 lo' ll)) fo1 
           ).
    apply lookup_updated_not_affected with o (Heap_OBJ cls3 F0 lo' ll)  h1; auto.
    

    exists cls_f1. exists cls_f2.
    exists lof1. exists lof2.
    exists FF1. exists FF2.
    exists llf1. exists llf2. 
    split; auto.

    (*beq_oid o1 o = false *)
    
    assert ( Some (Heap_OBJ cls0 F0 lb0 ll)  =
      lookup_heap_obj  (update_heap_obj h1 o (Heap_OBJ cls1 F1 lo' ll1))  o1).
    apply lookup_updated_not_affected with o (Heap_OBJ cls1 F1 lo' ll1) h1; auto.

    case_eq (beq_oid o2 o0); intro.
    (* cannot happen *)
    apply beq_oid_equal in H33.
    subst; auto.
    apply right_left in H16.
    apply right_left in H24.
    rewrite H24 in H16. inversion H16; subst; auto.
    assert (beq_oid o o = true). apply beq_oid_same.
    try (inconsist).

    assert ( Some (Heap_OBJ cls3 F3 lb3 ll)  =
      lookup_heap_obj  (update_heap_obj h2 o0 (Heap_OBJ cls2 F2 lo' ll1))  o2).
    apply lookup_updated_not_affected with o0 (Heap_OBJ cls2 F2 lo' ll1) h2; auto.

    
    apply object_equal_L with lb0 lb3 cls0 cls3
                              F0 F3 ll
                              ; auto.
    destruct H30. destruct H35. destruct H36. 
    split; auto. split; auto.
    split; auto. 
    intros.

    destruct H37 with fname fo1 fo2; auto. rename x into cls_f1.
    destruct H40 as [cls_f2]. destruct H40 as [lof1].
    destruct H40 as [lof2]. destruct H40 as [FF1]. destruct H40 as [FF2].
    destruct H40 as [llf1]. destruct H40 as [llf2].
    destruct H40. destruct H41.  destruct H42. 

    (* fields are both L *)
    case_eq (beq_oid fo1 o); intro.
    apply beq_oid_equal in H43.
    subst; auto. 
    assert (Some (Heap_OBJ cls1 F1 lo' ll1)
            = lookup_heap_obj (update_heap_obj h1 o  (Heap_OBJ cls1 F1 lo' ll1)) o).
    apply lookup_updated with h1 (Heap_OBJ cls_f1 FF1 lof1 llf1); auto.
    
    case_eq (beq_oid fo2 o0); intro.
    apply beq_oid_equal in H43.
    subst; auto. 
    assert (Some (Heap_OBJ cls2 F2 lo' ll1)
            = lookup_heap_obj (update_heap_obj h2 o0 (Heap_OBJ cls2 F2 lo' ll1)) o0).
    apply lookup_updated with h2 (Heap_OBJ cls2 F2 lo1 ll1); auto.
    
    exists cls1. exists cls2. exists lo'. exists lo'.
    exists F1.
    exists F2.
    exists ll1. exists ll1. 
    split; auto. split; auto.
    left; auto. split; auto.
    split; auto. split; auto. split; auto. split; auto. 
    rewrite H40 in H17; inversion H17; subst; auto.
    rewrite H41 in H21; inversion H21; subst; auto.
    apply H42. 

    (* beq_oid fo2 o0 = false*)

    assert (Some (Heap_OBJ cls_f2 FF2 lof2 llf2) =
           lookup_heap_obj (update_heap_obj h2 o0  (Heap_OBJ cls2 F2 lo' ll1)) fo2
           ).
    apply lookup_updated_not_affected with o0 (Heap_OBJ cls2 F2 lo' ll1) h2; auto.
    
    exists cls1. exists cls_f2.
    exists lo'. exists lof2.
    exists F1. exists FF2.
    exists ll1. exists llf2.  
    split; auto. split; auto.
    left; auto.
    split; auto. apply H42.
    split; auto. apply H42.
    split; auto. rewrite H40 in H17;inversion H17; subst; auto.
    apply H42.

    (* beq_oid fo1 o = false *)
    subst; auto.
    case_eq (beq_oid fo2 o0); intro.
    
    (* inconsist assumption *)
    apply beq_oid_equal in H30.
    subst; auto.
    apply right_left in H16.
    destruct H42.
     
    apply right_left in H30.
    rewrite H30 in H16.
    inversion H16; subst; auto. 
    pose proof (beq_oid_same o).
    try (inconsist).

    (* beq_oid fo2 o0 = false*)

    assert (Some (Heap_OBJ cls_f2 FF2 lof2 llf2) =
           lookup_heap_obj (update_heap_obj h2 o0 (Heap_OBJ cls2 F2 lo' ll1)) fo2
           ).
    apply lookup_updated_not_affected with o0 (Heap_OBJ cls2 F2 lo' ll1) h2; auto.

    assert (Some (Heap_OBJ cls_f1 FF1 lof1 llf1) =
            lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls1 F1 lo' ll1)) fo1 
           ).
    apply lookup_updated_not_affected with o (Heap_OBJ cls1 F1 lo' ll1)  h1; auto.

    exists cls_f1. exists cls_f2.
    exists lof1. exists lof2.
    exists FF1. exists FF2.
    exists llf1. exists llf2. 
    split; auto.



(* fields are both H *)
    case_eq (beq_oid fo1 o); intro.
    (*inconsistency fo1 and o cannot equal*)
    apply beq_oid_equal in H43.
    subst; auto.
    rewrite H40 in H17; inversion H17; subst; auto.
    destruct H42.
    assert (flow_to (join_label lof1 llf1) L_Label = true). apply join_L_label_flow_to_L; auto. try(inconsist).

    (*beq_oid fo1 o = false *)
    assert (Some (Heap_OBJ cls_f1 FF1 lof1 llf1) =
            lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls1 F1 lo' ll1)) fo1 
           ).
    apply lookup_updated_not_affected with o (Heap_OBJ cls1 F1 lo' ll1)  h1; auto.
    
    case_eq (beq_oid fo2 o0); intro.
    (*inconsistency fo2 and o0 cannot equal*)
    apply beq_oid_equal in H45.
    subst; auto. 
    rewrite H41 in H21; inversion H21; subst; auto.
    destruct H42.
    assert (flow_to (join_label lof2 llf2) L_Label = true). apply join_L_label_flow_to_L; auto. try(inconsist).

    (* only the case fo1 <> o and fo2 <> o0 is feasible  *)
    assert (Some (Heap_OBJ cls_f2 FF2 lof2 llf2) =
           lookup_heap_obj (update_heap_obj h2 o0  (Heap_OBJ cls2 F2 lo' ll1)) fo2
           ).
    apply lookup_updated_not_affected with o0 (Heap_OBJ cls2 F2 lo' ll1)  h2; auto.
    
    exists cls_f1. exists cls_f2. exists lof1. exists lof2.
    exists FF1.
    exists FF2.
    exists llf1. exists llf2. 
    split; auto.

  - (* None -> left φ o1 = None *)
    intros. apply lookup_updated_heap_must_none in H24.
    apply H15 in H24. auto. 

  - (* o1 = None -> right φ o1 = None *)
    intros. apply lookup_updated_heap_must_none in H24.
    apply H20 in H24. auto.

  - (* flow_to lb L_Label = false  *)
    intros.
    case_eq (beq_oid o1 o); intro.
    assert ( Some (Heap_OBJ cls F lb ll) = lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls1 F1 lo' ll1)) o1 ). auto.
    apply lookup_updated_heap_new_obj in H27; auto.
    inversion H27; subst; auto.
    assert (flow_to (join_label lo' ll1) L_Label = true). apply join_L_label_flow_to_L; auto. try(inconsist).    
    
    assert (Some (Heap_OBJ cls F lb ll) =
            lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls1 F1 lo' ll1)) o1
           ). auto.
    apply lookup_updated_heap_old_obj in H27; auto.
    assert ( lookup_heap_obj h1 o1 = Some (Heap_OBJ cls F lb ll) ); auto.
    apply H22 in H28; auto. 

  - (*flow_to lb L_Label = false -> right φ o1 = None *)
    intros.
    case_eq (beq_oid o1 o0); intro.
    assert ( Some (Heap_OBJ cls F lb ll) = lookup_heap_obj (update_heap_obj h2 o0 (Heap_OBJ cls2 F2 lo' ll1)) o1 ). auto.
    apply lookup_updated_heap_new_obj in H27; auto.
    inversion H27; subst; auto.
    assert (flow_to (join_label lo' ll1) L_Label = true). apply join_L_label_flow_to_L; auto. try(inconsist).   
    
    assert (Some (Heap_OBJ cls F lb ll) =
            lookup_heap_obj (update_heap_obj h2 o0 (Heap_OBJ cls2 F2 lo' ll1)) o1
           ). auto.
    apply lookup_updated_heap_old_obj in H27; auto.
    assert ( lookup_heap_obj h2 o1 = Some (Heap_OBJ cls F lb ll) ); auto.
    apply H23 in H28; auto.

  - (*flow_to lo' L_Label = false *)
    rewrite <- H16 in H5. inversion H5; subst; auto.
    rewrite <- H18 in H6; inversion H6; subst; auto. 
    apply  L_eq_heap; auto. 
    case_eq (beq_oid o1 o0); intro.
    assert ( Some (Heap_OBJ cls F lb ll) = lookup_heap_obj (update_heap_obj h2 o0 (Heap_OBJ cls2 F2 lo' ll1)) o1 ). auto.
    apply lookup_updated_heap_new_obj in H27; auto.
    inversion H27; subst; auto.
    assert (flow_to (join_label lo' ll1) L_Label = true). apply join_L_label_flow_to_L; auto. try(inconsist).   
    
    assert (Some (Heap_OBJ cls F lb ll) =
            lookup_heap_obj (update_heap_obj h2 o0 (Heap_OBJ cls2 F2 lo' ll1)) o1
           ). auto.
    apply lookup_updated_heap_old_obj in H27; auto.
    assert ( lookup_heap_obj h2 o1 = Some (Heap_OBJ cls F lb ll) ); auto.
    apply H23 in H28; auto.



    -----
    assert (flow_to (join_label lb0 ll1) L_Label = true). apply join_L_label_flow_to_L; auto. try(inconsist).   
    assert (flow_to lo' L_Label = false).
    apply flow_transitive with lb0; auto.
    try (inconsist).
   
Qed. Hint Resolve lbl_L_change_obj_both_lbl_preserve_bijection. 
lbl_H_change_obj_both_lbl_preserve_bijection
*)

  (* heap bijection preservation *)
Lemma lbl_H_raise_obj_both_lbl_preserve_bijection {DecOid : forall a1 a2 : oid, Decision (a1 = a2)} : forall  ct h1 h2 φ lo lo0 lo' F F0 o o0 lb1 lb2 cls cls0
  φ' (Hφ : (left φ o = Some o0)) ll ll0,
    flow_to (join_label lo' ll) L_Label = false ->
    wfe_heap ct h1 -> field_wfe_heap ct h1 ->
    wfe_heap ct h2 -> field_wfe_heap ct h2 ->  
    L_equivalence_heap h1 h2 φ ->
    Some (Heap_OBJ cls F lo ll) = lookup_heap_obj h1 o ->
    Some (Heap_OBJ cls0 F0 lo0 ll0) = lookup_heap_obj h2 o0 ->
    L_equivalence_tm (ObjId o) h1 (ObjId o0) h2 φ ->
    flow_to lb1 L_Label = true ->
    flow_to lb2 L_Label = true ->
    flow_to lb1 ll = true ->
    flow_to lb2 ll0 = true ->
    flow_to lo lo' = true ->
    flow_to lo0 lo' = true ->
    φ' =  (reduce_bijection φ o o0 Hφ) ->
      L_equivalence_heap
        (update_heap_obj h1 o (Heap_OBJ cls F lo' ll))
        (update_heap_obj h2 o0 (Heap_OBJ cls0 F0 lo' ll0)) φ'.
    
Proof with eauto.
  intros.   
  inversion H4; subst; auto.  
  - (*flow_to lo' L_Label = false *)    
    assert (L_equivalence_object o h1 o0 h2 φ) as H_eq_o1_o2.          
    apply H15; auto. 
    inversion H_eq_o1_o2; subst; auto.    
    apply L_eq_heap; auto.

    + intros.
      case_eq (beq_oid o1 o); intro.
      (* cannot happen *)
      apply beq_oid_equal in H26. subst; auto. 
      assert (left (reduce_bijection φ o o0 Hφ) o = None). apply reduce_bijection_lookup_eq_left; auto.
      rewrite H26 in H25; inversion H25.

      apply beq_oid_false_mark in H26.
      assert (left (reduce_bijection φ o o0 Hφ) o1 = left φ o1).
      apply reduce_bijection_lookup_neq_left. auto.
      
      subst; auto. assert (left φ o1 = Some o2). rewrite <- H27.  rewrite H25. auto.

      case_eq (beq_oid o2 o0); intro.
      apply beq_oid_equal in H29. subst; auto.
      assert (left φ o = Some o0). auto. 
      apply right_left in H28. apply right_left in H29.
      rewrite H28 in H29. inversion H29. 
      rewrite H31 in H26; try (contradiction).

      
      apply H15 in H28. inversion H28; subst; auto.       
    
      assert ( Some (Heap_OBJ cls3 F3 lb4 ll2)  =
      lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls F lo' ll))  o1).
      apply lookup_updated_not_affected with o (Heap_OBJ cls F lo' ll)  h1; auto.

      
      assert ( Some (Heap_OBJ cls4 F4 lb5 ll2)  =
      lookup_heap_obj  (update_heap_obj h2 o0 (Heap_OBJ cls0 F0 lo' ll0))  o2).
      apply lookup_updated_not_affected with o0 (Heap_OBJ cls0 F0 lo' ll0)  h2; auto.
      apply object_equal_L with lb4 lb5 cls3 cls4
                              F3 F4 ll2
      ; auto.
      destruct H35. destruct H38. destruct H39. destruct H40 as [tmp].
      split; auto. split; auto.
      split; auto. split; auto. 
      intros.

      destruct H40 with fname fo1 fo2; auto. rename x into cls_f1.
      destruct H43 as [cls_f2]. destruct H43 as [lof1].
      destruct H43 as [lof2]. destruct H43 as [FF1]. destruct H43 as [FF2].
      destruct H43 as [llf1]. destruct H43 as [llf2]. 
      destruct H43. destruct H44.  destruct H45. 


      (* fields are both L *)
      case_eq (beq_oid fo1 o); intro.
      apply beq_oid_equal in H46.
      assert (fo2 = o0).
      destruct H45. assert (left φ o = Some o0); auto.
      subst; auto. rewrite H45 in H48; inversion H48; subst; auto. 
      assert (Some (Heap_OBJ cls F lo' ll)
            = lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls F lo' ll)) fo1).
      apply lookup_updated with h1 (Heap_OBJ cls_f1 FF1 lof1 llf1); auto.
      rewrite H46; auto.

      assert (Some (Heap_OBJ cls0 F0 lo' ll0)
            = lookup_heap_obj (update_heap_obj h2 o0 (Heap_OBJ cls0 F0 lo' ll0)) fo2).
      apply lookup_updated with h2 (Heap_OBJ cls_f2 FF2 lof2 llf2); auto.
      rewrite H47. auto.

      subst; auto. 

      exists cls. exists cls0. exists lo'. exists lo'.
      exists F.
      exists F0.
      exists ll. exists ll0. 

      split; auto. split; auto.
      right. rewrite <- H14 in H5; inversion H5; subst; auto.
      case_eq (flow_to lo' L_Label); intro.
      assert (flow_to (join_label lo' ll1) L_Label = true ).  apply join_L_label_flow_to_L ; auto.
      try (inconsist).
      split; auto. apply flow_transitive with lo'; auto. apply join_def_flow1; auto.       
      
      (* beq_oid fo1 o = false*)
      subst; auto.
      assert (fo2 <> o0).
      intro contra. subst; auto.
      destruct H45.
      assert (left φ o = Some o0). auto.
      apply right_left in H35.
      apply right_left in H45. rewrite H45 in H35; inversion H35; subst; auto.
      assert (beq_oid fo1 fo1 = true). apply beq_oid_same. try (inconsist).
      apply beq_oid_not_equal in H35. 

    (* beq_oid fo2 o0 = false*)
      assert (Some (Heap_OBJ cls_f1 FF1 lof1 llf1) =
            lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls F lo' ll)) fo1 
           ).
      apply lookup_updated_not_affected with o (Heap_OBJ cls F lo' ll)  h1; auto.
 
    assert (Some (Heap_OBJ cls_f2 FF2 lof2 llf2) =
           lookup_heap_obj (update_heap_obj h2 o0   (Heap_OBJ cls0 F0 lo' ll0)) fo2
           ).
    apply lookup_updated_not_affected with o0  (Heap_OBJ cls0 F0 lo' ll0) h2; auto.

    exists cls_f1. exists cls_f2.
    exists lof1. exists lof2.
    exists FF1. exists FF2.
    exists llf1. exists llf2. 
    split; auto. split; auto. left; auto.
    destruct H45. 

    assert (left (reduce_bijection φ o o0 Hφ ) fo1 = left φ fo1).
    apply reduce_bijection_lookup_neq_left.
    intro contra. 
    rewrite contra in H46.
    assert (beq_oid fo1 fo1 = true).
    apply beq_oid_same. try (inconsist).
    split; auto. rewrite <- H49 in H45; auto. 

(* fields are both H *)
    case_eq (beq_oid fo1 o); intro.
    (*inconsistency fo1 and o cannot equal*)
    apply beq_oid_equal in H46.
    rewrite <- H46 in H14.
    rewrite H43 in H14; inversion H14; subst; auto.
    destruct H45.
    rewrite H43 in H5; inversion H5; subst; auto.
    assert (flow_to (join_label lof1 llf1) L_Label = true). apply  join_L_label_flow_to_L; auto. 
    try (inconsist).

    assert (fo2 <> o0).
    intro contra. subst; auto.
    rewrite H44 in H20; inversion H20; subst; auto.
    destruct H45.
    assert (flow_to (join_label lof2 llf2) L_Label = true). apply  join_L_label_flow_to_L; auto. 
    try (inconsist).
    apply beq_oid_not_equal in H47. 


    (* fo1 <> o and fo2 <> o0 *)
    assert (Some (Heap_OBJ cls_f1 FF1 lof1 llf1) =
            lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls F lo' ll)) fo1 
           ).
    apply lookup_updated_not_affected with o (Heap_OBJ cls F lo' ll)  h1; auto.

    assert (Some (Heap_OBJ cls_f2 FF2 lof2 llf2) =
           lookup_heap_obj (update_heap_obj h2 o0  (Heap_OBJ cls0 F0 lo' ll0)) fo2
           ).
    apply lookup_updated_not_affected with o0 (Heap_OBJ cls0 F0 lo' ll0)  h2; auto.
    
    exists cls_f1. exists cls_f2. exists lof1. exists lof2.
    exists FF1.
    exists FF2.
    exists llf1. exists llf2. 
    split; auto.


    +   (* None -> left φ o1 = None *)
    intros. apply lookup_updated_heap_must_none in H25.
    apply H16 in H25. subst; auto.
    case_eq (beq_oid o o1); intro.
    ++ apply beq_oid_equal in H26.  subst; auto.
       apply reduce_bijection_lookup_eq_left.
    ++ apply beq_oid_false_mark in H26.
       assert (left (reduce_bijection φ o o0 Hφ) o1 = left φ o1).
       apply reduce_bijection_lookup_neq_left; auto.
       rewrite H27. rewrite H25.
       auto. 
      
    + (* o1 = None -> right φ o1 = None *)
    intros. apply lookup_updated_heap_must_none in H25.
    apply H17 in H25.
    case_eq (beq_oid o0 o1); intro.
    ++ apply beq_oid_equal in H26.  subst; auto.
       apply reduce_bijection_lookup_eq_right.
    ++ apply beq_oid_false_mark in H26.
       assert (right (reduce_bijection φ o o0 Hφ) o1 = right φ o1).
       apply reduce_bijection_lookup_neq_right; auto.
       subst; auto. 
       rewrite H27. rewrite H25.
       auto. 

    + (* flow_to lb L_Label = false  *)
    intros.
    case_eq (beq_oid o1 o); intro.
    ++ apply beq_oid_equal in H27. subst; auto.
       apply reduce_bijection_lookup_eq_left.
    ++ 
      assert ( Some (Heap_OBJ cls3 F3 lb ll2) =
               lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls F lo' ll)) o1). auto.
    apply lookup_updated_heap_old_obj in H28; auto.
    assert (left φ o1 = None). 
    apply H18 with cls3 F3 lb ll2; auto.
    assert (left (reduce_bijection φ o o0 Hφ) o1 = left φ o1).
    apply reduce_bijection_lookup_neq_left; auto.
    intro contra. subst; auto.
    assert (beq_oid o1 o1 = true). apply beq_oid_same. try (inconsist).
    subst; auto. 
    rewrite H30. auto. 

  + (*flow_to lb L_Label = false -> right φ o1 = None *)
    intros.
    case_eq (beq_oid o1 o0); intro.
    ++ apply beq_oid_equal in H27; subst; auto.
       apply reduce_bijection_lookup_eq_right.
    ++ 
    assert ( Some (Heap_OBJ cls3 F3 lb ll2) = lookup_heap_obj (update_heap_obj h2 o0 (Heap_OBJ cls0 F0 lo' ll0)) o1); auto. 
    apply lookup_updated_heap_old_obj in H28; auto.
    assert (right φ o1 = None). 
    apply H19 with cls3 F3 lb ll2; auto.
    assert (right (reduce_bijection φ o o0 Hφ) o1 = right φ o1).
    apply reduce_bijection_lookup_neq_right; auto.
    intro contra.
    subst; auto. assert (beq_oid o1 o1 = true). apply beq_oid_same. try (inconsist).
    subst; auto. 
    rewrite H30. auto. 
Qed. Hint Resolve lbl_H_raise_obj_both_lbl_preserve_bijection. 

(*
  (* heap bijection preservation *)
Lemma lbl_H_change_obj_both_lbl_preserve_bijection {DecOid : forall a1 a2 : oid, Decision (a1 = a2)} : forall  ct h1 h2 φ lo lo0 lo' F F0 o o0 lb1 lb2 cls cls0,
    flow_to lo' L_Label = false ->
    wfe_heap ct h1 -> field_wfe_heap ct h1 ->
    wfe_heap ct h2 -> field_wfe_heap ct h2 ->  
    L_equivalence_heap h1 h2 φ ->
    Some (Heap_OBJ cls F lo) = lookup_heap_obj h1 o ->
    Some (Heap_OBJ cls0 F0 lo0) = lookup_heap_obj h2 o0 ->
    L_equivalence_tm (ObjId o) h1 (ObjId o0) h2 φ ->
    flow_to lo L_Label = false ->
    flow_to lo0 L_Label = false ->
    flow_to lb1 L_Label = true ->
    flow_to lb2 L_Label = true ->
    flow_to lb1 lo = true ->
    flow_to lb2 lo0 = true ->
    flow_to lo lo' = true ->
    flow_to lo0 lo' = true ->
    L_equivalence_heap
        (update_heap_obj h1 o (Heap_OBJ cls F lo'))
        (update_heap_obj h2 o0 (Heap_OBJ cls0 F0 lo')) φ.
    
Proof with eauto.
  intros.   
  inversion H4; subst; auto.  
  (*flow_to lo' L_Label = false *)
  apply L_eq_heap; auto.
  + intros.
    case_eq (beq_oid o1 o); intro.
      (* cannot happen *)
    apply beq_oid_equal in H22. subst; auto.
    apply H16 in H21. 
    inversion H21; subst; auto.
    rewrite <- H22 in H5; inversion H5; subst; auto.
    try (inconsist).

    assert (o0 <> o2).
    intro contra. subst; auto.
    apply H16 in H21. 
    inversion H21; subst; auto.
    rewrite <- H24 in H6; inversion H6; subst; auto.
    try (inconsist).

    apply beq_oid_not_equal in H23. 

    apply H16 in H21; inversion H21; subst; auto. 

    assert ( Some (Heap_OBJ cls1 F1 lb0)  =
             lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls F lo'))  o1).
    apply lookup_updated_not_affected with o (Heap_OBJ cls F lo')  h1; auto.
    
    assert ( Some (Heap_OBJ cls2 F2 lb3)  =
      lookup_heap_obj  (update_heap_obj h2 o0 (Heap_OBJ cls0 F0 lo'))  o2).
    apply lookup_updated_not_affected with o0 (Heap_OBJ cls0 F0 lo')  h2; auto.

    intro contra. subst; auto.
    assert (beq_oid o0 o0 = true). apply beq_oid_same.
    try (inconsist).

    apply object_equal_L with lb0 lb3 cls1 cls2
                              F1 F2; auto.

    destruct H28. destruct H31. destruct H32. 
    split; auto. split; auto.
    split; auto. 

    intros.
    destruct H33 with fname fo1 fo2; auto. rename x into cls_f1.
    destruct H36 as [cls_f2]. destruct H36 as [lof1].
    destruct H36 as [lof2]. destruct H36 as [FF1]. destruct H36 as [FF2].
    destruct H36. destruct H37.  destruct H38. 


      (* fields are both L *)
    case_eq (beq_oid fo1 o); intro.
    (*cannot happen *)
    apply beq_oid_equal in H39.
    subst; auto.
    destruct H38. destruct H38. destruct H39.
    rewrite H36 in H5; inversion H5; subst; auto.
    try (inconsist).

    assert (fo2 <> o0).
    intro contra. subst; auto.
    rewrite H37 in H6; inversion H6; subst; auto.
    destruct H38. destruct H38.
    try (inconsist).

    apply beq_oid_not_equal in H40. 

    (* beq_oid fo1 o = false*)
    (* beq_oid fo2 o0 = false*)
    assert (Some (Heap_OBJ cls_f1 FF1 lof1) =
            lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls F lo')) fo1 
           ).
    apply lookup_updated_not_affected with o (Heap_OBJ cls F lo')  h1; auto.
 
    assert (Some (Heap_OBJ cls_f2 FF2 lof2) =
           lookup_heap_obj (update_heap_obj h2 o0   (Heap_OBJ cls0 F0 lo')) fo2
           ).
    apply lookup_updated_not_affected with o0  (Heap_OBJ cls0 F0 lo') h2; auto.

    exists cls_f1. exists cls_f2.
    exists lof1. exists lof2.
    exists FF1. exists FF2.
    split; auto.

    
(* fields are both H *)
    case_eq (beq_oid fo1 o); intro.
    apply beq_oid_equal in H39; subst; auto.
    assert (Some (Heap_OBJ cls F lo') =
            lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls F lo')) o
           ).
    apply lookup_updated with h1 (Heap_OBJ cls_f1 FF1 lof1); auto.

    case_eq (beq_oid fo2 o0); intro.
    apply beq_oid_equal in H39; subst; auto.
    assert (Some (Heap_OBJ cls0 F0 lo') =
            lookup_heap_obj (update_heap_obj h2 o0 (Heap_OBJ cls0 F0 lo')) o0
           ).
    apply lookup_updated with h2 (Heap_OBJ cls_f2 FF2 lof2); auto.

    exists cls. exists cls0.
    exists lo'. exists lo'.
    exists F. exists F0.
    split; auto.

    (* fo1 = o and fo2 <> o0 *)
    assert (Some (Heap_OBJ cls_f2 FF2 lof2) =
           lookup_heap_obj (update_heap_obj h2 o0  (Heap_OBJ cls0 F0 lo')) fo2
           ).
    apply lookup_updated_not_affected with o0 (Heap_OBJ cls0 F0 lo')  h2; auto.
    exists cls. exists cls_f2.
    exists lo'. exists lof2.
    exists F. exists FF2.
    split; auto. split; auto.
    right. split; auto. apply H38.

    (* fo1 <> o *)
    assert (Some (Heap_OBJ cls_f1 FF1 lof1) =
            lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls F lo')) fo1 
           ).
    apply lookup_updated_not_affected with o (Heap_OBJ cls F lo')  h1; auto.

    (* fo1 <> o and fo2 = o0 *)
    case_eq (beq_oid fo2 o0); intro.
    apply beq_oid_equal in H41; subst; auto.
    assert (Some (Heap_OBJ cls0 F0 lo') =
            lookup_heap_obj (update_heap_obj h2 o0 (Heap_OBJ cls0 F0 lo')) o0
           ).
    apply lookup_updated with h2 (Heap_OBJ cls_f2 FF2 lof2); auto.

    exists cls_f1. exists cls0.
    exists lof1. exists lo'.
    exists FF1. exists F0.
    split; auto. split; auto.
    right. split; auto. apply H38. 

    (* fo1 <> o and fo2 <> o0 *)
    assert (Some (Heap_OBJ cls_f2 FF2 lof2) =
           lookup_heap_obj (update_heap_obj h2 o0  (Heap_OBJ cls0 F0 lo')) fo2
           ).
    apply lookup_updated_not_affected with o0 (Heap_OBJ cls0 F0 lo')  h2; auto.
    exists cls_f1. exists cls_f2.
    exists lof1. exists lof2.
    exists FF1. exists FF2.
    split; auto.

  +   (* None -> left φ o1 = None *)
    intros. apply lookup_updated_heap_must_none in H21.
    apply H17 in H21. subst; auto.
      
  + (* o1 = None -> right φ o1 = None *)
    intros. apply lookup_updated_heap_must_none in H21.
    apply H18 in H21; auto. 

  + (* flow_to lb L_Label = false  *)
    intros.
    case_eq (beq_oid o1 o); intro.
    ++ apply beq_oid_equal in H23. subst; auto.
       apply H19 with cls F lo; auto.  
    ++ 
      assert ( Some (Heap_OBJ cls1 F1 lb) = lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls F lo')) o1). auto.
      apply lookup_updated_heap_old_obj in H24; auto.
      apply H19 with cls1 F1 lb; auto. 

  + (*flow_to lb L_Label = false -> right φ o1 = None *)
    intros.
    case_eq (beq_oid o1 o0); intro.
    ++ apply beq_oid_equal in H23; subst; auto.
       apply H20 with cls0 F0 lo0; auto. 
    ++ 
    assert ( Some (Heap_OBJ cls1 F1 lb) = lookup_heap_obj (update_heap_obj h2 o0 (Heap_OBJ cls0 F0 lo')) o1); auto. 
    apply lookup_updated_heap_old_obj in H24; auto.
    apply H20 with cls1 F1 lb; auto. 

Qed. Hint Resolve lbl_H_change_obj_both_lbl_preserve_bijection. 
*)

*)

Lemma lbl_L_change_obj_both_lbl_preserve_l_eq_tm: forall  ct h1 h2 φ lo lo0 lo' F F0 o o0 lb1 lb2 cls cls0
  t1 t2 ll ll0,
    wfe_heap ct h1 -> field_wfe_heap ct h1 ->
    wfe_heap ct h2 -> field_wfe_heap ct h2 ->  
    L_equivalence_heap h1 h2 φ ->
    Some (Heap_OBJ cls F lo ll) = lookup_heap_obj h1 o ->
    Some (Heap_OBJ cls0 F0 lo0 ll0) = lookup_heap_obj h2 o0 ->
    L_equivalence_tm (ObjId o) h1 (ObjId o0) h2 φ ->
    L_equivalence_tm t1 h1 t2 h2 φ ->
    flow_to lb1 L_Label = true ->
    flow_to lb2 L_Label = true ->
    flow_to lb1 ll = true ->
    flow_to lb2 ll0 = true ->
    flow_to lo lo' = true ->
    flow_to lo0 lo' = true ->
    L_equivalence_tm t1 (update_heap_obj h1 o (Heap_OBJ cls F lo' ll))
                     t2 (update_heap_obj h2 o0 (Heap_OBJ cls0 F0 lo' ll0)) φ.
Proof with eauto.
  intros.
  inversion H6; subst; auto.
  - generalize dependent t2.
    induction t1; intros; inversion H7; subst; auto.
    + 
      case_eq (beq_oid o1 o); intro.
      ++
        apply beq_oid_equal in H14; subst; auto.
        *
        rewrite H15 in H16; inversion H16; subst; auto.
        assert (Some (Heap_OBJ cls F lo' ll) =
              lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls F lo' ll)) o ).
        apply lookup_updated with h1 (Heap_OBJ cls3 F3 lo2 ll2); auto.

        assert (Some (Heap_OBJ cls0 F0 lo' ll0) =
              lookup_heap_obj (update_heap_obj h2 o0  (Heap_OBJ cls0 F0 lo' ll0)) o0 ).
        apply lookup_updated with h2 (Heap_OBJ cls4 F4 lo2 ll2); auto.  
        apply L_equivalence_tm_eq_object_L with cls F lo' cls0 F0 ll; auto.
        rewrite <- H19 in H4; inversion H4; subst; auto.
        rewrite <- H4 in H17; inversion H17; subst; auto.
        rewrite <- H5 in H20; inversion H20; subst; auto. 
       
          
          
    ++ assert (o3 <> o0).
      intro contra. subst; auto.
      apply right_left in H15.
      apply right_left in H16.
      rewrite H15 in H16; inversion H16; subst; auto.
      assert (beq_oid o o = true). apply beq_oid_same.
      try (inconsist).

      assert (Some (Heap_OBJ cls3 F3 lo2 ll2) =
              lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls F lo' ll)) o1 ).
      apply lookup_updated_not_affected with o (Heap_OBJ cls F lo' ll) h1; auto.
      intro contra. subst; auto. pose proof (beq_oid_same o); try (inconsist).
      
      assert (Some (Heap_OBJ cls4 F4 lo2 ll2) =
              lookup_heap_obj (update_heap_obj h2 o0 (Heap_OBJ cls0 F0 lo' ll0)) o3 ).
      apply lookup_updated_not_affected with o0 (Heap_OBJ cls0 F0 lo' ll0) h2; auto.
      apply  L_equivalence_tm_eq_object_L with cls3 F3 lo2 cls4 F4 ll2; auto.


    + assert (o1 <> o). intro contra.
      subst; auto.
      rewrite <- H15 in H17; inversion H17; subst; auto.
      try (inconsist).

      assert (o3 <> o0). intro contra.
      subst; auto.
      rewrite <- H19 in H20; inversion H20; subst; auto.
      try (inconsist).
      
      assert (Some (Heap_OBJ cls3 F3 lo2 ll2) =
              lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls F lo' ll)) o1 ).
      apply lookup_updated_not_affected with o (Heap_OBJ cls F lo' ll) h1; auto.
      
      assert (Some (Heap_OBJ cls4 F4 lo3 ll3) =
              lookup_heap_obj (update_heap_obj h2 o0 (Heap_OBJ cls0 F0 lo' ll0)) o3 ).
      apply lookup_updated_not_affected with o0 (Heap_OBJ cls0 F0 lo' ll0) h2; auto.
      eauto using  L_equivalence_tm_eq_object_H.

  - rewrite <- H4 in H16; inversion H16; subst; auto.
    rewrite <- H5 in H17; inversion H17; subst; auto.

    generalize dependent t2.
    induction t1; intros; inversion H7; subst; auto.
    + assert (o1 <> o). intro contra.
      subst; auto.
      rewrite <- H19 in H4; inversion H4; subst; auto.
      try (inconsist).

      assert (o3 <> o0). intro contra.
      subst; auto.
      rewrite <- H22 in H5; inversion H5; subst; auto.
      try (inconsist).
      
      assert (Some (Heap_OBJ cls1 F1 lo1 ll1) =
              lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls F lo' ll)) o1 ).
      apply lookup_updated_not_affected with o (Heap_OBJ cls F lo' ll) h1; auto.
      
      assert (Some (Heap_OBJ cls2 F2 lo1 ll1) =
              lookup_heap_obj (update_heap_obj h2 o0 (Heap_OBJ cls0 F0 lo' ll0)) o3 ).
      apply lookup_updated_not_affected with o0 (Heap_OBJ cls0 F0 lo' ll0) h2; auto.
      eauto using  L_equivalence_tm_eq_object_L.

    + case_eq (beq_oid o1 o); intro.
      ++
        apply beq_oid_equal in H14; subst; auto.
        rewrite <- H15 in H4; inversion H4; subst; auto.
        assert (Some (Heap_OBJ cls1 F1 lo' ll1) =
                lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls1 F1 lo' ll1)) o ).        
        apply lookup_updated with h1 (Heap_OBJ cls1 F1 lo1 ll1); auto.
        case_eq (beq_oid o3 o0); intro.
      * apply beq_oid_equal in H23; subst; auto.
        rewrite <- H19 in H5; inversion H5; subst; auto.
        assert (Some (Heap_OBJ cls2 F2 lo' ll2) =
                lookup_heap_obj (update_heap_obj h2 o0 (Heap_OBJ cls2 F2 lo' ll2)) o0 ).        
        apply lookup_updated with h2 (Heap_OBJ cls2 F2 lo2 ll2); auto.
        eauto using  L_equivalence_tm_eq_object_H.

      * assert (Some (Heap_OBJ cls2 F2 lo2 ll2) =
              lookup_heap_obj (update_heap_obj h2 o0 (Heap_OBJ cls0 F0 lo' ll0)) o3 ).
        apply lookup_updated_not_affected with o0 (Heap_OBJ cls0 F0 lo' ll0) h2; auto.
        intro contra; subst; auto. pose proof (beq_oid_same o0); try (inconsist).
        eauto using  L_equivalence_tm_eq_object_H.
        
      ++
        assert (Some (Heap_OBJ cls1 F1 lo1 ll1) =
                lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls F lo' ll)) o1 ).
        apply lookup_updated_not_affected with o (Heap_OBJ cls F lo' ll) h1; auto.
        intro contra; subst; auto. pose proof (beq_oid_same o); try (inconsist).
        case_eq (beq_oid o3 o0); intro.
      * apply beq_oid_equal in H24; subst; auto.
        rewrite <- H19 in H5; inversion H5; subst; auto.
        assert (Some (Heap_OBJ cls2 F2 lo' ll2) =
                lookup_heap_obj (update_heap_obj h2 o0 (Heap_OBJ cls2 F2 lo' ll2)) o0 ).        
        apply lookup_updated with h2 (Heap_OBJ cls2 F2 lo2 ll2); auto.
        eauto using  L_equivalence_tm_eq_object_H.

      * assert (Some (Heap_OBJ cls2 F2 lo2 ll2) =
              lookup_heap_obj (update_heap_obj h2 o0 (Heap_OBJ cls0 F0 lo' ll0)) o3 ).
        apply lookup_updated_not_affected with o0 (Heap_OBJ cls0 F0 lo' ll0) h2; auto.
        intro contra; subst; auto. pose proof (beq_oid_same o0); try (inconsist).
        eauto using  L_equivalence_tm_eq_object_H.
Qed. Hint Resolve     lbl_L_change_obj_both_lbl_preserve_l_eq_tm.  

(*
Lemma lbl_H_raise_obj_both_lbl_preserve_l_eq_tm {DecOid : forall a1 a2 : oid, Decision (a1 = a2)} : forall  ct h1 h2 φ lo lo0 lo' F F0 o o0 lb1 lb2 cls cls0
  φ' (Hφ : (left φ o = Some o0)) t1 t2 ll ll0,
    flow_to (join_label lo' ll) L_Label = false ->
    wfe_heap ct h1 -> field_wfe_heap ct h1 ->
    wfe_heap ct h2 -> field_wfe_heap ct h2 ->  
    L_equivalence_heap h1 h2 φ ->
    Some (Heap_OBJ cls F lo ll) = lookup_heap_obj h1 o ->
    Some (Heap_OBJ cls0 F0 lo0 ll0) = lookup_heap_obj h2 o0 ->
    L_equivalence_tm (ObjId o) h1 (ObjId o0) h2 φ ->
    flow_to (join_label lo ll) L_Label = true ->
    flow_to (join_label lo0 ll0) L_Label = true ->
    flow_to lb1 L_Label = true ->
    flow_to lb2 L_Label = true ->
    flow_to lb1 ll = true ->
    flow_to lb2 ll0 = true ->
    flow_to lo lo' = true ->
    flow_to lo0 lo' = true ->
    φ' =  (reduce_bijection φ o o0 Hφ) ->
    L_equivalence_tm t1 h1 t2 h2 φ ->
    L_equivalence_tm t1 (update_heap_obj h1 o (Heap_OBJ cls F lo' ll))
                     t2 (update_heap_obj h2 o0 (Heap_OBJ cls0 F0 lo' ll0)) φ'.
    
Proof with eauto.
  intros.   
  generalize dependent t2.
  induction t1; intros; inversion H17; subst; auto.

  - case_eq (beq_oid o1 o); intro.
    apply beq_oid_equal in H16; subst; auto.
    + rewrite Hφ in H19; inversion H19; subst; auto.
      assert (Some (Heap_OBJ cls F lo' ll) =
              lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls F lo' ll)) o ).
      apply lookup_updated with h1 (Heap_OBJ cls1 F1 lo1 ll1); auto.
      
      assert (Some (Heap_OBJ cls0 F0 lo' ll0) =
              lookup_heap_obj (update_heap_obj h2 o3  (Heap_OBJ cls0 F0 lo' ll0)) o3 ).
      apply lookup_updated with h2 (Heap_OBJ cls2 F2 lo1 ll1); auto.  
      
      apply L_equivalence_tm_eq_object_H with cls cls0 F lo' F0 lo' ll ll0; auto.
      apply flow_dist in H8. destruct H8.
      case_eq (flow_to lo' L_Label); intro.
      assert (flow_to (join_label lo' ll) L_Label = true). apply join_L_label_flow_to_L; auto.
      try (inconsist).

      apply flow_transitive with lo' ; auto.
      apply join_def_flow1; auto. 

    + assert (o3 <> o0).
      intro contra. subst; auto.
      apply right_left in Hφ.
      apply right_left in H19.
      rewrite Hφ in H19; inversion H19; subst; auto.
      assert (beq_oid o1 o1 = true). apply beq_oid_same.
      try (inconsist).
      apply beq_oid_not_equal in H18.

      assert (Some (Heap_OBJ cls1 F1 lo1 ll1 ) =
              lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls F lo' ll)) o1 ).
      apply lookup_updated_not_affected with o (Heap_OBJ cls F lo' ll) h1; auto.
      
      assert (Some (Heap_OBJ cls2 F2 lo1 ll1) =
              lookup_heap_obj (update_heap_obj h2 o0 (Heap_OBJ cls0 F0 lo' ll0)) o3 ).
      apply lookup_updated_not_affected with o0 (Heap_OBJ cls0 F0 lo' ll0) h2; auto.
      apply  L_equivalence_tm_eq_object_L with cls1 F1 lo1 cls2 F2 ll1; auto.
      assert (left (reduce_bijection φ o o0 Hφ) o1 = left φ o1).
      apply reduce_bijection_lookup_neq_left.
      intro contra. subst; auto.
      assert (beq_oid o1 o1 = true). apply beq_oid_same.
      try (inconsist).
      rewrite H26. auto.

  - assert (o1 <> o). intro contra.
    subst; auto.
    inversion H17; subst; auto.
    rewrite <- H24 in H19; inversion H19; subst; auto.
    assert (flow_to (join_label lo1 ll3) L_Label = true). apply join_L_label_flow_to_L; auto.    
    try (inconsist).
    
    rewrite <- H19 in H5; inversion H5; subst; auto.
    try (inconsist).

    assert (o3 <> o0). intro contra.
    subst; auto.
    rewrite <- H21 in H6; inversion H6; subst; auto.
    try (inconsist).

    apply beq_oid_not_equal in H16.       apply beq_oid_not_equal in H18.
    assert (Some (Heap_OBJ cls1 F1 lb0 ll1) =
              lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls F lo' ll)) o1 ).
    apply lookup_updated_not_affected with o (Heap_OBJ cls F lo' ll) h1; auto.
      
    assert (Some (Heap_OBJ cls2 F2 lb3 ll2) =
              lookup_heap_obj (update_heap_obj h2 o0 (Heap_OBJ cls0 F0 lo' ll0)) o3 ).
    apply lookup_updated_not_affected with o0 (Heap_OBJ cls0 F0 lo' ll0) h2; auto.
    apply  L_equivalence_tm_eq_object_H with cls1 cls2 F1 lb0 F2 lb3 ll1 ll2; auto.
Qed. Hint Resolve lbl_H_raise_obj_both_lbl_preserve_l_eq_tm.



Lemma lbl_H_change_obj_both_lbl_preserve_l_eq_tm {DecOid : forall a1 a2 : oid, Decision (a1 = a2)} : forall  ct h1 h2 φ lo lo0 lo' F F0 o o0 lb1 lb2 cls cls0
  t1 t2 ll ll0,
    flow_to (join_label lo' ll)  L_Label = false ->
    wfe_heap ct h1 -> field_wfe_heap ct h1 ->
    wfe_heap ct h2 -> field_wfe_heap ct h2 ->  
    L_equivalence_heap h1 h2 φ ->
    Some (Heap_OBJ cls F lo ll) = lookup_heap_obj h1 o ->
    Some (Heap_OBJ cls0 F0 lo0 ll0) = lookup_heap_obj h2 o0 ->
    L_equivalence_tm (ObjId o) h1 (ObjId o0) h2 φ ->
    flow_to (join_label lo ll) L_Label = false  ->
    flow_to (join_label lo0 ll0) L_Label = false ->
    flow_to lb1 L_Label = true ->
    flow_to lb2 L_Label = true ->
    flow_to lb1 ll = true ->
    flow_to lb2 ll0 = true ->
    flow_to lo lo' = true ->
    flow_to lo0 lo' = true ->
    L_equivalence_tm t1 h1 t2 h2 φ ->
    L_equivalence_tm t1 (update_heap_obj h1 o (Heap_OBJ cls F lo' ll))
                     t2 (update_heap_obj h2 o0 (Heap_OBJ cls0 F0 lo' ll0)) φ.
    
Proof with eauto.
  intros.   
  generalize dependent t2.
  induction t1; intros; inversion H16; subst; auto.

  - assert (o1 <> o). intro contra.
    subst; auto.
    rewrite <- H5 in H19; inversion H19; subst; auto.
    assert (flow_to (join_label lo ll) L_Label = true). apply join_L_label_flow_to_L; auto. 
    try (inconsist).

    assert (o3 <> o0). intro contra.
    subst; auto.
    rewrite <- H22 in H6; inversion H6; subst; auto.
    assert (flow_to (join_label lo1 ll1) L_Label = true). apply join_L_label_flow_to_L; auto. 
    try (inconsist).

    apply beq_oid_not_equal in H17.       apply beq_oid_not_equal in H23.
    assert (Some (Heap_OBJ cls1 F1 lo1 ll1 ) =
              lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls F lo' ll)) o1 ).
    apply lookup_updated_not_affected with o (Heap_OBJ cls F lo' ll) h1; auto.
      
    assert (Some (Heap_OBJ cls2 F2 lo1 ll1 ) =
              lookup_heap_obj (update_heap_obj h2 o0 (Heap_OBJ cls0 F0 lo' ll0)) o3 ).
    apply lookup_updated_not_affected with o0 (Heap_OBJ cls0 F0 lo' ll0) h2; auto.
    apply  L_equivalence_tm_eq_object_L with cls1 F1 lo1 cls2 F2 ll1; auto.

  - case_eq (beq_oid o1 o); intro.
    + apply beq_oid_equal in H17; subst; auto.
      assert (Some (Heap_OBJ cls F lo' ll) =
              lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls F lo' ll)) o ).
      apply lookup_updated with h1 (Heap_OBJ cls1 F1 lb0 ll1); auto.
      case_eq (beq_oid o3 o0); intro.
      ++ apply beq_oid_equal in H22; subst; auto.
         assert (Some (Heap_OBJ cls0 F0 lo' ll0) =
              lookup_heap_obj (update_heap_obj h2 o0  (Heap_OBJ cls0 F0 lo' ll0)) o0 ).
         apply lookup_updated with h2 (Heap_OBJ cls2 F2 lb3 ll2); auto.
         apply L_equivalence_tm_eq_object_H with cls cls0 F lo'  F0 lo' ll ll0; auto.
         rewrite <- H18 in H5; inversion H5; subst; auto.
         rewrite <- H20 in H6; inversion H6; subst; auto.
         case_eq (flow_to ll2 L_Label); intro.
         case_eq (flow_to lb3 L_Label); intro.
         assert (flow_to (join_label lb3 ll2) L_Label = true). apply join_L_label_flow_to_L; auto. try (inconsist).
         assert (flow_to lo' L_Label = false). apply flow_transitive with lb3; auto.
         apply flow_transitive with lo'; auto.
         apply join_def_flow1 ; auto.          
         apply flow_transitive with ll2; auto.
         apply join_def_flow2 ; auto. 
      ++ assert (Some (Heap_OBJ cls2 F2 lb3 ll2) =
              lookup_heap_obj (update_heap_obj h2 o0 (Heap_OBJ cls0 F0 lo' ll0)) o3 ).
         apply lookup_updated_not_affected with o0 (Heap_OBJ cls0 F0 lo' ll0) h2; auto.
         apply L_equivalence_tm_eq_object_H with cls cls2 F lo'  F2 lb3 ll ll2; auto.
    + assert (Some (Heap_OBJ cls1 F1 lb0 ll1) =
              lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls F lo' ll)) o1 ).
      apply lookup_updated_not_affected with o (Heap_OBJ cls F lo' ll) h1; auto.
      case_eq (beq_oid o3 o0); intro.
      ++ apply beq_oid_equal in H23; subst; auto.
         assert (Some (Heap_OBJ cls0 F0 lo' ll0) =
              lookup_heap_obj (update_heap_obj h2 o0  (Heap_OBJ cls0 F0 lo' ll0)) o0 ).
         apply lookup_updated with h2 (Heap_OBJ cls2 F2 lb3 ll2); auto.
         apply L_equivalence_tm_eq_object_H with cls1 cls0 F1 lb0  F0 lo' ll1 ll0; auto.
         rewrite <- H20 in H6; inversion H6; subst; auto. 
         case_eq (flow_to ll2 L_Label); intro.
         case_eq (flow_to lb3 L_Label); intro.
         assert (flow_to (join_label lb3 ll2) L_Label = true). apply join_L_label_flow_to_L; auto. try (inconsist).
         assert (flow_to lo' L_Label = false). apply flow_transitive with lb3; auto.
         apply flow_transitive with lo'; auto.
         apply join_def_flow1 ; auto.          
         apply flow_transitive with ll2; auto.
         apply join_def_flow2 ; auto. 
      ++ assert (Some (Heap_OBJ cls2 F2 lb3 ll2) =
              lookup_heap_obj (update_heap_obj h2 o0 (Heap_OBJ cls0 F0 lo' ll0)) o3 ).
         apply lookup_updated_not_affected with o0 (Heap_OBJ cls0 F0 lo' ll0) h2; auto.
         apply L_equivalence_tm_eq_object_H with cls1 cls2 F1 lb0  F2 lb3 ll1 ll2; auto.
Qed. Hint Resolve lbl_H_change_obj_both_lbl_preserve_l_eq_tm. 

*)

Lemma lbl_H_raise_obj_both_lbl_preserve_l_eq_fs {DecOid : forall a1 a2 : oid, Decision (a1 = a2)} : forall  ct h1 h2 φ lo lo0 lo' F F0 o o0 lb1 lb2 cls cls0
   fs1 fs2 ll ll0,
    wfe_heap ct h1 -> field_wfe_heap ct h1 ->
    wfe_heap ct h2 -> field_wfe_heap ct h2 ->  
    L_equivalence_heap h1 h2 φ ->
    Some (Heap_OBJ cls F lo ll) = lookup_heap_obj h1 o ->
    Some (Heap_OBJ cls0 F0 lo0 ll0) = lookup_heap_obj h2 o0 ->
    L_equivalence_tm (ObjId o) h1 (ObjId o0) h2 φ ->
    flow_to lb1 L_Label = true ->
    flow_to lb2 L_Label = true ->
    flow_to lb1 ll = true ->
    flow_to lb2 ll0 = true ->
    flow_to lo lo' = true ->
    flow_to lo0 lo' = true ->
    L_equivalence_fs fs1 h1 fs2 h2 φ ->
    L_equivalence_fs fs1 (update_heap_obj h1 o (Heap_OBJ cls F lo' ll))
                     fs2 (update_heap_obj h2 o0 (Heap_OBJ cls0 F0 lo' ll0)) φ.
Proof with eauto.
  intros.
  generalize dependent fs2.
  induction fs1; intros; inversion H13; subst; auto.
  apply L_equal_fs; auto.
  eauto using lbl_L_change_obj_both_lbl_preserve_l_eq_tm.
Qed. Hint Resolve lbl_H_raise_obj_both_lbl_preserve_l_eq_fs.  


Lemma lbl_H_change_obj_both_lbl_preserve_l_eq_fs {DecOid : forall a1 a2 : oid, Decision (a1 = a2)} : forall  ct h1 h2 φ lo lo0 lo' F F0 o o0 lb1 lb2 cls cls0
  fs1 fs2 ll ll0,
    wfe_heap ct h1 -> field_wfe_heap ct h1 ->
    wfe_heap ct h2 -> field_wfe_heap ct h2 ->  
    L_equivalence_heap h1 h2 φ ->
    Some (Heap_OBJ cls F lo ll) = lookup_heap_obj h1 o ->
    Some (Heap_OBJ cls0 F0 lo0 ll0) = lookup_heap_obj h2 o0 ->
    L_equivalence_tm (ObjId o) h1 (ObjId o0) h2 φ ->
    flow_to lb1 L_Label = true ->
    flow_to lb2 L_Label = true ->
    flow_to lb1 ll = true ->
    flow_to lb2 ll0 = true ->
    flow_to lo lo' = true ->
    flow_to lo0 lo' = true ->
    L_equivalence_fs fs1 h1 fs2 h2 φ ->
    L_equivalence_fs fs1 (update_heap_obj h1 o (Heap_OBJ cls F lo' ll))
                     fs2 (update_heap_obj h2 o0 (Heap_OBJ cls0 F0 lo' ll0)) φ.
Proof with eauto.
  intros.
  generalize dependent fs2.
  induction fs1; intros; inversion H13; subst; auto.
  apply L_equal_fs; auto.
  eauto using lbl_L_change_obj_both_lbl_preserve_l_eq_tm.
Qed. Hint Resolve lbl_H_change_obj_both_lbl_preserve_l_eq_fs.


Lemma lbl_H_raise_obj_both_lbl_preserve_l_eq_store {DecOid : forall a1 a2 : oid, Decision (a1 = a2)} : forall  ct h1 h2 φ lo lo0 lo' F F0 o o0 lb1 lb2 cls cls0  sf1 sf2 ll ll0,
    wfe_heap ct h1 -> field_wfe_heap ct h1 ->
    wfe_heap ct h2 -> field_wfe_heap ct h2 ->  
    L_equivalence_heap h1 h2 φ ->
    Some (Heap_OBJ cls F lo ll) = lookup_heap_obj h1 o ->
    Some (Heap_OBJ cls0 F0 lo0 ll0) = lookup_heap_obj h2 o0 ->
    L_equivalence_tm (ObjId o) h1 (ObjId o0) h2 φ ->
    flow_to lb1 L_Label = true ->
    flow_to lb2 L_Label = true ->
    flow_to lb1 ll = true ->
    flow_to lb2 ll0 = true ->
    flow_to lo lo' = true ->
    flow_to lo0 lo' = true ->
    
    L_equivalence_store sf1 h1 sf2 h2 φ ->
    L_equivalence_store sf1 (update_heap_obj h1 o (Heap_OBJ cls F lo' ll))
                     sf2 (update_heap_obj h2 o0 (Heap_OBJ cls0 F0 lo' ll0)) φ.
Proof with eauto.
  intros.
  
  inversion H13; subst; auto. 
  apply L_equivalence_store_L; auto.
  split; auto. intros. 
  assert (L_equivalence_tm v1 h1 v2 h2 φ).
  apply H14 with x; auto.
  eauto using lbl_L_change_obj_both_lbl_preserve_l_eq_tm.
  apply H14.   
Qed. Hint Resolve lbl_H_raise_obj_both_lbl_preserve_l_eq_store .

Lemma lbl_H_change_obj_both_lbl_preserve_l_eq_store {DecOid : forall a1 a2 : oid, Decision (a1 = a2)} : forall  ct h1 h2 φ lo lo0 lo' F F0 o o0 lb1 lb2 cls cls0
                                                                                                                sf1 sf2 ll ll0,
    
    wfe_heap ct h1 -> field_wfe_heap ct h1 ->
    wfe_heap ct h2 -> field_wfe_heap ct h2 ->  
    L_equivalence_heap h1 h2 φ ->
    Some (Heap_OBJ cls F lo ll) = lookup_heap_obj h1 o ->
    Some (Heap_OBJ cls0 F0 lo0 ll0) = lookup_heap_obj h2 o0 ->
    L_equivalence_tm (ObjId o) h1 (ObjId o0) h2 φ ->
    flow_to lb1 L_Label = true ->
    flow_to lb2 L_Label = true ->
    flow_to lb1 ll = true ->
    flow_to lb2 ll0 = true ->
    flow_to lo lo' = true ->
    flow_to lo0 lo' = true ->
    L_equivalence_store sf1 h1 sf2 h2 φ ->
    L_equivalence_store sf1 (update_heap_obj h1 o (Heap_OBJ cls F lo' ll))
                     sf2 (update_heap_obj h2 o0 (Heap_OBJ cls0 F0 lo' ll0)) φ.
Proof with eauto.
  intros.
  inversion H13; subst; auto. 
  apply L_equivalence_store_L; auto.
  split; auto. intros. 
  assert (L_equivalence_tm v1 h1 v2 h2 φ).
  apply H14 with x; auto.
  eauto using lbl_L_change_obj_both_lbl_preserve_l_eq_tm. 
  apply H14.  
Qed. Hint Resolve lbl_H_change_obj_both_lbl_preserve_l_eq_store.



Lemma lbl_H_raise_obj_both_lbl_preserve_l_eq_ctn {DecOid : forall a1 a2 : oid, Decision (a1 = a2)} : forall  ct h1 h2 φ lo lo0 lo' F F0 o o0 lb1 lb2 cls cls0
   ctn1 ctn2 ll ll0,
    wfe_heap ct h1 -> field_wfe_heap ct h1 ->
    wfe_heap ct h2 -> field_wfe_heap ct h2 ->  
    L_equivalence_heap h1 h2 φ ->
    Some (Heap_OBJ cls F lo ll) = lookup_heap_obj h1 o ->
    Some (Heap_OBJ cls0 F0 lo0 ll0) = lookup_heap_obj h2 o0 ->
    L_equivalence_tm (ObjId o) h1 (ObjId o0) h2 φ ->
    flow_to lb1 L_Label = true ->
    flow_to lb2 L_Label = true ->
    flow_to lb1 ll = true ->
    flow_to lb2 ll0 = true ->
    flow_to lo lo' = true ->
    flow_to lo0 lo' = true ->
    L_eq_container ctn1 h1 ctn2 h2 φ ->
    L_eq_container ctn1 (update_heap_obj h1 o (Heap_OBJ cls F lo' ll))
                     ctn2 (update_heap_obj h2 o0 (Heap_OBJ cls0 F0 lo' ll0)) φ.
Proof with eauto.
  intros.  
  generalize dependent ctn2. 
  induction ctn1; intros;subst; auto;
  inversion H13; subst; auto.
  apply  L_eq_ctn; auto.
  eauto using lbl_L_change_obj_both_lbl_preserve_l_eq_tm.
  eauto using lbl_H_raise_obj_both_lbl_preserve_l_eq_fs.
  eauto using lbl_H_raise_obj_both_lbl_preserve_l_eq_store.
Qed. Hint Resolve lbl_H_raise_obj_both_lbl_preserve_l_eq_ctn.

Lemma lbl_H_change_obj_both_lbl_preserve_l_eq_ctn {DecOid : forall a1 a2 : oid, Decision (a1 = a2)} : forall  ct h1 h2 φ lo lo0 lo' F F0 o o0 lb1 lb2 cls cls0
  ctn1 ctn2 ll ll0,
    wfe_heap ct h1 -> field_wfe_heap ct h1 ->
    wfe_heap ct h2 -> field_wfe_heap ct h2 ->  
    L_equivalence_heap h1 h2 φ ->
    Some (Heap_OBJ cls F lo ll) = lookup_heap_obj h1 o ->
    Some (Heap_OBJ cls0 F0 lo0 ll0) = lookup_heap_obj h2 o0 ->
    L_equivalence_tm (ObjId o) h1 (ObjId o0) h2 φ ->
    flow_to lb1 L_Label = true ->
    flow_to lb2 L_Label = true ->
    flow_to lb1 ll = true ->
    flow_to lb2 ll0 = true ->
    flow_to lo lo' = true ->
    flow_to lo0 lo' = true ->
    L_eq_container ctn1 h1 ctn2 h2 φ ->
    L_eq_container ctn1 (update_heap_obj h1 o (Heap_OBJ cls F lo' ll))
                     ctn2 (update_heap_obj h2 o0 (Heap_OBJ cls0 F0 lo' ll0)) φ.
Proof with eauto.
  intros.
  generalize dependent ctn2. 
  induction ctn1; intros;subst; auto;
  inversion H13; subst; auto.
  apply  L_eq_ctn; auto.
   eauto using lbl_L_change_obj_both_lbl_preserve_l_eq_tm.
  eauto using lbl_H_raise_obj_both_lbl_preserve_l_eq_fs.
  eauto using lbl_H_raise_obj_both_lbl_preserve_l_eq_store.
Qed. Hint Resolve lbl_H_change_obj_both_lbl_preserve_l_eq_ctn.



Lemma lbl_H_raise_obj_both_lbl_preserve_l_eq_ctns {DecOid : forall a1 a2 : oid, Decision (a1 = a2)} : forall  ct h1 h2 φ lo lo0 lo' F F0 o o0 lb1 lb2 cls cls0 ctns1 ctns2 ll ll0,
    wfe_heap ct h1 -> field_wfe_heap ct h1 ->
    wfe_heap ct h2 -> field_wfe_heap ct h2 ->  
    L_equivalence_heap h1 h2 φ ->
    Some (Heap_OBJ cls F lo ll) = lookup_heap_obj h1 o ->
    Some (Heap_OBJ cls0 F0 lo0 ll0) = lookup_heap_obj h2 o0 ->
    L_equivalence_tm (ObjId o) h1 (ObjId o0) h2 φ ->
    flow_to lb1 L_Label = true ->
    flow_to lb2 L_Label = true ->
    flow_to lb1 ll = true ->
    flow_to lb2 ll0 = true ->
    flow_to lo lo' = true ->
    flow_to lo0 lo' = true ->
    L_eq_ctns ctns1 h1 ctns2 h2 φ ->
    L_eq_ctns ctns1 (update_heap_obj h1 o (Heap_OBJ cls F lo' ll))
                     ctns2 (update_heap_obj h2 o0 (Heap_OBJ cls0 F0 lo' ll0)) φ.
Proof with eauto.
  intros.  
  generalize dependent ctns2. 
  induction ctns1; intros;subst; auto;
  inversion H13; subst; auto.
  apply  L_eq_ctns_list; auto.
  apply lbl_H_raise_obj_both_lbl_preserve_l_eq_ctn with ct lo lo0 lb1 lb2; auto.
Qed. Hint Resolve lbl_H_raise_obj_both_lbl_preserve_l_eq_ctns.


  


Lemma lbl_change_obj_both_lbl_preserve_l_eq_config: forall  ct h1 h2 φ lo lo0 lo' F F0 o o0
                                                              t1 fs1 sf1 lb1
                                                              t2 fs2 sf2 lb2 cls cls0 ctns1 ctns2 ll ll0,
    valid_config (Config ct (Container t1 fs1 lb1 sf1 ) ctns1  h1)  ->
    valid_config (Config ct (Container t2 fs2 lb2 sf2) ctns2  h2)  ->
    L_equivalence_heap h1 h2 φ ->
    Some (Heap_OBJ cls F lo ll) = lookup_heap_obj h1 o ->
    Some (Heap_OBJ cls0 F0 lo0 ll0) = lookup_heap_obj h2 o0 ->
    L_equivalence_tm (ObjId o) h1 (ObjId o0) h2 φ ->
    flow_to lb1 L_Label = true ->
    flow_to lb2 L_Label = true ->
    flow_to lb1 ll = true ->
    flow_to lb2 ll0 = true ->
    flow_to lo lo' = true ->
    flow_to lo0 lo' = true ->
    L_equivalence_config (Config ct (Container t1 fs1 lb1 sf1) ctns1  h1)
                   (Config ct (Container t2 fs2 lb2 sf2) ctns2  h2) φ ->
    L_equivalence_config (Config ct (Container t1 fs1 lb1 sf1) ctns1  (update_heap_obj h1 o (Heap_OBJ cls F lo' ll)))
                   (Config ct (Container t2 fs2 lb2 sf2) ctns2  (update_heap_obj h2 o0 (Heap_OBJ cls0 F0 lo' ll0))) φ .
Proof with eauto.
  intros.
  inversion H; subst; auto.
  inversion H20; subst; auto.
  inversion H0; subst; auto.
  inversion H30; subst; auto. 
  

  remember (Config ct (Container t1 fs1 lb1 sf1 ) ctns1  h1) as config1.
  remember (Config ct (Container t2 fs2 lb2 sf2) ctns2  h2) as config2.

  generalize dependent t1. generalize dependent t2.
  generalize dependent fs1. generalize dependent fs2.
  generalize dependent sf1. generalize dependent sf2.
  generalize dependent ctns1. generalize dependent ctns2. 
  induction H11; subst; intros; inversion Heqconfig1; inversion Heqconfig2; subst; auto.
  - apply L_equivalence_config_L; auto.
    assert (forall a1 a2 : oid, Decision (a1 = a2)). auto. 
    apply lbl_H_change_obj_both_lbl_preserve_l_eq_ctn with ct lo lo0 lb2 lb2; auto.
    assert (forall a1 a2 : oid, Decision (a1 = a2)). auto. 
    apply  lbl_H_raise_obj_both_lbl_preserve_l_eq_ctns with ct lo lo0 lb2 lb2; auto.
  - try (inconsist).
Qed. Hint Resolve lbl_change_obj_both_lbl_preserve_l_eq_config. 





Lemma ctns_eq_lead_to_low_component_eq : forall ct h1 h2
                                                  t1 fs1 lb1 sf1
                                                  t2 fs2 lb2 sf2
                                                  ctns1 ctns2 φ,
      L_eq_ctns ctns1 h1 ctns2 h2 φ ->
      flow_to lb1 L_Label = false ->
      flow_to lb2 L_Label = false ->
      L_equivalence_config
        (low_component ct (Container t1 fs1 lb1 sf1) ctns1 h1)
        (low_component ct (Container t2 fs2 lb2 sf2) ctns2 h2) φ.
  Proof with eauto.
    intros. generalize dependent ctns2. 
    induction ctns1. intros. inversion H; subst.
    unfold low_component. rewrite H0. rewrite H1.
    apply L_equivalence_config_L ; auto.
    apply L_eq_ctn; auto.
    apply L_equivalence_store_L; intros.
    split; auto.
    intros. try (empty_sf).
    split; auto. 
    
    intros. inversion H; subst; auto.
    destruct a. destruct ctn2.
    inversion H4; subst; auto.
    unfold low_component. rewrite H0. rewrite H1.
    fold low_component. 
    
    assert ((low_component ct (Container t f l0 s) ctns1 h1)  =
            (Config ct (Container t f l0 s) ctns1 h1)).
    apply low_component_with_L_Label; auto.

    assert ((low_component ct (Container t0 f0 l0 s0) ctns3 h2)  =
            (Config ct (Container t0 f0 l0 s0) ctns3 h2)).
    apply low_component_with_L_Label; auto.

    rewrite H2. rewrite H3.
    apply L_equivalence_config_L ; auto.
  Qed.  Hint Resolve ctns_eq_lead_to_low_component_eq.   

 
    Lemma join_label_flow_L : forall lbv1 lbv2 lb1 lov1 lov2,
        flow_to lbv1 L_Label = true /\
              flow_to lbv2 L_Label = true /\       
       flow_to lb1 L_Label = true /\       
       flow_to lov1 L_Label = true /\       
       flow_to lov2 L_Label = true ->
       flow_to (join_label (join_label (join_label lbv1 lbv2) lb1)
             (join_label (lov1) (lov2))) L_Label = true.
    Proof with eauto.
      intros.
      destruct H. destruct H0. destruct H1. destruct H2.  
      apply join_L_label_flow_to_L; auto.
      apply join_L_label_flow_to_L; auto.
      apply join_L_label_flow_to_L; auto. 
      apply join_L_label_flow_to_L; auto.
      Qed. Hint Resolve join_label_flow_L.

    Lemma join_label_dist : forall lbv1 lbv2 lb1 lov1 lov2,
       flow_to (join_label (join_label (join_label lbv1 lbv2) lb1)
             (join_label (lov1) (lov2))) L_Label = true ->
              flow_to lbv1 L_Label = true /\
              flow_to lbv2 L_Label = true /\       
       flow_to lb1 L_Label = true /\       
       flow_to lov1 L_Label = true /\       
       flow_to lov2 L_Label = true.
    Proof with eauto.
      intros.
      apply flow_dist in H. destruct H.
      apply flow_dist in H. destruct H.
      apply flow_dist in H. destruct H.
      apply flow_dist in H0. destruct H0.
      split; auto.
    Qed. Hint Resolve join_label_dist. 
      
    Lemma join_label_flow_H : forall lbv1 lbv2 lb1 lov1 lov2,
        flow_to lbv1 L_Label = false \/
              flow_to lbv2 L_Label = false \/       
       flow_to lb1 L_Label = false \/
       flow_to lov1 L_Label = false \/       
       flow_to lov2 L_Label = false ->
        flow_to (join_label (join_label (join_label lbv1 lbv2) lb1)
             (join_label (lov1) (lov2))) L_Label = false.
    Proof with eauto.
      intros.
      destruct H.
      + apply flow_join_label with (join_label (join_label lbv1 lbv2) lb1) (join_label lov1 lov2); auto.
        apply flow_join_label with (join_label lbv1 lbv2) lb1; auto.
        apply flow_join_label with lbv1 lbv2; auto.
        apply join_label_commutative.
        apply join_label_commutative.
        apply join_label_commutative.

      + destruct H.
        ++ 
        apply flow_join_label with (join_label (join_label lbv1 lbv2) lb1) (join_label lov1 lov2); auto.
        apply flow_join_label with (join_label lbv1 lbv2) lb1; auto.
        apply flow_join_label with lbv2 lbv1; auto.
        apply join_label_commutative.
        apply join_label_commutative.
        ++
          destruct H.         
          apply flow_join_label with (join_label (join_label lbv1 lbv2) lb1) (join_label lov1 lov2); auto.
        apply flow_join_label with lb1 (join_label lbv1 lbv2); auto.
        apply join_label_commutative.
        +++ destruct H. 
        apply flow_join_label with  (join_label lov1 lov2) (join_label (join_label lbv1 lbv2) lb1); auto.
        apply flow_join_label with lov1 lov2; auto.
        apply join_label_commutative.
            ++++ apply flow_join_label with (join_label lov1 lov2) (join_label (join_label lbv1 lbv2) lb1); auto.
        apply flow_join_label with lov2 lov1; auto.
Qed. Hint Resolve join_label_flow_H .         






  (* heap bijection preservation *)
Lemma update_field_preserve_bijection_new : forall ct h1 h2 φ cls F lo
                                                 cls0 F0 lo0
                                                 lx lx0 v v0 f0
                                                 o o0 lb1 lb2 ll ll0
                                                 ,
    
    (v = null \/
       (exists (o0 : oid) (cls0 : CLASS) (F0 : FieldMap) (lo0 : Label) ll0,
          v = ObjId o0 /\ Some (Heap_OBJ cls0 F0 lo0 ll0) = lookup_heap_obj h1 o0)) ->
    (v0 = null \/
        (exists (o0 : oid) (cls0 : CLASS) (F0 : FieldMap) (lo1 : Label) ll1, 
           v0 = ObjId o0 /\ Some (Heap_OBJ cls0 F0 lo1 ll1) = lookup_heap_obj h2 o0) ) ->
    wfe_heap ct h1 -> field_wfe_heap ct h1 ->
    wfe_heap ct h2 -> field_wfe_heap ct h2 ->
    L_equivalence_heap h1 h2 φ ->
    Some (Heap_OBJ cls F lo ll) = lookup_heap_obj h1 o ->
    Some (Heap_OBJ cls0 F0 lo0 ll0) = lookup_heap_obj h2 o0 ->
    flow_to (join_label lb1 lx) (join_label lo ll) = true ->
    flow_to (join_label lb2 lx0) (join_label lo0 ll0) = true ->
    L_equivalence_tm (ObjId o) h1 (ObjId o0) h2 φ ->
    flow_to lb1 L_Label = true ->
    flow_to lb2 L_Label = true ->
    L_equivalence_tm (v_opa_l v lx) h1 (v_opa_l v0 lx0) h2 φ ->
    L_equivalence_heap (update_heap_obj h1 o (Heap_OBJ cls (fields_update F f0 v) lo ll))
                       (update_heap_obj h2 o0 (Heap_OBJ cls0 (fields_update F0 f0 v0) lo0 ll0)) φ.
    
Proof with eauto.
  intros ct h1 h2 φ cls F lo
         cls0 F0 lo0
         lx lx0 v v0 f0
         o o0 lb1 lb2 ll ll0.
        
  intros H_v. intro H_v0. intros.   
  inversion H8; subst; auto.
  rewrite <- H15 in H4; inversion H4; subst; auto.
  rewrite <- H18 in H5; inversion H5; subst; auto.
  inversion H11; subst; auto. 
  -   (* opa_l has low label*)
  inversion H3; subst; auto.
  + apply L_eq_heap; auto. 
  ++  intros.
      assert (L_equivalence_object o1 h1 o2 h2 φ) as H_eq_o1_o2.
      +++
        apply H12; auto. 
      +++
        inversion H_eq_o1_o2; subst; auto.
    *
    case_eq (beq_oid o1 o); intro.
    **
    apply beq_oid_equal in H30.
    rewrite H30 in H24. rewrite <- H24 in H15; inversion H15; subst.
    assert ( Some  (Heap_OBJ cls3 (fields_update F0 f0 v) lb ll)  =
      lookup_heap_obj  (update_heap_obj h1 o (Heap_OBJ cls3 (fields_update F0 f0 v) lb ll))  o).
    apply lookup_updated with h1  (Heap_OBJ cls3 F0 lb ll); auto.
    case_eq (beq_oid o2 o0); intro.
    ***
    apply beq_oid_equal in H31.
    rewrite H31 in H27; rewrite <- H27 in H18; inversion H18; subst; auto.  

    assert ( Some  (Heap_OBJ cls3 (fields_update F3 f0 v0) lb ll)  =
      lookup_heap_obj  (update_heap_obj h2 o0 (Heap_OBJ cls3 (fields_update F3 f0 v0) lb ll))  o0).
    apply lookup_updated with h2  (Heap_OBJ cls3 F3 lb ll ); auto.
    apply object_equal_H with lb cls3 cls3
                              (fields_update F0 f0 v)
                              (fields_update F3 f0 v0) ll; auto.
    ***
      rewrite H14 in H23;inversion H23; subst; auto.
      pose proof (beq_oid_same o2); try (inconsist).
    (*beq_oid o1 o = false *)
    ** case_eq (beq_oid o2 o0); intro.
       ***
       apply beq_oid_equal in H31.
       subst; auto. 
       apply right_left in H14.
       apply right_left in H23.
       rewrite H14 in H23; inversion H23; subst; auto.
       pose proof (beq_oid_same o1); try (inconsist).

       ***
       assert (Some  (Heap_OBJ cls3 F0 lb ll)  =
           lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls1 (fields_update F1 f0 v) lo1 ll1))  o1
           ).
       apply lookup_updated_not_affected with o (Heap_OBJ cls1 (fields_update F1 f0 v) lo1 ll1) h1; auto.
       intro contra; subst; auto. pose proof (beq_oid_same o); try (inconsist).

       assert (Some  (Heap_OBJ cls3 F3 lb ll)  =
           lookup_heap_obj (update_heap_obj h2 o0 (Heap_OBJ cls2 (fields_update F2 f0 v0) lo1 ll1))  o2
           ).
       apply lookup_updated_not_affected with o0  (Heap_OBJ cls2 (fields_update F2 f0 v0) lo1 ll1)  h2; auto.
       intro contra; subst; auto. pose proof (beq_oid_same o0); try (inconsist).
       eauto using  object_equal_H.
    * 
      destruct H30. destruct H31. destruct H32.
      case_eq (beq_oid o1 o); intro.
    **
    apply beq_oid_equal in H34.
    rewrite H34 in H24. rewrite <- H24 in H15; inversion H15; subst.
    assert ( Some  (Heap_OBJ cls3 (fields_update F0 f0 v) lb ll)  =
      lookup_heap_obj  (update_heap_obj h1 o (Heap_OBJ cls3 (fields_update F0 f0 v) lb ll))  o).
    apply lookup_updated with h1  (Heap_OBJ cls3 F0 lb ll); auto.
    case_eq (beq_oid o2 o0); intro.
    ***
    apply beq_oid_equal in H34.
    rewrite H34 in H27; rewrite <- H27 in H18; inversion H18; subst; auto.  
    assert ( Some  (Heap_OBJ cls3 (fields_update F3 f0 v0) lb ll)  =
      lookup_heap_obj  (update_heap_obj h2 o0 (Heap_OBJ cls3 (fields_update F3 f0 v0) lb ll))  o0).
    apply lookup_updated with h2  (Heap_OBJ cls3 F3 lb ll ); auto.
    apply object_equal_L with lb cls3 cls3
                              (fields_update F0 f0 v)
                              (fields_update F3 f0 v0) ll; auto.

    split; auto.
    split; auto. split; auto. 
    intro. unfold  fields_update in H35.
    case_eq (beq_id f0 fname); intro.
    rewrite H36 in H35;  inversion H35. 
    rewrite H36 in H35.  apply H31 in H35. 
    unfold  fields_update. rewrite H36; auto.

    intro. unfold  fields_update in H35.
    case_eq (beq_id f0 fname); intro.
    rewrite H36 in H35.  inversion H35. 
    rewrite H36 in H35.  destruct H31 with fname.
    apply H38 in H35. 
    unfold  fields_update. rewrite H36. auto.

    split; auto.
    intro. split; auto.
    intro. unfold  fields_update in H35.
    (* case_eq (beq_id f0 fname) *)
    case_eq (beq_id f0 fname); intro.
    rewrite H36 in H35; inversion H35.
    rewrite H38 in H26; inversion H26; auto. 
    unfold  fields_update. rewrite H36; auto.

    rewrite H36 in H35. apply H32 in H35. 
    unfold  fields_update. rewrite H36; auto.

    intro. unfold  fields_update in H35.
    case_eq (beq_id f0 fname); intro.
    rewrite H36 in H35; inversion H35.
    rewrite H38 in H26; inversion H26; auto. 
    unfold  fields_update. rewrite H36; auto.

    rewrite H36 in H35. destruct H32 with fname.
    apply H32 in H35. 
    unfold  fields_update. rewrite H36; auto.

    intros. unfold  fields_update in H35. 
    unfold  fields_update in H36.
    case_eq (beq_id f0 fname); intro.
    ++++
    rewrite H37 in H35; rewrite H37 in H36.
    inversion H35. inversion H36. 

    case_eq (beq_oid fo1 o); intro.
    +++++
    apply beq_oid_equal in H38.
    rewrite <- H38 in H24. 
    assert (Some (Heap_OBJ cls3 (fields_update F0 f0 (ObjId fo1)) lb ll)
            = lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls3 (fields_update F0 f0 (ObjId fo1)) lb ll)) fo1).
    apply lookup_updated with h1 (Heap_OBJ cls3 F0 lb ll); auto.
    rewrite H38; auto.

    case_eq (beq_oid fo2 o0); intro.
    ++++++
    apply beq_oid_equal in H42.
    rewrite <- H42 in H27. 
    assert (Some (Heap_OBJ cls3 (fields_update F3 f0 (ObjId fo2)) lb ll)
            = lookup_heap_obj (update_heap_obj h2 o0 (Heap_OBJ cls3 (fields_update F3 f0 (ObjId fo2)) lb ll)) fo2).
    apply lookup_updated with h2 (Heap_OBJ cls3 F3 lb ll); auto.
    rewrite H42; auto.
    exists cls3. exists cls3. exists lb. exists lb.
    exists (fields_update F0 f0 (ObjId fo1)).
    exists (fields_update F3 f0 (ObjId fo2)).
    exists ll. exists ll.  
    split; auto. split; auto.
    subst; auto. left; auto. 

    ++++++
    (* if fo1 = o, then fo2 must be equal to o2*)
    subst; auto.
    inversion H11; subst; auto.
    inversion H49; subst; auto.
    rewrite H40 in H14; inversion H14; subst; auto.
    pose proof (beq_oid_same o0);    try (inconsist).
    
    rewrite <- H40 in H24; inversion H24; subst; auto.
    try (inconsist_label).
    try (inconsist_label).
    (*
    assert (flow_to (join_label lb1 lx0) L_Label = false).
    apply flow_join_label with lx0 lb1; auto. 

    assert (flow_to (join_label lo ll) L_Label = false).
    apply flow_transitive with (join_label lb1 lx0); auto.
    try (inconsist_label).
    *) 
    +++++
    (* beq_oid fo1 o = false*)
    subst; auto. 
    inversion H26; subst; auto.
    case_eq (beq_oid fo2 o0); intro.
    ++++++    
    (* inconsist assumption *)
    apply beq_oid_equal in H39.
    subst; auto.
    apply right_left in H14.
    apply right_left in H41.
    rewrite H41 in H14.
    inversion H14; subst; auto. 
    pose proof (beq_oid_same o).
    try (inconsist).
    ++++++
    (* beq_oid fo2 o0 = false*)
    assert (Some (Heap_OBJ cls1 F1 lo ll0) =
            lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls3 (fields_update F0 f0 (ObjId fo1)) lb ll)) fo1 
           ).
    apply lookup_updated_not_affected with o (Heap_OBJ cls3 (fields_update F0 f0 (ObjId fo1)) lb ll)  h1; auto.
    intro contra. subst; auto. pose proof (beq_oid_same o); try (inconsist).

    assert (Some (Heap_OBJ cls2 F2 lo ll0) =
           lookup_heap_obj (update_heap_obj h2 o0 (Heap_OBJ cls3 (fields_update F3 f0 (ObjId fo2)) lb ll)) fo2
           ).
    apply lookup_updated_not_affected with o0 (Heap_OBJ cls3 (fields_update F3 f0 (ObjId fo2)) lb ll) h2; auto.
    intro contra. subst; auto. pose proof (beq_oid_same o0); try (inconsist).
    
    exists cls1. exists cls2.
    exists lo. exists lo.
    exists F1. exists F2.
    exists ll0. exists ll0. 
    split; auto. split; auto.
    left. split; auto. split; auto. split; auto.
    split; auto. 
    apply H12 in H41; inversion H41; subst; auto.
    rewrite <- H46 in H42; inversion H42; subst; auto.
    rewrite <- H47 in H45; inversion H45; subst; auto.
    rewrite <- H46 in H42; inversion H42; subst; auto.
    rewrite <- H47 in H45; inversion H45; subst; auto.
    apply H50. 

    ++++++
    
      (*cannot assign H objects to L objects*)
      (*
    destruct H_v.  inversion H39.
    destruct H39 as [o'].
    destruct H39 as [cls'].
    destruct H39 as [F'].
    destruct H39 as [lo'].
    destruct H39 as [ll'].
    destruct H39.
    inversion H39; subst; auto.
       *)
    case_eq (beq_oid fo2 o0); intro.
    +++++++
      apply beq_oid_equal in H39; subst; auto.
    rewrite <- H42 in H27; inversion H27; subst; auto.
    try (inconsist).
    +++++++
      assert (Some (Heap_OBJ cls1 F1 lo1 ll1) =
            lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls3 (fields_update F0 f0 (ObjId fo1)) lb ll)) fo1
             ).
    apply lookup_updated_not_affected with o  (Heap_OBJ cls3 (fields_update F0 f0 (ObjId fo1)) lb ll) h1; auto.
    intro contra; subst; auto. pose proof (beq_oid_same o). try (inconsist).
    assert (Some (Heap_OBJ cls2 F2 lo2 ll2) =
           lookup_heap_obj (update_heap_obj h2 o0 (Heap_OBJ cls3 (fields_update F3 f0 (ObjId fo2)) lb ll)) fo2
           ).
    apply lookup_updated_not_affected with o0  (Heap_OBJ cls3 (fields_update F3 f0 (ObjId fo2)) lb ll) h2; auto.
    intro contra; subst; auto. pose proof (beq_oid_same o0). try (inconsist).

    
    exists cls1. exists cls2.
    exists lo1. exists lo2.
    exists F1. exists F2.
    exists ll1. exists ll2.  
    split; auto.


    ++++ (* beq_id f0 fname = false *)
    rewrite H37 in H35. rewrite H37 in H36.
    destruct H33 with fname fo1 fo2; auto.
    destruct H38 as [cls_f2]. rename x into cls_f1.
    destruct H38 as [lof1]. destruct H38 as [lof2].
    destruct H38 as [FF1]. destruct H38 as [FF2].
    destruct H38 as [llf1]. destruct H38 as [llf2].
    destruct H38.  destruct H39. 
    
    case_eq (beq_oid fo1 o); intro.
    +++++
    apply beq_oid_equal in H41.
    rewrite <- H41 in H24.
    assert (Some (Heap_OBJ cls3 (fields_update F0 f0 v) lb ll)
            = lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls3 (fields_update F0 f0 v) lb ll)) fo1).
    apply lookup_updated with h1 (Heap_OBJ cls3 F0 lb ll); auto.
    rewrite H41; auto.
    
    case_eq (beq_oid fo2 o0); intro.
    ++++++
      
    apply beq_oid_equal in H43.
    rewrite <- H43 in H27.
    assert (Some (Heap_OBJ cls3 (fields_update F3 f0 v0) lb ll)
            = lookup_heap_obj (update_heap_obj h2 o0 (Heap_OBJ cls3 (fields_update F3 f0 v0) lb ll)) fo2).
    apply lookup_updated with h2 (Heap_OBJ cls3 F3 lb ll); auto.
    rewrite H43; auto.
    
    exists cls3. exists cls3.
    exists lb. exists lb.
    exists (fields_update F0 f0 v). exists (fields_update F3 f0 v0).
    exists ll. exists ll.  
    split; auto.
    split; auto.
    destruct H40. 
    left; split; auto.    apply H40.

    subst; auto.
    destruct H40.
    rewrite H38 in H24; inversion H24; subst; auto. 
    
    (* if fo1 = o, then fo2 must be equal to o2*)
    ++++++ (*  beq_oid fo2 o0 = false *)
      subst; auto.
    destruct H40. destruct H40. 
    rewrite  H40 in H14; inversion H14; subst; auto.
    pose proof (beq_oid_same o0).
    try (inconsist).

    apply H19 in H38; auto. rewrite H38 in H23; inversion H23.
    apply H40. 

    (* beq_oid fo1 o = false*)
    +++++ (* beq_oid fo1 o = false *)
      case_eq (beq_oid fo2 o0); intro.
    (* inconsist assumption *)
    apply beq_oid_equal in H42.
    subst; auto.
    apply right_left in H14.    
    destruct H40. destruct H40. 
    apply right_left in H40.
    rewrite H40 in H14.
    inversion H14; subst; auto. 
    pose proof (beq_oid_same o).
    try (inconsist).

    rewrite H39 in H27; inversion H27; subst; auto.
    destruct H40.
    try (inconsist).

    (* beq_oid fo2 o0 = false*)
    assert (Some (Heap_OBJ cls_f1 FF1 lof1 llf1) =
            lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls3 (fields_update F0 f0 v) lb ll)) fo1 
           ).
    apply lookup_updated_not_affected with o (Heap_OBJ cls3 (fields_update F0 f0 v) lb ll)  h1; auto.
    intro contra; subst; auto. pose proof (beq_oid_same o). try (inconsist).
    
    assert (Some  (Heap_OBJ cls_f2 FF2 lof2 llf2) =
           lookup_heap_obj (update_heap_obj h2 o0 (Heap_OBJ cls3 (fields_update F3 f0 v0) lb ll)) fo2
           ).
    apply lookup_updated_not_affected with o0 (Heap_OBJ cls3 (fields_update F3 f0 v0) lb ll) h2; auto.
    intro contra; subst; auto. pose proof (beq_oid_same o0). try (inconsist).
    
    exists  cls_f1. exists cls_f2.
    exists lof1. exists lof2.
    exists FF1. exists FF2.
    exists llf1. exists llf2. 
    split; auto.

    ***
    rewrite H14 in H23; inversion H23; subst; auto.
    pose proof (beq_oid_same o2).
    try (inconsist).

    (*beq_oid o2 o0 = true*)
    **
      case_eq (beq_oid o2 o0); intro.
    apply beq_oid_equal in H35.
    subst; auto. 
    apply right_left in H14.
    apply right_left in H23.
    rewrite H14 in H23; inversion H23; subst; auto.
    pose proof (beq_oid_same o1).
    try (inconsist).

     assert (Some  (Heap_OBJ cls0 F0 lb ll)  =
           lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls1 (fields_update F1 f0 v) lo1 ll1))  o1
           ).
    apply lookup_updated_not_affected with o (Heap_OBJ cls1 (fields_update F1 f0 v) lo1 ll1) h1; auto.
    intro contra; subst; auto. pose proof (beq_oid_same o). try (inconsist).
    
    assert (Some  (Heap_OBJ cls3 F3 lb ll)  =
           lookup_heap_obj (update_heap_obj h2 o0 (Heap_OBJ cls2 (fields_update F2 f0 v0) lo1 ll1))  o2
           ).
    apply lookup_updated_not_affected with o0  (Heap_OBJ cls2 (fields_update F2 f0 v0) lo1 ll1)  h2; auto.
    intro contra; subst; auto. pose proof (beq_oid_same o0). try (inconsist).
    
    apply  object_equal_L with lb cls0 cls3 F0 F3 ll; auto.

    split; auto. split; auto. split; auto.
    
    intros.
    destruct H33 with fname fo1 fo2; auto.
    rename x into cls_f1. destruct H40 as [cls_f2].
    destruct H40 as [lof1]. destruct H40 as [lof2].
    destruct H40 as [FF1]. destruct H40 as [FF2].
    destruct H40 as [llf1]. destruct H40 as [llf2]. 
    destruct H40.   destruct H41.
    
    case_eq (beq_oid fo1 o); intro.
    apply beq_oid_equal in H43.
    subst; auto.
    rewrite H14 in H42.  destruct H42. destruct H30. inversion H30; subst; auto.
    assert (Some (Heap_OBJ cls1 (fields_update F1 f0 v) lo1 ll1)
            = lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls1 (fields_update F1 f0 v) lo1 ll1)) o).
    apply lookup_updated with h1 (Heap_OBJ cls_f1 FF1 lof1 llf1); auto.

    assert (Some (Heap_OBJ cls2  (fields_update F2 f0 v0) lo1 ll1)
            = lookup_heap_obj (update_heap_obj h2 fo2 (Heap_OBJ cls2 (fields_update F2 f0 v0) lo1 ll1)) fo2).
    apply lookup_updated with h2 (Heap_OBJ cls_f2 FF2 lof2 llf2); auto.
    exists cls1. exists cls2.
    exists lo1. exists lo1.
    exists (fields_update F1 f0 v).
    exists (fields_update F2 f0 v0).
    exists ll1. exists ll1. 
    split; auto.
    split; auto.
    left; auto.
    split; auto.
    split; auto. split; auto.  split; auto. 
    rewrite H40 in H15; inversion H15; subst; auto.
    rewrite H41 in H18; inversion H18; subst; auto.
    apply H42. 

    (*flow_to lof2 L_Label = false /\ flow_to lof1 L_Label = false*)
    rewrite H40 in H15; inversion H15; subst; auto.
    destruct H30. 
    try (inconsist).

    (*beq_oid fo1 o = false*)        
    case_eq (beq_oid fo2 o0); intro.
    apply beq_oid_equal in H44.
    rewrite H44 in H42.
    destruct H42.
    destruct H42.
    apply right_left in H42.
    apply right_left in H14.
    rewrite H42 in H14; inversion H14; subst; auto.
    pose proof (beq_oid_same o).
    try (inconsist).
    subst; auto.
    rewrite H41 in H18; inversion H18; subst; auto.
    destruct H42.  try (inconsist).

    (* beq_oid fo2 o0 = false*)
    assert (Some (Heap_OBJ cls_f1 FF1 lof1 llf1) =
            lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls1 (fields_update F1 f0 v) lo1 ll1)) fo1
           ).
    apply lookup_updated_not_affected with o (Heap_OBJ cls1 (fields_update F1 f0 v) lo1 ll1)  h1; auto.
    intro contra; subst; auto. pose proof (beq_oid_same o). try (inconsist).
    
    subst; auto.
    assert (Some  (Heap_OBJ cls_f2 FF2 lof2 llf2) =
           lookup_heap_obj (update_heap_obj h2 o0 (Heap_OBJ cls2 (fields_update F2 f0 v0) lo1 ll1)) fo2
           ).
    apply lookup_updated_not_affected with o0 (Heap_OBJ cls2 (fields_update F2 f0 v0) lo1 ll1) h2; auto.
    intro contra; subst; auto. pose proof (beq_oid_same o0). try (inconsist).

    exists cls_f1. exists cls_f2.
    exists lof1. exists lof2.
    exists FF1. exists FF2.
    exists llf1. exists llf2.  
    split; auto.

      ++ (* None -> left φ o1 = None *)
    intros. apply lookup_updated_heap_must_none in H23.
    apply H13 in H23; auto. 

      ++ (* o1 = None -> right φ o1 = None *)
    intros. apply lookup_updated_heap_must_none in H23.
    apply H17 in H23. auto.

      ++(* flow_to lb L_Label = false  *)
    intros.
    case_eq (beq_oid o1 o); intro.
    assert ( Some (Heap_OBJ cls F lb ll) = lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls1 (fields_update F1 f0 v) lo1 ll1)) o1 ). auto.
    apply lookup_updated_heap_new_obj in H28; auto.
    inversion H28; subst; auto.
    try (inconsist).
    
    assert (Some (Heap_OBJ cls F lb ll) =
            lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls1 (fields_update F1 f0 v) lo1 ll1)) o1
           ). auto.
    apply lookup_updated_heap_old_obj in H28; auto.
    assert ( lookup_heap_obj h1 o1 = Some (Heap_OBJ cls F lb ll) ); auto.
    apply H19 in H29; auto. 

  ++ (*flow_to lb L_Label = false -> right φ o1 = None *)
    intros.
    case_eq (beq_oid o1 o0); intro.
    assert ( Some (Heap_OBJ cls F lb ll) = lookup_heap_obj (update_heap_obj h2 o0 (Heap_OBJ cls2 (fields_update F2 f0 v0) lo1 ll1)) o1 ). auto.
    apply lookup_updated_heap_new_obj in H28; auto.
    inversion H28; subst; auto. try (inconsist).
    
    assert (Some (Heap_OBJ cls F lb ll) =
            lookup_heap_obj (update_heap_obj h2 o0 (Heap_OBJ cls2 (fields_update F2 f0 v0) lo1 ll1)) o1
           ). auto.
    apply lookup_updated_heap_old_obj in H28; auto.
    assert ( lookup_heap_obj h2 o1 = Some (Heap_OBJ cls F lb ll) ); auto.
    apply H21 in H29; auto.


  -  (*  flow_to ll1 L_Label = true /\ flow_to ll1 L_Label = false*)

    assert (flow_to (join_label lo1 ll1) L_Label = false).
    apply flow_transitive with  (join_label lb1 lx); auto.
    apply flow_transitive with lx; auto.
    apply join_def_flow2.     

    inversion H3; subst; auto. 
    apply  L_eq_heap; auto. 
    + intros. assert ( L_equivalence_object o1 h1 o2 h2 φ). 
      apply H13; auto.  inversion H27; subst; auto.
      ++ 
        case_eq (beq_oid o1 o); intro.
        +++
      (*impossible*)
      apply beq_oid_equal in H32.
      rewrite H32 in H28.
      rewrite <- H28 in H15; inversion H15; subst; auto.
      rewrite H24 in H14; inversion H14; subst; auto. 
      rewrite <- H29 in H18; inversion H18; subst; auto.

      assert (Some (Heap_OBJ cls3 (fields_update F0 f0 v) lb ll) =
            lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls3 (fields_update F0 f0 v) lb ll)) o
             ).
      eauto using lookup_updated. 

      assert (Some (Heap_OBJ cls3 (fields_update F3 f0 v0) lb ll) =
              lookup_heap_obj (update_heap_obj h2 o0  (Heap_OBJ cls3 (fields_update F3 f0 v0) lb ll)) o0
             ).
      eauto using lookup_updated.
      eauto using object_equal_H.
        +++
          assert (Some (Heap_OBJ cls3 F0 lb ll) =
                   lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls1 (fields_update F1 f0 v) lo1 ll1)) o1
                 ).
          apply lookup_updated_not_affected with o (Heap_OBJ cls1 (fields_update F1 f0 v) lo1 ll1)  h1; auto.
          intro contra. subst; auto. pose proof (beq_oid_same o); try (inconsist).
          case_eq (beq_oid o2 o0); intro.
          apply beq_oid_equal in H34; subst; auto.
          apply right_left in H24. apply right_left in H14.
          rewrite H14 in H24; inversion H24; subst; auto.
          pose proof (beq_oid_same o1); try (inconsist).
          assert (Some (Heap_OBJ cls3 F3 lb ll) =
            lookup_heap_obj (update_heap_obj h2 o0 (Heap_OBJ cls2 (fields_update F2 f0 v0) lo1 ll1)) o2
             ).
          apply lookup_updated_not_affected with o0 (Heap_OBJ cls2 (fields_update F2 f0 v0) lo1 ll1)  h2; auto.
          intro contra. subst; auto. pose proof (beq_oid_same o0); try (inconsist).
          apply object_equal_H with lb cls3 cls3 F0 F3 ll; auto.

      ++
        case_eq (beq_oid o1 o); intro.
        +++
          apply beq_oid_equal in H33; subst; auto. 
          rewrite <- H28 in H15; inversion H15; subst; auto.
          assert (flow_to (join_label lb ll) L_Label = true).
          apply  join_L_label_flow_to_L; auto. 
          try (inconsist).
        +++
          case_eq (beq_oid o2 o0); intro.
           apply beq_oid_equal in H34; subst; auto. 
          rewrite <- H29 in H18; inversion H18; subst; auto.
          assert (flow_to (join_label lb ll) L_Label = true).
          apply  join_L_label_flow_to_L; auto. 
          try (inconsist).
          assert (Some (Heap_OBJ cls0 F0 lb ll) =
                   lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls1 (fields_update F1 f0 v) lo1 ll1)) o1
                 ).
          apply lookup_updated_not_affected with o (Heap_OBJ cls1 (fields_update F1 f0 v) lo1 ll1)  h1; auto.
          intro contra. subst; auto. pose proof (beq_oid_same o); try (inconsist).

          assert (Some (Heap_OBJ cls3 F3 lb ll) =
            lookup_heap_obj (update_heap_obj h2 o0 (Heap_OBJ cls2 (fields_update F2 f0 v0) lo1 ll1)) o2
             ).
          apply lookup_updated_not_affected with o0 (Heap_OBJ cls2 (fields_update F2 f0 v0) lo1 ll1)  h2; auto.
          intro contra. subst; auto. pose proof (beq_oid_same o0); try (inconsist).
          apply object_equal_L with lb cls0 cls3 F0 F3 ll; auto.
          destruct H32. destruct H37. destruct H38.  
          split; auto. split; auto. split; auto.  
          intros.
          destruct H39 with fname fo1 fo2; auto.
          destruct H42 as [cls_f2]. rename x into cls_f1.
          destruct H42 as [lof1]. destruct H42 as [lof2].
          destruct H42 as [FF1]. destruct H42 as [FF2].
          destruct H42 as [llf1]. destruct H42 as [llf2]. 
          destruct H42.  destruct H43.

          case_eq (beq_oid fo1 o); intro.
          apply beq_oid_equal in H45.
          **
            rewrite H45 in H42. rewrite H42 in H15; inversion H15; subst; auto.
            destruct H44.
            ***
              destruct H32. destruct H44. destruct H45. subst; auto.
              rewrite H32 in H14 ;inversion H14; subst; auto.
              rewrite H43 in H18; inversion H18; subst; auto. 
              assert (Some (Heap_OBJ cls_f1 (fields_update FF1 f0 v) lof2 llf2) =
                      lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls_f1 (fields_update FF1 f0 v) lof2 llf2)) o
             ).
              eauto using lookup_updated. 

              assert (Some (Heap_OBJ cls_f2 (fields_update FF2 f0 v0) lof2 llf2) =
              lookup_heap_obj (update_heap_obj h2 o0  (Heap_OBJ cls_f2 (fields_update FF2 f0 v0) lof2 llf2)) o0
             ).
              eauto using lookup_updated.
              exists cls_f1. exists cls_f2.
              exists lof2. exists lof2.
              exists (fields_update FF1 f0 v). exists (fields_update FF2 f0 v0).
              exists llf2. exists llf2.  
              split; auto.
              split; auto.
            ***
              destruct H32.  try (inconsist).

          **
             assert (Some  (Heap_OBJ cls_f1 FF1 lof1 llf1) = 
                   lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls1 (fields_update F1 f0 v) lo1 ll1)) fo1
                 ).
             apply lookup_updated_not_affected with o (Heap_OBJ cls1 (fields_update F1 f0 v) lo1 ll1)  h1; auto.
             intro contra. subst; auto. pose proof (beq_oid_same o); try (inconsist).
             
             case_eq (beq_oid fo2 o0); intro.
             *** 
             apply beq_oid_equal in H47; subst; auto.
             destruct H44.
             ****
               destruct H32. apply right_left in H32. apply right_left in H14.
               rewrite H32 in H14; inversion H14; subst; auto. 
               pose proof (beq_oid_same o); try (inconsist).
             ****
               rewrite H43 in H18; inversion H18; subst; auto.
               destruct H32. 
               try (inconsist).
             ***
               assert (Some  (Heap_OBJ cls_f2 FF2 lof2 llf2) =
                       lookup_heap_obj (update_heap_obj h2 o0 (Heap_OBJ cls2 (fields_update F2 f0 v0) lo1 ll1)) fo2
                      ).
               apply lookup_updated_not_affected with o0 (Heap_OBJ cls2 (fields_update F2 f0 v0) lo1 ll1) h2; auto.
               intro contra. subst; auto. pose proof (beq_oid_same o0); try (inconsist).
               
               exists cls_f1. exists cls_f2.
               exists lof1. exists lof2.
               exists FF1. exists FF2.
               exists llf1. exists llf2.   
               split; auto.

    + intros.
      apply lookup_updated_heap_must_none in H24.
      apply H17 in H24; auto. 

    + intros. 
      apply lookup_updated_heap_must_none in H24.
      apply H19 in H24; auto.

    + intros.
      case_eq (beq_oid o1 o); intro.
      ++ 
        apply  beq_oid_equal in H28.
        subst; auto.
        assert (Some (Heap_OBJ cls1 (fields_update F1 f0 v) lo1 ll1)  =
                lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls1 (fields_update F1 f0 v) lo1 ll1)) o).
        eauto using lookup_updated.
        rewrite H24 in H28; inversion H28; subst; auto.  try (inconsist).

      ++
        assert (Some (Heap_OBJ cls F lb ll) =
              lookup_heap_obj h1 o1
             ).
        eauto using  lookup_updated_heap_old_obj .
        destruct H21 with o1 cls F lb ll; auto.
      
    + intros.
      case_eq (beq_oid o1 o0); intro.
      ++
        apply  beq_oid_equal in H28; subst; auto.
        assert (Some (Heap_OBJ cls2 (fields_update F2 f0 v0) lo1 ll1)  =
                lookup_heap_obj (update_heap_obj h2 o0 (Heap_OBJ cls2 (fields_update F2 f0 v0) lo1 ll1)) o0).
        eauto using lookup_updated.
        rewrite H24 in H28; inversion H28; subst; auto.  try (inconsist).

      ++
        assert (Some (Heap_OBJ cls F lb ll) =
              lookup_heap_obj h2 o1
             ).
        eauto using  lookup_updated_heap_old_obj .
        destruct H23 with o1 cls F lb ll; auto.

  - 
    rewrite <- H14 in H4; inversion H4; subst; auto.
    rewrite <- H15 in H5; inversion H5; subst; auto.    
    inversion H3; subst; auto. 
    apply  L_eq_heap; auto.
    + intros. assert ( L_equivalence_object o1 h1 o2 h2 φ). 
      apply H12. auto.  inversion H22; subst; auto.
      ++
      case_eq (beq_oid o1 o); intro.
      +++
        apply beq_oid_equal in H27.
        rewrite H27 in H23.
        rewrite <- H23 in H14; inversion H14; subst; auto.
        try (inconsist).
      +++
        case_eq (beq_oid o2 o0); intro.
        apply beq_oid_equal in H28.
        rewrite H28 in H24.
        rewrite <- H24 in H15; inversion H15; subst; auto.
        try (inconsist).
        
        assert (Some (Heap_OBJ cls3 F0 lb ll) =
            lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls1 (fields_update F1 f0 v) lo1 ll1)) o1
           ).
        apply lookup_updated_not_affected with o (Heap_OBJ cls1 (fields_update F1 f0 v) lo1 ll1)  h1; auto.
        intro contra. subst; auto. pose proof (beq_oid_same o); try (inconsist).
        
        assert (Some (Heap_OBJ cls3 F3 lb ll) =
            lookup_heap_obj (update_heap_obj h2 o0 (Heap_OBJ cls2 (fields_update F2 f0 v0) lo2 ll2)) o2
             ).
        apply lookup_updated_not_affected with o0 (Heap_OBJ cls2 (fields_update F2 f0 v0) lo2 ll2)  h2; auto.
        intro contra. subst; auto. pose proof (beq_oid_same o0); try (inconsist).
        eauto using  object_equal_H.
      ++
        destruct H27. destruct H28. destruct H29. 
        case_eq (beq_oid o1 o); intro.
        +++
          apply beq_oid_equal in H31; subst; auto. 
          rewrite <- H23 in H14; inversion H14; subst; auto.
          try (inconsist).
        +++
          case_eq (beq_oid o2 o0); intro.
           apply beq_oid_equal in H32; subst; auto. 
          rewrite <- H24 in H15; inversion H15; subst; auto.
          try (inconsist).
          assert (Some (Heap_OBJ cls0 F0 lb ll) =
                   lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls1 (fields_update F1 f0 v) lo1 ll1)) o1
                 ).
          apply lookup_updated_not_affected with o (Heap_OBJ cls1 (fields_update F1 f0 v) lo1 ll1)  h1; auto.
          intro contra. subst; auto. pose proof (beq_oid_same o); try (inconsist).

          assert (Some (Heap_OBJ cls3 F3 lb ll) =
            lookup_heap_obj (update_heap_obj h2 o0 (Heap_OBJ cls2 (fields_update F2 f0 v0) lo2 ll2)) o2
             ).
          apply lookup_updated_not_affected with o0 (Heap_OBJ cls2 (fields_update F2 f0 v0) lo2 ll2)  h2; auto.
          intro contra. subst; auto. pose proof (beq_oid_same o0); try (inconsist).
          apply object_equal_L with lb cls0 cls3 F0 F3 ll; auto.
          split; auto. split; auto. split; auto.  
          intros.
          destruct H30 with fname fo1 fo2; auto.
          destruct H37 as [cls_f2]. rename x into cls_f1.
          destruct H37 as [lof1]. destruct H37 as [lof2].
          destruct H37 as [FF1]. destruct H37 as [FF2].
          destruct H37 as [llf1]. destruct H37 as [llf2]. 

          destruct H37.  destruct H38.
          case_eq (beq_oid fo1 o); intro.
          apply beq_oid_equal in H40.
          **
            rewrite H40 in H37. rewrite H37 in H14; inversion H14; subst; auto.
            assert (Some (Heap_OBJ cls_f1 (fields_update FF1 f0 v) lof1 llf1) =
                      lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls_f1 (fields_update FF1 f0 v) lof1 llf1)) o
             ).
            eauto using lookup_updated. 
            destruct H39.
            ***
              destruct H39. destruct H40. destruct H41. destruct H41. destruct H42. subst; auto.
              try (inconsist).
            ***
              destruct H39. 
              case_eq (beq_oid fo2 o0); intro.
            **** 
              apply beq_oid_equal in H41; subst; auto.
              rewrite H38 in H15; inversion H15; subst; auto.               
              assert (Some (Heap_OBJ cls_f2 (fields_update FF2 f0 v0) lof2 llf2) =
              lookup_heap_obj (update_heap_obj h2 o0  (Heap_OBJ cls_f2 (fields_update FF2 f0 v0) lof2 llf2)) o0
             ).
              eauto using lookup_updated.
              exists cls_f1. exists cls_f2.
              exists lof1. exists lof2.
              exists (fields_update FF1 f0 v). exists (fields_update FF2 f0 v0).
              exists llf1. exists llf2.  
              split; auto.
            ****
              assert (Some  (Heap_OBJ cls_f2 FF2 lof2 llf2) =
                       lookup_heap_obj (update_heap_obj h2 o0 (Heap_OBJ cls2 (fields_update F2 f0 v0) lo2 ll2)) fo2
                      ).
               apply lookup_updated_not_affected with o0 (Heap_OBJ cls2 (fields_update F2 f0 v0) lo2 ll2) h2; auto.
               intro contra. subst; auto. pose proof (beq_oid_same o0); try (inconsist).
               exists cls_f1. exists cls_f2.
               exists lof1. exists lof2.
               exists (fields_update FF1 f0 v). exists FF2.
               exists llf1. exists llf2.  
               split; auto.  
          **
             assert (Some  (Heap_OBJ cls_f1 FF1 lof1 llf1) = 
                   lookup_heap_obj (update_heap_obj h1 o (Heap_OBJ cls1 (fields_update F1 f0 v) lo1 ll1)) fo1
                 ).
             apply lookup_updated_not_affected with o (Heap_OBJ cls1 (fields_update F1 f0 v) lo1 ll1)  h1; auto.
             intro contra. subst; auto. pose proof (beq_oid_same o); try (inconsist).
             
             case_eq (beq_oid fo2 o0); intro.
             ***
               apply beq_oid_equal in H42; subst; auto.
               assert (Some (Heap_OBJ cls2 (fields_update F2 f0 v0) lo2 ll2) =
                       lookup_heap_obj (update_heap_obj h2 o0 (Heap_OBJ cls2 (fields_update F2 f0 v0) lo2 ll2)) o0
                      ).
               eauto using lookup_updated.               
               destruct H39.
             ****
               destruct H39.  destruct H42. destruct H43. destruct H43. destruct H44. subst; auto.
               rewrite H38 in H15; inversion H15; subst; auto. 
               try (inconsist).
             ****
               exists cls_f1. exists cls2.
               exists lof1. exists lo2.
               exists FF1. exists (fields_update F2 f0 v0).
               exists llf1. exists ll2.   
               split; auto. split; auto.
               rewrite H38 in H15; inversion H15; subst; auto. 
             ***
               assert (Some  (Heap_OBJ cls_f2 FF2 lof2 llf2) =
                       lookup_heap_obj (update_heap_obj h2 o0 (Heap_OBJ cls2 (fields_update F2 f0 v0) lo2 ll2)) fo2
                      ).
               apply lookup_updated_not_affected with o0 (Heap_OBJ cls2 (fields_update F2 f0 v0) lo2 ll2) h2; auto.
               intro contra. subst; auto. pose proof (beq_oid_same o0); try (inconsist).
               
               exists cls_f1. exists cls_f2.
               exists lof1. exists lof2.
               exists FF1. exists FF2.
               exists llf1. exists llf2.   
               split; auto.

    + intros.
      apply lookup_updated_heap_must_none in H21.
      apply H13 in H21; auto.
      
    + intros. 
      apply lookup_updated_heap_must_none in H21.
      apply H17 in H21. auto.

    + intros.
      case_eq (beq_oid o1 o); intro.
      apply  beq_oid_equal in H23.
      rewrite <- H23 in H14.
      destruct H19 with o1 cls1 F1 lo1 ll1; auto.

      assert (Some (Heap_OBJ cls F lb ll) =
              lookup_heap_obj h1 o1
             ).
      eauto using  lookup_updated_heap_old_obj .
      destruct H19 with o1 cls F lb ll; auto.
      
    + intros.
      case_eq (beq_oid o1 o0); intro.
      apply  beq_oid_equal in H23.
      rewrite <- H23 in H15.
      destruct H20 with o1 cls2 F2 lo2 ll2; auto.

      assert (Some (Heap_OBJ cls F lb ll) =
              lookup_heap_obj h2 o1
             ).
      eauto using  lookup_updated_heap_old_obj .
      destruct H20 with o1 cls F lb ll; auto. 
Qed. Hint Resolve update_field_preserve_bijection_new. 




