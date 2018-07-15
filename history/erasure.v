
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.

Require Import Label.
Require Import Language.
Require Import Lemmas.


Fixpoint erasure_L_fun (t : tm) :=
  match t with
    | Tvar x => Tvar x
    | null => null
    | FieldAccess e f => FieldAccess (erasure_L_fun e) f
    | MethodCall e1 meth e2 => MethodCall (erasure_L_fun e1) meth (erasure_L_fun e2)
    | NewExp cls => NewExp cls
(* label related *)
    | l lb => l lb
    | labelData e lb => labelData (erasure_L_fun e) lb
    | unlabel e => unlabel (erasure_L_fun e)
    | labelOf e => labelOf (erasure_L_fun e)
    | unlabelOpaque e => unlabelOpaque (erasure_L_fun e)
(* statements *)
    | Skip => Skip
    | Assignment x e => Assignment x (erasure_L_fun e)
    | FieldWrite e1 f e2 => FieldWrite (erasure_L_fun e1) f (erasure_L_fun e2)
    | If id0 id1 e1 e2 => If id0 id1 (erasure_L_fun e1) (erasure_L_fun e2)
    | Sequence e1 e2 => Sequence (erasure_L_fun e1) (erasure_L_fun e2)

(* special terms *)
    | ObjId o =>  ObjId o
  (* runtime labeled date*)
    | v_l e lb => if (flow_to lb L_Label) then v_l (erasure_L_fun e) lb else v_l dot lb 
    | v_opa_l e lb => if (flow_to lb L_Label) then v_opa_l (erasure_L_fun e) lb else v_opa_l dot lb 
    | dot => dot
    | return_hole =>  (v_opa_l dot H_Label)
    | hole => hole
  end.

(* Notes: add a reduction rule for dot.f fieldAccess, 
    so that it reduces to dot and changes the current label to high*)

Fixpoint erasure_obj_null (t: option tm) (h:heap) : (option tm) :=
  match t with 
    | Some null => Some null
    | Some (ObjId o) => match (lookup_heap_obj h o) with 
                              | Some (Heap_OBJ cls fields lb) => if (flow_to lb L_Label) then Some (ObjId o) else Some dot
                              | None => Some dot (*already deleted object*)
                          end
    | Some dot => Some dot
    | None => None
    | _ => None
  end. 


Fixpoint erasure_heap (h:heap) : heap := 
    match h with 
      | nil => nil
      | h1 :: t => match h1 with 
                            | ( o0 , ho ) => match ho with 
                                                       | Heap_OBJ cls F lb => if (flow_to lb L_Label) then 
                                                                              ( o0 , (Heap_OBJ cls (fun x => (erasure_obj_null (F x) h)) lb)) :: (erasure_heap t) 
                                                                              else (erasure_heap t) 
                                                      end
                      end
    end.

Fixpoint erasure_L_fs (fs : list tm) := 
  match fs with 
    | nil => nil
    | h1 :: t => erasure_L_fun h1 :: erasure_L_fs t
  end. 

Fixpoint erasure_fun (ct : Class_table) (ctn : container) (ctns_stack : list container) (h : heap) : config :=
match ctn with 
 | (Container t fs lb sf) =>
       if (flow_to lb L_Label) then (Config ct (Container (erasure_L_fun t) (erasure_L_fs fs) lb (fun x => (erasure_obj_null (sf x) h))) ctns_stack (erasure_heap h))
          else match ctns_stack with 
                | nil => (Config ct (Container dot nil lb empty_stack_frame) nil (erasure_heap h)) 
                | ctn :: ctns' => erasure_fun ct ctn ctns' (erasure_heap h)
                end
end. 


Lemma lookup_erasure_heap : forall h o cls F lb, 
   lookup_heap_obj h o = Some (Heap_OBJ cls F lb) -> 
   flow_to lb L_Label = true -> 
   exists F', lookup_heap_obj (erasure_heap h) o = Some (Heap_OBJ cls F' lb) .
Proof.      intros. induction h. unfold lookup_heap_obj in H. inversion H. 
      induction a. 
      case_eq ( beq_oid o o0). unfold lookup_heap_obj.  intro. 
      unfold erasure_heap. rename h0 into ho. induction ho. unfold  lookup_heap_obj in H. rewrite H1 in H. 
      inversion H. subst. rewrite H0. rewrite H1. exists (fun x : id => erasure_obj_null (F x) ((o0, Heap_OBJ cls F lb) :: h)). auto.
      intro. unfold  lookup_heap_obj in H. rewrite H1 in H. fold  lookup_heap_obj in H. 
      unfold erasure_heap. induction h0. fold erasure_heap.  unfold lookup_heap_obj. 
      case_eq (flow_to l L_Label). intro. rewrite H1. fold lookup_heap_obj.  apply IHh. auto. 
      intro. fold lookup_heap_obj. apply IHh. auto. 
Qed. 

Lemma multi_erasure_heap_equal : forall h, 
   erasure_heap (erasure_heap h) = (erasure_heap h).
  Proof. intro h.  induction h.  unfold erasure_heap. auto. induction a. rename h0 into ho.  unfold erasure_heap.
  induction ho. case_eq (flow_to l L_Label). 
  + intro. rewrite H. fold erasure_heap. fold erasure_heap. 
  assert ((o,
Heap_OBJ c (fun x : id =>   erasure_obj_null (erasure_obj_null (f x) ((o, Heap_OBJ c f l) :: h))
     ((o, Heap_OBJ c  (fun x0 : id => erasure_obj_null (f x0) ((o, Heap_OBJ c f l) :: h)) l) :: erasure_heap h)) l) = 
        (o, Heap_OBJ c (fun x : id => erasure_obj_null (f x) ((o, Heap_OBJ c f l) :: h))   l) ).

  Require Import Coq.Logic.FunctionalExtensionality.
  assert (forall a, (fun x : id =>   erasure_obj_null (erasure_obj_null (f x) ((o, Heap_OBJ c f l) :: h))
     ((o, Heap_OBJ c  (fun x0 : id => erasure_obj_null (f x0) ((o, Heap_OBJ c f l) :: h)) l) :: erasure_heap h)) a =  (fun x : id => erasure_obj_null (f x) ((o, Heap_OBJ c f l) :: h)) a).
   intro x. 
   case (f x). induction t; try (unfold erasure_obj_null; auto).
   rename o0 into o'. remember ((o, Heap_OBJ c f l) :: h) as h'. fold erasure_obj_null. 
   ++ remember (erasure_obj_null (Some (ObjId o')) h') as erased_field.
    unfold erasure_obj_null in Heqerased_field. 
    assert (forall h o, (exists cls F lb, lookup_heap_obj h o = Some (Heap_OBJ cls F lb) ) 
      \/ lookup_heap_obj h o = None).
    intro h0. induction h0.  right. unfold lookup_heap_obj. auto. 
    intro o0. induction a. case_eq ( beq_oid o0 o1). unfold lookup_heap_obj.  intro. unfold lookup_heap_obj. rewrite H0.
    rename h1 into ho. induction ho.     left. exists c0. exists f0. exists l0. auto. 
    intro. unfold lookup_heap_obj. rewrite H0. fold lookup_heap_obj. apply IHh0. 
    destruct H0 with h' o'. destruct H1 as [cls]. destruct H1 as [F]. destruct H1 as [lb]. 
    +++  rewrite H1 in Heqerased_field. rewrite H1.
      case_eq ( flow_to lb L_Label ).  
    ++++ intro. rewrite H2 in  Heqerased_field. 
      unfold erasure_obj_null. fold erasure_obj_null.  auto.
      assert (exists F', lookup_heap_obj (erasure_heap h') o' = Some (Heap_OBJ cls F' lb)).
      apply lookup_erasure_heap with F. auto. auto.  
      assert (   ((o, Heap_OBJ c (fun x1 : id => erasure_obj_null (f x1) h') l) :: (erasure_heap h)) = (erasure_heap h')).
      remember ( erasure_heap h' ) as erasuedh. 
      unfold erasure_heap in Heqerasuedh. rewrite Heqh' in Heqerasuedh. rewrite H in Heqerasuedh. fold erasure_heap in Heqerasuedh.
      rewrite Heqerasuedh. 
      assert ((fun x1 : id => erasure_obj_null (f x1) h') = (fun x1 : id => erasure_obj_null (f x1) ((o, Heap_OBJ c f l) :: h))). rewrite Heqh'. auto. 
      rewrite H4. auto. rewrite H4. destruct H3 as [F']. rewrite H3. rewrite H2. auto. 
    ++++ intro.  unfold erasure_obj_null. auto.
    +++ rewrite H1. unfold erasure_obj_null. auto.
    ++ unfold erasure_obj_null. auto.
    ++  fold erasure_obj_null. auto.
   apply functional_extensionality in H0. rewrite H0.  auto. 
   ++   rewrite IHh. rewrite H0. auto. 
  + intro. fold erasure_heap. auto.
Qed.  


Lemma extend_heap_preserve_erasure : forall h o h' cls F lb, 
  o = (get_fresh_oid h) ->
  h' =  add_heap_obj h o (Heap_OBJ cls F lb) ->
  flow_to lb L_Label = false ->
  erasure_heap h' = erasure_heap h.
Proof.
  intros h o h' cls F lb. 
  intro H_o. intro H_h'. intro H_flow. 
  induction h. 
  unfold erasure_heap. rewrite H_h'. unfold  add_heap_obj. rewrite H_flow. auto. 
  unfold add_heap_obj in H_h'. remember (a::h) as h0. unfold erasure_heap.
  rewrite H_h'. rewrite H_flow. fold  erasure_heap. auto. 
Qed. 


Lemma lookup_none_in_erasured_heap : forall o h, 
    lookup_heap_obj h o = None ->
    lookup_heap_obj (erasure_heap h) o = None.
Proof. induction h. unfold erasure_heap. auto.
    intro. induction a. unfold erasure_heap. induction h0.
    case_eq (flow_to l L_Label). intro. fold lookup_heap_obj.
    fold erasure_heap. unfold lookup_heap_obj. 
    unfold lookup_heap_obj in H. case_eq (beq_oid o o0). intro. 
    rewrite H1 in H. inversion H. intro.  rewrite H1 in H. fold lookup_heap_obj in H.
    fold lookup_heap_obj. apply IHh. auto.
    intro. fold erasure_heap. unfold lookup_heap_obj in H.
    case_eq (beq_oid o o0). intro.  rewrite H1 in H. inversion H.
    intro. rewrite H1 in H. fold lookup_heap_obj in H. apply IHh. auto.
Qed. 

Lemma lookup_erasure_heap_erasured : forall h o cls F lb CT, 
       wfe_heap CT h ->
   lookup_heap_obj h o = Some (Heap_OBJ cls F lb) -> 
   flow_to lb L_Label = false -> 
   lookup_heap_obj (erasure_heap h) o = None.
Proof. induction h. intros. unfold lookup_heap_obj in H0. inversion H0. 
      induction a. intros. 
      case_eq ( beq_oid o0 o). intro. unfold lookup_heap_obj. 
      unfold erasure_heap. rename h0 into ho. induction ho.
      case_eq (flow_to l L_Label). unfold lookup_heap_obj in H0.
      rewrite H2 in H0. inversion H0. subst. intro. rewrite H1 in H3. inversion H3.

      intro. assert ( lookup_heap_obj h o0 = None). 
      apply heap_lookup with ((o, Heap_OBJ c f l) :: h) CT (Heap_OBJ c f l); auto. 
      apply beq_oid_equal in H2.
      rewrite H2. auto.
      fold lookup_heap_obj. fold erasure_heap.  apply lookup_none_in_erasured_heap.
      auto.
     intro.  unfold lookup_heap_obj in H0. 
     rewrite H2 in H0. fold lookup_heap_obj in H0.
     unfold lookup_heap_obj. unfold erasure_heap. fold lookup_heap_obj. induction h0. 
     case_eq (flow_to l L_Label). unfold lookup_heap_obj. rewrite H2.  fold lookup_heap_obj.
     fold erasure_heap. intro.  apply IHh with cls F lb CT; auto.  
    inversion H. inversion H4. subst. auto.
     intro.      fold erasure_heap. apply IHh with cls F lb CT. 
    inversion H. inversion H4. subst. auto. auto. auto.  
Qed. 

  Lemma erasure_obj_null_equal_erasure_h_helper : forall h t CT,
      wfe_heap CT h ->
      erasure_obj_null t h = erasure_obj_null t (erasure_heap h).
      Proof. intros. induction t. induction a; try (unfold erasure_obj_null; auto). 
          assert (forall h o, (exists cls F lb, lookup_heap_obj h o = Some (Heap_OBJ cls F lb) ) 
          \/ lookup_heap_obj h o = None).
        intro h0. induction h0.  right. unfold lookup_heap_obj. auto. 
        intro o0. induction a. case_eq ( beq_oid o0 o1). unfold lookup_heap_obj.  intro. unfold lookup_heap_obj. rewrite H0. 
         rename h1 into ho. induction ho.     left. exists c. exists f. exists l. auto. 
        intro. unfold lookup_heap_obj. rewrite H0. fold lookup_heap_obj. apply IHh0. 
        destruct H0 with h o. destruct H1 as [cls]. destruct H1 as [F]. destruct H1 as [lb]. rewrite H1.
        case_eq (flow_to lb L_Label ). intro. 
        assert (exists F', lookup_heap_obj (erasure_heap h) o = Some (Heap_OBJ cls F' lb)).
        apply lookup_erasure_heap with F. auto. auto. destruct H3 as [F']. rewrite H3. rewrite H2. auto. 
       intro.   assert ( lookup_heap_obj (erasure_heap h) o = None).  apply lookup_erasure_heap_erasured with cls F lb CT; auto. 
        rewrite H3. auto. rewrite H1. auto. assert (lookup_heap_obj (erasure_heap h) o  = None). 
       apply lookup_none_in_erasured_heap. auto. rewrite H2. auto.
      (unfold erasure_obj_null; auto).
    Qed.

 Lemma update_H_object_equal_erasure : forall h o CT cls F F' lb lb',
       wfe_heap CT h -> 
        Some (Heap_OBJ cls F lb) = lookup_heap_obj h o ->
        flow_to lb' L_Label = false ->
        flow_to lb L_Label = false ->
          erasure_heap h = erasure_heap
                                            (update_heap_obj h o
                                               (Heap_OBJ cls F' lb')).
    Proof. intros h o CT cls F F' lb lb'. intros.  induction h. unfold lookup_heap_obj in H0. inversion H0.
     induction a. case_eq (beq_oid o o0). intro. unfold update_heap_obj. rewrite H3. 

    unfold lookup_heap_obj in H0.  rewrite H3 in H0.  inversion H0. 
    unfold erasure_heap. fold erasure_heap. rewrite H2. rewrite H1.  auto. 
    intro. unfold update_heap_obj. rewrite H3.  fold update_heap_obj. 
    assert (erasure_heap h =
      erasure_heap (update_heap_obj h o (Heap_OBJ cls F' lb'))).
    apply IHh. auto.  inversion H. auto. inversion H4. subst. auto.
    unfold  lookup_heap_obj in H0. rewrite H3 in H0. fold lookup_heap_obj in H0. auto.
    unfold erasure_heap. fold erasure_heap.
    rewrite H4. auto. 

    induction h0. 
    assert ( forall a, 
     (fun x : id => erasure_obj_null (f x) ((o0, Heap_OBJ c f l) :: h)) a
          = (fun x : id => erasure_obj_null (f x)
                     ((o0, Heap_OBJ c f l) :: update_heap_obj h o (Heap_OBJ cls F' lb'))) a).
    Proof. intro  a. 
assert (forall h o, (exists cls F lb, lookup_heap_obj h o = Some (Heap_OBJ cls F lb) ) 
      \/ lookup_heap_obj h o = None).
    intro h1. induction h1.  right. unfold lookup_heap_obj. auto.
    intro o1.  induction a0. case_eq ( beq_oid o1 o2). unfold lookup_heap_obj.  intro. unfold lookup_heap_obj. rewrite H5.
    rename h0 into ho. induction ho.     left. exists c0. exists f0. exists l0. auto. 
    intro. unfold lookup_heap_obj. rewrite H5. fold lookup_heap_obj. apply IHh1. 
    remember ((o, Heap_OBJ c f l) :: h) as h'. 
    case (f a). induction t; try (unfold erasure_obj_null; auto).
    

    destruct H5 with  ((o0, Heap_OBJ c f l) :: h)  o1. 
    destruct H6 as [cls1]. destruct H6 as [F1]. destruct H6 as [lb1]. rewrite H6.

      remember ((o0, Heap_OBJ c f l) :: h) as h0.
      assert(  (lookup_heap_obj
               (update_heap_obj h0 o (Heap_OBJ cls F' lb')) o1  = 
                      Some (Heap_OBJ cls1 F1 lb1)) \/ 
              (lookup_heap_obj (update_heap_obj h0 o (Heap_OBJ cls F' lb')) o1  = 
                      Some (Heap_OBJ cls F' lb')) /\ beq_oid o1 o = true ).
      apply lookup_updated_heap_equal with F lb; auto. 
      destruct H7. unfold update_heap_obj in H7. rewrite Heqh0 in H7.  rewrite H3 in H7. 
      fold update_heap_obj in H7. rewrite H7. auto.

      unfold update_heap_obj in H7. rewrite Heqh0 in H7.  rewrite H3 in H7. 
      fold update_heap_obj in H7. destruct H7. rewrite H7. apply beq_oid_equal in H8.
      rewrite H8 in H6. rewrite H6 in H0. inversion H0. subst. rewrite H2.  rewrite H1.  auto.

      rewrite H6. 
      auto.

      assert (lookup_heap_obj (update_heap_obj ((o0, Heap_OBJ c f l) :: h) o (Heap_OBJ cls F' lb')) o1 = None).
      apply lookup_updated_heap_none; auto. 
      intro contra. rewrite contra in H0. rewrite <- H0 in H6. inversion H6. 
      unfold update_heap_obj in H7. rewrite H3 in H7. fold update_heap_obj in H7. rewrite H7. auto. 
        
      auto. 
      apply functional_extensionality in H5. rewrite H5. auto.  
Qed.


Lemma simulation_H : forall ct t1 fs1 lb1 sf1 ctns_stack1 h1  t2 fs2 lb2 sf2 ctns_stack2 h2, 
      valid_syntax t1 ->
      forall T, tm_has_type ct empty_context h1 t1 T -> 
      field_wfe_heap ct h1 -> wfe_heap ct h1 ->         
      wfe_stack_frame ct h1 sf1 ->
      flow_to lb1 L_Label = false ->
     Config ct (Container t1 fs1 lb1 sf1) ctns_stack1 h1 
      ==> Config ct (Container t2 fs2 lb2 sf2) ctns_stack2 h2 ->
      erasure_fun ct (Container t1 fs1 lb1 sf1) ctns_stack1 h1  = 
      erasure_fun ct (Container t2 fs2 lb2 sf2) ctns_stack2 h2.
Proof with eauto. intros ct t1 fs1 lb1 sf1 ctns_stack1 h1  t2 fs2 lb2 sf2 ctns_stack2 h2.
     intro H_valid_syntx. intro T. intro H_typing.  intro H_wfe_field. intro H_wfe_heap. 
     intro H_wfe_sf.  intro H_flow. intro H_reduction. 
     remember (Config ct (Container t1 fs1 lb1 sf1) ctns_stack1 h1) as config1. 
     remember (Config ct (Container t2 fs2 lb2 sf2) ctns_stack2 h2) as config2.
     generalize dependent t1. generalize dependent fs1. generalize dependent lb1. 
     generalize dependent ctns_stack1. generalize dependent h1. 

     generalize dependent t2. generalize dependent fs2. generalize dependent lb2. 
     generalize dependent ctns_stack2. generalize dependent h2. 
     generalize dependent T. generalize dependent sf1. generalize dependent sf2. 

induction H_reduction; intros; auto; inversion Heqconfig1; inversion Heqconfig2; subst; auto; try (rename lb2 into lb1);
case_eq (flow_to lb1 L_Label); try (intro H_lb1_true; rewrite H_flow in H_lb1_true; inversion H_lb1_true);
try (induction ctns_stack2; unfold erasure_fun; rewrite H_flow; auto); fold erasure_fun.

- assert (flow_to (join_label lo lb1) L_Label = false).  apply flow_join_label with lb1 lo; auto. rewrite H1. 
apply H_Label_not_flow_to_L in H1. rewrite H1. apply H_Label_not_flow_to_L in H_flow. rewrite H_flow. auto. 
- assert (flow_to (join_label lo lb1) L_Label = false).  apply flow_join_label with lb1 lo; auto. rewrite H1. auto.  
-  pose proof  (multi_erasure_heap_equal h2) as Hy. 
unfold erasure_fun. fold erasure_fun. rewrite H_flow. 
induction ctns_stack1. unfold erasure_fun. fold erasure_fun. rewrite H_flow. rewrite Hy. auto.  
induction a. unfold erasure_fun. fold erasure_fun. rewrite H_flow. rewrite Hy. auto.  

-  pose proof  (multi_erasure_heap_equal h2) as Hy.
assert (flow_to (join_label lb1 lx) L_Label = false).  apply flow_join_label with lb1 lx;auto.
apply join_label_commutative. 
induction ctns_stack1;  unfold erasure_fun; fold erasure_fun; rewrite H_flow; rewrite H0; rewrite Hy; auto.

- assert (erasure_heap
     (add_heap_obj h1 (get_fresh_oid h1)
        (Heap_OBJ (class_def cls_name field_defs method_defs)
           (init_field_map
              (find_fields (class_def cls_name field_defs method_defs))
              empty_field_map) lb1)) = erasure_heap h1  ).
   apply extend_heap_preserve_erasure with  (get_fresh_oid h1)  (class_def cls_name field_defs method_defs)
         (init_field_map
              (find_fields (class_def cls_name field_defs method_defs))
              empty_field_map)     lb1; auto. rewrite H0. auto.
- assert (erasure_heap
     (add_heap_obj h1 (get_fresh_oid h1)
        (Heap_OBJ (class_def cls_name field_defs method_defs)
           (init_field_map
              (find_fields (class_def cls_name field_defs method_defs))
              empty_field_map) lb1)) = erasure_heap h1  ).
   apply extend_heap_preserve_erasure with  (get_fresh_oid h1)  (class_def cls_name field_defs method_defs)
         (init_field_map
              (find_fields (class_def cls_name field_defs method_defs))
              empty_field_map)     lb1; auto. rewrite H0. auto.

- assert (flow_to (join_label lb1 lo) L_Label = false).  apply flow_join_label with lb1 lo; auto. 
apply join_label_commutative. 
rewrite H. apply H_Label_not_flow_to_L in H. rewrite H. apply H_Label_not_flow_to_L in H_flow. rewrite H_flow. auto.

- assert (flow_to (join_label lb1 lo) L_Label = false).  apply flow_join_label with lb1 lo; auto. 
apply join_label_commutative. rewrite H. apply H_Label_not_flow_to_L in H. auto.  

-  assert (flow_to (join_label lb1 lo) L_Label = false).  apply flow_join_label with lb1 lo; auto. 
apply join_label_commutative. 
rewrite H. apply H_Label_not_flow_to_L in H. rewrite H. apply H_Label_not_flow_to_L in H_flow. rewrite H_flow. auto.
- assert (flow_to (join_label lb1 lo) L_Label = false).  apply flow_join_label with lb1 lo; auto. 
apply join_label_commutative. rewrite H. apply H_Label_not_flow_to_L in H. auto.  
- assert ((erasure_heap h1) =  (erasure_heap
     (update_heap_obj h1 o (Heap_OBJ cls (fields_update F f v) lo)))).
  assert (flow_to lo L_Label = false). apply flow_transitive with (join_label lb1 lx); auto. 
   apply flow_join_label with lb1 lx; auto. apply join_label_commutative.
  apply update_H_object_equal_erasure with ct F lo; auto. rewrite H0. auto.  

- assert ((erasure_heap h1) =  (erasure_heap
     (update_heap_obj h1 o (Heap_OBJ cls (fields_update F f v) lo)))).
  assert (flow_to lo L_Label = false). apply flow_transitive with (join_label lb1 lx); auto. 
   apply flow_join_label with lb1 lx; auto. apply join_label_commutative.
  apply update_H_object_equal_erasure with ct F lo; auto. rewrite H0. auto.  

- 
pose proof  (multi_erasure_heap_equal h2) as Hy; rewrite Hy; auto.
try (case_eq (flow_to lb2 L_Label)); try (auto); try (intro H_lb2_true; 
unfold erasure_L_fun; fold erasure_L_fun; rewrite H_flow).
assert ( forall a, (fun x : id => erasure_obj_null (sf2 x) h2) a = (fun x : id => (erasure_obj_null (sf2 x) (erasure_heap h2))) a).
  intro a. apply erasure_obj_null_equal_erasure_h_helper with ct; auto. apply functional_extensionality in H0.
  rewrite H0. pose proof (H_Label_not_flow_to_L lb1 H_flow) as H_lb1; rewrite H_lb1; auto.


-pose proof  (multi_erasure_heap_equal h2) as Hy; rewrite Hy; auto.
try (case_eq (flow_to lb2 L_Label)); try (auto); try (intro H_lb2_true; 
unfold erasure_L_fun; fold erasure_L_fun; rewrite H_flow).
assert ( forall a, (fun x : id => erasure_obj_null (sf2 x) h2) a = (fun x : id => (erasure_obj_null (sf2 x) (erasure_heap h2))) a).
  intro a0. apply erasure_obj_null_equal_erasure_h_helper with ct; auto. apply functional_extensionality in H0.
  rewrite H0. pose proof (H_Label_not_flow_to_L lb1 H_flow) as H_lb1; rewrite H_lb1; auto.
 
Qed.



Reserved Notation "c '==l>' c'"
  (at level 40, c' at level 39).

Definition erasure (c : config ) : config :=
  match c with 
    | (Config ct ctn ctns_stack h) => erasure_fun ct ctn ctns_stack h
    | Error_state => Error_state
    | Terminal => Terminal
  end. 

Inductive l_reduction : config -> config -> Prop :=
    | L_reduction : forall c1 c2 c2_r, 
      c1 ==> c2 ->
      erasure  c2 = c2_r ->
      l_reduction c1 c2_r
where "c '==l>' c'" := (l_reduction c c').

Inductive multi_step_l_reduction : config -> config -> Prop := 
  | multi_reduction_l_refl : forall config , multi_step_l_reduction config config
  | multi_reduction_l_step : forall c1 c2 c3, 
                    l_reduction c1 c2 ->
                    multi_step_l_reduction c2 c3 ->
                    multi_step_l_reduction c1 c3.

Notation "c1 '==>L*' c2" := (multi_step_l_reduction c1 c2) (at level 40).



Theorem L_reduction_determinacy: forall c c1 c2, 
     l_reduction c c1 ->
     l_reduction c c2 -> 
      c1 = c2.
Proof. Admitted.

Lemma ct_erasure : forall ct ctn ctns h ct' ctn' ctns' h', 
  erasure (Config ct ctn ctns h)  = (Config ct' ctn' ctns' h') -> ct = ct'. 
Proof. intros ct ctn ctns h ct' ctn' ctns' h'. 
    intro. unfold erasure in H. unfold erasure_fun in H; auto.
    generalize dependent ctn.  generalize dependent h. 
    induction ctns. intros. destruct ctn. 
    case_eq (flow_to l L_Label). intros. rewrite H0 in H. inversion H.  auto. 
    intro. rewrite H0 in H. inversion H. auto. 
  intros.  
destruct ctn. 
    case_eq (flow_to l L_Label). intro. rewrite H0 in H. inversion H. auto. 
    intro. rewrite H0 in H.  fold erasure_fun in IHctns.  fold erasure_fun in H. apply IHctns with (erasure_heap h) a. auto.
Qed.


Lemma l_reduction_ct_consist : forall ct ctn ctns h ct' ctn' ctns' h', 
  (Config ct ctn ctns h) ==l> (Config ct' ctn' ctns' h') -> ct = ct'. 
 Proof.
   intros. inversion H. subst. induction c2. assert (ct = c).
   apply ct_consist with ctn ctns h c0 l h0; auto.  subst. apply ct_erasure with c0 l h0 ctn' ctns' h'; auto. 
    inversion H1. inversion H1. 
  Qed.  
(*
Theorem L_reduction_multistep_determinacy: forall ct ctn ctns h v1 lb1 sf1 h1 v2 lb2 sf2 h2, 
      (Config ct ctn ctns h) ==>L* (Config ct (Container v1 nil lb1 sf1) nil h1) ->
      (Config ct ctn ctns h) ==>L* (Config ct (Container v2 nil lb2 sf2) nil h2)  -> 
     value v1 -> value v2 ->
      (Config ct (Container v1 nil lb1 sf1) nil h1) = (Config ct (Container v2 nil lb2 sf2) nil h2). 
Proof.
  intros ct ctn ctns h v1 lb1 sf1 h1 v2 lb2 sf2 h2.
  intro Hy1.   intro Hy2. 
  intro Hv1. intro Hv2.  
  remember (Config ct (Container v1 nil lb1 sf1) nil h1) as v1_config. 
  remember (Config ct ctn ctns h) as config. 
  generalize dependent v1.      generalize dependent v2.
  generalize dependent lb1.      generalize dependent lb2.
  generalize dependent sf1.      generalize dependent sf2.
  generalize dependent h1.      generalize dependent h2.
  generalize dependent h.  generalize dependent ctn.      generalize dependent ctns.
  induction Hy1.
  - intros. subst. inversion Heqv1_config. subst. 
    inversion Hy2. auto. inversion H. subst. 
inversion Hv1; subst; inversion H3; subst; inversion H0; try ( inversion H1; inversion H6; fail);
try (inversion H2; inversion H7).
- intros. subst.  inversion Hy2. subst. inversion H.  subst. inversion Hv2; subst; inversion H0; subst;
try (inversion Hy1; inversion H1; inversion H5; fail); try (inversion Hy1; inversion H2; inversion H6; fail).
  subst.  induction c2.  induction c0. 
  assert (ct = c). apply l_reduction_ct_consist with ctn ctns h c1 l h0. auto. 
  assert (ct = c0). apply l_reduction_ct_consist with ctn ctns h c2 l h3. auto.
  subst. assert (Config c0 c1 l h0 = Config c0 c2 l h3). 
  apply L_reduction_determinacy with (Config c0 ctn ctns h); auto. 
  rewrite <- H2 in H. apply IHHy1 with l c1 h0 h1 sf1 lb1 v1; auto.
   inversion H1. inversion H2. inversion H6.  
 inversion H1. inversion H2. inversion H6.  
 inversion Hy1. inversion H2. inversion H6. 
 inversion Hy1. inversion H2. inversion H6.
Qed.  
 *)

 
Lemma multi_erasure_L_tm_equal : forall t, 
   erasure_L_fun (erasure_L_fun t) = (erasure_L_fun t).
  Proof. induction t; try (unfold erasure_L_fun; auto; fold erasure_L_fun;  rewrite IHt; auto; fail);
 try (unfold erasure_L_fun; auto; fold erasure_L_fun; rewrite IHt1; rewrite IHt2; auto).
 - fold erasure_L_fun. unfold erasure_L_fun. fold erasure_L_fun. 
    case_eq (flow_to l L_Label ). intro. unfold erasure_L_fun. fold erasure_L_fun. rewrite H. rewrite IHt.  auto. 
    intro. unfold erasure_L_fun. auto. rewrite H. auto.

 - fold  erasure_L_fun. 
    case_eq (flow_to l L_Label ). intro. unfold erasure_L_fun. fold erasure_L_fun. rewrite H.
    unfold erasure_L_fun. fold erasure_L_fun.  rewrite IHt. rewrite H.  auto. 
    intro. unfold erasure_L_fun. auto. rewrite H. rewrite H. auto. 
Qed.  

Lemma multi_erasure_L_fs_equal : forall fs, 
   erasure_L_fs (erasure_L_fs fs) = (erasure_L_fs fs).
  Proof. induction fs.
  - auto. 
  - unfold erasure_L_fs. fold erasure_L_fs.  pose proof (multi_erasure_L_tm_equal a ).
  rewrite H. rewrite IHfs. auto. Qed. 


Lemma erasure_obj_null_equal : forall h t, 
  erasure_obj_null (erasure_obj_null t h) h = (erasure_obj_null t h).
Proof. intros. induction t. induction a; try (unfold erasure_obj_null; auto). 
      assert (forall h o, (exists cls F lb, lookup_heap_obj h o = Some (Heap_OBJ cls F lb) ) 
      \/ lookup_heap_obj h o = None).
    intro h0. induction h0.  right. unfold lookup_heap_obj. auto. 
    intro o0. induction a. case_eq ( beq_oid o0 o1). unfold lookup_heap_obj.  intro. unfold lookup_heap_obj. rewrite H. 
     rename h1 into ho. induction ho.     left. exists c. exists f. exists l. auto. 
    intro. unfold lookup_heap_obj. rewrite H. fold lookup_heap_obj. apply IHh0. 
    destruct H with h o. destruct H0 as [cls]. destruct H0 as [F]. destruct H0 as [lb]. rewrite H0.
    case_eq (flow_to lb L_Label ). intro. rewrite H0. rewrite H1. auto. 
   intro. auto. 
  rewrite H0. auto. 
  (unfold erasure_obj_null; auto).
Qed. 

Lemma erasure_obj_null_equal_erasure_h : forall h t, 
    erasure_obj_null (erasure_obj_null t h) (erasure_heap h) = (erasure_obj_null t h).
    Proof. intros. induction t. induction a; try (unfold erasure_obj_null; auto). 
        assert (forall h o, (exists cls F lb, lookup_heap_obj h o = Some (Heap_OBJ cls F lb) ) 
        \/ lookup_heap_obj h o = None).
      intro h0. induction h0.  right. unfold lookup_heap_obj. auto. 
      intro o0. induction a. case_eq ( beq_oid o0 o1). unfold lookup_heap_obj.  intro. unfold lookup_heap_obj. rewrite H. 
       rename h1 into ho. induction ho.     left. exists c. exists f. exists l. auto. 
      intro. unfold lookup_heap_obj. rewrite H. fold lookup_heap_obj. apply IHh0. 
      destruct H with h o. destruct H0 as [cls]. destruct H0 as [F]. destruct H0 as [lb]. rewrite H0.
      case_eq (flow_to lb L_Label ). intro. 
      assert (exists F', lookup_heap_obj (erasure_heap h) o = Some (Heap_OBJ cls F' lb)).
      apply lookup_erasure_heap with F. auto. auto. destruct H2 as [F']. rewrite H2. rewrite H1. auto. 
     intro. auto. 
    rewrite H0. auto. 
    (unfold erasure_obj_null; auto).
  Qed. 


    


Lemma erasure_L_fun_value : forall t, 
  value t -> value (erasure_L_fun t). 
Proof. intros.  induction t; auto; inversion H. 
- unfold erasure_L_fun. fold erasure_L_fun.  case_eq ( flow_to l L_Label); intro. 
   apply IHt in H1. auto. auto.
- unfold erasure_L_fun. fold erasure_L_fun.  case_eq ( flow_to l L_Label); intro. 
   apply IHt in H1. auto. auto.
Qed. 
  

Lemma erasure_L_fun_not_value  : forall t T h ct, 
tm_has_type ct empty_context h t T -> 
t <> return_hole ->
~ value t -> ~ value (erasure_L_fun t).
Proof. intros. induction t; auto; try (unfold erasure_L_fun; fold erasure_L_fun; intro contra; inversion contra; fail). 
  - inversion H. subst. assert (value (v_l t l)). auto. intuition.
  - inversion H. subst. assert (value (v_opa_l t l)). auto. intuition.
Qed. 

Lemma field_access_erasure_L_fun_pop : forall t2 fs1 lb2 sf2 ctns_stack h2 f ct , 
  flow_to lb2 L_Label = true ->
 (~ value (erasure_L_fun t2)) ->
  erasure_fun ct (Container (FieldAccess t2 f) fs1 lb2 sf2) ctns_stack h2 ==l>
  erasure_fun ct (Container t2 (FieldAccess hole f :: fs1) lb2 sf2) ctns_stack h2.
Proof with eauto. intros t2 fs1 lb2 sf2 ctns_stack h2 f ct. intro H_flow. intro Hy. 
remember ctns_stack as ctns. 
assert (erasure_L_fun (FieldAccess hole f) = (FieldAccess hole f)).
unfold erasure_L_fun. fold erasure_L_fun. auto. 
 pose proof (multi_erasure_heap_equal h2) as H_h.  
  pose proof (multi_erasure_L_tm_equal t2) as Ht2. 
  assert (erasure_fun ct (Container (FieldAccess t2 f) fs1 lb2 sf2) ctns h2 ==>
    Config ct
    (Container (erasure_L_fun t2) (erasure_L_fs  (FieldAccess hole f :: fs1)) lb2
       (fun x : id => erasure_obj_null (sf2 x) h2)) ctns (erasure_heap h2) ).
destruct ctns;  try (induction c); unfold erasure; unfold erasure_fun; 
induction fs1; unfold erasure_L_fs; fold erasure_L_fs; rewrite H_flow; rewrite H; 
 try (eauto using reduction).

  assert ( erasure ( Config ct
       (Container (erasure_L_fun t2) (erasure_L_fs (FieldAccess hole f :: fs1)) lb2
          (fun x : id => erasure_obj_null (sf2 x) h2)) ctns_stack (erasure_heap h2)) =
    erasure_fun ct (Container t2 (FieldAccess hole f :: fs1) lb2 sf2) ctns h2).
  rewrite <- Heqctns. 
  assert (forall a, (fun x : id =>
        erasure_obj_null (erasure_obj_null (sf2 x) h2) (erasure_heap h2)) a = 
         (fun x : id => erasure_obj_null (sf2 x) h2) a ). 
  intro a. apply erasure_obj_null_equal_erasure_h. 
  apply functional_extensionality in H1. 

destruct ctns;  try (induction c); unfold erasure; unfold erasure_fun; 
induction fs1; unfold erasure_L_fs; fold erasure_L_fs; rewrite H_flow;rewrite H1; rewrite H; rewrite H;  
  rewrite H_h;rewrite Ht2; try ( pose proof (multi_erasure_L_tm_equal a) as Ha; rewrite Ha;
  pose proof (multi_erasure_L_fs_equal fs1) as Hfs1; rewrite Hfs1
);auto. 
  rewrite <- Heqctns in H1. 
  apply L_reduction with (Config ct
       (Container (erasure_L_fun t2)
          (erasure_L_fs (FieldAccess hole f :: fs1)) lb2
          (fun x : id => erasure_obj_null (sf2 x) h2)) ctns (erasure_heap h2)); auto.
Qed.  

Lemma field_access_erasure_L_fun_push : forall t1 fs lb sf ctns_stack h f ct , 
  flow_to lb L_Label = true ->
 (value t1) ->
erasure_fun ct (Container t1 (FieldAccess hole f :: fs) lb sf) ctns_stack h ==l>
erasure_fun ct (Container (FieldAccess t1 f) fs lb sf) ctns_stack h.
Proof with eauto. intros t1 fs lb sf ctns_stack h f ct. intro H_flow. intro Hv. 
remember ctns_stack as ctns. 
assert (erasure_L_fun (FieldAccess hole f) = (FieldAccess hole f)).
unfold erasure_L_fun. fold erasure_L_fun. auto. 
 pose  proof (erasure_L_fun_value t1 Hv).
 pose proof (multi_erasure_heap_equal h) as H_h.  
  pose proof (multi_erasure_L_tm_equal t1) as Ht1. 
assert (forall a, (fun x : id =>
        erasure_obj_null (erasure_obj_null (sf x) h) (erasure_heap h)) a = 
         (fun x : id => erasure_obj_null (sf x) h) a ). 
  intro a. apply erasure_obj_null_equal_erasure_h. 
  apply functional_extensionality in H1. 

  assert (erasure_fun ct (Container t1 (FieldAccess hole f :: fs) lb sf) ctns h ==>
    Config ct
    (Container (FieldAccess (erasure_L_fun t1) f) (erasure_L_fs fs) lb
       (fun x : id => erasure_obj_null (sf x) h)) ctns (erasure_heap h) ).
destruct ctns;  try (induction c); unfold erasure; unfold erasure_fun; 
induction fs; unfold erasure_L_fs; fold erasure_L_fs; rewrite H_flow; rewrite H; 
 try (eauto using reduction).

  assert ( erasure ( Config ct
    (Container (FieldAccess (erasure_L_fun t1) f) (erasure_L_fs fs) lb
       (fun x : id => erasure_obj_null (sf x) h)) ctns (erasure_heap h)  ) =
    erasure_fun ct (Container (FieldAccess t1 f) fs lb sf) ctns h).

destruct ctns;  try (induction c); unfold erasure; unfold erasure_fun; 
induction fs; unfold erasure_L_fs; fold erasure_L_fs; rewrite H_flow;
rewrite H1; rewrite H_h; unfold erasure_L_fun; fold erasure_L_fun; rewrite Ht1;  auto;
  try ( pose proof (multi_erasure_L_tm_equal a) as Ha; rewrite Ha;
   pose proof (multi_erasure_L_fs_equal fs) as Hfs; rewrite Hfs);auto. 

  apply L_reduction with (Config ct
       (Container (FieldAccess (erasure_L_fun t1) f) (erasure_L_fs fs) lb
          (fun x : id => erasure_obj_null (sf x) h)) ctns (erasure_heap h)); auto.
Qed. 

Lemma method_call_erasure_L_fun_pop1 : forall t2 fs1 lb2 sf2 ctns_stack h2 ct e2 meth, 
  flow_to lb2 L_Label = true ->
 (~ value (erasure_L_fun t2)) ->
erasure_fun ct (Container (MethodCall t2 meth e2) fs1 lb2 sf2) ctns_stack h2 ==l>
erasure_fun ct (Container t2 (MethodCall hole meth e2 :: fs1) lb2 sf2) ctns_stack h2.
Proof with eauto. intros  t2 fs1 lb2 sf2 ctns_stack h2 ct e2 meth. intro H_flow. intro Hy. 
remember ctns_stack as ctns. 
 pose proof (multi_erasure_heap_equal h2) as H_h.  
  pose proof (multi_erasure_L_tm_equal t2) as Ht2. 
  assert (erasure_fun ct (Container (MethodCall t2 meth e2) fs1 lb2 sf2) ctns h2 ==>
    Config ct
    (Container (erasure_L_fun t2) ((MethodCall hole meth (erasure_L_fun e2)) :: (erasure_L_fs fs1)) lb2
       (fun x : id => erasure_obj_null (sf2 x) h2)) ctns (erasure_heap h2) ).
destruct ctns;  try (induction c); unfold erasure; unfold erasure_fun; 
induction fs1; unfold erasure_L_fs; fold erasure_L_fs; rewrite H_flow; 
 unfold erasure_L_fun; fold erasure_L_fun;
 try (eauto using reduction).

  assert (erasure_fun
     ct
      (Container (erasure_L_fun t2)
         (MethodCall hole meth (erasure_L_fun e2) :: erasure_L_fs fs1) lb2
         (fun x : id => erasure_obj_null (sf2 x) h2)) ctns (erasure_heap h2) =
         erasure_fun ct (Container t2 (MethodCall hole meth e2 :: fs1) lb2 sf2) ctns  h2).
  assert (forall a, (fun x : id =>
        erasure_obj_null (erasure_obj_null (sf2 x) h2) (erasure_heap h2)) a = 
         (fun x : id => erasure_obj_null (sf2 x) h2) a ). 
  intro a. apply erasure_obj_null_equal_erasure_h. 
  apply functional_extensionality in H0. 

 pose proof (multi_erasure_L_tm_equal e2) as He2. 
destruct ctns;  try (induction c); unfold erasure; unfold erasure_fun; 
induction fs1; unfold erasure_L_fs; fold erasure_L_fs; rewrite H_flow; 
try (unfold erasure_L_fun; fold erasure_L_fun);
try( rewrite H0);  try (rewrite He2);
  try (rewrite H_h); try (rewrite Ht2); try ( pose proof (multi_erasure_L_tm_equal a) as Ha; rewrite Ha;
  pose proof (multi_erasure_L_fs_equal fs1) as Hfs1; rewrite Hfs1
);auto. 
  apply L_reduction with (Config ct
      (Container (erasure_L_fun t2)
         (MethodCall hole meth (erasure_L_fun e2) :: erasure_L_fs fs1) lb2
         (fun x : id => erasure_obj_null (sf2 x) h2)) ctns (erasure_heap h2)); auto.
Qed.

Lemma method_call_erasure_L_fun_push1 : forall v fs1 lb2 sf2 ctns_stack h2 ct e2 meth, 
  flow_to lb2 L_Label = true ->
 (value v) ->
erasure_fun ct (Container v ((MethodCall hole meth e2) :: fs1) lb2 sf2) ctns_stack h2 ==l>
erasure_fun ct (Container (MethodCall v meth e2) fs1 lb2 sf2) ctns_stack h2.
Proof with eauto. intros v fs1 lb2 sf2 ctns_stack h2 ct e2 meth. intro H_flow. intro Hv. 
remember ctns_stack as ctns. 
 pose  proof (erasure_L_fun_value v Hv).
 pose proof (multi_erasure_heap_equal h2) as H_h.  
  pose proof (multi_erasure_L_tm_equal v) as H_m_v.
  pose proof (multi_erasure_L_tm_equal e2) as He2. 
assert (forall a, (fun x : id =>
        erasure_obj_null (erasure_obj_null (sf2 x) h2) (erasure_heap h2)) a = 
         (fun x : id => erasure_obj_null (sf2 x) h2) a ). 
  intro a. apply erasure_obj_null_equal_erasure_h. 
  apply functional_extensionality in H0. 

  assert (erasure_fun ct (Container v ((MethodCall hole meth e2) :: fs1) lb2 sf2) ctns h2 ==>
    Config ct
    (Container (MethodCall (erasure_L_fun v) meth (erasure_L_fun e2)) (erasure_L_fs fs1) lb2
       (fun x : id => erasure_obj_null (sf2 x) h2)) ctns (erasure_heap h2) ).
destruct ctns;  try (induction c); unfold erasure; unfold erasure_fun; 
induction fs1; unfold erasure_L_fs; fold erasure_L_fs; rewrite H_flow; 
unfold erasure_L_fun; fold erasure_L_fun;
 try (eauto using reduction).

  assert( erasure ( Config ct
       (Container (MethodCall (erasure_L_fun v) meth (erasure_L_fun e2))
          (erasure_L_fs fs1) lb2 (fun x : id => erasure_obj_null (sf2 x) h2))
       ctns (erasure_heap h2)) =
    erasure_fun ct (Container (MethodCall v meth e2) fs1 lb2 sf2) ctns h2).

destruct ctns;  try (induction c); unfold erasure; unfold erasure_fun; 
induction fs1; unfold erasure_L_fs; fold erasure_L_fs; rewrite H_flow;
try (unfold erasure_L_fun; fold erasure_L_fun);
 try (rewrite He2); try (rewrite H_m_v);

  try (rewrite H_h); try (rewrite H0); try (rewrite Ht2); try ( pose proof (multi_erasure_L_tm_equal a) as Ha; rewrite Ha;
  pose proof (multi_erasure_L_fs_equal fs1) as Hfs1; rewrite Hfs1
);auto. 

  apply L_reduction with (( Config ct
       (Container (MethodCall (erasure_L_fun v) meth (erasure_L_fun e2))
          (erasure_L_fs fs1) lb2 (fun x : id => erasure_obj_null (sf2 x) h2))
       ctns (erasure_heap h2))); auto.
Qed. 

Lemma method_call_erasure_L_fun_push2 : forall v1 t1 fs1 lb2 sf2 ctns_stack h2 ct meth, 
  flow_to lb2 L_Label = true ->
 (value t1) -> (value v1) ->
erasure_fun ct (Container t1 ((MethodCall v1 meth hole) :: fs1) lb2 sf2) ctns_stack h2 ==l>
erasure_fun ct (Container (MethodCall v1 meth t1) fs1 lb2 sf2) ctns_stack h2.
Proof with eauto. intros v1 t1 fs1 lb2 sf2 ctns_stack h2 ct meth.  intro H_flow. intro Hv_t1.
intro Hv_v1.  
remember ctns_stack as ctns. 
 pose  proof (erasure_L_fun_value v1 Hv_v1).
 pose  proof (erasure_L_fun_value t1 Hv_t1).
 pose proof (multi_erasure_heap_equal h2) as H_h.  
  pose proof (multi_erasure_L_tm_equal v1) as H_m_v1.
  pose proof (multi_erasure_L_tm_equal t1) as H_m_t1.

assert (forall a, (fun x : id =>
        erasure_obj_null (erasure_obj_null (sf2 x) h2) (erasure_heap h2)) a = 
         (fun x : id => erasure_obj_null (sf2 x) h2) a ). 
  intro a. apply erasure_obj_null_equal_erasure_h. 
  apply functional_extensionality in H1. 

  assert (erasure_fun ct (Container t1 (MethodCall v1 meth hole :: fs1) lb2 sf2) ctns h2 ==>
    Config ct
    (Container (MethodCall (erasure_L_fun v1) meth (erasure_L_fun t1)) (erasure_L_fs fs1) lb2
       (fun x : id => erasure_obj_null (sf2 x) h2)) ctns (erasure_heap h2) ).
destruct ctns;  try (induction c); unfold erasure; unfold erasure_fun; 
induction fs1; unfold erasure_L_fs; fold erasure_L_fs; rewrite H_flow; 
unfold erasure_L_fun; fold erasure_L_fun;
 try (eauto using reduction).

  assert( erasure_fun ct
      (Container (MethodCall (erasure_L_fun v1) meth (erasure_L_fun t1))
          (erasure_L_fs fs1) lb2 (fun x : id => erasure_obj_null (sf2 x) h2))
       ctns (erasure_heap h2) =
    erasure_fun ct (Container (MethodCall v1 meth t1) fs1 lb2 sf2) ctns h2).

destruct ctns;  try (induction c); unfold erasure; unfold erasure_fun; 
induction fs1; unfold erasure_L_fs; fold erasure_L_fs; rewrite H_flow;
try (unfold erasure_L_fun; fold erasure_L_fun);
 try (rewrite He2); try (rewrite H_m_v1); try (rewrite H_m_t1);
  try (rewrite H_h); try (rewrite H1); try (rewrite Ht2); try ( pose proof (multi_erasure_L_tm_equal a) as Ha; rewrite Ha;
  pose proof (multi_erasure_L_fs_equal fs1) as Hfs1; rewrite Hfs1
);auto. 

  apply L_reduction with (Config ct
       (Container (MethodCall (erasure_L_fun v1) meth (erasure_L_fun t1))
          (erasure_L_fs fs1) lb2 (fun x : id => erasure_obj_null (sf2 x) h2))
       ctns (erasure_heap h2)); auto.
Qed. 


Lemma erasure_L_fun_preserve_value : forall v, 
  value v ->
  value (erasure_L_fun v).
Proof. 
  intros. induction v; try (inversion H); try ( unfold erasure_L_fun; auto; fail).
  unfold erasure_L_fun. fold erasure_L_fun. case_eq (flow_to l L_Label).  intro. auto. auto. 
  unfold erasure_L_fun. fold erasure_L_fun. case_eq (flow_to l L_Label).  intro. auto. auto.
Qed. 


(*
Lemma erasure_preserve_value : forall v v' sigma sigma' CT, 
  Config CT v sigma =e=> Config CT v' sigma' -> value v ->
  value v'.
Proof. intros. inversion H. subst. apply erasure_L_fun_preserve_value. auto. 
          subst. apply erasure_H_fun_preserve_value. auto.
Qed.  
 *)