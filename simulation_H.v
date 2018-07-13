Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.

Require Import SfLib.
Require Import Language.
Require Import Lemmas.
Require Import Low_eq.
Require Import Label.

Lemma simulation_L : forall ct t1 fs1 lb1 sf1 ctns_stack1 h1  t2 fs2 lb2 sf2 ctns_stack2 h2
      ctn1' ctns_stack1' h1'  ctn2' ctns_stack2' h2' φ, 
      valid_config (Config ct (Container t1 fs1 lb1 sf1) ctns_stack1 h1 ) ->
      valid_config (Config ct (Container t2 fs2 lb2 sf2) ctns_stack2 h2 ) ->
      forall T, tm_has_type ct empty_context h1 t1 T -> 
      tm_has_type ct empty_context h2 t2 T -> 
      field_wfe_heap ct h1 -> wfe_heap ct h1 ->
      (*wfe_stack_frame ct h1 sf1 -> *)
      field_wfe_heap ct h2 -> wfe_heap ct h2 ->
      (* wfe_stack_frame ct h2 sf2 -> *)
      flow_to lb1 L_Label = true ->
      flow_to lb2 L_Label = true ->
      L_equivalence_config (Config ct (Container t1 fs1 lb1 sf1) ctns_stack1 h1 )
            (Config ct (Container t2 fs2 lb2 sf2) ctns_stack2 h2)  φ ->
     Config ct (Container t1 fs1 lb1 sf1) ctns_stack1 h1 
      ==> Config ct ctn1' ctns_stack1' h1' ->
     Config ct (Container t2 fs2 lb2 sf2) ctns_stack2 h2
      ==> Config ct ctn2' ctns_stack2' h2' ->
     L_equivalence_heap h1 h2 φ ->
      exists  φ', L_equivalence_config (Config ct ctn1' ctns_stack1' h1')
                                       (Config ct ctn2' ctns_stack2' h2')  φ'.

  

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