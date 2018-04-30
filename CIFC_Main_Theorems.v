Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.

Add LoadPath "/Users/llama_jian/Develop/HarvardPLCIFC".

Require Import Label. 
Require Import Lang. 
Require Import Helper_Lemmas. 

Theorem progress : forall t T sigma  CT s h, 
  field_wfe_heap CT h -> sigma = SIGMA s h ->  wfe_heap CT h -> wfe_stack CT h s -> 
  has_type CT empty_context h t T -> value t \/ (exists config', Config CT t sigma ==> config').
Proof with auto.
  intros t T sigma CT s h.
  intro wfe_fields. intros.
  remember (empty_context) as Gamma.
  induction H2; subst Gamma... 
(* TVar *)
- inversion H2.

(* null *)
-  left. apply v_null.
(* field access *)
- right. 
    destruct IHhas_type. auto. auto. auto. auto.  
    + auto. 
    + 
      inversion H6. rewrite <- H7 in H2. 
      assert (exists F lb, lookup_heap_obj h o = Some (Heap_OBJ cls_def F lb)).
       apply wfe_oid with (gamma:=empty_context) (o:=o) (ct:=CT) (s:=s) (h:=h) 
                          (sigma:=sigma) (cls_def:=cls_def) (cn:=clsT). auto. auto. auto. auto. 
       destruct H8 as [F]. destruct H8 as [lb].

      assert (exists v, F(f) = Some v).
      apply field_val_of_heap_obj with (h:=h) (o:=o)  (CT:=CT) 
                              (cls_def:=cls_def) (F:=F) (lo:=lb) (cls':=cls') (fields:=fields_def).
      auto. auto. auto. auto. auto. 



      destruct H9 as [v].
      remember (join_label lb (current_label sigma)) as l'.
      remember (update_current_label s l') as s'.
      remember (SIGMA s' h) as sigma'.
            exists (Config CT v sigma'). apply ST_fieldRead2 with 
            (sigma:=sigma) (sigma':=sigma') (o:=o) (s:=s) (h:=h) (fname:=f) (lb:=lb) 
            (cls:=cls_def) (fields:=F) (v:=v) (l':=l') (s':=s'). 
            auto. auto. auto.            auto. auto. auto. 
    (* skip *)
    rewrite <- H7 in H2. inversion H2. 
    (* call field access on null point object *)
    exists Error_state. apply ST_fieldReadException.
    (* label is primitive: calling field access is not valid *)
    rewrite <- H7 in H2. inversion H2.
   
     (* call field access on labeled value*)
    {rewrite <- H8  in H2. inversion H2. }
    
     (* call field access on opaque label value*)
    {rewrite <- H8  in H2. inversion H2. }

     (* context rule *)
    + destruct H6. destruct x. 
    exists (Config CT (FieldAccess t f) s0). pose proof (ct_consist CT c e t sigma s0). 
    destruct H7.  auto.  
    apply ST_fieldRead1 with (sigma:=sigma) (sigma':=s0) (e:=e) (e':=t) (f:=f). assumption.

    exists Error_state. apply ST_fieldRead3. auto.

(* method call *)
- 
   destruct IHhas_type1. auto. auto. auto. auto.
    + auto.
       + right. inversion H5. rewrite <- H6 in H2_. inversion H2_.
          (* case analysis for argument: if the argument is a value *)
             destruct IHhas_type2. auto. auto. auto. auto. auto. subst. 
            remember (sf_update empty_stack_frame arg_id argu) as sf. 
            remember (SIGMA s h ) as sigma.
            remember (current_label sigma) as l.
            remember (Labeled_frame l sf) as lsf. 
            remember (cons lsf s) as s'.
            remember (SIGMA s' (get_heap sigma)) as sigma'. 

            auto. 
            exists (Config CT ((Return body)) sigma').
            destruct H14 as [F]. destruct H as [lo].
            apply ST_MethodCall3 with (sigma:=sigma) (sigma':=sigma') (o:=o) (s:=s) (h:=h) (cls:=cls_def) (fields:=F) 
                                       (v:=argu) (lx:=lo) (l:=l) 
                                       (cls_a:=arguT) (s':=s') (sf:=sf) (lsf:=lsf) (arg_id:=arg_id) 
                                       (body:=body) (meth:=meth) (returnT:=returnT) ;auto.
            rewrite <- H9 in H2. inversion H2.  auto. 
          (* case analysis for argument, if the argument is not a value *)
            subst.
                destruct H15 as [config']. destruct config'. rename t into t'.
                pose proof (excluded_middle_opaqueLabel argu).
                destruct H4.
                  (* case for argu = unlabelOpaque t *)
                  destruct H4 as [t]. 
                  rewrite -> H4 in H. inversion H. subst. 
                  exists (Config c (MethodCall (ObjId o) meth (unlabelOpaque e')) s0).
                  apply ST_MethodCall2 with (sigma:=(SIGMA s h)) (sigma':=s0) 
                                            (v:=(ObjId o)) (e:=unlabelOpaque t) (e':=unlabelOpaque e') (id:=meth).
                  intros. subst. intro contra. inversion contra. rewrite -> H10 in H. inversion H4.
                      rewrite <- H8 in H; subst; inversion H7. auto.  subst. inversion H7.  subst.
                      inversion H7. subst. inversion H7. subst. inversion H7. subst. inversion H7.
                      assumption. apply v_oid. 
                      subst. 
                      remember (SIGMA s h ) as sigma.
                      remember (sf_update empty_stack_frame arg_id t') as sf.
                      remember (join_label lb (current_label sigma)) as l'. 
                      remember (Labeled_frame l' sf) as lsf. 
                      remember (cons lsf s) as s'.
                      remember (SIGMA s' (get_heap sigma)) as sigma''.
                      exists (Config c (Return body) sigma'').  
                      destruct H14 as [F]. destruct H4 as [lo].
                      apply ST_MethodCall_unlableOpaque with (sigma:=sigma) (sigma':=sigma'') (o:=o) (s:=s) (h:=h) 
                                            (cls:=cls_def0) (fields:=F) (v:=t') (lx:=lo) (l':=l') (lb:=lb) (s':=s')
                                           (sf:=sf) (lsf:=lsf) (arg_id:=arg_id) (cls_a:=arguT) (body:=body) 
                                           (meth:=meth) (returnT:=returnT) .
                      auto. auto. auto. auto. auto. auto. subst. 
                      
                      inversion H2_0. inversion H11. auto. 
                      rewrite <- H9 in H2. inversion H2. rewrite <- H7. auto.  

                      auto. 
                  (*exception case
                  subst. exists NPE. exists (SIGMA s h).
                  apply ST_MethodCallOpaqueDataException with (sigma:=(SIGMA s h)) (o:=o).   *)

                  (* case for argu <> unlabelOpaque t *)
                  exists (Config CT (MethodCall (ObjId o) meth t') s0). 
                  apply ST_MethodCall2 with (sigma:=(SIGMA s h)) (sigma':=s0) (v:=((ObjId o))) 
                                            (e:=argu) (e':=t') (id:=meth).
                  intro. intro. intro. 
                  
                  assert (argu <> unlabelOpaque t).  apply (H4 t). apply (H4 t). auto.
                  assert (CT = c). apply ct_consist with (t:=argu) (t':=t') (sigma:=(SIGMA s h)) (sigma':=s0); auto. 
                  rewrite <- H6 in H. auto. apply v_oid.
                   
                  exists Error_state. 
                   apply ST_MethodCall5 with (sigma:=(SIGMA s h)) (v:=(ObjId o)) (e:=argu) (id:=meth).
                  intros. intro contra. rewrite contra in H. inversion H. inversion H4. 
                  rewrite <- H12 in H8. inversion H8.                    rewrite <- H12 in H8. inversion H8.
                  rewrite <- H12 in H8. inversion H8.                    rewrite <- H12 in H8. inversion H8.
                  rewrite <- H15 in H8. inversion H8.                    rewrite <- H15 in H8. inversion H8.
                  rewrite <- H10 in H6. auto. auto. auto. subst. inversion H2_. 

                   exists Error_state. 
                  apply ST_MethodCallException with (sigma:=sigma) (v:=argu) (meth:=meth). 

                  rewrite <- H6 in H2_. inversion H2_. 
                rewrite <- H7 in H2_. inversion H2_.                 
                 rewrite <- H7 in H2_. inversion H2_. 
      +  right. destruct H5 as [config']. destruct config'. 

            exists (Config CT (MethodCall t meth argu) (s0)).
                  apply ST_MethodCall1 with (sigma:=sigma) (sigma':=s0) (e2:=argu) (e:=e) (e':=t) (id:=meth). 
                  assert (CT = c). apply ct_consist with (t:=e) (t':=t) (sigma:=sigma) (sigma':=s0); auto. 
                  rewrite <- H6 in H5.
                  apply H5.

            exists Error_state. apply ST_MethodCall4 with (sigma:=sigma) (e:=e) (e2:=argu) (id:=meth). auto. 

(* new expression *)
- right. inversion H0.
    destruct H2 as [cls_def]. destruct H2 as [field_defs]. destruct H2 as [method_defs].
    destruct H2. 
(*
    assert (exists o, empty_heap o = None). 
      unfold empty_heap. auto. exists (OID 0). auto. 
      destruct H7 as [o]. 
*)
      remember (get_fresh_oid h) as o.
      remember (init_field_map (find_fields cls_def) empty_field_map) as F.
      remember (current_label sigma) as lb. 
      remember  (add_heap_obj h o (Heap_OBJ cls_def F lb)) as h'.
      remember (SIGMA s h') as sigma'.
      exists (Config CT (ObjId o) sigma').
       
      (*destruct H3 as [field_defs]. destruct H3 as [method_defs].*)
      apply ST_NewExp with (sigma:=sigma) (sigma':=sigma') (F:=F) (o:=o) (h:=h) (cls:=cls_def)
                  (h':=h') (s:=s) (lb:=lb) (cls_name:=cls_name) 
                  (field_defs:= field_defs) (method_defs:=method_defs).

      subst; auto. auto.  auto.  auto. auto. auto.  auto. auto.   
      
    destruct H2 as [cls_def']. destruct H2 as [field_defs']. destruct H2 as [method_defs'].
    destruct H2. 

      remember (current_label sigma) as lb. 
    remember (get_fresh_oid h) as o'.
      remember (init_field_map (find_fields cls_def') empty_field_map) as F'.
      remember (add_heap_obj h o' (Heap_OBJ cls_def' F' lb)) as h''.
      remember (SIGMA s h'') as sigma''.
      exists (Config CT (ObjId o') sigma''). 

      apply ST_NewExp with (sigma:=sigma) (sigma':=sigma'') 
                                          (F:=F') (o:=o') (h:=h) (cls:=cls_def')
                                          (h':=h'') (s:=s) (lb:=lb) (cls_name:=cls_name)
                                          (field_defs:=field_defs') (method_defs:=method_defs').
      auto. auto.  auto.  auto. auto. auto.  auto. auto. 

(* label *)
- left. apply  v_label.


(* label Data *)
- right. destruct IHhas_type2. auto. auto. auto. auto. auto. 
            destruct IHhas_type1. auto. auto. auto. auto. auto.
            
            (* subgoal #1 *)
           exists (Config CT (v_l e lb) sigma).
                apply ST_LabelData2 with (sigma:=sigma) (lb:=lb) (v:=e).  auto. 

            (* subgoal #2 *)  
                destruct H3 as [config']. inversion H3.  
                destruct H2 as [config']. destruct config'. 
                    exists (Config CT (labelData t lb) s0).
                    apply ST_LabelData1 with (sigma:=sigma) (sigma':=s0) (e:=e) (e':=t) (lb:=lb).
                    auto.
                    assert (CT = c). apply ct_consist with (t:=e) (t':=t) (sigma:=sigma) (sigma':=s0); auto. 
                    rewrite <- H3 in H2.  auto. 
           (* subgoal #4*)
               exists Error_state. 
                  apply ST_LabelDataError with (e:=e) (sigma:=sigma) (lb:=lb). auto. 

(* unlabel : *)
- right.
 
            destruct IHhas_type. auto. auto. auto. auto. auto.
             (* subgoal #1 *)
                + inversion H3. 
                     rewrite <- H4 in H2. inversion H2. 
                     rewrite <- H4 in H2.  inversion H2. 
                    exists Error_state.  apply ST_unlabelDataException with (sigma:=sigma).
                    rewrite <- H4 in H2.  inversion H2.

             (* subgoal #2 *)
                remember ( join_label lb (current_label sigma)) as l'.
                remember (update_current_label s l') as s'.
                remember (SIGMA s' (get_heap sigma)) as sigma'.
                exists (Config CT v sigma'). 
                apply ST_unlabel2 with (sigma:=sigma) (s':=s') (sigma':=sigma') (l':=l') (s:=s) (h:=h) (lb:=lb) (v:=v). 
                auto. auto. auto. auto. auto.

            (* subgoal #3 *)
                rewrite <- H5 in H2.  inversion H2. 

              + destruct H3 as [config']. 
                 destruct config'. 
                 exists (Config CT (unlabel t) s0). 
                 apply ST_unlabel1 with (sigma:=sigma) (sigma':=s0) (e:=e) (e':=t). auto. 
                assert (CT = c). apply ct_consist with (t:=e) (t':=t) (sigma:=sigma) (sigma':=s0); auto. 
                    rewrite <- H4 in H3. auto.  
                 exists Error_state. apply ST_unlabelContextError with (sigma:=sigma) (e:=e). auto. 

(* label Of *)
(* same issue as above, we may need to add (v_l v lb) as a value*)
- right. 
         destruct IHhas_type. auto. auto. auto. auto. auto.  
            (* subgoal #1 *)
                + inversion H3. rewrite <- H4 in H2. inversion H2. 
                    rewrite <- H4 in H2. inversion H2. 
                    exists Error_state.  apply ST_labelOfDataException with (sigma:=sigma).
                    rewrite <- H4 in H2.  inversion H2.
                    
                   exists (Config CT (l lb) (sigma)). apply ST_labelof2 with (v:=v) (lb:=lb).

                    rewrite <- H5 in H2. inversion H2. 
             (* subgoal #2 *)
                + destruct H3 as [config']. destruct config'. 
                    exists (Config CT (labelOf t) s0). apply ST_labelof1 with (sigma:=sigma) (sigma':=s0) (e:=e) (e':=t).
                    assert (CT = c). apply ct_consist with (t:=e) (t':=t) (sigma:=sigma) (sigma':=s0); auto. 
                    rewrite <- H4 in H3. auto. 
    
             (*error state *)
                 exists Error_state. apply ST_labelofCtxError with (e:=e) (sigma:=sigma). auto. 

(* unlabel opaque *)
- right. 
         destruct IHhas_type. auto. auto. auto. auto. auto. 
            (* subgoal #1 *)
                + inversion H3. rewrite <- H4 in H2. inversion H2. 
                    rewrite <- H4 in H2. inversion H2. 
                    exists Error_state.  apply ST_unlabel_opaqueDataException with (sigma:=sigma).
                    rewrite <- H4 in H2.  inversion H2.
              
                     rewrite <- H5 in H2. inversion H2. 
 
                remember ( join_label lb (current_label sigma)) as l'.
                remember (update_current_label s l') as s'.
                remember (SIGMA s' (get_heap sigma)) as sigma'.
                exists (Config CT v sigma'). 
                apply ST_unlabel_opaque2 with (sigma:=sigma) (s':=s') (sigma':=sigma') (l':=l') (s:=s) (h:=h) (lb:=lb) (v:=v). 
                auto. auto. auto. auto. 

             (* subgoal #2 *)
                + destruct H3 as [config']. destruct config'. 
                    exists (Config CT (unlabelOpaque t) s0). apply ST_unlabel_opaque1 with (sigma:=sigma) (sigma':=s0) (e:=e) (e':=t). auto.
                  assert (CT = c). apply ct_consist with (t:=e) (t':=t) (sigma:=sigma) (sigma':=s0); auto. 
                    rewrite <- H4 in H3. auto.  
                exists Error_state. apply ST_unlabel_opaque_ctx_error with (sigma:=sigma) (e:=e).  auto. 

(* opaque call *)
- right.  destruct IHhas_type. auto. auto. auto. auto. auto. 
            (* opaquecall won't be applied on values  *)

            remember (current_label sigma) as lb. 
            exists (Config CT (v_opa_l e lb)  sigma). 
            apply ST_opaquecall_val2 with (v:=e) (sigma:=sigma) (lb:=lb). auto. auto. 

            subst. destruct H3 as [config'].
                pose proof (excluded_middle_returnT e).
                destruct H3.
                  (* case for e = return t *)
                  destruct H3 as [t].
                  rewrite -> H3 in H. 
                  inversion H.  subst. 
                  exists (Config CT (opaqueCall(Return e')) sigma').
                  apply ST_opaquecall_return1 with (sigma:=(SIGMA s h)) (sigma':=sigma') (e:= t) (e':=e').
                  auto.

                  exists Error_state. rewrite H3.  apply ST_opaquecall_return_error with (sigma:=(SIGMA s h)) (e:=t).
                  auto. 

                  destruct config'.
                  remember  (current_label sigma) as lb. 
                  exists (Config CT (v_opa_l t lb) (SIGMA s' h)).
                  rewrite H3. 
                  apply ST_opaquecall_return2 with (sigma:=(SIGMA s h) ) (sigma':=(SIGMA s' h)) (s:=s) (h:=h) 
                                            (lb:=lb) (s':=s') (lsf:=lsf) (v:=t).
                  auto. inversion H8.  auto.
                  rewrite H3 in H2. inversion H2. inversion H8.  auto.
                  rewrite <- H6. auto. auto. auto.
                  inversion H12.  

                  exists Error_state. rewrite H3.  
                  apply ST_opaquecall_return4 with (sigma:=(SIGMA s h)) (s:=s) (h:=h) (lsf:=lsf); auto.
                  inversion H9. auto. 

                    (* case for e <> return t *)

                  destruct config'. 
                  exists (Config CT (opaqueCall t) s0). 
                  apply ST_opaquecall1 with  (sigma:=(SIGMA s h) ) (sigma':=(s0)) (e:=e) (e':=t). 

                  intros. apply H3. 
                  assert (CT = c). apply ct_consist with (t:=e) (t':=t) (sigma:=(SIGMA s h)) (sigma':=s0); auto. 
                  rewrite <- H4 in H. auto.

                  exists Error_state. apply ST_opaquecall_ctx_error with (sigma:=(SIGMA s h)) (e:=e). auto. 

(* Skip *)
  - left. apply v_none. 

(* assignment *)
- right. destruct IHhas_type. auto. auto. auto. auto. auto. 
                  remember (update_stack_top s x e) as s0.
                  remember (SIGMA s0 h) as sigma'.
                  exists (Config CT Skip sigma').
                  apply ST_assignment2 with (sigma:=sigma) (sigma':=sigma') (id:=x) (v:=e) (s':=s0) (s:=s) (h:=h).
                  auto. auto. auto. auto.

                  destruct H4 as [config']. destruct config'. 
                  exists (Config CT (Assignment x t) s0). 
                  apply ST_assignment1 with (sigma:=sigma) (sigma':=s0) (e:=e) (e':=t) (id:=x).   
                  assert (CT = c). apply ct_consist with (t:=e) (t':=t) (sigma:=sigma) (sigma':=s0); auto. 
                    rewrite <- H5 in H4. auto.  
                  auto.

                  exists Error_state. 
                  apply ST_assignment_ctx_error with (sigma:=sigma) (e:=e) (id:=x). auto.  

(* FieldWrite *)
-right. 
      destruct IHhas_type1. auto. auto. auto. auto. auto. 
       + inversion H4. 
          (* case analysis for argument: if the argument is a value *)
             destruct IHhas_type2. auto. auto. auto. auto. auto. subst.
            assert (exists fieldsMap lb, lookup_heap_obj h o = Some (Heap_OBJ cls_def fieldsMap lb)).
            remember (SIGMA s h ) as sigma.
            apply wfe_oid with (o:=o) (ct:=CT) (gamma:=empty_context) (s:=s) (h:=h) 
                          (sigma:=sigma) (cls_def:=cls_def) (cn:=clsT). auto. auto. auto. auto. auto.
            destruct H as [F]. destruct H as [lb]. 
            remember (SIGMA s h ) as sigma.
            remember (join_label lb (current_label sigma)) as l'. 
            remember (fields_update F f e) as F'. 
            remember (update_heap_obj h o (Heap_OBJ cls_def F' l')) as h'.
            remember (SIGMA s h') as sigma'.
            exists (Config CT Skip sigma').
            apply ST_fieldWrite3 with (sigma:=sigma) (sigma':=sigma') (o:=o) (s:=s) (h:=h) (h':=h') (f:=f) 
                                                      (lb:=lb) (cls:=cls_def) (F:=F) (F':=F') (v:=e) (l':=l').
            auto. auto. auto. auto. auto. auto.  auto.
            
          (* case analysis for argument, if the argument is not a value *)
            subst. 
                destruct H6 as [config'].
                pose proof (excluded_middle_opaqueLabel e).
                destruct H5.
                  (* case for e = unlabelOpaque t *)
                  destruct H5 as [t]. 
                  rewrite -> H5 in H. inversion H. subst. 
                  exists (Config CT (FieldWrite (ObjId o) f (unlabelOpaque e')) sigma').
                  apply ST_fieldWrite2 with (sigma:=(SIGMA s h)) (sigma':=sigma') 
                                            (v:=(ObjId o)) (e2:=unlabelOpaque t) (e2':=unlabelOpaque e') (f:=f).
                  intros. subst. intro contra. inversion contra.  rewrite H8 in H10. 
                  inversion H5. 
                  rewrite <- H7 in H10.  inversion H10.                   rewrite <- H7 in H10.  inversion H10. 
                  rewrite <- H7 in H10.  inversion H10.                   rewrite <- H7 in H10.  inversion H10. 
                  rewrite <- H9 in H10.  inversion H10.                   rewrite <- H9 in H10.  inversion H10. 
                  auto. auto. 

                  exists Error_state. subst. apply ST_fieldWrite_ctx_error2 
                        with (sigma:=(SIGMA s h)) (f:=f) (v:=(ObjId o)) (e2:=(unlabelOpaque t)).

                  intros. intro contra. inversion contra. rewrite H8 in H10. inversion H5. 
                  rewrite <- H7 in H10.  inversion H10.                   rewrite <- H7 in H10.  inversion H10. 
                  rewrite <- H7 in H10.  inversion H10.                   rewrite <- H7 in H10.  inversion H10. 
                  rewrite <- H9 in H10.  inversion H10.                   rewrite <- H9 in H10.  inversion H10. 
                  auto. auto. 

                  assert (exists fieldsMap lb, lookup_heap_obj h o = Some (Heap_OBJ cls_def fieldsMap lb)).
                      apply wfe_oid with (o:=o) (ct:=CT) (gamma:=empty_context) (s:=s) (h:=h) 
                                    (sigma:=sigma) (cls_def:=cls_def) (cn:=clsT). auto. auto. auto. auto. auto.
                      destruct H14 as [F]. destruct H14 as [lo]. 
                      remember (fields_update F f v) as F'. 
                      remember (join_label lo lb) as l''. 
                      remember (update_heap_obj h o (Heap_OBJ cls_def F' l'')) as h'.
                      remember (SIGMA s h') as sigma''.

                      exists (Config CT Skip sigma'').
                      apply ST_fieldWrite_opaque with (sigma:=(SIGMA s h)) (sigma':=sigma'') (o:=o) (s:=s) (h:=h) (h':=h') (f:=f) 
                                                      (lb:=lb) (lo:=lo) (cls:=cls_def) (F:=F) (F':=F') (v:=v) (l':=l'') (e2:=e).
                      rewrite <- H7 in H5. auto. auto. auto. auto. auto. auto.  auto.

                      rewrite H5 in H2_0. inversion H2_0. rewrite <-H7 in H19. inversion H19. auto. 

                      exists Error_state. 

                      apply ST_fieldWrite_ctx_error2 with (sigma:=(SIGMA s h)) (f:=f) (v:=(ObjId o)) (e2:=e).
                       intros. rewrite H5. intro contra. inversion contra. rewrite <- H13 in H10.
                      rewrite H8 in H11. auto. auto. subst. auto.   

                  (* case for argu <> unlabelOpaque t *)
                  destruct config'. 
                  exists (Config CT (FieldWrite (ObjId o) f t) s0). 
                  apply ST_fieldWrite2 with (sigma:=(SIGMA s h)) (sigma':=s0) (v:=((ObjId o))) 
                                            (e2:=e) (e2':=t) (f:=f).
                  intros. apply H5. apply v_oid. 
                  assert (CT = c). apply ct_consist with (t:=e) (t':=t) (sigma:=(SIGMA s h)) (sigma':=s0); auto. 
                    rewrite <- H6 in H. auto.  

                  exists Error_state. 
                      apply ST_fieldWrite_ctx_error2 with (sigma:=(SIGMA s h)) (f:=f) (v:=(ObjId o)) (e2:=e).
                       intros. apply H5.  auto. auto. 
     
                  destruct  IHhas_type2.  auto. auto. auto. auto.  
                  rewrite <- H5 in H2_. inversion H2_.                   rewrite <- H5 in H2_. inversion H2_.
                  rewrite <- H5 in H2_. inversion H2_.
                  exists Error_state.
                  apply ST_fieldWriteException with (sigma:=sigma) (f:=f) (v:=e). 

                  rewrite <- H5 in H2_. inversion H2_.                   rewrite <- H6 in H2_. inversion H2_.
                  rewrite <- H6 in H2_. inversion H2_.       


          +    destruct H4 as [config'].
                 destruct config'. 
                  exists (Config CT (FieldWrite t f e) (s0)). 
                  apply ST_fieldWrite1 with (sigma:=sigma) (sigma':=s0) (f:=f) (e1:=x) (e1':=t) (e2:=e).
                  assert (CT = c). apply ct_consist with (t:=x) (t':=t) (sigma:=sigma) (sigma':=s0); auto. 
                    rewrite <- H5 in H4. auto.  
        
              exists Error_state. 
              apply ST_fieldWrite_ctx_error1 with (sigma:=sigma) (f:=f) (e1:=x) (e2:=e). auto. 

(* if *)
- inversion H2_0. inversion H7.
(* sequence *)
- right. destruct IHhas_type1; auto.
    exists (Config CT e2 sigma).
   
   apply ST_seq2 with (sigma:=sigma) (v:=e1) (s:=e2); auto.
  
  destruct H2 as [config'].
  destruct config'.
  exists (Config CT (Sequence t e2) s0). 
   apply ST_seq1 with (sigma:=sigma) (s1:=e1) (s2:=e2) (s1':=t); auto.
   assert (CT = c). apply ct_consist with (t:=e1) (t':=t) (sigma:=sigma) (sigma':=s0); auto. 
                  rewrite <- H3 in H2. auto. 

  exists Error_state. apply ST_seq_ctx_error with (sigma:=sigma) (s1:=e1) (s2:=e2).
  auto. 

(* return e *)
- right. destruct IHhas_type; auto.
  assert (exists lsf s', s = cons lsf s'). 
  apply stack_not_nil with (sigma:=sigma) (CT:=CT) (s:=s) (h:=h).
  auto. auto. auto.
  destruct H5 as [lsf0]. destruct H5 as [s0].
  remember (join_label (get_current_label s) (get_current_label s0)) as l'.
  remember (update_current_label s0 l' ) as s''.
  remember (SIGMA s'' h) as sigma'.

destruct s0.
exists Error_state. 
  apply ST_return_terminal with (s:=s) (h:=h) (lsf:=lsf0); auto.

exists (Config CT e sigma').
  apply ST_return2 with (sigma:=sigma) (sigma':=sigma') (v:=e)
                                    (s:=s) (s':=(l :: s0)) (s'':=s'') (h:=h) (lsf:=lsf0) (l':=l').
  auto. auto. auto. intuition. inversion H6. auto. auto. auto. 
  
destruct H4 as [config'].
  destruct config'. 
  exists (Config CT (Return t) s0). 
  apply ST_return1 with (sigma:=sigma) (sigma':=s0) (e:=e) (e':=t). 

  assert (CT = c). apply ct_consist with (t:=e) (t':=t) (sigma:=sigma) (sigma':=s0); auto. 
                  rewrite <- H5 in H4. auto. 
  auto.

  exists Error_state. apply ST_return_ctx_error with (sigma:=sigma) (e:=e). auto. 

(* ObjId o *)
- left. apply v_oid. 

(* v_l *)
- left. apply v_labeled. auto.  

(* v_opl_l *)
- left. apply v_opa_labeled. auto.
Qed.

Theorem preservation : forall CT s s' h h' sigma sigma',
    field_wfe_heap CT h -> sigma = SIGMA s h ->  
    wfe_heap CT h -> wfe_stack CT h s -> sigma' = SIGMA s' h' -> 
    forall t T, has_type CT empty_context h t T -> 
     forall t',  Config CT t sigma ==> Config CT t' sigma' ->
     ( has_type CT empty_context h' t' T) .
Proof with auto.
   intros CT s s' h h' sigma sigma'. intro H_field_wfe. 
  intro H_sigma. intro H_wfe_heap. intro H_wfe_stack. intro H_sigma'.
  induction t. (*induction on the terms *)
  (* (Tvar i) *)
  + intro T. intro typing. intro t'.  intro step.
        inversion step.   inversion typing. subst.   inversion H12.
  (* null *)
  + intro T. intro typing. intro t'.  intro step.
        inversion step.  

  (* field access *)
  + intro T'. intro typing. intro t'. inversion typing. intro step. 
     inversion step. subst. apply T_FieldAccess with (Gamma:=empty_context) (e:=e') (f:=i) 
            (cls_def:=cls_def) (CT:=CT) (clsT:=clsT) (cls':=cls') (h:=h') 
            (fields_def:=(find_fields cls_def)). apply IHt. 
             auto. auto. auto. auto. auto.

   assert (wfe_heap CT h' /\ wfe_stack CT h' s' /\ field_wfe_heap CT h').
   apply reduction_preserve_wfe with (t:=(FieldAccess t i)) (t':=t') (T:=T')  (sigma:=sigma) (sigma':=sigma')
           (CT:=CT) (s:=s) (s':=s') (h:=h) (h':=h').
   auto. auto. auto. auto. auto. auto. auto.

   rewrite <- H10 in H1. inversion H1. 

   destruct H28 as [field_defs]. destruct H28 as [method_defs].
      assert (v = null \/
             (exists
                (o' : oid) (field_defs0 : list field) (method_defs0 : 
                                                       list method_def) 
              (field_cls_def : CLASS) (F' : FieldMap) (lo : Label),
                v = ObjId o' /\
                field_cls_def =
                class_def cls' field_defs0 method_defs0 /\
                lookup_heap_obj h' o'  = Some (Heap_OBJ field_cls_def F' lo) /\
                CT cls' = Some field_cls_def)
      ).

    apply field_consist_typing with (CT:=CT)  (v:=v) (h:=h') (o:=o) (cls_def:=cls)
             (F:=fields) (f:=i) (lb:=lb) (field_cls_name:=cls') (cls_name:=cls_name) 
             (field_defs:=field_defs) (method_defs:=method_defs).
    apply H21. apply H21. rewrite H_sigma' in H20. inversion H20. auto. subst. 
    inversion H15. rewrite <- H3 in H16. rewrite <- H16 in H29.
    destruct H29 as [F0]. destruct H as [lo0]. inversion H. auto.  
    rewrite <- H2 in H24. inversion H24. rewrite <- H31 in H6.
    rewrite H28 in H6. unfold find_fields in H6.
    rewrite <- H6. auto. subst. auto. 

    destruct H30. 
    subst. apply T_null with (Gamma:=empty_context) (h:=h') (T:=(classTy cls')) (CT:=CT). 

    destruct H30 as [o']. destruct H30 as [field_defs0]. destruct H30 as [method_defs0]. 
    destruct H30 as [field_cls_def]. destruct H30 as [F']. destruct H30 as [lx]. 
    destruct H30. subst. destruct H31. destruct H0. 


    apply T_ObjId with (h:=h') (Gamma:=empty_context) (CT:=CT) (cls_name:=cls') 
                                  (cls_def:=field_cls_def) (o:=o').

     auto. auto.  
     exists field_defs0. exists method_defs0. auto. 
    exists  F'. exists lx. auto. 

  (* MethodCall  *)
    + intro T'. intro typing. intro t'. inversion typing. intro step. 
        inversion step. 
      (* reduction on the object  *)
        - apply T_MethodCall with (Gamma:=empty_context) (e:=e') (meth:=i) (argu:=t2)
                            ( CT:=CT) (h:=h') (T:=T) (returnT:=returnT) (cls_def:=cls_def)
                            (body:=body) (arg_id:=arg_id) (arguT:=arguT) (Gamma':=Gamma').

      apply IHt1; auto. 

      apply heap_preserve_typing with (h:=h).
      intros o cls_def0 F lo. intro.  

      apply reduction_preserve_heap_pointer with (t:=t1) (s:=s) (s':=s') (h:=h) (h':=h')
                             (CT:=CT) (gamma:=empty_context) (T:=(classTy T))
                              (t':=e') (F:=F) (lo:=lo); auto.
     rewrite <- H_sigma. rewrite <-H_sigma'.
      auto.  auto. auto. auto. auto. auto. auto.
      apply heap_preserve_typing with (h:=h).
      intros o cls_def0 F lo. intro.  
      apply reduction_preserve_heap_pointer with (t:=t1) (s:=s) (s':=s') (h:=h) (h':=h')
                             (CT:=CT) (gamma:=empty_context) (T:=(classTy T))
                              (t':=e') (F:=F) (lo:=lo); auto. 
     rewrite <- H_sigma. rewrite <-H_sigma'.
      auto.  auto. 
      apply heap_preserve_typing with (h:=h).
      intros o cls_def0 F lo. intro.  
      apply reduction_preserve_heap_pointer with (t:=t1) (s:=s) (s':=s') (h:=h) (h':=h')
                                   (CT:=CT) (gamma:=empty_context) (T:=(classTy T))
                                    (t':=e') (F:=F) (lo:=lo); auto. 
     rewrite <- H_sigma. rewrite <-H_sigma'.  auto.  auto.

      (* reduction on the argument  *)
        -  apply T_MethodCall with (Gamma:=empty_context) (e:=t1) (meth:=i) (argu:=e')
                    ( CT:=CT) (h:=h') (T:=T) (returnT:=returnT) (cls_def:=cls_def)
                            (body:=body) (arg_id:=arg_id) (arguT:=arguT) (Gamma':=Gamma').
          apply heap_preserve_typing with (h:=h).
          intros o cls_def0 F lo. intro. 

          apply reduction_preserve_heap_pointer with (t:=t2) (s:=s) (s':=s') (h:=h) (h':=h')
                                 (CT:=CT) (gamma:=empty_context) (T:=classTy arguT)
                                  (t':=e') (F:=F) (lo:=lo); auto. 
         rewrite <- H_sigma. rewrite <-H_sigma'.
          auto.  auto. auto. auto. auto. auto. auto.

          apply heap_preserve_typing with (h:=h).
          intros o cls_def0 F lo. intro. 

          apply reduction_preserve_heap_pointer with (t:=t2) (s:=s) (s':=s') (h:=h) (h':=h')
                                 (CT:=CT) (gamma:=empty_context) (T:=classTy arguT)
                                  (t':=e') (F:=F) (lo:=lo); auto. 
         rewrite <- H_sigma. rewrite <-H_sigma'. auto.  auto. 

apply heap_preserve_typing with (h:=h).
          intros o cls_def0 F lo. intro. 

          apply reduction_preserve_heap_pointer with (t:=t2) (s:=s) (s':=s') (h:=h) (h':=h')
                                 (CT:=CT) (gamma:=empty_context) (T:=classTy arguT)
                                  (t':=e') (F:=F) (lo:=lo); auto. 
         rewrite <- H_sigma. rewrite <-H_sigma'. auto.  auto. 

      (* normal return  *)
          -  apply heap_preserve_typing with (h:=h).
          intros o0 cls_def0 F0 lo0. intro. 

          apply reduction_preserve_heap_pointer with (t:=(MethodCall t1 i t2)) (s:=s) (s':=s') (h:=h) (h':=h')
                                 (CT:=CT) (gamma:=empty_context) (T:=T')
                                  (t':=t') (F:=F0) (lo:=lo0); auto. 
         rewrite <- H_sigma. rewrite <-H_sigma'. auto. subst.  auto.
          inversion H2. inversion H20. destruct H10 as [F']. destruct H10 as [lo'].
         rewrite H15 in H10. rewrite H10 in H21. inversion H21. rewrite <- H16 in H1. 
          rewrite <- H1 in H4. inversion H4. rewrite <- H19 in H22. rewrite H5 in H22. 
          inversion H22.  rewrite <- H15. auto.  
      (* opaque return  *)
      - subst. apply heap_preserve_typing with (h:=h).
          intros o0 cls_def0 F0 lo0. intro. 

          apply reduction_preserve_heap_pointer with 
                    (t:=(MethodCall (ObjId o) i (unlabelOpaque (v_opa_l v lb))))
                     (s:=s) (s':=s') (h:=h) (h':=h')
                                 (CT:=CT) (gamma:=empty_context) (T:= (classTy returnT))
                                  (t':=(Return body0)) (F:=F0) (lo:=lo0); auto. 

          inversion H2. inversion H20. destruct H10 as [F']. destruct H10 as [lo'].
         rewrite H15 in H10. rewrite H10 in H21. inversion H21. rewrite <- H16 in H1. 
          rewrite <- H1 in H4. inversion H4. rewrite <- H19 in H27. rewrite H5 in H27. 
          inversion H27.  rewrite <- H15. auto.

(* new expression  *)
    + intro T. intro typing. intro t'.  intro step. 
   assert (wfe_heap CT h' /\ wfe_stack CT h' s' /\ field_wfe_heap CT h').
   apply reduction_preserve_wfe with (t:=(NewExp c)) (t':=t') (T:=T)  (sigma:=sigma)
           (sigma':=sigma') (CT:=CT) (s:=s) (s':=s') (h:=h) (h':=h').
   auto. auto. auto. auto. auto. auto. auto.   
      inversion step. inversion typing. 
      apply T_ObjId with (h:=h') (Gamma:=empty_context) (CT:=CT) (o:=o)
                (cls_name:=c) (cls_def:=cls). 
      assert (lookup_heap_obj h' o = Some (Heap_OBJ cls F lb)).
      rewrite H_sigma' in H12.       inversion H12.  rewrite H11.       unfold add_heap_obj. 
      assert (beq_oid o o = true). apply beq_oid_same.
      unfold lookup_heap_obj. rewrite H19. auto.
      assert (exists cls_name field_defs method_defs, 
                CT cls_name = Some cls /\ cls = (class_def cls_name field_defs method_defs)).
      apply heap_consist_ct with (h:=h') (o:=o)(F:=F) (lo:=lb).
      apply H. auto. auto. exists field_defs. exists method_defs.  auto.

      rewrite H_sigma' in H12.       inversion H12.  rewrite H11.       unfold add_heap_obj. 
      assert (beq_oid o o = true). apply beq_oid_same.
     unfold lookup_heap_obj. rewrite H19. auto.
      exists F. exists lb. auto.

(* Label  *)
    + intro T. intro typing. intro t'.  intro step. 
       inversion step. 
 
(* label data *)
    + intro T. intro typing. intro t'.  intro step.
        inversion step.   inversion typing.
        apply T_labelData with (h:=h') (Gamma:=empty_context) (lb:=l) (CT:=CT) (e:=e') (T:=T0).
        apply T_label. apply IHt; auto. inversion typing.
        apply T_v_l with (h:=h') (Gamma:=empty_context) (lb:=l) (CT:=CT) (v:=t) (T:=T0).
        apply T_label. 
        apply heap_preserve_typing with (h:=h).
          intros o0 cls_def0 F0 lo0. intro. 
        apply reduction_preserve_heap_pointer with 
                    (t:=(labelData t l))
                     (s:=s) (s':=s') (h:=h) (h':=h')
                                 (CT:=CT) (gamma:=empty_context) (T:= T)
                                  (t':=t') (F:=F0) (lo:=lo0); auto.
        rewrite <- H_sigma.         rewrite <- H_sigma'. auto. auto. auto.

(* unlabel *)
    + intro T. intro typing. intro t'.  intro step.
        inversion step.   inversion typing.
        apply T_unlabel. apply IHt. auto. auto.
        inversion typing. rewrite <- H0 in H13. inversion H13. 
        apply heap_preserve_typing with (h:=h).
          intros o0 cls_def0 F0 lo0. intro. 
        apply reduction_preserve_heap_pointer with 
                    (t:=(unlabel t) )
                     (s:=s) (s':=s') (h:=h) (h':=h')
                                 (CT:=CT) (gamma:=empty_context) (T:= T)
                                  (t':=t') (F:=F0) (lo:=lo0); auto.
         rewrite <- H_sigma.         rewrite <- H_sigma'. auto.
        rewrite <- H2. auto.

(* Label of  *)
   + intro T. intro typing. intro t'.  intro step.
        inversion step.   inversion typing.
        apply T_labelOf with (T:=T0).  apply IHt. auto. auto. 
        inversion typing. apply T_label.

(* unlabelopaque  *)
   + intro T. intro typing. intro t'.  intro step.
        inversion step.   inversion typing.
        apply T_unlabelOpaque. apply IHt. auto. auto.
        inversion typing. rewrite <- H0 in H12. inversion H12. rewrite <- H2.  
        apply heap_preserve_typing with (h:=h).
          intros o0 cls_def0 F0 lo0. intro. 
        apply reduction_preserve_heap_pointer with 
                    (t:=(unlabelOpaque t) )
                     (s:=s) (s':=s') (h:=h) (h':=h')
                                 (CT:=CT) (gamma:=empty_context) (T:= T)
                                  (t':=t') (F:=F0) (lo:=lo0); auto.
         rewrite <- H_sigma.         rewrite <- H_sigma'. auto. auto. 

(* opaque call  *)
   +  intro T. intro typing. intro t'.  intro step.
        inversion step.   inversion typing.
        apply T_opaqueCall. apply IHt. auto. auto.
        inversion typing. 
              apply T_opaqueCall. apply IHt. auto. rewrite <- H1. 
        apply ST_return1. auto.
        inversion typing.  apply T_v_opa_l. apply T_label.
        apply heap_preserve_typing with (h:=h).
          intros o0 cls_def0 F0 lo0. intro. 
        apply reduction_preserve_heap_pointer with 
                    (t:=(opaqueCall t) )
                     (s:=s) (s':=s') (h:=h) (h':=h')
                                 (CT:=CT) (gamma:=empty_context) (T:= T)
                                  (t':=t') (F:=F0) (lo:=lo0); auto.
      rewrite <- H_sigma.         rewrite <- H_sigma'. auto. auto. auto.  

        inversion typing. auto. inversion typing.  apply T_v_opa_l. apply T_label.
        apply heap_preserve_typing with (h:=h).
          intros o0 cls_def0 F0 lo0. intro. 
        apply reduction_preserve_heap_pointer with 
                    (t:=(opaqueCall t) )
                     (s:=s) (s':=s') (h:=h) (h':=h')
                                 (CT:=CT) (gamma:=empty_context) (T:= T)
                                  (t':=t') (F:=F0) (lo:=lo0); auto.
      rewrite <- H_sigma.         rewrite <- H_sigma'. auto. auto.
        rewrite <- H0 in H14. inversion H14. 
        apply value_typing_invariant_gamma with (gamma:=empty_context).
        auto. auto. auto. 

(* skip  *)
   + intro T. intro typing. intro t'.  intro step.
        inversion step.  

(* assignment  *)
   + intro T. intro typing. intro t'.  intro step.
        inversion step.    inversion typing.
        apply T_assignment with (T:=T0); auto.
        inversion typing.
        apply T_skip with (Gamma:=empty_context)(CT:=CT)  (h:=h').

(* field write  *)
   + intro T. intro typing. intro t'.  intro step.
        inversion step.    inversion typing.
        apply T_FieldWrite with (cls_def:=cls_def) (clsT:=clsT) (cls':=cls'). 
        apply IHt1. auto. auto.  
        apply heap_preserve_typing with (h:=h).
          intros o0 cls_def0 F0 lo0. intro. 
        apply reduction_preserve_heap_pointer with 
                    (t:=(FieldWrite t1 i t2) )
                     (s:=s) (s':=s') (h:=h) (h':=h')
                                 (CT:=CT) (gamma:=empty_context) (T:= T)
                                  (t':=t') (F:=F0) (lo:=lo0); auto.
       rewrite <- H_sigma.         rewrite <- H_sigma'. auto. auto. auto. auto.  
        
        inversion typing. 
        apply T_FieldWrite with (cls_def:=cls_def) (clsT:=clsT) (cls':=cls'). 
        
        apply heap_preserve_typing with (h:=h).
          intros o0 cls_def0 F0 lo0. intro. 
        apply reduction_preserve_heap_pointer with 
                    (t:=(FieldWrite t1 i t2) )
                     (s:=s) (s':=s') (h:=h) (h':=h')
                                 (CT:=CT) (gamma:=empty_context) (T:= T)
                                  (t':=t') (F:=F0) (lo:=lo0); auto.
        rewrite <- H_sigma.         rewrite <- H_sigma'. auto. auto. auto. auto. auto. 

        inversion typing. apply T_skip.         inversion typing. apply T_skip.

(* if statement  *)
   + intro T. intro typing. intro t'.  intro step.
        inversion step. 
        inversion typing. inversion H20. inversion H28.
        inversion typing. inversion H20. inversion H28.

(* sequence *)
   + intro T. intro typing. intro t'.  intro step.
        inversion step. 
        inversion typing. 
        apply T_sequence with (T:=T0) (T':=T). 
        apply IHt1. auto. auto.
        apply heap_preserve_typing with (h:=h).
          intros o0 cls_def0 F0 lo0. intro. 
        apply reduction_preserve_heap_pointer with 
                    (t:=(Sequence t1 t2)  )
                     (s:=s) (s':=s') (h:=h) (h':=h')
                                 (CT:=CT) (gamma:=empty_context) (T:= T)
                                  (t':=t') (F:=F0) (lo:=lo0); auto.
        rewrite <- H_sigma.         rewrite <- H_sigma'. auto. auto.

        inversion typing. rewrite <- H4.  
        apply heap_preserve_typing with (h:=h).
          intros o0 cls_def0 F0 lo0. intro. 
        apply reduction_preserve_heap_pointer with 
                    (t:=(Sequence t1 t2)  )
                     (s:=s) (s':=s') (h:=h) (h':=h')
                                 (CT:=CT) (gamma:=empty_context) (T:= T)
                                  (t':=t') (F:=F0) (lo:=lo0); auto.
        rewrite <- H_sigma.         rewrite <- H_sigma'. auto. auto.

(* return   *)
   + intro T. intro typing. intro t'.  intro step.
        inversion step. 
        inversion typing. 
        apply T_return; auto. 
        inversion typing. auto.  rewrite <- H2. 
        apply heap_preserve_typing with (h:=h).
          intros o0 cls_def0 F0 lo0. intro. 
        apply reduction_preserve_heap_pointer with 
                    (t:=(Return t) )
                     (s:=s) (s':=s') (h:=h) (h':=h')
                                 (CT:=CT) (gamma:=empty_context) (T:= T)
                                  (t':=t') (F:=F0) (lo:=lo0); auto.
        rewrite <- H_sigma.         rewrite <- H_sigma'. auto. auto.

(* objId *)
     + intro T. intro typing. intro t'.  intro step.
        inversion step. 

(* runtime labeled data *)
     + intro T. intro typing. intro t'.  intro step.
        inversion step. 
(* runtime opaque labeled data *)
     + intro T. intro typing. intro t'.  intro step.
        inversion step. 
Qed. 

Inductive multi_step_reduction : config -> config -> Prop := 
  | multi_reduction_refl : forall config , multi_step_reduction config config
  | multi_reduction_step : forall c1 c2 c3, 
                    reduction c1 c2 ->
                    multi_step_reduction c2 c3 ->
                    multi_step_reduction c1 c3.

Inductive multi_step : Class_table -> tm -> Sigma -> Class_table-> tm -> Sigma -> Prop := 
  | multi_refl : forall t ct sigma , multi_step ct t sigma ct t sigma
  | multi_reduction : forall t1 t2 t3 sigma1 sigma2 sigma3 ct, 
                    reduction (Config ct t1 sigma1) (Config ct t2 sigma2) ->
                    multi_step ct t2 sigma2 ct t3 sigma3 ->
                    multi_step ct t1 sigma1 ct t3 sigma3.

Notation "c1 '==>*' c2" := (multi_step_reduction c1 c2) (at level 40).


Theorem soundness : forall CT,
    forall sigma s h, sigma = SIGMA s h ->  
      wfe_heap CT h -> wfe_stack CT h s -> field_wfe_heap CT h ->
    forall t s' h' t',  multi_step CT t sigma CT t' (SIGMA s' h')  ->
    forall T, has_type CT empty_context h t T -> 
     value t' \/ (exists config', Config CT t' (SIGMA s' h') ==> config').
Proof with auto. 
  intros CT sigma s h.  intro. intro. intro. intro. intros t s' h' t'.
  intro multiH. 

generalize dependent s.  generalize dependent h. 
  induction multiH.
  + intro h. intro well_heap. intro well_fields. intro s. intro sigmaH. intro well_stack. intro T. 
     intro typing. apply progress with  (T:=T) (CT:=ct)  (s:=s) (h:=h); auto.
  + intro h1. intro well_heap. intro well_fields. intro s1. intro. intro well_stack. intro T. intro typing. 
      induction sigma2.  
      assert (wfe_heap ct h /\ wfe_stack ct h s /\  field_wfe_heap ct h).
      apply reduction_preserve_wfe with (t:=t1) (t':=t2) 
              (sigma:=sigma1) (sigma':=(SIGMA s h)) (CT:=ct)
              (s:=s1) (s':=s) (h:=h1) (h':=h) (T:=T).
      auto. auto.       auto. auto.       auto. auto. auto. 
      destruct IHmultiH with (h0:=h) (s0:=s) (T:=T).
      apply H1. apply H1.  auto. apply H1. 
      apply preservation with  (CT:=ct) (s:=s1) (s':=s) 
                    (h:=h1) (h':=h) (sigma:=sigma1) (sigma':= (SIGMA s h)) (t:=t1).
      auto.       auto.       auto.       auto.       auto.       auto. auto.  
      left. auto. right. auto.
Qed.

Lemma normal_form : forall v sigma ct, value v->
(~exists v' sigma', Config ct v sigma ==> Config ct v' sigma').
Proof. 
  intros v sigma ct. intro H_v. intro contra. 
  destruct contra as [v']. destruct H as [sigma']. 
  inversion H_v; try (rewrite <-H0 in H; inversion H; fail); 
  try (rewrite <-H1 in H; inversion H).
Qed. 

Lemma normal_form_prime : forall v sigma ct, value v->
(forall v' sigma', Config ct v sigma ==> Config ct v' sigma' -> False).
Proof. 
  intros v sigma ct. intro H_v. intros.
  inversion H_v; try (rewrite <-H0 in H; inversion H; fail); 
  try (rewrite <-H1 in H; inversion H).
Qed.

Theorem deterministic: forall ct t sigma t1 sigma1 t2 sigma2, 
     reduction (Config ct t sigma) (Config ct t1 sigma1) ->
     reduction (Config ct t sigma) (Config ct t2 sigma2) -> 
      t1 = t2 /\ sigma1 = sigma2. 
Proof.
     intros ct t sigma t1 sigma1 t2 sigma2 Hy1 Hy2.

     remember (Config ct t1 sigma1) as t1_config. 
     generalize dependent t2.      generalize dependent t1.
     induction Hy1; intro t1; intro; intro t2; intro Hy2; inversion Heqt1_config; subst.
      (*Tvar *)
     - inversion Hy2. subst. inversion H5. rewrite <- H1 in H8. rewrite <- H2 in H8.
        inversion H8.
          split. auto. auto. 
     (*field access*)
    - inversion Hy2. subst. destruct IHHy1 with e' e'0. subst.
       auto. auto. subst. auto.
       subst. inversion Hy1.  
    - inversion Hy2. subst. inversion H2.
      subst. inversion H7. rewrite <- H3 in H8. rewrite <- H8 in H0. inversion H0.
       subst. rewrite <- H1 in H9.  inversion H9.  split; auto.
    - inversion Hy2. subst.  destruct IHHy1 with e' e'0; auto. split; subst; auto.
       subst. apply normal_form_prime in Hy1. intuition. auto.
        
       subst.  inversion Hy1. subst. inversion Hy1.
    - inversion Hy2. 
          subst. apply normal_form_prime in H2. intuition. auto.
          subst. destruct IHHy1 with e' e'0; auto. split; auto. rewrite H1. auto.
          subst. apply normal_form_prime in Hy1. intuition. auto.
          subst. destruct H with (v_opa_l v0 lb). apply v_opa_labeled. auto.
                intuition. inversion H1. auto.
    - inversion Hy2.
          subst. inversion H3. 
          subst. apply normal_form_prime in H10. intuition. auto.
          subst. inversion H9. rewrite <- H4 in H10. rewrite <-H10 in H0.
              inversion H0. rewrite <- H5 in H11. rewrite <-H11 in H1. 
              inversion H1. subst. auto.
          subst.  inversion H9. rewrite <- H4 in H10. rewrite <-H10 in H0.
              inversion H0. rewrite <- H5 in H16. rewrite <-H16 in H1. 
              inversion H1. subst. auto. inversion H2. 
    - inversion Hy2. 
          subst. inversion H1.
          subst. destruct H3 with  (v_opa_l v lb).  apply v_opa_labeled; auto. 
              intuition. inversion H. auto.
          subst. inversion H12. 
          subst. inversion H10. rewrite <- H2 in H11. rewrite <- H11 in H0.
              inversion H0. rewrite <- H3 in H17. rewrite <- H17 in H6. 
              inversion H6.  subst. auto.
      - inversion Hy2. 
          subst. inversion H6. rewrite H5 in H. inversion H. subst.  auto.
      - inversion Hy2. 
          subst. destruct IHHy1 with  e' e'0; auto. rewrite H. auto.
          subst. apply normal_form_prime in Hy1. intuition. auto.
      - inversion Hy2. 
          subst. apply normal_form_prime in H1. intuition. auto. auto.
      - inversion Hy2.
          subst. destruct IHHy1 with  e' e'0; auto. rewrite H. auto.
          subst. inversion Hy1.
      - inversion Hy2.
          subst. inversion H0. 
          subst.  inversion H6. subst. auto.
      - inversion Hy2.
          subst. destruct IHHy1 with  e' e'0; auto.  rewrite H. auto.
          subst. inversion Hy1.
      - inversion Hy2. 
          subst.  inversion H0. 
          subst.  auto.
      - inversion Hy2.
          subst.  destruct IHHy1 with  e' e'0; auto.  rewrite H. auto.
          subst. inversion Hy1.
      - inversion Hy2.
          subst. inversion H0.
          subst. inversion H4. rewrite <-H0. auto.
      - inversion Hy2.
          subst. destruct IHHy1 with  e' e'0; auto.  rewrite H0. auto.
          subst. destruct IHHy1 with e' (Return e'0); auto.
              apply ST_return1 in H1. auto. 
          subst.  auto.
          subst. apply normal_form_prime in Hy1. intuition. auto.
          subst. destruct H with v; auto.
      - inversion Hy2.
          subst. inversion H5. subst.
              destruct IHHy1 with  e' e'1; auto.  
              apply ST_return1 in H0. rewrite <- H. auto.
          subst.   apply normal_form_prime in Hy1. intuition. auto.
          subst. destruct IHHy1 with e' e'0; auto. rewrite H. auto.
          subst. inversion H1.
          subst.  apply normal_form_prime in Hy1. intuition. auto.
       - inversion Hy2.
          subst.   apply normal_form_prime in H6. intuition. auto.
          subst. inversion H.
          subst. auto.
          subst. inversion H.
       - inversion Hy2.
          subst. destruct H2 with v. auto. auto.
          subst.  apply normal_form_prime in H0. intuition. auto.
          subst. inversion H2.
          subst. inversion H6. subst. auto.
       - inversion Hy2.
          subst. destruct IHHy1 with e' e'0; auto. rewrite H. auto.
          subst.  apply normal_form_prime in Hy1. intuition. auto.
       - inversion Hy2.
          subst. apply normal_form_prime in H1. intuition. auto.
          subst.  inversion H7. auto.
       - inversion Hy2.   
          subst. destruct IHHy1 with e1' e1'0; auto. rewrite H. auto.
          subst. apply normal_form_prime in Hy1. intuition. auto.
          subst. inversion Hy1.
          subst. inversion Hy1.
       - inversion Hy2.
          subst. apply normal_form_prime in H2. intuition. auto.
          subst. destruct IHHy1 with e2' e2'0; auto. rewrite H1. auto.
          subst. apply normal_form_prime in Hy1. intuition. auto.
          subst. destruct H with (v_opa_l v0 lb).
              apply v_opa_labeled. auto. intuition. inversion H1.
          subst.  auto.
       - inversion Hy2.
          subst. inversion H1.
          subst. apply normal_form_prime in H10. intuition. auto.
          subst. inversion H8. subst. rewrite <-H9 in H0. inversion H0.
              subst. auto.
          subst. inversion H5.
      - inversion Hy2.
          subst. inversion H0.
          subst.  destruct H3 with (v_opa_l v lb).
              apply v_opa_labeled. auto. intuition. inversion H.
          subst. auto.
          subst. inversion H14.
          subst. inversion H9. subst. rewrite <- H10 in H1. 
            inversion H1. inversion H8. subst. auto.
      - inversion Hy2. 
          subst.  destruct IHHy1 with e' e'0; auto. rewrite H. auto.
          subst. apply normal_form_prime in Hy1. intuition. auto. 
      - inversion Hy2. 
          subst. apply normal_form_prime in H1.  intuition. auto. 
          subst. inversion H7. auto. 
      - inversion Hy2.
          subst. auto. 
          subst. inversion H2.  inversion H4. subst. intuition. 
      - inversion Hy2. 
          subst. inversion H11. inversion H4. subst. intuition. 
          subst. inversion H4. subst. auto. 
      - inversion Hy2. 
          subst. destruct IHHy1 with s1' s1'0; auto. rewrite H. auto.
          subst. apply normal_form_prime in Hy1.  intuition. auto.
      - inversion Hy2. 
          subst. apply normal_form_prime in H1.  intuition. auto.
          subst. auto. 
Qed. 


