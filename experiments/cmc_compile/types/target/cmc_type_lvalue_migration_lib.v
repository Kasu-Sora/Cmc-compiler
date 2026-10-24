Require Export SimpleC.EE.QCP_demos_human.cmc_type_expr_access_migration_lib.
Require Export SimpleC.EE.QCP_demos_human.cmc_type_expr_unary_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_lvalue_result_type_ready policy nilslot p fid ty cursors v :
 cm_cursor_head_lvalue_type_ready policy nilslot p fid ty cursors -> cm_value_type_compatible v ty -> cm_cursor_head_value_type_ready policy nilslot p fid v cursors.
Proof. destruct cursors; cbv beta iota delta [cm_cursor_head_lvalue_type_ready cm_cursor_head_value_type_ready cm_phase_lvalue_type_ready]; intuition. Qed.
Lemma cm_l_var_type_ready_step sp ap nilslot p fid scope slot ty st ks ann :
 cm_task_type_ready (cm_source_function_policy sp) nilslot p (CMLTask p fid (CMVarE scope slot ty) st ks) ann ->
 cm_task_type_ready (cm_source_function_policy sp) nilslot p (cm_lstart sp p fid (CMVarE scope slot ty) st ks) (cm_update_annotation (cm_update_l sp ap p fid st ann (CMVarE scope slot ty))).
Proof.
 intros [_ [FL [FU [[BV TY] [LV [CT [IN VAL]]]]]]].
 cbn [cm_lstart cm_update_l cm_update_annotation]; destruct (cm_binding_address_ok sp p fid scope slot st) eqn:OK.
 - cbn [cm_task_type_ready]; split; [reflexivity|]; split; [exact CT|].
   eapply cm_lvalue_result_type_ready; [exact VAL|]; left; apply cm_binding_pointer_type; assumption.
 - apply cm_type_error; exact CT.
Qed.
Lemma cm_l_unary_type_ready_step sp ap nilslot p fid op arg ty st ks ann :
 cm_task_type_ready (cm_source_function_policy sp) nilslot p (CMLTask p fid (CMUnaryE op arg ty) st ks) ann ->
 cm_task_type_ready (cm_source_function_policy sp) nilslot p (cm_lstart sp p fid (CMUnaryE op arg ty) st ks) (cm_update_annotation (cm_update_l sp ap p fid st ann (CMUnaryE op arg ty))).
Proof.
 intros [_ [FL [FU [EW [LV [CT [IN VAL]]]]]]].
 cbn [cm_lvalue] in LV; subst op.
 destruct EW as [AW [[_ [PTR TY]] _]].
 pose proof (cm_pointer_pointee_type _ PTR) as PT; rewrite <-TY in PT.
 cbn [cm_lstart cm_update_l cm_update_annotation Z.eqb Pos.eqb cm_task_type_ready].
 cbn [cm_lvalue_output_type cm_expr_type] in IN,VAL.
 rewrite <-PT in IN,VAL.
 repeat first [assumption|reflexivity|match goal with |- _ /\ _=>split end].
 - now right.
 - intros v [V _]; eapply cm_lvalue_result_type_ready; eauto.
Qed.
Lemma cm_l_index_type_ready_step sp ap nilslot p fid base index ty st ks ann :
 cm_typed_program (cm_source_function_policy sp) p ->
 cm_task_type_ready (cm_source_function_policy sp) nilslot p (CMLTask p fid (CMIndexE base index ty) st ks) ann ->
 cm_task_type_ready (cm_source_function_policy sp) nilslot p (cm_lstart sp p fid (CMIndexE base index ty) st ks) (cm_update_annotation (cm_update_l sp ap p fid st ann (CMIndexE base index ty))).
Proof.
 intros WF [_ [FL [FU [EW [LV [CT [IN VAL]]]]]]].
 pose proof (cm_typed_function_at _ _ _ WF FL FU) as FW.
 pose proof FW as [_ [[PARAM _] [LOC _]]].
 pose proof (cm_expr_type_refs__constructor_facts_c _ _ _ _ WF PARAM LOC EW) as REFS.
 cbn [cm_expr_type] in REFS.
 destruct EW as [BW [IW [PTR [IINT TY]]]].
 pose proof (cm_pointer_pointee_type _ PTR) as PT; rewrite <-TY in PT.
 cbv beta iota zeta delta [cm_lstart cm_update_l cm_lvalue_output_type cm_expr_type] in *; cm_ty_reduce.
 repeat first [assumption|reflexivity|exact I|match goal with |- _ /\ _=>split end].
 - now right.
 - intros result v -> V; eapply cm_lvalue_result_type_ready; eauto.
 - apply cm_cursor_expr_value_ready; cbv beta iota delta [cm_cursor_head_expr_type_ready cm_phase_expr_type_ready cm_cursor_phase]; exact PT.
Qed.
Lemma cm_l_member_type_ready_step sp ap nilslot p fid base mid ty st ks ann :
 cm_task_type_ready (cm_source_function_policy sp) nilslot p (CMLTask p fid (CMMemberE base mid ty) st ks) ann ->
 cm_task_type_ready (cm_source_function_policy sp) nilslot p (cm_lstart sp p fid (CMMemberE base mid ty) st ks) (cm_update_annotation (cm_update_l sp ap p fid st ann (CMMemberE base mid ty))).
Proof.
 intros [_ [FL [FU [EW [LV [CT [IN VAL]]]]]]].
 destruct EW as [BW [MEM TY]].
 pose proof MEM as [PTR _].
 cbv beta iota zeta delta [cm_lstart cm_update_l cm_lvalue_output_type cm_expr_type] in *; cm_ty_reduce.
 repeat first [assumption|reflexivity|exact I|match goal with |- _ /\ _=>split end].
 - now right.
 - intros result v -> V; eapply cm_lvalue_result_type_ready; eauto.
 - apply cm_cursor_expr_value_ready; cbv beta iota delta [cm_cursor_head_expr_type_ready cm_phase_expr_type_ready cm_cursor_phase]; reflexivity.
Qed.
Lemma cm_l_type_ready_step sp ap nilslot p fid expr st ks ann :
 cm_typed_program (cm_source_function_policy sp) p ->
 cm_task_type_ready (cm_source_function_policy sp) nilslot p (CMLTask p fid expr st ks) ann ->
 cm_task_type_ready (cm_source_function_policy sp) nilslot p (cm_lstart sp p fid expr st ks) (cm_update_annotation (cm_update_l sp ap p fid st ann expr)).
Proof.
 intros WF H; destruct expr;
 try solve [apply cm_l_var_type_ready_step; exact H|apply cm_l_unary_type_ready_step; exact H|eapply cm_l_index_type_ready_step; eauto|apply cm_l_member_type_ready_step; exact H];
 destruct H as [_ [_ [_ [_ [LV _]]]]]; exact (False_rect _ LV).
Qed.
