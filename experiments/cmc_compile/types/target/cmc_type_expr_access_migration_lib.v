Require Export SimpleC.EE.QCP_demos_human.cmc_type_binding_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_r_var_type_ready_step sp ap nilslot p fid scope slot ty st ks ann :
 cm_typed_program (cm_source_function_policy sp) p ->
 cm_task_type_ready (cm_source_function_policy sp) nilslot p (CMRTask p fid (CMVarE scope slot ty) st ks) ann ->
 cm_task_type_ready (cm_source_function_policy sp) nilslot p (cm_rstart sp p fid (CMVarE scope slot ty) st ks) (cm_update_annotation (cm_update_r sp ap p fid st ann (CMVarE scope slot ty))).
Proof.
 intros WF H; pose proof H as [_ [FL [FU [EW [SC [CT [IN VAL]]]]]]]. pose proof EW as [BV TY].
 pose proof (cm_typed_function_at _ _ _ WF FL FU) as FW.
 pose proof (cm_binding_output_array sp p fid scope slot ty FW BV) as OUT.
 pose proof (cm_nonzero_cursor_values _ _ _ _ (CMVarE scope slot ty) _ ltac:(discriminate) VAL) as RESULT.
 cbn [cm_rstart cm_update_r cm_update_annotation]; destruct (cm_binding_array sp p fid scope slot) eqn:ARRAY.
 - destruct (cm_binding_address_ok sp p fid scope slot st) eqn:OK.
   + eapply cm_r_type_yield; [exact H| |reflexivity]. apply cm_expr_not_zero_ready; [discriminate|]. left.
     rewrite (cm_binding_pointer_type sp p fid scope slot ty st BV OK),OUT; symmetry; exact TY.
   + apply cm_type_error; exact CT.
 - unfold cm_source_function_at in OUT,TY; cm_ty_reduce; rewrite OUT,<-TY.
   repeat first [assumption|reflexivity|exact I|match goal with |- _ /\ _=>split end].
   + intros result v -> COMP; apply RESULT; exact COMP.
   + cbv beta iota delta [cm_cursor_head_lvalue_type_ready cm_phase_lvalue_type_ready cm_phase_value_type_ready cm_cursor_phase]; auto.
Qed.
Lemma cm_r_member_type_ready_step sp ap nilslot p fid base mid ty st ks ann :
 cm_task_type_ready (cm_source_function_policy sp) nilslot p (CMRTask p fid (CMMemberE base mid ty) st ks) ann ->
 cm_task_type_ready (cm_source_function_policy sp) nilslot p (cm_rstart sp p fid (CMMemberE base mid ty) st ks) (cm_update_annotation (cm_update_r sp ap p fid st ann (CMMemberE base mid ty))).
Proof.
 intros [_ [FL [FU [EW [SC [CT [IN VAL]]]]]]]; pose proof EW as [BW [MEM TY]].
 pose proof (cm_member_output_array sp p (cm_expr_type base) mid MEM) as OUT.
 pose proof (cm_nonzero_cursor_values _ _ _ _ (CMMemberE base mid ty) _ ltac:(discriminate) VAL) as RESULT.
 cbn [cm_rstart cm_update_r cm_update_annotation]; destruct (cm_member_array sp p (cm_expr_type base) mid) eqn:ARRAY;
 cm_ty_reduce; cbn [cm_lvalue cm_lvalue_output_type]; rewrite OUT,<-TY;
 repeat first [assumption|reflexivity|exact I|match goal with |- _ /\ _=>split end].
 - fold (cm_ann_cursors ann) in *; destruct (cm_ann_cursors ann) as [|c rest] eqn:C; [contradiction|].
   cbv beta iota delta [cm_cursor_head_lvalue_type_ready cm_phase_lvalue_type_ready]; intros v V; apply RESULT; exact V.
 - intros result v -> COMP; apply RESULT; exact COMP.
 - cbv beta iota delta [cm_cursor_head_lvalue_type_ready cm_phase_lvalue_type_ready cm_phase_value_type_ready cm_cursor_phase]; auto.
Qed.
