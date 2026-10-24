Require Export SimpleC.EE.QCP_demos_human.cmc_type_lvalue_facts_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Ltac cm_ty_expr_reduce := cbv beta iota zeta delta [cm_rstart cm_update_r cm_ann_linear cm_ann_plain cm_expr_type] in *; cm_ty_reduce.
Lemma cm_r_assign_type_ready_step sp ap nilslot p fid dst src ty st ks ann :
 cm_typed_program (cm_source_function_policy sp) p ->
 cm_task_type_ready (cm_source_function_policy sp) nilslot p (CMRTask p fid (CMAssignE dst src ty) st ks) ann ->
 cm_task_type_ready (cm_source_function_policy sp) nilslot p (cm_rstart sp p fid (CMAssignE dst src ty) st ks) (cm_update_annotation (cm_update_r sp ap p fid st ann (CMAssignE dst src ty))).
Proof.
 intros WF [_ [FL [FU [EW [SC [CT [IN VAL]]]]]]].
 pose proof (cm_typed_function_at _ _ _ WF FL FU) as FW.
 pose proof (cm_nonzero_cursor_values _ _ _ _ (CMAssignE dst src ty) _ ltac:(discriminate) VAL) as RESULT.
 destruct EW as [DW [SW [LV [NA [TY CONV]]]]].
 pose proof (cm_nonarray_lvalue_output _ _ _ _ FW DW NA) as OUT.
 cm_ty_expr_reduce; rewrite OUT,<-TY.
 repeat first [assumption|reflexivity|exact I|match goal with |- _ /\ _=>split end].
 - intros result v -> COMP; apply RESULT; exact COMP.
 - cbv beta iota zeta delta [cm_cursor_head_lvalue_type_ready cm_phase_lvalue_type_ready cm_phase_value_type_ready cm_cursor_phase]; auto.
Qed.
Lemma cm_r_binary_type_ready_step sp ap nilslot p fid op lhs rhs ty st ks ann :
 cm_task_type_ready (cm_source_function_policy sp) nilslot p (CMRTask p fid (CMBinaryE op lhs rhs ty) st ks) ann ->
 cm_task_type_ready (cm_source_function_policy sp) nilslot p (cm_rstart sp p fid (CMBinaryE op lhs rhs ty) st ks) (cm_update_annotation (cm_update_r sp ap p fid st ann (CMBinaryE op lhs rhs ty))).
Proof.
 intros [_ [FL [FU [EW [SC [CT [IN VAL]]]]]]].
 pose proof (cm_nonzero_cursor_values _ _ _ _ (CMBinaryE op lhs rhs ty) _ ltac:(discriminate) VAL) as RESULT.
 pose proof EW as [LW [RW BIN]]; pose proof (cm_binary_operand_scalars _ _ _ _ BIN) as [LS RS].
 cm_ty_expr_reduce.
 repeat first [assumption|reflexivity|exact I|match goal with |- _ /\ _=>split end].
 - intros result v -> COMP; apply RESULT; exact COMP.
 - apply cm_cursor_expr_value_ready; cbv beta iota delta [cm_cursor_head_expr_type_ready cm_phase_expr_type_ready cm_cursor_phase]; reflexivity.
Qed.
Lemma cm_r_putc_type_ready_step sp ap nilslot p fid arg ty st ks ann :
 cm_task_type_ready (cm_source_function_policy sp) nilslot p (CMRTask p fid (CMPutcE arg ty) st ks) ann ->
 cm_task_type_ready (cm_source_function_policy sp) nilslot p (cm_rstart sp p fid (CMPutcE arg ty) st ks) (cm_update_annotation (cm_update_r sp ap p fid st ann (CMPutcE arg ty))).
Proof.
 intros [_ [FL [FU [EW [SC [CT [IN VAL]]]]]]].
 pose proof (cm_nonzero_cursor_values _ _ _ _ (CMPutcE arg ty) _ ltac:(discriminate) VAL) as RESULT.
 destruct EW as [AW [AT TY]].
 pose proof (cm_scalar_type_is_expr_type _ _ AT) as ASC.
 cm_ty_expr_reduce; rewrite TY in *.
 repeat first [assumption|reflexivity|exact I|match goal with |- _ /\ _=>split end|match goal with |- forall _ _,False -> _=>intros; contradiction end].
 - intros result v -> COMP; apply RESULT; exact COMP.
 - apply cm_cursor_expr_value_ready; cbv beta iota delta [cm_cursor_head_expr_type_ready cm_phase_expr_type_ready cm_cursor_phase]; assumption.
Qed.
Lemma cm_r_puti_type_ready_step sp ap nilslot p fid arg ty st ks ann :
 cm_task_type_ready (cm_source_function_policy sp) nilslot p (CMRTask p fid (CMPutiE arg ty) st ks) ann ->
 cm_task_type_ready (cm_source_function_policy sp) nilslot p (cm_rstart sp p fid (CMPutiE arg ty) st ks) (cm_update_annotation (cm_update_r sp ap p fid st ann (CMPutiE arg ty))).
Proof.
 intros [_ [FL [FU [EW [SC [CT [IN VAL]]]]]]].
 pose proof (cm_nonzero_cursor_values _ _ _ _ (CMPutiE arg ty) _ ltac:(discriminate) VAL) as RESULT.
 destruct EW as [AW [AT TY]].
 assert (ASC:cm_scalar_expr_type (cm_expr_type arg)) by (now left).
 cm_ty_expr_reduce; rewrite TY in *.
 repeat first [assumption|reflexivity|exact I|match goal with |- _ /\ _=>split end|match goal with |- forall _ _,False -> _=>intros; contradiction end].
 - intros result v -> COMP; apply RESULT; exact COMP.
 - apply cm_cursor_expr_value_ready; cbv beta iota delta [cm_cursor_head_expr_type_ready cm_phase_expr_type_ready cm_cursor_phase]; assumption.
Qed.
Lemma cm_r_exit_type_ready_step sp ap nilslot p fid arg ty st ks ann :
 cm_task_type_ready (cm_source_function_policy sp) nilslot p (CMRTask p fid (CMExitE arg ty) st ks) ann ->
 cm_task_type_ready (cm_source_function_policy sp) nilslot p (cm_rstart sp p fid (CMExitE arg ty) st ks) (cm_update_annotation (cm_update_r sp ap p fid st ann (CMExitE arg ty))).
Proof.
 intros [_ [FL [FU [EW [SC [CT [IN VAL]]]]]]].
 pose proof (cm_nonzero_cursor_values _ _ _ _ (CMExitE arg ty) _ ltac:(discriminate) VAL) as RESULT.
 destruct EW as [AW [AT TY]].
 assert (ASC:cm_scalar_expr_type (cm_expr_type arg)) by (now left).
 cm_ty_expr_reduce; rewrite TY in *.
 repeat first [assumption|reflexivity|exact I|match goal with |- _ /\ _=>split end|match goal with |- forall _ _,False -> _=>intros; contradiction end].
 - apply cm_cursor_expr_value_ready; cbv beta iota delta [cm_cursor_head_expr_type_ready cm_phase_expr_type_ready cm_cursor_phase]; assumption.
Qed.
Lemma cm_r_index_type_ready_step sp ap nilslot p fid base index ty st ks ann :
 cm_task_type_ready (cm_source_function_policy sp) nilslot p (CMRTask p fid (CMIndexE base index ty) st ks) ann ->
 cm_task_type_ready (cm_source_function_policy sp) nilslot p (cm_rstart sp p fid (CMIndexE base index ty) st ks) (cm_update_annotation (cm_update_r sp ap p fid st ann (CMIndexE base index ty))).
Proof.
 intros [_ [FL [FU [EW [SC [CT [IN VAL]]]]]]].
 pose proof (cm_nonzero_cursor_values _ _ _ _ (CMIndexE base index ty) _ ltac:(discriminate) VAL) as RESULT.
 cm_ty_expr_reduce; cbn [cm_lvalue cm_lvalue_output_type].
 repeat first [assumption|reflexivity|exact I|match goal with |- _ /\ _=>split end].
 - intros result v -> COMP; apply RESULT; exact COMP.
 - cbv beta iota delta [cm_cursor_head_lvalue_type_ready cm_phase_lvalue_type_ready cm_phase_value_type_ready cm_cursor_phase]; auto.
Qed.
