Require Export SimpleC.EE.QCP_demos_human.cmc_type_call_migration_lib.
Require Export SimpleC.EE.QCP_demos_human.cmc_type_expr_struct_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_r_call_type_ready_step sp ap nilslot p fid callee args ty st ann :
 cm_typed_program (cm_source_function_policy sp) p ->
 cm_task_type_ready (cm_source_function_policy sp) nilslot p (CMRTask p fid (CMCallE callee args ty) st (cm_cursor_frames (cm_ann_cursors ann))) ann ->
 cm_task_type_ready (cm_source_function_policy sp) nilslot p (cm_rstart sp p fid (CMCallE callee args ty) st (cm_cursor_frames (cm_ann_cursors ann))) (cm_update_annotation (cm_update_r sp ap p fid st ann (CMCallE callee args ty))).
Proof.
 intros WF [_ [FL [FU [EW [SC [CT [IN VAL]]]]]]]. apply cm_expr_wf_call in EW; destruct EW as [CALLEE [AW RET]].
 pose proof (cm_nonzero_cursor_values _ _ _ _ (CMCallE callee args ty) _ ltac:(discriminate) VAL) as RESULT.
 destruct args as [|arg args].
 - cbv beta iota zeta delta [cm_rstart cm_args_start cm_begin_call cm_update_r cm_list_empty cm_update_annotation andb].
   destruct (cm_call_ok sp p callee [] st); [destruct (cm_call_depth (cm_cursor_frames (cm_ann_cursors ann))<?65536)|]; try solve [apply cm_type_error; exact CT].
   eapply cm_type_enter_call with (values:=[]); try eassumption; right; lia.
 - pose proof (cm_args_wf_exprs _ _ _ _ _ AW) as [ARG [ASC REST]].
   pose proof (cm_args_wf_head_convertible _ nilslot arg _ _ _ _ AW ltac:(discriminate)) as CONV.
   pose proof (cm_args_wf_slots_nonempty _ _ _ _ _ AW ltac:(discriminate)) as SLOTS.
   cbv beta iota zeta delta [cm_rstart cm_update_r cm_args_start cm_list_empty tl]; cm_ty_expr_reduce;
   cbn [cm_arg_progress_type_ready rev hd tl].
   repeat first [assumption|reflexivity|exact I|match goal with |- _ /\ _=>split end].
   + exact (proj1 CALLEE).
   + exact (proj2 CALLEE).
   + discriminate.
   + intros result v -> COMP; apply RESULT; exact COMP.
   + apply cm_cursor_expr_value_ready; cbv beta iota zeta delta [cm_cursor_head_expr_type_ready cm_phase_expr_type_ready cm_cursor_phase cm_arg_next_type rev hd]; exact CONV.
Qed.
