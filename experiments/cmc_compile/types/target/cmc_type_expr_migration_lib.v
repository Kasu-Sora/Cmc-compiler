Require Export SimpleC.EE.QCP_demos_human.cmc_type_lvalue_migration_lib.
Require Export SimpleC.EE.QCP_demos_human.cmc_type_expr_call_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_r_type_ready_step sp ap nilslot p fid expr st ann :
 cm_typed_program (cm_source_function_policy sp) p ->
 cm_task_type_ready (cm_source_function_policy sp) nilslot p (CMRTask p fid expr st (cm_cursor_frames (cm_ann_cursors ann))) ann ->
 cm_task_type_ready (cm_source_function_policy sp) nilslot p (cm_rstart sp p fid expr st (cm_cursor_frames (cm_ann_cursors ann))) (cm_update_annotation (cm_update_r sp ap p fid st ann expr)).
Proof.
 intros WF H; destruct expr; eauto using cm_r_const_type_ready_step,cm_r_string_type_ready_step,cm_r_var_type_ready_step,cm_r_assign_type_ready_step,cm_r_binary_type_ready_step,cm_r_unary_type_ready_step,cm_r_index_type_ready_step,cm_r_member_type_ready_step,cm_r_call_type_ready_step,cm_r_sizeof_type_ready_step,cm_r_getc_type_ready_step,cm_r_putc_type_ready_step,cm_r_puti_type_ready_step,cm_r_exit_type_ready_step.
Qed.
