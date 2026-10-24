Require Export SimpleC.EE.QCP_demos_human.cmc_code_binary_migration_lib.
Require Export SimpleC.EE.QCP_demos_human.cmc_code_access_migration_lib.
Require Export SimpleC.EE.QCP_demos_human.cmc_code_call_cons_migration_lib.
From Coq Require Import ZArith List Bool Lia.
From AUXLib Require Import ListLib.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_r_task_layout_step sp ap p fid expr st ann :
 cm_expr_wf (cm_source_function_policy sp) p (cm_source_function_at sp fid p) expr ->
 cm_r_layout_ready sp p fid expr st (cm_cursor_frames (cm_ann_cursors ann)) ann ->
 cm_task_succeeds sp (CMRTask p fid expr st (cm_cursor_frames (cm_ann_cursors ann))) ->
 cm_task_layout sp ap p (CMRTask p fid expr st (cm_cursor_frames (cm_ann_cursors ann))) ann ->
 cm_task_layout sp ap p (cm_step sp (CMRTask p fid expr st (cm_cursor_frames (cm_ann_cursors ann)))) (cm_update_annotation(cm_annotation_step sp ap (CMRTask p fid expr st (cm_cursor_frames (cm_ann_cursors ann))) ann)).
Proof.
 intros EW [CALL [INPUT VAR]] S L; cbn [cm_step cm_annotation_step].
 destruct expr; try solve [eauto using cm_r_const_layout_step,cm_r_string_layout_step,cm_r_assign_layout_step,cm_r_binary_layout_step,cm_r_unary_layout_step,cm_r_index_layout_step,cm_r_sizeof_layout_step,cm_r_putc_layout_step,cm_r_puti_layout_step,cm_r_exit_layout_step].
 - apply cm_r_var_layout_step; [exact(proj1 EW)|intros AR; eapply VAR; eauto|exact L].
 - apply cm_r_member_layout_step; [exact(proj1(proj2 EW))|exact L].
 - destruct args as [|arg args]; [|now apply cm_r_call_cons_layout_step].
   destruct (CALL fid0 ty eq_refl) as [OK [_ DEPTH]]; now apply cm_r_call_nil_layout_step.
 - apply cm_r_getc_layout_step; [exact(cm_succeeds_step_total sp _ S)|exact L].
Qed.
Lemma cm_l_task_layout_step sp ap p fid expr st ks ann :
 cm_l_layout_ready sp p fid expr st -> cm_task_layout sp ap p (CMLTask p fid expr st ks) ann ->
 cm_task_layout sp ap p (cm_step sp (CMLTask p fid expr st ks)) (cm_update_annotation(cm_annotation_step sp ap (CMLTask p fid expr st ks) ann)).
Proof.
 intros [LV VAR] L; cbn [cm_step cm_annotation_step]; destruct expr; cbn [cm_lvalue] in LV; try contradiction.
 - apply cm_l_var_layout_step; [eapply VAR; reflexivity|exact L].
 - subst op; now apply cm_l_unary_layout_step.
 - now apply cm_l_index_layout_step.
 - now apply cm_l_member_layout_step.
Qed.
