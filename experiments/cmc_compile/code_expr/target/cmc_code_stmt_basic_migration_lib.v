Require Export SimpleC.EE.QCP_demos_human.cmc_code_expr_dispatch_migration_lib.
From Coq Require Import ZArith List Bool Lia.
From AUXLib Require Import ListLib.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_normal_control_code sp p fid pc temp breakpc continuepc cursors : cm_control_phase_code sp p fid pc temp breakpc continuepc CMNormal cursors=cm_normal_cont_code sp p fid pc temp cursors.
Proof. destruct cursors; reflexivity. Qed.
Ltac cm_code_stmt_reduce := cbv beta iota zeta delta [cm_task_layout cm_task_code cm_task_fid cm_sstart cm_update_s cm_update_annotation cm_ann_push cm_ann_pc cm_ann_temp cm_ann_break cm_ann_continue cm_ann_cursors cm_ann_calls cm_cursor_phase cm_cursor_temp cm_cursor_break cm_cursor_continue] in *; rewrite ?cm_normal_control_code; cbn [cm_cont_code cm_normal_cont_code cm_cursor_code cm_cursor_phase cm_cursor_temp cm_cursor_break cm_cursor_continue cm_value_phase_code cm_normal_phase_code cm_phase_stops cm_normal_phase_stops cm_phase_yields_normal cm_saved_layout cm_phase_site cm_phase_is_call orb] in *.
Lemma cm_s_skip_layout_step sp ap p fid st ks ann : cm_task_layout sp ap p (CMSTask p fid CMSkipS st ks) ann -> cm_task_layout sp ap p (cm_sstart sp p fid CMSkipS st ks) (cm_update_annotation(cm_update_s sp ap p fid st ann CMSkipS)).
Proof. intros [CODE SAVED]; cm_code_stmt_reduce; split; [|exact SAVED]. cbn [cm_emit_stmt cm_stmt_code_count] in CODE; rewrite Z.add_0_r in CODE; exact CODE. Qed.
Lemma cm_s_decl_layout_step sp ap p fid slot st ks ann : cm_local_slot_ok sp p fid slot=true -> cm_task_layout sp ap p (CMSTask p fid (CMDeclS slot) st ks) ann -> cm_task_layout sp ap p (cm_sstart sp p fid (CMDeclS slot) st ks) (cm_update_annotation(cm_update_s sp ap p fid st ann (CMDeclS slot))).
Proof. intros OK [CODE SAVED]; cbn [cm_sstart]; rewrite OK; cm_code_stmt_reduce; split; [|exact SAVED]. cbn [cm_emit_stmt cm_stmt_code_count] in CODE; rewrite Z.add_0_r in CODE; exact CODE. Qed.
Lemma cm_s_expr_layout_step sp ap p fid expr st ks ann : cm_task_layout sp ap p (CMSTask p fid (CMExprS expr) st ks) ann -> cm_task_layout sp ap p (cm_sstart sp p fid (CMExprS expr) st ks) (cm_update_annotation(cm_update_s sp ap p fid st ann (CMExprS expr))).
Proof.
 intros [CODE SAVED]; cm_code_stmt_reduce; split; [|split; [exact I|exact SAVED]].
 match type of CODE with cm_code_at ?c ?pc ?old=>match goal with |- cm_code_at _ _ ?new=>replace new with old; [exact CODE|] end end.
 cbn [cm_emit_stmt cm_stmt_code_count]; unfold cm_emit_rvalue; repeat rewrite <-app_assoc; repeat rewrite Zlength_cons; rewrite Zlength_nil; repeat rewrite Z.add_assoc; reflexivity.
Qed.
Lemma cm_s_seq_layout_step sp ap p fid first second st ks ann : cm_task_layout sp ap p (CMSTask p fid (CMSeqS first second) st ks) ann -> cm_task_layout sp ap p (cm_sstart sp p fid (CMSeqS first second) st ks) (cm_update_annotation(cm_update_s sp ap p fid st ann (CMSeqS first second))).
Proof.
 intros [CODE SAVED]; cm_code_stmt_reduce; split; [|split; [exact I|exact SAVED]].
 match type of CODE with cm_code_at ?c ?pc ?old=>match goal with |- cm_code_at _ _ ?new=>replace new with old; [exact CODE|] end end.
 cbn [cm_emit_stmt cm_stmt_code_count]; rewrite cm_emit_stmt_length__stmt_capacity; repeat rewrite <-app_assoc; repeat rewrite Z.add_assoc; reflexivity.
Qed.
Lemma cm_s_block_layout_step sp ap p fid body st ks ann : cm_task_layout sp ap p (CMSTask p fid (CMBlockS body) st ks) ann -> cm_task_layout sp ap p (cm_sstart sp p fid (CMBlockS body) st ks) (cm_update_annotation(cm_update_s sp ap p fid st ann (CMBlockS body))).
Proof.
 intros [CODE SAVED]; cm_code_stmt_reduce; split; [|split; [now left|exact SAVED]].
 cbn [cm_emit_stmt cm_stmt_code_count] in CODE; rewrite Z.add_0_r; exact CODE.
Qed.
Lemma cm_s_break_layout_step sp ap p fid st ks ann : cm_task_layout sp ap p (CMSTask p fid CMBreakS st ks) ann -> cm_task_layout sp ap p (cm_sstart sp p fid CMBreakS st ks) (cm_update_annotation(cm_update_s sp ap p fid st ann CMBreakS)).
Proof. intros [CODE SAVED]; split; [|exact SAVED]. exact (cm_code_at_append_left _ _ _ _ CODE). Qed.
Lemma cm_s_continue_layout_step sp ap p fid st ks ann : cm_task_layout sp ap p (CMSTask p fid CMContinueS st ks) ann -> cm_task_layout sp ap p (cm_sstart sp p fid CMContinueS st ks) (cm_update_annotation(cm_update_s sp ap p fid st ann CMContinueS)).
Proof. intros [CODE SAVED]; split; [|exact SAVED]. exact (cm_code_at_append_left _ _ _ _ CODE). Qed.
Lemma cm_s_return_layout_step sp ap p fid expr st ks ann : cm_task_layout sp ap p (CMSTask p fid (CMReturnS expr) st ks) ann -> cm_task_layout sp ap p (cm_sstart sp p fid (CMReturnS expr) st ks) (cm_update_annotation(cm_update_s sp ap p fid st ann (CMReturnS expr))).
Proof.
 intros [CODE SAVED]; cm_code_stmt_reduce; split; [|split; [exact I|exact SAVED]].
 apply cm_code_at_append_left in CODE; rewrite app_nil_r; exact CODE.
Qed.
