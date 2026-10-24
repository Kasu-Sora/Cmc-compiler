Require Export SimpleC.EE.QCP_demos_human.cmc_code_layout_leaf_migration_lib.
From Coq Require Import ZArith List Bool Lia.
From AUXLib Require Import ListLib.
Import ListNotations.
Local Open Scope Z_scope.
Ltac cm_code_expr_reduce := cbv beta iota zeta delta [cm_task_layout cm_task_code cm_task_fid cm_rstart cm_update_r cm_update_annotation cm_ann_push cm_ann_pc cm_ann_temp cm_ann_break cm_ann_continue cm_ann_cursors cm_ann_calls cm_cont_code cm_normal_cont_code cm_cursor_phase cm_cursor_temp cm_cursor_break cm_cursor_continue] in *; cbn [cm_cursor_code cm_cursor_phase cm_cursor_temp cm_cursor_break cm_cursor_continue cm_value_phase_code cm_phase_stops cm_phase_yields_normal cm_saved_layout cm_phase_site cm_phase_is_call orb] in *.
Lemma cm_r_putc_layout_step sp ap p fid arg ty st ks ann : cm_task_layout sp ap p (CMRTask p fid (CMPutcE arg ty) st ks) ann -> cm_task_layout sp ap p (cm_rstart sp p fid (CMPutcE arg ty) st ks) (cm_update_annotation (cm_update_r sp ap p fid st ann (CMPutcE arg ty))).
Proof.
 intros [CODE SAVED]; cm_code_expr_reduce; split; [|split; [exact I|exact SAVED]].
 match type of CODE with cm_code_at ?c ?pc ?old=>match goal with |- cm_code_at _ _ ?new=>replace new with old; [exact CODE|] end end.
 unfold cm_emit_rvalue,cm_expr_code_for.
 cbn [Z.eqb cm_emit_rvalue cm_expr_code_for cm_emit_expr_pair cm_rcode_of cm_rvalue_code_count cm_expr_code_counts cm_rcount_of].
 repeat rewrite <-app_assoc.
 cbn [orb].
 change (Zlength [TVMInst TVMDupOp 0;TVMInst TVMPutcOp 0]) with 2.
 repeat rewrite Z.add_assoc.
 reflexivity.
Qed.
Lemma cm_r_puti_layout_step sp ap p fid arg ty st ks ann : cm_task_layout sp ap p (CMRTask p fid (CMPutiE arg ty) st ks) ann -> cm_task_layout sp ap p (cm_rstart sp p fid (CMPutiE arg ty) st ks) (cm_update_annotation (cm_update_r sp ap p fid st ann (CMPutiE arg ty))).
Proof.
 intros [CODE SAVED]; cm_code_expr_reduce; split; [|split; [exact I|exact SAVED]].
 match type of CODE with cm_code_at ?c ?pc ?old=>match goal with |- cm_code_at _ _ ?new=>replace new with old; [exact CODE|] end end.
 unfold cm_emit_rvalue,cm_expr_code_for.
 cbn [Z.eqb cm_emit_rvalue cm_expr_code_for cm_emit_expr_pair cm_rcode_of cm_rvalue_code_count cm_expr_code_counts cm_rcount_of].
 repeat rewrite <-app_assoc.
 cbn [orb].
 change (Zlength [TVMInst TVMDupOp 0;TVMInst TVMPutiOp 0]) with 2.
 repeat rewrite Z.add_assoc.
 reflexivity.
Qed.
Lemma cm_r_exit_layout_step sp ap p fid arg ty st ks ann : cm_task_layout sp ap p (CMRTask p fid (CMExitE arg ty) st ks) ann -> cm_task_layout sp ap p (cm_rstart sp p fid (CMExitE arg ty) st ks) (cm_update_annotation (cm_update_r sp ap p fid st ann (CMExitE arg ty))).
Proof.
 intros [CODE SAVED]; cm_code_expr_reduce; split; [|split; [exact I|exact SAVED]].
 apply cm_code_at_append_left in CODE.
 rewrite app_nil_r.
 exact CODE.
Qed.
Lemma cm_r_index_layout_step sp ap p fid base index ty st ks ann : cm_task_layout sp ap p (CMRTask p fid (CMIndexE base index ty) st ks) ann -> cm_task_layout sp ap p (cm_rstart sp p fid (CMIndexE base index ty) st ks) (cm_update_annotation (cm_update_r sp ap p fid st ann (CMIndexE base index ty))).
Proof.
 intros [CODE SAVED]; cm_code_expr_reduce; split; [|split; [exact I|exact SAVED]].
 match type of CODE with cm_code_at ?c ?pc ?old=>match goal with |- cm_code_at _ _ ?new=>replace new with old; [exact CODE|] end end.
 unfold cm_emit_rvalue,cm_emit_lvalue,cm_expr_code_for.
 cbn [Z.eqb cm_emit_expr_pair cm_rcode_of cm_lcode_of cm_rvalue_code_count cm_lvalue_code_count cm_expr_code_counts cm_rcount_of cm_lcount_of orb].
 rewrite cm_layout_load_length; repeat rewrite <-app_assoc; repeat rewrite Z.add_assoc; repeat match goal with |-context[?x+13+1]=>replace (x+13+1) with (x+14) by lia end; reflexivity.
Qed.
Lemma cm_r_assign_layout_step sp ap p fid dst src ty st ks ann : cm_task_layout sp ap p (CMRTask p fid (CMAssignE dst src ty) st ks) ann -> cm_task_layout sp ap p (cm_rstart sp p fid (CMAssignE dst src ty) st ks) (cm_update_annotation (cm_update_r sp ap p fid st ann (CMAssignE dst src ty))).
Proof.
 intros [CODE SAVED]; cm_code_expr_reduce; split; [|split; [exact I|exact SAVED]].
 match type of CODE with cm_code_at ?c ?pc ?old=>match goal with |- cm_code_at _ _ ?new=>replace new with old; [exact CODE|] end end.
 unfold cm_emit_rvalue,cm_emit_lvalue,cm_expr_code_for,cm_assign_tail_code.
 cbn [Z.eqb cm_emit_expr_pair cm_rcode_of cm_lcode_of cm_rvalue_code_count cm_lvalue_code_count cm_expr_code_counts cm_rcount_of cm_lcount_of orb].
 repeat rewrite Zlength_app; rewrite cm_layout_temp_store_length,cm_layout_char_normalize_length,cm_layout_temp_load_length,cm_layout_store_length,cm_layout_load_length.
 match goal with |-context[Zlength (cm_rcode_of (cm_emit_expr_pair ?pol ?pr ?f ?pc ?t ?e))]=>rewrite (proj2 (cm_emit_pair_lengths__store_bounds pol pr f e pc t)) end.
 repeat rewrite <-app_assoc.
 unfold cm_lvalue_code_count,cm_rvalue_code_count.
 repeat first [reflexivity|solve [lia]|progress f_equal].
Qed.
