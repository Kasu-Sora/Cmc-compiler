Require Export SimpleC.EE.QCP_demos_human.cmc_code_stmt_basic_migration_lib.
From Coq Require Import ZArith List Bool Lia.
From AUXLib Require Import ListLib.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_s_init_layout_step sp ap p fid slot expr st ks ann : cm_local_slot_ok sp p fid slot=true -> cm_task_layout sp ap p (CMSTask p fid (CMInitS slot expr) st ks) ann -> cm_task_layout sp ap p (cm_sstart sp p fid (CMInitS slot expr) st ks) (cm_update_annotation(cm_update_s sp ap p fid st ann (CMInitS slot expr))).
Proof.
 intros OK [CODE SAVED]; pose proof OK as B; unfold cm_local_slot_ok in B; repeat rewrite andb_true_iff in B; destruct B as [[[_ _] LO] HI]; apply Z.leb_le in LO; apply Z.ltb_lt in HI.
 cbn [cm_sstart cm_update_s]; rewrite OK; cm_code_stmt_reduce; split; [|split; [exact I|exact SAVED]].
 match type of CODE with cm_code_at ?c ?pc ?old=>match goal with |- cm_code_at _ _ ?new=>replace new with old; [exact CODE|] end end.
 cbn [cm_emit_stmt cm_stmt_code_count]; unfold cm_emit_rvalue,cm_init_tail_code; rewrite(cm_source_slot_at_valid sp _ _ (conj LO HI)).
 repeat rewrite Zlength_app; rewrite cm_layout_char_normalize_length,cm_layout_store_length.
 change (Zlength(cm_fp_relative_address_code (cm_local_offset (cm_source_function_policy sp) p fid slot))) with 4.
 unfold cm_source_function_at,cm_normal_cont_code; unfold cm_normal_cont_code; repeat rewrite <-app_assoc; repeat first [reflexivity|solve [lia]|progress f_equal].
Qed.
Lemma cm_s_if_layout_step sp ap p fid guard yes no st ks ann : cm_task_layout sp ap p (CMSTask p fid (CMIfS guard yes no) st ks) ann -> cm_task_layout sp ap p (cm_sstart sp p fid (CMIfS guard yes no) st ks) (cm_update_annotation(cm_update_s sp ap p fid st ann (CMIfS guard yes no))).
Proof.
 intros [CODE SAVED]; cm_code_stmt_reduce; split; [|split; [exact I|exact SAVED]].
 match type of CODE with cm_code_at ?c ?pc ?old=>match goal with |- cm_code_at _ _ ?new=>replace new with old; [exact CODE|] end end.
 cbn [cm_emit_stmt cm_stmt_code_count]; unfold cm_emit_rvalue; repeat rewrite Zlength_app; repeat rewrite cm_emit_stmt_length__stmt_capacity; repeat rewrite Zlength_cons; rewrite Zlength_nil.
 unfold cm_normal_cont_code; repeat rewrite <-app_assoc; repeat first [reflexivity|solve [lia]|progress f_equal].
Qed.
Lemma cm_s_while_layout_step sp ap p fid guard body st ks ann : cm_task_layout sp ap p (CMSTask p fid (CMWhileS guard body) st ks) ann -> cm_task_layout sp ap p (cm_sstart sp p fid (CMWhileS guard body) st ks) (cm_update_annotation(cm_update_s sp ap p fid st ann (CMWhileS guard body))).
Proof.
 intros [CODE SAVED]; pose proof CODE as TAIL; cbn [cm_task_code] in TAIL; apply cm_code_at_append_right in TAIL; rewrite cm_emit_stmt_length__stmt_capacity in TAIL.
 cm_code_stmt_reduce; split; [|split; [split; [cbn [cm_emit_stmt] in CODE; repeat rewrite <-app_assoc in CODE; exact CODE|exact TAIL]|exact SAVED]].
 match type of CODE with cm_code_at ?c ?pc ?old=>match goal with |- cm_code_at _ _ ?new=>replace new with old; [exact CODE|] end end.
 cbn [cm_emit_stmt cm_stmt_code_count]; unfold cm_emit_rvalue; repeat rewrite Zlength_app; repeat rewrite cm_emit_stmt_length__stmt_capacity; repeat rewrite Zlength_cons; rewrite Zlength_nil.
 unfold cm_normal_cont_code; repeat rewrite <-app_assoc; repeat first [reflexivity|solve [lia]|progress f_equal].
Qed.
Lemma cm_s_task_layout_step sp ap p fid stmt st ks ann : cm_stmt_start_safe sp p fid stmt=true -> cm_task_layout sp ap p (CMSTask p fid stmt st ks) ann -> cm_task_layout sp ap p (cm_step sp (CMSTask p fid stmt st ks)) (cm_update_annotation(cm_annotation_step sp ap (CMSTask p fid stmt st ks) ann)).
Proof.
 intros SAFE L; cbn [cm_step cm_annotation_step]; destruct stmt; eauto using cm_s_skip_layout_step,cm_s_expr_layout_step,cm_s_decl_layout_step,cm_s_init_layout_step,cm_s_seq_layout_step,cm_s_block_layout_step,cm_s_if_layout_step,cm_s_while_layout_step,cm_s_break_layout_step,cm_s_continue_layout_step,cm_s_return_layout_step.
Qed.
