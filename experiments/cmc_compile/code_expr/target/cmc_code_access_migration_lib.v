Require Export SimpleC.EE.QCP_demos_human.cmc_code_binding_migration_lib.
From Coq Require Import ZArith List Bool Lia.
From AUXLib Require Import ListLib.
Import ListNotations.
Local Open Scope Z_scope.
Ltac cm_code_lvalue_reduce := cbv beta iota zeta delta [cm_task_layout cm_task_code cm_task_fid cm_lstart cm_update_l cm_update_annotation cm_ann_push cm_ann_pc cm_ann_temp cm_ann_break cm_ann_continue cm_ann_cursors cm_ann_calls cm_cont_code cm_normal_cont_code cm_cursor_phase cm_cursor_temp cm_cursor_break cm_cursor_continue] in *; cbn [cm_cursor_code cm_cursor_phase cm_cursor_temp cm_cursor_break cm_cursor_continue cm_value_phase_code cm_phase_stops cm_phase_yields_normal cm_saved_layout cm_phase_site cm_phase_is_call orb] in *.
Lemma cm_l_index_layout_step sp ap p fid base index ty st ks ann : cm_task_layout sp ap p (CMLTask p fid (CMIndexE base index ty) st ks) ann -> cm_task_layout sp ap p (cm_lstart sp p fid (CMIndexE base index ty) st ks) (cm_update_annotation (cm_update_l sp ap p fid st ann (CMIndexE base index ty))).
Proof.
 intros [CODE SAVED]; cm_code_lvalue_reduce; split; [|split; [exact I|exact SAVED]].
 match type of CODE with cm_code_at ?c ?pc ?old=>match goal with |- cm_code_at _ _ ?new=>replace new with old; [exact CODE|] end end.
 unfold cm_emit_lvalue,cm_emit_rvalue,cm_expr_code_for,cm_index_tail_code; cbn [Z.eqb cm_emit_expr_pair cm_lcode_of].
 repeat rewrite Zlength_app; rewrite cm_layout_temp_store_length,cm_layout_temp_load_length.
 repeat match goal with |-context[Zlength (cm_rcode_of (cm_emit_expr_pair ?pol ?pr ?f ?pc ?t ?e))]=>rewrite (proj2 (cm_emit_pair_lengths__store_bounds pol pr f e pc t)) end.
 unfold cm_lvalue_code_count,cm_rvalue_code_count; cbn [cm_expr_code_counts cm_lcount_of Zlength]; repeat rewrite <-app_assoc; repeat rewrite Zlength_cons; rewrite ?Zlength_nil; repeat first [reflexivity|solve [lia]|progress f_equal].
Qed.
Lemma cm_l_member_layout_step sp ap p fid base mid ty st ks ann : cm_task_layout sp ap p (CMLTask p fid (CMMemberE base mid ty) st ks) ann -> cm_task_layout sp ap p (cm_lstart sp p fid (CMMemberE base mid ty) st ks) (cm_update_annotation (cm_update_l sp ap p fid st ann (CMMemberE base mid ty))).
Proof.
 intros [CODE SAVED]; cm_code_lvalue_reduce; split; [|split; [exact I|exact SAVED]].
 match type of CODE with cm_code_at ?c ?pc ?old=>match goal with |- cm_code_at _ _ ?new=>replace new with old; [exact CODE|] end end.
 unfold cm_emit_lvalue,cm_emit_rvalue,cm_expr_code_for,cm_member_tail_code; cbn [Z.eqb cm_emit_expr_pair cm_lcode_of].
 unfold cm_lvalue_code_count,cm_rvalue_code_count; cbn [cm_expr_code_counts cm_lcount_of Zlength]; repeat rewrite <-app_assoc; repeat rewrite Z.add_assoc; reflexivity.
Qed.
Lemma cm_r_member_layout_step sp ap p fid base mid ty st ks ann : cm_member_valid p (cm_expr_type base) mid -> cm_task_layout sp ap p (CMRTask p fid (CMMemberE base mid ty) st ks) ann -> cm_task_layout sp ap p (cm_rstart sp p fid (CMMemberE base mid ty) st ks) (cm_update_annotation (cm_update_r sp ap p fid st ann (CMMemberE base mid ty))).
Proof.
 intros B [CODE SAVED]; pose proof (cm_member_array_code_agrees sp p (cm_expr_type base) mid B) as ARRAY.
 cm_code_expr_reduce; destruct(cm_member_array sp p (cm_expr_type base) mid) eqn:AR; cbn [cm_task_code cm_task_fid cm_update_annotation cm_ann_push cm_ann_pc cm_ann_temp cm_ann_break cm_ann_continue cm_ann_cursors cm_ann_calls cm_cursor_code cm_cursor_phase cm_cursor_temp cm_cursor_break cm_cursor_continue cm_value_phase_code cm_phase_stops cm_phase_yields_normal cm_saved_layout cm_phase_site cm_phase_is_call orb]; split; try(split; [exact I|exact SAVED]); try exact SAVED.
 all: match type of CODE with cm_code_at ?c ?pc ?old=>match goal with |- cm_code_at _ _ ?new=>replace new with old; [exact CODE|] end end.
 all: unfold cm_emit_rvalue,cm_emit_lvalue,cm_expr_code_for; cbn [Z.eqb cm_emit_expr_pair cm_rcode_of cm_lcode_of]; unfold cm_rvalue_code_count,cm_lvalue_code_count; cbn [cm_expr_code_counts cm_rcount_of cm_lcount_of]; rewrite ARRAY; cbn [negb]; rewrite ?app_nil_r,?cm_layout_load_length; repeat rewrite <-app_assoc; repeat rewrite Zlength_cons; rewrite ?Zlength_nil; repeat first [reflexivity|solve [lia]|progress f_equal].
Qed.
