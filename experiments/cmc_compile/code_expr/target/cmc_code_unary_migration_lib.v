Require Export SimpleC.EE.QCP_demos_human.cmc_code_expr_struct_migration_lib.
From Coq Require Import ZArith List Bool Lia.
From AUXLib Require Import ListLib.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_r_unary_layout_step sp ap p fid op arg ty st ks ann : cm_task_layout sp ap p (CMRTask p fid (CMUnaryE op arg ty) st ks) ann -> cm_task_layout sp ap p (cm_rstart sp p fid (CMUnaryE op arg ty) st ks) (cm_update_annotation (cm_update_r sp ap p fid st ann (CMUnaryE op arg ty))).
Proof.
 intros [CODE SAVED]; cm_code_expr_reduce.
 destruct (op=?2) eqn:TWO; [|destruct(op=?3) eqn:THREE]; cbn [cm_task_code cm_task_fid cm_ann_push cm_ann_pc cm_ann_temp cm_ann_break cm_ann_continue cm_ann_cursors cm_ann_calls cm_cursor_code cm_cursor_phase cm_cursor_temp cm_cursor_break cm_cursor_continue cm_value_phase_code cm_phase_stops cm_phase_yields_normal cm_saved_layout cm_phase_site cm_phase_is_call orb]; split; try (split; [exact I|exact SAVED]); try exact SAVED.
 all: match type of CODE with cm_code_at ?c ?pc ?old=>match goal with |- cm_code_at _ _ ?new=>replace new with old; [exact CODE|] end end.
 all: unfold cm_emit_rvalue,cm_emit_lvalue,cm_expr_code_for; cbn [Z.eqb cm_emit_expr_pair cm_rcode_of cm_lcode_of cm_rvalue_code_count cm_lvalue_code_count cm_expr_code_counts cm_rcount_of cm_lcount_of]; rewrite TWO; try rewrite THREE; cbn [cm_rcode_of cm_lcode_of cm_rcount_of cm_lcount_of]; repeat rewrite <-app_assoc; try rewrite cm_layout_load_length; try reflexivity.
 all: unfold cm_rvalue_code_count,cm_lvalue_code_count; cbn [cm_expr_code_counts cm_rcount_of cm_lcount_of]; rewrite ?TWO,?THREE; cbn [cm_rcount_of cm_lcount_of Zlength]; repeat rewrite Z.add_assoc; reflexivity.
Qed.
Lemma cm_layout_lvalue_linear sp ap p fid expr st ks ann out st' :
 cm_task_layout sp ap p (CMLTask p fid expr st ks) ann ->
 cm_task_layout sp ap p (CMVTask p fid out st' ks) (cm_ann_linear (cm_emit_lvalue (cm_source_function_policy sp) p fid (cm_ann_pc ann) (cm_ann_temp ann) expr) ann).
Proof.
 intros [CODE SAVED]; split; [|exact SAVED].
 cbn [cm_task_code] in CODE; cbn [cm_task_code cm_ann_linear cm_ann_plain cm_ann_pc cm_ann_temp cm_ann_cursors].
 rewrite <-(cm_layout_lvalue_code_length (cm_source_function_policy sp) p fid expr (cm_ann_pc ann) (cm_ann_temp ann)) in CODE; now apply cm_code_at_append_right in CODE.
Qed.
Lemma cm_l_unary_layout_step sp ap p fid arg ty st ks ann : cm_task_layout sp ap p (CMLTask p fid (CMUnaryE 2 arg ty) st ks) ann -> cm_task_layout sp ap p (cm_lstart sp p fid (CMUnaryE 2 arg ty) st ks) (cm_update_annotation (cm_update_l sp ap p fid st ann (CMUnaryE 2 arg ty))).
Proof. intros [CODE SAVED]; split; [|exact SAVED]. cbn [cm_lstart cm_update_l cm_update_annotation cm_task_code] in *; unfold cm_emit_lvalue,cm_emit_rvalue,cm_expr_code_for in *; cbn [Z.eqb cm_emit_expr_pair cm_lcode_of cm_lvalue_code_count cm_expr_code_counts cm_lcount_of] in *; exact CODE. Qed.
