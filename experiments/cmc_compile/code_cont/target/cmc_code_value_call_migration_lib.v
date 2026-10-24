Require Export SimpleC.EE.QCP_demos_human.cmc_code_value_branch_migration_lib.
From Coq Require Import ZArith List Bool Lia.
From AUXLib Require Import ListLib.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_v_arg_cons_layout_step sp ap p fid v st callee arg args values ret all_args base current scratch pc temp b c owner ob oc tail spills saved calls :
 let phase:=CAArgP callee (arg::args) values ret all_args base current scratch in
 let ann:=CMAnnotation pc temp b c (CMACursor phase owner ob oc::tail) spills saved calls in
 cm_task_layout sp ap p (CMVTask p fid v st (cm_cursor_frames(cm_ann_cursors ann))) ann ->
 cm_task_layout sp ap p (cm_vapply sp p fid (cm_phase_frame phase) v st (cm_cursor_frames tail)) (cm_update_annotation(cm_update_v sp ap p fid v st ann phase)).
Proof.
 cbn zeta; intros [CODE [_ SAVED]]; cm_code_value_reduce; cbn [cm_list_empty]; cm_code_value_reduce; split; [|split; [exact I|exact SAVED]].
 repeat rewrite <-app_assoc in CODE; apply cm_code_at_append_right in CODE.
 cbn [cm_emit_args_store] in CODE; cm_code_layout_lengths; repeat rewrite cm_layout_temp_store_length in *.
 change (cm_expr_code_for (cm_source_function_policy sp) p fid (pc+5) scratch arg 0) with (cm_emit_rvalue (cm_source_function_policy sp) p fid (pc+5) scratch arg) in CODE.
 cm_code_layout_lengths; cm_code_layout_equal CODE.
Qed.
Lemma cm_v_arg_nil_layout_step sp ap p fid v st callee values ret all_args base current scratch pc temp b c owner ob oc tail spills saved calls :
 let phase:=CAArgP callee [] values ret all_args base current scratch in
 let ann:=CMAnnotation pc temp b c (CMACursor phase owner ob oc::tail) spills saved calls in
 cm_call_ok sp p callee (rev(v::values)) st=true -> cm_call_depth(cm_cursor_frames tail)<65536 ->
 cm_task_layout sp ap p (CMVTask p fid v st (cm_cursor_frames(cm_ann_cursors ann))) ann ->
 cm_task_layout sp ap p (cm_vapply sp p fid (cm_phase_frame phase) v st (cm_cursor_frames tail)) (cm_update_annotation(cm_update_v sp ap p fid v st ann phase)).
Proof.
 cbn zeta; intros OK DEPTH [CODE [_ SAVED]]; pose proof(cm_call_ok_fid_bounds _ _ _ _ _ OK)as B; apply Z.ltb_lt in DEPTH.
 cbv beta iota zeta delta [cm_vapply cm_phase_frame cm_update_v cm_list_empty cm_begin_call cm_ann_cursors tl]; rewrite OK,DEPTH; cbn [andb cm_update_annotation cm_ann_pc cm_ann_temp cm_ann_break cm_ann_continue cm_ann_spills cm_ann_saved cm_ann_calls hd cm_cursor_temp cm_cursor_break cm_cursor_continue].
 eapply cm_layout_enter_call with(values:=rev(v::values)); [exact B| |exact SAVED].
 cbn [cm_task_code cm_cont_code cm_cursor_code cm_ann_pc cm_ann_temp cm_ann_cursors cm_cursor_phase cm_cursor_temp cm_cursor_break cm_cursor_continue cm_value_phase_code cm_phase_stops cm_phase_yields_normal cm_emit_args_store orb] in CODE.
 apply cm_code_at_append_right in CODE; cm_code_layout_lengths; cm_code_layout_equal CODE.
Qed.
