Require Export SimpleC.EE.QCP_demos_human.cmc_code_stmt_flow_migration_lib.
From Coq Require Import ZArith List Bool Lia.
From AUXLib Require Import ListLib.
Import ListNotations.
Local Open Scope Z_scope.
Ltac cm_code_value_reduce := cbv beta iota zeta delta [cm_task_layout cm_task_code cm_task_fid cm_vapply cm_phase_frame cm_update_v cm_update_annotation cm_ann_pop cm_ann_replace cm_ann_put_spill cm_ann_spills_set cm_ann_pc cm_ann_temp cm_ann_break cm_ann_continue cm_ann_cursors cm_ann_spills cm_ann_saved cm_ann_calls cm_cursor_phase cm_cursor_temp cm_cursor_break cm_cursor_continue hd tl] in *; rewrite ?cm_normal_control_code; cbn [cm_cont_code cm_normal_cont_code cm_cursor_code cm_cursor_phase cm_cursor_temp cm_cursor_break cm_cursor_continue cm_value_phase_code cm_normal_phase_code cm_phase_stops cm_normal_phase_stops cm_phase_yields_normal cm_saved_layout cm_phase_site cm_phase_is_call orb] in *.
Lemma cm_value_layout_tail sp ap p fid v st ks pc temp b c phase owner ob oc tail spills saved calls :
 cm_phase_stops phase=false -> cm_phase_is_call phase=false ->
 cm_task_layout sp ap p (CMVTask p fid v st ks) (CMAnnotation pc temp b c (CMACursor phase owner ob oc::tail) spills saved calls) ->
 cm_code_at (cm_model_code (cm_source_function_policy sp) p) (pc+Zlength(cm_value_phase_code sp p fid pc temp owner ob oc phase)) (cm_cursor_code sp p fid (pc+Zlength(cm_value_phase_code sp p fid pc temp owner ob oc phase)) owner (cm_phase_yields_normal phase) tail) /\ cm_saved_layout sp ap p (cm_model_code(cm_source_function_policy sp) p) fid tail calls.
Proof.
 intros STOP CALL [CODE [_ SAVED]]; cbn [cm_task_code cm_cont_code cm_cursor_code cm_ann_pc cm_ann_temp cm_ann_cursors cm_cursor_phase cm_cursor_temp cm_cursor_break cm_cursor_continue] in CODE; rewrite STOP in CODE; cbn [orb] in CODE.
 cbn [cm_cursor_phase] in SAVED; rewrite CALL in SAVED; split; [now apply cm_code_at_append_right in CODE|exact SAVED].
Qed.
Lemma cm_code_at_empty {A} (code:list A) pc : 0<=pc<=Zlength code -> cm_code_at code pc [].
Proof.
 intros [LO HI]; exists (firstn (Z.to_nat pc) code),(skipn (Z.to_nat pc) code); split.
 - cbn; symmetry; apply firstn_skipn.
 - rewrite Zlength_correct,firstn_length,Nat.min_l; [now rewrite Z2Nat.id|rewrite Zlength_correct in HI; lia].
Qed.
Lemma cm_error_control_code sp p fid pc temp b c status cursors : cm_control_phase_code sp p fid pc temp b c (CMError status) cursors=cm_normal_cont_code sp p fid pc temp cursors.
Proof. destruct cursors; reflexivity. Qed.
Lemma cm_layout_exit_empty sp ap p fid status st ks ann : cm_saved_layout sp ap p (cm_model_code(cm_source_function_policy sp) p) fid (cm_ann_cursors ann) (cm_ann_calls ann) -> 0<=cm_ann_pc ann<=Zlength(cm_model_code(cm_source_function_policy sp) p) -> cm_task_layout sp ap p (CMCTask p fid (CMExit status) st ks) ann.
Proof.
 intros S B; split; [|exact S]. cbn [cm_task_code cm_control_phase_code cm_control_kind Z.eqb Pos.eqb orb].
 apply cm_code_at_empty; exact B.
Qed.
