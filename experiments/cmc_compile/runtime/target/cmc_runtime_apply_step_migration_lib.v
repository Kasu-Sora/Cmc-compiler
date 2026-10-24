Require Export SimpleC.EE.QCP_demos_human.cmc_runtime_apply_helpers_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_v_runtime_step sp ap p fid phase owner ob oc rest v st ann :
 cm_typed_program (cm_source_function_policy sp) p -> cm_ann_cursors ann=CMACursor phase owner ob oc::rest ->
 cm_frame_fid_ready p fid (cm_phase_frame phase) -> cm_cursors_budget (cm_source_function_policy sp) p fid (cm_ann_cursors ann) ->
 cm_annotation_child_ready (cm_source_function_policy sp) p fid ann ->
 cm_task_succeeds sp (cm_vapply sp p fid (cm_phase_frame phase) v st (cm_cursor_frames rest)) ->
 cm_runtime_core (cm_source_function_policy sp) ap p fid st ann ->
 cm_task_runtime_invariant (cm_source_function_policy sp) ap p (cm_vapply sp p fid (cm_phase_frame phase) v st (cm_cursor_frames rest)) (cm_update_annotation (cm_update_v sp ap p fid v st ann phase)).
Proof.
 intros WF CUR F B COORD S R; pose proof (proj1 R) as BEFORE.
 rewrite CUR in B; cbn [cm_cursors_budget cm_cursor_phase cm_cursor_temp] in B; destruct B as [B BT].
 unfold cm_annotation_child_ready in COORD; rewrite CUR in COORD; cbn [cm_cursors_coordinate cm_cursor_phase cm_cursor_temp] in COORD; destruct COORD as [TEMP COORD].
 destruct phase; cbn [cm_frame_fid_ready cm_phase_frame cm_phase_budget cm_phase_child_temp] in F,B,TEMP; cm_rt_conj B; cm_rt_conj F;
 cm_rt_reduce; try rewrite CUR; cm_rt_cases; try cm_rt_apply_finish.
 all: try solve [exact BEFORE].
 - eapply cm_runtime_core_enter_arg; [exact WF|lia|lia|exact CUR|assumption|exact R].

Qed.

Lemma cm_c_runtime_step sp ap p fid phase owner ob oc rest ctl st ann :
 cm_ann_cursors ann=CMACursor phase owner ob oc::rest ->
 cm_frame_fid_ready p fid (cm_phase_frame phase) ->
 cm_runtime_core (cm_source_function_policy sp) ap p fid st ann ->
 cm_task_runtime_invariant (cm_source_function_policy sp) ap p (cm_capply sp p fid (cm_phase_frame phase) ctl st (cm_cursor_frames rest)) (cm_update_annotation (cm_update_c sp ap p fid ctl st ann phase)).
Proof.
 intros CUR F R; pose proof (proj1 R) as BEFORE.
 destruct phase; cbn [cm_frame_fid_ready cm_phase_frame] in F; cm_rt_conj F;
 cm_rt_reduce; try rewrite CUR; cm_rt_cases; try cm_rt_apply_finish.
 all: try solve [exact BEFORE].
 all: exact R.
Qed.
