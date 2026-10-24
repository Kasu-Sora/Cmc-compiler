Require Export SimpleC.EE.QCP_demos_human.cmc_target_io_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_target_s_structural_step sp ap p fid stmt st ks target ann :
 (match stmt with CMDeclS _ | CMInitS _ _=>False | _=>True end) ->
 cm_task_target_sim (cm_source_function_policy sp) p (CMSTask p fid stmt st ks) target ann ->
 cm_target_step_result sp ap p (CMSTask p fid stmt st ks) target ann.
Proof.
 intros GUARD [_ SIM]; destruct stmt; try contradiction;
 unfold cm_target_step_result; cbn [cm_step cm_sstart cm_annotation_step cm_update_s cm_update_annotation cm_update_steps tvm_iter cm_task_target_sim cm_control_kind Z.eqb].
 all: split; [reflexivity|exact SIM].
Qed.
Lemma cm_target_v_return_step sp ap p fid v st pc temp b c owner ob oc tail spills saved calls target :
 let ann:=CMAnnotation pc temp b c (CMACursor CAReturnP owner ob oc::tail) spills saved calls in
 cm_task_target_sim (cm_source_function_policy sp) p (CMVTask p fid v st (cm_cursor_frames(cm_ann_cursors ann))) target ann ->
 cm_target_step_result sp ap p (CMVTask p fid v st (cm_cursor_frames(cm_ann_cursors ann))) target ann.
Proof. exact(fun x=>x). Qed.
Lemma cm_target_c_sequence_step sp ap p fid ctl st second pc temp b c owner ob oc tail spills saved calls target :
 let ann:=CMAnnotation pc temp b c (CMACursor (CASeqP second) owner ob oc::tail) spills saved calls in
 cm_control_kind ctl<>4 ->
 cm_task_target_sim (cm_source_function_policy sp) p (CMCTask p fid ctl st (cm_cursor_frames(cm_ann_cursors ann))) target ann ->
 cm_target_step_result sp ap p (CMCTask p fid ctl st (cm_cursor_frames(cm_ann_cursors ann))) target ann.
Proof.
 cbn zeta; intros NE [_ SIM]; destruct ctl; try contradiction;
 unfold cm_target_step_result; cbn [cm_step cm_cursor_frames cm_phase_frame cm_cursor_phase map cm_annotation_step cm_update_c cm_update_annotation cm_update_steps tvm_iter cm_task_target_sim cm_control_kind cm_control_value Z.eqb Pos.eqb cm_ann_cursors cm_ann_pc hd].
 all: split; [reflexivity|exact SIM].
Qed.
Lemma cm_machine_sim_drop_active policy p fid st vm ann vals suffix :
 cm_machine_state_sim policy p st vm (cm_ann_calls ann) (cm_active_spill_frames fid st ann) vals suffix ->
 cm_machine_state_sim policy p st vm (cm_ann_calls ann) (cm_ann_saved ann) vals suffix.
Proof.
 intros [M [P [F [C [[ACTIVE SAVED] [I [O S]]]]]]]; unfold cm_machine_state_sim; do 7(split;[assumption|]); exact S.
Qed.
Lemma cm_target_exit_step sp ap p fid status st ks target ann :
 cm_task_target_sim (cm_source_function_policy sp) p (CMCTask p fid (CMExit status) st ks) target ann ->
 cm_target_step_result sp ap p (CMCTask p fid (CMExit status) st ks) target ann.
Proof.
 intros [_ [vm [-> [PC SIM]]]]; exists vm; split; [reflexivity|split;[exact PC|]].
 now apply cm_machine_sim_drop_active with(fid:=fid).
Qed.
