Require Export SimpleC.EE.QCP_demos_human.cmc_target_scope_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_target_c_while_step sp ap p fid ctl st guard body env regions loop_start loop_end pc temp owner ob oc tail spills saved calls target :
 let ann:=CMAnnotation pc temp loop_end loop_start(CMACursor(CAWhileBodyP guard body env regions loop_start loop_end)owner ob oc::tail)spills saved calls in
 cm_semantic_wf_program (cm_source_function_policy sp)p -> cm_control_kind ctl<>4 -> incl regions(cm_state_regions st) ->
 cm_task_layout sp ap p(CMCTask p fid ctl st(cm_cursor_frames(cm_ann_cursors ann)))ann ->
 cm_task_target_sim (cm_source_function_policy sp)p(CMCTask p fid ctl st(cm_cursor_frames(cm_ann_cursors ann)))target ann ->
 cm_target_step_result sp ap p(CMCTask p fid ctl st(cm_cursor_frames(cm_ann_cursors ann)))target ann.
Proof.
 cbn zeta;intros WF NE INC[CODE SAVED][_ SIM];destruct ctl;cbn[cm_control_kind]in NE;try contradiction.
 4,5: split;[reflexivity|exact(cm_running_restore_scope _ _ _ _ _ _ _ _ _ INC SIM)].
 all: destruct SIM as[vm[-> [PC OLD]]];destruct vm as[vpc stack vcalls mem input output];cbn[tvm_pc cm_ann_pc]in PC;subst vpc.
 all: assert(STACK:stack=[]);[destruct OLD as[_[_[_[_[_[_[_ H]]]]]]];exact H|subst stack].
 all: cbn[cm_task_code cm_control_phase_code cm_normal_cont_code cm_cursor_code cm_cursor_phase cm_cursor_temp cm_cursor_break cm_cursor_continue cm_normal_phase_code cm_normal_phase_stops cm_ann_pc cm_ann_cursors cm_ann_break cm_ann_continue cm_control_kind]in CODE.
 all: cbv beta iota zeta delta [cm_control_phase_code cm_control_kind cm_ann_temp cm_list_empty cm_normal_cont_code cm_cursor_code cm_cursor_phase cm_cursor_temp cm_cursor_break cm_cursor_continue cm_normal_phase_code cm_normal_phase_stops Z.eqb Pos.eqb orb] in CODE.
 all: cbn [app] in CODE.
 all: match type of CODE with cm_code_at _ _ (TVMInst TVMJmpOp ?dest::_)=>
 pose proof(cm_tvm_jmp (cm_compile_model(cm_source_function_policy sp)p)pc[]vcalls mem input output dest _ (cm_model_jump_targets _ _ WF)CODE)as EXEC end.
 all: unfold cm_target_step_result;cbv beta iota zeta delta [cm_step cm_cursor_frames cm_cursor_phase cm_phase_frame map cm_ann_cursors cm_annotation_step cm_update_c cm_control_kind Z.eqb Pos.eqb cm_update_steps cm_update_annotation tvm_iter cm_capply cm_ann_pc hd orb andb];rewrite EXEC.
 all: split;[reflexivity|];eexists;split;[reflexivity|split;[reflexivity|]];apply cm_machine_sim_restore_scope;[exact INC|].
 all: exact(cm_machine_sim_stack (cm_source_function_policy sp)p st _ _ _ [][] [][] _ OLD).
Qed.
