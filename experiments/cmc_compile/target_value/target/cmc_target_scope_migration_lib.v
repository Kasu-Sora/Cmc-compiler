Require Export SimpleC.EE.QCP_demos_human.cmc_target_scope_memory_migration_lib.
Require Export SimpleC.EE.QCP_demos_human.cmc_target_branch_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_running_restore_scope policy p fid st env old vals ann target : incl old(cm_state_regions st) ->
 cm_running_target_sim policy p fid st vals ann target ->
 cm_running_target_sim policy p fid(cm_restore_scope st env old)vals ann target.
Proof.
 intros INC[vm[EQ[PC SIM]]];exists vm;split;[exact EQ|split;[exact PC|]];
 now apply cm_machine_sim_restore_scope.
Qed.
Lemma cm_target_c_block_step sp ap p fid ctl st env regions jump dest pc temp b c owner ob oc tail spills saved calls target :
 let ann:=CMAnnotation pc temp b c(CMACursor(CABlockP env regions jump dest)owner ob oc::tail)spills saved calls in
 cm_semantic_wf_program (cm_source_function_policy sp)p -> cm_control_kind ctl<>4 -> incl regions(cm_state_regions st) ->
 cm_task_layout sp ap p(CMCTask p fid ctl st(cm_cursor_frames(cm_ann_cursors ann)))ann ->
 cm_task_target_sim (cm_source_function_policy sp)p(CMCTask p fid ctl st(cm_cursor_frames(cm_ann_cursors ann)))target ann ->
 cm_target_step_result sp ap p(CMCTask p fid ctl st(cm_cursor_frames(cm_ann_cursors ann)))target ann.
Proof.
 cbn zeta;intros WF NE INC[CODE SAVED][_ SIM];destruct ctl;cbn[cm_control_kind]in NE;try contradiction.
 - destruct jump.
   + destruct SIM as[vm[-> [PC OLD]]];destruct vm as[vpc stack vcalls mem input output];cbn[tvm_pc cm_ann_pc]in PC;subst vpc.
     assert(STACK:stack=[]).
     { destruct OLD as[_[_[_[_[_[_[_ H]]]]]]];exact H. }
     subst stack.
     cbn[cm_task_code cm_control_phase_code cm_normal_cont_code cm_cursor_code cm_cursor_phase cm_cursor_temp cm_cursor_break cm_cursor_continue cm_normal_phase_code cm_normal_phase_stops cm_ann_pc cm_ann_cursors cm_control_kind]in CODE.
     pose proof(cm_tvm_jmp (cm_compile_model(cm_source_function_policy sp)p)pc[]vcalls mem input output dest _ (cm_model_jump_targets _ _ WF)CODE)as EXEC.
     change(p=p /\ cm_running_target_sim (cm_source_function_policy sp)p fid(cm_restore_scope st env regions)[]
       (cm_ann_pop ap dest(CMAnnotation pc temp b c(CMACursor(CABlockP env regions true dest)owner ob oc::tail)spills saved calls))
       (tvm_step(TVMRunTask(cm_compile_model(cm_source_function_policy sp)p)(TVMState pc[]vcalls mem input output)))).
     rewrite EXEC;split;[reflexivity|];eexists;split;[reflexivity|split;[reflexivity|]].
     apply cm_machine_sim_restore_scope;[exact INC|];exact(cm_machine_sim_stack (cm_source_function_policy sp)p st _ _ _ [][] [][] dest OLD).
   + split;[reflexivity|];exact(cm_running_restore_scope _ _ _ _ _ _ _ _ _ INC SIM).
 - split;[reflexivity|];exact(cm_running_restore_scope _ _ _ _ _ _ _ _ _ INC SIM).
 - split;[reflexivity|];exact(cm_running_restore_scope _ _ _ _ _ _ _ _ _ INC SIM).
 - split;[reflexivity|];exact(cm_running_restore_scope _ _ _ _ _ _ _ _ _ INC SIM).
 - split;[reflexivity|];exact(cm_running_restore_scope _ _ _ _ _ _ _ _ _ INC SIM).
Qed.
