Require Export SimpleC.EE.QCP_demos_human.cmc_target_jump_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_target_v_if_step sp ap p fid v st yes no pc temp b c owner ob oc tail spills saved calls target :
 let ann:=CMAnnotation pc temp b c (CMACursor (CAIfP yes no) owner ob oc::tail) spills saved calls in
 cm_semantic_wf_program (cm_source_function_policy sp)p ->
 cm_task_layout sp ap p (CMVTask p fid v st (cm_cursor_frames(cm_ann_cursors ann))) ann ->
 cm_task_target_sim (cm_source_function_policy sp) p (CMVTask p fid v st (cm_cursor_frames(cm_ann_cursors ann))) target ann ->
 cm_target_step_result sp ap p (CMVTask p fid v st (cm_cursor_frames(cm_ann_cursors ann))) target ann.
Proof.
 cbn zeta; intros WF [CODE SAVED] [_ [vm [-> [PC SIM]]]]; pose proof SIM as OLD.
 destruct vm as [vpc stack vcalls mem input output]; cbn [tvm_pc cm_ann_pc]in PC; subst vpc.
 destruct SIM as [M [P [F [C [S [I [O STACK]]]]]]]; change(stack=[cm_value_number st v])in STACK; subst stack.
 pose proof(cm_tvm_jz (cm_compile_model(cm_source_function_policy sp)p) pc (cm_value_number st v) vcalls mem input output (pc+1+cm_stmt_code_count(cm_source_function_policy sp)p fid yes+1) _ (cm_model_jump_targets _ _ WF) CODE)as EXEC.
 replace(pc+1+cm_stmt_code_count(cm_source_function_policy sp)p fid yes+1)with(pc+2+cm_stmt_code_count(cm_source_function_policy sp)p fid yes)in EXEC by lia.
 unfold cm_target_step_result; cbv beta iota zeta delta [cm_step cm_cursor_frames map cm_phase_frame cm_cursor_phase cm_ann_cursors cm_annotation_step cm_update_v cm_update_steps cm_update_annotation cm_vapply cm_truth cm_ann_pc hd].
 destruct(cm_value_number st v=?0)eqn:ZERO; cbn [negb cm_task_target_sim cm_control_kind Z.eqb Pos.eqb tvm_iter]; rewrite EXEC; rewrite ?ZERO.
 all: split;[reflexivity|].
 all: eexists; split;[reflexivity|split;[reflexivity|]]; exact(cm_machine_sim_stack (cm_source_function_policy sp)p st _ _ _ [v][] [][] _ OLD).
Qed.
Lemma cm_target_v_while_guard_step sp ap p fid v st guard body loop_start loop_end pc temp b c owner ob oc tail spills saved calls target :
 let ann:=CMAnnotation pc temp b c (CMACursor (CAWhileGuardP guard body loop_start loop_end) owner ob oc::tail) spills saved calls in
 cm_semantic_wf_program (cm_source_function_policy sp)p ->
 cm_task_layout sp ap p (CMVTask p fid v st (cm_cursor_frames(cm_ann_cursors ann))) ann ->
 cm_task_target_sim (cm_source_function_policy sp) p (CMVTask p fid v st (cm_cursor_frames(cm_ann_cursors ann))) target ann ->
 cm_target_step_result sp ap p (CMVTask p fid v st (cm_cursor_frames(cm_ann_cursors ann))) target ann.
Proof.
 cbn zeta; intros WF [CODE SAVED] [_ [vm [-> [PC SIM]]]]; pose proof SIM as OLD.
 destruct vm as [vpc stack vcalls mem input output]; cbn [tvm_pc cm_ann_pc]in PC; subst vpc.
 destruct SIM as [M [P [F [C [S [I [O STACK]]]]]]]; change(stack=[cm_value_number st v])in STACK; subst stack.
 pose proof(cm_tvm_jz (cm_compile_model(cm_source_function_policy sp)p) pc (cm_value_number st v) vcalls mem input output (loop_end) _ (cm_model_jump_targets _ _ WF) CODE)as EXEC.
 unfold cm_target_step_result; cbv beta iota zeta delta [cm_step cm_cursor_frames map cm_phase_frame cm_cursor_phase cm_ann_cursors cm_annotation_step cm_update_v cm_update_steps cm_update_annotation cm_vapply cm_truth cm_ann_pc hd].
 destruct(cm_value_number st v=?0)eqn:ZERO; cbn [negb cm_task_target_sim cm_control_kind Z.eqb Pos.eqb tvm_iter]; rewrite EXEC; rewrite ?ZERO.
 all: split;[reflexivity|].
 all: eexists; split;[reflexivity|split;[reflexivity|]]; exact(cm_machine_sim_stack (cm_source_function_policy sp)p st _ _ _ [v][] [][] _ OLD).
Qed.
