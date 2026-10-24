Require Export SimpleC.EE.QCP_demos_human.cmc_target_normalize_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_target_v_halt_step sp ap p fid v st pc temp b c owner ob oc tail spills saved calls target :
 let ann:=CMAnnotation pc temp b c(CMACursor CAHaltP owner ob oc::tail)spills saved calls in
 cm_task_layout sp ap p(CMVTask p fid v st(cm_cursor_frames(cm_ann_cursors ann)))ann ->
 cm_task_target_sim (cm_source_function_policy sp)p(CMVTask p fid v st(cm_cursor_frames(cm_ann_cursors ann)))target ann ->
 cm_target_step_result sp ap p(CMVTask p fid v st(cm_cursor_frames(cm_ann_cursors ann)))target ann.
Proof.
 cbn zeta;intros[CODE SAVED][_ [vm[-> [PC SIM]]]];pose proof SIM as OLD.
 destruct vm as[vpc stack vcalls mem input output];cbn[tvm_pc cm_ann_pc]in PC;subst vpc.
 destruct SIM as[M[P[F[C[S[I[O STACK]]]]]]];change(stack=[cm_value_number st v])in STACK;subst stack.
 assert(CODE':cm_code_at(tvm_object_code(cm_compile_model(cm_source_function_policy sp)p))pc cm_status_tail_code).
 { cbn[cm_task_code cm_cont_code cm_cursor_code cm_cursor_phase cm_cursor_temp cm_cursor_break cm_cursor_continue cm_value_phase_code cm_phase_stops cm_ann_pc cm_ann_cursors]in CODE;rewrite app_nil_r in CODE;exact CODE. }
 pose proof(cm_tvm_status_tail _ pc (cm_value_number st v) vcalls mem input output CODE')as EXEC.
 change(cm_halted_target_sim (cm_source_function_policy sp)p(-1)st(tower_status(cm_value_number st v))false
 (cm_ann_pop ap(pc+6)(CMAnnotation pc temp b c(CMACursor CAHaltP owner ob oc::tail)spills saved calls))
 (tvm_iter 7(TVMRunTask(cm_compile_model(cm_source_function_policy sp)p)(TVMState pc[cm_value_number st v]vcalls mem input output)))).
 rewrite EXEC;eexists;split;[reflexivity|split;[reflexivity|]].
 apply cm_machine_sim_drop_active with(fid:=fid)(ann:=CMAnnotation pc temp b c(CMACursor CAHaltP owner ob oc::tail)spills saved calls).
 exact(cm_machine_sim_stack (cm_source_function_policy sp)p st _ _ _ [v][] [][] (pc+6) OLD).
Qed.
Lemma cm_target_v_exit_step sp ap p fid v st pc temp b c owner ob oc tail spills saved calls target :
 let ann:=CMAnnotation pc temp b c(CMACursor CAExitP owner ob oc::tail)spills saved calls in
 cm_task_layout sp ap p(CMVTask p fid v st(cm_cursor_frames(cm_ann_cursors ann)))ann ->
 cm_task_target_sim (cm_source_function_policy sp)p(CMVTask p fid v st(cm_cursor_frames(cm_ann_cursors ann)))target ann ->
 cm_target_step_result sp ap p(CMVTask p fid v st(cm_cursor_frames(cm_ann_cursors ann)))target ann.
Proof.
 cbn zeta;intros[CODE SAVED][_ [vm[-> [PC SIM]]]];pose proof SIM as OLD.
 destruct vm as[vpc stack vcalls mem input output];cbn[tvm_pc cm_ann_pc]in PC;subst vpc.
 destruct SIM as[M[P[F[C[S[I[O STACK]]]]]]];change(stack=[cm_value_number st v])in STACK;subst stack.
 assert(CODE':cm_code_at(tvm_object_code(cm_compile_model(cm_source_function_policy sp)p))pc cm_status_tail_code).
 { cbn[cm_task_code cm_cont_code cm_cursor_code cm_cursor_phase cm_cursor_temp cm_cursor_break cm_cursor_continue cm_value_phase_code cm_phase_stops cm_ann_pc cm_ann_cursors]in CODE;rewrite app_nil_r in CODE;exact CODE. }
 pose proof(cm_tvm_status_tail _ pc (cm_value_number st v) vcalls mem input output CODE')as EXEC.
 change(p=p /\ cm_halted_target_sim (cm_source_function_policy sp)p fid st(tower_status(cm_value_number st v))true
 (cm_ann_pop ap(pc+6)(CMAnnotation pc temp b c(CMACursor CAExitP owner ob oc::tail)spills saved calls))
 (tvm_iter 7(TVMRunTask(cm_compile_model(cm_source_function_policy sp)p)(TVMState pc[cm_value_number st v]vcalls mem input output)))).
 rewrite EXEC;split;[reflexivity|];eexists;split;[reflexivity|split;[reflexivity|]].
 exact(cm_machine_sim_stack (cm_source_function_policy sp)p st _ _ _ [v][] [][] (pc+6) OLD).
Qed.
