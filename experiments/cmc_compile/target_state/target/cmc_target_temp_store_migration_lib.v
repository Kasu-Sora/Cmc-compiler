Require Export SimpleC.EE.QCP_demos_human.cmc_target_temp_memory_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_target_temp_store_sim sp ap p fid st v slot ann target rest :
 cm_runtime_core(cm_source_function_policy sp)ap p fid st ann -> 0<=fid ->
 0<=slot<cm_temp_slots(cm_source_function_at sp fid p) -> cm_tagged_span_valid st ->
 cm_code_at(cm_model_code(cm_source_function_policy sp)p)(cm_ann_pc ann)(cm_temp_store_code(cm_source_function_policy sp)p fid slot++rest) ->
 cm_running_target_sim(cm_source_function_policy sp)p fid st[v]ann target ->
 cm_running_target_sim(cm_source_function_policy sp)p fid st[]
 (cm_ann_put_spill slot v(cm_ann_linear(cm_temp_store_code(cm_source_function_policy sp)p fid slot)ann))(tvm_iter 5 target).
Proof.
 intros RT FID SLOT TAG CODE[vm[-> [PC SIM]]];pose proof SIM as OLD.
 destruct vm as[vpc stack vcalls mem input output];cbn[tvm_pc]in PC;subst vpc.
 destruct SIM as[M[P[F[C[S[I[O STACK]]]]]]];change(stack=[cm_value_number st v])in STACK;subst stack.
 cbn[tvm_mem]in F;pose proof(cm_runtime_temp_machine_safe _ _ _ _ _ _ _ _ _ _ _ _ (proj2 RT)FID SLOT)as[ADDR _];rewrite <-F in ADDR.
 unfold cm_temp_store_code in CODE;rewrite <-app_assoc in CODE.
 pose proof(cm_tvm_fp_store (cm_compile_model(cm_source_function_policy sp)p)(cm_ann_pc ann)(cm_value_number st v)vcalls mem input output _ _ ADDR CODE)as EXEC.
 rewrite EXEC,F;eexists;split;[reflexivity|split;[reflexivity|]].
 exact(cm_machine_temp_store sp ap p fid st ann _ slot v (cm_ann_pc ann+5)RT FID SLOT TAG OLD).
Qed.
Lemma cm_target_v_assign_left_step sp ap p fid v st src ty pc temp b c owner ob oc tail spills saved calls target :
 let ann:=CMAnnotation pc temp b c(CMACursor(CAAssignLP src ty)owner ob oc::tail)spills saved calls in
 temp=owner -> cm_runtime_core(cm_source_function_policy sp)ap p fid st ann -> 0<=fid ->
 0<=temp<cm_temp_slots(cm_source_function_at sp fid p) -> cm_tagged_span_valid st ->
 cm_task_layout sp ap p(CMVTask p fid v st(cm_cursor_frames(cm_ann_cursors ann)))ann ->
 cm_task_target_sim(cm_source_function_policy sp)p(CMVTask p fid v st(cm_cursor_frames(cm_ann_cursors ann)))target ann ->
 cm_target_step_result sp ap p(CMVTask p fid v st(cm_cursor_frames(cm_ann_cursors ann)))target ann.
Proof.
 cbn zeta;intros -> RT FID SLOT TAG[CODE SAVED][_ SIM].
 cbn[cm_task_code cm_cont_code cm_cursor_code cm_cursor_phase cm_cursor_temp cm_cursor_break cm_cursor_continue cm_value_phase_code cm_phase_stops cm_ann_pc cm_ann_cursors]in CODE;repeat rewrite <-app_assoc in CODE.
 split;[reflexivity|];exact(cm_target_temp_store_sim sp ap p fid st v owner _ _ _ RT FID SLOT TAG CODE SIM).
Qed.
Lemma cm_target_v_index_left_step sp ap p fid v st index ty pc temp b c owner ob oc tail spills saved calls target :
 let ann:=CMAnnotation pc temp b c(CMACursor(CAIndexLP index ty)owner ob oc::tail)spills saved calls in
 temp=owner -> cm_runtime_core(cm_source_function_policy sp)ap p fid st ann -> 0<=fid ->
 0<=temp<cm_temp_slots(cm_source_function_at sp fid p) -> cm_tagged_span_valid st ->
 cm_task_layout sp ap p(CMVTask p fid v st(cm_cursor_frames(cm_ann_cursors ann)))ann ->
 cm_task_target_sim(cm_source_function_policy sp)p(CMVTask p fid v st(cm_cursor_frames(cm_ann_cursors ann)))target ann ->
 cm_target_step_result sp ap p(CMVTask p fid v st(cm_cursor_frames(cm_ann_cursors ann)))target ann.
Proof.
 cbn zeta;intros -> RT FID SLOT TAG[CODE SAVED][_ SIM].
 cbn[cm_task_code cm_cont_code cm_cursor_code cm_cursor_phase cm_cursor_temp cm_cursor_break cm_cursor_continue cm_value_phase_code cm_phase_stops cm_ann_pc cm_ann_cursors]in CODE;repeat rewrite <-app_assoc in CODE.
 split;[reflexivity|];exact(cm_target_temp_store_sim sp ap p fid st v owner _ _ _ RT FID SLOT TAG CODE SIM).
Qed.
Lemma cm_target_v_binary_left_step sp ap p fid op lhs rhs v st ty pc temp b c owner ob oc tail spills saved calls target :
 let ann:=CMAnnotation pc temp b c(CMACursor(CABinLP op lhs rhs ty)owner ob oc::tail)spills saved calls in
 op<>0 -> op<>1 -> temp=owner -> cm_runtime_core(cm_source_function_policy sp)ap p fid st ann -> 0<=fid ->
 0<=temp<cm_temp_slots(cm_source_function_at sp fid p) -> cm_tagged_span_valid st ->
 cm_task_layout sp ap p(CMVTask p fid v st(cm_cursor_frames(cm_ann_cursors ann)))ann ->
 cm_task_target_sim(cm_source_function_policy sp)p(CMVTask p fid v st(cm_cursor_frames(cm_ann_cursors ann)))target ann ->
 cm_target_step_result sp ap p(CMVTask p fid v st(cm_cursor_frames(cm_ann_cursors ann)))target ann.
Proof.
 cbn zeta;intros NZ NO -> RT FID SLOT TAG[CODE SAVED][_ SIM].
 apply Z.eqb_neq in NZ,NO.
 cbn[cm_task_code cm_cont_code cm_cursor_code cm_cursor_phase cm_cursor_temp cm_cursor_break cm_cursor_continue cm_value_phase_code cm_phase_stops cm_ann_pc cm_ann_cursors]in CODE;rewrite NZ,NO in CODE;cbn[orb]in CODE;repeat rewrite <-app_assoc in CODE.
 unfold cm_target_step_result;cbn[cm_step cm_cursor_frames cm_cursor_phase cm_phase_frame map cm_ann_cursors cm_annotation_step cm_update_v cm_vapply];rewrite NZ,NO;cbn[orb andb].
 split;[reflexivity|];exact(cm_target_temp_store_sim sp ap p fid st v owner _ _ _ RT FID SLOT TAG CODE SIM).
Qed.
Lemma cm_target_v_arg_cons_step sp ap p fid callee arg args values ty all_args base current scratch v st pc temp b c owner ob oc tail spills saved calls target :
 let ann:=CMAnnotation pc temp b c(CMACursor(CAArgP callee(arg::args)values ty all_args base current scratch)owner ob oc::tail)spills saved calls in
 cm_runtime_core(cm_source_function_policy sp)ap p fid st ann -> 0<=fid ->
 0<=current<cm_temp_slots(cm_source_function_at sp fid p) -> cm_tagged_span_valid st ->
 cm_task_layout sp ap p(CMVTask p fid v st(cm_cursor_frames(cm_ann_cursors ann)))ann ->
 cm_task_target_sim(cm_source_function_policy sp)p(CMVTask p fid v st(cm_cursor_frames(cm_ann_cursors ann)))target ann ->
 cm_target_step_result sp ap p(CMVTask p fid v st(cm_cursor_frames(cm_ann_cursors ann)))target ann.
Proof.
 cbn zeta;intros RT FID SLOT TAG[CODE SAVED][_ SIM].
 cbn[cm_task_code cm_cont_code cm_cursor_code cm_cursor_phase cm_cursor_temp cm_cursor_break cm_cursor_continue cm_value_phase_code cm_phase_stops cm_ann_pc cm_ann_cursors]in CODE;repeat rewrite <-app_assoc in CODE.
 split;[reflexivity|];exact(cm_target_temp_store_sim sp ap p fid st v current _ _ _ RT FID SLOT TAG CODE SIM).
Qed.
