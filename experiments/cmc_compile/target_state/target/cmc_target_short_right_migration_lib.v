Require Export SimpleC.EE.QCP_demos_human.cmc_target_member_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_tvm_bool_pair obj pc value calls mem input output rest :
 cm_code_at(tvm_object_code obj)pc([TVMInst TVMPushOp 0;TVMInst TVMNeOp 0]++rest) ->
 tvm_iter 2(TVMRunTask obj(TVMState pc[value]calls mem input output))=
 TVMRunTask obj(TVMState(pc+2)[tower_bool(negb(value=?0))]calls mem input output).
Proof.
 intro CODE;cbn[app]in CODE;pose proof(cm_code_at_tail _ _ _ _ CODE)as C1.
 cbn[tvm_iter];rewrite(cm_tvm_push_step obj(TVMState pc[value]calls mem input output)_ _ CODE ltac:(change(1<65536);lia)).
 cbv beta iota zeta delta [tvm_next_state tvm_pc tvm_stack tvm_calls tvm_mem tvm_input tvm_output];change(tower_wrap64 0)with 0.
 rewrite(cm_tvm_code_step obj(TVMState(pc+1)[0;value]calls mem input output)_ _ _ C1).
 cbn[tvm_inst_step tvm_stack];change(2<=?Zlength[0;value])with true.
 cbv beta iota zeta delta [tvm_action_task tvm_next_state tvm_pc tvm_calls tvm_mem tvm_input tvm_output hd tl].
 f_equal;f_equal;lia.
Qed.
Lemma cm_tvm_short_finish obj pc value calls mem input output imm rest : tvm_targets_valid(tvm_object_code obj) ->
 cm_code_at(tvm_object_code obj)pc([TVMInst TVMPushOp 0;TVMInst TVMNeOp 0;TVMInst TVMJmpOp(pc+4);TVMInst TVMPushOp imm]++rest) ->
 tvm_iter 3(TVMRunTask obj(TVMState pc[value]calls mem input output))=
 TVMRunTask obj(TVMState(pc+4)[tower_bool(negb(value=?0))]calls mem input output).
Proof.
 intros VALID CODE;pose proof(cm_code_at_tail _ _ _ _ CODE)as C1;pose proof(cm_code_at_tail _ _ _ _ C1)as C2.
 replace(pc+1+1)with(pc+2)in C2 by lia.
 change(tvm_step(tvm_iter 2(TVMRunTask obj(TVMState pc[value]calls mem input output)))=TVMRunTask obj(TVMState(pc+4)[tower_bool(negb(value=?0))]calls mem input output)).
 rewrite(cm_tvm_bool_pair _ _ _ _ _ _ _ _ CODE);exact(cm_tvm_jmp _ _ _ _ _ _ _ _ _ VALID C2).
Qed.
Lemma cm_binary_short_number p st op left right ty : (op=0 \/ op=1) -> cm_frame_short_ready st(CMBinRK op left ty) ->
 cm_value_number st(cm_binary_value p op left right ty st)=tower_bool(cm_truth st right).
Proof.
 intros [-> | ->] [ZERO ONE];cbn[cm_binary_value Z.eqb Pos.eqb];[rewrite(ZERO eq_refl)|rewrite(ONE eq_refl)];cbn[orb andb cm_value_number];apply tower_wrap64_bool.
Qed.
Lemma cm_target_v_short_right_step sp ap p fid op lhs rhs left ty v st pc temp b c owner ob oc tail spills saved calls target :
 let ann:=CMAnnotation pc temp b c(CMACursor(CABinRP op lhs rhs left ty)owner ob oc::tail)spills saved calls in
 cm_semantic_wf_program(cm_source_function_policy sp)p -> (op=0 \/ op=1) -> cm_frame_short_ready st(CMBinRK op left ty) ->
 cm_task_layout sp ap p(CMVTask p fid v st(cm_cursor_frames(cm_ann_cursors ann)))ann ->
 cm_task_target_sim (cm_source_function_policy sp)p(CMVTask p fid v st(cm_cursor_frames(cm_ann_cursors ann)))target ann ->
 cm_target_step_result sp ap p(CMVTask p fid v st(cm_cursor_frames(cm_ann_cursors ann)))target ann.
Proof.
 cbn zeta;intros WF OPS SHORT[CODE SAVED][_ [vm[-> [PC SIM]]]];pose proof SIM as OLD.
 destruct vm as[vpc stack vcalls mem input output];cbn[tvm_pc cm_ann_pc]in PC;subst vpc.
 destruct SIM as[M[P[F[C[S[I[O STACK]]]]]]];change(stack=[cm_value_number st v])in STACK;subst stack.
 assert(OPS':((op=?0)||(op=?1))=true)by(destruct OPS as [-> | ->];reflexivity).
 cbn[cm_task_code cm_cont_code cm_cursor_code cm_cursor_phase cm_cursor_temp cm_cursor_break cm_cursor_continue cm_value_phase_code cm_phase_stops cm_ann_pc cm_ann_cursors]in CODE;rewrite OPS' in CODE.
 pose proof(cm_tvm_short_finish (cm_compile_model(cm_source_function_policy sp)p)pc(cm_value_number st v)vcalls mem input output _ _ (cm_model_jump_targets _ _ WF)CODE)as EXEC.
 assert(OK:cm_binary_ok p op left v st=true)by(destruct OPS as [-> | ->];reflexivity).
 unfold cm_target_step_result;cbn[cm_step cm_cursor_frames cm_cursor_phase cm_phase_frame map cm_ann_cursors cm_annotation_step cm_update_v cm_vapply];rewrite OK,OPS'.
 change(p=p /\ cm_running_target_sim (cm_source_function_policy sp)p fid st[cm_binary_value p op left v ty st]
 (cm_ann_pop ap(pc+4)(CMAnnotation pc temp b c(CMACursor(CABinRP op lhs rhs left ty)owner ob oc::tail)spills saved calls))
 (tvm_iter 3(TVMRunTask(cm_compile_model(cm_source_function_policy sp)p)(TVMState pc[cm_value_number st v]vcalls mem input output)))).
 rewrite EXEC;split;[reflexivity|];eexists;split;[reflexivity|split;[reflexivity|]].
 pose proof(cm_machine_sim_stack (cm_source_function_policy sp)p st _ _ _ [v][][cm_binary_value p op left v ty st][] (pc+4) OLD)as NEW.
 cbn[cm_encode_values map app]in NEW;rewrite(cm_binary_short_number _ _ _ _ _ _ OPS SHORT)in NEW;exact NEW.
Qed.
