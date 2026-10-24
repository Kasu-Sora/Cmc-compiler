Require Export SimpleC.EE.QCP_demos_human.cmc_target_short_right_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_tvm_jnz obj pc value calls mem input output dest rest :
 tvm_targets_valid(tvm_object_code obj) -> cm_code_at(tvm_object_code obj)pc(TVMInst TVMJnzOp dest::rest) ->
 tvm_step(TVMRunTask obj(TVMState pc[value]calls mem input output))=
 TVMRunTask obj(TVMState(if value=?0 then pc+1 else dest)[]calls mem input output).
Proof.
 intros VALID CODE;pose proof(cm_code_at_target_valid _ _ TVMJnzOp _ _ VALID eq_refl CODE)as DEST.
 rewrite(cm_tvm_code_step obj(TVMState pc[value]calls mem input output)_ _ _ CODE).
 cbn[tvm_inst_step tvm_stack];change(1<=?Zlength[value])with true;cbv beta iota zeta delta [hd tl];rewrite DEST;destruct(value=?0);reflexivity.
Qed.
Lemma cm_tvm_short_begin obj pc value calls mem input output (is_or:bool) dest rest tail :
 tvm_targets_valid(tvm_object_code obj) ->
 cm_code_at(tvm_object_code obj)pc(TVMInst(if is_or then TVMJnzOp else TVMJzOp)dest::rest) ->
 cm_code_at(tvm_object_code obj)dest(TVMInst TVMPushOp(if is_or then 1 else 0)::tail) ->
 let short:=if is_or then negb(value=?0)else(value=?0) in
 tvm_iter(if short then 2 else 1)(TVMRunTask obj(TVMState pc[value]calls mem input output))=
 TVMRunTask obj(TVMState(if short then dest+1 else pc+1)(if short then[if is_or then 1 else 0]else[])calls mem input output).
Proof.
 intros VALID CODE PUSH;destruct is_or;cbn zeta;destruct(value=?0)eqn:ZERO;cbn[negb tvm_iter].
 - rewrite(cm_tvm_jnz _ _ _ _ _ _ _ _ _ VALID CODE),ZERO;reflexivity.
 - rewrite(cm_tvm_jnz _ _ _ _ _ _ _ _ _ VALID CODE),ZERO.
   rewrite(cm_tvm_push_step obj(TVMState dest[]calls mem input output)_ _ PUSH ltac:(change(0<65536);lia));reflexivity.
 - rewrite(cm_tvm_jz _ _ _ _ _ _ _ _ _ VALID CODE),ZERO.
   rewrite(cm_tvm_push_step obj(TVMState dest[]calls mem input output)_ _ PUSH ltac:(change(0<65536);lia));reflexivity.
 - rewrite(cm_tvm_jz _ _ _ _ _ _ _ _ _ VALID CODE),ZERO;reflexivity.
Qed.
Lemma cm_target_v_short_left_step sp ap p fid (is_or:bool) lhs rhs ty v st pc temp b c owner ob oc tail spills saved calls target :
 let op:=if is_or then 0 else 1 in
 let ann:=CMAnnotation pc temp b c(CMACursor(CABinLP op lhs rhs ty)owner ob oc::tail)spills saved calls in
 cm_semantic_wf_program(cm_source_function_policy sp)p ->
 cm_task_layout sp ap p(CMVTask p fid v st(cm_cursor_frames(cm_ann_cursors ann)))ann ->
 cm_task_target_sim (cm_source_function_policy sp)p(CMVTask p fid v st(cm_cursor_frames(cm_ann_cursors ann)))target ann ->
 cm_target_step_result sp ap p(CMVTask p fid v st(cm_cursor_frames(cm_ann_cursors ann)))target ann.
Proof.
 cbn zeta;intros WF[CODE SAVED][_ [vm[-> [PC SIM]]]];pose proof SIM as OLD.
 destruct vm as[vpc stack vcalls mem input output];cbn[tvm_pc cm_ann_pc]in PC;subst vpc.
 destruct SIM as[M[P[F[C[S[I[O STACK]]]]]]];change(stack=[cm_value_number st v])in STACK;subst stack.
 destruct is_or;cbn[cm_task_code cm_cont_code cm_cursor_code cm_cursor_phase cm_cursor_temp cm_cursor_break cm_cursor_continue cm_value_phase_code cm_phase_stops cm_ann_pc cm_ann_cursors Z.eqb Pos.eqb orb app]in CODE.
 all: pose proof(cm_code_at_tail _ _ _ _ CODE)as C1;repeat rewrite <-app_assoc in C1;apply cm_code_at_append_right in C1;rewrite cm_layout_rvalue_code_length in C1.
 all: pose proof(cm_code_at_tail _ _ _ _ C1)as C2;pose proof(cm_code_at_tail _ _ _ _ C2)as C3;pose proof(cm_code_at_tail _ _ _ _ C3)as C4.
 all: replace(pc+1+cm_rvalue_code_count(cm_source_function_policy sp)p fid rhs+1+1+1)with(pc+cm_rvalue_code_count(cm_source_function_policy sp)p fid rhs+4)in C4 by lia.
 all: match type of CODE with cm_code_at _ _ (TVMInst ?op ?dest::_)=>
 let isor:=eval cbv in(match op with TVMJnzOp=>true|_=>false end)in
 pose proof(cm_tvm_short_begin (cm_compile_model(cm_source_function_policy sp)p)pc(cm_value_number st v)vcalls mem input output isor dest _ _ (cm_model_jump_targets _ _ WF)CODE C4)as EXEC end.
 all: unfold cm_target_step_result;cbv beta iota zeta delta [cm_step cm_cursor_frames cm_cursor_phase cm_phase_frame map cm_ann_cursors cm_annotation_step cm_update_v cm_update_steps cm_update_annotation cm_vapply cm_truth cm_ann_pc hd orb andb];cbn[Z.eqb Pos.eqb orb andb].
 all: destruct(cm_value_number st v=?0)eqn:ZERO;cbn[negb]in EXEC|-*;rewrite EXEC;rewrite ?ZERO;cbn[negb].
 all: split;[reflexivity|];eexists;split;[reflexivity|split;[cbn[tvm_pc cm_ann_pc cm_ann_pop cm_ann_replace];lia|]].
 all: first[exact(cm_machine_sim_stack (cm_source_function_policy sp)p st _ _ _ [v][] [][] _ OLD)|exact(cm_machine_sim_stack (cm_source_function_policy sp)p st _ _ _ [v][] [CMIntV 0][] _ OLD)|exact(cm_machine_sim_stack (cm_source_function_policy sp)p st _ _ _ [v][] [CMIntV 1][] _ OLD)].
Qed.
