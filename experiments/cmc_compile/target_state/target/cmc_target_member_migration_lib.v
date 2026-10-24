Require Export SimpleC.EE.QCP_demos_human.cmc_target_stmt_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma tower_wrap64_add_left a b : tower_wrap64(tower_wrap64 a+b)=tower_wrap64(a+b).
Proof. rewrite Z.add_comm,tower_wrap64_add_right,Z.add_comm;reflexivity. Qed.
Lemma cm_ptr_member_number_bridge sp p st ptr ty mid : cm_value_type_compatible ptr ty -> cm_ptr_member_ok sp p ptr mid st=true ->
 cm_value_number st(cm_ptr_member sp p ptr mid)=tower_add(cm_value_number st ptr)(cm_member_offset(cm_program_structs p)(cm_struct_id(cm_pointee ty))mid).
Proof.
 intros TYPE OK;unfold cm_ptr_member_ok in OK;repeat rewrite andb_true_iff in OK;destruct OK as[[[LIVE _]_]_].
 destruct ptr;cbn[cm_pointer_live cm_ptr_gen]in LIVE;try discriminate.
 destruct TYPE as[TYPE|[BAD _]];[|discriminate];cbn[cm_value_type]in TYPE;subst ty.
 cbn[cm_ptr_member cm_ptr_gen cm_ptr_offset cm_ptr_view cm_value_number cm_pointee];unfold tower_add;
 rewrite tower_wrap64_add_left;f_equal;ring.
Qed.
Lemma cm_tvm_add_immediate obj pc value calls mem input output imm rest :
 cm_code_at(tvm_object_code obj)pc([TVMInst TVMPushOp imm;TVMInst TVMAddOp 0]++rest) ->
 tvm_iter 2(TVMRunTask obj(TVMState pc[value]calls mem input output))=
 TVMRunTask obj(TVMState(pc+2)[tower_add value imm]calls mem input output).
Proof.
 intro CODE;cbn[app]in CODE;pose proof(cm_code_at_tail _ _ _ _ CODE)as C1.
 cbn[tvm_iter];rewrite(cm_tvm_push_step obj(TVMState pc[value]calls mem input output)_ _ CODE ltac:(change(1<65536);lia)).
 cbv beta iota zeta delta [tvm_next_state tvm_pc tvm_stack tvm_calls tvm_mem tvm_input tvm_output].
 rewrite(cm_tvm_code_step obj(TVMState(pc+1)[tower_wrap64 imm;value]calls mem input output)_ _ _ C1).
 cbn[tvm_inst_step tvm_stack];change(2<=?Zlength[tower_wrap64 imm;value])with true.
 cbv beta iota zeta delta [tvm_action_task tvm_next_state tvm_pc tvm_calls tvm_mem tvm_input tvm_output hd tl].
 unfold tower_add;rewrite tower_wrap64_add_right;f_equal;f_equal;lia.
Qed.
Lemma cm_target_v_member_step sp ap p fid v st mid ty pc temp b c owner ob oc tail spills saved calls target :
 let ann:=CMAnnotation pc temp b c(CMACursor(CAMemberP mid ty)owner ob oc::tail)spills saved calls in
 cm_value_type_compatible v ty -> cm_ptr_member_ok sp p v mid st=true ->
 cm_task_layout sp ap p(CMVTask p fid v st(cm_cursor_frames(cm_ann_cursors ann)))ann ->
 cm_task_target_sim (cm_source_function_policy sp)p(CMVTask p fid v st(cm_cursor_frames(cm_ann_cursors ann)))target ann ->
 cm_target_step_result sp ap p(CMVTask p fid v st(cm_cursor_frames(cm_ann_cursors ann)))target ann.
Proof.
 cbn zeta;intros TYPE OK[CODE SAVED][_ [vm[-> [PC SIM]]]];pose proof SIM as OLD.
 destruct vm as[vpc stack vcalls mem input output];cbn[tvm_pc cm_ann_pc]in PC;subst vpc.
 destruct SIM as[M[P[F[C[S[I[O STACK]]]]]]];change(stack=[cm_value_number st v])in STACK;subst stack.
 cbn[cm_task_code cm_cont_code cm_cursor_code cm_cursor_phase cm_cursor_temp cm_cursor_break cm_cursor_continue cm_value_phase_code cm_phase_stops cm_ann_pc cm_ann_cursors]in CODE.
 pose proof(cm_tvm_add_immediate (cm_compile_model(cm_source_function_policy sp)p)pc(cm_value_number st v)vcalls mem input output _ _ CODE)as EXEC.
 unfold cm_target_step_result;cbn[cm_step cm_cursor_frames cm_cursor_phase cm_phase_frame map cm_ann_cursors cm_annotation_step cm_update_v cm_vapply];rewrite OK.
 change(p=p /\ cm_running_target_sim (cm_source_function_policy sp)p fid st[cm_ptr_member sp p v mid]
 (cm_ann_pop ap(pc+2)(CMAnnotation pc temp b c(CMACursor(CAMemberP mid ty)owner ob oc::tail)spills saved calls))
 (tvm_iter 2(TVMRunTask(cm_compile_model(cm_source_function_policy sp)p)(TVMState pc[cm_value_number st v]vcalls mem input output)))).
 rewrite EXEC;split;[reflexivity|];eexists;split;[reflexivity|split;[reflexivity|]].
 pose proof(cm_machine_sim_stack (cm_source_function_policy sp)p st _ _ _ [v][][cm_ptr_member sp p v mid][] (pc+2) OLD)as NEW.
 cbn[cm_encode_values map app]in NEW;rewrite(cm_ptr_member_number_bridge _ _ _ _ _ _ TYPE OK)in NEW;exact NEW.
Qed.
