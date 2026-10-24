Require Export SimpleC.EE.QCP_demos_human.cmc_target_binary_code_migration_lib.
From Coq Require Import ZArith List Bool Lia.
From AUXLib Require Import ListLib.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_compatible_pointerb v ty : cm_value_type_compatible v ty -> cm_is_pointerb(cm_value_type v)=cm_pointerb ty.
Proof.
 destruct v,ty;cbv beta iota delta [cm_value_type_compatible cm_value_type cm_is_pointer cm_is_pointerb cm_pointerb];intros H;try reflexivity;intuition discriminate.
Qed.
Lemma cm_target_v_binary_numeric_step sp ap p fid v st op lhs rhs left ty pc temp b c owner ob oc tail spills saved calls target :
 let ann:=CMAnnotation pc temp b c(CMACursor(CABinRP op lhs rhs left ty)owner ob oc::tail)spills saved calls in
 cm_runtime_core(cm_source_function_policy sp)ap p fid st ann -> 0<=fid ->
 0<=owner<cm_temp_slots(cm_source_function_at sp fid p) -> cm_spill_holds owner left spills ->
 2<=op<=12 -> (op=8 \/ op=9 -> cm_pointerb(cm_expr_type lhs)=false /\ cm_pointerb(cm_expr_type rhs)=false) ->
 cm_value_type_compatible left(cm_expr_type lhs) ->cm_value_type_compatible v(cm_expr_type rhs) ->cm_binary_ok p op left v st=true ->
 cm_task_layout sp ap p(CMVTask p fid v st(cm_cursor_frames(cm_ann_cursors ann)))ann ->
 cm_task_target_sim(cm_source_function_policy sp)p(CMVTask p fid v st(cm_cursor_frames(cm_ann_cursors ann)))target ann ->
 cm_target_step_result sp ap p(CMVTask p fid v st(cm_cursor_frames(cm_ann_cursors ann)))target ann.
Proof.
 cbn zeta;intros RT FID SLOT HOLD BOUND SCALAR LTYPE RTYPE OK[CODE SAVED][_ [vm[-> [PC SIM]]]];pose proof SIM as OLD.
 destruct vm as[vpc stack vcalls mem input output];cbn[tvm_pc cm_ann_pc]in PC;subst vpc.
 destruct SIM as[M[P[F[C[[S SS][I[O STACK]]]]]]];change(stack=[cm_value_number st v])in STACK;subst stack;cbn[tvm_mem]in F.
 pose proof(cm_spill_sim_holds _ _ _ _ _ _ _ _ _ S HOLD)as WORD;cbn[tvm_mem cm_spill_frame_fid cm_spill_frame_fp]in WORD.
 pose proof(cm_runtime_temp_machine_safe _ _ _ _ _ _ _ _ _ _ _ _ (proj2 RT)FID SLOT)as[ADDR _];rewrite <-F in ADDR.
 assert(E0:(op=?0)=false)by(apply Z.eqb_neq;lia);assert(E1:(op=?1)=false)by(apply Z.eqb_neq;lia).
 cbn[cm_task_code cm_cont_code cm_cursor_code cm_cursor_phase cm_cursor_temp cm_cursor_break cm_cursor_continue cm_value_phase_code cm_phase_stops cm_ann_pc cm_ann_cursors]in CODE;rewrite E0,E1 in CODE;cbn[orb]in CODE.
 pose proof(cm_tvm_binary_numeric_tail (cm_source_function_policy sp)p fid op lhs rhs owner(cm_compile_model(cm_source_function_policy sp)p)pc(cm_value_number st v)vcalls mem input output _ SCALAR BOUND(cm_binary_divisor _ _ _ _ _ BOUND OK)ADDR CODE)as EXEC;rewrite F,WORD in EXEC.
 assert(LEN:Zlength(cm_binary_finish_code(cm_source_function_policy sp)p fid op lhs rhs owner)=7).
 { rewrite(cm_binary_finish_numeric _ _ _ _ _ _ _ SCALAR),Zlength_app,cm_layout_temp_load_length;reflexivity. }
 unfold cm_target_step_result;cbn[cm_step cm_cursor_frames cm_cursor_phase cm_phase_frame map cm_ann_cursors cm_annotation_step cm_update_v cm_vapply];rewrite OK,E0,E1;cbn[orb cm_update_steps cm_update_annotation hd cm_cursor_temp cm_cursor_phase cm_ann_pc cm_ann_cursors];rewrite LEN.
 change(p=p /\ cm_running_target_sim(cm_source_function_policy sp)p fid st[cm_binary_value p op left v ty st]
 (cm_ann_pop ap(pc+7)(CMAnnotation pc temp b c(CMACursor(CABinRP op lhs rhs left ty)owner ob oc::tail)spills saved calls))
 (tvm_iter(cm_code_steps(cm_binary_finish_code(cm_source_function_policy sp)p fid op lhs rhs owner))(TVMRunTask(cm_compile_model(cm_source_function_policy sp)p)(TVMState pc[cm_value_number st v]vcalls mem input output)))).
 rewrite EXEC;split;[reflexivity|];eexists;split;[reflexivity|split;[reflexivity|]].
 pose proof(cm_machine_sim_stack (cm_source_function_policy sp)p st _ _ _ [v][][cm_binary_value p op left v ty st][] (pc+7) OLD)as NEW.
 cbn[cm_encode_values map app]in NEW;rewrite(cm_binary_scalar_number _ _ _ _ _ _ BOUND ltac:(intros H;rewrite(cm_compatible_pointerb _ _ LTYPE),(cm_compatible_pointerb _ _ RTYPE);exact(SCALAR H)))in NEW;exact NEW.
Qed.
