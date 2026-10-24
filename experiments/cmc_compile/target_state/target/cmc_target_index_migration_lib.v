Require Export SimpleC.EE.QCP_demos_human.cmc_target_index_code_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_target_v_index_right_step sp ap p fid v st base ty pc temp b c owner ob oc tail spills saved calls target :
 let ann:=CMAnnotation pc temp b c(CMACursor(CAIndexRP base ty)owner ob oc::tail)spills saved calls in
 cm_runtime_core(cm_source_function_policy sp)ap p fid st ann -> 0<=fid ->
 0<=owner<cm_temp_slots(cm_source_function_at sp fid p) -> cm_spill_holds owner base spills ->
 cm_value_type_compatible base(CMPtrTy ty) -> cm_ptr_shift_ok(cm_program_structs p)base(cm_value_number st v)st=true ->
 cm_task_layout sp ap p(CMVTask p fid v st(cm_cursor_frames(cm_ann_cursors ann)))ann ->
 cm_task_target_sim(cm_source_function_policy sp)p(CMVTask p fid v st(cm_cursor_frames(cm_ann_cursors ann)))target ann ->
 cm_target_step_result sp ap p(CMVTask p fid v st(cm_cursor_frames(cm_ann_cursors ann)))target ann.
Proof.
 cbn zeta;intros RT FID SLOT HOLD TYPE OK[CODE SAVED][_ [vm[-> [PC SIM]]]];pose proof SIM as OLD.
 destruct vm as[vpc stack vcalls mem input output];cbn[tvm_pc cm_ann_pc]in PC;subst vpc.
 destruct SIM as[M[P[F[C[[S SS][I[O STACK]]]]]]];change(stack=[cm_value_number st v])in STACK;subst stack.
 cbn[tvm_mem]in F;pose proof(cm_spill_sim_holds _ _ _ _ _ _ _ _ _ S HOLD)as WORD;cbn[tvm_mem cm_spill_frame_fp cm_spill_frame_fid]in WORD.
 pose proof(cm_runtime_temp_machine_safe _ _ _ _ _ _ _ _ _ _ _ _ (proj2 RT)FID SLOT)as[ADDR _];rewrite <-F in ADDR.
 cbn[cm_task_code cm_cont_code cm_cursor_code cm_cursor_phase cm_cursor_temp cm_cursor_break cm_cursor_continue cm_value_phase_code cm_phase_stops cm_ann_pc cm_ann_cursors]in CODE.
 pose proof(cm_tvm_index_tail (cm_source_function_policy sp)p fid ty owner(cm_compile_model(cm_source_function_policy sp)p)pc(cm_value_number st v)vcalls mem input output _ ADDR CODE)as EXEC.
 rewrite F,WORD in EXEC.
 unfold cm_target_step_result;cbn[cm_step cm_cursor_frames cm_cursor_phase cm_phase_frame map cm_ann_cursors cm_annotation_step cm_update_v cm_vapply];rewrite OK.
 change(p=p /\ cm_running_target_sim (cm_source_function_policy sp)p fid st[cm_ptr_add(cm_program_structs p)base(cm_value_number st v)]
 (cm_ann_pop ap(pc+8)(CMAnnotation pc temp b c(CMACursor(CAIndexRP base ty)owner ob oc::tail)spills saved calls))
 (tvm_iter 8(TVMRunTask(cm_compile_model(cm_source_function_policy sp)p)(TVMState pc[cm_value_number st v]vcalls mem input output)))).
 rewrite EXEC;split;[reflexivity|];eexists;split;[reflexivity|split;[reflexivity|]].
 pose proof(cm_machine_sim_stack (cm_source_function_policy sp)p st _ _ _ [v][][cm_ptr_add(cm_program_structs p)base(cm_value_number st v)][] (pc+8) OLD)as NEW.
 cbn[cm_encode_values map app]in NEW;rewrite(cm_ptr_add_number_bridge _ _ _ _ _ TYPE OK)in NEW;exact NEW.
Qed.
