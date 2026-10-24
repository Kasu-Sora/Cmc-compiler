Require Export SimpleC.EE.QCP_demos_human.cmc_target_assign_code_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_spill_holds_range policy p fid fp spills slot ptr base width :
 cm_spill_list_range_safe policy p fid fp base width spills -> cm_spill_holds slot ptr spills ->
 cm_range_disjoint base width(fp+cm_temp_offset policy p fid slot)8.
Proof.
 induction spills as[|[s v]rest IH];cbn[cm_spill_list_range_safe cm_spill_holds cm_spill_slot cm_spill_value];[tauto|].
 intros[H T];destruct(s=?slot)eqn:E;intro HOLD;[apply Z.eqb_eq in E;subst;exact H|now apply IH].
Qed.
Lemma cm_target_v_assign_right_step sp ap p fid v st ptr ty pc temp b c owner ob oc tail spills saved calls target :
 let ann:=CMAnnotation pc temp b c(CMACursor(CAAssignRP ptr ty)owner ob oc::tail)spills saved calls in
 cm_runtime_core(cm_source_function_policy sp)ap p fid st ann -> 0<=fid ->
 0<=owner<cm_temp_slots(cm_source_function_at sp fid p) -> cm_spill_holds owner ptr spills ->
 cm_store_ok ty ptr st=true ->
 cm_task_layout sp ap p(CMVTask p fid v st(cm_cursor_frames(cm_ann_cursors ann)))ann ->
 cm_task_target_sim(cm_source_function_policy sp)p(CMVTask p fid v st(cm_cursor_frames(cm_ann_cursors ann)))target ann ->
 cm_target_step_result sp ap p(CMVTask p fid v st(cm_cursor_frames(cm_ann_cursors ann)))target ann.
Proof.
 cbn zeta;intros RT FID SLOT HOLD OK[CODE SAVED][_ [vm[-> [PC SIM]]]];pose proof SIM as OLD.
 destruct vm as[vpc stack vcalls mem input output];cbn[tvm_pc cm_ann_pc]in PC;subst vpc.
 destruct SIM as[M[P[F[C[[S SS][I[O STACK]]]]]]];change(stack=[cm_value_number st v])in STACK;subst stack;cbn[tvm_mem]in F.
 pose proof(cm_runtime_stack_memory_layout _ _ _ _ _ _ _ _ _ (proj2 RT))as MEMORY.
 pose proof(cm_runtime_store_machine_safe _ _ _ _ _ _ _ MEMORY OK)as[FP[CALLS[SP _]]].
 pose proof(cm_spill_holds_range _ _ _ _ _ _ _ _ _ SP HOLD)as DIS;cbn[cm_spill_frame_fid cm_spill_frame_fp]in DIS.
 pose proof(cm_spill_sim_holds _ _ _ _ _ _ _ _ _ S HOLD)as WORD;cbn[tvm_mem cm_spill_frame_fid cm_spill_frame_fp]in WORD.
 pose proof(cm_runtime_temp_machine_safe _ _ _ _ _ _ _ _ _ _ _ _ (proj2 RT)FID SLOT)as[ADDR _];rewrite <-F in ADDR.
 cbn[cm_task_code cm_cont_code cm_cursor_code cm_cursor_phase cm_cursor_temp cm_cursor_break cm_cursor_continue cm_value_phase_code cm_phase_stops cm_ann_pc cm_ann_cursors]in CODE.
 pose proof(cm_tvm_assign_tail (cm_source_function_policy sp)p fid ty owner st v (cm_compile_model(cm_source_function_policy sp)p)pc vcalls mem input output _ ADDR ltac:(rewrite F,WORD;exact(cm_store_address_valid _ _ _ OK)) ltac:(rewrite F,WORD;exact FP) ltac:(rewrite F,WORD;exact DIS) CODE)as EXEC.
 cbn zeta in EXEC;rewrite F,WORD in EXEC.
 unfold cm_target_step_result;cbn[cm_step cm_cursor_frames cm_cursor_phase cm_phase_frame map cm_ann_cursors cm_annotation_step cm_update_v cm_vapply];rewrite OK;cbn[cm_update_steps cm_update_annotation].
 change(p=p /\ cm_running_target_sim(cm_source_function_policy sp)p fid(cm_state_store ty ptr v st)[cm_convert_value st ty v]
 (cm_ann_pop ap(pc+Zlength(cm_assign_tail_code(cm_source_function_policy sp)p fid ty owner))(CMAnnotation pc temp b c(CMACursor(CAAssignRP ptr ty)owner ob oc::tail)spills saved calls))
 (tvm_iter(cm_code_steps(cm_assign_tail_code(cm_source_function_policy sp)p fid ty owner))(TVMRunTask(cm_compile_model(cm_source_function_policy sp)p)(TVMState pc[cm_value_number st v]vcalls mem input output)))).
 rewrite EXEC;split;[reflexivity|];eexists;split;[reflexivity|split;[reflexivity|]].
 pose proof(cm_machine_source_store (cm_source_function_policy sp)p st (TVMState pc[cm_value_number st v]vcalls mem input output) calls (cm_active_spill_frames fid st(CMAnnotation pc temp b c(CMACursor(CAAssignRP ptr ty)owner ob oc::tail)spills saved calls)) [v][] ty ptr v [cm_convert_value st ty v][] (pc+Zlength(cm_assign_tail_code(cm_source_function_policy sp)p fid ty owner)) MEMORY OK OLD)as NEW.
 cbn[cm_encode_values map app]in NEW;rewrite cm_store_value_number in NEW;exact NEW.
Qed.
