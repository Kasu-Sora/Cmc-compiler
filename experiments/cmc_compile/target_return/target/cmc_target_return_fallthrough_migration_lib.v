Require Export SimpleC.EE.QCP_demos_human.cmc_target_return_value_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_target_c_fallthrough_step sp ap p fid st caller env fp regions ret returnpc caller_spills pc temp b c owner ob oc tail spills saved calls target :
 let ann:=CMAnnotation pc temp b c(CMACursor(CACallP caller env fp regions ret)owner ob oc::tail)spills(CMSpillFrame caller fp caller_spills::saved)(CMCallSimFrame(cm_state_fp st)fp returnpc::calls)in
 cm_runtime_core(cm_source_function_policy sp)ap p fid st ann ->cm_tagged_span_valid st ->incl regions(cm_state_regions st) ->
 cm_task_layout sp ap p(CMCTask p fid(CMNormal)st(cm_cursor_frames(cm_ann_cursors ann)))ann ->
 cm_task_target_sim(cm_source_function_policy sp)p(CMCTask p fid(CMNormal)st(cm_cursor_frames(cm_ann_cursors ann)))target ann ->
 cm_target_step_result sp ap p(CMCTask p fid(CMNormal)st(cm_cursor_frames(cm_ann_cursors ann)))target ann.
Proof.
 cbn zeta;intros RT TAG INC[CODE SAVED][_ [vm[-> [PC SIM]]]];pose proof SIM as OLD.
 destruct vm as[vpc stack vcalls mem input output];cbn[tvm_pc cm_ann_pc]in PC;subst vpc.
 destruct SIM as[M[P[F[C[S[I[O STACK]]]]]]];change(stack=[])in STACK;subst stack;cbn[tvm_mem]in F.
 change(vcalls<>[] /\ hd 0 vcalls=returnpc /\ tower_getw mem(cm_state_fp st)=fp /\ cm_call_frames_sim mem calls(tl vcalls))in C.
 destruct C as[N[RET[WORD CT]]];destruct vcalls as[|head vcalls];[contradiction|];cbn[hd]in RET;subst head.
 pose proof(cm_runtime_stack_memory_layout _ _ _ _ _ _ _ _ _ (proj2 RT))as MEMORY.
 pose proof(cm_runtime_return_slot_safe _ _ _ _ _ _ _ _ _ (proj2 RT))as[[_ CSAFE][_ SSAFE]].
 pose proof(proj2 RT)as R;cbn[cm_runtime_stack cm_ann_cursors cm_ann_saved cm_ann_calls cm_ann_spills cm_cursor_phase cm_phase_is_call cm_phase_oldfp]in R;destruct R as[_[SEG _]].
 pose proof(cm_frame_segment_bounds _ _ _ _ _ SEG)as[SB[LOW[HIGH TOP]]].
 assert(FP:tower_word_valid(tower_getw mem 8))by(rewrite F;unfold tower_word_valid;lia).
 assert(SIGN:tower_signed64 fp)by(unfold tower_signed64;lia).
 cbn[cm_task_code cm_control_phase_code cm_control_kind Z.eqb Pos.eqb cm_ann_pc cm_ann_temp cm_ann_break cm_ann_continue cm_normal_cont_code cm_cursor_code cm_cursor_phase cm_cursor_temp cm_cursor_break cm_cursor_continue cm_normal_phase_code cm_normal_phase_stops cm_list_empty cm_ann_cursors orb]in CODE;rewrite ?app_nil_r in CODE.
 pose proof(cm_tvm_return_zero (cm_compile_model(cm_source_function_policy sp)p)pc returnpc vcalls mem input output [] FP ltac:(rewrite app_nil_r;exact CODE))as EXEC;rewrite F,WORD in EXEC.
 unfold cm_target_step_result;cbn[cm_step cm_cursor_frames cm_cursor_phase cm_phase_frame map cm_ann_cursors cm_annotation_step cm_update_c cm_capply cm_control_kind Z.eqb Pos.eqb cm_control_value cm_update_steps cm_update_annotation].
 change(p=p /\ cm_running_target_sim(cm_source_function_policy sp)p caller(cm_restore_call st env fp regions)[cm_convert_value(cm_restore_call st env fp regions)ret(CMIntV 0)]
 (cm_ann_leave_call ap returnpc(CMAnnotation pc temp b c(CMACursor(CACallP caller env fp regions ret)owner ob oc::tail)spills(CMSpillFrame caller fp caller_spills::saved)(CMCallSimFrame(cm_state_fp st)fp returnpc::calls)))
 (tvm_iter(cm_code_steps(cm_fallthrough_tail_code))(TVMRunTask(cm_compile_model(cm_source_function_policy sp)p)(TVMState pc[](returnpc::vcalls)mem input output)))).
 change(cm_code_steps cm_fallthrough_tail_code)with 7%nat;rewrite EXEC;split;[reflexivity|];eexists;split;[reflexivity|split;[reflexivity|]].
 pose proof(cm_machine_restore_call_return (cm_source_function_policy sp)p st(TVMState pc[](returnpc::vcalls)mem input output)(CMSpillFrame fid(cm_state_fp st)spills)(CMSpillFrame caller fp caller_spills::saved)env fp regions returnpc calls[][cm_convert_value(cm_restore_call st env fp regions)ret(CMIntV 0)]returnpc MEMORY TAG INC SIGN CSAFE SSAFE OLD)as NEW.
 cbn[cm_encode_values map]in NEW;rewrite cm_convert_number in NEW;change(cm_value_number(cm_restore_call st env fp regions)(CMIntV 0))with 0 in NEW.
 destruct(cm_type_eqb ret CMCharTy);exact NEW.
Qed.
