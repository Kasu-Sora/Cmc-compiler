Require Export SimpleC.EE.QCP_demos_human.cmc_target_load_memory_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_tvm_load_byte obj pc addr calls mem input output rest :
 tower_addr_valid addr -> cm_code_at(tvm_object_code obj)pc(TVMInst TVMLoadBOp 0::rest) ->
 tvm_step(TVMRunTask obj(TVMState pc[addr]calls mem input output))=
 TVMRunTask obj(TVMState(pc+1)[tower_getb mem addr]calls mem input output).
Proof.
 intros ADDR CODE; apply tower_addr_validb_spec in ADDR; rewrite(cm_tvm_code_step obj(TVMState pc[addr]calls mem input output)_ _ _ CODE).
 cbn [tvm_inst_step tvm_stack]; change(1<=?Zlength[addr])with true; cbv beta iota zeta delta [andb hd];rewrite ADDR;reflexivity.
Qed.
Lemma cm_tvm_typed_load obj pc addr calls mem input output ty rest :
 (match ty with CMCharTy=>tower_addr_valid addr|_=>tower_word_valid addr end) -> cm_code_at(tvm_object_code obj)pc(cm_load_code ty++rest) ->
 tvm_step(TVMRunTask obj(TVMState pc[addr]calls mem input output))=
 TVMRunTask obj(TVMState(pc+1)[match ty with CMCharTy=>tower_getb mem addr|_=>tower_getw mem addr end]calls mem input output).
Proof.
 intros ADDR CODE; destruct ty;
 first[exact(cm_tvm_load_byte _ _ _ _ _ _ _ _ ADDR CODE)|exact(cm_tvm_load_step obj(TVMState pc[addr]calls mem input output)addr[] _ CODE eq_refl ADDR)].
Qed.
Lemma cm_target_v_load_step sp ap p fid ty v st pc temp b c owner ob oc tail spills saved calls target :
 let ann:=CMAnnotation pc temp b c (CMACursor (CALoadP ty) owner ob oc::tail) spills saved calls in
 cm_task_runtime_invariant (cm_source_function_policy sp)ap p (CMVTask p fid v st(cm_cursor_frames(cm_ann_cursors ann)))ann ->
 cm_scalar_expr_type ty -> cm_load_ok ty v st=true ->
 cm_task_layout sp ap p(CMVTask p fid v st(cm_cursor_frames(cm_ann_cursors ann)))ann ->
 cm_task_target_sim (cm_source_function_policy sp)p(CMVTask p fid v st(cm_cursor_frames(cm_ann_cursors ann)))target ann ->
 cm_target_step_result sp ap p(CMVTask p fid v st(cm_cursor_frames(cm_ann_cursors ann)))target ann.
Proof.
 cbn zeta;intros [_ [_ RT]] TYPE OK [CODE SAVED] [_ [vm [-> [PC SIM]]]];pose proof SIM as OLD.
 destruct vm as[vpc stack vcalls mem input output];cbn [tvm_pc cm_ann_pc]in PC;subst vpc.
 destruct SIM as[M[P[F[C[S[I[O STACK]]]]]]];change(stack=[cm_value_number st v])in STACK;subst stack.
 pose proof(cm_runtime_stack_memory_layout _ _ _ _ _ _ _ _ _ RT)as MEMORY.
 pose proof(cm_load_machine_number _ _ _ _ _ _ _ _ MEMORY OK TYPE M P)as VALUE.
 assert(ADDR:match ty with CMCharTy=>tower_addr_valid(cm_value_number st v)|_=>tower_word_valid(cm_value_number st v)end).
 { unfold cm_load_ok in OK;repeat rewrite andb_true_iff in OK;destruct OK as[[[[[_ _]_]ADDR]_]_];destruct ty;[apply tower_word_validb_spec|apply tower_addr_validb_spec|apply tower_word_validb_spec|apply tower_word_validb_spec];exact ADDR. }
 pose proof(cm_tvm_typed_load (cm_compile_model(cm_source_function_policy sp)p)pc(cm_value_number st v)vcalls mem input output ty (cm_cursor_code sp p fid(pc+1)owner false tail)ADDR)as EXEC.
 specialize(EXEC ltac:(cbn [cm_task_code cm_cont_code cm_cursor_code cm_cursor_phase cm_cursor_temp cm_cursor_break cm_cursor_continue cm_value_phase_code cm_phase_stops cm_phase_yields_normal cm_ann_pc cm_ann_temp cm_ann_cursors orb]in CODE;rewrite cm_layout_load_length in CODE;exact CODE)).
 unfold cm_target_step_result;cbn [cm_step cm_cursor_frames map cm_cursor_phase cm_phase_frame cm_vapply cm_ann_cursors cm_annotation_step cm_update_v];rewrite OK;cbn [cm_update_steps cm_update_annotation].
 rewrite cm_layout_load_length; change(p=p /\ cm_running_target_sim (cm_source_function_policy sp)p fid st[cm_load_value ty v st]
 (cm_ann_pop ap(pc+1)(CMAnnotation pc temp b c(CMACursor(CALoadP ty)owner ob oc::tail)spills saved calls))
 (tvm_step(TVMRunTask(cm_compile_model(cm_source_function_policy sp)p)(TVMState pc[cm_value_number st v]vcalls mem input output)))).
 rewrite EXEC;split;[reflexivity|]. eexists;split;[reflexivity|split;[reflexivity|]].
 pose proof(cm_machine_sim_stack (cm_source_function_policy sp)p st _ _ _ [v][][cm_load_value ty v st][] (pc+1) OLD)as NEW.
 cbn [cm_encode_values map app]in NEW;rewrite VALUE in NEW;exact NEW.
Qed.
