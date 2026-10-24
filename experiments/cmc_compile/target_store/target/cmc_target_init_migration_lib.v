Require Export SimpleC.EE.QCP_demos_human.cmc_target_store_code_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_store_address_valid ty ptr st : cm_store_ok ty ptr st=true ->
 match ty with CMCharTy=>tower_addr_valid(cm_value_number st ptr)|_=>tower_word_valid(cm_value_number st ptr)end.
Proof.
 unfold cm_store_ok;intro OK;repeat rewrite andb_true_iff in OK;destruct OK as[_ A];destruct ty;first[apply tower_word_validb_spec|apply tower_addr_validb_spec];exact A.
Qed.
Lemma cm_binding_local_number sp p fid slot st : cm_binding_address_ok sp p fid 1 slot st=true ->
 cm_value_number st(cm_state_env st 1 slot)=tower_wrap64(cm_state_fp st+cm_local_offset(cm_source_function_policy sp)p fid slot).
Proof.
 unfold cm_binding_address_ok;intro OK;repeat rewrite andb_true_iff in OK;destruct OK as[[_ N]_];apply Z.eqb_eq in N;cbn[Z.eqb Pos.eqb]in N;rewrite <-N.
 cbn[Z.eqb];unfold cm_local_base,cm_local_offset,cm_source_function_at;f_equal;lia.
Qed.
Lemma cm_target_v_init_step sp ap p fid v st slot pc temp b c owner ob oc tail spills saved calls target :
 let ann:=CMAnnotation pc temp b c(CMACursor(CAInitP slot)owner ob oc::tail)spills saved calls in
 let ty:=cm_slot_ty(cm_source_slot_at sp slot(cm_function_locals(cm_source_function_at sp fid p)))in
 cm_runtime_core(cm_source_function_policy sp)ap p fid st ann ->
 cm_binding_address_ok sp p fid 1 slot st=true -> cm_store_ok ty(cm_state_env st 1 slot)st=true ->
 cm_task_layout sp ap p(CMVTask p fid v st(cm_cursor_frames(cm_ann_cursors ann)))ann ->
 cm_task_target_sim(cm_source_function_policy sp)p(CMVTask p fid v st(cm_cursor_frames(cm_ann_cursors ann)))target ann ->
 cm_target_step_result sp ap p(CMVTask p fid v st(cm_cursor_frames(cm_ann_cursors ann)))target ann.
Proof.
 cbn zeta;intros RT BIND OK[CODE SAVED][_ [vm[-> [PC SIM]]]];pose proof SIM as OLD.
 destruct vm as[vpc stack vcalls mem input output];cbn[tvm_pc cm_ann_pc]in PC;subst vpc.
 destruct SIM as[M[P[F[C[S[I[O STACK]]]]]]];change(stack=[cm_value_number st v])in STACK;subst stack.
 pose proof(cm_runtime_stack_memory_layout _ _ _ _ _ _ _ _ _ (proj2 RT))as MEMORY.
 pose proof(cm_store_address_valid _ _ _ OK)as ADDR;rewrite(cm_binding_local_number _ _ _ _ _ BIND),<-F in ADDR.
 cbn[cm_task_code cm_cont_code cm_cursor_code cm_cursor_phase cm_cursor_temp cm_cursor_break cm_cursor_continue cm_value_phase_code cm_phase_stops cm_phase_yields_normal cm_ann_pc cm_ann_cursors orb]in CODE.
 unfold cm_init_tail_code in CODE;repeat rewrite <-app_assoc in CODE.
 pose proof(cm_tvm_init_code st v _ (cm_compile_model(cm_source_function_policy sp)p)pc vcalls mem input output _ _ ADDR CODE)as EXEC.
 cbn[tvm_mem]in F;rewrite F,<- (cm_binding_local_number _ _ _ _ _ BIND)in EXEC.
 unfold cm_target_step_result;cbn[cm_step cm_cursor_frames cm_cursor_phase cm_phase_frame map cm_ann_cursors cm_annotation_step cm_update_v cm_vapply];rewrite BIND,OK;cbn[andb cm_update_steps cm_update_annotation].
 change(p=p /\ cm_running_target_sim(cm_source_function_policy sp)p fid
 (cm_state_store (cm_slot_ty(cm_source_slot_at sp slot(cm_function_locals(cm_source_function_at sp fid p)))) (cm_state_env st 1 slot)v st)[]
 (cm_ann_pop ap(pc+Zlength(cm_init_tail_code sp p fid slot))(CMAnnotation pc temp b c(CMACursor(CAInitP slot)owner ob oc::tail)spills saved calls))
 (tvm_iter(cm_code_steps(cm_init_tail_code sp p fid slot))(TVMRunTask(cm_compile_model(cm_source_function_policy sp)p)(TVMState pc[cm_value_number st v]vcalls mem input output)))).
 unfold cm_init_tail_code;rewrite EXEC;split;[reflexivity|];eexists;split;[reflexivity|split;[reflexivity|]].
 pose proof(cm_machine_source_store (cm_source_function_policy sp)p st (TVMState pc[cm_value_number st v]vcalls mem input output) calls (cm_active_spill_frames fid st(CMAnnotation pc temp b c(CMACursor(CAInitP slot)owner ob oc::tail)spills saved calls)) [v][] _ _ v [][] (pc+Zlength(cm_init_tail_code sp p fid slot)) MEMORY OK OLD)as NEW.
 exact NEW.
Qed.
