Require Export SimpleC.EE.QCP_demos_human.cmc_target_call_depth_migration_lib.
From AUXLib Require Import ListLib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_target_r_empty_call_step sp ap p fid callee ty st ks target ann :
 cm_semantic_wf_program(cm_source_function_policy sp)p ->
 cm_runtime_core(cm_source_function_policy sp)ap p fid st ann ->cm_tagged_span_valid st ->
 0<=cm_state_nextgen st ->cm_tags_generation_below(cm_state_nextgen st)(cm_state_tags st) ->
 cm_spill_frames_generation_below(cm_state_nextgen st)(cm_active_spill_frames fid st ann) ->
 cm_call_ok sp p callee[]st=true ->cm_call_depth ks<65536 ->cm_call_depth(cm_cursor_frames(cm_ann_cursors ann))<65536 ->
 cm_task_layout sp ap p(CMRTask p fid(CMCallE callee[]ty)st ks)ann ->
 cm_task_target_sim(cm_source_function_policy sp)p(CMRTask p fid(CMCallE callee[]ty)st ks)target ann ->
 cm_target_step_result sp ap p(CMRTask p fid(CMCallE callee[]ty)st ks)target ann.
Proof.
 intros WF RT TAG GEN TGEN FGEN OK DEPTH ADEPTH[CODE SAVED][_ [vm[-> [PC SIM]]]].
 pose proof SIM as[_[_[_[CALLSIM _]]]].
 pose proof(cm_call_sim_length _ _ _ CALLSIM)as LENGTH.
 pose proof(cm_saved_layout_call_depth _ _ _ _ _ _ _ SAVED)as ADEQ.
 assert(VD:Zlength(tvm_calls vm)<65536)by lia.
 assert(FID:0<=callee<Zlength(cm_program_functions p)).
 { unfold cm_call_ok in OK;repeat rewrite andb_true_iff in OK;split;[apply Z.leb_le|apply Z.ltb_lt];tauto. }
 pose proof(cm_model_function_at(cm_source_function_policy sp)p callee FID)as PROLOGUE.
 unfold cm_emit_function in PROLOGUE.
 cbn[cm_task_code]in CODE;unfold cm_emit_rvalue in CODE;rewrite cm_call_code_equation in CODE;cbn[cm_emit_args_store cm_emit_args_reload app]in CODE;rewrite <-PC in CODE.
 destruct(cm_tvm_invoke_function sp ap p fid callee st[]ann(cm_compile_model(cm_source_function_policy sp)p)vm _ _ WF OK RT TAG GEN TGEN FGEN I VD SIM CODE PROLOGUE)as[next[EXEC[NPC NEXT]]].
 assert(D:(cm_call_depth ks<?65536)=true)by(now apply Z.ltb_lt).
 assert(AD:(cm_call_depth(cm_cursor_frames(cm_ann_cursors ann))<?65536)=true)by(now apply Z.ltb_lt).
 unfold cm_target_step_result;cbv beta iota zeta delta[cm_step cm_rstart cm_args_start cm_begin_call cm_annotation_step cm_update_r cm_list_empty];rewrite OK,D,AD;cbn[andb cm_update_steps cm_update_annotation cm_task_target_sim].
 rewrite EXEC;split;[reflexivity|];exists next;split;[reflexivity|];split;[exact NPC|].
 unfold cm_active_spill_frames,cm_ann_enter_call;cbn[cm_ann_calls cm_ann_saved cm_ann_spills];rewrite <-PC;unfold cm_enter_call;rewrite cm_store_params_fp;exact NEXT.
Qed.
