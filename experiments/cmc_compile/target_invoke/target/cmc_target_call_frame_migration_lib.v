Require Export SimpleC.EE.QCP_demos_human.cmc_target_parameters_complete_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_machine_save_call_frame policy p st vm calls frames values base returnpc pc :
 cm_tagged_span_valid st ->(forall a,cm_live_address st a ->a<base \/ base+8<=a) ->
 cm_machine_range_safe policy p base 8 calls frames ->tower_signed64(cm_state_fp st) ->
 cm_machine_state_sim policy p st vm calls frames values[] ->
 cm_machine_state_sim policy p st
 (TVMState pc(cm_encode_values st values)(returnpc::tvm_calls vm)(tower_setw(tvm_mem vm)base(cm_state_fp st))(tvm_input vm)(tvm_output vm))
 (CMCallSimFrame base(cm_state_fp st)returnpc::calls)frames values[].
Proof.
 intros TAG OUT[D[CR SR]]SIGN[M[P[F[C[S[I[O STACK]]]]]]].
 unfold cm_machine_state_sim;split;[now apply cm_temp_initialized_sim|];split;[now apply cm_temp_provenance_sim|].
 split;[cbn[tvm_mem];rewrite tower_getw_setw_outside;[exact F|exact D]|].
 split.
 - cbn[cm_call_frames_sim tvm_mem tvm_calls cm_call_sim_return cm_call_sim_base cm_call_sim_saved hd tl];split;[discriminate|];split;[reflexivity|];split;[rewrite tower_getw_setw;now apply tower_wrap64_fixed|now apply cm_call_frames_sim_setw].
 - split;[now apply cm_spill_frames_sim_setw|];split;[exact I|];split;[exact O|];unfold cm_operand_suffix_sim;cbn[tvm_stack];now rewrite app_nil_r.
Qed.
Lemma cm_machine_prologue_pending sp p fid st vm calls frames values returnpc pc :
 let base:=cm_state_fp(cm_call_base_state sp p fid st)in
 cm_function_wf(cm_source_function_policy sp)p(cm_source_function_at sp fid p) ->cm_regions_before(cm_state_regions st)(cm_state_nextgen st) ->
 cm_tags_generation_below(cm_state_nextgen st)(cm_state_tags st) ->cm_spill_frames_generation_below(cm_state_nextgen st)frames ->cm_tagged_span_valid st ->
 (forall a,cm_live_address st a ->a<base \/ base+8<=a) ->(forall a,cm_live_address st a ->a<8 \/ 16<=a) ->
 cm_machine_range_safe(cm_source_function_policy sp)p base 8 calls frames ->
 cm_call_frames_range_safe 8 8 calls ->cm_spill_frames_range_safe(cm_source_function_policy sp)p 8 8 frames ->
 tower_signed64 base ->tower_signed64(cm_state_fp st) ->
 cm_machine_state_sim(cm_source_function_policy sp)p st vm calls frames values[] ->
 cm_machine_state_sim(cm_source_function_policy sp)p(cm_call_pending_base sp p fid st)
 (TVMState pc(cm_encode_values(cm_call_pending_base sp p fid st)values)(returnpc::tvm_calls vm)
 (tower_setw(tower_setw(tvm_mem vm)base(cm_state_fp st))8 base)(tvm_input vm)(tvm_output vm))
 (CMCallSimFrame base(cm_state_fp st)returnpc::calls)(CMSpillFrame fid base[]::frames)values[].
Proof.
 cbn zeta;intros FW BEFORE GEN FGEN TAG OUT OUT8 SAFE CR SR BSIGN FSIGN SIM.
 pose proof(cm_machine_save_call_frame(cm_source_function_policy sp)p st vm calls frames values(cm_state_fp(cm_call_base_state sp p fid st))returnpc pc TAG OUT SAFE FSIGN SIM)as SAVE.
 assert(CRNEW:cm_call_frames_range_safe 8 8(CMCallSimFrame(cm_state_fp(cm_call_base_state sp p fid st))(cm_state_fp st)returnpc::calls)).
 { cbn[cm_call_frames_range_safe cm_call_sim_base];split;[destruct SAFE as[D _];unfold cm_range_disjoint in *;tauto|exact CR]. }
 exact(cm_machine_call_pending_store sp p fid st
 (TVMState pc(cm_encode_values st values)(returnpc::tvm_calls vm)(tower_setw(tvm_mem vm)(cm_state_fp(cm_call_base_state sp p fid st))(cm_state_fp st))(tvm_input vm)(tvm_output vm))
 (CMCallSimFrame(cm_state_fp(cm_call_base_state sp p fid st))(cm_state_fp st)returnpc::calls)frames values pc
 FW BEFORE GEN FGEN TAG OUT OUT8 CRNEW SR BSIGN SAVE).
Qed.
