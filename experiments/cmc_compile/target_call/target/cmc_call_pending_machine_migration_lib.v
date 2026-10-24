Require Export SimpleC.EE.QCP_demos_human.cmc_call_pending_memory_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_machine_call_pending_store sp p fid st vm calls frames values pc :
 let base:=cm_state_fp(cm_call_base_state sp p fid st)in
 cm_function_wf(cm_source_function_policy sp)p(cm_source_function_at sp fid p) ->cm_regions_before(cm_state_regions st)(cm_state_nextgen st) ->
 cm_tags_generation_below(cm_state_nextgen st)(cm_state_tags st) ->cm_spill_frames_generation_below(cm_state_nextgen st)frames ->cm_tagged_span_valid st ->
 (forall a,cm_live_address st a ->a<base \/ base+8<=a) ->(forall a,cm_live_address st a ->a<8 \/ 16<=a) ->
 cm_call_frames_range_safe 8 8 calls ->cm_spill_frames_range_safe(cm_source_function_policy sp)p 8 8 frames ->tower_signed64 base ->
 cm_machine_state_sim(cm_source_function_policy sp)p st vm calls frames values[] ->
 cm_machine_state_sim(cm_source_function_policy sp)p(cm_call_pending_base sp p fid st)
 (TVMState pc(cm_encode_values(cm_call_pending_base sp p fid st)values)(tvm_calls vm)(tower_setw(tvm_mem vm)8 base)(tvm_input vm)(tvm_output vm))
 calls(CMSpillFrame fid base[]::frames)values[].
Proof.
 cbn zeta;intros WF BEFORE GEN FGEN TAG OUT OUT8 CALLS SPILLS SIGN[M[P[F[C[S[I[O STACK]]]]]]].
 unfold cm_machine_state_sim;split;[apply cm_call_pending_initialized_transport;[exact WF|exact BEFORE|now apply cm_temp_initialized_sim|exact OUT]|].
 split;[apply cm_call_pending_provenance_transport;[exact WF|exact BEFORE|exact GEN|now apply cm_temp_provenance_sim]|].
 split;[cbn[tvm_mem];rewrite tower_getw_setw,tower_wrap64_fixed by exact SIGN;reflexivity|].
 split;[now apply cm_call_frames_sim_setw|];split;[split;[constructor|apply cm_call_pending_spills_transport;[exact FGEN|now apply cm_spill_frames_sim_setw]]|].
 split;[exact I|];split;[exact O|];unfold cm_operand_suffix_sim;cbn[tvm_stack];now rewrite app_nil_r.
Qed.
Lemma cm_call_pending_encode_values sp p fid st values :cm_values_generation_below(cm_state_nextgen st)values ->
 cm_encode_values(cm_call_pending_base sp p fid st)values=cm_encode_values st values.
Proof.
 induction values as[|v rest IH];cbn[cm_values_generation_below cm_encode_values map];[reflexivity|intros[V REST];rewrite cm_call_pending_value_number by exact V;f_equal;now apply IH].
Qed.
