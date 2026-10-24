Require Export SimpleC.EE.QCP_demos_human.cmc_target_store_runtime_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_call_frames_sim_store mem ty base value frames calls : cm_call_frames_range_safe base(cm_store_width ty)frames -> cm_call_frames_sim mem frames calls ->
 cm_call_frames_sim(cm_store_mem ty base value mem)frames calls.
Proof.
 revert calls;induction frames as[|f rest IH];intros calls;cbn[cm_call_frames_range_safe cm_call_frames_sim];[auto|].
 intros[D DS][N[R[W T]]];split;[exact N|];split;[exact R|];split;[rewrite cm_store_mem_word_outside;[exact W|unfold cm_range_disjoint in D;tauto]|now apply IH].
Qed.
Lemma cm_spill_list_sim_source_store policy p st mem fid fp ty ptr v spills :
 cm_spill_list_range_safe policy p fid fp(cm_value_number st ptr)(cm_store_width ty)spills ->
 cm_spill_list_sim policy p st mem fid fp spills ->
 cm_spill_list_sim policy p(cm_state_store ty ptr v st)(cm_store_mem ty(cm_value_number st ptr)(cm_value_number st(cm_convert_value st ty v))mem)fid fp spills.
Proof.
 induction spills as[|s rest IH];cbn[cm_spill_list_range_safe cm_spill_list_sim];[auto|].
 intros[D DS][W T];split;[rewrite cm_store_value_number,cm_store_mem_word_outside;[exact W|unfold cm_range_disjoint in D;tauto]|now apply IH].
Qed.
Lemma cm_spill_frames_sim_source_store policy p st mem ty ptr v frames :
 cm_spill_frames_range_safe policy p(cm_value_number st ptr)(cm_store_width ty)frames -> cm_spill_frames_sim policy p st mem frames ->
 cm_spill_frames_sim policy p(cm_state_store ty ptr v st)(cm_store_mem ty(cm_value_number st ptr)(cm_value_number st(cm_convert_value st ty v))mem)frames.
Proof.
 induction frames as[|f rest IH];cbn[cm_spill_frames_range_safe cm_spill_frames_sim];[auto|].
 intros[D DS][W T];split;[now apply cm_spill_list_sim_source_store|now apply IH].
Qed.
Lemma cm_machine_source_store policy p st vm calls frames oldvals oldsuffix ty ptr v vals suffix pc :
 cm_runtime_memory_layout policy p st calls frames -> cm_store_ok ty ptr st=true ->
 cm_machine_state_sim policy p st vm calls frames oldvals oldsuffix ->
 cm_machine_state_sim policy p(cm_state_store ty ptr v st)
 (TVMState pc(cm_encode_values(cm_state_store ty ptr v st)vals++suffix)(tvm_calls vm)
 (cm_store_mem ty(cm_value_number st ptr)(cm_value_number st(cm_convert_value st ty v))(tvm_mem vm))(tvm_input vm)(tvm_output vm))calls frames vals suffix.
Proof.
 intros RT OK[M[P[F[C[S[I[O STACK]]]]]]];destruct(cm_runtime_store_machine_safe _ _ _ _ _ _ _ RT OK)as[FP[CALLS SPILLS]].
 unfold cm_machine_state_sim;split;[now apply cm_store_initialized_sim|];split;[now apply cm_store_provenance_sim|].
 split;[cbn[tvm_mem];rewrite cm_store_mem_word_outside;[exact F|unfold cm_range_disjoint in FP;tauto]|];split;[now apply cm_call_frames_sim_store|].
 split;[now apply cm_spill_frames_sim_source_store|];split;[exact I|];split;[exact O|];reflexivity.
Qed.
