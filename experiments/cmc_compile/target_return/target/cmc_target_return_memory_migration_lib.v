Require Export SimpleC.EE.QCP_demos_human.cmc_target_return_code_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_runtime_fp_slot_disjoint policy p st calls frames a :cm_runtime_memory_layout policy p st calls frames ->cm_live_address st a ->a<8 \/ 16<=a.
Proof.
 intros RT[r[IN[LIVE[LO HI]]]];specialize(RT r IN);destruct RT as[DEAD|[L[H[B[U[DIS REST]]]]]];[congruence|unfold cm_range_disjoint in DIS;lia].
Qed.
Lemma cm_machine_restore_call_return policy p st vm current saved oldenv oldfp oldregions returnpc calls oldvals vals pc :
 cm_runtime_memory_layout policy p st(CMCallSimFrame(cm_state_fp st)oldfp returnpc::calls)(current::saved) ->
 cm_tagged_span_valid st ->incl oldregions(cm_state_regions st) ->tower_signed64 oldfp ->
 cm_call_frames_range_safe 8 8 calls ->cm_spill_frames_range_safe policy p 8 8 saved ->
 cm_machine_state_sim policy p st vm(CMCallSimFrame(cm_state_fp st)oldfp returnpc::calls)(current::saved)oldvals[] ->
 cm_machine_state_sim policy p(cm_restore_call st oldenv oldfp oldregions)
 (TVMState pc(cm_encode_values(cm_restore_call st oldenv oldfp oldregions)vals)(tl(tvm_calls vm))(tower_setw(tvm_mem vm)8 oldfp)(tvm_input vm)(tvm_output vm))calls saved vals[].
Proof.
 intros RT TAG INC SIGN CALLS SPILLS[M[P[F[[_[_[_ C]]][[_ S][I[O STACK]]]]]]].
 assert(OUT:forall a,cm_live_address st a ->a<8 \/ 8+8<=a)by(intros;now apply cm_runtime_fp_slot_disjoint with policy p st(CMCallSimFrame(cm_state_fp st)oldfp returnpc::calls)(current::saved)).
 assert(GEN:cm_region_generations_incl oldregions(cm_state_regions st))by(unfold cm_region_generations_incl;now apply incl_map).
 unfold cm_machine_state_sim;split;[apply cm_restore_initialized_sim;[exact INC|now apply cm_temp_initialized_sim]|].
 split;[apply cm_restore_provenance_sim;[exact INC|now apply cm_temp_provenance_sim]|].
 split;[cbn[tvm_mem cm_restore_call cm_state_fp];now rewrite tower_getw_setw,tower_wrap64_fixed|].
 split;[now apply cm_call_frames_sim_setw|];split;[apply cm_restore_spill_frames_sim;[exact GEN|now apply cm_spill_frames_sim_setw]|].
 split;[exact I|];split;[exact O|];unfold cm_operand_suffix_sim;cbn[tvm_stack];now rewrite app_nil_r.
Qed.
Lemma cm_runtime_return_slot_safe policy ap p st fid cursors spills saved calls :
 cm_runtime_stack policy ap p(cm_state_regions st)fid(cm_state_fp st)(cm_state_regions st)cursors spills saved calls ->
 cm_call_frames_range_safe 8 8 calls /\ cm_spill_frames_range_safe policy p 8 8 (CMSpillFrame fid(cm_state_fp st)spills::saved).
Proof.
 intro RT;pose proof(cm_runtime_stack_fp_bounds _ _ _ _ _ _ _ _ _ _ _ RT)as[S[F U]].
 pose proof(cm_runtime_stack_lower _ _ _ _ _ _ _ _ _ _ _ RT)as[C[SP SAVED]].
 split;[eapply cm_call_frames_lower_range;[exact C|lia]|].
 split;[eapply cm_spill_list_lower_range;[exact SP|lia]|eapply cm_spill_frames_lower_range;[exact SAVED|lia]].
Qed.
