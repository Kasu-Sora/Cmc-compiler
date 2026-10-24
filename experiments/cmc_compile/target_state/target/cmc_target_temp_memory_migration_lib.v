Require Export SimpleC.EE.QCP_demos_human.cmc_target_temp_code_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma tower_getb_setw_outside mem base value a : a<base \/ base+8<=a -> tower_getb(tower_setw mem base value)a=tower_getb mem a.
Proof. intro OUT;unfold tower_getb,tower_setw;tower_offset_eqb;reflexivity. Qed.
Lemma tower_getw_setw_outside mem base value a : cm_range_disjoint base 8 a 8 -> tower_getw(tower_setw mem base value)a=tower_getw mem a.
Proof. intros OUT;apply tower_getw_ext;intros i I;apply tower_getb_setw_outside;unfold cm_range_disjoint in OUT;lia. Qed.
Lemma cm_temp_initialized_sim st mem base value : (forall a,cm_live_address st a -> a<base \/ base+8<=a) ->
 cm_initialized_bytes_sim st mem -> cm_initialized_bytes_sim st(tower_setw mem base value).
Proof. intros OUT SIM a INIT LIVE;rewrite tower_getb_setw_outside by exact(OUT a LIVE);exact(SIM a INIT LIVE). Qed.
Lemma cm_temp_provenance_sim st mem base value : cm_tagged_span_valid st -> (forall a,cm_live_address st a -> a<base \/ base+8<=a) ->
 cm_stored_provenance_sim st mem -> cm_stored_provenance_sim st(tower_setw mem base value).
Proof.
 intros TAG OUT SIM a T LIVE;destruct(SIM a T LIVE)as[INIT WORD];split;[exact INIT|];rewrite <-WORD;apply tower_getw_ext;intros i I;
 apply tower_getb_setw_outside;apply OUT;apply(TAG a T LIVE);lia.
Qed.
Lemma cm_call_frames_sim_setw mem base value frames calls : cm_call_frames_range_safe base 8 frames -> cm_call_frames_sim mem frames calls ->
 cm_call_frames_sim(tower_setw mem base value)frames calls.
Proof.
 revert calls;induction frames as[|f rest IH];intros calls;cbn[cm_call_frames_range_safe cm_call_frames_sim];[auto|].
 intros[D DS][N[R[W T]]];split;[exact N|];split;[exact R|];split;[now rewrite tower_getw_setw_outside|now apply IH].
Qed.
Lemma cm_spill_list_sim_setw policy p st mem fid fp base value spills : cm_spill_list_range_safe policy p fid fp base 8 spills ->
 cm_spill_list_sim policy p st mem fid fp spills -> cm_spill_list_sim policy p st(tower_setw mem base value)fid fp spills.
Proof.
 induction spills as[|s rest IH];cbn[cm_spill_list_range_safe cm_spill_list_sim];[auto|].
 intros[D DS][W T];split;[now rewrite tower_getw_setw_outside|now apply IH].
Qed.
Lemma cm_spill_frames_sim_setw policy p st mem base value frames : cm_spill_frames_range_safe policy p base 8 frames ->
 cm_spill_frames_sim policy p st mem frames -> cm_spill_frames_sim policy p st(tower_setw mem base value)frames.
Proof.
 induction frames as[|f rest IH];cbn[cm_spill_frames_range_safe cm_spill_frames_sim];[auto|].
 intros[D DS][W T];split;[now apply cm_spill_list_sim_setw|now apply IH].
Qed.
Lemma cm_temp_remove_sim policy p st mem fid fp slot value spills : cm_spill_list_sim policy p st mem fid fp spills ->
 cm_spill_list_sim policy p st(tower_setw mem(fp+cm_temp_offset policy p fid slot)value)fid fp(cm_spill_remove slot spills).
Proof.
 induction spills as[|s rest IH];cbn[cm_spill_remove cm_spill_list_sim];[auto|];intros[W T].
 destruct(cm_spill_slot s=?slot)eqn:E;[now apply IH|];split;[|now apply IH].
 rewrite tower_getw_setw_outside;[exact W|];apply Z.eqb_neq in E;unfold cm_range_disjoint,cm_temp_offset;lia.
Qed.
Lemma cm_temp_put_sim policy p st mem fid fp slot v spills : cm_spill_list_sim policy p st mem fid fp spills ->
 cm_spill_list_sim policy p st(tower_setw mem(fp+cm_temp_offset policy p fid slot)(cm_value_number st v))fid fp(cm_spill_put slot v spills).
Proof. intro SIM;split;[cbn[cm_spill_slot cm_spill_value];rewrite tower_getw_setw;apply cm_value_number_wrap|now apply cm_temp_remove_sim]. Qed.
Lemma cm_machine_temp_store sp ap p fid st ann vm slot v pc :
 cm_runtime_core(cm_source_function_policy sp)ap p fid st ann -> 0<=fid ->
 0<=slot<cm_temp_slots(cm_source_function_at sp fid p) -> cm_tagged_span_valid st ->
 cm_machine_state_sim(cm_source_function_policy sp)p st vm(cm_ann_calls ann)(cm_active_spill_frames fid st ann)[v][] ->
 cm_machine_state_sim(cm_source_function_policy sp)p st
 (TVMState pc[](tvm_calls vm)(tower_setw(tvm_mem vm)(cm_state_fp st+cm_temp_offset(cm_source_function_policy sp)p fid slot)(cm_value_number st v))(tvm_input vm)(tvm_output vm))
 (cm_ann_calls ann)(cm_active_spill_frames fid st(cm_ann_put_spill slot v ann))[][].
Proof.
 intros[BEFORE RT]FID SLOT TAG[M[P[F[C[[S SS][I[O STACK]]]]]]].
 pose proof(cm_runtime_temp_machine_safe _ _ _ _ _ _ _ _ _ _ _ _ RT FID SLOT)as[VALID[FP[CALLS SAVED]]].
 assert(OUT:forall a,cm_live_address st a -> a<cm_state_fp st+cm_temp_offset(cm_source_function_policy sp)p fid slot \/ cm_state_fp st+cm_temp_offset(cm_source_function_policy sp)p fid slot+8<=a).
 { intros a LIVE;eapply cm_runtime_temp_live_disjoint;eassumption. }
 unfold cm_machine_state_sim;split;[now apply cm_temp_initialized_sim|];split;[now apply cm_temp_provenance_sim|].
 split;[cbn[tvm_mem];now rewrite tower_getw_setw_outside|];split;[now apply cm_call_frames_sim_setw|].
 split;[split;[now apply cm_temp_put_sim|now apply cm_spill_frames_sim_setw]|];split;[exact I|];split;[exact O|];reflexivity.
Qed.
