Require Export SimpleC.EE.QCP_demos_human.cmc_target_loop_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_activate_initialized_sim sp p fid slot st mem : cm_regions_before(cm_state_regions st)(cm_state_nextgen st) ->
 cm_initialized_bytes_sim st mem -> cm_initialized_bytes_sim(cm_activate_local sp p fid slot st)mem.
Proof.
 intros BEFORE SIM a INIT LIVE;destruct(cm_activate_live_old_or_local _ _ _ _ _ _ BEFORE LIVE)as[OLD|LOCAL].
 - apply SIM;[apply andb_true_iff in INIT;exact(proj1 INIT)|exact OLD].
 - change(cm_clear_init(cm_state_init st)(cm_local_base sp p fid slot(cm_state_fp st))(cm_slot_size(cm_program_structs p)(cm_source_slot_at sp slot(cm_function_locals(cm_source_function_at sp fid p))))a=true)in INIT.
   unfold cm_clear_init in INIT;apply andb_true_iff in INIT;destruct INIT as[_ BAD];apply negb_true_iff in BAD.
   destruct LOCAL as[LO HI];apply Z.leb_le in LO;apply Z.ltb_lt in HI;rewrite LO,HI in BAD;discriminate.
Qed.
Lemma cm_activate_provenance_sim sp p fid slot st mem : cm_regions_before(cm_state_regions st)(cm_state_nextgen st) ->
 cm_tags_generation_below(cm_state_nextgen st)(cm_state_tags st) ->
 cm_stored_provenance_sim st mem -> cm_stored_provenance_sim(cm_activate_local sp p fid slot st)mem.
Proof.
 intros BEFORE GEN SIM a TAG LIVE;pose proof TAG as TAG0;apply andb_true_iff in TAG;destruct TAG as[TAG _].
 destruct(cm_activate_live_old_or_local _ _ _ _ _ _ BEFORE LIVE)as[OLD|LOCAL].
 - specialize(SIM a TAG OLD);split;[eapply cm_clear_tagged_init;[exact TAG0|exact(proj1 SIM)]|].
   cbn[cm_activate_local cm_state_tags];rewrite(cm_value_number_bases _ st _ (cm_state_nextgen st)(cm_activate_local_bases _ _ _ _ _) (GEN a));exact(proj2 SIM).
 - assert(FALSE:cm_clear_init(fun _=>true)(cm_local_base sp p fid slot(cm_state_fp st))(cm_slot_size(cm_program_structs p)(cm_source_slot_at sp slot(cm_function_locals(cm_source_function_at sp fid p))))a=true).
   { eapply cm_clear_tagged_init;[exact TAG0|reflexivity]. }
   unfold cm_clear_init in FALSE;cbn[andb]in FALSE;apply negb_true_iff in FALSE.
   destruct LOCAL as[LO HI];apply Z.leb_le in LO;apply Z.ltb_lt in HI;rewrite LO,HI in FALSE;discriminate.
Qed.
Lemma cm_spill_list_sim_bases policy p old new limit mem fid fp spills :
 cm_region_bases_below_equal(cm_state_regions new)(cm_state_regions old)limit -> cm_spills_generation_below limit spills ->
 cm_spill_list_sim policy p old mem fid fp spills -> cm_spill_list_sim policy p new mem fid fp spills.
Proof.
 intros BASE;induction spills as[|s rest IH];cbn[cm_spills_generation_below cm_spill_list_sim];[auto|].
 intros[G GS][H HS];split;[rewrite(cm_value_number_bases _ _ _ _ BASE G);exact H|now apply IH].
Qed.
Lemma cm_spill_frames_sim_bases policy p old new limit mem frames :
 cm_region_bases_below_equal(cm_state_regions new)(cm_state_regions old)limit -> cm_spill_frames_generation_below limit frames ->
 cm_spill_frames_sim policy p old mem frames -> cm_spill_frames_sim policy p new mem frames.
Proof.
 intros BASE;induction frames as[|f rest IH];cbn[cm_spill_frames_generation_below cm_spill_frames_sim];[auto|].
 intros[G GS][H HS];split;[now apply cm_spill_list_sim_bases with(old:=old)(limit:=limit)|now apply IH].
Qed.
Lemma cm_machine_activate_local_empty sp p fid slot st vm calls spills :
 cm_regions_before(cm_state_regions st)(cm_state_nextgen st) -> cm_tags_generation_below(cm_state_nextgen st)(cm_state_tags st) ->
 cm_spill_frames_generation_below(cm_state_nextgen st)spills ->
 cm_machine_state_sim(cm_source_function_policy sp)p st vm calls spills[][] ->
 cm_machine_state_sim(cm_source_function_policy sp)p(cm_activate_local sp p fid slot st)vm calls spills[][].
Proof.
 intros BEFORE GEN SG[M[P[F[C[S[I[O STACK]]]]]]];unfold cm_machine_state_sim.
 split;[now apply cm_activate_initialized_sim|];split;[now apply cm_activate_provenance_sim|];split;[exact F|];split;[exact C|].
 split;[eapply cm_spill_frames_sim_bases;[apply cm_activate_local_bases|exact SG|exact S]|].
 split;[exact I|];split;[exact O|];exact STACK.
Qed.
