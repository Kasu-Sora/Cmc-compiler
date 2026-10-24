Require Export SimpleC.EE.QCP_demos_human.cmc_target_halt_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_restore_value_number st env fp old v : cm_region_generations_incl old(cm_state_regions st) ->
 cm_value_number(cm_restore_call st env fp old)v=cm_value_number st v.
Proof.
 intro INC;destruct v;cbn[cm_value_number cm_restore_call cm_state_regions];try reflexivity;
 now rewrite cm_restore_regions_base_transport.
Qed.
Lemma cm_restore_init_old all current old init a : cm_restore_init all current old init a=true -> init a=true.
Proof.
 revert init;induction current as[|r rest IH];intros init;cbn[cm_restore_init];[auto|].
 destruct(cm_regions_eqb(r::rest)old);[auto|];destruct(cm_region_live r);intro H;apply IH in H;
 [unfold cm_clear_init in H;now apply andb_true_iff in H|exact H].
Qed.
Lemma cm_restore_initialized_sim st env fp old mem : incl old(cm_state_regions st) ->
 cm_initialized_bytes_sim st mem -> cm_initialized_bytes_sim(cm_restore_call st env fp old)mem.
Proof.
 intros INC SIM a INIT LIVE;apply cm_restore_init_old in INIT;
 pose proof(cm_restore_call_live_old _ _ _ _ _ INC LIVE)as LIVE0;exact(SIM a INIT LIVE0).
Qed.
Lemma cm_clear_tagged_init tags init base width a : cm_clear_tagged tags base width a=true -> init a=true -> cm_clear_init init base width a=true.
Proof.
 unfold cm_clear_tagged,cm_clear_init;intros TAG INIT;rewrite INIT;cbn[andb].
 apply andb_true_iff in TAG;destruct TAG as[_ TAG];apply negb_true_iff in TAG;apply negb_true_iff.
 destruct((base<=?a)&&(a<?base+width))eqn:H;[|reflexivity].
 apply andb_true_iff in H;destruct H as[LO HI];apply Z.leb_le in LO;apply Z.ltb_lt in HI.
 assert(W:(0<?width)=true)by(apply Z.ltb_lt;lia).
 assert(H:(a<?base+width)=true)by(apply Z.ltb_lt;lia).
 assert(L:(base<?a+8)=true)by(apply Z.ltb_lt;lia).
 rewrite W,H,L in TAG;discriminate.
Qed.
Lemma cm_restore_tagged_init all current old tags init a : cm_restore_tagged all current old tags a=true -> init a=true -> cm_restore_init all current old init a=true.
Proof.
 revert tags init;induction current as[|r rest IH];intros tags init;cbn[cm_restore_tagged cm_restore_init];[auto|].
 destruct(cm_regions_eqb(r::rest)old);[auto|];destruct(cm_region_live r);intros TAG INIT.
 - apply IH with(tags:=cm_clear_tagged tags (cm_region_base all(cm_region_gen r)+cm_region_lo r)(cm_region_hi r-cm_region_lo r));[exact TAG|].
   apply cm_restore_tagged_old in TAG;now apply cm_clear_tagged_init with(tags:=tags).
 - exact(IH tags init TAG INIT).
Qed.
Lemma cm_restore_provenance_sim st env fp old mem : incl old(cm_state_regions st) ->
 cm_stored_provenance_sim st mem -> cm_stored_provenance_sim(cm_restore_call st env fp old)mem.
Proof.
 intros INC SIM a TAG LIVE;pose proof TAG as TAG0;apply cm_restore_tagged_old in TAG.
 pose proof(cm_restore_call_live_old _ _ _ _ _ INC LIVE)as LIVE0;specialize(SIM a TAG LIVE0).
 split;[eapply cm_restore_tagged_init;[exact TAG0|exact(proj1 SIM)]|].
 cbn[cm_restore_call cm_state_tags];rewrite cm_restore_value_number by(unfold cm_region_generations_incl;now apply incl_map);exact(proj2 SIM).
Qed.
Lemma cm_restore_spill_list_sim policy p st env fp old mem fid base spills : cm_region_generations_incl old(cm_state_regions st) ->
 cm_spill_list_sim policy p st mem fid base spills -> cm_spill_list_sim policy p (cm_restore_call st env fp old)mem fid base spills.
Proof.
 intros INC;induction spills as[|s rest IH];cbn[cm_spill_list_sim];[auto|].
 intros[H T];split;[rewrite cm_restore_value_number by exact INC;exact H|now apply IH].
Qed.
Lemma cm_restore_spill_frames_sim policy p st env fp old mem frames : cm_region_generations_incl old(cm_state_regions st) ->
 cm_spill_frames_sim policy p st mem frames -> cm_spill_frames_sim policy p(cm_restore_call st env fp old)mem frames.
Proof.
 intros INC;induction frames as[|f rest IH];cbn[cm_spill_frames_sim];[auto|].
 intros[H T];split;[now apply cm_restore_spill_list_sim|now apply IH].
Qed.
Lemma cm_machine_sim_restore_scope policy p st env old vm calls frames vals suffix : incl old(cm_state_regions st) ->
 cm_machine_state_sim policy p st vm calls frames vals suffix ->
 cm_machine_state_sim policy p(cm_restore_scope st env old)vm calls frames vals suffix.
Proof.
 intros INC[M[P[F[C[S[I[O STACK]]]]]]];assert(GEN:cm_region_generations_incl old(cm_state_regions st))by(unfold cm_region_generations_incl;now apply incl_map).
 unfold cm_machine_state_sim;split;[now apply cm_restore_initialized_sim|];split;[now apply cm_restore_provenance_sim|].
 split;[exact F|];split;[exact C|];split;[now apply cm_restore_spill_frames_sim|];split;[exact I|];split;[exact O|].
 unfold cm_operand_suffix_sim in *;rewrite STACK;unfold cm_encode_values;f_equal;apply map_ext;intro v;symmetry;now apply cm_restore_value_number.
Qed.
