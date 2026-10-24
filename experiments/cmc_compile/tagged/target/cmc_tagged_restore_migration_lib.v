Require Export SimpleC.EE.QCP_demos_human.cmc_tagged_allocation_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_restore_regions_old_incl current old : incl old (cm_restore_regions current old).
Proof. induction current as [|r rs IH]; cbn [cm_restore_regions]; [apply incl_refl|]. destruct (cm_regions_eqb (r::rs) old); [apply incl_refl|intros x X; right; now apply IH]. Qed.
Lemma cm_restore_regions_live_old current old r : In r (cm_restore_regions current old) -> cm_region_live r=true -> In r old.
Proof.
 induction current as [|h rest IH]; cbn [cm_restore_regions]; [auto|]. destruct (cm_regions_eqb (h::rest) old); [auto|].
 intros [EQ|IN] LIVE; [subst r; destruct h; discriminate|now apply IH].
Qed.
Lemma cm_restore_tagged_old all current old tagged a : cm_restore_tagged all current old tagged a=true -> tagged a=true.
Proof.
 revert tagged; induction current as [|r rest IH]; intros tagged; cbn [cm_restore_tagged]; [auto|].
 destruct (cm_regions_eqb (r::rest) old); [auto|]. destruct (cm_region_live r); intro H; apply IH in H; [unfold cm_clear_tagged in H; now apply andb_true_iff in H|exact H].
Qed.
Lemma cm_restore_tagged_live_member all current old tagged a b r :
 cm_restore_tagged all current old tagged a=true -> a<=b<a+8 ->
 In r current -> cm_region_live r=true ->
 cm_region_base all (cm_region_gen r)+cm_region_lo r<=b<cm_region_base all (cm_region_gen r)+cm_region_hi r -> In r old.
Proof.
 revert tagged; induction current as [|h rest IH]; intros tagged TAG AB IN LIVE RANGE; [contradiction|].
 cbn [cm_restore_tagged] in TAG; destruct (cm_regions_eqb (h::rest) old) eqn:E.
 - apply cm_regions_eqb_spec in E; now rewrite <-E.
 - destruct IN as [EQ|IN].
   + subst h; rewrite LIVE in TAG; apply cm_restore_tagged_old in TAG.
     assert (W:0<cm_region_hi r-cm_region_lo r) by lia.
     destruct (cm_clear_tagged_survives _ _ _ _ W TAG) as [_ OUT]; exfalso; lia.
   + eapply IH; eassumption.
Qed.
Lemma cm_restore_call_live_old st env fp old a : incl old (cm_state_regions st) ->
 cm_live_address (cm_restore_call st env fp old) a -> cm_live_address st a.
Proof.
 intros INC [r [IN [LIVE [LO HI]]]]. pose proof (cm_restore_regions_live_old _ _ _ IN LIVE) as OLD.
 assert (GEN:cm_region_generations_incl old (cm_state_regions st)) by (unfold cm_region_generations_incl; now apply incl_map).
 change (cm_region_base (cm_restore_regions (cm_state_regions st) old) (cm_region_gen r)+cm_region_lo r<=a) in LO.
 change (a<cm_region_base (cm_restore_regions (cm_state_regions st) old) (cm_region_gen r)+cm_region_hi r) in HI.
 rewrite cm_restore_regions_base_transport in LO,HI by exact GEN.
 exists r; split; [now apply INC|auto].
Qed.
Lemma cm_tagged_span_restore_call st env fp old : incl old (cm_state_regions st) -> cm_tagged_span_valid st -> cm_tagged_span_valid (cm_restore_call st env fp old).
Proof.
 intros INC VALID a TAG LIVE; pose proof TAG as TAG0; apply cm_restore_tagged_old in TAG0.
 pose proof (cm_restore_call_live_old _ _ _ _ _ INC LIVE) as OLDLIVE; specialize (VALID a TAG0 OLDLIVE).
 intros b AB; destruct (VALID b AB) as [r [IN [RL RANGE]]].
 assert (OLD:In r old) by (eapply (cm_restore_tagged_live_member (cm_state_regions st) (cm_state_regions st) old (cm_state_tagged st) a b r); eassumption).
 assert (GEN:cm_region_generations_incl old (cm_state_regions st)) by (unfold cm_region_generations_incl; now apply incl_map).
 exists r; split; [now apply cm_restore_regions_old_incl|]. split; [exact RL|].
 change (cm_region_base (cm_restore_regions (cm_state_regions st) old) (cm_region_gen r)+cm_region_lo r<=b /\ b<cm_region_base (cm_restore_regions (cm_state_regions st) old) (cm_region_gen r)+cm_region_hi r).
 now rewrite cm_restore_regions_base_transport by exact GEN.
Qed.
Lemma cm_tagged_span_restore_scope st env old : incl old (cm_state_regions st) -> cm_tagged_span_valid st -> cm_tagged_span_valid (cm_restore_scope st env old).
Proof. apply cm_tagged_span_restore_call. Qed.
