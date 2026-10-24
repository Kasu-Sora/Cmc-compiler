Require Export SimpleC.EE.QCP_demos_human.cmc_runtime_memory_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_region_prefix_suffix_incl policy p all fid fp active old : cm_region_prefix_safe policy p all fid fp active old -> incl old active.
Proof.
 induction active as [|r rs IH]; cbn [cm_region_prefix_safe]; [intros ->; apply incl_refl|].
 destruct (cm_regions_eqb (r::rs) old) eqn:E; [apply cm_regions_eqb_spec in E; intros _; subst; apply incl_refl|].
 intros [_ H] x IN; right; exact (IH H x IN).
Qed.
Lemma cm_region_dead_suffix_incl active old : cm_region_dead_prefix active old -> incl old active.
Proof.
 induction active as [|r rs IH]; cbn [cm_region_dead_prefix]; [intros ->; apply incl_refl|].
 destruct (cm_regions_eqb (r::rs) old) eqn:E; [apply cm_regions_eqb_spec in E; intros _; subst; apply incl_refl|].
 intros [_ H] x IN; right; exact (IH H x IN).
Qed.
Lemma cm_regions_before_prefix_suffix policy p all fid fp active old limit : cm_region_prefix_safe policy p all fid fp active old -> cm_regions_before active limit -> cm_regions_before old limit.
Proof. intros H B r IN; apply B; eapply cm_region_prefix_suffix_incl; eauto. Qed.
Lemma cm_regions_before_dead_suffix active old limit : cm_region_dead_prefix active old -> cm_regions_before active limit -> cm_regions_before old limit.
Proof. intros H B r IN; apply B; eapply cm_region_dead_suffix_incl; eauto. Qed.
Lemma cm_region_frame_safe_below_bases policy p newer older limit fid fp r : cm_region_bases_below_equal newer older limit -> cm_region_gen r<limit -> cm_region_frame_safe policy p older fid fp r -> cm_region_frame_safe policy p newer fid fp r.
Proof. intros B L; unfold cm_region_frame_safe; now rewrite (B _ L). Qed.
Lemma cm_region_prefix_safe_below_bases policy p newer older limit fid fp active old : cm_region_bases_below_equal newer older limit -> cm_regions_before active limit -> cm_region_prefix_safe policy p older fid fp active old -> cm_region_prefix_safe policy p newer fid fp active old.
Proof.
 intros B; induction active as [|r rs IH]; cbn [cm_region_prefix_safe]; intros A H; [exact H|].
 destruct (cm_regions_eqb (r::rs) old); [exact I|]; apply cm_regions_before_cons in A; destruct A as [R RS]; destruct H as [H HS]; split; [eapply cm_region_frame_safe_below_bases; eauto|now apply IH].
Qed.
Lemma cm_static_regions_layout_below_bases p newer older limit : cm_region_bases_below_equal newer older limit -> cm_regions_before (cm_static_regions p) limit -> cm_static_regions_layout p older -> cm_static_regions_layout p newer.
Proof. intros B G H r IN LIVE; unfold cm_static_regions_layout in H; rewrite (B _ (G r IN)); now apply H. Qed.
Lemma cm_runtime_stack_below_bases policy ap p newer older limit cursors fid fp active spills saved calls : cm_region_bases_below_equal newer older limit -> cm_regions_before active limit -> cm_runtime_stack policy ap p older fid fp active cursors spills saved calls -> cm_runtime_stack policy ap p newer fid fp active cursors spills saved calls.
Proof.
 intro B; revert fid fp active spills saved calls; induction cursors as [|c rest IH]; intros fid fp active spills saved calls A H; [contradiction|].
 cbn [cm_runtime_stack] in *; destruct (cm_phase_is_call (cm_cursor_phase c)).
 - destruct H as [PREFIX [SEG [SP [S [C [BASE [SAVED [FID [FP REC]]]]]]]]].
   split; [eapply cm_region_prefix_safe_below_bases; eauto|].
   repeat first [assumption|match goal with |- _ /\ _=>split end].
   eapply IH; [eapply cm_regions_before_prefix_suffix; eauto|exact REC].
 - destruct (cm_phase_is_scope (cm_cursor_phase c)).
   + destruct H as [FID [PREFIX REC]]; split; [exact FID|]; split; [eapply cm_region_prefix_safe_below_bases; eauto|].
     eapply IH; [eapply cm_regions_before_prefix_suffix; eauto|exact REC].
   + destruct (cm_phase_is_halt (cm_cursor_phase c)).
     * destruct H as [FID [FP [DEAD [LOW [UP [R [S [SV [C STATIC]]]]]]]]].
       repeat first [assumption|match goal with |- _ /\ _=>split end].
       eapply cm_static_regions_layout_below_bases; [exact B|eapply cm_regions_before_dead_suffix; eauto|exact STATIC].
     * eapply IH; eauto.
Qed.
Definition cm_region_bases_equal lhs rhs : Prop := forall gen,cm_region_base lhs gen=cm_region_base rhs gen.
Lemma cm_region_frame_safe_bases policy p newer older fid fp r : cm_region_bases_equal newer older -> cm_region_frame_safe policy p older fid fp r -> cm_region_frame_safe policy p newer fid fp r.
Proof. intros B; unfold cm_region_frame_safe; now rewrite (B (cm_region_gen r)). Qed.
Lemma cm_region_prefix_safe_bases policy p newer older fid fp active old : cm_region_bases_equal newer older -> cm_region_prefix_safe policy p older fid fp active old -> cm_region_prefix_safe policy p newer fid fp active old.
Proof. intros B; induction active as [|r rs IH]; cbn [cm_region_prefix_safe]; [auto|destruct (cm_regions_eqb (r::rs) old); [auto|intros [H HS]; split; [eapply cm_region_frame_safe_bases; eauto|now apply IH]]]. Qed.
Lemma cm_static_regions_layout_bases p newer older : cm_region_bases_equal newer older -> cm_static_regions_layout p older -> cm_static_regions_layout p newer.
Proof. intros B H r IN LIVE; rewrite (B (cm_region_gen r)); now apply H. Qed.
Lemma cm_runtime_stack_bases policy ap p newer older cursors fid fp active spills saved calls : cm_region_bases_equal newer older -> cm_runtime_stack policy ap p older fid fp active cursors spills saved calls -> cm_runtime_stack policy ap p newer fid fp active cursors spills saved calls.
Proof.
 intro B; revert fid fp active spills saved calls; induction cursors as [|c rest IH]; intros fid fp active spills saved calls H; [contradiction|].
 cbn [cm_runtime_stack] in *; destruct (cm_phase_is_call (cm_cursor_phase c)).
 - destruct H as [PREFIX [SEG [SP [S [C [BASE [SAVED [FID [FP REC]]]]]]]]].
   split; [eapply cm_region_prefix_safe_bases; eauto|].
   repeat first [assumption|match goal with |- _ /\ _=>split end]; eapply IH; exact REC.
 - destruct (cm_phase_is_scope (cm_cursor_phase c)).
   + destruct H as [FID [PREFIX REC]]; split; [exact FID|]; split; [eapply cm_region_prefix_safe_bases; eauto|eapply IH; exact REC].
   + destruct (cm_phase_is_halt (cm_cursor_phase c)).
     * destruct H as [FID [FP [DEAD [LOW [UP [R [S [SV [C STATIC]]]]]]]]].
       repeat first [assumption|match goal with |- _ /\ _=>split end]; eapply cm_static_regions_layout_bases; eauto.
     * eapply IH; eauto.
Qed.
Lemma cm_region_dead_prefix_cons r active old : cm_region_live r=false -> cm_region_dead_prefix active old -> cm_region_dead_prefix (r::active) old.
Proof. cbn [cm_region_dead_prefix]; destruct (cm_regions_eqb (r::active) old); auto. Qed.
Lemma cm_region_prefix_dead_cons policy p all fid fp r active old : cm_region_live r=false -> cm_region_prefix_safe policy p all fid fp active old -> cm_region_prefix_safe policy p all fid fp (r::active) old.
Proof. cbn [cm_region_prefix_safe]; destruct (cm_regions_eqb (r::active) old); [auto|intros H T; split; [now left|exact T]]. Qed.
Lemma cm_region_dead_prefix_trans a b c : cm_region_dead_prefix a b -> cm_region_dead_prefix b c -> cm_region_dead_prefix a c.
Proof.
 induction a as [|r rs IH]; cbn [cm_region_dead_prefix]; [intros -> H; exact H|].
 destruct (cm_regions_eqb (r::rs) b) eqn:E; [apply cm_regions_eqb_spec in E; subst; auto|].
 intros [DEAD T] H; apply cm_region_dead_prefix_cons; [exact DEAD|now apply IH].
Qed.
Lemma cm_region_dead_prefix_safe_trans policy p all fid fp a b c : cm_region_dead_prefix a b -> cm_region_prefix_safe policy p all fid fp b c -> cm_region_prefix_safe policy p all fid fp a c.
Proof.
 induction a as [|r rs IH]; cbn [cm_region_dead_prefix]; [intros -> H; exact H|].
 destruct (cm_regions_eqb (r::rs) b) eqn:E; [apply cm_regions_eqb_spec in E; subst; auto|].
 intros [DEAD T] H; apply cm_region_prefix_dead_cons; [exact DEAD|now apply IH].
Qed.
Lemma cm_runtime_stack_dead_prefix policy ap p all cursors fid fp active old spills saved calls : cm_region_dead_prefix active old -> cm_runtime_stack policy ap p all fid fp old cursors spills saved calls -> cm_runtime_stack policy ap p all fid fp active cursors spills saved calls.
Proof.
 revert fid fp active old spills saved calls; induction cursors as [|c rest IH]; intros fid fp active old spills saved calls DEAD H; [contradiction|].
 cbn [cm_runtime_stack] in *; destruct (cm_phase_is_call (cm_cursor_phase c)).
 - destruct H as [PREFIX T]; split; [eapply cm_region_dead_prefix_safe_trans; eauto|exact T].
 - destruct (cm_phase_is_scope (cm_cursor_phase c)).
   + destruct H as [FID [PREFIX T]]; split; [exact FID|]; split; [eapply cm_region_dead_prefix_safe_trans; eauto|exact T].
   + destruct (cm_phase_is_halt (cm_cursor_phase c)).
     * destruct H as [FID [FP [D T]]]; split; [exact FID|]; split; [exact FP|]; split; [eapply cm_region_dead_prefix_trans; eauto|exact T].
     * eapply IH; eauto.
Qed.
Lemma cm_runtime_stack_restore_incl policy ap p current old cursors fid fp spills saved calls : cm_region_generations_incl old current -> cm_runtime_stack policy ap p current fid fp old cursors spills saved calls -> cm_runtime_stack policy ap p (cm_restore_regions current old) fid fp (cm_restore_regions current old) cursors spills saved calls.
Proof.
 intros INC H; eapply cm_runtime_stack_dead_prefix; [apply cm_restore_regions_dead_prefix|].
 eapply cm_runtime_stack_bases; [intro gen; now apply cm_restore_regions_base_transport|exact H].
Qed.
Lemma cm_runtime_stack_regions_for_slots policy ap p structs slots gen base regions fid fp cursors spills saved calls : cm_regions_before regions gen -> cm_runtime_stack policy ap p regions fid fp regions cursors spills saved calls -> cm_runtime_stack policy ap p (cm_regions_for_slots structs slots gen base++regions) fid fp regions cursors spills saved calls.
Proof. intros B H; eapply cm_runtime_stack_below_bases with (limit:=gen); [apply cm_regions_for_slots_bases; lia|exact B|exact H]. Qed.
Lemma cm_runtime_stack_fresh_region policy ap p r regions fid fp cursors spills saved calls : cm_regions_before regions (cm_region_gen r) -> cm_runtime_stack policy ap p regions fid fp regions cursors spills saved calls -> cm_runtime_stack policy ap p (r::regions) fid fp regions cursors spills saved calls.
Proof. intros B H; eapply cm_runtime_stack_below_bases with (limit:=cm_region_gen r); [apply cm_region_bases_cons_fresh; lia|exact B|exact H]. Qed.
