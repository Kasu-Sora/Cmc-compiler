Require Export SimpleC.EE.QCP_demos_human.cmc_runtime_static_geometry_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_slots_wf_nonnegative_members structs slots : cm_slots_wf structs slots -> Forall (fun s=>0<=cm_slot_size structs s) slots.
Proof.
 intros WF; apply Forall_forall; intros s IN; apply In_nth with (d:=cm_default_slot) in IN; destruct IN as [i [B <-]].
 assert (BI:0<=Z.of_nat i<Zlength slots) by (rewrite Zlength_correct; lia).
 specialize (WF _ BI); unfold cm_slot_wf,cm_slot_at in WF; rewrite Nat2Z.id in WF; intuition lia.
Qed.
Lemma cm_slots_size_nonnegative_from_members structs slots : Forall (fun s=>0<=cm_slot_size structs s) slots -> 0<=cm_slots_size structs slots.
Proof. intro H; induction H; cbn [cm_slots_size]; lia. Qed.
Lemma cm_slots_prefix_cell_bounds_nat structs slots i : Forall (fun s=>0<=cm_slot_size structs s) slots -> (i<length slots)%nat ->
 0<=cm_slots_prefix structs slots (Z.of_nat i) /\ cm_slots_prefix structs slots (Z.of_nat i)+cm_slot_size structs (nth i slots cm_default_slot)<=cm_slots_size structs slots.
Proof.
 revert i; induction slots as [|s slots IH]; intros i ALL B; [cbn in B; lia|]; inversion ALL as [|? ? S T]; subst.
 destruct i as [|i].
 - cbn [cm_slots_prefix nth Z.of_nat Z.eqb cm_slots_size]; pose proof (cm_slots_size_nonnegative_from_members _ _ T); lia.
 - assert (NZ:(Z.of_nat (Datatypes.S i)=?0)=false) by (apply Z.eqb_neq; lia).
   cbn [cm_slots_prefix]; rewrite NZ; replace (Z.of_nat (Datatypes.S i)-1) with (Z.of_nat i) by lia.
   specialize (IH i T ltac:(cbn in B; lia)); cbn [nth cm_slots_size]; lia.
Qed.
Lemma cm_source_slot_at_valid sp slots slot : 0<=slot<Zlength slots -> cm_source_slot_at sp slot slots=cm_slot_at slot slots.
Proof.
 intros [L U]; unfold cm_source_slot_at,cm_slot_at; apply cm_source_at_valid; [exact L|].
 apply nth_error_nth'; rewrite Zlength_correct in U; lia.
Qed.
Lemma cm_slots_prefix_cell_bounds structs slots slot : cm_slots_wf structs slots -> 0<=slot<Zlength slots ->
 0<=cm_slots_prefix structs slots slot /\ cm_slots_prefix structs slots slot+cm_slot_size structs (cm_slot_at slot slots)<=cm_slots_size structs slots.
Proof.
 intros WF B; pose proof (cm_slots_prefix_cell_bounds_nat structs slots (Z.to_nat slot) (cm_slots_wf_nonnegative_members _ _ WF) ltac:(rewrite Zlength_correct in B; lia)) as H.
 rewrite Z2Nat.id in H by lia; exact H.
Qed.
Lemma cm_regions_for_slots_generation_bounds structs slots gen base r : In r (cm_regions_for_slots structs slots gen base) -> gen<=cm_region_gen r<gen+Zlength slots.
Proof.
 revert gen base; induction slots as [|s slots IH]; intros gen base IN; [contradiction|].
 cbn [cm_regions_for_slots] in IN; rewrite Zlength_cons; destruct IN as [<-|IN].
 - cbn [cm_region_gen]; pose proof (ListLib.General.Length.Zlength_nonneg slots); lia.
 - specialize (IH (gen+1) (base+cm_slot_size structs s) IN); lia.
Qed.
Lemma cm_regions_for_slots_unique structs slots gen base : cm_region_generations_unique (cm_regions_for_slots structs slots gen base).
Proof.
 revert gen base; induction slots; intros gen base; [exact I|]; split; [|apply IHslots].
 intros r IN; pose proof (cm_regions_for_slots_generation_bounds _ _ _ _ _ IN); cbn [cm_region_gen]; lia.
Qed.
Lemma cm_region_base_prefix_unique prefix tail r : cm_region_generations_unique prefix -> In r prefix -> cm_region_base (prefix++tail) (cm_region_gen r)=cm_region_base_field r.
Proof.
 induction prefix as [|a rs IH]; intros U IN; [contradiction|]; destruct U as [SEP U]; cbn [app cm_region_base]; destruct IN as [<-|IN].
 - now rewrite Z.eqb_refl.
 - assert (NE:cm_region_gen a=?cm_region_gen r=false) by (apply Z.eqb_neq; intro E; apply (SEP r IN); symmetry; exact E).
   rewrite NE; now apply IH.
Qed.
Lemma cm_regions_for_slots_geometry structs slots gen base r : Forall (fun s=>0<=cm_slot_size structs s) slots -> In r (cm_regions_for_slots structs slots gen base) ->
 cm_region_lo r=0 /\ 0<=cm_region_hi r /\ base<=cm_region_base_field r /\ cm_region_base_field r+cm_region_hi r<=base+cm_slots_size structs slots.
Proof.
 revert gen base; induction slots as [|s slots IH]; intros gen base ALL IN; [contradiction|].
 inversion ALL as [|? ? S T]; subst; destruct IN as [<-|IN].
 - cbn [cm_region_lo cm_region_hi cm_region_base_field cm_slots_size]; pose proof (cm_slots_size_nonnegative_from_members _ _ T); repeat split; lia.
 - specialize (IH (gen+1) (base+cm_slot_size structs s) T IN); cbn [cm_slots_size]; intuition lia.
Qed.
Lemma cm_region_prefix_safe_append policy p all fid fp prefix old : (forall r,In r prefix -> cm_region_frame_safe policy p all fid fp r) -> cm_region_prefix_safe policy p all fid fp (prefix++old) old.
Proof.
 induction prefix as [|r rs IH]; intro SAFE; [apply cm_region_prefix_safe_refl|].
 cbn [app cm_region_prefix_safe]; destruct (cm_regions_eqb (r::rs++old) old); [exact I|].
 split; [apply SAFE; now left|apply IH; intros x IN; apply SAFE; now right].
Qed.
Lemma cm_parameter_region_prefix_safe policy p fid fp gen old : cm_function_wf policy p (cm_function_at policy fid (cm_program_functions p)) ->
 let fresh:=cm_regions_for_slots (cm_program_structs p) (cm_function_params (cm_function_at policy fid (cm_program_functions p))) gen (fp+8) in
 cm_region_prefix_safe policy p (fresh++old) fid fp (fresh++old) old.
Proof.
 intros [_ [[PW _] [LW _]]]; cbv zeta; apply cm_region_prefix_safe_append; intros r IN; right.
 rewrite (cm_region_base_prefix_unique _ _ _ (cm_regions_for_slots_unique _ _ _ _) IN).
 pose proof (cm_regions_for_slots_geometry _ _ _ _ _ (cm_slots_wf_nonnegative_members _ _ PW) IN) as [LO [HI [LOW UP]]].
 pose proof (cm_slots_size_nonnegative__call_bounds _ _ LW); unfold cm_temp_offset; rewrite LO; repeat split; lia.
Qed.
Lemma cm_local_region_frame_safe sp p fid slot st : cm_function_wf (cm_source_function_policy sp) p (cm_source_function_at sp fid p) -> 0<=slot<Zlength (cm_function_locals (cm_source_function_at sp fid p)) ->
 let r:=CMRegion (cm_state_nextgen st) (cm_local_base sp p fid slot (cm_state_fp st)) 0 (cm_slot_size (cm_program_structs p) (cm_source_slot_at sp slot (cm_function_locals (cm_source_function_at sp fid p)))) true true in
 cm_region_frame_safe (cm_source_function_policy sp) p (r::cm_state_regions st) fid (cm_state_fp st) r.
Proof.
 intros [_ [[PW _] [LW _]]] B; cbv zeta; right; cbn [cm_region_base cm_region_gen cm_region_lo cm_region_hi cm_region_base_field]; rewrite Z.eqb_refl.
 rewrite (cm_source_slot_at_valid _ _ _ B); pose proof (cm_slots_prefix_cell_bounds _ _ _ LW B) as [L U].
 pose proof (LW _ B) as SW; unfold cm_slot_wf in SW; pose proof (cm_slots_size_nonnegative__call_bounds _ _ PW).
 unfold cm_local_base,cm_temp_offset,cm_source_function_at in *; repeat split; intuition lia.
Qed.
Lemma cm_runtime_stack_region_cons policy ap p all cursors fid fp active spills saved calls r : 0<=fid -> cm_region_frame_safe policy p all fid fp r -> cm_runtime_stack policy ap p all fid fp active cursors spills saved calls -> cm_runtime_stack policy ap p all fid fp (r::active) cursors spills saved calls.
Proof.
 revert fid fp active spills saved calls; induction cursors as [|c rest IH]; intros fid fp active spills saved calls F SAFE H; [contradiction|].
 cbn [cm_runtime_stack] in *; destruct (cm_phase_is_call (cm_cursor_phase c)).
 - destruct H as [PRE T]; split; [cbn [cm_region_prefix_safe]; destruct (cm_regions_eqb (r::active) (cm_phase_oldregions (cm_cursor_phase c))); auto|exact T].
 - destruct (cm_phase_is_scope (cm_cursor_phase c)).
   + destruct H as [FID [PRE T]]; split; [exact FID|]; split; [cbn [cm_region_prefix_safe]; destruct (cm_regions_eqb (r::active) (cm_phase_oldregions (cm_cursor_phase c))); auto|exact T].
   + destruct (cm_phase_is_halt (cm_cursor_phase c)); [destruct H as [BAD _]; lia|eapply IH; eauto].
Qed.
Lemma cm_runtime_core_activate_local sp ap p fid slot st ann : cm_function_wf (cm_source_function_policy sp) p (cm_source_function_at sp fid p) -> 0<=fid -> 0<=slot<Zlength (cm_function_locals (cm_source_function_at sp fid p)) -> cm_runtime_core (cm_source_function_policy sp) ap p fid st ann -> cm_runtime_core (cm_source_function_policy sp) ap p fid (cm_activate_local sp p fid slot st) ann.
Proof.
 intros WF F B [BEFORE RUN]; split; [now apply cm_activate_local_regions_before|].
 change (cm_runtime_stack (cm_source_function_policy sp) ap p (cm_state_regions (cm_activate_local sp p fid slot st)) fid (cm_state_fp st) (cm_state_regions (cm_activate_local sp p fid slot st)) (cm_ann_cursors ann) (cm_ann_spills ann) (cm_ann_saved ann) (cm_ann_calls ann)).
 apply cm_runtime_stack_region_cons; [exact F|now apply cm_local_region_frame_safe|].
 apply cm_runtime_stack_fresh_region; assumption.
Qed.
