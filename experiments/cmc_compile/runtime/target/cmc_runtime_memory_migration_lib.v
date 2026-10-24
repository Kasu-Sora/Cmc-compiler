Require Export SimpleC.EE.QCP_demos_human.cmc_runtime_stack_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Definition cm_range_disjoint lhs lw rhs rw : Prop := lhs+lw<=rhs \/ rhs+rw<=lhs.
Fixpoint cm_call_frames_range_safe base width calls : Prop := match calls with []=>True | f::rest=>cm_range_disjoint base width (cm_call_sim_base f) 8 /\ cm_call_frames_range_safe base width rest end.
Fixpoint cm_spill_list_range_safe policy p fid fp base width spills : Prop := match spills with []=>True | s::rest=>cm_range_disjoint base width (fp+cm_temp_offset policy p fid (cm_spill_slot s)) 8 /\ cm_spill_list_range_safe policy p fid fp base width rest end.
Fixpoint cm_spill_frames_range_safe policy p base width frames : Prop := match frames with []=>True | f::rest=>cm_spill_list_range_safe policy p (cm_spill_frame_fid f) (cm_spill_frame_fp f) base width (cm_spill_frame_spills f) /\ cm_spill_frames_range_safe policy p base width rest end.
Definition cm_machine_range_safe policy p base width calls frames : Prop := cm_range_disjoint base width 8 8 /\ cm_call_frames_range_safe base width calls /\ cm_spill_frames_range_safe policy p base width frames.
Definition cm_region_runtime_safe policy p calls frames regions r : Prop := cm_region_live r=false \/
 (0<=cm_region_lo r /\ cm_region_lo r<=cm_region_hi r /\ 0<=cm_region_base regions (cm_region_gen r)+cm_region_lo r /\ cm_region_base regions (cm_region_gen r)+cm_region_hi r<=1048576 /\
 cm_machine_range_safe policy p (cm_region_base regions (cm_region_gen r)+cm_region_lo r) (cm_region_hi r-cm_region_lo r) calls frames).
Definition cm_regions_runtime_safe policy p calls frames regions : Prop := forall r,In r regions -> cm_region_runtime_safe policy p calls frames regions r.
Definition cm_runtime_memory_layout policy p st calls frames : Prop := cm_regions_runtime_safe policy p calls frames (cm_state_regions st).
Lemma cm_call_frames_lower_range calls lower base width : cm_call_frames_lower lower calls -> base+width<=lower -> cm_call_frames_range_safe base width calls.
Proof. intros H B; induction calls; [exact I|destruct H as [L H]; split; [left; lia|now apply IHcalls]]. Qed.
Lemma cm_spill_list_lower_range policy p fid fp spills lower base width : cm_spill_list_lower policy p lower fid fp spills -> base+width<=lower -> cm_spill_list_range_safe policy p fid fp base width spills.
Proof. intros H B; induction spills; [exact I|destruct H as [L H]; split; [left; lia|now apply IHspills]]. Qed.
Lemma cm_spill_frames_lower_range policy p frames lower base width : cm_spill_frames_lower policy p lower frames -> base+width<=lower -> cm_spill_frames_range_safe policy p base width frames.
Proof. intros H B; induction frames; [exact I|destruct H as [L H]; split; [eapply cm_spill_list_lower_range; eauto|now apply IHframes]]. Qed.
Lemma cm_spills_before_range_safe policy p fid fp oldfp base width spills : cm_spills_within_frame policy p fid fp oldfp spills -> oldfp<=base -> cm_spill_list_range_safe policy p fid fp base width spills.
Proof. intros H B; induction spills; [exact I|destruct H as [L [U H]]; split; [right; lia|now apply IHspills]]. Qed.
Lemma cm_runtime_stack_frame_range policy ap p all cursors fid fp active spills saved calls base width :
 cm_runtime_stack policy ap p all fid fp active cursors spills saved calls -> 0<=fid -> fp+8<=base -> base+width<=fp+cm_temp_offset policy p fid 0 ->
 cm_call_frames_range_safe base width calls /\ cm_spill_frames_range_safe policy p base width (CMSpillFrame fid fp spills::saved).
Proof.
 intros H F L U; pose proof (cm_runtime_stack_current_machine_lower _ _ _ _ _ _ _ _ _ _ _ H F) as [C [BASE [CL [SL SFL]]]].
 destruct calls; [contradiction|]; cbn in BASE,CL; split.
 - split; [right; lia|eapply cm_call_frames_lower_range; eauto].
 - split; [eapply cm_spill_list_lower_range; eauto|eapply cm_spill_frames_lower_range; eauto].
Qed.
Lemma cm_runtime_stack_region_safe policy ap p all cursors fid fp active spills saved calls region :
 cm_runtime_stack policy ap p all fid fp active cursors spills saved calls -> In region active -> cm_region_live region=true ->
 cm_region_runtime_safe policy p calls (CMSpillFrame fid fp spills::saved) all region.
Proof.
 revert fid fp active spills saved calls; induction cursors as [|c rest IH]; intros fid fp active spills saved calls H IN LIVE; [contradiction|].
 pose proof (cm_runtime_stack_region_bounds _ _ _ _ _ _ _ _ _ _ _ _ H IN LIVE) as [LO [HI [LOW [UP WHICH]]]].
 right; split; [exact LO|]; split; [exact HI|]; split; [lia|]; split; [exact UP|].
 unfold cm_machine_range_safe; split; [right; lia|].
 cbn [cm_runtime_stack] in H; destruct (cm_phase_is_call (cm_cursor_phase c)).
 - destruct H as [PREFIX [SEG [SPILLS [S [C [BASE [SAVED [SFID [SFP REC]]]]]]]]].
   destruct saved as [|sf ss]; [contradiction|]; destruct calls as [|cf cs]; [contradiction|]; cbn in BASE,SAVED,SFID,SFP,REC.
   pose proof (cm_frame_segment_bounds _ _ _ _ _ SEG) as [SLOW [SFPLOW [BEFORE LIMIT]]].
   pose proof (cm_region_prefix_member _ _ _ _ _ _ _ _ PREFIX IN) as [OLD|NEW].
   + pose proof (cm_runtime_stack_region_bounds _ _ _ _ _ _ _ _ _ _ _ _ REC OLD LIVE) as [_ [_ [_ [_ PLACEMENT]]]].
     pose proof (IH _ _ _ _ _ _ REC OLD LIVE) as SAFE; unfold cm_region_runtime_safe in SAFE; destruct SAFE as [DEAD|[_ [_ [_ [_ [_ [CALLS FRAMES]]]]]]]; [congruence|].
     assert (FRAME_EQ:CMSpillFrame (cm_phase_caller (cm_cursor_phase c)) (cm_phase_oldfp (cm_cursor_phase c)) (cm_spill_frame_spills sf)=sf) by (rewrite <- SFID,<- SFP; destruct sf; reflexivity).
     rewrite FRAME_EQ in FRAMES; split.
     * split; [unfold cm_range_disjoint; destruct PLACEMENT; [left|right]; lia|exact CALLS].
     * split; [|exact FRAMES]; cbn [cm_spill_frame_fid cm_spill_frame_fp cm_spill_frame_spills]; destruct PLACEMENT as [STATIC|DYNAMIC].
       -- eapply cm_spill_list_lower_range; [eapply cm_spills_within_lower; [|exact SPILLS]; unfold cm_frame_segment in SEG; intuition lia|lia].
       -- eapply cm_spills_before_range_safe; [exact SPILLS|lia].
   + unfold cm_region_frame_safe in NEW; destruct NEW as [DEAD|[_ [_ [L U]]]]; [congruence|].
     pose proof (cm_runtime_stack_lower _ _ _ _ _ _ _ _ _ _ _ REC) as [CL [SL SFL]].
     assert (TEMP:fp+cm_temp_offset policy p fid 0<=cm_phase_oldfp (cm_cursor_phase c)) by (unfold cm_frame_segment in SEG; intuition).
     split; [split; [right; lia|eapply cm_call_frames_lower_range; [exact CL|lia]]|].
     split; [cbn [cm_spill_frame_fid cm_spill_frame_fp cm_spill_frame_spills]; eapply cm_spill_list_lower_range; [eapply cm_spills_within_temp_lower; exact SPILLS|lia]|].
     split; [cbn; rewrite SFID,SFP; eapply cm_spill_list_lower_range; [exact SL|lia]|eapply cm_spill_frames_lower_range; [exact SFL|lia]].
 - destruct (cm_phase_is_scope (cm_cursor_phase c)).
   + destruct H as [FID [PREFIX REC]].
     pose proof (cm_region_prefix_member _ _ _ _ _ _ _ _ PREFIX IN) as [OLD|NEW].
     * pose proof (IH _ _ _ _ _ _ REC OLD LIVE) as SAFE; unfold cm_region_runtime_safe in SAFE; destruct SAFE as [DEAD|[_ [_ [_ [_ [_ SAFE]]]]]]; [congruence|exact SAFE].
     * unfold cm_region_frame_safe in NEW; destruct NEW as [DEAD|[_ [_ [L U]]]]; [congruence|].
       eapply cm_runtime_stack_frame_range; [exact REC|exact FID|exact L|lia].
   + destruct (cm_phase_is_halt (cm_cursor_phase c)).
     * destruct H as [_ [_ [_ [_ [_ [_ [-> [-> [-> _]]]]]]]]]; repeat split; exact I.
     * pose proof (IH _ _ _ _ _ _ H IN LIVE) as SAFE; unfold cm_region_runtime_safe in SAFE; destruct SAFE as [DEAD|[_ [_ [_ [_ [_ SAFE]]]]]]; [congruence|exact SAFE].
Qed.
Theorem cm_runtime_stack_memory_layout policy ap p st fid cursors spills saved calls :
 cm_runtime_stack policy ap p (cm_state_regions st) fid (cm_state_fp st) (cm_state_regions st) cursors spills saved calls ->
 cm_runtime_memory_layout policy p st calls (CMSpillFrame fid (cm_state_fp st) spills::saved).
Proof.
 intros H region IN; destruct (cm_region_live region) eqn:LIVE.
 - eapply cm_runtime_stack_region_safe; eauto.
 - now left.
Qed.
