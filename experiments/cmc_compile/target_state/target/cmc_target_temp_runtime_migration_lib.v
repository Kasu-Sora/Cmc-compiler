Require Export SimpleC.EE.QCP_demos_human.cmc_target_short_left_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_runtime_stack_current_segment policy ap p all cursors fid fp active spills saved calls :
 cm_runtime_stack policy ap p all fid fp active cursors spills saved calls -> 0<=fid ->
 exists oldfp,cm_frame_segment policy p fid fp oldfp /\ calls<>[] /\ cm_call_sim_base(hd(cm_call_nil ap)calls)=fp /\
 cm_call_frames_lower oldfp(tl calls) /\ cm_spill_frames_lower policy p oldfp saved.
Proof.
 revert fid fp active spills saved calls;induction cursors as[|c rest IH];intros fid fp active spills saved calls H FID;[contradiction|].
 cbn[cm_runtime_stack]in H;destruct(cm_phase_is_call(cm_cursor_phase c)).
 - destruct H as[PRE[SEG[SP[S[C[BASE[SAVED[SFID[SFP REC]]]]]]]]].
   pose proof(cm_runtime_stack_lower _ _ _ _ _ _ _ _ _ _ _ REC)as[CL[SL SFL]].
   exists(cm_phase_oldfp(cm_cursor_phase c));split;[exact SEG|];split;[exact C|];split;[exact BASE|];split;[exact CL|].
   destruct saved as[|sf ss];[contradiction|];cbn in SFID,SFP,SL,SFL;split;[rewrite SFID,SFP;exact SL|exact SFL].
 - destruct(cm_phase_is_scope(cm_cursor_phase c));[destruct H as[_[_ H]];eapply IH;eauto|].
   destruct(cm_phase_is_halt(cm_cursor_phase c));[destruct H as[BAD _];lia|eapply IH;eauto].
Qed.
Lemma cm_runtime_temp_machine_safe policy ap p all cursors fid fp active spills saved calls slot :
 cm_runtime_stack policy ap p all fid fp active cursors spills saved calls -> 0<=fid ->
 0<=slot<cm_temp_slots(cm_function_at policy fid(cm_program_functions p)) ->
 tower_word_valid(fp+cm_temp_offset policy p fid slot) /\
 cm_range_disjoint(fp+cm_temp_offset policy p fid slot)8 8 8 /\
 cm_call_frames_range_safe(fp+cm_temp_offset policy p fid slot)8 calls /\
 cm_spill_frames_range_safe policy p(fp+cm_temp_offset policy p fid slot)8 saved.
Proof.
 intros RT FID SLOT;destruct(cm_runtime_stack_current_segment _ _ _ _ _ _ _ _ _ _ _ RT FID)as[oldfp[SEG[NONEMPTY[BASE[CL SL]]]]].
 assert(BOUNDS:fp+8<=fp+cm_temp_offset policy p fid slot /\ fp+cm_temp_offset policy p fid slot+8<=oldfp).
 { unfold cm_frame_segment,cm_frame_size,cm_temp_offset in *;intuition lia. }
 pose proof(cm_frame_segment_bounds _ _ _ _ _ SEG)as[STATIC[LOW[BEFORE LIMIT]]].
 split;[unfold tower_word_valid;lia|];split;[unfold cm_range_disjoint;right;lia|];split.
 - destruct calls as[|cf cs];[contradiction|];split;[unfold cm_range_disjoint;cbn[hd]in BASE;right;lia|eapply cm_call_frames_lower_range;[exact CL|lia]].
 - eapply cm_spill_frames_lower_range;[exact SL|lia].
Qed.
Lemma cm_runtime_temp_live_disjoint policy ap p st fid cursors spills saved calls slot a :
 cm_runtime_stack policy ap p(cm_state_regions st)fid(cm_state_fp st)(cm_state_regions st)cursors spills saved calls ->
 0<=fid -> 0<=slot<cm_temp_slots(cm_function_at policy fid(cm_program_functions p)) -> cm_live_address st a ->
 a<cm_state_fp st+cm_temp_offset policy p fid slot \/ cm_state_fp st+cm_temp_offset policy p fid slot+8<=a.
Proof.
 intros RT FID SLOT[r[IN[LIVE[LO HI]]]].
 pose proof(cm_runtime_stack_spill_put _ _ _ _ _ _ _ _ _ _ _ slot(CMIntV 0)FID SLOT RT)as PUT.
 pose proof(cm_runtime_stack_memory_layout _ _ _ _ _ _ _ _ _ PUT r IN)as SAFE.
 destruct SAFE as[DEAD|[_[_[_[_[_[_[SP _]]]]]]]];[congruence|].
 change(cm_spill_list_range_safe policy p fid(cm_state_fp st)(cm_region_base(cm_state_regions st)(cm_region_gen r)+cm_region_lo r)(cm_region_hi r-cm_region_lo r)(cm_spill_put slot(CMIntV 0)spills))in SP.
 destruct SP as[DISJ _];cbn[cm_spill_slot]in DISJ;unfold cm_range_disjoint in DISJ;lia.
Qed.
