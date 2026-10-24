Require Export SimpleC.EE.QCP_demos_human.cmc_target_index_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_range_disjoint_subrange base width inner size other n : base<=inner -> inner+size<=base+width ->
 cm_range_disjoint base width other n -> cm_range_disjoint inner size other n.
Proof. unfold cm_range_disjoint;intros;lia. Qed.
Lemma cm_call_range_subrange base width inner size calls : base<=inner -> inner+size<=base+width ->
 cm_call_frames_range_safe base width calls -> cm_call_frames_range_safe inner size calls.
Proof. intros LO HI;induction calls;cbn[cm_call_frames_range_safe];[auto|];intros[H T];split;[eapply cm_range_disjoint_subrange;eassumption|now apply IHcalls]. Qed.
Lemma cm_spill_range_subrange policy p fid fp base width inner size spills : base<=inner -> inner+size<=base+width ->
 cm_spill_list_range_safe policy p fid fp base width spills -> cm_spill_list_range_safe policy p fid fp inner size spills.
Proof. intros LO HI;induction spills;cbn[cm_spill_list_range_safe];[auto|];intros[H T];split;[eapply cm_range_disjoint_subrange;eassumption|now apply IHspills]. Qed.
Lemma cm_frames_range_subrange policy p base width inner size frames : base<=inner -> inner+size<=base+width ->
 cm_spill_frames_range_safe policy p base width frames -> cm_spill_frames_range_safe policy p inner size frames.
Proof. intros LO HI;induction frames;cbn[cm_spill_frames_range_safe];[auto|];intros[H T];split;[eapply cm_spill_range_subrange;eassumption|now apply IHframes]. Qed.
Lemma cm_machine_range_subrange policy p base width inner size calls frames : base<=inner -> inner+size<=base+width ->
 cm_machine_range_safe policy p base width calls frames -> cm_machine_range_safe policy p inner size calls frames.
Proof. intros LO HI[F[C S]];split;[eapply cm_range_disjoint_subrange;eassumption|];split;[eapply cm_call_range_subrange;eassumption|eapply cm_frames_range_subrange;eassumption]. Qed.
Lemma cm_runtime_store_machine_safe policy p st calls frames ty ptr :
 cm_runtime_memory_layout policy p st calls frames -> cm_store_ok ty ptr st=true ->
 cm_machine_range_safe policy p(cm_value_number st ptr)(cm_store_width ty)calls frames.
Proof.
 intros RT STORE;unfold cm_store_ok in STORE;repeat rewrite andb_true_iff in STORE;destruct STORE as[[[WRITE LO]HI]ADDR].
 unfold cm_pointer_writable in WRITE;apply andb_true_iff in WRITE;destruct WRITE as[LIVE REG].
 destruct(cm_pointer_region_witness _ _ REG)as[r[IN[GEN[RL[RW[RLO RHI]]]]]].
 specialize(RT r IN);destruct RT as[DEAD|[L0[LH[BL[BH MACHINE]]]]];[congruence|].
 apply Z.leb_le in LO,HI;pose proof(cm_store_width_positive ty)as WIDTH.
 destruct ptr as[n|n| |gen lo hi off view];cbn[cm_pointer_live cm_ptr_gen cm_ptr_lo cm_ptr_hi cm_ptr_offset]in LIVE,GEN,RLO,RHI,LO,HI;try discriminate.
 assert(BASE:cm_value_number st(CMPtrV gen lo hi off view)=cm_region_base(cm_state_regions st)gen+off).
 { cbn[cm_value_number];apply tower_wrap64_fixed;unfold tower_signed64;rewrite GEN in BL,BH;lia. }
 rewrite BASE;rewrite GEN in MACHINE;eapply cm_machine_range_subrange;[| |exact MACHINE];lia.
Qed.
