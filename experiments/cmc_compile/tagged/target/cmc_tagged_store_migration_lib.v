Require Export SimpleC.EE.QCP_demos_human.cmc_layout_readiness_invariant_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Definition cm_task_tagged_valid task : Prop := match task with
 | CMStartTask _ _=>True
 | CMRTask _ _ _ st _ | CMLTask _ _ _ st _ | CMSTask _ _ _ st _ | CMVTask _ _ _ st _ | CMCTask _ _ _ st _ | CMDoneTask st _ _=>cm_tagged_span_valid st end.
Lemma cm_pointer_store_width ty : cm_is_pointerb ty=true -> cm_store_width ty=8.
Proof. destruct ty; cbn; intros; congruence. Qed.
Lemma cm_pointer_region_witness regions ptr : cm_pointer_region_ok regions ptr true=true ->
 exists r, In r regions /\ cm_region_gen r=cm_ptr_gen ptr /\ cm_region_live r=true /\ cm_region_writable r=true /\ cm_region_lo r<=cm_ptr_lo ptr /\ cm_ptr_hi ptr<=cm_region_hi r.
Proof.
 induction regions as [|r rest IH]; cbn [cm_pointer_region_ok]; [discriminate|].
 rewrite orb_true_iff; intros [H|H]; [|destruct (IH H) as [r0 [IN R]]; exists r0; split; [now right|exact R]].
 repeat rewrite andb_true_iff in H; cbn [negb orb] in H; destruct H as [[[[G L] LO] HI] W].
 apply Z.eqb_eq in G; apply Z.leb_le in LO,HI; exists r; repeat split; auto; now left.
Qed.
Lemma cm_runtime_store_live_span policy p st calls frames ty ptr :
 cm_runtime_memory_layout policy p st calls frames -> cm_store_ok ty ptr st=true -> cm_is_pointerb ty=true ->
 cm_live_span st (cm_value_number st ptr) 8.
Proof.
 intros RT STORE PTR; pose proof (cm_pointer_store_width ty PTR) as WIDTH.
 unfold cm_store_ok in STORE; repeat rewrite andb_true_iff in STORE; destruct STORE as [[[WRITE LO] HI] ADDR].
 unfold cm_pointer_writable in WRITE; apply andb_true_iff in WRITE; destruct WRITE as [LIVE REG].
 destruct (cm_pointer_region_witness _ _ REG) as [r [IN [GEN [RL [RW [RLO RHI]]]]]].
 specialize (RT r IN); destruct RT as [DEAD|[L0 [LH [BL [BH MACHINE]]]]]; [congruence|].
 apply Z.leb_le in LO,HI; rewrite WIDTH in HI.
 destruct ptr as [n|n| |gen lo hi off view]; cbn [cm_pointer_live cm_ptr_gen cm_ptr_lo cm_ptr_hi cm_ptr_offset] in LIVE,GEN,RLO,RHI,LO,HI; try discriminate.
 assert (BASE: cm_value_number st (CMPtrV gen lo hi off view)=cm_region_base (cm_state_regions st) gen+off).
 { cbn [cm_value_number]; apply tower_wrap64_fixed; unfold tower_signed64; rewrite GEN in BL,BH; lia. }
 unfold cm_live_span; rewrite BASE; intros addr RANGE; exists r; repeat split; try assumption; rewrite GEN; lia.
Qed.
Lemma cm_tagged_span_store policy p st calls frames ty ptr v :
 cm_runtime_memory_layout policy p st calls frames -> cm_store_ok ty ptr st=true -> cm_tagged_span_valid st -> cm_tagged_span_valid (cm_state_store ty ptr v st).
Proof.
 intros RT OK VALID a TAG LIVE; change (cm_live_address st a) in LIVE; change (cm_live_span st a 8).
 cbn [cm_state_store cm_state_tagged] in TAG; destruct (cm_is_pointerb ty) eqn:PTR.
 - apply orb_true_iff in TAG; destruct TAG as [NEW|OLD].
   + apply andb_true_iff in NEW; destruct NEW as [EQ NZ]; apply Z.eqb_eq in EQ; subst a; eapply cm_runtime_store_live_span; eassumption.
   + unfold cm_clear_tagged in OLD; apply andb_true_iff in OLD; apply (VALID a (proj1 OLD) LIVE).
 - unfold cm_clear_tagged in TAG; apply andb_true_iff in TAG; apply (VALID a (proj1 TAG) LIVE).
Qed.
Lemma cm_tagged_span_initial sp p input : cm_tagged_span_valid (cm_initial_state sp p input).
Proof. intros a H; discriminate H. Qed.
Lemma cm_tagged_span_io st input output : cm_tagged_span_valid st -> cm_tagged_span_valid (cm_state_io st input output).
Proof. exact (fun H=>H). Qed.
Lemma cm_live_span_forward left right base width : (forall a,cm_live_address left a -> cm_live_address right a) -> cm_live_span left base width -> cm_live_span right base width.
Proof. intros F H a A; now apply F,H. Qed.
Lemma cm_tagged_span_clear_extension left right base width :
 (forall a,cm_state_tagged right a=cm_clear_tagged (cm_state_tagged left) base width a) ->
 (forall a,cm_live_address right a -> cm_live_address left a \/ base<=a<base+width) ->
 (forall a,cm_live_address left a -> cm_live_address right a) -> cm_tagged_span_valid left -> cm_tagged_span_valid right.
Proof.
 intros TAG CLASS FORWARD VALID a T L; rewrite TAG in T; destruct (CLASS a L) as [OLD|NEW].
 - eapply cm_live_span_forward; [exact FORWARD|]. apply VALID; [unfold cm_clear_tagged in T; now apply andb_true_iff in T|exact OLD].
 - assert (W:0<width) by lia; destruct (cm_clear_tagged_survives _ _ _ _ W T) as [_ OUT]; exfalso; lia.
Qed.
