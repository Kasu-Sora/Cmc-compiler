Require Export SimpleC.EE.QCP_demos_human.cmc_tagged_restore_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
(* Local induction predicate: only the unfilled parameter suffix may contain
   stale tags. This is not a new assumption on source programs. *)
Definition cm_tagged_span_except st start finish : Prop := forall a,
 cm_state_tagged st a=true -> cm_live_address st a -> (a<start \/ finish<=a) -> cm_live_span st a 8.
Lemma cm_tagged_span_except_empty st edge : cm_tagged_span_except st edge edge -> cm_tagged_span_valid st.
Proof. intros H a T L; apply H; [exact T|exact L|lia]. Qed.
Lemma cm_tagged_span_except_full st start finish : cm_tagged_span_valid st -> cm_tagged_span_except st start finish.
Proof. intros H a T L OUT; now apply H. Qed.
Lemma cm_tagged_span_except_extension left right start finish :
 (forall a,cm_state_tagged right a=cm_state_tagged left a) ->
 (forall a,cm_live_address right a -> cm_live_address left a \/ start<=a<finish) ->
 (forall a,cm_live_address left a -> cm_live_address right a) ->
 cm_tagged_span_valid left -> cm_tagged_span_except right start finish.
Proof.
 intros TAG CLASS FORWARD VALID a T L OUT; rewrite TAG in T; destruct (CLASS a L) as [OLD|NEW]; [|exfalso; lia].
 eapply cm_live_span_forward; [exact FORWARD|now apply VALID].
Qed.
Lemma cm_tagged_span_except_store st ty ptr v finish :
 (cm_is_pointerb ty=true -> cm_live_span st (cm_value_number st ptr) 8) ->
 cm_tagged_span_except st (cm_value_number st ptr) finish ->
 cm_tagged_span_except (cm_state_store ty ptr v st) (cm_value_number st ptr+cm_store_width ty) finish.
Proof.
 intros NEWSPAN VALID a TAG LIVE OUT; change (cm_live_address st a) in LIVE; change (cm_live_span st a 8).
 cbn [cm_state_store cm_state_tagged] in TAG; destruct (cm_is_pointerb ty) eqn:PTR.
 - apply orb_true_iff in TAG; destruct TAG as [NEW|OLD].
   + apply andb_true_iff in NEW; destruct NEW as [EQ _]; apply Z.eqb_eq in EQ; subst a; now apply NEWSPAN.
   + rewrite <-(cm_pointer_store_width ty PTR) in OLD.
     destruct (cm_clear_tagged_survives _ _ _ _ (cm_store_width_positive ty) OLD) as [T D].
     apply VALID; [exact T|exact LIVE|pose proof (cm_store_width_positive ty); lia].
 - destruct (cm_clear_tagged_survives _ _ _ _ (cm_store_width_positive ty) TAG) as [T D].
   apply VALID; [exact T|exact LIVE|pose proof (cm_store_width_positive ty); lia].
Qed.
Lemma cm_call_base_live_old sp p fid st a : cm_regions_before (cm_state_regions st) (cm_state_nextgen st) ->
 cm_live_address st a -> cm_live_address (cm_call_base_state sp p fid st) a.
Proof.
 intros BEFORE [r [IN [LIVE [LO HI]]]]; exists r; split.
 - apply in_or_app; now right.
 - split; [exact LIVE|].
   assert (BASE:cm_region_bases_below_equal (cm_state_regions (cm_call_base_state sp p fid st)) (cm_state_regions st) (cm_state_nextgen st)) by (apply cm_regions_for_slots_bases; lia).
   rewrite (BASE _ (BEFORE r IN)); auto.
Qed.
Lemma cm_call_base_live_old_or_param sp p fid st a :
 cm_function_wf (cm_source_function_policy sp) p (cm_source_function_at sp fid p) ->
 cm_regions_before (cm_state_regions st) (cm_state_nextgen st) ->
 cm_live_address (cm_call_base_state sp p fid st) a -> cm_live_address st a \/
 (cm_state_fp st-cm_frame_size (cm_program_structs p) (cm_source_function_at sp fid p)+8<=a /\
 a<cm_state_fp st-cm_frame_size (cm_program_structs p) (cm_source_function_at sp fid p)+8+cm_slots_size (cm_program_structs p) (cm_function_params (cm_source_function_at sp fid p))).
Proof.
 intros WF BEFORE [r [IN [LIVE [LO HI]]]]; destruct WF as [_ [[SLOTS _] _]].
 change (In r (cm_regions_for_slots (cm_program_structs p) (cm_function_params (cm_source_function_at sp fid p)) (cm_state_nextgen st) (cm_state_fp st-cm_frame_size (cm_program_structs p) (cm_source_function_at sp fid p)+8)++cm_state_regions st)) in IN.
 apply in_app_or in IN; destruct IN as [FRESH|OLD].
 - right; pose proof (cm_regions_for_slots_geometry _ _ _ _ _ (cm_slots_wf_nonnegative_members _ _ SLOTS) FRESH) as GEO.
   assert (BASE:cm_region_base (cm_state_regions (cm_call_base_state sp p fid st)) (cm_region_gen r)=cm_region_base_field r) by (apply cm_region_base_prefix_unique; [apply cm_regions_for_slots_unique|exact FRESH]).
   rewrite BASE in LO,HI; destruct GEO as [ZERO [POS [LOW HIGH]]]; lia.
 - left; exists r; split; [exact OLD|]. split; [exact LIVE|].
   assert (BASE:cm_region_bases_below_equal (cm_state_regions (cm_call_base_state sp p fid st)) (cm_state_regions st) (cm_state_nextgen st)) by (apply cm_regions_for_slots_bases; lia).
   rewrite (BASE _ (BEFORE r OLD)) in LO,HI; auto.
Qed.
Lemma cm_tagged_span_call_base_except sp p fid st :
 cm_function_wf (cm_source_function_policy sp) p (cm_source_function_at sp fid p) ->
 cm_regions_before (cm_state_regions st) (cm_state_nextgen st) -> cm_tagged_span_valid st ->
 cm_tagged_span_except (cm_call_base_state sp p fid st)
 (cm_state_fp st-cm_frame_size (cm_program_structs p) (cm_source_function_at sp fid p)+8)
 (cm_state_fp st-cm_frame_size (cm_program_structs p) (cm_source_function_at sp fid p)+8+cm_slots_size (cm_program_structs p) (cm_function_params (cm_source_function_at sp fid p))).
Proof.
 intros WF BEFORE VALID; eapply cm_tagged_span_except_extension with (left:=st); [intro a; reflexivity| | |exact VALID].
 - intros a A; eapply cm_call_base_live_old_or_param; eassumption.
 - intros a A; eapply cm_call_base_live_old; eassumption.
Qed.
