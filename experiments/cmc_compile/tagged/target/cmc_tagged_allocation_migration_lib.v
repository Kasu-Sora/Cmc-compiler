Require Export SimpleC.EE.QCP_demos_human.cmc_tagged_store_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_activate_live_old sp p fid slot st a : cm_regions_before (cm_state_regions st) (cm_state_nextgen st) -> cm_live_address st a -> cm_live_address (cm_activate_local sp p fid slot st) a.
Proof.
 intros BEFORE [r [IN [LIVE [LO HI]]]]; exists r; split; [now right|]. split; [exact LIVE|].
 pose proof (cm_activate_local_bases sp p fid slot st (cm_region_gen r) (BEFORE r IN)) as BASE; rewrite BASE; auto.
Qed.
Lemma cm_activate_live_old_or_local sp p fid slot st a : cm_regions_before (cm_state_regions st) (cm_state_nextgen st) ->
 cm_live_address (cm_activate_local sp p fid slot st) a -> cm_live_address st a \/
 cm_local_base sp p fid slot (cm_state_fp st)<=a<cm_local_base sp p fid slot (cm_state_fp st)+cm_slot_size (cm_program_structs p) (cm_source_slot_at sp slot (cm_function_locals (cm_source_function_at sp fid p))).
Proof.
 intros BEFORE [r [IN [LIVE [LO HI]]]]; cbn [cm_activate_local cm_state_regions] in IN; destruct IN as [EQ|IN].
 - subst r; right; cbn [cm_activate_local cm_state_regions cm_region_base cm_region_gen cm_region_base_field cm_region_lo cm_region_hi] in LO,HI; rewrite Z.eqb_refl in LO,HI; lia.
 - left; exists r; split; [exact IN|]; split; [exact LIVE|].
   pose proof (cm_activate_local_bases sp p fid slot st (cm_region_gen r) (BEFORE r IN)) as BASE; rewrite BASE in LO,HI; auto.
Qed.
Lemma cm_tagged_span_activate_local sp p fid slot st : cm_regions_before (cm_state_regions st) (cm_state_nextgen st) -> cm_tagged_span_valid st -> cm_tagged_span_valid (cm_activate_local sp p fid slot st).
Proof.
 intros BEFORE VALID; eapply cm_tagged_span_clear_extension; [intro a; reflexivity| | |exact VALID].
 - intros a A; eapply cm_activate_live_old_or_local; eassumption.
 - intros a A; eapply cm_activate_live_old; eassumption.
Qed.
