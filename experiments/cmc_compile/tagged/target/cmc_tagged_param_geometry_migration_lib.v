Require Export SimpleC.EE.QCP_demos_human.cmc_tagged_param_iteration_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_regions_for_slots_member_nat structs slots gen base i : (i<length slots)%nat ->
 In (CMRegion (gen+Z.of_nat i) (base+cm_slots_prefix structs slots (Z.of_nat i)) 0 (cm_slot_size structs (nth i slots cm_default_slot)) true true) (cm_regions_for_slots structs slots gen base).
Proof.
 revert gen base i; induction slots as [|s slots IH]; intros gen base i B; [cbn in B; lia|]. destruct i as [|i].
 - cbn [cm_regions_for_slots cm_slots_prefix nth Z.of_nat Z.eqb]; rewrite !Z.add_0_r; now left.
 - cbn [cm_regions_for_slots nth]; right.
   assert (NZ:(Z.of_nat (S i)=?0)=false) by (apply Z.eqb_neq; lia).
   cbn [cm_slots_prefix]; rewrite NZ; replace (Z.of_nat (S i)-1) with (Z.of_nat i) by lia.
   replace (gen+Z.of_nat (S i)) with ((gen+1)+Z.of_nat i) by lia.
   replace (base+(cm_slot_size structs s+cm_slots_prefix structs slots (Z.of_nat i))) with ((base+cm_slot_size structs s)+cm_slots_prefix structs slots (Z.of_nat i)) by lia.
   apply IH; cbn in B; lia.
Qed.
Lemma cm_regions_for_slots_member structs slots gen base i : 0<=i<Zlength slots ->
 In (CMRegion (gen+i) (base+cm_slots_prefix structs slots i) 0 (cm_slot_size structs (cm_slot_at i slots)) true true) (cm_regions_for_slots structs slots gen base).
Proof.
 intro B; pose proof (cm_regions_for_slots_member_nat structs slots gen base (Z.to_nat i) ltac:(rewrite Zlength_correct in B; lia)) as H.
 rewrite Z2Nat.id in H by lia; exact H.
Qed.
Lemma cm_param_slot_store_width structs slots i : cm_params_wf structs slots -> 0<=i<Zlength slots ->
 cm_slot_size structs (cm_slot_at i slots)=cm_store_width (cm_slot_ty (cm_slot_at i slots)).
Proof.
 intros [WF COUNT] B; specialize (WF i B); specialize (COUNT i B).
 unfold cm_slot_size; rewrite COUNT; cbn [Z.eqb]; destruct WF as [_ [[_ [_ NS]] _]].
 destruct (cm_slot_ty (cm_slot_at i slots)); cbn [cm_type_size cm_store_width]; try reflexivity; exfalso; apply NS; exact I.
Qed.
Lemma cm_call_param_geometry sp p fid st j :
 cm_function_wf (cm_source_function_policy sp) p (cm_source_function_at sp fid p) ->
 cm_frame_segment (cm_source_function_policy sp) p fid (cm_state_fp st-cm_frame_size (cm_program_structs p) (cm_source_function_at sp fid p)) (cm_state_fp st) ->
 0<=j<Zlength (cm_function_params (cm_source_function_at sp fid p)) ->
 cm_value_number (cm_call_base_state sp p fid st) (cm_state_env (cm_call_base_state sp p fid st) 2 j)=cm_param_base sp p fid j (cm_state_fp st-cm_frame_size (cm_program_structs p) (cm_source_function_at sp fid p)) /\
 cm_param_base sp p fid j (cm_state_fp st-cm_frame_size (cm_program_structs p) (cm_source_function_at sp fid p))+cm_store_width (cm_slot_ty (cm_source_slot_at sp j (cm_function_params (cm_source_function_at sp fid p))))=cm_param_base sp p fid (j+1) (cm_state_fp st-cm_frame_size (cm_program_structs p) (cm_source_function_at sp fid p)) /\
 (cm_is_pointerb (cm_slot_ty (cm_source_slot_at sp j (cm_function_params (cm_source_function_at sp fid p))))=true -> cm_live_span (cm_call_base_state sp p fid st) (cm_param_base sp p fid j (cm_state_fp st-cm_frame_size (cm_program_structs p) (cm_source_function_at sp fid p))) 8).
Proof.
 intros FW SEG J; pose proof FW as [_ [PW [LW [_ [_ [_ [TEMP FS]]]]]]].
 pose proof (cm_slots_prefix_cell_bounds _ _ _ (proj1 PW) J) as BOUNDS.
 pose proof (cm_param_slot_store_width _ _ _ PW J) as WIDTH.
 pose proof (cm_regions_for_slots_member (cm_program_structs p) (cm_function_params (cm_source_function_at sp fid p)) (cm_state_nextgen st) (cm_state_fp st-cm_frame_size (cm_program_structs p) (cm_source_function_at sp fid p)+8) j J) as MEMBER.
 pose proof (cm_region_base_prefix_unique _ (cm_state_regions st) _ (cm_regions_for_slots_unique _ _ _ _) MEMBER) as BASE.
 cbn [cm_region_gen cm_region_base_field] in BASE.
 pose proof (cm_slots_size_nonnegative__call_bounds _ _ LW) as LN.
 assert (ADDR:16<=cm_param_base sp p fid j (cm_state_fp st-cm_frame_size (cm_program_structs p) (cm_source_function_at sp fid p))<=1048576).
 { unfold cm_param_base; unfold cm_frame_segment,cm_temp_offset,cm_source_function_at in SEG; unfold cm_source_function_at in *; pose proof (cm_store_width_positive (cm_slot_ty (cm_slot_at j (cm_function_params (cm_source_function_at sp fid p))))) as POS; unfold cm_source_function_at in POS; intuition lia. }
 split.
 - cbn [cm_call_base_state cm_state_env cm_call_env Z.eqb Pos.eqb cm_value_number cm_state_regions]; rewrite BASE,Z.add_0_r; apply tower_wrap64_fixed; unfold tower_signed64,cm_param_base in *; lia.
 - rewrite (cm_source_slot_at_valid sp _ j J); split.
   + unfold cm_param_base; rewrite cm_slots_prefix_successor by exact J; lia.
   + intro PTR; unfold cm_live_span; intros a RANGE.
     exists (CMRegion (cm_state_nextgen st+j) (cm_param_base sp p fid j (cm_state_fp st-cm_frame_size (cm_program_structs p) (cm_source_function_at sp fid p))) 0 (cm_slot_size (cm_program_structs p) (cm_slot_at j (cm_function_params (cm_source_function_at sp fid p)))) true true).
     split; [apply in_or_app; now left|]. split; [reflexivity|].
     cbn [cm_region_gen cm_region_lo cm_region_hi cm_call_base_state cm_state_regions]; rewrite BASE.
     rewrite WIDTH,(cm_pointer_store_width _ PTR); unfold cm_param_base in RANGE; lia.
Qed.
