Require Export SimpleC.EE.QCP_demos_human.cmc_target_push_migration_lib.
From Coq Require Import ZArith List Bool Lia.
From AUXLib Require Import ListLib.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_string_region_at_nat p ss start i : (i<length ss)%nat ->
 In (CMRegion (cm_string_generation p (start+Z.of_nat i)) (cm_string_address p (start+Z.of_nat i)) 0 (Zlength(cm_string_bytes(nth i ss (CMStringD [])))+1) false true) (cm_string_regions p ss start).
Proof.
 revert i start; induction ss as [|s rest IH]; intros [|i] start H; cbn [length]in H; try lia.
 - cbn [cm_string_regions nth Nat2Z.inj_0]; rewrite Z.add_0_r; now left.
 - cbn [cm_string_regions nth]; right; rewrite Nat2Z.inj_succ; replace(start+Z.succ(Z.of_nat i))with(start+1+Z.of_nat i)by lia; apply IH; lia.
Qed.
Lemma cm_string_static_base p sid : 0<=sid<Zlength(cm_program_strings p) -> cm_region_base (cm_static_regions p) (cm_string_generation p sid)=cm_string_address p sid.
Proof.
 intros B; pose proof(cm_string_region_at_nat p (cm_program_strings p) 0 (Z.to_nat sid) ltac:(rewrite Zlength_correct in B; lia))as IN.
 rewrite Z2Nat.id in IN by lia; rewrite Z.add_0_l in IN.
 pose proof(cm_static_region_base_member p _ ltac:(unfold cm_static_regions; apply in_or_app; right; exact IN))as BASE; exact BASE.
Qed.
Lemma cm_string_number sp p st sid : 0<=sid<Zlength(cm_program_strings p) ->
 cm_region_bases_below_equal (cm_state_regions st) (cm_static_regions p) (cm_first_dynamic_generation p) ->
 cm_value_number st (cm_string_pointer sp p sid)=tower_wrap64(cm_string_address p sid).
Proof.
 intros B BASE; cbn [cm_string_pointer cm_value_number]; rewrite BASE by(unfold cm_string_generation,cm_first_dynamic_generation; lia).
 rewrite cm_string_static_base by exact B; now rewrite Z.add_0_r.
Qed.
Lemma cm_target_string_step sp ap p fid sid ty st ks target ann :
 0<=sid<Zlength(cm_program_strings p) ->
 cm_region_bases_below_equal (cm_state_regions st) (cm_static_regions p) (cm_first_dynamic_generation p) ->
 cm_task_layout sp ap p (CMRTask p fid (CMStringE sid ty) st ks) ann ->
 cm_task_target_sim (cm_source_function_policy sp) p (CMRTask p fid (CMStringE sid ty) st ks) target ann ->
 cm_target_step_result sp ap p (CMRTask p fid (CMStringE sid ty) st ks) target ann.
Proof.
 intros B BASE [CODE SAVED] [_ SIM]; unfold cm_target_step_result; cbn [cm_step cm_rstart cm_annotation_step cm_update_r cm_update_annotation cm_update_steps cm_task_target_sim].
 split; [reflexivity|]. eapply cm_target_push_sim; [exact SIM|exact CODE|now apply cm_string_number].
Qed.
