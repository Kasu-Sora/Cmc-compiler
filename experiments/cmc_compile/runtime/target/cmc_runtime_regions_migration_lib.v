Require Export SimpleC.EE.QCP_demos_human.cmc_simulation_short_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
(* Original cmc_preservation_invariant.c predicate, with local task lifting. *)
Definition cm_regions_before regions limit : Prop := forall region, In region regions -> cm_region_gen region<limit.
Definition cm_task_regions_before task : Prop := match task with
 | CMStartTask _ _=>True
 | CMRTask _ _ _ st _ | CMLTask _ _ _ st _ | CMSTask _ _ _ st _ | CMVTask _ _ _ st _ | CMCTask _ _ _ st _ | CMDoneTask st _ _=>cm_regions_before (cm_state_regions st) (cm_state_nextgen st) end.
Lemma cm_regions_before_nil limit : cm_regions_before [] limit.
Proof. intros r H; contradiction. Qed.
Lemma cm_regions_before_cons r rest limit : cm_regions_before (r::rest) limit <-> cm_region_gen r<limit /\ cm_regions_before rest limit.
Proof. unfold cm_regions_before; cbn; split.
 - intro H; split; [apply H; now left|intros x IN; apply H; now right].
 - intros [R RS] x [E|IN]; [now subst x|now apply RS].
Qed.
Lemma cm_regions_before_app xs ys limit : cm_regions_before (xs++ys) limit <-> cm_regions_before xs limit /\ cm_regions_before ys limit.
Proof. unfold cm_regions_before; setoid_rewrite in_app_iff; firstorder. Qed.
Lemma cm_regions_before_mono regions lower upper : lower<=upper -> cm_regions_before regions lower -> cm_regions_before regions upper.
Proof. intros L H r I; specialize (H r I); lia. Qed.
Lemma cm_regions_before_incl old current limit : cm_region_generations_incl old current -> cm_regions_before current limit -> cm_regions_before old limit.
Proof.
 intros INC B r I; pose proof (INC (cm_region_gen r) (in_map cm_region_gen old r I)) as H.
 apply in_map_iff in H; destruct H as [r' [E IN]]; specialize (B r' IN); lia.
Qed.
Lemma cm_restore_regions_before current old limit : cm_regions_before current limit -> cm_regions_before old limit -> cm_regions_before (cm_restore_regions current old) limit.
Proof.
 induction current as [|r rs IH]; intros C O; [exact O|].
 apply cm_regions_before_cons in C; destruct C as [R RS]; cbn [cm_restore_regions].
 destruct (cm_regions_eqb (r::rs) old); [exact O|]. apply cm_regions_before_cons; split; [destruct r; exact R|now apply IH].
Qed.
Lemma cm_regions_for_slots_before structs slots first base : cm_regions_before (cm_regions_for_slots structs slots first base) (first+Zlength slots).
Proof.
 revert first base; induction slots; intros; [apply cm_regions_before_nil|].
 cbn [cm_regions_for_slots]; apply cm_regions_before_cons; split.
 - cbn [cm_region_gen]; rewrite Zlength_cons; pose proof (ListLib.General.Length.Zlength_nonneg slots); lia.
 - eapply cm_regions_before_mono; [|apply IHslots]. rewrite Zlength_cons; lia.
Qed.
Lemma cm_global_regions_before p gs index limit : cm_global_generation (index+Zlength gs)<=limit -> cm_regions_before (cm_global_regions p gs index) limit.
Proof.
 revert index; induction gs; intros index B; [apply cm_regions_before_nil|].
 cbn [cm_global_regions]; apply cm_regions_before_cons; split.
 - cbn [cm_region_gen]; unfold cm_global_generation in *; rewrite Zlength_cons in B; pose proof (ListLib.General.Length.Zlength_nonneg gs); lia.
 - apply IHgs; rewrite Zlength_cons in B; unfold cm_global_generation in *; lia.
Qed.
Lemma cm_string_regions_before p ss index limit : cm_string_generation p (index+Zlength ss)<=limit -> cm_regions_before (cm_string_regions p ss index) limit.
Proof.
 revert index; induction ss; intros index B; [apply cm_regions_before_nil|].
 cbn [cm_string_regions]; apply cm_regions_before_cons; split.
 - cbn [cm_region_gen]; unfold cm_string_generation in *; rewrite Zlength_cons in B; pose proof (ListLib.General.Length.Zlength_nonneg ss); lia.
 - apply IHss; rewrite Zlength_cons in B; unfold cm_string_generation in *; lia.
Qed.
Lemma cm_static_regions_before p : cm_regions_before (cm_static_regions p) (cm_first_dynamic_generation p).
Proof.
 unfold cm_static_regions; apply cm_regions_before_app; split.
 - apply cm_global_regions_before; unfold cm_global_generation,cm_first_dynamic_generation; pose proof (ListLib.General.Length.Zlength_nonneg (cm_program_strings p)); lia.
 - apply cm_string_regions_before; unfold cm_string_generation,cm_first_dynamic_generation; lia.
Qed.
Lemma cm_initial_regions_before sp p input : cm_regions_before (cm_state_regions (cm_initial_state sp p input)) (cm_state_nextgen (cm_initial_state sp p input)).
Proof. apply cm_static_regions_before. Qed.
Lemma cm_enter_call_regions_before sp p fid values st : cm_regions_before (cm_state_regions st) (cm_state_nextgen st) -> cm_regions_before (cm_state_regions (cm_enter_call sp p fid values st)) (cm_state_nextgen (cm_enter_call sp p fid values st)).
Proof.
 intro H; unfold cm_enter_call; rewrite cm_store_params_regions,cm_store_params_nextgen.
 cbv beta iota zeta delta [cm_call_base_state cm_state_regions cm_state_nextgen]; apply cm_regions_before_app; split; [apply cm_regions_for_slots_before|].
 eapply cm_regions_before_mono; [|exact H]; pose proof (ListLib.General.Length.Zlength_nonneg (cm_function_params (cm_source_function_at sp fid p))); unfold cm_source_function_at,cm_state_nextgen in *; lia.
Qed.
Lemma cm_activate_local_regions_before sp p fid slot st : cm_regions_before (cm_state_regions st) (cm_state_nextgen st) -> cm_regions_before (cm_state_regions (cm_activate_local sp p fid slot st)) (cm_state_nextgen (cm_activate_local sp p fid slot st)).
Proof. intro H; cbv beta iota zeta delta [cm_activate_local cm_state_regions cm_state_nextgen] in *; apply cm_regions_before_cons; split; [cbn [cm_region_gen]; lia|eapply cm_regions_before_mono; [|exact H]; lia]. Qed.
Lemma cm_restore_call_regions_before st env fp old : cm_region_generations_incl old (cm_state_regions st) -> cm_regions_before (cm_state_regions st) (cm_state_nextgen st) -> cm_regions_before (cm_state_regions (cm_restore_call st env fp old)) (cm_state_nextgen (cm_restore_call st env fp old)).
Proof. intros INC B; apply cm_restore_regions_before; [exact B|eapply cm_regions_before_incl; eauto]. Qed.
Ltac cm_before_reduce := repeat progress (cm_ann_reduce; cbn [cm_task_regions_before cm_task_saved_generations cm_frames_saved_generations cm_frame_saved_generations cm_control_kind] in *).
Ltac cm_before_cases := cm_before_reduce; repeat match goal with |- context[if ?b then _ else _]=>cm_ann_bool b; cm_before_reduce end.
Ltac cm_before_finish := repeat match goal with H:_ /\ _|-_=>destruct H end;
 repeat first [assumption|exact I|apply cm_enter_call_regions_before; assumption|apply cm_activate_local_regions_before; assumption|apply cm_restore_call_regions_before; assumption|match goal with |- _ /\ _=>split end].
Lemma cm_r_regions_before sp p fid expr st ks : cm_regions_before (cm_state_regions st) (cm_state_nextgen st) -> cm_task_regions_before (cm_rstart sp p fid expr st ks).
Proof.
 destruct expr; intro H; cm_before_cases; try cm_before_finish.
 all: match goal with |- context[match ?xs with []=>_ | _::_=>_ end]=>destruct xs; cm_before_cases; cm_before_finish end.
Qed.
Lemma cm_l_regions_before sp p fid expr st ks : cm_regions_before (cm_state_regions st) (cm_state_nextgen st) -> cm_task_regions_before (cm_lstart sp p fid expr st ks).
Proof. destruct expr; intro H; cm_before_cases; cm_before_finish. Qed.
Lemma cm_s_regions_before sp p fid stmt st ks : cm_regions_before (cm_state_regions st) (cm_state_nextgen st) -> cm_task_regions_before (cm_sstart sp p fid stmt st ks).
Proof. destruct stmt; intro H; cm_before_cases; cm_before_finish. Qed.
Lemma cm_v_regions_before sp p fid frame v st ks : cm_frames_saved_generations (cm_state_regions st) (frame::ks) -> cm_regions_before (cm_state_regions st) (cm_state_nextgen st) -> cm_task_regions_before (cm_vapply sp p fid frame v st ks).
Proof.
 destruct frame; intros S H; cm_before_cases; try cm_before_finish.
 all: match goal with |- context[match ?xs with []=>_ | _::_=>_ end]=>destruct xs; cm_before_cases; cm_before_finish end.
Qed.
Lemma cm_c_regions_before sp p fid frame ctl st ks : cm_frames_saved_generations (cm_state_regions st) (frame::ks) -> cm_regions_before (cm_state_regions st) (cm_state_nextgen st) -> cm_task_regions_before (cm_capply sp p fid frame ctl st ks).
Proof. destruct frame; intros S H; cm_before_cases; cm_before_finish. Qed.
Lemma cm_task_regions_before_step sp task : cm_task_saved_generations task -> cm_task_regions_before task -> cm_task_regions_before (cm_step sp task).
Proof.
 destruct task as [p input|p fid expr st ks|p fid expr st ks|p fid stmt st ks|p fid v st ks|p fid ctl st ks|st ctl status]; intros S H.
 - cbv beta iota zeta delta [cm_step cm_begin_call]; cm_before_cases; try apply cm_enter_call_regions_before; apply cm_initial_regions_before.
 - now apply cm_r_regions_before.
 - now apply cm_l_regions_before.
 - now apply cm_s_regions_before.
 - destruct ks; [exact H|now apply cm_v_regions_before].
 - cbv beta iota zeta delta [cm_step]; destruct (cm_control_kind ctl=?4); [exact H|]; destruct ks; [destruct (cm_control_kind ctl=?5); exact H|now apply cm_c_regions_before].
 - exact H.
Qed.
Lemma cm_start_iter_regions_before sp ap p input n : cm_task_regions_before (cm_astate_task (cm_annotated_iter sp ap n (cm_annotated_start (cm_source_function_policy sp) p input))).
Proof.
 assert (ALL:forall n ast,cm_task_saved_generations (cm_astate_task ast) -> cm_task_regions_before (cm_astate_task ast) -> cm_task_regions_before (cm_astate_task (cm_annotated_iter sp ap n ast))).
 { induction n0; intros ast S B; [exact B|apply IHn0; [now apply cm_task_saved_generations_step|now apply cm_task_regions_before_step]]. }
 apply ALL; exact I.
Qed.
