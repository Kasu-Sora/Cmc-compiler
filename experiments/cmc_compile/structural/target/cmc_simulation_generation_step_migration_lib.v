Require Export SimpleC.EE.QCP_demos_human.cmc_simulation_generation_state_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_begin_call_generation sp p caller fid values st ret ks :
 cm_state_generation_below (cm_source_function_policy sp) p caller st ->
 cm_frames_generation_below (cm_source_function_policy sp) p caller (cm_state_nextgen st) ks ->
 cm_values_generation_below (cm_state_nextgen st) values ->
 cm_task_generation_below (cm_source_function_policy sp) p (cm_begin_call sp p caller fid values st ret ks).
Proof.
 intros ST KS VS; unfold cm_begin_call; destruct (_ && _); cbn [cm_task_generation_below]; split; [reflexivity| |reflexivity|].
 - split; [eapply cm_enter_call_generation; eauto|]. cbn [cm_frames_generation_below cm_frame_generation_below cm_frame_parent_fid]. rewrite cm_enter_call_nextgen.
   pose proof (ListLib.General.Length.Zlength_nonneg (cm_function_params (cm_source_function_at sp fid p))) as LEN; split.
   + eapply cm_env_generation_below_mono; [|exact (proj1 (proj2 ST))]; lia.
   + eapply cm_frames_generation_below_mono; [|exact KS]; lia.
 - split; [exact ST|]; split; [exact I|exact KS].
Qed.
Lemma cm_binding_value_generation sp p fid scope slot st : cm_state_generation_below (cm_source_function_policy sp) p fid st ->
 cm_binding_valid p (cm_source_function_at sp fid p) scope slot ->
 cm_value_generation_below (cm_state_nextgen st) (if scope=?0 then cm_global_pointer sp p slot else cm_state_env st scope slot).
Proof.
 intros [B [E T]] V; destruct (scope=?0) eqn:H; [apply Z.eqb_eq in H; subst|eapply cm_env_binding_generation; eauto].
 eapply cm_value_generation_below_mono; [exact B|apply cm_global_pointer_generation_below]. unfold cm_binding_valid in V; intuition congruence.
Qed.
Ltac cm_gen_reduce := cbv beta iota zeta delta [cm_rstart cm_lstart cm_sstart cm_vapply cm_capply cm_args_start
 cm_task_generation_below cm_frames_generation_below cm_frame_generation_below cm_frame_parent_fid cm_control_generation_below
 cm_values_generation_below cm_control_kind cm_control_value andb orb negb] in *.
Ltac cm_gen_cases := cm_gen_reduce;
 repeat match goal with |- context[if ?b then _ else _]=>cm_ann_bool b; cm_gen_reduce end.
Ltac cm_gen_atom := match goal with
 | |- cm_value_generation_below _ (cm_convert_value _ _ _) =>apply cm_convert_value_generation
 | |- cm_value_generation_below _ (cm_load_value _ _ _) =>apply cm_load_value_generation
 | |- cm_value_generation_below _ (cm_unary_value _ _ _) =>apply cm_unary_value_generation
 | |- cm_value_generation_below _ (cm_binary_value _ _ _ _ _ _) =>apply cm_binary_value_generation
 | |- cm_value_generation_below _ (cm_ptr_add _ _ _) =>apply cm_ptr_add_generation
 | |- cm_value_generation_below _ (cm_ptr_member _ _ _ _) =>apply cm_ptr_member_generation
 | |- cm_state_generation_below _ _ _ (cm_state_io _ _ _) =>apply cm_state_io_generation
 | |- cm_state_generation_below _ _ _ (cm_state_store _ _ _ _) =>apply cm_state_store_generation
 | |- cm_state_generation_below _ _ _ (cm_activate_local _ _ _ _ _) =>apply cm_activate_local_generation
 | |- 0<=cm_state_nextgen _ =>eapply cm_state_generation_limit_positive; eassumption
 end.
Ltac cm_gen_finish := repeat match goal with H:_ /\ _ |- _=>destruct H end;
 repeat first [assumption | reflexivity | exact I | cm_gen_atom | match goal with |- _ /\ _=>split end].
Lemma cm_r_generation_step sp p fid expr st ks : cm_expr_static_valid p (cm_source_function_at sp fid p) expr ->
 cm_state_generation_below (cm_source_function_policy sp) p fid st ->
 cm_frames_generation_below (cm_source_function_policy sp) p fid (cm_state_nextgen st) ks ->
 cm_task_generation_below (cm_source_function_policy sp) p (cm_rstart sp p fid expr st ks).
Proof.
 destruct expr; intros V ST KS; try match type of V with cm_expr_static_valid _ _ (CMCallE _ _ _) =>rewrite cm_expr_static_call in V end;
 cbn [cm_expr_static_valid] in V; cm_gen_cases; try cm_gen_finish.
 all: try solve [apply cm_begin_call_generation; auto; exact I].
 all: try solve [eapply cm_value_generation_below_mono; [exact (proj1 ST)|now apply cm_string_pointer_generation_below]].
 all: try solve [pose proof (cm_binding_value_generation sp p fid scope slot st ST V) as H; rewrite Heqb1 in H; exact H].
 all: try match goal with |- context[match ?xs with []=>_ | _::_=>_ end]=>destruct xs; cm_gen_cases; try cm_gen_finish end.
 all: apply cm_begin_call_generation; auto; exact I.
Qed.
Lemma cm_l_generation_step sp p fid expr st ks : cm_expr_static_valid p (cm_source_function_at sp fid p) expr ->
 cm_state_generation_below (cm_source_function_policy sp) p fid st ->
 cm_frames_generation_below (cm_source_function_policy sp) p fid (cm_state_nextgen st) ks ->
 cm_task_generation_below (cm_source_function_policy sp) p (cm_lstart sp p fid expr st ks).
Proof.
 destruct expr; intros V ST KS; cbn [cm_expr_static_valid] in V; cm_gen_cases; try cm_gen_finish.
 all: pose proof (cm_binding_value_generation sp p fid scope slot st ST V) as H; rewrite Heqb0 in H; exact H.
Qed.
Lemma cm_s_generation_step sp p fid stmt st ks :
 cm_state_generation_below (cm_source_function_policy sp) p fid st ->
 cm_frames_generation_below (cm_source_function_policy sp) p fid (cm_state_nextgen st) ks ->
 cm_task_generation_below (cm_source_function_policy sp) p (cm_sstart sp p fid stmt st ks).
Proof.
 destruct stmt; intros ST KS; cm_gen_cases; try cm_gen_finish.
 all: try solve [exact (proj1 (proj2 ST))].
 all: eapply cm_frames_generation_below_mono; [|exact KS]; change (cm_state_nextgen st<=cm_state_nextgen st+1); lia.
Qed.
Lemma cm_v_generation_step sp p fid frame v st ks : cm_task_succeeds sp (cm_vapply sp p fid frame v st ks) ->
 cm_state_generation_below (cm_source_function_policy sp) p fid st ->
 cm_value_generation_below (cm_state_nextgen st) v ->
 cm_frames_generation_below (cm_source_function_policy sp) p fid (cm_state_nextgen st) (frame::ks) ->
 cm_task_generation_below (cm_source_function_policy sp) p (cm_vapply sp p fid frame v st ks).
Proof.
 destruct frame; intros S ST V KS; pose proof (proj1 ST) as LOW; pose proof (proj1 (proj2 ST)) as ENV; pose proof (proj2 (proj2 ST)) as TAGS.
 all: cm_gen_cases.
 all: try cm_gen_finish.
 all: try solve [unfold cm_restore_scope; eapply cm_restore_call_generation; eauto].
 all: try match goal with |- context[match ?xs with []=>_ | _::_=>_ end]=>destruct xs; cm_gen_cases; try cm_gen_finish end.
 all: try solve [apply cm_begin_call_generation; auto; apply cm_values_generation_below_reverse; cbn; auto].
 all: try solve [exfalso; eapply cm_error_not_succeeds; exact S].

Qed.
Lemma cm_c_generation_step sp p fid frame ctl st ks :
 cm_state_generation_below (cm_source_function_policy sp) p fid st -> cm_control_generation_below (cm_state_nextgen st) ctl ->
 cm_frames_generation_below (cm_source_function_policy sp) p fid (cm_state_nextgen st) (frame::ks) ->
 cm_task_generation_below (cm_source_function_policy sp) p (cm_capply sp p fid frame ctl st ks).
Proof.
 destruct ctl; destruct frame; intros ST V KS; pose proof (proj1 ST) as LOW; pose proof (proj1 (proj2 ST)) as ENV; pose proof (proj2 (proj2 ST)) as TAGS;
 cm_gen_cases; try cm_gen_finish.
 all: unfold cm_restore_scope; eapply cm_restore_call_generation; eauto.
Qed.
Lemma cm_task_generation_step_coordinate sp p task ann : cm_task_succeeds sp task ->
 cm_task_static_valid (cm_source_function_policy sp) task ->
 cm_task_generation_below (cm_source_function_policy sp) p task ->
 cm_task_coordinate_ready (cm_source_function_policy sp) p task ann ->
 cm_task_generation_below (cm_source_function_policy sp) p (cm_step sp task).
Proof.
 destruct task as [q input|q fid expr st ks|q fid expr st ks|q fid stmt st ks|q fid v st ks|q fid ctl st ks|st ctl status]; intros S STATIC G C.
 - destruct C as [-> C]; apply cm_begin_call_generation; [apply cm_state_generation_initial|repeat split; reflexivity|exact I].
 - destruct G as [-> [ST KS]]; destruct STATIC as [V _]; now apply cm_r_generation_step.
 - destruct G as [-> [ST KS]]; destruct STATIC as [V _]; now apply cm_l_generation_step.
 - destruct G as [-> [ST KS]]; now apply cm_s_generation_step.
 - destruct G as [-> [ST [V KS]]]; destruct ks as [|frame ks]; [cbn; split; [exact (proj1 ST)|split; [exact (proj2 (proj2 ST))|exact I]]|].
   apply cm_v_generation_step; auto; now apply cm_succeeds_step_total in S.
 - destruct G as [-> [ST [V KS]]]; pose proof (proj1 ST); pose proof (proj2 (proj2 ST)); cbv beta iota zeta delta [cm_step]; destruct (cm_control_kind ctl=?4); [cbn; intuition|].
   destruct ks as [|frame ks]; [destruct (cm_control_kind ctl=?5); cbn; intuition|now apply cm_c_generation_step].
 - exact G.
Qed.
Lemma cm_annotated_iter_generation_coordinate sp ap p n ast : cm_typed_program (cm_source_function_policy sp) p ->
 cm_task_succeeds sp (cm_astate_task ast) ->
 cm_annotation_erases (cm_astate_task ast) (cm_astate_annotation ast) /\ cm_annotation_rooted (cm_astate_annotation ast) ->
 cm_task_coordinate_ready (cm_source_function_policy sp) p (cm_astate_task ast) (cm_astate_annotation ast) ->
 cm_task_static_valid (cm_source_function_policy sp) (cm_astate_task ast) ->
 cm_task_generation_below (cm_source_function_policy sp) p (cm_astate_task ast) ->
 cm_task_generation_below (cm_source_function_policy sp) p (cm_astate_task (cm_annotated_iter sp ap n ast)).
Proof.
 intros WF; revert ast; induction n; intros ast S E C V G; [exact G|]. apply IHn.
 - now apply cm_succeeds_step_total.
 - now apply cm_annotated_step_invariant.
 - apply cm_task_coordinate_step; [exact (proj1 E)|exact C].
 - eapply cm_task_static_step_coordinate; eauto.
 - eapply cm_task_generation_step_coordinate; eauto.
Qed.
Theorem cm_source_termination_generation_below sp ap p input output status n :
 cm_semantic_wf_program (cm_source_function_policy sp) p -> cm_source_terminates sp p input output status ->
 cm_task_generation_below (cm_source_function_policy sp) p (cm_astate_task (cm_annotated_iter sp ap n (cm_annotated_start (cm_source_function_policy sp) p input))).
Proof.
 intros [WF _] TERM; eapply cm_annotated_iter_generation_coordinate; [exact WF| | |apply cm_task_coordinate_initial|exact I|reflexivity].
 - unfold cm_source_terminates in TERM; destruct TERM as [_ [_ [st [ctl [E [S OUT]]]]]]. exists st,ctl,status; now split.
 - split; [apply cm_annotated_start_erases|apply cm_annotated_start_rooted].
Qed.
