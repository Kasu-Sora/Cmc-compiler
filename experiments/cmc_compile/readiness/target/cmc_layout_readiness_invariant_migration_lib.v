Require Export SimpleC.EE.QCP_demos_human.cmc_layout_readiness_control_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_task_layout_ready_support sp ap p task ann :
 cm_task_succeeds sp task -> cm_annotation_erases task ann -> cm_annotation_rooted ann ->
 cm_task_coordinate_ready (cm_source_function_policy sp) p task ann ->
 cm_task_context_ready task ann -> cm_task_statement_control task ann -> cm_task_layout_ready sp ap p task ann.
Proof.
 intros S E ROOT C X H; pose proof (cm_succeeds_step_total sp task S) as NEXT.
 destruct task as [q input|q fid expr st ks|q fid expr st ks|q fid stmt st ks|q fid v st ks|q fid ctl st ks|st ctl status].
 - destruct C as [-> ->]; split; [reflexivity|split; [reflexivity|now apply cm_start_succeeds_ready]].
 - destruct C as [-> C]; split; [reflexivity|now apply cm_r_succeeds_ready].
 - destruct C as [-> C]; split; [reflexivity|now apply cm_l_succeeds_ready with (ks:=ks)].
 - destruct C as [-> C]; split; [reflexivity|now apply cm_s_succeeds_ready with (st:=st) (ks:=ks)].
 - destruct C as [-> C]; split; [reflexivity|]. cbn [cm_annotation_erases] in E; subst ks.
   unfold cm_v_layout_ready; destruct (cm_ann_cursors ann) as [|[phase owner ob oc] rest] eqn:CUR; [now left|].
   right; split; [discriminate|]; cbn [hd cm_cursor_phase]; split.
   + unfold cm_v_temp_ready; rewrite CUR; cbn [hd cm_cursor_temp].
     unfold cm_annotation_child_ready in C; rewrite CUR in C; exact (proj1 C).
   + eapply cm_v_succeeds_phase_ready with (fid:=fid); [exact CUR|exact ROOT|exact NEXT].
 - destruct C as [-> C]; split; [reflexivity|].
   pose proof (cm_succeeds_control_not_error _ _ _ _ _ _ S) as NE; destruct C as [ERR|C]; [contradiction|].
   cbn [cm_annotation_erases] in E; subst ks; unfold cm_c_layout_ready.
   destruct (cm_ann_cursors ann) as [|[phase owner ob oc] rest] eqn:CUR.
   + left; split; [reflexivity|]. unfold cm_task_context_ready,cm_control_context_ready in X; rewrite CUR in X.
     destruct ctl; cbn [cm_control_kind cm_cursors_loop_ready cm_cursors_call_ready] in *; intuition discriminate.
   + right; split; [discriminate|]; cbn [hd cm_cursor_phase]; split.
     * eapply cm_c_phase_ready_support; try eassumption. rewrite CUR; exact S.
     * eapply cm_c_code_ready_coordinate; eassumption.
 - exact I.
Qed.
Definition cm_readiness_support_invariants sp ap p ast : Prop :=
 cm_runtime_support_invariants sp ap p ast /\
 cm_task_statement_control (cm_astate_task ast) (cm_astate_annotation ast).
Lemma cm_readiness_support_initial sp ap p input : cm_task_succeeds sp (CMStartTask p input) ->
 cm_readiness_support_invariants sp ap p (cm_annotated_start (cm_source_function_policy sp) p input).
Proof. intro S; split; [now apply cm_runtime_support_initial|exact I]. Qed.
Lemma cm_readiness_support_step sp ap p ast : cm_semantic_wf_program (cm_source_function_policy sp) p ->
 cm_readiness_support_invariants sp ap p ast -> cm_readiness_support_invariants sp ap p (cm_annotated_step sp ap ast).
Proof.
 intros WF [R H]; split; [now apply cm_runtime_support_step|].
 pose proof (proj1 (proj1 (proj1 (proj1 R)))) as CTRL.
 destruct CTRL as [S [E [ROOT [C [X O]]]]].
 eapply cm_task_statement_control_step; eassumption.
Qed.
Lemma cm_readiness_support_iter sp ap p n ast : cm_semantic_wf_program (cm_source_function_policy sp) p ->
 cm_readiness_support_invariants sp ap p ast -> cm_readiness_support_invariants sp ap p (cm_annotated_iter sp ap n ast).
Proof. intro WF; revert ast; induction n; intros ast H; [exact H|apply IHn; now apply cm_readiness_support_step]. Qed.
Lemma cm_readiness_support_layout_ready sp ap p ast : cm_readiness_support_invariants sp ap p ast ->
 cm_task_layout_ready sp ap p (cm_astate_task ast) (cm_astate_annotation ast).
Proof.
 intros [R H]; pose proof (proj1 (proj1 (proj1 (proj1 R)))) as CTRL.
 destruct CTRL as [S [E [ROOT [C [X O]]]]].
 apply cm_task_layout_ready_support; assumption.
Qed.
Theorem cm_source_termination_readiness_invariants sp ap p input output status n :
 cm_semantic_wf_program (cm_source_function_policy sp) p -> cm_source_terminates sp p input output status ->
 cm_readiness_support_invariants sp ap p (cm_annotated_iter sp ap n (cm_annotated_start (cm_source_function_policy sp) p input)).
Proof.
 intros WF [INPUT [STATUS [st [ctl [RUN [SUCCESS OUTPUT]]]]]].
 apply cm_readiness_support_iter; [exact WF|]. apply cm_readiness_support_initial.
 exists st,ctl,status; auto.
Qed.
Theorem cm_source_termination_layout_ready sp ap p input output status n :
 cm_semantic_wf_program (cm_source_function_policy sp) p -> cm_source_terminates sp p input output status ->
 cm_task_layout_ready sp ap p
 (cm_astate_task (cm_annotated_iter sp ap n (cm_annotated_start (cm_source_function_policy sp) p input)))
 (cm_astate_annotation (cm_annotated_iter sp ap n (cm_annotated_start (cm_source_function_policy sp) p input))).
Proof. intros WF RUN; apply cm_readiness_support_layout_ready; exact (cm_source_termination_readiness_invariants sp ap p input output status n WF RUN). Qed.
Lemma cm_task_layout_ready_initial sp ap p input : cm_task_succeeds sp (CMStartTask p input) ->
 cm_task_layout_ready sp ap p (CMStartTask p input) cm_initial_annotation.
Proof. intro S; split; [reflexivity|split; [reflexivity|now apply cm_start_succeeds_ready]]. Qed.
Lemma cm_task_layout_ready_step_support sp ap p ast : cm_semantic_wf_program (cm_source_function_policy sp) p ->
 cm_readiness_support_invariants sp ap p ast ->
 cm_task_layout_ready sp ap p (cm_astate_task (cm_annotated_step sp ap ast)) (cm_astate_annotation (cm_annotated_step sp ap ast)).
Proof. intros WF H; apply cm_readiness_support_layout_ready; now apply cm_readiness_support_step. Qed.
