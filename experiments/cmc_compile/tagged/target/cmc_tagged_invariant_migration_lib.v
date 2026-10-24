Require Export SimpleC.EE.QCP_demos_human.cmc_tagged_step_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_task_tagged_step_support sp ap p task ann :
 cm_typed_program (cm_source_function_policy sp) p -> cm_annotation_erases task ann ->
 cm_task_runtime_invariant (cm_source_function_policy sp) ap p task ann -> cm_task_tagged_valid task -> cm_task_tagged_valid (cm_step sp task).
Proof.
 intros WF E R TAG; destruct task as [q input|q fid e st ks|q fid e st ks|q fid stmt st ks|q fid v st ks|q fid ctl st ks|st ctl status].
 - destruct R as [-> _]; pose proof (cm_initial_regions_before sp p input) as BEFORE; pose proof (cm_tagged_span_initial sp p input) as VALID.
   cbn [cm_step]; cm_tag_cases; cm_tag_finish.
 - destruct R as [-> [B R]]; now apply cm_r_tagged_step.
 - now apply cm_l_tagged_step.
 - destruct R as [_ [B R]]; now apply cm_s_tagged_step.
 - destruct R as [-> R]; cbn [cm_annotation_erases] in E; subst ks.
   cbn [cm_step]; destruct (cm_ann_cursors ann) as [|[phase owner ob oc] rest] eqn:CUR; [exact TAG|].
   cbn [cm_cursor_frames cm_cursor_phase]; eapply cm_v_tagged_step; try eassumption.
   unfold cm_runtime_core; rewrite CUR; exact R.
 - destruct R as [-> R]; cbn [cm_annotation_erases] in E; subst ks.
   cbn [cm_step]; destruct (cm_control_kind ctl=?4); [exact TAG|].
   destruct (cm_ann_cursors ann) as [|[phase owner ob oc] rest] eqn:CUR.
   + destruct (cm_control_kind ctl=?5); exact TAG.
   + cbn [cm_cursor_frames cm_cursor_phase]; eapply cm_c_tagged_step; try eassumption.
     unfold cm_runtime_core; rewrite CUR; exact R.
 - exact TAG.
Qed.
Definition cm_tagged_support_invariants sp ap p ast : Prop := cm_readiness_support_invariants sp ap p ast /\ cm_task_tagged_valid (cm_astate_task ast).
Lemma cm_tagged_support_initial sp ap p input : cm_task_succeeds sp (CMStartTask p input) ->
 cm_tagged_support_invariants sp ap p (cm_annotated_start (cm_source_function_policy sp) p input).
Proof. intro S; split; [now apply cm_readiness_support_initial|exact I]. Qed.
Lemma cm_tagged_support_step sp ap p ast : cm_semantic_wf_program (cm_source_function_policy sp) p ->
 cm_tagged_support_invariants sp ap p ast -> cm_tagged_support_invariants sp ap p (cm_annotated_step sp ap ast).
Proof.
 intros WF [READ TAG]; split; [now apply cm_readiness_support_step|].
 pose proof (proj1 READ) as RUN; pose proof (proj1 (proj1 (proj1 (proj1 RUN)))) as CTRL.
 destruct CTRL as [S [E REST]]. eapply cm_task_tagged_step_support; [exact (proj1 WF)|exact E|exact (proj2 RUN)|exact TAG].
Qed.
Lemma cm_tagged_support_iter sp ap p n ast : cm_semantic_wf_program (cm_source_function_policy sp) p ->
 cm_tagged_support_invariants sp ap p ast -> cm_tagged_support_invariants sp ap p (cm_annotated_iter sp ap n ast).
Proof. intro WF; revert ast; induction n; intros ast H; [exact H|apply IHn; now apply cm_tagged_support_step]. Qed.
Theorem cm_source_termination_tagged_invariants sp ap p input output status n :
 cm_semantic_wf_program (cm_source_function_policy sp) p -> cm_source_terminates sp p input output status ->
 cm_tagged_support_invariants sp ap p (cm_annotated_iter sp ap n (cm_annotated_start (cm_source_function_policy sp) p input)).
Proof.
 intros WF [INPUT [STATUS [st [ctl [RUN [SUCCESS OUTPUT]]]]]].
 apply cm_tagged_support_iter; [exact WF|]. apply cm_tagged_support_initial; exists st,ctl,status; auto.
Qed.
Theorem cm_source_termination_tagged_valid sp ap p input output status n :
 cm_semantic_wf_program (cm_source_function_policy sp) p -> cm_source_terminates sp p input output status ->
 cm_task_tagged_valid (cm_astate_task (cm_annotated_iter sp ap n (cm_annotated_start (cm_source_function_policy sp) p input))).
Proof. intros WF RUN; exact (proj2 (cm_source_termination_tagged_invariants sp ap p input output status n WF RUN)). Qed.
