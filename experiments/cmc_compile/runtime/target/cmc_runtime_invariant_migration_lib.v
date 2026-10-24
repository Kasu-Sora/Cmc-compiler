Require Export SimpleC.EE.QCP_demos_human.cmc_runtime_apply_step_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_task_runtime_step_support sp ap p task ann :
 cm_typed_program (cm_source_function_policy sp) p ->
 cm_task_succeeds sp task -> cm_annotation_erases task ann ->
 cm_task_coordinate_ready (cm_source_function_policy sp) p task ann ->
 cm_task_fid_ready p task -> cm_task_active_fid_ready p task ->
 cm_task_budget (cm_source_function_policy sp) p task ann ->
 cm_task_runtime_invariant (cm_source_function_policy sp) ap p task ann ->
 cm_task_runtime_invariant (cm_source_function_policy sp) ap p (cm_step sp task) (cm_update_annotation (cm_annotation_step sp ap task ann)).
Proof.
 intros WF S E C F A B R; pose proof (cm_succeeds_step_total sp task S) as NEXT.
 destruct task as [q input|q fid e st ks|q fid e st ks|q fid stmt st ks|q fid v st ks|q fid ctl st ks|st ctl status].
 - destruct R as [-> ->]; now apply cm_runtime_start_step.
 - destruct R as [-> R]; cbn [cm_annotation_erases] in E; rewrite <-E; now apply cm_r_runtime_step.
 - destruct R as [-> R]; cbn [cm_annotation_erases] in E; rewrite <-E; now apply cm_l_runtime_step.
 - destruct R as [-> R]; cbn [cm_annotation_erases] in E; rewrite <-E; now apply cm_s_runtime_step.
 - destruct R as [-> R]; destruct C as [_ C]. cbn [cm_annotation_erases] in E; subst ks.
   cbn [cm_step cm_annotation_step]; destruct (cm_ann_cursors ann) as [|[phase owner ob oc] rest] eqn:CUR.
   + exact (proj1 R).
   + cbn [cm_cursor_frames cm_cursor_phase]; eapply cm_v_runtime_step; try eassumption.
     * exact (proj1 F).
     * unfold cm_runtime_core; rewrite CUR; exact R.
 - destruct R as [-> R]; cbn [cm_annotation_erases] in E; subst ks.
   cbn [cm_step cm_annotation_step]; destruct (cm_control_kind ctl=?4); [exact (proj1 R)|].
   destruct (cm_ann_cursors ann) as [|[phase owner ob oc] rest] eqn:CUR.
   + destruct (cm_control_kind ctl=?5); exact (proj1 R).
   + cbn [cm_cursor_frames cm_cursor_phase]; eapply cm_c_runtime_step; try eassumption.
     exact (proj1 F).
     unfold cm_runtime_core; rewrite CUR; exact R.
 - exact R.
Qed.
Definition cm_runtime_support_invariants sp ap p ast : Prop :=
 cm_short_support_invariants sp ap p ast /\
 cm_task_runtime_invariant (cm_source_function_policy sp) ap p (cm_astate_task ast) (cm_astate_annotation ast).
Lemma cm_runtime_support_initial sp ap p input : cm_task_succeeds sp (CMStartTask p input) ->
 cm_runtime_support_invariants sp ap p (cm_annotated_start (cm_source_function_policy sp) p input).
Proof. intro S; split; [now apply cm_short_support_initial|split; reflexivity]. Qed.
Lemma cm_runtime_support_step sp ap p ast : cm_semantic_wf_program (cm_source_function_policy sp) p ->
 cm_runtime_support_invariants sp ap p ast -> cm_runtime_support_invariants sp ap p (cm_annotated_step sp ap ast).
Proof.
 intros WF [SHORT R]; split; [now apply cm_short_support_step|].
 destruct SHORT as [[[CTRL [STATIC [B OTHER]]] BASE] OTHER2].
 destruct CTRL as [S [E [ROOT [C [X [F [SP A]]]]]]].
 apply cm_task_runtime_step_support; try assumption; exact (proj1 WF).
Qed.
Lemma cm_runtime_support_iter sp ap p n ast : cm_semantic_wf_program (cm_source_function_policy sp) p ->
 cm_runtime_support_invariants sp ap p ast -> cm_runtime_support_invariants sp ap p (cm_annotated_iter sp ap n ast).
Proof. intro WF; revert ast; induction n; intros ast H; [exact H|apply IHn; now apply cm_runtime_support_step]. Qed.
Theorem cm_source_termination_runtime_invariants sp ap p input output status n :
 cm_semantic_wf_program (cm_source_function_policy sp) p -> cm_source_terminates sp p input output status ->
 cm_runtime_support_invariants sp ap p (cm_annotated_iter sp ap n (cm_annotated_start (cm_source_function_policy sp) p input)).
Proof.
 intros WF [INPUT [STATUS [st [ctl [RUN [SUCCESS OUTPUT]]]]]].
 apply cm_runtime_support_iter; [exact WF|]. apply cm_runtime_support_initial.
 exists st,ctl,status; auto.
Qed.
Theorem cm_source_termination_runtime_invariant sp ap p input output status n :
 cm_semantic_wf_program (cm_source_function_policy sp) p -> cm_source_terminates sp p input output status ->
 cm_task_runtime_invariant (cm_source_function_policy sp) ap p
 (cm_astate_task (cm_annotated_iter sp ap n (cm_annotated_start (cm_source_function_policy sp) p input)))
 (cm_astate_annotation (cm_annotated_iter sp ap n (cm_annotated_start (cm_source_function_policy sp) p input))).
Proof. intros WF RUN; exact (proj2 (cm_source_termination_runtime_invariants sp ap p input output status n WF RUN)). Qed.
