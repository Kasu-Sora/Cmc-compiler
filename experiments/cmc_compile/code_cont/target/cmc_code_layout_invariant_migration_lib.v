Require Export SimpleC.EE.QCP_demos_human.cmc_code_value_total_migration_lib.
Require Export SimpleC.EE.QCP_demos_human.cmc_code_control_total_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_task_layout_step_support sp ap nilslot p task ann :
 cm_task_succeeds sp task -> cm_annotation_erases task ann ->
 cm_task_type_ready (cm_source_function_policy sp) nilslot p task ann ->
 cm_task_layout_ready sp ap p task ann -> cm_task_layout sp ap p task ann ->
 cm_task_layout sp ap p (cm_step sp task) (cm_update_annotation(cm_annotation_step sp ap task ann)).
Proof.
 intros S ER TYPE READY LAYOUT; destruct task as [q input|q fid expr st ks|q fid expr st ks|q fid stmt st ks|q fid v st ks|q fid ctl st ks|st ctl status].
 - destruct READY as [-> [-> OK]]; now apply cm_start_task_layout_step.
 - destruct READY as [-> READY]; cbn [cm_annotation_erases] in ER; subst ks.
   destruct TYPE as [_ [_ [_ [EW REST]]]]; eapply cm_r_task_layout_step; eauto.
 - destruct READY as [-> READY]; now apply cm_l_task_layout_step.
 - destruct READY as [-> READY]; now apply cm_s_task_layout_step.
 - destruct READY as [-> READY]; now apply cm_v_task_layout_step.
 - destruct READY as [-> READY]; now apply cm_c_task_layout_step.
 - exact I.
Qed.
Definition cm_code_support_invariants sp ap nilslot p ast : Prop :=
 cm_type_support_invariants sp ap nilslot p ast /\ cm_task_layout sp ap p (cm_astate_task ast) (cm_astate_annotation ast).
Lemma cm_code_support_initial sp ap nilslot p input : cm_task_succeeds sp (CMStartTask p input) -> cm_code_support_invariants sp ap nilslot p (cm_annotated_start (cm_source_function_policy sp) p input).
Proof. intro S; split; [now apply cm_type_support_initial|apply cm_task_layout_initial]. Qed.
Lemma cm_code_support_step sp ap nilslot p ast : cm_semantic_wf_program (cm_source_function_policy sp) p -> cm_code_support_invariants sp ap nilslot p ast -> cm_code_support_invariants sp ap nilslot p (cm_annotated_step sp ap ast).
Proof.
 intros WF [TYPE LAYOUT]; split; [now apply cm_type_support_step|].
 destruct TYPE as [TAG TYPE]; pose proof(cm_readiness_support_layout_ready sp ap p ast (proj1 TAG))as READY.
 pose proof(proj1(proj1 TAG))as RUN; pose proof(proj1(proj1(proj1(proj1 RUN))))as CTRL.
 destruct CTRL as [S [ER REST]]; eapply cm_task_layout_step_support; eauto.
Qed.
Lemma cm_code_support_iter sp ap nilslot p n ast : cm_semantic_wf_program (cm_source_function_policy sp) p -> cm_code_support_invariants sp ap nilslot p ast -> cm_code_support_invariants sp ap nilslot p (cm_annotated_iter sp ap n ast).
Proof. intro WF; revert ast; induction n; intros ast H; [exact H|apply IHn; now apply cm_code_support_step]. Qed.
Theorem cm_source_termination_code_invariants sp ap nilslot p input output status n :
 cm_semantic_wf_program (cm_source_function_policy sp) p -> cm_source_terminates sp p input output status ->
 cm_code_support_invariants sp ap nilslot p (cm_annotated_iter sp ap n (cm_annotated_start (cm_source_function_policy sp) p input)).
Proof.
 intros WF [INPUT [STATUS [st [ctl [RUN [SUCCESS OUTPUT]]]]]]; apply cm_code_support_iter; [exact WF|].
 apply cm_code_support_initial; exists st,ctl,status; auto.
Qed.
Theorem cm_source_termination_code_layout sp ap (nilslot:cm_slot_d) p input output status n :
 cm_semantic_wf_program (cm_source_function_policy sp) p -> cm_source_terminates sp p input output status ->
 cm_task_layout sp ap p (cm_astate_task (cm_annotated_iter sp ap n (cm_annotated_start (cm_source_function_policy sp) p input))) (cm_astate_annotation (cm_annotated_iter sp ap n (cm_annotated_start (cm_source_function_policy sp) p input))).
Proof. intros WF RUN; exact(proj2(cm_source_termination_code_invariants sp ap nilslot p input output status n WF RUN)). Qed.
