Require Export SimpleC.EE.QCP_demos_human.cmc_type_step_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Definition cm_type_support_invariants sp ap nilslot p ast : Prop := cm_tagged_support_invariants sp ap p ast /\ cm_task_type_ready (cm_source_function_policy sp) nilslot p (cm_astate_task ast) (cm_astate_annotation ast).
Lemma cm_type_support_initial sp ap nilslot p input : cm_task_succeeds sp (CMStartTask p input) -> cm_type_support_invariants sp ap nilslot p (cm_annotated_start (cm_source_function_policy sp) p input).
Proof. intro S; split; [now apply cm_tagged_support_initial|reflexivity]. Qed.
Lemma cm_type_support_step sp ap nilslot p ast : cm_semantic_wf_program (cm_source_function_policy sp) p -> cm_type_support_invariants sp ap nilslot p ast -> cm_type_support_invariants sp ap nilslot p (cm_annotated_step sp ap ast).
Proof.
 intros WF [TAG TYPE]; split; [now apply cm_tagged_support_step|].
 pose proof (proj1 (proj1 TAG)) as RUN; pose proof (proj1 (proj1 (proj1 (proj1 RUN)))) as CTRL.
 destruct CTRL as [S [ER [ROOT [COORD [CONTEXT [FID REST]]]]]].
 eapply cm_task_type_step_support; eauto; exact (proj1 WF).
Qed.
Lemma cm_type_support_iter sp ap nilslot p n ast : cm_semantic_wf_program (cm_source_function_policy sp) p -> cm_type_support_invariants sp ap nilslot p ast -> cm_type_support_invariants sp ap nilslot p (cm_annotated_iter sp ap n ast).
Proof. intro WF; revert ast; induction n; intros ast H; [exact H|apply IHn; now apply cm_type_support_step]. Qed.
Theorem cm_source_termination_type_invariants sp ap nilslot p input output status n :
 cm_semantic_wf_program (cm_source_function_policy sp) p -> cm_source_terminates sp p input output status ->
 cm_type_support_invariants sp ap nilslot p (cm_annotated_iter sp ap n (cm_annotated_start (cm_source_function_policy sp) p input)).
Proof.
 intros WF [INPUT [STATUS [st [ctl [RUN [SUCCESS OUTPUT]]]]]].
 apply cm_type_support_iter; [exact WF|]. apply cm_type_support_initial; exists st,ctl,status; auto.
Qed.
Theorem cm_source_termination_type_ready sp ap nilslot p input output status n :
 cm_semantic_wf_program (cm_source_function_policy sp) p -> cm_source_terminates sp p input output status ->
 cm_task_type_ready (cm_source_function_policy sp) nilslot p (cm_astate_task (cm_annotated_iter sp ap n (cm_annotated_start (cm_source_function_policy sp) p input))) (cm_astate_annotation (cm_annotated_iter sp ap n (cm_annotated_start (cm_source_function_policy sp) p input))).
Proof. intros WF RUN; exact (proj2 (cm_source_termination_type_invariants sp ap nilslot p input output status n WF RUN)). Qed.
