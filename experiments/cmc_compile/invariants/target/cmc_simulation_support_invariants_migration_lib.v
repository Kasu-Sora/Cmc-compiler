Require Export SimpleC.EE.QCP_demos_human.cmc_simulation_fid_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
(* Seven of the source's eighteen conjuncts, plus a proved local refinement.
   This is deliberately not named cm_preservation_invariant: no claim about
   target execution or the eleven remaining conjuncts is made here. *)
Definition cm_control_support_invariants sp ap p ast : Prop :=
 cm_task_succeeds sp (cm_astate_task ast) /\
 cm_annotation_erases (cm_astate_task ast) (cm_astate_annotation ast) /\
 cm_annotation_rooted (cm_astate_annotation ast) /\
 cm_task_coordinate_ready (cm_source_function_policy sp) p (cm_astate_task ast) (cm_astate_annotation ast) /\
 cm_task_context_ready (cm_astate_task ast) (cm_astate_annotation ast) /\
 cm_task_fid_ready p (cm_astate_task ast) /\
 cm_annotation_spill_consistent ap (cm_astate_annotation ast) /\
 cm_task_active_fid_ready p (cm_astate_task ast).
Lemma cm_control_support_initial sp ap p input : cm_task_succeeds sp (CMStartTask p input) ->
 cm_control_support_invariants sp ap p (cm_annotated_start (cm_source_function_policy sp) p input).
Proof. intro H; repeat split; try exact H; try reflexivity. Qed.
Lemma cm_control_support_step sp ap p ast : cm_semantic_wf_program (cm_source_function_policy sp) p ->
 cm_control_support_invariants sp ap p ast -> cm_control_support_invariants sp ap p (cm_annotated_step sp ap ast).
Proof.
 intros [WF _] [S [E [R [C [X [F [L A]]]]]]].
 pose proof (cm_annotation_step_preserves sp ap _ _ E R) as [E' R'].
 pose proof (cm_task_fid_step_coordinate sp p _ _ C S F A) as [F' A'].
 unfold cm_control_support_invariants; split; [now apply cm_succeeds_step_total|].
 split; [exact E'|]. split; [exact R'|]. split; [now apply cm_task_coordinate_step|].
 split; [eapply cm_task_context_step_coordinate; eauto|]. split; [exact F'|].
 split; [eapply cm_annotation_step_spill_coordinate; eauto|exact A'].
Qed.
Lemma cm_control_support_iter sp ap p n ast : cm_semantic_wf_program (cm_source_function_policy sp) p ->
 cm_control_support_invariants sp ap p ast -> cm_control_support_invariants sp ap p (cm_annotated_iter sp ap n ast).
Proof. intro WF; revert ast; induction n; intros ast H; [exact H|apply IHn; now apply cm_control_support_step]. Qed.
Lemma cm_source_termination_support_invariants sp ap p input output status n :
 cm_semantic_wf_program (cm_source_function_policy sp) p -> cm_source_terminates sp p input output status ->
 cm_control_support_invariants sp ap p (cm_annotated_iter sp ap n (cm_annotated_start (cm_source_function_policy sp) p input)).
Proof.
 intros WF [INPUT [STATUS [st [ctl [RUN [SUCCESS OUTPUT]]]]]].
 apply cm_control_support_iter; [exact WF|]. apply cm_control_support_initial.
 exists st,ctl,status; auto.
Qed.
