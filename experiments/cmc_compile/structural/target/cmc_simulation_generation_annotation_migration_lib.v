Require Export SimpleC.EE.QCP_demos_human.cmc_simulation_generation_step_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Ltac cm_limit_reduce := repeat progress (cm_ann_reduce;
 cbv beta iota zeta delta [cm_task_generation_limit cm_step cm_control_kind] in *).
Ltac cm_limit_finish := repeat rewrite cm_enter_call_nextgen;
 cbv beta iota zeta delta [cm_state_store cm_state_io cm_activate_local cm_restore_scope cm_restore_call cm_initial_state cm_state_nextgen] in *;
 try lia; match goal with |- context[Zlength ?xs]=>pose proof (ListLib.General.Length.Zlength_nonneg xs); lia end.
Ltac cm_limit_cases := cm_limit_reduce;
 repeat match goal with |- context[if ?b then _ else _]=>cm_ann_bool b; cm_limit_reduce end.
Lemma cm_task_generation_limit_step sp task : cm_task_generation_limit task<=cm_task_generation_limit (cm_step sp task).
Proof.
 destruct task as [p input|p fid expr st ks|p fid expr st ks|p fid stmt st ks|p fid v st ks|p fid ctl st ks|st ctl status].
 - cm_limit_cases; cm_limit_finish.
 - destruct expr; cm_limit_cases; try cm_limit_finish.
   all: match goal with |- context[match ?xs with []=>_ | _::_=>_ end]=>destruct xs; cm_limit_cases; cm_limit_finish end.
 - destruct expr; cm_limit_cases; cm_limit_finish.
 - destruct stmt; cm_limit_cases; cm_limit_finish.
 - destruct ks as [|frame ks]; [reflexivity|destruct frame; cm_limit_cases; try cm_limit_finish].
   all: match goal with |- context[match ?xs with []=>_ | _::_=>_ end]=>destruct xs; cm_limit_cases; cm_limit_finish end.
 - destruct ks as [|frame ks]; [cm_limit_cases; cm_limit_finish|destruct frame; cm_limit_cases; cm_limit_finish].
 - reflexivity.
Qed.
Lemma cm_spill_remove_generation limit slot spills : cm_spills_generation_below limit spills -> cm_spills_generation_below limit (cm_spill_remove slot spills).
Proof. induction spills as [|[i v] rest IH]; cbn; auto; intros [V REST]; destruct (i=?slot); cbn; auto. Qed.
Lemma cm_spill_put_generation limit slot v spills : cm_value_generation_below limit v -> cm_spills_generation_below limit spills -> cm_spills_generation_below limit (cm_spill_put slot v spills).
Proof. intros V S; split; [exact V|now apply cm_spill_remove_generation]. Qed.
Ltac cm_payload_reduce := repeat progress (cm_ann_reduce;
 cbv beta iota zeta delta [cm_annotation_payload_generation_below cm_spill_frames_generation_below cm_spill_frame_spills cm_ann_done] in *).
Ltac cm_payload_cases := cm_payload_reduce;
 repeat match goal with |- context[if ?b then _ else _]=>cm_ann_bool b; cm_payload_reduce end.
Ltac cm_payload_finish := repeat match goal with H:_ /\ _ |- _=>destruct H end;
 repeat first [assumption | reflexivity | exact I | solve [apply cm_spill_put_generation; assumption] | match goal with |- _ /\ _=>split end].
Lemma cm_update_r_generation_payload sp ap p fid st ann expr limit : cm_annotation_payload_generation_below limit ann ->
 cm_annotation_payload_generation_below limit (cm_update_annotation (cm_update_r sp ap p fid st ann expr)).
Proof. destruct expr; intro H; cm_payload_cases; cm_payload_finish. Qed.
Lemma cm_update_l_generation_payload sp ap p fid st ann expr limit : cm_annotation_payload_generation_below limit ann ->
 cm_annotation_payload_generation_below limit (cm_update_annotation (cm_update_l sp ap p fid st ann expr)).
Proof. destruct expr; intro H; cm_payload_cases; cm_payload_finish. Qed.
Lemma cm_update_s_generation_payload sp ap p fid st ann stmt limit : cm_annotation_payload_generation_below limit ann ->
 cm_annotation_payload_generation_below limit (cm_update_annotation (cm_update_s sp ap p fid st ann stmt)).
Proof. destruct stmt; intro H; cm_payload_cases; cm_payload_finish. Qed.
Lemma cm_update_v_generation_payload sp ap p fid v st ann phase limit : cm_value_generation_below limit v -> cm_annotation_payload_generation_below limit ann ->
 cm_annotation_payload_generation_below limit (cm_update_annotation (cm_update_v sp ap p fid v st ann phase)).
Proof. destruct phase; intros V H; cm_payload_cases; cm_payload_finish. Qed.
Lemma cm_update_c_generation_payload sp ap p fid ctl st phase pc temp b c pt pb pk rest spills saved calls limit :
 let ann:=CMAnnotation pc temp b c (CMACursor phase pt pb pk::rest) spills saved calls in
 cm_annotation_spill_consistent ap ann -> cm_annotation_payload_generation_below limit ann ->
 cm_annotation_payload_generation_below limit (cm_update_annotation (cm_update_c sp ap p fid ctl st ann phase)).
Proof.
 cbn zeta; destruct phase; intros S H; cm_payload_cases; try cm_payload_finish.
 all: cbv beta iota zeta delta [cm_annotation_spill_consistent cm_cursors_spill_consistent cm_phase_is_call cm_ann_temp cm_ann_cursors cm_ann_spills cm_ann_saved cm_cursor_temp cm_cursor_phase] in S;
 destruct S as [_ [NE REST]]; destruct saved; [contradiction|cm_payload_reduce; cm_payload_finish].
Qed.
Lemma cm_annotation_generation_payload_step sp ap p task ann :
 cm_task_generation_below (cm_source_function_policy sp) p task -> cm_annotation_erases task ann ->
 cm_annotation_spill_consistent ap ann ->
 cm_annotation_payload_generation_below (cm_task_generation_limit task) ann ->
 cm_annotation_payload_generation_below (cm_task_generation_limit (cm_step sp task)) (cm_update_annotation (cm_annotation_step sp ap task ann)).
Proof.
 intros G E SP H; eapply cm_annotation_payload_generation_below_mono; [apply cm_task_generation_limit_step|].
 destruct task as [q input|q fid expr st ks|q fid expr st ks|q fid stmt st ks|q fid v st ks|q fid ctl st ks|st ctl status].
 - cbv beta iota zeta delta [cm_annotation_step]; cm_payload_cases; cm_payload_finish.
 - now apply cm_update_r_generation_payload.
 - now apply cm_update_l_generation_payload.
 - now apply cm_update_s_generation_payload.
 - destruct G as [_ [_ [V _]]]; destruct ann as [pc temp b c cursors spills saved calls]; cbn [cm_annotation_erases cm_ann_cursors] in E; subst ks.
   destruct cursors as [|[phase pt pb pk] rest]; [exact H|now apply cm_update_v_generation_payload].
 - destruct ann as [pc temp b c cursors spills saved calls]; cbn [cm_annotation_erases cm_ann_cursors] in E; subst ks.
   cbv beta iota zeta delta [cm_annotation_step cm_ann_cursors]. destruct (cm_control_kind ctl=?4); [exact H|].
   destruct cursors as [|[phase pt pb pk] rest]; [exact H|now apply cm_update_c_generation_payload].
 - exact H.
Qed.
(* This local conjunction contains ten original invariant components plus
   the proved active-fid and payload refinements. It makes no target claim. *)
Definition cm_structural_support_invariants sp ap p ast : Prop :=
 cm_control_support_invariants sp ap p ast /\
 cm_task_static_valid (cm_source_function_policy sp) (cm_astate_task ast) /\
 cm_task_budget (cm_source_function_policy sp) p (cm_astate_task ast) (cm_astate_annotation ast) /\
 cm_task_generation_below (cm_source_function_policy sp) p (cm_astate_task ast) /\
 cm_annotation_payload_generation_below (cm_task_generation_limit (cm_astate_task ast)) (cm_astate_annotation ast).
Lemma cm_structural_support_initial sp ap p input : cm_task_succeeds sp (CMStartTask p input) ->
 cm_structural_support_invariants sp ap p (cm_annotated_start (cm_source_function_policy sp) p input).
Proof. intro S; split; [now apply cm_control_support_initial|]. split; [exact I|]. split; [apply cm_task_budget_initial|]. split; [reflexivity|now split]. Qed.
Lemma cm_structural_support_step sp ap p ast : cm_semantic_wf_program (cm_source_function_policy sp) p ->
 cm_structural_support_invariants sp ap p ast -> cm_structural_support_invariants sp ap p (cm_annotated_step sp ap ast).
Proof.
 intros WF [SUP [STATIC [BUDGET [GEN PAYLOAD]]]]; pose proof SUP as [S [E [R [C [X [F [SP A]]]]]]].
 split; [now apply cm_control_support_step|]. split; [eapply cm_task_static_step_coordinate; eauto; exact (proj1 WF)|].
 split; [eapply cm_task_budget_step_coordinate; eauto|]. split; [eapply cm_task_generation_step_coordinate; eauto|].
 eapply cm_annotation_generation_payload_step; eauto.
Qed.
Lemma cm_structural_support_iter sp ap p n ast : cm_semantic_wf_program (cm_source_function_policy sp) p ->
 cm_structural_support_invariants sp ap p ast -> cm_structural_support_invariants sp ap p (cm_annotated_iter sp ap n ast).
Proof. intro WF; revert ast; induction n; intros ast H; [exact H|apply IHn; now apply cm_structural_support_step]. Qed.
Theorem cm_source_termination_structural_invariants sp ap p input output status n :
 cm_semantic_wf_program (cm_source_function_policy sp) p -> cm_source_terminates sp p input output status ->
 cm_structural_support_invariants sp ap p (cm_annotated_iter sp ap n (cm_annotated_start (cm_source_function_policy sp) p input)).
Proof.
 intros WF [INPUT [STATUS [st [ctl [RUN [SUCCESS OUTPUT]]]]]]; apply cm_structural_support_iter; [exact WF|].
 apply cm_structural_support_initial; exists st,ctl,status; auto.
Qed.
Theorem cm_source_termination_generation_safe sp ap p input output status n :
 cm_semantic_wf_program (cm_source_function_policy sp) p -> cm_source_terminates sp p input output status ->
 cm_task_generation_safe (cm_source_function_policy sp) p
 (cm_astate_task (cm_annotated_iter sp ap n (cm_annotated_start (cm_source_function_policy sp) p input)))
 (cm_astate_annotation (cm_annotated_iter sp ap n (cm_annotated_start (cm_source_function_policy sp) p input))).
Proof.
 intros WF TERM; pose proof (cm_source_termination_structural_invariants sp ap p input output status n WF TERM) as [_ [_ [_ [GEN PAYLOAD]]]].
 split; [exact GEN|now apply cm_annotation_payload_implies_task_generation].
Qed.
