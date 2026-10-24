Require Export SimpleC.EE.QCP_demos_human.cmc_annotation_execution_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
(* Proofs inspect finite constructors and boolean guards; they do not assume
   any source/target preservation result. *)
Ltac cm_ann_reduce := cbv beta iota zeta delta [cm_update_r cm_update_l cm_update_s cm_update_v cm_update_c
 cm_rstart cm_lstart cm_sstart cm_vapply cm_capply cm_args_start cm_begin_call
 cm_ann_plain cm_ann_linear cm_ann_push cm_ann_replace cm_ann_pop cm_ann_spills_set
 cm_ann_put_spill cm_ann_enter_call cm_ann_leave_call cm_update_annotation
 cm_ann_cursors cm_cursor_phase cm_cursor_frames cm_phase_frame cm_annotation_erases
 cm_annotation_rooted cm_cursors_rooted cm_list_empty cm_cursor_temp cm_cursor_break
 cm_cursor_continue cm_ann_temp cm_ann_break cm_ann_continue cm_ann_spills cm_ann_saved
 cm_ann_calls cm_ann_pc hd tl map andb orb] in *.
Ltac cm_ann_bool b := lazymatch b with
 | andb ?x ?y=>cm_ann_bool x | orb ?x ?y=>cm_ann_bool x | negb ?x=>cm_ann_bool x
 | _=>destruct b eqn:? end.
Ltac cm_ann_cases := cm_ann_reduce;
 repeat match goal with |- context[if ?b then _ else _] => cm_ann_bool b; cm_ann_reduce end.
Lemma cm_update_r_rooted sp ap p fid expr st ann : cm_annotation_rooted ann ->
 cm_annotation_rooted (cm_update_annotation (cm_update_r sp ap p fid st ann expr)).
Proof. destruct expr; intro H; cm_ann_cases; intuition discriminate. Qed.
Lemma cm_update_l_rooted sp ap p fid expr st ann : cm_annotation_rooted ann ->
 cm_annotation_rooted (cm_update_annotation (cm_update_l sp ap p fid st ann expr)).
Proof. destruct expr; intro H; cm_ann_cases; intuition discriminate. Qed.
Lemma cm_update_s_rooted sp ap p fid stmt st ann : cm_annotation_rooted ann ->
 cm_annotation_rooted (cm_update_annotation (cm_update_s sp ap p fid st ann stmt)).
Proof. destruct stmt; intro H; cm_ann_cases; intuition discriminate. Qed.
Lemma cm_update_r_erases sp ap p fid expr st ann :
 cm_annotation_erases (cm_rstart sp p fid expr st (cm_cursor_frames (cm_ann_cursors ann)))
 (cm_update_annotation (cm_update_r sp ap p fid st ann expr)).
Proof.
 destruct expr; try match goal with xs:list cm_expr |- _=>destruct xs end; cm_ann_cases; try reflexivity.
 all: try match goal with |- context[match ?xs with []=>_ | _::_=>_ end] => destruct xs; cm_ann_cases; reflexivity end.
Qed.
Lemma cm_update_l_erases sp ap p fid expr st ann :
 cm_annotation_erases (cm_lstart sp p fid expr st (cm_cursor_frames (cm_ann_cursors ann)))
 (cm_update_annotation (cm_update_l sp ap p fid st ann expr)).
Proof. destruct expr; cm_ann_cases; reflexivity. Qed.
Lemma cm_update_s_erases sp ap p fid stmt st ann :
 cm_annotation_erases (cm_sstart sp p fid stmt st (cm_cursor_frames (cm_ann_cursors ann)))
 (cm_update_annotation (cm_update_s sp ap p fid st ann stmt)).
Proof. destruct stmt; cm_ann_cases; reflexivity. Qed.
Lemma cm_update_v_preserves sp ap p fid v st phase pc temp breakpc continuepc pt pb pk rest spills saved calls :
 let ann:=CMAnnotation pc temp breakpc continuepc (CMACursor phase pt pb pk::rest) spills saved calls in
 cm_annotation_rooted ann ->
 cm_annotation_erases (cm_vapply sp p fid (cm_phase_frame phase) v st (cm_cursor_frames rest))
 (cm_update_annotation (cm_update_v sp ap p fid v st ann phase)) /\
 cm_annotation_rooted (cm_update_annotation (cm_update_v sp ap p fid v st ann phase)).
Proof.
 cbn zeta. destruct phase; intro H; cm_ann_cases; try (intuition discriminate).
 all: try match goal with |- context[match ?xs with []=>_ | _::_=>_ end] => destruct xs; cm_ann_cases; intuition discriminate end.
Qed.
Lemma cm_update_c_preserves sp ap p fid ctl st phase pc temp breakpc continuepc pt pb pk rest spills saved calls :
 let ann:=CMAnnotation pc temp breakpc continuepc (CMACursor phase pt pb pk::rest) spills saved calls in
 cm_annotation_rooted ann ->
 cm_annotation_erases (cm_capply sp p fid (cm_phase_frame phase) ctl st (cm_cursor_frames rest))
 (cm_update_annotation (cm_update_c sp ap p fid ctl st ann phase)) /\
 cm_annotation_rooted (cm_update_annotation (cm_update_c sp ap p fid ctl st ann phase)).
Proof. cbn zeta. destruct phase; intro H; cm_ann_cases; intuition discriminate. Qed.
Lemma cm_annotation_step_preserves sp ap task ann :
 cm_annotation_erases task ann -> cm_annotation_rooted ann ->
 cm_annotation_erases (cm_step sp task) (cm_update_annotation (cm_annotation_step sp ap task ann)) /\
 cm_annotation_rooted (cm_update_annotation (cm_annotation_step sp ap task ann)).
Proof.
 destruct task as [p input|p fid expr st ks|p fid expr st ks|p fid stmt st ks|p fid v st ks|p fid ctl st ks|st ctl status]; intros E H.
 - cbv beta iota zeta delta [cm_step cm_annotation_step cm_begin_call] .
   destruct (cm_call_ok sp p (cm_program_main p) [] (cm_initial_state sp p input) && (cm_call_depth [CMHaltK] <? 65536)); cm_ann_reduce; intuition discriminate.
 - cbn [cm_annotation_erases] in E; subst ks; split; [apply cm_update_r_erases|now apply cm_update_r_rooted].
 - cbn [cm_annotation_erases] in E; subst ks; split; [apply cm_update_l_erases|now apply cm_update_l_rooted].
 - cbn [cm_annotation_erases] in E; subst ks; split; [apply cm_update_s_erases|now apply cm_update_s_rooted].
 - destruct ann as [pc temp b c cursors spills saved calls]; cbn [cm_annotation_erases cm_ann_cursors] in E; subst ks.
   destruct cursors as [|[phase pt pb pk] rest].
   + split; [reflexivity|exact I].
   + apply cm_update_v_preserves; exact H.
 - destruct ann as [pc temp b c cursors spills saved calls]; cbn [cm_annotation_erases cm_ann_cursors] in E; subst ks.
   cbv beta iota zeta delta [cm_step cm_annotation_step cm_ann_cursors].
   destruct (cm_control_kind ctl =? 4) eqn:Exit.
   + split; [reflexivity|exact I].
   + destruct cursors as [|[phase pt pb pk] rest].
     * destruct (cm_control_kind ctl =? 5); split; try reflexivity; exact I.
     * apply cm_update_c_preserves; exact H.
 - split; assumption.
Qed.
Lemma cm_annotated_step_invariant sp ap ast :
 cm_annotation_erases (cm_astate_task ast) (cm_astate_annotation ast) /\ cm_annotation_rooted (cm_astate_annotation ast) ->
 cm_annotation_erases (cm_astate_task (cm_annotated_step sp ap ast)) (cm_astate_annotation (cm_annotated_step sp ap ast)) /\
 cm_annotation_rooted (cm_astate_annotation (cm_annotated_step sp ap ast)).
Proof. intros [E H]; now apply cm_annotation_step_preserves. Qed.
Lemma cm_annotated_iter_invariant sp ap n ast :
 cm_annotation_erases (cm_astate_task ast) (cm_astate_annotation ast) /\ cm_annotation_rooted (cm_astate_annotation ast) ->
 cm_annotation_erases (cm_astate_task (cm_annotated_iter sp ap n ast)) (cm_astate_annotation (cm_annotated_iter sp ap n ast)) /\
 cm_annotation_rooted (cm_astate_annotation (cm_annotated_iter sp ap n ast)).
Proof. revert ast; induction n; intros ast H; [exact H|apply IHn; now apply cm_annotated_step_invariant]. Qed.
Lemma cm_annotated_iter_erasure sp ap n ast :
 cm_annotation_erases (cm_astate_task ast) (cm_astate_annotation ast) /\ cm_annotation_rooted (cm_astate_annotation ast) ->
 cm_annotation_erases (cm_iter sp n (cm_astate_task ast)) (cm_astate_annotation (cm_annotated_iter sp ap n ast)).
Proof. intro H; rewrite <-cm_annotated_iter_task with (ap:=ap); exact (proj1 (cm_annotated_iter_invariant sp ap n ast H)). Qed.
Lemma cm_annotated_iter_succeeds sp ap n ast : cm_task_succeeds sp (cm_astate_task ast) -> cm_task_succeeds sp (cm_astate_task (cm_annotated_iter sp ap n ast)).
Proof. revert ast; induction n; intros ast H; [exact H|apply IHn; apply cm_succeeds_step_total; exact H]. Qed.
