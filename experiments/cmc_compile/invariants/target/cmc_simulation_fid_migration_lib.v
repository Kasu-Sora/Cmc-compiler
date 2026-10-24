Require Export SimpleC.EE.QCP_demos_human.cmc_simulation_context_step_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
(* Original cmc_preservation_fid.c predicates. *)
Definition cm_frame_parent_fid frame fid := match frame with CMCallK caller _ _ _ _=>caller | _=>fid end.
Definition cm_frame_fid_ready p fid frame : Prop := match frame with CMHaltK=>fid = -1 | _=>0<=fid<Zlength (cm_program_functions p) end.
Fixpoint cm_frames_fid_ready p fid frames : Prop := match frames with
 | []=>fid = -1 | frame::rest=>cm_frame_fid_ready p fid frame /\ cm_frames_fid_ready p (cm_frame_parent_fid frame fid) rest end.
Definition cm_task_fid_ready p task : Prop := match task with
 | CMStartTask _ _ | CMDoneTask _ _ _=>True
 | CMRTask _ fid _ _ ks | CMLTask _ fid _ _ ks | CMSTask _ fid _ _ ks | CMVTask _ fid _ _ ks | CMCTask _ fid _ _ ks=>cm_frames_fid_ready p fid ks end.
Definition cm_cursors_fid_ready p fid cursors := cm_frames_fid_ready p fid (cm_cursor_frames cursors).
(* Local refinement established from Start and preserved, not a new C precondition.
   Expressions/statements run inside a function; only V/C may run at root -1. *)
Definition cm_task_active_fid_ready p task : Prop := match task with
 | CMRTask _ fid _ _ _ | CMLTask _ fid _ _ _ | CMSTask _ fid _ _ _=>0<=fid<Zlength (cm_program_functions p) | _=>True end.
Lemma cm_call_ok_fid_bounds sp p fid values st : cm_call_ok sp p fid values st=true -> 0<=fid<Zlength (cm_program_functions p).
Proof. unfold cm_call_ok; intro H; repeat rewrite andb_true_iff in H; repeat match goal with H:_ /\ _ |- _=>destruct H end; split; [now apply Z.leb_le|now apply Z.ltb_lt]. Qed.
Ltac cm_fid_reduce := repeat progress (cm_ann_reduce;
 cbv beta iota zeta delta [cm_task_fid_ready cm_task_active_fid_ready cm_frames_fid_ready cm_frame_fid_ready cm_frame_parent_fid cm_control_kind] in *).
Ltac cm_fid_cases := cm_fid_reduce;
 repeat match goal with |- context[if ?b then _ else _]=>cm_ann_bool b; cm_fid_reduce end.
Ltac cm_fid_finish :=
 repeat match goal with H:(if cm_call_ok ?sp ?p ?fid ?vs ?st then ?b else false)=true |- _=>
   apply andb_true_iff in H; destruct H as [H D]; apply cm_call_ok_fid_bounds in H end;
 repeat match goal with H:_ /\ _ |- _=>destruct H end;
 repeat split; try assumption; try reflexivity; try lia.
Lemma cm_r_fid_step sp p fid expr st ks : 0<=fid<Zlength (cm_program_functions p) -> cm_frames_fid_ready p fid ks ->
 cm_task_fid_ready p (cm_rstart sp p fid expr st ks) /\ cm_task_active_fid_ready p (cm_rstart sp p fid expr st ks).
Proof.
 destruct expr; try match goal with xs:list cm_expr |- _=>destruct xs end; intros B H; cm_fid_cases; try cm_fid_finish.
 all: match goal with |- context[match ?xs with []=>_ | _::_=>_ end]=>destruct xs; cm_fid_cases; cm_fid_finish end.
Qed.
Lemma cm_l_fid_step sp p fid expr st ks : 0<=fid<Zlength (cm_program_functions p) -> cm_frames_fid_ready p fid ks ->
 cm_task_fid_ready p (cm_lstart sp p fid expr st ks) /\ cm_task_active_fid_ready p (cm_lstart sp p fid expr st ks).
Proof. destruct expr; intros B H; cm_fid_cases; cm_fid_finish. Qed.
Lemma cm_s_fid_step sp p fid stmt st ks : 0<=fid<Zlength (cm_program_functions p) -> cm_frames_fid_ready p fid ks ->
 cm_task_fid_ready p (cm_sstart sp p fid stmt st ks) /\ cm_task_active_fid_ready p (cm_sstart sp p fid stmt st ks).
Proof. destruct stmt; intros B H; cm_fid_cases; cm_fid_finish. Qed.
Lemma cm_v_fid_step sp p fid frame v st ks :
 cm_task_succeeds sp (cm_vapply sp p fid frame v st ks) -> cm_frames_fid_ready p fid (frame::ks) ->
 cm_task_fid_ready p (cm_vapply sp p fid frame v st ks) /\ cm_task_active_fid_ready p (cm_vapply sp p fid frame v st ks).
Proof.
 destruct frame; intros S H; cm_fid_cases; try cm_fid_finish.
 all: try match goal with |- context[match ?xs with []=>_ | _::_=>_ end]=>destruct xs; cm_fid_cases; cm_fid_finish end.
 all: exfalso; eapply cm_error_not_succeeds; exact S.
Qed.
Lemma cm_c_fid_step sp p fid frame ctl st ks : cm_frames_fid_ready p fid (frame::ks) ->
 cm_task_fid_ready p (cm_capply sp p fid frame ctl st ks) /\ cm_task_active_fid_ready p (cm_capply sp p fid frame ctl st ks).
Proof. destruct frame; intros H; cm_fid_cases; cm_fid_finish. Qed.
Lemma cm_task_fid_step_coordinate sp p task ann :
 cm_task_coordinate_ready (cm_source_function_policy sp) p task ann -> cm_task_succeeds sp task ->
 cm_task_fid_ready p task -> cm_task_active_fid_ready p task ->
 cm_task_fid_ready p (cm_step sp task) /\ cm_task_active_fid_ready p (cm_step sp task).
Proof.
 destruct task as [q input|q fid expr st ks|q fid expr st ks|q fid stmt st ks|q fid v st ks|q fid ctl st ks|st ctl status]; intros C S H B.
 - destruct C as [-> C]. cbv beta iota zeta delta [cm_step cm_begin_call].
   destruct (cm_call_ok sp p (cm_program_main p) [] (cm_initial_state sp p input) && (cm_call_depth [CMHaltK] <? 65536)) eqn:Call; cm_fid_reduce; cm_fid_finish.
 - destruct C as [-> C]; now apply cm_r_fid_step.
 - destruct C as [-> C]; now apply cm_l_fid_step.
 - destruct C as [-> C]; now apply cm_s_fid_step.
 - destruct C as [-> C]; destruct ks as [|frame rest]; [repeat split|].
   apply cm_v_fid_step; [now apply cm_succeeds_step_total in S|exact H].
 - destruct C as [-> C]; cbv beta iota zeta delta [cm_step]. destruct (cm_control_kind ctl=?4); [repeat split|].
   destruct ks as [|frame rest]; [destruct (cm_control_kind ctl=?5); repeat split|now apply cm_c_fid_step].
 - repeat split.
Qed.
Lemma cm_annotated_iter_fid_coordinate sp ap p n ast :
 cm_task_succeeds sp (cm_astate_task ast) ->
 cm_annotation_erases (cm_astate_task ast) (cm_astate_annotation ast) /\ cm_annotation_rooted (cm_astate_annotation ast) ->
 cm_task_coordinate_ready (cm_source_function_policy sp) p (cm_astate_task ast) (cm_astate_annotation ast) ->
 cm_task_fid_ready p (cm_astate_task ast) /\ cm_task_active_fid_ready p (cm_astate_task ast) ->
 cm_task_fid_ready p (cm_astate_task (cm_annotated_iter sp ap n ast)) /\ cm_task_active_fid_ready p (cm_astate_task (cm_annotated_iter sp ap n ast)).
Proof.
 revert ast; induction n; intros ast S E C [H B]; [now split|]. apply IHn.
 - now apply cm_succeeds_step_total.
 - now apply cm_annotated_step_invariant.
 - apply cm_task_coordinate_step; [exact (proj1 E)|exact C].
 - eapply cm_task_fid_step_coordinate; eauto.
Qed.
Lemma cm_annotated_start_iter_fid_ready sp ap p input n : cm_task_succeeds sp (CMStartTask p input) ->
 cm_task_fid_ready p (cm_astate_task (cm_annotated_iter sp ap n (cm_annotated_start (cm_source_function_policy sp) p input))) /\
 cm_task_active_fid_ready p (cm_astate_task (cm_annotated_iter sp ap n (cm_annotated_start (cm_source_function_policy sp) p input))).
Proof.
 intro H; eapply cm_annotated_iter_fid_coordinate; [exact H| |apply cm_task_coordinate_initial|now split].
 split; [apply cm_annotated_start_erases|apply cm_annotated_start_rooted].
Qed.
