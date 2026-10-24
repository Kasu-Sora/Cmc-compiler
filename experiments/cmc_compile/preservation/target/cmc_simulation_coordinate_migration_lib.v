Require Export SimpleC.EE.QCP_demos_human.cmc_simulation_composition_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
(* cmc_preservation_ready_coordinate.c, with the original loop/call exceptions. *)
Definition cm_phase_child_temp phase owner := match phase with
 | CAAssignRP _ _ | CAIndexRP _ _=>owner+1
 | CABinRP op _ _ _ _=>if (op =? 0) || (op =? 1) then owner else owner+1
 | CAArgP _ _ _ _ _ _ _ scratch=>scratch | CACallP _ _ _ _ _=>0 | _=>owner end.
Definition cm_phase_control_regular phase := match phase with
 | CAWhileGuardP _ _ _ _ | CAWhileBodyP _ _ _ _ _ _ | CACallP _ _ _ _ _=>false | _=>true end.
Definition cm_phase_next_fid fid phase := match phase with CACallP caller _ _ _ _=>caller | _=>fid end.
Definition cm_phase_code_ready_at policy p fid breakpc continuepc phase : Prop := match phase with
 | CAWhileGuardP guard body start finish=>finish=start+cm_rvalue_code_count policy p fid guard+1+cm_stmt_code_count policy p fid body+1
 | CAWhileBodyP guard body _ _ start finish=>breakpc=finish /\ continuepc=start /\ finish=start+cm_rvalue_code_count policy p fid guard+1+cm_stmt_code_count policy p fid body+1
 | _=>True end.
Fixpoint cm_cursors_coordinate policy p fid temp breakpc continuepc cursors : Prop := match cursors with
 | []=>True | cursor::rest=>
 temp=cm_phase_child_temp (cm_cursor_phase cursor) (cm_cursor_temp cursor) /\
 (cm_phase_control_regular (cm_cursor_phase cursor)=true -> breakpc=cm_cursor_break cursor /\ continuepc=cm_cursor_continue cursor) /\
 cm_phase_code_ready_at policy p fid breakpc continuepc (cm_cursor_phase cursor) /\
 cm_cursors_coordinate policy p (cm_phase_next_fid fid (cm_cursor_phase cursor)) (cm_cursor_temp cursor) (cm_cursor_break cursor) (cm_cursor_continue cursor) rest end.
Definition cm_annotation_child_ready policy p fid ann := cm_cursors_coordinate policy p fid (cm_ann_temp ann) (cm_ann_break ann) (cm_ann_continue ann) (cm_ann_cursors ann).
Definition cm_task_coordinate_ready policy p task ann := match task with
 | CMStartTask q input=>q=p /\ ann=cm_initial_annotation
 | CMRTask q fid _ _ _ | CMLTask q fid _ _ _ | CMSTask q fid _ _ _ | CMVTask q fid _ _ _=>q=p /\ cm_annotation_child_ready policy p fid ann
 | CMCTask q fid ctl _ _=>q=p /\ (cm_control_kind ctl=5 \/ cm_annotation_child_ready policy p fid ann)
 | CMDoneTask _ _ _=>True end.
Ltac cm_coord_reduce := repeat progress (cm_ann_reduce;
 cbv beta iota zeta delta [cm_task_coordinate_ready cm_annotation_child_ready cm_cursors_coordinate
 cm_phase_child_temp cm_phase_control_regular cm_phase_code_ready_at cm_phase_next_fid cm_control_kind andb orb] in *).
Ltac cm_coord_cases := cm_coord_reduce;
 repeat match goal with |- context[if ?b then _ else _] => cm_ann_bool b; cm_coord_reduce end.
Ltac cm_coord_finish := repeat match goal with H:_ \/ _ |- _ => destruct H end; try discriminate;
 repeat match goal with H:_ /\ _ |- _ => destruct H end;
 repeat match goal with H:true=true -> _ |- _ => specialize (H eq_refl) end;
 repeat match goal with H:_ /\ _ |- _ => destruct H end;
 subst; cbn [andb orb] in *; intuition (try congruence; try lia).
Lemma cm_task_coordinate_initial policy p input : cm_task_coordinate_ready policy p (CMStartTask p input) cm_initial_annotation.
Proof. split; reflexivity. Qed.
Lemma cm_r_coordinate_step sp ap p fid expr st ann : cm_annotation_child_ready (cm_source_function_policy sp) p fid ann ->
 cm_task_coordinate_ready (cm_source_function_policy sp) p (cm_rstart sp p fid expr st (cm_cursor_frames (cm_ann_cursors ann)))
 (cm_update_annotation (cm_update_r sp ap p fid st ann expr)).
Proof.
 destruct expr; try match goal with xs:list cm_expr |- _=>destruct xs end; intro H; cm_coord_cases; try cm_coord_finish.
 all: match goal with |- context[match ?xs with []=>_ | _::_=>_ end] => destruct xs; cm_coord_cases; cm_coord_finish end.
Qed.
Lemma cm_l_coordinate_step sp ap p fid expr st ann : cm_annotation_child_ready (cm_source_function_policy sp) p fid ann ->
 cm_task_coordinate_ready (cm_source_function_policy sp) p (cm_lstart sp p fid expr st (cm_cursor_frames (cm_ann_cursors ann)))
 (cm_update_annotation (cm_update_l sp ap p fid st ann expr)).
Proof. destruct expr; intro H; cm_coord_cases; cm_coord_finish. Qed.
Lemma cm_s_coordinate_step sp ap p fid stmt st ann : cm_annotation_child_ready (cm_source_function_policy sp) p fid ann ->
 cm_task_coordinate_ready (cm_source_function_policy sp) p (cm_sstart sp p fid stmt st (cm_cursor_frames (cm_ann_cursors ann)))
 (cm_update_annotation (cm_update_s sp ap p fid st ann stmt)).
Proof. destruct stmt; intro H; cm_coord_cases; cbn [cm_stmt_code_count]; cm_coord_finish. Qed.
Lemma cm_v_coordinate_step sp ap p fid v st phase pc temp b c pt pb pk rest spills saved calls :
 let ann:=CMAnnotation pc temp b c (CMACursor phase pt pb pk::rest) spills saved calls in
 cm_annotation_child_ready (cm_source_function_policy sp) p fid ann ->
 cm_task_coordinate_ready (cm_source_function_policy sp) p (cm_vapply sp p fid (cm_phase_frame phase) v st (cm_cursor_frames rest))
 (cm_update_annotation (cm_update_v sp ap p fid v st ann phase)).
Proof.
 cbn zeta; destruct phase; intro H; cm_coord_cases; try cm_coord_finish.
 all: try match goal with |- context[match ?xs with []=>_ | _::_=>_ end] => destruct xs; cm_coord_cases; cm_coord_finish end.
Qed.
Lemma cm_c_coordinate_step sp ap p fid ctl st phase pc temp b c pt pb pk rest spills saved calls :
 let ann:=CMAnnotation pc temp b c (CMACursor phase pt pb pk::rest) spills saved calls in
 (cm_control_kind ctl=5 \/ cm_annotation_child_ready (cm_source_function_policy sp) p fid ann) ->
 cm_task_coordinate_ready (cm_source_function_policy sp) p (cm_capply sp p fid (cm_phase_frame phase) ctl st (cm_cursor_frames rest))
 (cm_update_annotation (cm_update_c sp ap p fid ctl st ann phase)).
Proof. cbn zeta; destruct ctl; destruct phase; intro H; cm_coord_cases; cm_coord_finish. Qed.
Lemma cm_task_coordinate_step sp ap p task ann :
 cm_annotation_erases task ann -> cm_task_coordinate_ready (cm_source_function_policy sp) p task ann ->
 cm_task_coordinate_ready (cm_source_function_policy sp) p (cm_step sp task) (cm_update_annotation (cm_annotation_step sp ap task ann)).
Proof.
 destruct task as [q input|q fid expr st ks|q fid expr st ks|q fid stmt st ks|q fid v st ks|q fid ctl st ks|st ctl status]; intros E H.
 - destruct H as [-> ->]. cbv beta iota zeta delta [cm_step cm_annotation_step cm_begin_call].
   destruct (cm_call_ok sp p (cm_program_main p) [] (cm_initial_state sp p input) && (cm_call_depth [CMHaltK] <? 65536)); cm_coord_reduce; cbn [cm_initial_annotation cm_ann_temp cm_ann_break cm_ann_continue]; cm_coord_finish.
 - destruct H as [-> H]; cbn [cm_annotation_erases] in E; subst ks; now apply cm_r_coordinate_step.
 - destruct H as [-> H]; cbn [cm_annotation_erases] in E; subst ks; now apply cm_l_coordinate_step.
 - destruct H as [-> H]; cbn [cm_annotation_erases] in E; subst ks; now apply cm_s_coordinate_step.
 - destruct H as [-> H]; destruct ann as [pc temp b c cursors spills saved calls]; cbn [cm_annotation_erases cm_ann_cursors] in E; subst ks.
   destruct cursors as [|[phase pt pb pk] rest]; [exact I|now apply cm_v_coordinate_step].
 - destruct H as [-> H]; destruct ann as [pc temp b c cursors spills saved calls]; cbn [cm_annotation_erases cm_ann_cursors] in E; subst ks.
   cbv beta iota zeta delta [cm_step cm_annotation_step cm_ann_cursors].
   destruct (cm_control_kind ctl =? 4); [exact I|].
   destruct cursors as [|[phase pt pb pk] rest]; [destruct (cm_control_kind ctl =? 5); exact I|now apply cm_c_coordinate_step].
 - exact I.
Qed.
Lemma cm_annotated_iter_coordinate sp ap p n ast :
 cm_annotation_erases (cm_astate_task ast) (cm_astate_annotation ast) /\ cm_annotation_rooted (cm_astate_annotation ast) ->
 cm_task_coordinate_ready (cm_source_function_policy sp) p (cm_astate_task ast) (cm_astate_annotation ast) ->
 cm_task_coordinate_ready (cm_source_function_policy sp) p (cm_astate_task (cm_annotated_iter sp ap n ast)) (cm_astate_annotation (cm_annotated_iter sp ap n ast)).
Proof.
 revert ast; induction n; intros ast HE HC; [exact HC|]. apply IHn.
 - now apply cm_annotated_step_invariant.
 - apply cm_task_coordinate_step; [exact (proj1 HE)|exact HC].
Qed.
Lemma cm_annotated_start_iter_coordinate sp ap p input n :
 cm_task_coordinate_ready (cm_source_function_policy sp) p
 (cm_astate_task (cm_annotated_iter sp ap n (cm_annotated_start (cm_source_function_policy sp) p input)))
 (cm_astate_annotation (cm_annotated_iter sp ap n (cm_annotated_start (cm_source_function_policy sp) p input))).
Proof. apply cm_annotated_iter_coordinate; [split; [apply cm_annotated_start_erases|apply cm_annotated_start_rooted]|apply cm_task_coordinate_initial]. Qed.
