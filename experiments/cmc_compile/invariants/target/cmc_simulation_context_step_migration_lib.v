Require Export SimpleC.EE.QCP_demos_human.cmc_simulation_context_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_stmt_scope_context_view loop call stmt : cm_stmt_scope_ready loop call stmt ->
 (match stmt with CMBreakS | CMContinueS=>loop=true | CMReturnS _=>call=true | _=>True end).
Proof. destruct stmt; cbn; tauto. Qed.
Ltac cm_context_reduce := repeat progress (cm_ann_reduce;
 cbv beta iota zeta delta [cm_task_context_ready cm_cursors_context_ready cm_cursors_scope_ready
 cm_phase_scope_ready cm_phase_accepts_statement cm_phase_requires_statement_parent
 cm_statement_cursors_ready cm_control_context_ready cm_stmt_context_ready cm_control_kind
 cm_cursors_loop_ready cm_cursors_call_ready cm_phase_control_scope] in *).
Ltac cm_context_cases := cm_context_reduce;
 repeat match goal with |- context[if ?b then _ else _]=>cm_ann_bool b; cm_context_reduce end.
Ltac cm_context_finish := repeat match goal with H:_ /\ _ |- _=>destruct H end;
 repeat match goal with H:true=true -> _ |- _=>specialize (H eq_refl) end;
 try solve [intuition discriminate]; repeat split; try assumption; try reflexivity; try discriminate;
 try solve [apply cm_stmt_scope_context_ready; assumption].
Lemma cm_r_context_step sp ap p fid expr st ann : cm_typed_program (cm_source_function_policy sp) p ->
 cm_task_context_ready (CMRTask p fid expr st (cm_cursor_frames (cm_ann_cursors ann))) ann ->
 cm_task_context_ready (cm_rstart sp p fid expr st (cm_cursor_frames (cm_ann_cursors ann)))
 (cm_update_annotation (cm_update_r sp ap p fid st ann expr)).
Proof.
 intros WF; destruct expr; try match goal with xs:list cm_expr |- _=>destruct xs end; intro H;
 cm_context_cases; try cm_context_finish.
 all: try match goal with |- context[match ?xs with []=>_ | _::_=>_ end]=>destruct xs; cm_context_cases; try cm_context_finish end.
 all: match goal with H:(if cm_call_ok ?sp ?p ?fid ?vs ?st then ?b else false)=true |- _=>
   apply andb_true_iff in H; destruct H as [CALL DEPTH];
   pose proof (cm_call_ok_scope_ready sp p fid vs st WF CALL) as BODY end.
 all: try exact BODY.
 all: destruct (cm_function_body (cm_source_function_at sp fid0 p)); cbn [cm_stmt_scope_ready] in BODY; auto.
Qed.
Lemma cm_l_context_step sp ap p fid expr st ann :
 cm_task_context_ready (CMLTask p fid expr st (cm_cursor_frames (cm_ann_cursors ann))) ann ->
 cm_task_context_ready (cm_lstart sp p fid expr st (cm_cursor_frames (cm_ann_cursors ann)))
 (cm_update_annotation (cm_update_l sp ap p fid st ann expr)).
Proof. destruct expr; intro H; cm_context_cases; cm_context_finish. Qed.
Lemma cm_s_context_step sp ap p fid stmt st ann :
 cm_task_context_ready (CMSTask p fid stmt st (cm_cursor_frames (cm_ann_cursors ann))) ann ->
 cm_task_context_ready (cm_sstart sp p fid stmt st (cm_cursor_frames (cm_ann_cursors ann)))
 (cm_update_annotation (cm_update_s sp ap p fid st ann stmt)).
Proof.
 destruct stmt; intro H; cm_context_cases; cbn [cm_stmt_scope_ready] in *; try cm_context_finish.
all: intros; assumption.
Qed.
Lemma cm_v_context_step sp ap p fid v st phase pc temp b c pt pb pk rest spills saved calls :
 let ann:=CMAnnotation pc temp b c (CMACursor phase pt pb pk::rest) spills saved calls in
 cm_typed_program (cm_source_function_policy sp) p ->
 cm_task_context_ready (CMVTask p fid v st (cm_cursor_frames (cm_ann_cursors ann))) ann ->
 cm_task_context_ready (cm_vapply sp p fid (cm_phase_frame phase) v st (cm_cursor_frames rest))
 (cm_update_annotation (cm_update_v sp ap p fid v st ann phase)).
Proof.
 cbn zeta; intros WF; destruct phase; intro H; cm_context_cases; try cm_context_finish.
 all: try match goal with |- context[match ?xs with []=>_ | _::_=>_ end]=>destruct xs; cm_context_cases; try cm_context_finish end.
 all: try solve [apply cm_stmt_scope_context_view; assumption].
 all: match goal with H:(if cm_call_ok ?sp ?p ?fid ?vs ?st then ?b else false)=true |- _=>
   apply andb_true_iff in H; destruct H as [CALL DEPTH];
   pose proof (cm_call_ok_scope_ready sp p fid vs st WF CALL) as BODY end.
 all: try exact BODY.
 all: apply cm_stmt_scope_context_view; exact BODY.
Qed.
Lemma cm_c_context_step sp ap p fid ctl st phase pc temp b c pt pb pk rest spills saved calls :
 let ann:=CMAnnotation pc temp b c (CMACursor phase pt pb pk::rest) spills saved calls in
 cm_task_context_ready (CMCTask p fid ctl st (cm_cursor_frames (cm_ann_cursors ann))) ann ->
 cm_task_context_ready (cm_capply sp p fid (cm_phase_frame phase) ctl st (cm_cursor_frames rest))
 (cm_update_annotation (cm_update_c sp ap p fid ctl st ann phase)).
Proof.
 cbn zeta; destruct ctl; destruct phase; intro H; cm_context_cases; try cm_context_finish.
 all: try solve [apply cm_stmt_scope_context_view; assumption].
Qed.
Lemma cm_task_context_step_coordinate sp ap p task ann :
 cm_typed_program (cm_source_function_policy sp) p -> cm_annotation_erases task ann ->
 cm_task_coordinate_ready (cm_source_function_policy sp) p task ann ->
 cm_task_context_ready task ann ->
 cm_task_context_ready (cm_step sp task) (cm_update_annotation (cm_annotation_step sp ap task ann)).
Proof.
 intros WF; destruct task as [q input|q fid expr st ks|q fid expr st ks|q fid stmt st ks|q fid v st ks|q fid ctl st ks|st ctl status]; intros E C H.
 - destruct C as [-> ->]. cbv beta iota zeta delta [cm_step cm_annotation_step cm_begin_call].
   destruct (cm_call_ok sp p (cm_program_main p) [] (cm_initial_state sp p input) && (cm_call_depth [CMHaltK] <? 65536)) eqn:Call;
   cm_context_reduce; cbn [cm_initial_annotation cm_ann_cursors]; try cm_context_finish.
   all: apply andb_true_iff in Call; destruct Call as [Call _];
     pose proof (cm_call_ok_scope_ready sp p (cm_program_main p) [] (cm_initial_state sp p input) WF Call) as B;
     try exact B; apply cm_stmt_scope_context_view; exact B.
 - destruct C as [-> C]; cbn [cm_annotation_erases] in E; subst ks; now apply cm_r_context_step.
 - destruct C as [-> C]; cbn [cm_annotation_erases] in E; subst ks; now apply cm_l_context_step.
 - destruct C as [-> C]; cbn [cm_annotation_erases] in E; subst ks; now apply cm_s_context_step.
 - destruct C as [-> C]; destruct ann as [pc temp b c cursors spills saved calls]; cbn [cm_annotation_erases cm_ann_cursors] in E; subst ks.
   destruct cursors as [|[phase pt pb pk] rest]; [repeat split|now apply cm_v_context_step].
 - destruct C as [-> C]; destruct ann as [pc temp b c cursors spills saved calls]; cbn [cm_annotation_erases cm_ann_cursors] in E; subst ks.
   cbv beta iota zeta delta [cm_step cm_annotation_step cm_ann_cursors].
   destruct (cm_control_kind ctl=?4); [repeat split|].
   destruct cursors as [|[phase pt pb pk] rest]; [destruct (cm_control_kind ctl=?5); repeat split|now apply cm_c_context_step].
 - exact H.
Qed.
Lemma cm_annotated_iter_context_coordinate sp ap p n ast : cm_typed_program (cm_source_function_policy sp) p ->
 cm_annotation_erases (cm_astate_task ast) (cm_astate_annotation ast) /\ cm_annotation_rooted (cm_astate_annotation ast) ->
 cm_task_coordinate_ready (cm_source_function_policy sp) p (cm_astate_task ast) (cm_astate_annotation ast) ->
 cm_task_context_ready (cm_astate_task ast) (cm_astate_annotation ast) ->
 cm_task_context_ready (cm_astate_task (cm_annotated_iter sp ap n ast)) (cm_astate_annotation (cm_annotated_iter sp ap n ast)).
Proof.
 intros WF; revert ast; induction n; intros ast E C H; [exact H|]. apply IHn.
 - now apply cm_annotated_step_invariant.
 - apply cm_task_coordinate_step; [exact (proj1 E)|exact C].
 - eapply cm_task_context_step_coordinate; eauto; exact (proj1 E).
Qed.
Lemma cm_annotated_start_iter_context sp ap p input n : cm_semantic_wf_program (cm_source_function_policy sp) p ->
 cm_task_context_ready (cm_astate_task (cm_annotated_iter sp ap n (cm_annotated_start (cm_source_function_policy sp) p input)))
 (cm_astate_annotation (cm_annotated_iter sp ap n (cm_annotated_start (cm_source_function_policy sp) p input))).
Proof.
 intros [WF _]; eapply cm_annotated_iter_context_coordinate; [exact WF| |apply cm_task_coordinate_initial|apply cm_task_context_initial].
 split; [apply cm_annotated_start_erases|apply cm_annotated_start_rooted].
Qed.
