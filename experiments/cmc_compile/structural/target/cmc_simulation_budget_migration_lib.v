Require Export SimpleC.EE.QCP_demos_human.cmc_simulation_static_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
(* cmc_preservation_budget_defs.c. No machine-capacity bound is added. *)
Definition cm_phase_budget policy p fid phase owner : Prop := let slots:=cm_temp_slots (cm_function_at policy fid (cm_program_functions p)) in match phase with
 | CAAssignLP src _ | CAIndexLP src _=>0<=owner /\ owner+1+cm_rtemps src<=slots
 | CABinLP op _ rhs _=>0<=owner /\ owner+(if (op=?0)||(op=?1) then cm_rtemps rhs else 1+cm_rtemps rhs)<=slots
 | CASeqP second=>0<=owner /\ owner+cm_stemps second<=slots
 | CAIfP yes no=>0<=owner /\ owner+cm_stemps yes<=slots /\ owner+cm_stemps no<=slots
 | CAWhileGuardP guard body _ _ | CAWhileBodyP guard body _ _ _ _=>0<=owner /\ owner+cm_rtemps guard<=slots /\ owner+cm_stemps body<=slots
 | CAArgP _ rest _ _ _ base current scratch=>0<=base /\ 0<=current /\ 0<=scratch /\ current<slots /\ current+1+Zlength rest=scratch /\ scratch+cm_adepth (cm_args_apair rest)<=slots
 | _=>True end.
Fixpoint cm_cursors_budget policy p fid cursors : Prop := match cursors with []=>True | cursor::rest=>
 cm_phase_budget policy p fid (cm_cursor_phase cursor) (cm_cursor_temp cursor) /\
 cm_cursors_budget policy p (cm_frame_parent_fid (cm_phase_frame (cm_cursor_phase cursor)) fid) rest end.
Definition cm_task_budget policy root task ann : Prop := match task with
 | CMStartTask _ _=>cm_cursors_budget policy root (-1) (cm_ann_cursors ann)
 | CMRTask _ fid e _ _=>0<=cm_ann_temp ann /\ cm_ann_temp ann+cm_rtemps e<=cm_temp_slots (cm_function_at policy fid (cm_program_functions root)) /\ cm_cursors_budget policy root fid (cm_ann_cursors ann)
 | CMLTask _ fid e _ _=>0<=cm_ann_temp ann /\ cm_ann_temp ann+cm_ltemps e<=cm_temp_slots (cm_function_at policy fid (cm_program_functions root)) /\ cm_cursors_budget policy root fid (cm_ann_cursors ann)
 | CMSTask _ fid s _ _=>0<=cm_ann_temp ann /\ cm_ann_temp ann+cm_stemps s<=cm_temp_slots (cm_function_at policy fid (cm_program_functions root)) /\ cm_cursors_budget policy root fid (cm_ann_cursors ann)
 | CMVTask _ fid _ _ _ | CMCTask _ fid _ _ _=>cm_cursors_budget policy root fid (cm_ann_cursors ann) | CMDoneTask _ _ _=>True end.
Lemma cm_task_budget_initial policy p input : cm_task_budget policy p (CMStartTask p input) cm_initial_annotation.
Proof. exact I. Qed.
Lemma cm_stemps_nonnegative stmt : 0<=cm_stemps stmt.
Proof. induction stmt; cbn [cm_stemps]; unfold cm_imax; try lia; match goal with |- context[cm_rtemps ?e]=>pose proof (cm_expr_temps_nonnegative__index_bounds e) end; lia. Qed.
Lemma cm_args_budget_cons a rest :
 cm_adepth (cm_args_apair (a::rest))=Z.max (cm_rtemps a) (cm_adepth (cm_args_apair rest)) /\
 0<=cm_adepth (cm_args_apair rest) /\ cm_acount (cm_args_apair (a::rest))=1+Zlength rest.
Proof. pose proof (cm_args_apair_count_depth__call_bounds rest); cbn [cm_args_apair cm_acount cm_adepth]; unfold cm_imax, cm_rtemps; intuition lia. Qed.
Ltac cm_budget_reduce := repeat progress (cm_ann_reduce;
 cbv beta iota zeta delta [cm_task_budget cm_cursors_budget cm_phase_budget cm_frame_parent_fid] in *).
Ltac cm_budget_cases := cm_budget_reduce;
 repeat match goal with |- context[if ?b then _ else _]=>cm_ann_bool b; cm_budget_reduce end.
Ltac cm_budget_arith :=
 repeat match goal with H:_ /\ _ |- _=>destruct H end;
 unfold cm_rtemps, cm_ltemps in *; repeat rewrite cm_expr_tpair_call in *; unfold cm_args_temps in *;
 cbn [cm_rtemps cm_ltemps cm_expr_tpair cm_tleft cm_tright cm_stemps cm_args_apair cm_acount cm_adepth] in *;
 unfold cm_imax, cm_ltemps, cm_rtemps in *;
 cbv beta iota delta [orb andb] in *;
 repeat match goal with H:?b=true |- _=>rewrite H in * | H:?b=false |- _=>rewrite H in * end;
 cbn [orb andb cm_tleft cm_tright] in *;
 repeat split; try assumption; try reflexivity; try lia.
Lemma cm_r_budget_step sp ap p fid expr st ann :
 cm_task_budget (cm_source_function_policy sp) p (CMRTask p fid expr st (cm_cursor_frames (cm_ann_cursors ann))) ann ->
 cm_task_budget (cm_source_function_policy sp) p (cm_rstart sp p fid expr st (cm_cursor_frames (cm_ann_cursors ann)))
 (cm_update_annotation (cm_update_r sp ap p fid st ann expr)).
Proof.
 destruct expr; try match goal with xs:list cm_expr |- _=>destruct xs end; intro H;
 cm_budget_cases; try cm_budget_arith.
 all: try match goal with |- context[match ?xs with []=>_ | _::_=>_ end]=>destruct xs; cm_budget_cases; try cm_budget_arith end.
 all: try (pose proof (cm_args_apair_count_depth__call_bounds args) as AD;
   pose proof (ListLib.General.Length.Zlength_nonneg args) as LEN;
   repeat rewrite Zlength_cons in *; cm_budget_arith).
 all: try (fold cm_args_apair in *; pose proof (cm_args_apair_count_depth__call_bounds args); cm_budget_arith).
 all: try (repeat match goal with H: context[if ?b then _ else _] |- _=>destruct b eqn:? end; cm_budget_arith).

Qed.
Lemma cm_l_budget_step sp ap p fid expr st ann :
 cm_task_budget (cm_source_function_policy sp) p (CMLTask p fid expr st (cm_cursor_frames (cm_ann_cursors ann))) ann ->
 cm_task_budget (cm_source_function_policy sp) p (cm_lstart sp p fid expr st (cm_cursor_frames (cm_ann_cursors ann)))
 (cm_update_annotation (cm_update_l sp ap p fid st ann expr)).
Proof. destruct expr; intro H; cm_budget_cases; cm_budget_arith. Qed.
Lemma cm_s_budget_step sp ap p fid stmt st ann :
 cm_task_budget (cm_source_function_policy sp) p (CMSTask p fid stmt st (cm_cursor_frames (cm_ann_cursors ann))) ann ->
 cm_task_budget (cm_source_function_policy sp) p (cm_sstart sp p fid stmt st (cm_cursor_frames (cm_ann_cursors ann)))
 (cm_update_annotation (cm_update_s sp ap p fid st ann stmt)).
Proof. destruct stmt; intro H; cm_budget_cases; cm_budget_arith. Qed.
Lemma cm_v_budget_step sp ap p fid v st phase pc temp b c pt pb pk rest spills saved calls :
 let ann:=CMAnnotation pc temp b c (CMACursor phase pt pb pk::rest) spills saved calls in
 cm_annotation_child_ready (cm_source_function_policy sp) p fid ann ->
 cm_task_succeeds sp (cm_vapply sp p fid (cm_phase_frame phase) v st (cm_cursor_frames rest)) ->
 cm_task_budget (cm_source_function_policy sp) p (CMVTask p fid v st (cm_cursor_frames (cm_ann_cursors ann))) ann ->
 cm_task_budget (cm_source_function_policy sp) p (cm_vapply sp p fid (cm_phase_frame phase) v st (cm_cursor_frames rest))
 (cm_update_annotation (cm_update_v sp ap p fid v st ann phase)).
Proof.
 cbn zeta; destruct phase; intros C S H; cm_budget_cases; try cm_budget_arith.
 all: try match goal with |- context[match ?xs with []=>_ | _::_=>_ end]=>destruct xs; cm_budget_cases; try cm_budget_arith end.
 all: try solve [exfalso; eapply cm_error_not_succeeds; exact S].
 all: cm_coord_reduce; try cm_budget_arith.
 all: pose proof (ListLib.General.Length.Zlength_nonneg rest0);
 pose proof (cm_args_apair_count_depth__call_bounds rest0); repeat rewrite Zlength_cons in *; cm_budget_arith.
Qed.
Lemma cm_c_budget_step sp ap p fid ctl st phase pc temp b c pt pb pk rest spills saved calls :
 let ann:=CMAnnotation pc temp b c (CMACursor phase pt pb pk::rest) spills saved calls in
 cm_task_budget (cm_source_function_policy sp) p (CMCTask p fid ctl st (cm_cursor_frames (cm_ann_cursors ann))) ann ->
 cm_task_budget (cm_source_function_policy sp) p (cm_capply sp p fid (cm_phase_frame phase) ctl st (cm_cursor_frames rest))
 (cm_update_annotation (cm_update_c sp ap p fid ctl st ann phase)).
Proof. cbn zeta; destruct ctl; destruct phase; intro H; cm_budget_cases; cm_budget_arith. Qed.
Lemma cm_task_budget_step_coordinate sp ap p task ann : cm_annotation_erases task ann ->
 cm_task_coordinate_ready (cm_source_function_policy sp) p task ann -> cm_task_succeeds sp task ->
 cm_task_budget (cm_source_function_policy sp) p task ann ->
 cm_task_budget (cm_source_function_policy sp) p (cm_step sp task) (cm_update_annotation (cm_annotation_step sp ap task ann)).
Proof.
 destruct task as [q input|q fid expr st ks|q fid expr st ks|q fid stmt st ks|q fid v st ks|q fid ctl st ks|st ctl status]; intros E C S H.
 - destruct C as [-> ->]. cbv beta iota zeta delta [cm_step cm_annotation_step cm_begin_call].
   destruct (cm_call_ok sp p (cm_program_main p) [] (cm_initial_state sp p input) && (cm_call_depth [CMHaltK] <? 65536)); cm_budget_reduce; cbn [cm_initial_annotation cm_ann_cursors]; unfold cm_temp_slots,cm_source_function_at; cm_budget_arith.
 - destruct C as [-> C]; cbn [cm_annotation_erases] in E; subst ks; now apply cm_r_budget_step.
 - destruct C as [-> C]; cbn [cm_annotation_erases] in E; subst ks; now apply cm_l_budget_step.
 - destruct C as [-> C]; cbn [cm_annotation_erases] in E; subst ks; now apply cm_s_budget_step.
 - destruct C as [-> C]; destruct ann as [pc temp b c cursors spills saved calls]; cbn [cm_annotation_erases cm_ann_cursors] in E; subst ks.
   destruct cursors as [|[phase pt pb pk] rest]; [exact I|]. apply cm_v_budget_step; [exact C|now apply cm_succeeds_step_total in S|exact H].
 - destruct C as [-> C]; destruct ann as [pc temp b c cursors spills saved calls]; cbn [cm_annotation_erases cm_ann_cursors] in E; subst ks.
   cbv beta iota zeta delta [cm_step cm_annotation_step cm_ann_cursors]. destruct (cm_control_kind ctl=?4); [exact I|].
   destruct cursors as [|[phase pt pb pk] rest]; [destruct (cm_control_kind ctl=?5); exact I|now apply cm_c_budget_step].
 - exact I.
Qed.
Lemma cm_annotated_iter_budget_coordinate sp ap p n ast :
 cm_task_succeeds sp (cm_astate_task ast) ->
 cm_annotation_erases (cm_astate_task ast) (cm_astate_annotation ast) /\ cm_annotation_rooted (cm_astate_annotation ast) ->
 cm_task_coordinate_ready (cm_source_function_policy sp) p (cm_astate_task ast) (cm_astate_annotation ast) ->
 cm_task_budget (cm_source_function_policy sp) p (cm_astate_task ast) (cm_astate_annotation ast) ->
 cm_task_budget (cm_source_function_policy sp) p (cm_astate_task (cm_annotated_iter sp ap n ast)) (cm_astate_annotation (cm_annotated_iter sp ap n ast)).
Proof.
 revert ast; induction n; intros ast S E C H; [exact H|]. apply IHn.
 - now apply cm_succeeds_step_total.
 - now apply cm_annotated_step_invariant.
 - apply cm_task_coordinate_step; [exact (proj1 E)|exact C].
 - eapply cm_task_budget_step_coordinate; eauto; exact (proj1 E).
Qed.
Theorem cm_source_termination_budget sp ap p input output status n : cm_source_terminates sp p input output status ->
 cm_task_budget (cm_source_function_policy sp) p (cm_astate_task (cm_annotated_iter sp ap n (cm_annotated_start (cm_source_function_policy sp) p input)))
 (cm_astate_annotation (cm_annotated_iter sp ap n (cm_annotated_start (cm_source_function_policy sp) p input))).
Proof.
 intro TERM; eapply cm_annotated_iter_budget_coordinate; [ | |apply cm_task_coordinate_initial|apply cm_task_budget_initial].
 - unfold cm_source_terminates in TERM; destruct TERM as [_ [_ [st [ctl [E [S OUT]]]]]]. exists st,ctl,status; now split.
 - split; [apply cm_annotated_start_erases|apply cm_annotated_start_rooted].
Qed.
