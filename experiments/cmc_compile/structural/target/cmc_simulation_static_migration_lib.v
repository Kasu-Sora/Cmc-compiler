Require Export SimpleC.EE.QCP_demos_human.cmc_simulation_support_invariants_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
(* Exact static predicates from cmc_preservation_generation_task.c. The
   total function lookup policy is inherited unchanged from the source model. *)
Fixpoint cm_expr_static_valid p f e : Prop := match e with
 | CMConstE _ _ | CMSizeofE _ _ | CMGetcE _=>True
 | CMStringE sid _=>0<=sid<Zlength (cm_program_strings p)
 | CMVarE scope slot _=>cm_binding_valid p f scope slot
 | CMAssignE a b _ | CMBinaryE _ a b _ | CMIndexE a b _=>cm_expr_static_valid p f a /\ cm_expr_static_valid p f b
 | CMUnaryE _ a _ | CMMemberE a _ _ | CMPutcE a _ | CMPutiE a _ | CMExitE a _=>cm_expr_static_valid p f a
 | CMCallE callee args _=>0<=callee<Zlength (cm_program_functions p) /\
   (fix all (xs:list cm_expr) : Prop := match xs with []=>True | a::rest=>cm_expr_static_valid p f a /\ all rest end) args end.
Fixpoint cm_args_static_valid p f args : Prop := match args with []=>True | a::rest=>cm_expr_static_valid p f a /\ cm_args_static_valid p f rest end.
Fixpoint cm_stmt_static_valid p f stmt : Prop := match stmt with
 | CMExprS e | CMInitS _ e | CMReturnS e=>cm_expr_static_valid p f e
 | CMSeqS a b=>cm_stmt_static_valid p f a /\ cm_stmt_static_valid p f b
 | CMBlockS a=>cm_stmt_static_valid p f a
 | CMIfS e a b=>cm_expr_static_valid p f e /\ cm_stmt_static_valid p f a /\ cm_stmt_static_valid p f b
 | CMWhileS e a=>cm_expr_static_valid p f e /\ cm_stmt_static_valid p f a | _=>True end.
Definition cm_frame_static_valid policy p fid frame : Prop := let f:=cm_function_at policy fid (cm_program_functions p) in match frame with
 | CMAssignLK e _ | CMBinLK _ e _ | CMIndexLK e _=>cm_expr_static_valid p f e
 | CMSeqK s=>cm_stmt_static_valid p f s
 | CMIfK a b=>cm_stmt_static_valid p f a /\ cm_stmt_static_valid p f b
 | CMWhileGuardK e s | CMWhileBodyK e s _ _=>cm_expr_static_valid p f e /\ cm_stmt_static_valid p f s
 | CMArgK callee args _ _=>0<=callee<Zlength (cm_program_functions p) /\ cm_args_static_valid p f args | _=>True end.
Fixpoint cm_frames_static_valid policy p fid frames : Prop := match frames with []=>True | frame::rest=>
 cm_frame_static_valid policy p fid frame /\ cm_frames_static_valid policy p (cm_frame_parent_fid frame fid) rest end.
Definition cm_task_static_valid policy task : Prop := match task with
 | CMRTask p fid e _ ks | CMLTask p fid e _ ks=>cm_expr_static_valid p (cm_function_at policy fid (cm_program_functions p)) e /\ cm_frames_static_valid policy p fid ks
 | CMSTask p fid s _ ks=>cm_stmt_static_valid p (cm_function_at policy fid (cm_program_functions p)) s /\ cm_frames_static_valid policy p fid ks
 | CMVTask p fid _ _ ks | CMCTask p fid _ _ ks=>cm_frames_static_valid policy p fid ks | _=>True end.
Lemma cm_expr_wf_static_valid : forall policy p f e, cm_expr_wf policy p f e -> cm_expr_static_valid p f e.
Proof.
 fix IH 4; intros policy p f e; destruct e; cbn [cm_expr_wf cm_expr_static_valid]; intro H; try solve [intuition eauto].
 destruct H as [B [H T]]; split; [exact B|].
 revert H; generalize (cm_function_params (cm_function_at policy fid (cm_program_functions p))).
 induction args as [|a rest IHr]; intros slots H; destruct slots; cbn in *; try contradiction; auto.
 destruct H as [Ha [_ Hrest]]; split; [exact (IH policy p f a Ha)|now apply (IHr slots)].
Qed.
Lemma cm_stmt_wf_static_valid policy p f loop stmt : cm_stmt_wf policy p f loop stmt -> cm_stmt_static_valid p f stmt.
Proof. revert loop; induction stmt; intros loop H; cbn in *; intuition eauto using cm_expr_wf_static_valid. Qed.
Lemma cm_typed_body_static_valid sp p fid : cm_typed_program (cm_source_function_policy sp) p -> 0<=fid<Zlength (cm_program_functions p) ->
 cm_stmt_static_valid p (cm_source_function_at sp fid p) (cm_function_body (cm_source_function_at sp fid p)).
Proof. intros [_ [_ [_ [WF _]]]] B; specialize (WF fid B); destruct WF as [_ [_ [_ [H _]]]]. eapply cm_stmt_wf_static_valid; exact H. Qed.
Lemma cm_expr_static_call p f callee args ty : cm_expr_static_valid p f (CMCallE callee args ty) <->
 0<=callee<Zlength (cm_program_functions p) /\ cm_args_static_valid p f args.
Proof. cbn [cm_expr_static_valid]; induction args; cbn; tauto. Qed.
Ltac cm_static_reduce := repeat progress (cm_ann_reduce;
 cbv beta iota zeta delta [cm_task_static_valid cm_frames_static_valid cm_frame_static_valid cm_frame_parent_fid cm_expr_static_valid cm_stmt_static_valid cm_args_static_valid cm_control_kind] in *).
Ltac cm_static_cases := cm_static_reduce;
 repeat match goal with |- context[if ?b then _ else _]=>cm_ann_bool b; cm_static_reduce end.
Ltac cm_static_finish := repeat match goal with H:_ /\ _ |- _=>destruct H end; repeat split; try assumption; try reflexivity; try lia.
Ltac cm_static_call_body :=
 match goal with H:(if cm_call_ok ?sp ?p ?fid ?vs ?st then ?b else false)=true |- _=>
 apply andb_true_iff in H; destruct H as [H D]; apply cm_call_ok_fid_bounds in H;
 match goal with WF:cm_typed_program (cm_source_function_policy sp) p |- _=>
 pose proof (cm_typed_body_static_valid sp p fid WF H) as BODY end end;
 cm_static_finish.
Lemma cm_r_static_step sp p fid expr st ks : cm_typed_program (cm_source_function_policy sp) p ->
 cm_task_static_valid (cm_source_function_policy sp) (CMRTask p fid expr st ks) ->
 cm_task_static_valid (cm_source_function_policy sp) (cm_rstart sp p fid expr st ks).
Proof.
 intros WF; destruct expr; try match goal with xs:list cm_expr |- _=>destruct xs end; intro H; cbn [cm_task_static_valid] in H;
 try match type of H with cm_expr_static_valid _ _ (CMCallE _ _ _) /\ _=>rewrite cm_expr_static_call in H end;
 cm_static_cases; try cm_static_finish.
 all: try match goal with |- context[match ?xs with []=>_ | _::_=>_ end]=>destruct xs; cm_static_cases; try cm_static_finish end.
 all: cm_static_call_body.
Qed.
Lemma cm_l_static_step sp p fid expr st ks :
 cm_task_static_valid (cm_source_function_policy sp) (CMLTask p fid expr st ks) ->
 cm_task_static_valid (cm_source_function_policy sp) (cm_lstart sp p fid expr st ks).
Proof. destruct expr; intro H; cm_static_cases; cm_static_finish. Qed.
Lemma cm_s_static_step sp p fid stmt st ks :
 cm_task_static_valid (cm_source_function_policy sp) (CMSTask p fid stmt st ks) ->
 cm_task_static_valid (cm_source_function_policy sp) (cm_sstart sp p fid stmt st ks).
Proof. destruct stmt; intro H; cm_static_cases; cm_static_finish. Qed.
Lemma cm_v_static_step sp p fid frame v st ks : cm_typed_program (cm_source_function_policy sp) p ->
 cm_task_succeeds sp (cm_vapply sp p fid frame v st ks) ->
 cm_frames_static_valid (cm_source_function_policy sp) p fid (frame::ks) ->
 cm_task_static_valid (cm_source_function_policy sp) (cm_vapply sp p fid frame v st ks).
Proof.
 destruct frame; intros WF S H; cm_static_cases; try cm_static_finish.
 all: try match goal with |- context[match ?xs with []=>_ | _::_=>_ end]=>destruct xs; cm_static_cases; try cm_static_finish end.
 all: try solve [exfalso; eapply cm_error_not_succeeds; exact S].
 all: cm_static_call_body.
Qed.
Lemma cm_c_static_step sp p fid frame ctl st ks :
 cm_frames_static_valid (cm_source_function_policy sp) p fid (frame::ks) ->
 cm_task_static_valid (cm_source_function_policy sp) (cm_capply sp p fid frame ctl st ks).
Proof. destruct frame; intro H; cm_static_cases; cm_static_finish. Qed.
Lemma cm_task_static_step_coordinate sp p task ann : cm_typed_program (cm_source_function_policy sp) p ->
 cm_task_coordinate_ready (cm_source_function_policy sp) p task ann -> cm_task_succeeds sp task ->
 cm_task_static_valid (cm_source_function_policy sp) task -> cm_task_static_valid (cm_source_function_policy sp) (cm_step sp task).
Proof.
 intros WF; destruct task as [q input|q fid expr st ks|q fid expr st ks|q fid stmt st ks|q fid v st ks|q fid ctl st ks|st ctl status]; intros C S H.
 - destruct C as [-> C]. cbv beta iota zeta delta [cm_step cm_begin_call].
   destruct (cm_call_ok sp p (cm_program_main p) [] (cm_initial_state sp p input) && (cm_call_depth [CMHaltK] <? 65536)) eqn:Call; cm_static_reduce; try cm_static_finish.
   apply andb_true_iff in Call; destruct Call as [Call _]. apply cm_call_ok_fid_bounds in Call.
   now apply cm_typed_body_static_valid.
 - destruct C as [-> C]; now apply cm_r_static_step.
 - destruct C as [-> C]; now apply cm_l_static_step.
 - destruct C as [-> C]; now apply cm_s_static_step.
 - destruct C as [-> C]; destruct ks as [|frame rest]; [exact I|].
   apply cm_v_static_step; [exact WF|now apply cm_succeeds_step_total in S|exact H].
 - destruct C as [-> C]; cbv beta iota zeta delta [cm_step]. destruct (cm_control_kind ctl=?4); [exact I|].
   destruct ks as [|frame rest]; [destruct (cm_control_kind ctl=?5); exact I|now apply cm_c_static_step].
 - exact I.
Qed.
Lemma cm_annotated_iter_static_coordinate sp ap p n ast : cm_typed_program (cm_source_function_policy sp) p ->
 cm_task_succeeds sp (cm_astate_task ast) ->
 cm_annotation_erases (cm_astate_task ast) (cm_astate_annotation ast) /\ cm_annotation_rooted (cm_astate_annotation ast) ->
 cm_task_coordinate_ready (cm_source_function_policy sp) p (cm_astate_task ast) (cm_astate_annotation ast) ->
 cm_task_static_valid (cm_source_function_policy sp) (cm_astate_task ast) ->
 cm_task_static_valid (cm_source_function_policy sp) (cm_astate_task (cm_annotated_iter sp ap n ast)).
Proof.
 intros WF; revert ast; induction n; intros ast S E C H; [exact H|]. apply IHn.
 - now apply cm_succeeds_step_total.
 - now apply cm_annotated_step_invariant.
 - apply cm_task_coordinate_step; [exact (proj1 E)|exact C].
 - eapply cm_task_static_step_coordinate; eauto.
Qed.
Theorem cm_source_termination_static_valid sp ap p input output status n :
 cm_semantic_wf_program (cm_source_function_policy sp) p -> cm_source_terminates sp p input output status ->
 cm_task_static_valid (cm_source_function_policy sp) (cm_astate_task (cm_annotated_iter sp ap n (cm_annotated_start (cm_source_function_policy sp) p input))).
Proof.
 intros [WF _] TERM; eapply cm_annotated_iter_static_coordinate; [exact WF| | |apply cm_task_coordinate_initial|exact I].
 - unfold cm_source_terminates in TERM; destruct TERM as [_ [_ [st [ctl [E [S OUT]]]]]]. exists st,ctl,status; now split.
 - split; [apply cm_annotated_start_erases|apply cm_annotated_start_rooted].
Qed.
