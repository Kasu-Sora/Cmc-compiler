Require Export SimpleC.EE.QCP_demos_human.cmc_simulation_spill_update_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
(* cmc_preservation_ready_context.c, preserving all scope barriers. *)
Definition cm_phase_accepts_statement phase := match phase with
 | CABlockP _ _ _ _ | CASeqP _ | CAWhileBodyP _ _ _ _ _ _ | CACallP _ _ _ _ _=>true | _=>false end.
Definition cm_phase_requires_statement_parent phase := match phase with
 | CAExprStmtP | CAInitP _ | CABlockP _ _ _ _ | CASeqP _ | CAIfP _ _ | CAWhileGuardP _ _ _ _ | CAWhileBodyP _ _ _ _ _ _ | CAReturnP=>true | _=>false end.
Definition cm_phase_control_scope phase : Z := match phase with
 | CAHaltP=>3 | CAWhileBodyP _ _ _ _ _ _=>1 | CACallP _ _ _ _ _=>2 | _=>0 end.
Fixpoint cm_cursors_loop_ready cursors := match cursors with []=>false | cursor::rest=>
 if cm_phase_control_scope (cm_cursor_phase cursor)=?1 then true else
 if (cm_phase_control_scope (cm_cursor_phase cursor)=?2)||(cm_phase_control_scope (cm_cursor_phase cursor)=?3) then false else cm_cursors_loop_ready rest end.
Fixpoint cm_cursors_call_ready cursors := match cursors with []=>false | cursor::rest=>
 if cm_phase_control_scope (cm_cursor_phase cursor)=?2 then true else
 if cm_phase_control_scope (cm_cursor_phase cursor)=?3 then false else cm_cursors_call_ready rest end.
Definition cm_stmt_context_ready stmt cursors : Prop := match stmt with
 | CMBreakS | CMContinueS=>cm_cursors_loop_ready cursors=true
 | CMReturnS _=>cm_cursors_call_ready cursors=true | _=>True end.
Fixpoint cm_stmt_scope_ready loop call stmt : Prop := match stmt with
 | CMSeqS a b | CMIfS _ a b=>cm_stmt_scope_ready loop call a /\ cm_stmt_scope_ready loop call b
 | CMBlockS a=>cm_stmt_scope_ready loop call a | CMWhileS _ body=>cm_stmt_scope_ready true call body
 | CMBreakS | CMContinueS=>loop=true | CMReturnS _=>call=true | _=>True end.
Definition cm_phase_scope_ready phase rest : Prop := match phase with
 | CASeqP second=>cm_stmt_scope_ready (cm_cursors_loop_ready rest) (cm_cursors_call_ready rest) second
 | CAIfP yes no=>cm_stmt_scope_ready (cm_cursors_loop_ready rest) (cm_cursors_call_ready rest) yes /\ cm_stmt_scope_ready (cm_cursors_loop_ready rest) (cm_cursors_call_ready rest) no
 | CAWhileGuardP _ body _ _ | CAWhileBodyP _ body _ _ _ _=>cm_stmt_scope_ready true (cm_cursors_call_ready rest) body | _=>True end.
Fixpoint cm_cursors_scope_ready cursors : Prop := match cursors with []=>True | cursor::rest=>
 cm_cursors_scope_ready rest /\ cm_phase_scope_ready (cm_cursor_phase cursor) rest end.
Definition cm_control_context_ready ctl cursors : Prop :=
 if (cm_control_kind ctl=?1)||(cm_control_kind ctl=?2) then cm_cursors_loop_ready cursors=true else
 if cm_control_kind ctl=?3 then cm_cursors_call_ready cursors=true else True.
Definition cm_statement_cursors_ready cursors := match cursors with []=>false | cursor::_=>cm_phase_accepts_statement (cm_cursor_phase cursor) end.
Fixpoint cm_cursors_context_ready cursors : Prop := match cursors with []=>True | cursor::rest=>
 cm_cursors_context_ready rest /\ (cm_cursor_phase cursor=CAHaltP -> rest=[]) /\
 (cm_phase_requires_statement_parent (cm_cursor_phase cursor)=true -> cm_statement_cursors_ready rest=true) /\
 (cm_cursor_phase cursor=CAReturnP -> cm_cursors_call_ready rest=true) end.
Definition cm_task_context_ready task ann : Prop :=
 cm_cursors_context_ready (cm_ann_cursors ann) /\ cm_cursors_scope_ready (cm_ann_cursors ann) /\
 match task with
 | CMSTask _ _ stmt _ _=>cm_statement_cursors_ready (cm_ann_cursors ann)=true /\
   cm_stmt_context_ready stmt (cm_ann_cursors ann) /\
   cm_stmt_scope_ready (cm_cursors_loop_ready (cm_ann_cursors ann)) (cm_cursors_call_ready (cm_ann_cursors ann)) stmt
 | CMCTask _ _ ctl _ _=>cm_control_context_ready ctl (cm_ann_cursors ann) | _=>True end.
Lemma cm_task_context_initial p input : cm_task_context_ready (CMStartTask p input) cm_initial_annotation.
Proof. repeat split. Qed.
Lemma cm_stmt_scope_context_ready stmt cursors :
 cm_stmt_scope_ready (cm_cursors_loop_ready cursors) (cm_cursors_call_ready cursors) stmt -> cm_stmt_context_ready stmt cursors.
Proof. destruct stmt; cbn; tauto. Qed.
Lemma cm_stmt_wf_scope_ready policy p fn loop stmt : cm_stmt_wf policy p fn loop stmt -> cm_stmt_scope_ready loop true stmt.
Proof. revert loop; induction stmt; intros loop H; cbn in *; intuition eauto. Qed.
Lemma cm_typed_body_scope_ready sp p fid : cm_typed_program (cm_source_function_policy sp) p -> 0<=fid<Zlength (cm_program_functions p) ->
 cm_stmt_scope_ready false true (cm_function_body (cm_source_function_at sp fid p)).
Proof.
 intros [_ [_ [_ [WF _]]]] B; specialize (WF fid B); destruct WF as [_ [_ [_ [H _]]]].
 now apply (cm_stmt_wf_scope_ready (cm_source_function_policy sp) p (cm_source_function_at sp fid p)).
Qed.
Lemma cm_call_ok_scope_ready sp p fid values st : cm_typed_program (cm_source_function_policy sp) p -> cm_call_ok sp p fid values st=true ->
 cm_stmt_scope_ready false true (cm_function_body (cm_source_function_at sp fid p)).
Proof.
 intros WF H; apply cm_typed_body_scope_ready; [exact WF|]. unfold cm_call_ok in H.
 repeat rewrite andb_true_iff in H; repeat match goal with H:_ /\ _ |- _=>destruct H end.
 split; [now apply Z.leb_le|now apply Z.ltb_lt].
Qed.
