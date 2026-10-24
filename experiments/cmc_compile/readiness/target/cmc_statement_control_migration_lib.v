Require Export SimpleC.EE.QCP_demos_human.cmc_layout_readiness_leaf_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Ltac cm_sc_reduce := repeat progress (cm_context_reduce; cbv beta iota zeta delta [cm_task_statement_control] in *).
Ltac cm_sc_cases := cm_sc_reduce; repeat match goal with |- context[if ?b then _ else _]=>destruct b eqn:?; cm_sc_reduce end.
Ltac cm_sc_finish := repeat match goal with H:_ /\ _|-_=>destruct H end;
 repeat match goal with H:true=true -> _|-_=>specialize (H eq_refl) end; try solve [timeout 1 intuition discriminate].
Lemma cm_r_statement_control sp ap p fid expr st ann :
 cm_task_statement_control (cm_rstart sp p fid expr st (cm_cursor_frames (cm_ann_cursors ann))) (cm_update_annotation (cm_update_r sp ap p fid st ann expr)).
Proof.
 destruct expr; cm_sc_cases; try cm_sc_finish.
 all: match goal with |-context[match ?xs with []=>_ | _::_=>_ end]=>destruct xs; cm_sc_cases; cm_sc_finish end.
Qed.
Lemma cm_l_statement_control sp ap p fid expr st ann :
 cm_task_statement_control (cm_lstart sp p fid expr st (cm_cursor_frames (cm_ann_cursors ann))) (cm_update_annotation (cm_update_l sp ap p fid st ann expr)).
Proof. destruct expr; cm_sc_cases; cm_sc_finish. Qed.
Lemma cm_s_statement_control sp ap p fid stmt st ann :
 cm_task_context_ready (CMSTask p fid stmt st (cm_cursor_frames (cm_ann_cursors ann))) ann ->
 cm_task_statement_control (cm_sstart sp p fid stmt st (cm_cursor_frames (cm_ann_cursors ann))) (cm_update_annotation (cm_update_s sp ap p fid st ann stmt)).
Proof. destruct stmt; intro X; cm_sc_cases; cm_sc_finish. Qed.
Lemma cm_v_statement_control sp ap p fid v st phase pc temp b c pt pb pk rest spills saved calls :
 let ann:=CMAnnotation pc temp b c (CMACursor phase pt pb pk::rest) spills saved calls in
 cm_task_context_ready (CMVTask p fid v st (cm_cursor_frames (cm_ann_cursors ann))) ann ->
 cm_task_statement_control (cm_vapply sp p fid (cm_phase_frame phase) v st (cm_cursor_frames rest))
 (cm_update_annotation (cm_update_v sp ap p fid v st ann phase)).
Proof.
 cbn zeta; destruct phase; intro X.
 all: cm_sc_cases.
 all: try cm_sc_finish.
 all: match goal with |-context[match ?xs with []=>_ | _::_=>_ end]=>destruct xs; cm_sc_cases; cm_sc_finish end.
Qed.
Lemma cm_c_statement_control sp ap p fid ctl st phase pc temp b c pt pb pk rest spills saved calls :
 let ann:=CMAnnotation pc temp b c (CMACursor phase pt pb pk::rest) spills saved calls in
 cm_task_context_ready (CMCTask p fid ctl st (cm_cursor_frames (cm_ann_cursors ann))) ann ->
 cm_task_statement_control (CMCTask p fid ctl st (cm_cursor_frames (cm_ann_cursors ann))) ann ->
 cm_task_statement_control (cm_capply sp p fid (cm_phase_frame phase) ctl st (cm_cursor_frames rest))
 (cm_update_annotation (cm_update_c sp ap p fid ctl st ann phase)).
Proof. cbn zeta; destruct ctl; destruct phase; intros X H; cm_sc_cases; cm_sc_finish. Qed.
Lemma cm_task_statement_control_step sp ap p task ann :
 cm_annotation_erases task ann -> cm_task_coordinate_ready (cm_source_function_policy sp) p task ann ->
 cm_task_context_ready task ann -> cm_task_statement_control task ann ->
 cm_task_statement_control (cm_step sp task) (cm_update_annotation (cm_annotation_step sp ap task ann)).
Proof.
 destruct task as [q input|q fid expr st ks|q fid expr st ks|q fid stmt st ks|q fid v st ks|q fid ctl st ks|st ctl status]; intros E C X H.
 - cbv beta iota zeta delta [cm_step cm_annotation_step cm_begin_call]; cm_sc_cases; cm_sc_finish.
 - destruct C as [-> C]; cbn [cm_annotation_erases] in E; subst ks; apply cm_r_statement_control.
 - destruct C as [-> C]; cbn [cm_annotation_erases] in E; subst ks; apply cm_l_statement_control.
 - destruct C as [-> C]; cbn [cm_annotation_erases] in E; subst ks; now apply cm_s_statement_control.
 - destruct C as [-> C]; destruct ann as [pc temp b c cursors spills saved calls]; cbn [cm_annotation_erases cm_ann_cursors] in E; subst ks.
   destruct cursors as [|[phase pt pb pk] rest]; [exact I|now apply cm_v_statement_control].
 - destruct C as [-> C]; destruct ann as [pc temp b c cursors spills saved calls]; cbn [cm_annotation_erases cm_ann_cursors] in E; subst ks.
   cbv beta iota zeta delta [cm_step cm_annotation_step cm_ann_cursors]. destruct (cm_control_kind ctl=?4); [exact I|].
   destruct cursors as [|[phase pt pb pk] rest]; [destruct (cm_control_kind ctl=?5); exact I|now apply cm_c_statement_control].
 - exact I.
Qed.
