Require Export SimpleC.EE.QCP_demos_human.cmc_statement_control_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_succeeds_control_not_error sp p fid ctl st ks : cm_task_succeeds sp (CMCTask p fid ctl st ks) -> cm_control_kind ctl<>5.
Proof. destruct ctl; cbn [cm_control_kind]; intro S; try discriminate; cm_ready_error. Qed.
Lemma cm_c_code_ready_coordinate policy p fid ann phase owner ob oc rest :
 cm_ann_cursors ann=CMACursor phase owner ob oc::rest -> cm_annotation_child_ready policy p fid ann ->
 cm_c_code_ready policy p fid ann phase.
Proof.
 intros CUR C guard body env regions start finish EQ; subst phase.
 unfold cm_annotation_child_ready in C; rewrite CUR in C; cbn [cm_cursors_coordinate cm_cursor_phase cm_cursor_temp cm_phase_code_ready_at] in C.
 exact (proj1 (proj2 (proj2 C))).
Qed.
Lemma cm_c_phase_ready_support sp ap p fid ctl st phase owner ob oc rest ann :
 cm_ann_cursors ann=CMACursor phase owner ob oc::rest ->
 cm_task_succeeds sp (CMCTask p fid ctl st (cm_cursor_frames (cm_ann_cursors ann))) ->
 cm_annotation_rooted ann -> cm_annotation_child_ready (cm_source_function_policy sp) p fid ann ->
 cm_task_context_ready (CMCTask p fid ctl st (cm_cursor_frames (cm_ann_cursors ann))) ann ->
 cm_task_statement_control (CMCTask p fid ctl st (cm_cursor_frames (cm_ann_cursors ann))) ann ->
 cm_c_phase_ready ap ctl ann phase.
Proof.
 intros CUR S ROOT C X H; pose proof (cm_succeeds_control_not_error _ _ _ _ _ _ S) as NE.
 destruct ann as [pc temp b c cursors spills saved calls]; cbn [cm_ann_cursors] in CUR; subst cursors.
 destruct ctl; destruct phase; cbn [cm_control_kind] in NE; try contradiction;
 unfold cm_c_phase_ready,cm_c_regular_ready;
 cbn [cm_task_statement_control cm_control_kind cm_annotation_rooted] in H,ROOT;
 cm_coord_reduce; cm_context_reduce; try cm_sc_finish.
Qed.
