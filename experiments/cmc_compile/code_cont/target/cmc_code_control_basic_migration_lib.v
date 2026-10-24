Require Export SimpleC.EE.QCP_demos_human.cmc_code_value_helpers_migration_lib.
From Coq Require Import ZArith List Bool Lia.
From AUXLib Require Import ListLib.
Import ListNotations.
Local Open Scope Z_scope.
Ltac cm_code_control_reduce := cbv beta iota zeta delta [cm_task_layout cm_task_code cm_task_fid cm_capply cm_phase_frame cm_update_c cm_update_annotation cm_ann_pop cm_ann_replace cm_ann_leave_call cm_ann_pc cm_ann_temp cm_ann_break cm_ann_continue cm_ann_cursors cm_ann_spills cm_ann_saved cm_ann_calls cm_cursor_phase cm_cursor_temp cm_cursor_break cm_cursor_continue hd tl] in *; rewrite ?cm_normal_control_code in *; cbn [cm_control_phase_code cm_control_kind Z.eqb Pos.eqb cm_cont_code cm_normal_cont_code cm_cursor_code cm_cursor_phase cm_cursor_temp cm_cursor_break cm_cursor_continue cm_value_phase_code cm_normal_phase_code cm_phase_stops cm_normal_phase_stops cm_phase_yields_normal cm_saved_layout cm_phase_site cm_phase_is_call orb andb] in *.
Lemma cm_c_block_layout_step sp ap p fid ctl st env regions jump target pc temp b c owner ob oc tail spills saved calls :
 let ann:=CMAnnotation pc temp b c (CMACursor (CABlockP env regions jump target) owner ob oc::tail) spills saved calls in
 cm_control_kind ctl<>4 -> cm_c_regular_ready ap ctl ann -> cm_task_layout sp ap p (CMCTask p fid ctl st (cm_cursor_frames(cm_ann_cursors ann))) ann ->
 cm_task_layout sp ap p (cm_capply sp p fid (CMBlockK env regions) ctl st (cm_cursor_frames tail)) (cm_update_annotation(cm_update_c sp ap p fid ctl st ann (CABlockP env regions jump target))).
Proof.
 cbn zeta; intros NE [ERR [BR CONT]] [CODE [SITE SAVED]]; destruct ctl; cbn[cm_control_kind]in *; try contradiction.
 - destruct jump; cm_code_control_reduce; split; try exact SAVED.
   + destruct SITE as [BAD|SITE]; [discriminate|exact SITE].
   + rewrite Z.add_0_r in CODE; exact CODE.
 - specialize(BR eq_refl); cbn[cm_ann_break cm_ann_cursors hd cm_cursor_break]in BR; subst b; cm_code_control_reduce; split; assumption.
 - specialize(CONT eq_refl); cbn[cm_ann_continue cm_ann_cursors hd cm_cursor_continue]in CONT; subst c; cm_code_control_reduce; split; assumption.
 - cm_code_control_reduce; split; assumption.
Qed.
Lemma cm_c_seq_layout_step sp ap p fid ctl st second pc temp b c owner ob oc tail spills saved calls :
 let ann:=CMAnnotation pc temp b c (CMACursor (CASeqP second) owner ob oc::tail) spills saved calls in
 cm_control_kind ctl<>4 -> cm_c_regular_ready ap ctl ann -> cm_task_layout sp ap p (CMCTask p fid ctl st (cm_cursor_frames(cm_ann_cursors ann))) ann ->
 cm_task_layout sp ap p (cm_capply sp p fid (CMSeqK second) ctl st (cm_cursor_frames tail)) (cm_update_annotation(cm_update_c sp ap p fid ctl st ann (CASeqP second))).
Proof.
 cbn zeta; intros NE [ERR [BR CONT]] [CODE [_ SAVED]]; destruct ctl; cbn[cm_control_kind]in *; try contradiction.
 - cm_code_control_reduce; split; [|exact SAVED]. rewrite cm_emit_stmt_length__stmt_capacity in CODE; exact CODE.
 - specialize(BR eq_refl); cbn[cm_ann_break cm_ann_cursors hd cm_cursor_break]in BR; subst b; cm_code_control_reduce; split; assumption.
 - specialize(CONT eq_refl); cbn[cm_ann_continue cm_ann_cursors hd cm_cursor_continue]in CONT; subst c; cm_code_control_reduce; split; assumption.
 - cm_code_control_reduce; split; assumption.
Qed.
