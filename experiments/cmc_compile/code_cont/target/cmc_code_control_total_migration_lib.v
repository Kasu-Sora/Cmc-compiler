Require Export SimpleC.EE.QCP_demos_human.cmc_code_control_loop_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_c_phase_layout_step sp ap p fid ctl st phase pc temp b c owner ob oc tail spills saved calls :
 let ann:=CMAnnotation pc temp b c (CMACursor phase owner ob oc::tail) spills saved calls in
 cm_control_kind ctl<>4 -> cm_c_phase_ready ap ctl ann phase -> cm_c_code_ready (cm_source_function_policy sp) p fid ann phase ->
 cm_task_layout sp ap p (CMCTask p fid ctl st (cm_cursor_frames(cm_ann_cursors ann))) ann ->
 cm_task_layout sp ap p (cm_capply sp p fid (cm_phase_frame phase) ctl st (cm_cursor_frames tail)) (cm_update_annotation(cm_update_c sp ap p fid ctl st ann phase)).
Proof.
 cbn zeta; intros NE READY CODE LAYOUT; destruct phase; cbn [cm_c_phase_ready] in READY; try tauto.
 - eapply cm_c_block_layout_step; eauto.
 - eapply cm_c_seq_layout_step; eauto.
 - unfold cm_c_code_ready in CODE; specialize(CODE _ _ _ _ _ _ eq_refl); destruct CODE as [_ [_ END]]; eapply cm_c_while_layout_step; eauto.
 - eapply cm_c_call_layout_step; [tauto|exact LAYOUT].
Qed.
Lemma cm_c_task_layout_step sp ap p fid ctl st ks ann :
 cm_annotation_erases (CMCTask p fid ctl st ks) ann -> cm_c_layout_ready (cm_source_function_policy sp) ap p fid ctl ann ->
 cm_task_layout sp ap p (CMCTask p fid ctl st ks) ann ->
 cm_task_layout sp ap p (cm_step sp (CMCTask p fid ctl st ks)) (cm_update_annotation(cm_annotation_step sp ap (CMCTask p fid ctl st ks) ann)).
Proof.
 destruct ann as [pc temp b c cursors spills saved calls]; cbn [cm_annotation_erases cm_ann_cursors]; intros ER READY LAYOUT; subst ks.
 unfold cm_step,cm_annotation_step; destruct(cm_control_kind ctl=?4)eqn:EXIT; [exact I|].
 apply Z.eqb_neq in EXIT; destruct cursors as [|[phase owner ob oc] tail]; [destruct(cm_control_kind ctl=?5); exact I|].
 cbn [cm_c_layout_ready cm_ann_cursors hd cm_cursor_phase] in READY; destruct READY as [[NO _]|[_ [PHASE CODE]]]; [discriminate|].
 change (cm_task_layout sp ap p (cm_capply sp p fid (cm_phase_frame phase) ctl st (cm_cursor_frames tail)) (cm_update_annotation(cm_update_c sp ap p fid ctl st (CMAnnotation pc temp b c (CMACursor phase owner ob oc::tail) spills saved calls) phase))).
 eapply cm_c_phase_layout_step; eauto.
Qed.
