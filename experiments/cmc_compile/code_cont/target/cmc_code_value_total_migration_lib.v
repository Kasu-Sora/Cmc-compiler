Require Export SimpleC.EE.QCP_demos_human.cmc_code_value_linear_migration_lib.
Require Export SimpleC.EE.QCP_demos_human.cmc_code_value_flow_migration_lib.
Require Export SimpleC.EE.QCP_demos_human.cmc_code_value_binary_migration_lib.
Require Export SimpleC.EE.QCP_demos_human.cmc_code_value_call_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_v_phase_layout_step sp ap p fid v st phase pc temp b c owner ob oc tail spills saved calls :
 let ann:=CMAnnotation pc temp b c (CMACursor phase owner ob oc::tail) spills saved calls in
 cm_v_temp_ready ap ann phase -> cm_v_phase_ready sp p v st ann phase ->
 cm_task_layout sp ap p (CMVTask p fid v st (cm_cursor_frames(cm_ann_cursors ann))) ann ->
 cm_task_layout sp ap p (cm_vapply sp p fid (cm_phase_frame phase) v st (cm_cursor_frames tail)) (cm_update_annotation(cm_update_v sp ap p fid v st ann phase)).
Proof.
 cbn zeta; intros TEMP READY LAYOUT; destruct phase; cbn [cm_v_phase_ready cm_ann_cursors tl] in READY; try contradiction;
 cbn [cm_v_temp_ready cm_ann_temp cm_ann_cursors hd cm_cursor_temp cm_phase_child_temp] in TEMP;
 try solve[eapply cm_v_load_layout_step; eauto|eapply cm_v_assign_l_layout_step; eauto|eapply cm_v_assign_r_layout_step; eauto|eapply cm_v_unary_layout_step; eauto|eapply cm_v_binary_l_layout_step; eauto|eapply cm_v_binary_r_layout_step; eauto|eapply cm_v_index_l_layout_step; eauto|eapply cm_v_index_r_layout_step; eauto|eapply cm_v_member_layout_step; eauto|eapply cm_v_putc_layout_step; eauto|eapply cm_v_puti_layout_step; eauto|eapply cm_v_exit_layout_step; eauto|eapply cm_v_expr_stmt_layout_step; eauto|eapply cm_v_init_layout_step; eauto|eapply cm_v_if_layout_step; eauto|eapply cm_v_while_guard_layout_step; eauto|eapply cm_v_return_layout_step; eauto|apply cm_v_halt_layout_step].
 destruct rest; [destruct READY as [NO|[OK DEPTH]]; [contradiction|eapply cm_v_arg_nil_layout_step; eauto]|eapply cm_v_arg_cons_layout_step; exact LAYOUT].
Qed.
Lemma cm_v_task_layout_step sp ap p fid v st ks ann :
 cm_annotation_erases (CMVTask p fid v st ks) ann -> cm_v_layout_ready sp ap p v st ann ->
 cm_task_layout sp ap p (CMVTask p fid v st ks) ann ->
 cm_task_layout sp ap p (cm_step sp (CMVTask p fid v st ks)) (cm_update_annotation(cm_annotation_step sp ap (CMVTask p fid v st ks) ann)).
Proof.
 destruct ann as [pc temp b c cursors spills saved calls]; cbn [cm_annotation_erases cm_ann_cursors]; intros ER READY LAYOUT; subst ks.
 destruct cursors as [|[phase owner ob oc] tail].
 - exact I.
 - cbn [cm_v_layout_ready cm_ann_cursors hd cm_cursor_phase] in READY; destruct READY as [NO|[_ [TEMP PHASE]]]; [discriminate|].
   change (cm_task_layout sp ap p (cm_vapply sp p fid (cm_phase_frame phase) v st (cm_cursor_frames tail)) (cm_update_annotation(cm_update_v sp ap p fid v st (CMAnnotation pc temp b c (CMACursor phase owner ob oc::tail) spills saved calls) phase))).
   eapply cm_v_phase_layout_step; eauto.
Qed.
