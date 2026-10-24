Require Export SimpleC.EE.QCP_demos_human.cmc_type_value_binary_migration_lib.
Require Export SimpleC.EE.QCP_demos_human.cmc_type_value_args_migration_lib.
Require Export SimpleC.EE.QCP_demos_human.cmc_type_expr_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_v_type_ready_step sp ap nilslot p fid phase owner ob oc rest v st ann :
 cm_typed_program (cm_source_function_policy sp) p -> cm_ann_cursors ann=CMACursor phase owner ob oc::rest ->
 cm_frame_fid_ready p fid (cm_phase_frame phase) ->
 cm_cursors_type_ready (cm_source_function_policy sp) nilslot p fid (cm_ann_cursors ann) -> cm_phase_value_type_ready (cm_source_function_policy sp) nilslot p fid phase v ->
 cm_task_type_ready (cm_source_function_policy sp) nilslot p (cm_vapply sp p fid (cm_phase_frame phase) v st (cm_cursor_frames rest)) (cm_update_annotation (cm_update_v sp ap p fid v st ann phase)).
Proof.
 intros WF CUR FID TYPES VALUE; destruct phase;
 try solve [eapply cm_v_basic_type_ready_step; eauto; exact I].
 - eapply cm_v_binleft_type_ready_step; eauto.
 - eapply cm_v_binright_type_ready_step; eauto.
 - eapply cm_v_args_type_ready_step; eauto.
Qed.
Lemma cm_task_type_step_support sp ap nilslot p task ann :
 cm_typed_program (cm_source_function_policy sp) p -> cm_annotation_erases task ann ->
 cm_task_coordinate_ready (cm_source_function_policy sp) p task ann -> cm_task_fid_ready p task ->
 cm_task_type_ready (cm_source_function_policy sp) nilslot p task ann ->
 cm_task_type_ready (cm_source_function_policy sp) nilslot p (cm_step sp task) (cm_update_annotation (cm_annotation_step sp ap task ann)).
Proof.
 intros WF ERASE COORD FID T; destruct task as [q input|q fid e st ks|q fid e st ks|q fid stmt st ks|q fid v st ks|q fid ctl st ks|st ctl status].
 - destruct COORD as [-> ->]; now apply cm_type_start_step.
 - destruct T as [-> T]; cbn [cm_annotation_erases] in ERASE; subst ks; apply cm_r_type_ready_step; [exact WF|now split].
 - destruct T as [-> T]; cbn [cm_annotation_erases] in ERASE; subst ks; apply cm_l_type_ready_step; [exact WF|now split].
 - destruct T as [-> T]; cbn [cm_annotation_erases] in ERASE; subst ks; apply cm_s_type_ready_step; [exact WF|now split].
 - destruct T as [-> [T V]]; cbn [cm_annotation_erases] in ERASE; subst ks.
   cbn [cm_step cm_annotation_step]; destruct (cm_ann_cursors ann) as [|[phase owner ob oc] rest] eqn:CUR; [exact I|].
   cbn [cm_cursor_frames cm_cursor_phase]; eapply cm_v_type_ready_step; try eassumption.
   + cbn [cm_task_fid_ready] in FID; try rewrite CUR in FID; exact (proj1 FID).
   + now rewrite CUR.
 - destruct T as [-> [C T]]; cbn [cm_annotation_erases] in ERASE; subst ks.
   cbn [cm_step cm_annotation_step]; destruct (cm_control_kind ctl=?4); [exact I|].
   destruct (cm_ann_cursors ann) as [|[phase owner ob oc] rest] eqn:CUR.
   + destruct (cm_control_kind ctl=?5); exact I.
   + cbn [cm_cursor_frames cm_cursor_phase]; eapply cm_c_type_ready_step; try eassumption.
     * cbn [cm_task_fid_ready] in FID; try rewrite CUR in FID; exact (proj1 FID).
     * now rewrite CUR.
 - exact I.
Qed.
