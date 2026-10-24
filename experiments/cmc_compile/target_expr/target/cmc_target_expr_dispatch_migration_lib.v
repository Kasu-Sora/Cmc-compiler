Require Export SimpleC.EE.QCP_demos_human.cmc_target_binding_migration_lib.
Require Export SimpleC.EE.QCP_demos_human.cmc_target_io_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_target_l_step sp ap p fid expr st ks target ann :
 cm_l_layout_ready sp p fid expr st -> cm_task_layout sp ap p (CMLTask p fid expr st ks) ann ->
 cm_task_target_sim (cm_source_function_policy sp) p (CMLTask p fid expr st ks) target ann ->
 cm_target_step_result sp ap p (CMLTask p fid expr st ks) target ann.
Proof.
 intros [LV VAR] LAYOUT SIM; destruct expr; cbn [cm_lvalue]in LV; try contradiction;
 try solve[apply cm_target_l_structural_step; [exact LV|exact SIM]|apply cm_target_l_structural_step; [exact I|exact SIM]].
 eapply cm_target_l_var_step; [eapply VAR; reflexivity|exact LAYOUT|exact SIM].
Qed.
Lemma cm_target_r_step_except_empty_call sp ap p fid expr st ks target ann :
 (forall callee ty,expr<>CMCallE callee [] ty) ->
 cm_expr_wf (cm_source_function_policy sp) p (cm_source_function_at sp fid p) expr ->
 cm_r_layout_ready sp p fid expr st ks ann -> cm_task_static_bases p (CMRTask p fid expr st ks) ->
 cm_task_layout sp ap p (CMRTask p fid expr st ks) ann ->
 cm_task_target_sim (cm_source_function_policy sp) p (CMRTask p fid expr st ks) target ann ->
 cm_target_step_result sp ap p (CMRTask p fid expr st ks) target ann.
Proof.
 intros NONEMPTY WF [CALL [INPUT VAR]] [_ BASE] LAYOUT SIM; destruct expr;
 try solve[apply cm_target_r_structural_step; [exact I|exact SIM]|eapply cm_target_const_step; eauto|eapply cm_target_sizeof_step; eauto].
 - eapply cm_target_string_step; [exact(proj1 WF)|exact BASE|exact LAYOUT|exact SIM].
 - eapply cm_target_r_var_step; [exact(proj1 WF)|intros AR; eapply VAR; eauto|exact LAYOUT|exact SIM].
 - apply cm_target_r_structural_step; [intro E; subst args; eapply NONEMPTY; reflexivity|exact SIM].
 - eapply cm_target_getc_step; [eapply INPUT; reflexivity|exact LAYOUT|exact SIM].
Qed.
