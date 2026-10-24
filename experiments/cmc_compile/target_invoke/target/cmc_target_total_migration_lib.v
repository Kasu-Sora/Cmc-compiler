Require Export SimpleC.EE.QCP_demos_human.cmc_target_start_migration_lib.
Require Export SimpleC.EE.QCP_demos_human.cmc_target_control_invariant_migration_lib.
Require Export SimpleC.EE.QCP_demos_human.cmc_target_stmt_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Theorem cm_code_support_target_step sp ap nilslot p task target ann :
 cm_semantic_wf_program(cm_source_function_policy sp)p ->
 cm_code_support_invariants sp ap nilslot p(CMAState task target ann) ->
 cm_task_target_sim(cm_source_function_policy sp)p task target ann ->
 cm_target_step_result sp ap p task target ann.
Proof.
 intros WF SUPPORT SIM;destruct task as[q input|q fid expr st ks|q fid expr st ks|q fid stmt st ks|q fid v st ks|q fid ctl st ks|st ctl status].
 - destruct SIM as[-> [-> ->]];destruct SUPPORT as[[[READY _]_]_].
   pose proof(cm_readiness_support_layout_ready sp ap p _ READY)as[_[_ OK]];now apply cm_target_start_step.
 - pose proof SIM as[E _];subst q;eapply cm_code_support_r_target_step;eassumption.
 - pose proof SIM as[E _];subst q;destruct SUPPORT as[[[READY _]_]LAYOUT].
   pose proof(cm_readiness_support_layout_ready sp ap p _ READY)as[_ LR];eapply cm_target_l_step;eassumption.
 - pose proof SIM as[E _];subst q;destruct SUPPORT as[[[READY _]_]_].
   destruct READY as[RUN _];destruct RUN as[SHORT[_ RT]];destruct SHORT as[BASE _];destruct BASE as[STRUCT _].
   destruct STRUCT as[_[_[_[GEN PAYLOAD]]]];pose proof(cm_annotation_payload_implies_task_generation _ _ PAYLOAD)as FG.
   destruct GEN as[_[[_[_ TG]] _]];eapply cm_target_s_step;[exact(proj1 RT)|exact TG|exact FG|exact SIM].
 - pose proof SIM as[E _];subst q;eapply cm_code_support_v_target_step;eassumption.
 - pose proof SIM as[E _];subst q;eapply cm_code_support_c_target_step;eassumption.
 - now apply cm_target_done_step.
Qed.
Definition cm_full_support_invariants sp ap nilslot p ast :Prop :=cm_code_support_invariants sp ap nilslot p ast /\cm_astate_sim(cm_source_function_policy sp)p ast.
Theorem cm_full_support_initial sp ap nilslot p input :cm_task_succeeds sp(CMStartTask p input) ->
 cm_full_support_invariants sp ap nilslot p(cm_annotated_start(cm_source_function_policy sp)p input).
Proof. intro S;split;[now apply cm_code_support_initial|repeat split]. Qed.
Theorem cm_full_support_step sp ap nilslot p ast :cm_semantic_wf_program(cm_source_function_policy sp)p ->
 cm_full_support_invariants sp ap nilslot p ast ->cm_full_support_invariants sp ap nilslot p(cm_annotated_step sp ap ast).
Proof. intros WF[SUP SIM];split;[now apply cm_code_support_step|];destruct ast as[task target ann];eapply cm_code_support_target_step;eassumption. Qed.
Theorem cm_full_support_iter sp ap nilslot p n ast :cm_semantic_wf_program(cm_source_function_policy sp)p ->
 cm_full_support_invariants sp ap nilslot p ast ->cm_full_support_invariants sp ap nilslot p(cm_annotated_iter sp ap n ast).
Proof. intros WF;revert ast;induction n;intros ast H;[exact H|apply IHn;now apply cm_full_support_step]. Qed.
Theorem cm_source_termination_target_invariant sp ap (nilslot:cm_slot_d) p input output status n :
 cm_semantic_wf_program(cm_source_function_policy sp)p ->cm_source_terminates sp p input output status ->
 cm_astate_sim(cm_source_function_policy sp)p(cm_annotated_iter sp ap n(cm_annotated_start(cm_source_function_policy sp)p input)).
Proof.
 intros WF[INPUT[STATUS[st[ctl[RUN[SUCCESS OUTPUT]]]]]];apply(proj2(cm_full_support_iter sp ap nilslot p n (cm_annotated_start(cm_source_function_policy sp)p input) WF ltac:(apply cm_full_support_initial;exists st,ctl,status;split;assumption))).
Qed.
