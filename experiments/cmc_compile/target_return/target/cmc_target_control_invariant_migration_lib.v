Require Export SimpleC.EE.QCP_demos_human.cmc_target_control_total_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Theorem cm_code_support_c_target_step sp ap nilslot p fid ctl st ks target ann :
 cm_semantic_wf_program(cm_source_function_policy sp)p ->
 cm_code_support_invariants sp ap nilslot p(CMAState(CMCTask p fid ctl st ks)target ann) ->
 cm_task_target_sim(cm_source_function_policy sp)p(CMCTask p fid ctl st ks)target ann ->
 cm_target_step_result sp ap p(CMCTask p fid ctl st ks)target ann.
Proof.
 intros WF[[[READY TAG]TYPE]LAYOUT]SIM.
 pose proof(cm_readiness_support_layout_ready sp ap p _ READY)as[_ LR].
 pose proof(proj1 READY)as RUN;pose proof(proj1(proj1(proj1(proj1 RUN))))as CTRL.
 destruct CTRL as[S[ER REST]];destruct(proj2 RUN)as[_ RT];destruct TYPE as[_[_ CUR]].
 eapply cm_target_c_task_step;try eassumption.
Qed.
