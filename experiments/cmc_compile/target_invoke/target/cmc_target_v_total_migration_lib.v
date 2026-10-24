Require Export SimpleC.EE.QCP_demos_human.cmc_target_v_phase_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Theorem cm_code_support_v_target_step sp ap nilslot p fid v st ks target ann :
 cm_semantic_wf_program(cm_source_function_policy sp)p ->
 cm_code_support_invariants sp ap nilslot p(CMAState(CMVTask p fid v st ks)target ann) ->
 cm_task_target_sim(cm_source_function_policy sp)p(CMVTask p fid v st ks)target ann ->
 cm_target_step_result sp ap p(CMVTask p fid v st ks)target ann.
Proof.
 intros WF[[[READY TAG]TYPE]LAYOUT]SIM.
 pose proof(cm_readiness_support_layout_ready sp ap p _ READY)as[_ LR].
 destruct READY as[RUN _];destruct RUN as[SHORT[_ RT]];destruct SHORT as[BASE[_ SHORT]].
 destruct BASE as[STRUCT _];destruct STRUCT as[CTRL[_[BUD[GEN PAYLOAD]]]].
 pose proof(cm_annotation_payload_implies_task_generation _ _ PAYLOAD)as FG.
 destruct CTRL as[S[ER[_[_[_[FID[SP _]]]]]]].
 destruct GEN as[_[SG[VG FGEN]]];destruct TYPE as[_[CT VT]].
 destruct ann as[pc temp b c cursors spills saved calls];change(cm_cursor_frames cursors=ks)in ER;subst ks.
 destruct cursors as[|[phase owner ob oc]tail];[exact(False_rect _ (proj2 RT))|].
 cbn[cm_v_layout_ready cm_ann_cursors hd cm_cursor_phase]in LR;destruct LR as[BAD|[_[TEMP READY]]];[discriminate|].
 destruct CT as[TYPE _];destruct FID as[FID _];destruct BUD as[BUD _];destruct FGEN as[FGEN _];destruct SHORT as[SHORT _];destruct SP as[SP _].
 pose proof(cm_succeeds_step_total sp _ S)as SUCCESS.
 eapply cm_target_v_phase_step;try eassumption;exact TEMP.
Qed.
