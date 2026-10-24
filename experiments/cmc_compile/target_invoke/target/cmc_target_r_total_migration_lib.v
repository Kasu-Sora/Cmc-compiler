Require Export SimpleC.EE.QCP_demos_human.cmc_target_empty_call_migration_lib.
From AUXLib Require Import ListLib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_target_r_task_step sp ap p fid expr st ks target ann :
 cm_semantic_wf_program(cm_source_function_policy sp)p ->
 cm_expr_wf(cm_source_function_policy sp)p(cm_source_function_at sp fid p)expr ->
 cm_runtime_core(cm_source_function_policy sp)ap p fid st ann ->cm_tagged_span_valid st ->
 0<=cm_state_nextgen st ->cm_tags_generation_below(cm_state_nextgen st)(cm_state_tags st) ->
 cm_spill_frames_generation_below(cm_state_nextgen st)(cm_active_spill_frames fid st ann) ->
 cm_r_layout_ready sp p fid expr st ks ann ->cm_task_static_bases p(CMRTask p fid expr st ks) ->
 cm_task_layout sp ap p(CMRTask p fid expr st ks)ann ->
 cm_task_target_sim(cm_source_function_policy sp)p(CMRTask p fid expr st ks)target ann ->
 cm_target_step_result sp ap p(CMRTask p fid expr st ks)target ann.
Proof.
 intros WF EW RT TAG GEN TG FG LR BASE LAYOUT SIM.
 destruct expr;try solve[eapply cm_target_r_step_except_empty_call;[intros;discriminate|eassumption|eassumption|eassumption|eassumption|eassumption]].
 destruct args as[|a rest].
 - destruct LR as[CALL _];destruct(CALL fid0 ty eq_refl)as[OK[D AD]].
   eapply cm_target_r_empty_call_step;eassumption.
 - eapply cm_target_r_step_except_empty_call;[intros;discriminate|eassumption|eassumption|eassumption|eassumption|eassumption].
Qed.
Theorem cm_code_support_r_target_step sp ap nilslot p fid expr st ks target ann :
 cm_semantic_wf_program(cm_source_function_policy sp)p ->
 cm_code_support_invariants sp ap nilslot p(CMAState(CMRTask p fid expr st ks)target ann) ->
 cm_task_target_sim(cm_source_function_policy sp)p(CMRTask p fid expr st ks)target ann ->
 cm_target_step_result sp ap p(CMRTask p fid expr st ks)target ann.
Proof.
 intros WF[[[READY TAG]TYPE]LAYOUT]SIM.
 pose proof(cm_readiness_support_layout_ready sp ap p _ READY)as[_ LR].
 destruct READY as[RUN _];destruct RUN as[SHORT[_ RT]];destruct SHORT as[BASE _].
 destruct BASE as[STRUCT[STATIC _]];destruct STRUCT as[_[_[_[GEN PAYLOAD]]]].
 pose proof(cm_annotation_payload_implies_task_generation _ _ PAYLOAD)as FG.
 destruct GEN as[_[[LOW[_ TG]] _]];destruct TYPE as[_[_[_[EW _]]]].
 assert(NG:0<=cm_state_nextgen st).
 { unfold cm_first_dynamic_generation in LOW;pose proof(Zlength_nonneg(cm_program_globals p));pose proof(Zlength_nonneg(cm_program_strings p));lia. }
 eapply cm_target_r_task_step;eassumption.
Qed.
