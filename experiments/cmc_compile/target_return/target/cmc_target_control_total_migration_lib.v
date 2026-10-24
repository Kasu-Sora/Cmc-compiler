Require Export SimpleC.EE.QCP_demos_human.cmc_target_return_dispatch_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_target_c_phase_step sp ap nilslot p fid ctl st phase pc temp b c owner ob oc tail spills saved calls target :
 let ann:=CMAnnotation pc temp b c(CMACursor phase owner ob oc::tail)spills saved calls in
 cm_semantic_wf_program(cm_source_function_policy sp)p ->cm_control_kind ctl<>4 ->
 cm_runtime_core(cm_source_function_policy sp)ap p fid st ann ->cm_tagged_span_valid st ->
 cm_phase_static_type_ready(cm_source_function_policy sp)nilslot p fid phase ->cm_c_phase_ready ap ctl ann phase ->cm_c_code_ready(cm_source_function_policy sp)p fid ann phase ->
 cm_task_layout sp ap p(CMCTask p fid ctl st(cm_cursor_frames(cm_ann_cursors ann)))ann ->
 cm_task_target_sim(cm_source_function_policy sp)p(CMCTask p fid ctl st(cm_cursor_frames(cm_ann_cursors ann)))target ann ->
 cm_target_step_result sp ap p(CMCTask p fid ctl st(cm_cursor_frames(cm_ann_cursors ann)))target ann.
Proof.
 cbn zeta;intros WF NE RT TAG TYPE READY CODE LAYOUT SIM;destruct phase;cbn[cm_c_phase_ready]in READY;try tauto.
 - pose proof(proj2 RT)as R;cbn[cm_runtime_stack cm_ann_cursors cm_cursor_phase cm_phase_is_call cm_phase_is_scope cm_phase_oldregions]in R;destruct R as[_[PREFIX REST]].
   eapply cm_target_c_block_step;try eassumption;now apply cm_region_prefix_suffix_incl in PREFIX.
 - now apply cm_target_c_sequence_step.
 - unfold cm_c_code_ready in CODE;specialize(CODE _ _ _ _ _ _ eq_refl);destruct CODE as[B[C END]];cbn[cm_ann_break cm_ann_continue]in B,C;subst b c.
   pose proof(proj2 RT)as R;cbn[cm_runtime_stack cm_ann_cursors cm_cursor_phase cm_phase_is_call cm_phase_is_scope cm_phase_oldregions]in R;destruct R as[_[PREFIX REST]].
   eapply cm_target_c_while_step;try eassumption;now apply cm_region_prefix_suffix_incl in PREFIX.
 - eapply cm_target_c_call_step;try eassumption.
Qed.
Lemma cm_target_c_task_step sp ap nilslot p fid ctl st ks ann target :
 cm_semantic_wf_program(cm_source_function_policy sp)p ->cm_annotation_erases(CMCTask p fid ctl st ks)ann ->
 cm_runtime_core(cm_source_function_policy sp)ap p fid st ann ->cm_tagged_span_valid st ->
 cm_cursors_type_ready(cm_source_function_policy sp)nilslot p fid(cm_ann_cursors ann) ->cm_c_layout_ready(cm_source_function_policy sp)ap p fid ctl ann ->
 cm_task_layout sp ap p(CMCTask p fid ctl st ks)ann ->cm_task_target_sim(cm_source_function_policy sp)p(CMCTask p fid ctl st ks)target ann ->
 cm_target_step_result sp ap p(CMCTask p fid ctl st ks)target ann.
Proof.
 intros WF ER RT TAG TYPE READY LAYOUT SIM;destruct(Z.eq_dec(cm_control_kind ctl)4)as[EXIT|NE].
 - destruct ctl;cbn[cm_control_kind]in EXIT;try discriminate;now apply cm_target_exit_step.
 - destruct ann as[pc temp b c cursors spills saved calls];cbn[cm_annotation_erases cm_ann_cursors]in ER;subst ks.
   destruct cursors as[|[phase owner ob oc]tail];[exact(False_rect _ (proj2 RT))|].
   cbn[cm_c_layout_ready cm_ann_cursors hd cm_cursor_phase]in READY;destruct READY as[[NO _]|[_[PHASE CODE]]];[discriminate|].
   destruct TYPE as[TYPE _];eapply cm_target_c_phase_step;try eassumption.
Qed.
