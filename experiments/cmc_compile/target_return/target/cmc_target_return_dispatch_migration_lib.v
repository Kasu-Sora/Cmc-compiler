Require Export SimpleC.EE.QCP_demos_human.cmc_target_return_fallthrough_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_target_c_call_step sp ap nilslot p fid ctl st caller env fp regions ret pc temp b c owner ob oc tail spills saved calls target :
 let ann:=CMAnnotation pc temp b c(CMACursor(CACallP caller env fp regions ret)owner ob oc::tail)spills saved calls in
 cm_runtime_core(cm_source_function_policy sp)ap p fid st ann ->cm_tagged_span_valid st ->
 cm_phase_static_type_ready(cm_source_function_policy sp)nilslot p fid(CACallP caller env fp regions ret) ->
 cm_c_phase_ready ap ctl ann(CACallP caller env fp regions ret) ->
 cm_task_layout sp ap p(CMCTask p fid ctl st(cm_cursor_frames(cm_ann_cursors ann)))ann ->
 cm_task_target_sim(cm_source_function_policy sp)p(CMCTask p fid ctl st(cm_cursor_frames(cm_ann_cursors ann)))target ann ->
 cm_target_step_result sp ap p(CMCTask p fid ctl st(cm_cursor_frames(cm_ann_cursors ann)))target ann.
Proof.
 cbn zeta;intros RT TAG[_[_[_ TY]]]READY LAYOUT SIM;pose proof(proj2 RT)as R.
 cbn[cm_runtime_stack cm_ann_cursors cm_ann_spills cm_ann_saved cm_ann_calls cm_cursor_phase cm_phase_is_call cm_phase_oldregions cm_phase_oldfp cm_phase_caller]in R.
 destruct R as[PREFIX[SEG[SPILLS[S[C[BASE[SV[SFID[SFP REC]]]]]]]]].
 pose proof(cm_region_prefix_suffix_incl _ _ _ _ _ _ _ PREFIX)as INC.
 destruct saved as[|[sfid sfp sspills]saved];[contradiction|];destruct calls as[|[base save returnpc]calls];[contradiction|].
 cbn[hd cm_call_sim_base cm_call_sim_saved cm_spill_frame_fid cm_spill_frame_fp]in BASE,SV,SFID,SFP;subst base save sfid sfp.
 cbn[cm_c_phase_ready]in READY;destruct ctl;cbn[cm_control_kind]in READY;try lia.
 - now eapply cm_target_c_fallthrough_step.
 - now eapply cm_target_c_return_step.
 - now apply cm_target_exit_step.
Qed.
