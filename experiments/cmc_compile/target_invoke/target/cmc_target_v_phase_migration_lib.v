Require Export SimpleC.EE.QCP_demos_human.cmc_target_value_support_migration_lib.
Require Export SimpleC.EE.QCP_demos_human.cmc_target_value_linear_migration_lib.
Require Export SimpleC.EE.QCP_demos_human.cmc_target_output_migration_lib.
Require Export SimpleC.EE.QCP_demos_human.cmc_target_branch_migration_lib.
From AUXLib Require Import ListLib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_target_v_phase_step sp ap nilslot p fid phase v st pc temp b c owner ob oc tail spills saved calls target :
 let ann:=CMAnnotation pc temp b c(CMACursor phase owner ob oc::tail)spills saved calls in
 cm_semantic_wf_program(cm_source_function_policy sp)p ->
 cm_task_succeeds sp(cm_vapply sp p fid(cm_phase_frame phase)v st(cm_cursor_frames tail)) ->
 cm_runtime_core(cm_source_function_policy sp)ap p fid st ann ->cm_tagged_span_valid st ->
 cm_state_generation_below(cm_source_function_policy sp)p fid st ->
 cm_value_generation_below(cm_state_nextgen st)v ->cm_frame_generation_below(cm_source_function_policy sp)p fid(cm_state_nextgen st)(cm_phase_frame phase) ->
 cm_spill_frames_generation_below(cm_state_nextgen st)(cm_active_spill_frames fid st ann) ->
 cm_frame_fid_ready p fid(cm_phase_frame phase) ->cm_phase_budget(cm_source_function_policy sp)p fid phase owner ->
 cm_phase_spill_consistent temp owner phase spills ->cm_frame_short_ready st(cm_phase_frame phase) ->
 cm_phase_static_type_ready(cm_source_function_policy sp)nilslot p fid phase ->cm_phase_value_type_ready(cm_source_function_policy sp)nilslot p fid phase v ->
 temp=cm_phase_child_temp phase owner ->cm_v_phase_ready sp p v st ann phase ->
 cm_task_layout sp ap p(CMVTask p fid v st(cm_cursor_frames(cm_ann_cursors ann)))ann ->
 cm_task_target_sim(cm_source_function_policy sp)p(CMVTask p fid v st(cm_cursor_frames(cm_ann_cursors ann)))target ann ->
 cm_target_step_result sp ap p(CMVTask p fid v st(cm_cursor_frames(cm_ann_cursors ann)))target ann.
Proof.
 cbn zeta;intros WF SUCCESS RT TAG GEN VG FGEN FG FID BUD SP SHORT TYPE VALUE TEMP READY LAYOUT SIM.
 assert(NG:0<=cm_state_nextgen st).
 { destruct GEN as[G _];unfold cm_first_dynamic_generation in G;pose proof(Zlength_nonneg(cm_program_globals p));pose proof(Zlength_nonneg(cm_program_strings p));lia. }
 assert(HELD:forall slot value,0<=fid ->cm_spill_holds slot value spills ->0<=slot<cm_temp_slots(cm_source_function_at sp fid p)).
 { intros;eapply cm_runtime_held_slot_bounds;[exact(proj2 RT)|eassumption|eassumption]. }
 destruct phase;cbn[cm_v_phase_ready]in READY;try contradiction;
 cbn[cm_frame_fid_ready cm_phase_frame]in FID;
 cbn[cm_phase_static_type_ready]in TYPE;cbn[cm_phase_value_type_ready]in VALUE;
 cbn[cm_phase_budget]in BUD;cbn[cm_phase_spill_consistent]in SP;cbn[cm_phase_child_temp]in TEMP;
 try solve[eapply cm_target_v_halt_step;eassumption|eapply cm_target_v_unary_step;eassumption|eapply cm_target_v_putc_step;eassumption|eapply cm_target_v_puti_step;eassumption|eapply cm_target_v_exit_step;eassumption|eapply cm_target_v_expr_stmt_step;eassumption|eapply cm_target_v_if_step;eassumption|eapply cm_target_v_while_guard_step;eassumption|eapply cm_target_v_return_step;eassumption].
 - eapply cm_target_v_load_step;[split;[reflexivity|exact RT]|exact TYPE|exact READY|exact LAYOUT|exact SIM].
 - pose proof(cm_expr_temps_nonnegative__index_bounds expr)as N.
   eapply cm_target_v_assign_left_step;try eassumption;[lia|unfold cm_source_function_at;lia].
 - destruct SP as[_ HOLD];eapply cm_target_v_assign_right_step;try eassumption;[lia|eapply HELD;[lia|exact HOLD]].
 - destruct(Z.eq_dec op 0)as[->|N0];[exact(cm_target_v_short_left_step sp ap p fid true lhs rhs ty v st pc temp b c owner ob oc tail spills saved calls target WF LAYOUT SIM)|].
   destruct(Z.eq_dec op 1)as[->|N1];[exact(cm_target_v_short_left_step sp ap p fid false lhs rhs ty v st pc temp b c owner ob oc tail spills saved calls target WF LAYOUT SIM)|].
   assert(E0:(op=?0)=false)by(now apply Z.eqb_neq);assert(E1:(op=?1)=false)by(now apply Z.eqb_neq);rewrite E0,E1 in BUD;cbn[orb]in BUD.
   pose proof(cm_expr_temps_nonnegative__index_bounds rhs)as N.
   eapply cm_target_v_binary_left_step;try eassumption;[lia|unfold cm_source_function_at;lia].
 - destruct(Z.eq_dec op 0)as[E0|N0];[eapply cm_target_v_short_right_step;try eassumption;now left|].
   destruct(Z.eq_dec op 1)as[E1|N1];[eapply cm_target_v_short_right_step;try eassumption;now right|].
   destruct SP as[_[[BAD|BAD]|[_ HOLD]]];try contradiction;destruct TYPE as[EW LT].
   cbn[cm_expr_wf]in EW.
   eapply cm_target_v_binary_ordinary_step;try eassumption;[exact(proj1 WF)|lia|eapply HELD;[lia|exact HOLD]|tauto].
 - pose proof(cm_expr_temps_nonnegative__index_bounds expr)as N.
   eapply cm_target_v_index_left_step;try eassumption;[lia|unfold cm_source_function_at;lia].
 - destruct SP as[_ HOLD];eapply cm_target_v_index_right_step;try eassumption;[lia|eapply HELD;[lia|exact HOLD]|exact(proj1 TYPE)].
 - eapply cm_target_v_member_step;eassumption.
 - destruct(cm_init_succeeds_ready _ _ _ _ _ _ _ SUCCESS)as[ADDRESS STORE];eapply cm_target_v_init_step;eassumption.
 - destruct rest as[|arg args0].
   + destruct READY as[BAD|[OK DEPTH]];[contradiction|].
     destruct SP as[_[_[CUR[_[LEN[_ STAGED]]]]]].
     cbn[cm_frame_generation_below cm_phase_frame]in FGEN.
     eapply cm_target_v_arg_nil_step;try eassumption;[exact(proj2(proj2 GEN))|now split|lia|tauto|unfold cm_source_function_at;tauto|rewrite Zlength_cons;rewrite Zlength_nil in LEN;lia].
   + eapply cm_target_v_arg_cons_step;try eassumption;[lia|unfold cm_source_function_at;tauto].
Qed.
