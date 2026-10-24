Require Export SimpleC.EE.QCP_demos_human.cmc_type_expr_leaf_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_type_enter_call sp nilslot p caller callee st values ret returnpc temp breakpc continuepc tail spills saved calls :
 cm_typed_program (cm_source_function_policy sp) p -> 0<=callee<Zlength (cm_program_functions p) ->
 (caller= -1 \/ 0<=caller<Zlength (cm_program_functions p)) -> ret=cm_function_ret (cm_source_function_at sp callee p) ->
 cm_cursors_type_ready (cm_source_function_policy sp) nilslot p caller tail -> cm_cursor_head_input_type_ready p caller ret tail ->
 (forall v,cm_value_type_compatible v ret -> cm_cursor_head_value_type_ready (cm_source_function_policy sp) nilslot p caller v tail) ->
 cm_task_type_ready (cm_source_function_policy sp) nilslot p (CMSTask p callee (cm_function_body (cm_source_function_at sp callee p)) (cm_enter_call sp p callee values st) (CMCallK caller (cm_state_env st) (cm_state_fp st) (cm_state_regions st) ret::cm_cursor_frames tail))
 (cm_ann_enter_call sp p caller callee st ret returnpc temp breakpc continuepc tail spills saved calls).
Proof.
 intros WF [CL CU] CALLER RET CT INPUT RESULT.
 pose proof (cm_typed_function_at _ _ callee WF CL CU) as FW; destruct FW as [_ [_ [_ [BODY _]]]].
 cbv beta iota zeta delta [cm_ann_enter_call cm_ann_cursors]; cm_ty_reduce.
 repeat first [assumption|reflexivity|exact I|match goal with |- _ /\ _=>split end].
 - now apply cm_stmt_wf_loop_mono with (loop:=false).
 - intros result v -> V; now apply RESULT.
Qed.
Lemma cm_halt_cursors_type policy nilslot p fid owner ob oc : cm_cursors_type_ready policy nilslot p fid [CMACursor CAHaltP owner ob oc].
Proof. cbv beta iota zeta delta [cm_cursors_type_ready cm_cursor_phase cm_phase_static_type_ready cm_phase_parent_type_ready cm_phase_result_type_ready cm_phase_result_type cm_phase_next_fid]; repeat split; intros; contradiction. Qed.
Lemma cm_type_start_step sp ap nilslot p input : cm_typed_program (cm_source_function_policy sp) p ->
 cm_task_type_ready (cm_source_function_policy sp) nilslot p (cm_step sp (CMStartTask p input)) (cm_update_annotation (cm_annotation_step sp ap (CMStartTask p input) cm_initial_annotation)).
Proof.
 intro WF; pose proof WF as [_ [_ [_ [_ [MAIN [RET _]]]]]].
 cbv beta iota zeta delta [cm_step cm_annotation_step cm_begin_call cm_update_annotation cm_list_empty andb].
 destruct (cm_call_ok sp p (cm_program_main p) [] (cm_initial_state sp p input)); [|split; [reflexivity|split; [exact I|apply cm_halt_cursors_type]]].
 cbn [cm_call_depth Z.ltb Pos.ltb cm_ann_cursors cm_initial_annotation cm_cursor_frames cm_cursor_phase cm_phase_frame].
 eapply cm_type_enter_call with (values:=[]); [exact WF|exact MAIN|now left|symmetry; exact RET| |exact I|intros; exact I].
 apply cm_halt_cursors_type.
Qed.
