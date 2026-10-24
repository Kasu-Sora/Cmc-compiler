Require Export SimpleC.EE.QCP_demos_human.cmc_type_value_basic_migration_lib.
Require Export SimpleC.EE.QCP_demos_human.cmc_type_expr_call_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_v_args_type_ready_step sp ap nilslot p fid callee args values ret all_args base current scratch owner ob oc rest v st ann :
 cm_typed_program (cm_source_function_policy sp) p ->
 cm_ann_cursors ann=CMACursor (CAArgP callee args values ret all_args base current scratch) owner ob oc::rest -> 0<=fid<Zlength (cm_program_functions p) ->
 cm_cursors_type_ready (cm_source_function_policy sp) nilslot p fid (cm_ann_cursors ann) -> cm_value_convertible_to v (cm_arg_next_type nilslot (cm_function_params (cm_source_function_at sp callee p)) (rev values)) ->
 cm_task_type_ready (cm_source_function_policy sp) nilslot p (cm_vapply sp p fid (cm_phase_frame (CAArgP callee args values ret all_args base current scratch)) v st (cm_cursor_frames rest)) (cm_update_annotation (cm_update_v sp ap p fid v st ann (CAArgP callee args values ret all_args base current scratch))).
Proof.
 intros WF CUR FID TYPES VALUE; rewrite CUR in TYPES.
 destruct TYPES as [[CL [CU [ARGS [AW [PROG RET]]]]] [INPUT [RESULT TAIL]]].
 destruct ann as [pc temp breakpc continuepc cursors spills saved calls]; cbn [cm_ann_cursors] in CUR; subst cursors.
 destruct args as [|arg args].
 - cbv beta iota zeta delta [cm_vapply cm_phase_frame cm_update_v cm_list_empty cm_begin_call cm_ann_cursors cm_update_annotation cm_cursor_temp cm_cursor_break cm_cursor_continue tl hd].
   destruct (cm_call_ok sp p callee (rev (v::values)) st); cbn [andb]; [destruct (cm_call_depth (cm_cursor_frames rest)<?65536)|]; try solve [apply cm_type_error; exact TAIL].
   eapply cm_type_enter_call with (values:=rev (v::values)); try eassumption; try lia.
   + intros x X; exact (RESULT ret x eq_refl X).
 - pose proof (cm_arg_progress_extend _ _ _ _ _ _ _ _ _ AW PROG ltac:(discriminate) VALUE) as PROG'.
   pose proof (cm_arg_progress_next_expr _ _ arg _ _ _ _ _ _ _ AW PROG ltac:(discriminate) VALUE) as CONV.
   cbn [hd tl] in CONV,PROG'.
   destruct ARGS as [ARG [SC ARGS]].
   cm_ty_value_reduce; cbn [rev];
   repeat first [assumption|reflexivity|exact I|match goal with |- _ /\ _=>split end].
   + exact (proj1 FID).
   + exact (proj2 FID).
   + apply cm_cursor_expr_value_ready; cbv beta iota zeta delta [cm_cursor_head_expr_type_ready cm_phase_expr_type_ready cm_cursor_phase]; exact CONV.
Qed.
