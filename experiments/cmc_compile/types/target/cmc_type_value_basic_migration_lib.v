Require Export SimpleC.EE.QCP_demos_human.cmc_type_operations_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Ltac cm_ty_value_reduce := cbv beta iota zeta delta [cm_vapply cm_update_v cm_ann_pop cm_ann_replace cm_ann_put_spill cm_ann_spills_set cm_ann_cursors cm_phase_frame cm_ann_plain cm_update_annotation cm_cursor_temp cm_cursor_break cm_cursor_continue cm_cursor_phase cm_phase_value_type_ready cm_cursor_head_value_type_ready cm_phase_lvalue_type_ready cm_list_empty hd tl andb orb negb] in *; cm_ty_reduce.
Lemma cm_v_basic_type_ready_step sp ap nilslot p fid phase owner ob oc rest v st ann :
 cm_typed_program (cm_source_function_policy sp) p -> cm_ann_cursors ann=CMACursor phase owner ob oc::rest ->
 cm_frame_fid_ready p fid (cm_phase_frame phase) ->
 (match phase with CABinLP _ _ _ _ | CABinRP _ _ _ _ _ | CAArgP _ _ _ _ _ _ _ _=>False | _=>True end) ->
 cm_cursors_type_ready (cm_source_function_policy sp) nilslot p fid (cm_ann_cursors ann) -> cm_phase_value_type_ready (cm_source_function_policy sp) nilslot p fid phase v ->
 cm_task_type_ready (cm_source_function_policy sp) nilslot p (cm_vapply sp p fid (cm_phase_frame phase) v st (cm_cursor_frames rest)) (cm_update_annotation (cm_update_v sp ap p fid v st ann phase)).
Proof.
 intros WF CUR FID BASIC TYPES VALUE; rewrite CUR in TYPES.
 destruct ann as [pc temp breakpc continuepc cursors spills saved calls]; cbn [cm_ann_cursors] in CUR; subst cursors.
 destruct phase; try contradiction; cbn [cm_frame_fid_ready cm_phase_frame] in FID; cm_ty_value_reduce;
 repeat match goal with |- context[if ?b then _ else _]=>cm_rt_bool b; cm_ty_value_reduce end;
 repeat first [assumption|reflexivity|exact I|match goal with |- _ /\ _=>split end|match goal with |- forall _ _,False -> _=>intros; contradiction end].
 all: try solve [intuition eauto].
 all: try solve [apply cm_cursor_expr_value_ready; cbv beta iota zeta delta [cm_cursor_head_expr_type_ready cm_phase_expr_type_ready cm_cursor_phase]; intuition].
 all: repeat match goal with H:_ /\ _|-_=>destruct H end.
 all: try solve [now left].
 all: try solve [match goal with H:forall (result:cm_type) (v:cm_value),result = ?ty -> _|-_=>apply (H ty _ eq_refl) end; eauto using cm_load_value_type_ready,cm_convert_value_type_ready,cm_unary_value_type_ready,cm_ptr_shift_type_ready,cm_member_value_type_ready; left; reflexivity].
 eapply cm_expr_convertible_source_scalar; eassumption.
Qed.
