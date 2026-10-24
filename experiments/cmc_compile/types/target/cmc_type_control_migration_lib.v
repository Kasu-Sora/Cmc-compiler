Require Export SimpleC.EE.QCP_demos_human.cmc_type_statement_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_convert_value_type_ready st v ty : cm_value_convertible_to v ty -> cm_value_type_compatible (cm_convert_value st ty v) ty.
Proof. intro H; apply cm_convert_value_type; [destruct H as [H|[_ P]]; [exact (proj2 (cm_convertible_scalar_types _ _ H))|now right]|exact H]. Qed.
Lemma cm_zero_value_convertible ty : cm_scalar_expr_type ty -> cm_value_convertible_to (CMIntV 0) ty.
Proof. destruct ty; cbv beta iota delta [cm_scalar_expr_type cm_integer_type cm_value_convertible_to cm_value_type cm_is_pointer cm_convertible cm_is_struct]; intuition discriminate. Qed.
Ltac cm_ty_control_reduce := cbv beta iota zeta delta [cm_capply cm_update_c cm_ann_pop cm_ann_plain cm_ann_leave_call cm_ann_replace cm_update_annotation cm_ann_cursors cm_phase_frame cm_control_kind andb orb negb hd tl] in *; cm_ty_reduce.
Lemma cm_c_type_ready_step sp ap nilslot p fid phase owner ob oc rest ctl st ann :
 cm_typed_program (cm_source_function_policy sp) p -> cm_ann_cursors ann=CMACursor phase owner ob oc::rest ->
 cm_frame_fid_ready p fid (cm_phase_frame phase) ->
 cm_control_type_ready (cm_source_function_policy sp) p fid ctl -> cm_cursors_type_ready (cm_source_function_policy sp) nilslot p fid (cm_ann_cursors ann) ->
 cm_task_type_ready (cm_source_function_policy sp) nilslot p (cm_capply sp p fid (cm_phase_frame phase) ctl st (cm_cursor_frames rest)) (cm_update_annotation (cm_update_c sp ap p fid ctl st ann phase)).
Proof.
 intros WF CUR FID CONTROL TYPES; rewrite CUR in TYPES.
 destruct ann as [pc temp breakpc continuepc cursors spills saved calls]; cbn [cm_ann_cursors] in CUR; subst cursors.
 destruct phase; cbn [cm_frame_fid_ready cm_phase_frame] in FID; cm_ty_control_reduce;
 repeat match goal with |- context[if ?b then _ else _]=>cm_rt_bool b; cm_ty_control_reduce end;
 repeat first [assumption|reflexivity|exact I|match goal with |- _ /\ _=>split end|match goal with |- forall _ _,False -> _=>intros; contradiction end].
 all: try solve [intuition eauto].
 all: try solve [apply cm_cursor_expr_value_ready; cbv beta iota zeta delta [cm_cursor_head_expr_type_ready cm_phase_expr_type_ready cm_cursor_phase]; intuition].
 all: destruct ctl; cbn [cm_control_kind cm_control_value] in *; try discriminate.
 all: repeat match goal with H:_ /\ _|-_=>destruct H end.
 all: try exact I.
 all: match goal with H:forall (result:cm_type) (v:cm_value), result = ?ty -> _|-_=>apply (H ty _ eq_refl) end.
 all: apply cm_convert_value_type_ready.
 all: try congruence.
 all: apply cm_zero_value_convertible; match goal with H: ?ret = cm_function_ret _|-_=>rewrite H end.
 all: apply cm_scalar_type_is_expr_type with (structs:=cm_program_structs p); exact (proj1 (cm_typed_function_at _ _ fid WF ltac:(assumption) ltac:(assumption))).
Qed.
