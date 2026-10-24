Require Export SimpleC.EE.QCP_demos_human.cmc_type_value_basic_migration_lib.
Require Export SimpleC.EE.QCP_demos_human.cmc_type_binary_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_binary_short_result op a b ty : cm_binary_types op a b ty -> (op=0 \/ op=1) -> ty=CMIntTy.
Proof. intros [_ B] [-> | ->]; cbv beta iota delta [Z.eqb Pos.eqb orb] in B; tauto. Qed.
Lemma cm_v_binleft_type_ready_step sp ap nilslot p fid op lhs rhs ty owner ob oc rest v st ann :
 cm_ann_cursors ann=CMACursor (CABinLP op lhs rhs ty) owner ob oc::rest -> 0<=fid<Zlength (cm_program_functions p) ->
 cm_cursors_type_ready (cm_source_function_policy sp) nilslot p fid (cm_ann_cursors ann) -> cm_value_type_compatible v (cm_expr_type lhs) ->
 cm_task_type_ready (cm_source_function_policy sp) nilslot p (cm_vapply sp p fid (cm_phase_frame (CABinLP op lhs rhs ty)) v st (cm_cursor_frames rest)) (cm_update_annotation (cm_update_v sp ap p fid v st ann (CABinLP op lhs rhs ty))).
Proof.
 intros CUR FID TYPES VALUE; rewrite CUR in TYPES.
 pose proof (proj1 TYPES) as EW; pose proof EW as [LW [RW BT]].
 pose proof (cm_binary_operand_scalars _ _ _ _ BT) as [LS RS].
 destruct ann as [pc temp breakpc continuepc cursors spills saved calls]; cbn [cm_ann_cursors] in CUR; subst cursors.
 cm_ty_value_reduce; repeat match goal with |- context[if ?b then _ else _]=>cm_rt_bool b; cm_ty_value_reduce end;
 repeat first [assumption|reflexivity|exact I|match goal with |- _ /\ _=>split end].
 all: try solve [intuition].
 all: try solve [apply cm_cursor_expr_value_ready; cbv beta iota zeta delta [cm_cursor_head_expr_type_ready cm_phase_expr_type_ready cm_cursor_phase]; reflexivity].
 all: repeat match goal with H:_ /\ _|-_=>destruct H end.
 all: match goal with H:forall (result:cm_type) (v:cm_value),result = ?ty -> _|-_=>apply (H ty _ eq_refl) end.
 all: assert (T:ty=CMIntTy) by (eapply cm_binary_short_result; [exact BT|first [now left|now right|match goal with H:(?op=?0)=true|-_=>apply Z.eqb_eq in H; now left | H:(?op=?1)=true|-_=>apply Z.eqb_eq in H; now right end]]).
 all: rewrite T; left; reflexivity.
Qed.
Lemma cm_v_binright_type_ready_step sp ap nilslot p fid op lhs rhs left ty owner ob oc rest v st ann :
 cm_ann_cursors ann=CMACursor (CABinRP op lhs rhs left ty) owner ob oc::rest ->
 cm_cursors_type_ready (cm_source_function_policy sp) nilslot p fid (cm_ann_cursors ann) -> cm_value_type_compatible v (cm_expr_type rhs) ->
 cm_task_type_ready (cm_source_function_policy sp) nilslot p (cm_vapply sp p fid (cm_phase_frame (CABinRP op lhs rhs left ty)) v st (cm_cursor_frames rest)) (cm_update_annotation (cm_update_v sp ap p fid v st ann (CABinRP op lhs rhs left ty))).
Proof.
 intros CUR TYPES VALUE; rewrite CUR in TYPES.
 pose proof (proj1 TYPES) as [[LW [RW BT]] LEFT].
 destruct ann as [pc temp breakpc continuepc cursors spills saved calls]; cbn [cm_ann_cursors] in CUR; subst cursors.
 cm_ty_value_reduce; repeat match goal with |- context[if ?b then _ else _]=>cm_rt_bool b; cm_ty_value_reduce end;
 repeat first [assumption|reflexivity|exact I|match goal with |- _ /\ _=>split end].
 all: try solve [intuition].
 all: repeat match goal with H:_ /\ _|-_=>destruct H end.
 all: match goal with H:forall (result:cm_type) (v:cm_value),result = ?ty -> _|-_=>apply (H ty _ eq_refl) end.
 all: eapply cm_binary_value_type_ready; eauto.
Qed.
