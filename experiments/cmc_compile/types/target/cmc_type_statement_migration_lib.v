Require Export SimpleC.EE.QCP_demos_human.cmc_type_facts_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Ltac cm_ty_reduce := cbv beta iota zeta delta [cm_task_type_ready cm_update_s cm_sstart cm_update_annotation cm_ann_push cm_ann_cursors cm_cursors_type_ready cm_phase_static_type_ready cm_phase_parent_type_ready cm_phase_result_type_ready cm_phase_result_type cm_phase_next_fid cm_cursor_phase cm_cursor_head_input_type_ready cm_phase_input_type_ready cm_control_type_ready] in *.
Lemma cm_s_type_ready_step sp ap nilslot p fid stmt st ann :
 cm_typed_program (cm_source_function_policy sp) p -> cm_task_type_ready (cm_source_function_policy sp) nilslot p (CMSTask p fid stmt st (cm_cursor_frames (cm_ann_cursors ann))) ann ->
 cm_task_type_ready (cm_source_function_policy sp) nilslot p (cm_sstart sp p fid stmt st (cm_cursor_frames (cm_ann_cursors ann))) (cm_update_annotation (cm_update_s sp ap p fid st ann stmt)).
Proof.
 intros WF [_ [FL [FU [SW CT]]]].
 pose proof (cm_typed_function_at _ _ _ WF FL FU) as FW.
 destruct stmt; cbn [cm_stmt_wf] in SW; cm_ty_reduce;
 repeat match goal with |- context[if ?b then _ else _]=>destruct b eqn:?; cm_ty_reduce end;
 repeat first [assumption|reflexivity|exact I|match goal with |- _ /\ _=>split end|match goal with |- forall _ _,False -> _=>intros; contradiction end].
 all: try solve [intuition eauto using cm_expr_convertible_source_scalar].
 all: try solve [apply cm_cursor_expr_value_ready; cbv beta iota zeta delta [cm_cursor_head_expr_type_ready cm_phase_expr_type_ready cm_cursor_phase]; intuition].
 destruct FW as [_ [_ [LOC _]]]; destruct SW as [BOUND _].
 exact (proj1 (proj2 (LOC slot BOUND))).
Qed.
