Require Export SimpleC.EE.QCP_demos_human.cmc_type_expr_struct_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Lemma cm_pointer_pointee_type ty : cm_is_pointer ty -> ty=CMPtrTy (cm_pointee ty).
Proof. destruct ty; cbn [cm_is_pointer cm_pointee]; intuition. Qed.
Lemma cm_r_unary_type_ready_step sp ap nilslot p fid op arg ty st ks ann :
 cm_typed_program (cm_source_function_policy sp) p ->
 cm_task_type_ready (cm_source_function_policy sp) nilslot p (CMRTask p fid (CMUnaryE op arg ty) st ks) ann ->
 cm_task_type_ready (cm_source_function_policy sp) nilslot p (cm_rstart sp p fid (CMUnaryE op arg ty) st ks) (cm_update_annotation (cm_update_r sp ap p fid st ann (CMUnaryE op arg ty))).
Proof.
 intros WF [_ [FL [FU [EW [SC [CT [IN VAL]]]]]]].
 pose proof (cm_typed_function_at _ _ _ WF FL FU) as FW.
 pose proof (cm_nonzero_cursor_values _ _ _ _ (CMUnaryE op arg ty) _ ltac:(discriminate) VAL) as RESULT.
 destruct EW as [AW [[BOUND UT] LVAL]].
 assert (CASES:op=0 \/ op=1 \/ op=2 \/ op=3) by lia.
 destruct CASES as [-> | [-> | [-> | ->]]];
 cbv beta iota zeta delta [Z.eqb Pos.eqb orb] in UT;
 cm_ty_expr_reduce; cbv beta iota zeta delta [Z.eqb Pos.eqb] in *; cm_ty_reduce.
 all: try match goal with UT:cm_integer_type _ /\ _|-_=>destruct UT as [ARGINT TY]; rewrite TY in * end.
 all: try match goal with UT:cm_is_pointer _ /\ _|-_=>destruct UT as [ARGPTR TY]; pose proof (cm_pointer_pointee_type _ ARGPTR) as PT; rewrite <-TY in PT end.
 all: try solve [
 repeat first [assumption|reflexivity|exact I|match goal with |- _ /\ _=>split end];
 try solve [now left|lia|intros result v -> V; apply RESULT; exact V|
 apply cm_cursor_expr_value_ready; cbv beta iota delta [cm_cursor_head_expr_type_ready cm_phase_expr_type_ready cm_cursor_phase]; assumption]].
 - repeat first [assumption|reflexivity|exact I|match goal with |- _ /\ _=>split end].
   + now right.
   + intros result v -> V; apply RESULT; exact V.
   + apply cm_cursor_expr_value_ready; cbv beta iota delta [cm_cursor_head_expr_type_ready cm_phase_expr_type_ready cm_cursor_phase]; exact PT.
 - destruct (LVAL eq_refl) as [LV NA].
   pose proof (cm_nonarray_lvalue_output _ _ _ _ FW AW NA) as OUT.
   rewrite OUT; unfold cm_expr_type; rewrite <-UT.
   repeat first [assumption|reflexivity|exact I|match goal with |- _ /\ _=>split end].
   fold (cm_ann_cursors ann) in *.
   destruct (cm_ann_cursors ann) as [|c rest]; [contradiction|].
   cbv beta iota delta [cm_cursor_head_lvalue_type_ready cm_phase_lvalue_type_ready]; intros v V; apply RESULT; exact V.
Qed.
