Require Export SimpleC.EE.QCP_demos_human.cmc_tagged_invariant_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Definition cm_member_lvalue_type p base_ty mid := CMPtrTy (cm_slot_ty (cm_slot_at mid (cm_struct_members (cm_struct_at (cm_struct_id (cm_pointee base_ty)) (cm_program_structs p))))).
Definition cm_lvalue_output_type p f expr := match expr with
 | CMVarE scope slot ty=>CMPtrTy (if scope=?0 then cm_global_ty (cm_global_at slot (cm_program_globals p)) else if scope=?1 then cm_slot_ty (cm_slot_at slot (cm_function_locals f)) else cm_slot_ty (cm_slot_at slot (cm_function_params f)))
 | CMMemberE base mid ty=>cm_member_lvalue_type p (cm_expr_type base) mid
 | _=>CMPtrTy (cm_expr_type expr) end.
Fixpoint cm_exprs_type_ready policy p f exprs : Prop := match exprs with []=>True | e::rest=>cm_expr_wf policy p f e /\ cm_scalar_expr_type (cm_expr_type e) /\ cm_exprs_type_ready policy p f rest end.
Definition cm_value_type_compatible v ty := cm_value_type v=ty \/ (v=CMNullV /\ cm_is_pointer ty).
Definition cm_expr_value_type_ready expr v := cm_value_type_compatible v (cm_expr_type expr) /\ (cm_zero_literal expr -> v=CMIntV 0).
Definition cm_value_convertible_to v ty := cm_convertible (cm_value_type v) ty \/ (v=CMIntV 0 /\ cm_is_pointer ty).
(* Explicit interpretation of HOL HD [] for slot lists. No property of it is assumed. *)
Fixpoint cm_arg_next_type (nilslot:cm_slot_d) slots (done:list cm_value) := match done with []=>cm_slot_ty (hd nilslot slots) | _::rest=>cm_arg_next_type nilslot (tl slots) rest end.
Fixpoint cm_arg_progress_type_ready (nilslot:cm_slot_d) (all_args:list cm_expr) slots done (rest:list cm_expr) : Prop := match done with
 | []=>all_args<>[] /\ slots<>[] /\ tl all_args=rest
 | v::vs=>all_args<>[] /\ slots<>[] /\ cm_value_convertible_to v (cm_slot_ty (hd nilslot slots)) /\ cm_arg_progress_type_ready nilslot (tl all_args) (tl slots) vs rest end.
Definition cm_phase_input_type_ready (p:cm_program) (fid:Z) phase incoming : Prop := match phase with
 | CAHaltP | CAAssignRP _ _ | CAInitP _ | CAReturnP | CAArgP _ _ _ _ _ _ _ _=>True
 | CALoadP ty | CAAssignLP _ ty | CAIndexLP _ ty=>incoming=CMPtrTy ty
 | CABinLP _ lhs _ _=>incoming=cm_expr_type lhs
 | CABinRP _ _ rhs _ _=>incoming=cm_expr_type rhs
 | CAUnaryP _ | CAIndexRP _ _ | CAPutiP | CAExitP=>cm_integer_type incoming
 | CAMemberP _ ty=>incoming=ty
 | CAPutcP | CAExprStmtP | CAIfP _ _ | CAWhileGuardP _ _ _ _=>cm_scalar_expr_type incoming
 | _=>False end.
Definition cm_cursor_head_input_type_ready p fid incoming cursors : Prop := match cursors with []=>False | c::_=>cm_phase_input_type_ready p fid (cm_cursor_phase c) incoming end.
Definition cm_phase_value_type_ready policy nilslot p fid phase v : Prop := match phase with
 | CAHaltP=>True
 | CALoadP ty | CAAssignLP _ ty | CAIndexLP _ ty=>cm_value_type_compatible v (CMPtrTy ty)
 | CAAssignRP _ ty=>cm_value_convertible_to v ty
 | CABinLP _ lhs _ _=>cm_value_type_compatible v (cm_expr_type lhs)
 | CABinRP _ _ rhs _ _=>cm_value_type_compatible v (cm_expr_type rhs)
 | CAUnaryP _ | CAIndexRP _ _ | CAPutiP | CAExitP=>cm_integer_type (cm_value_type v)
 | CAMemberP _ ty=>cm_value_type_compatible v ty
 | CAPutcP | CAExprStmtP | CAIfP _ _ | CAWhileGuardP _ _ _ _=>cm_scalar_expr_type (cm_value_type v)
 | CAInitP slot=>cm_value_convertible_to v (cm_slot_ty (cm_slot_at slot (cm_function_locals (cm_function_at policy fid (cm_program_functions p)))))
 | CAReturnP=>cm_value_convertible_to v (cm_function_ret (cm_function_at policy fid (cm_program_functions p)))
 | CAArgP callee _ values _ _ _ _ _=>cm_value_convertible_to v (cm_arg_next_type nilslot (cm_function_params (cm_function_at policy callee (cm_program_functions p))) (rev values))
 | _=>False end.
Definition cm_control_type_ready policy p fid ctl : Prop := match ctl with CMReturn v=>cm_value_convertible_to v (cm_function_ret (cm_function_at policy fid (cm_program_functions p))) | _=>True end.
Definition cm_cursor_head_value_type_ready policy nilslot p fid v cursors : Prop := match cursors with []=>False | c::_=>cm_phase_value_type_ready policy nilslot p fid (cm_cursor_phase c) v end.
Definition cm_phase_result_type (p:cm_program) (fid:Z) phase result : Prop := match phase with
 | CALoadP ty | CAAssignLP _ ty | CAAssignRP _ ty | CABinLP _ _ _ ty | CABinRP _ _ _ _ ty | CAArgP _ _ _ ty _ _ _ _ | CACallP _ _ _ _ ty=>result=ty
 | CAUnaryP _ | CAPutcP | CAPutiP=>result=CMIntTy
 | CAIndexLP _ ty | CAIndexRP _ ty=>result=CMPtrTy ty
 | CAMemberP mid ty=>result=cm_member_lvalue_type p ty mid
 | _=>False end.
Definition cm_phase_result_type_ready policy nilslot p fid phase rest : Prop := forall result v,cm_phase_result_type p fid phase result -> cm_value_type_compatible v result -> cm_cursor_head_value_type_ready policy nilslot p (cm_phase_next_fid fid phase) v rest.
Definition cm_phase_expr_type_ready policy nilslot p fid phase expr : Prop := match phase with
 | CAHaltP=>True
 | CALoadP ty | CAAssignLP _ ty | CAIndexLP _ ty=>cm_expr_type expr=CMPtrTy ty
 | CAAssignRP _ ty=>cm_expr_convertible expr ty
 | CABinLP _ lhs _ _=>cm_expr_type expr=cm_expr_type lhs
 | CABinRP _ _ rhs _ _=>cm_expr_type expr=cm_expr_type rhs
 | CAUnaryP _ | CAIndexRP _ _ | CAPutiP | CAExitP=>cm_integer_type (cm_expr_type expr)
 | CAMemberP _ ty=>cm_expr_type expr=ty
 | CAPutcP | CAExprStmtP | CAIfP _ _ | CAWhileGuardP _ _ _ _=>cm_scalar_expr_type (cm_expr_type expr)
 | CAInitP slot=>cm_expr_convertible expr (cm_slot_ty (cm_slot_at slot (cm_function_locals (cm_function_at policy fid (cm_program_functions p)))))
 | CAReturnP=>cm_expr_convertible expr (cm_function_ret (cm_function_at policy fid (cm_program_functions p)))
 | CAArgP callee _ values _ _ _ _ _=>cm_expr_convertible expr (cm_arg_next_type nilslot (cm_function_params (cm_function_at policy callee (cm_program_functions p))) (rev values))
 | _=>False end.
Definition cm_cursor_head_expr_type_ready policy nilslot p fid expr cursors : Prop := match cursors with []=>False | c::_=>cm_phase_expr_type_ready policy nilslot p fid (cm_cursor_phase c) expr end.
Definition cm_cursor_expr_values_type_ready policy nilslot p fid expr cursors : Prop := forall v,cm_expr_value_type_ready expr v -> cm_cursor_head_value_type_ready policy nilslot p fid v cursors.
Definition cm_phase_lvalue_type_ready policy nilslot p fid phase output : Prop := forall v,cm_value_type_compatible v output -> cm_phase_value_type_ready policy nilslot p fid phase v.
Definition cm_cursor_head_lvalue_type_ready policy nilslot p fid output cursors : Prop := match cursors with []=>False | c::_=>cm_phase_lvalue_type_ready policy nilslot p fid (cm_cursor_phase c) output end.
