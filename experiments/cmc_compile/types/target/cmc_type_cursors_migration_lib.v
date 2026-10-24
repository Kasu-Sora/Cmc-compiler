Require Export SimpleC.EE.QCP_demos_human.cmc_type_values_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Definition cm_phase_static_type_ready policy nilslot p fid phase : Prop :=
 let f:=cm_function_at policy fid (cm_program_functions p) in match phase with
 | CALoadP ty=>cm_scalar_expr_type ty
 | CAAssignLP src ty=>cm_expr_wf policy p f src /\ cm_expr_convertible src ty /\ cm_scalar_expr_type ty
 | CAAssignRP ptr ty=>cm_value_type_compatible ptr (CMPtrTy ty) /\ cm_scalar_expr_type ty
 | CABinLP op lhs rhs ty=>cm_expr_wf policy p f (CMBinaryE op lhs rhs ty)
 | CABinRP op lhs rhs v ty=>cm_expr_wf policy p f (CMBinaryE op lhs rhs ty) /\ cm_value_type_compatible v (cm_expr_type lhs)
 | CAUnaryP op=>op=0 \/ op=1
 | CAIndexLP index ty=>cm_expr_wf policy p f index /\ cm_integer_type (cm_expr_type index) /\ cm_type_refs (cm_program_structs p) ty
 | CAIndexRP base ty=>cm_value_type_compatible base (CMPtrTy ty) /\ cm_type_refs (cm_program_structs p) ty
 | CAMemberP mid ty=>cm_member_valid p ty mid
 | CAInitP slot=>0<=slot /\ slot<Zlength (cm_function_locals f) /\ cm_slot_count (cm_slot_at slot (cm_function_locals f))=0 /\ cm_scalar_type (cm_program_structs p) (cm_slot_ty (cm_slot_at slot (cm_function_locals f)))
 | CASeqP second=>cm_stmt_wf policy p f true second
 | CAIfP yes no=>cm_stmt_wf policy p f true yes /\ cm_stmt_wf policy p f true no
 | CAWhileGuardP guard body _ _ | CAWhileBodyP guard body _ _ _ _=>cm_expr_wf policy p f guard /\ cm_scalar_expr_type (cm_expr_type guard) /\ cm_stmt_wf policy p f true body
 | CAArgP callee rest values ret all_args _ _ _=>0<=callee /\ callee<Zlength (cm_program_functions p) /\ cm_exprs_type_ready policy p f rest /\ cm_args_wf policy p f all_args (cm_function_params (cm_function_at policy callee (cm_program_functions p))) /\ cm_arg_progress_type_ready nilslot all_args (cm_function_params (cm_function_at policy callee (cm_program_functions p))) (rev values) rest /\ ret=cm_function_ret (cm_function_at policy callee (cm_program_functions p))
 | CACallP caller _ _ _ ret=>0<=fid /\ fid<Zlength (cm_program_functions p) /\ (caller= -1 \/ (0<=caller /\ caller<Zlength (cm_program_functions p))) /\ ret=cm_function_ret f
 | _=>True end.
Definition cm_phase_parent_type_ready p fid phase rest : Prop := match phase with
 | CAHaltP=>rest=[]
 | CALoadP ty | CAAssignLP _ ty | CAAssignRP _ ty | CABinLP _ _ _ ty | CABinRP _ _ _ _ ty | CAArgP _ _ _ ty _ _ _ _=>cm_cursor_head_input_type_ready p fid ty rest
 | CAUnaryP _ | CAPutcP | CAPutiP=>cm_cursor_head_input_type_ready p fid CMIntTy rest
 | CAIndexLP _ ty | CAIndexRP _ ty=>cm_cursor_head_input_type_ready p fid (CMPtrTy ty) rest
 | CAMemberP mid ty=>cm_cursor_head_input_type_ready p fid (cm_member_lvalue_type p ty mid) rest
 | CACallP caller _ _ _ ret=>cm_cursor_head_input_type_ready p caller ret rest
 | _=>True end.
Fixpoint cm_cursors_type_ready policy nilslot p fid cursors : Prop := match cursors with
 | []=>True
 | c::rest=>cm_phase_static_type_ready policy nilslot p fid (cm_cursor_phase c) /\ cm_phase_parent_type_ready p fid (cm_cursor_phase c) rest /\ cm_phase_result_type_ready policy nilslot p fid (cm_cursor_phase c) rest /\ cm_cursors_type_ready policy nilslot p (cm_phase_next_fid fid (cm_cursor_phase c)) rest end.
Definition cm_task_type_ready policy nilslot p task ann : Prop := match task with
 | CMStartTask q _=>q=p
 | CMRTask q fid expr _ _=>q=p /\ 0<=fid /\ fid<Zlength (cm_program_functions p) /\ cm_expr_wf policy p (cm_function_at policy fid (cm_program_functions p)) expr /\ cm_scalar_expr_type (cm_expr_type expr) /\ cm_cursors_type_ready policy nilslot p fid (cm_ann_cursors ann) /\ cm_cursor_head_input_type_ready p fid (cm_expr_type expr) (cm_ann_cursors ann) /\ cm_cursor_expr_values_type_ready policy nilslot p fid expr (cm_ann_cursors ann)
 | CMLTask q fid expr _ _=>q=p /\ 0<=fid /\ fid<Zlength (cm_program_functions p) /\ cm_expr_wf policy p (cm_function_at policy fid (cm_program_functions p)) expr /\ cm_lvalue expr /\ cm_cursors_type_ready policy nilslot p fid (cm_ann_cursors ann) /\ cm_cursor_head_input_type_ready p fid (cm_lvalue_output_type p (cm_function_at policy fid (cm_program_functions p)) expr) (cm_ann_cursors ann) /\ cm_cursor_head_lvalue_type_ready policy nilslot p fid (cm_lvalue_output_type p (cm_function_at policy fid (cm_program_functions p)) expr) (cm_ann_cursors ann)
 | CMSTask q fid stmt _ _=>q=p /\ 0<=fid /\ fid<Zlength (cm_program_functions p) /\ cm_stmt_wf policy p (cm_function_at policy fid (cm_program_functions p)) true stmt /\ cm_cursors_type_ready policy nilslot p fid (cm_ann_cursors ann)
 | CMVTask q fid v _ _=>q=p /\ cm_cursors_type_ready policy nilslot p fid (cm_ann_cursors ann) /\ cm_cursor_head_value_type_ready policy nilslot p fid v (cm_ann_cursors ann)
 | CMCTask q fid ctl _ _=>q=p /\ cm_control_type_ready policy p fid ctl /\ cm_cursors_type_ready policy nilslot p fid (cm_ann_cursors ann)
 | CMDoneTask _ _ _=>True end.
