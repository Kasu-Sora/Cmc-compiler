Require Export SimpleC.EE.QCP_demos_human.cmc_type_invariant_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Definition cm_emit_rvalue policy p fid pc temp expr := cm_expr_code_for policy p fid pc temp expr 0.
Definition cm_emit_lvalue policy p fid pc temp expr := cm_expr_code_for policy p fid pc temp expr 1.
Definition cm_value_phase_code (sp:cm_source_lookup_policy) (p:cm_program) (fid pc temp owner breakpc continuepc:Z) (phase:cm_aphase) := match phase with
 | CAHaltP => cm_status_tail_code
 | (CALoadP ty) => (cm_load_code ty)
 | (CAAssignLP src ty) => ((cm_temp_store_code (cm_source_function_policy sp) p fid owner) ++ ((cm_emit_rvalue (cm_source_function_policy sp) p fid (pc + (Zlength (cm_temp_store_code (cm_source_function_policy sp) p fid owner))) (owner + 1) src) ++ (cm_assign_tail_code (cm_source_function_policy sp) p fid ty owner)))
 | (CAAssignRP ptr ty) => (cm_assign_tail_code (cm_source_function_policy sp) p fid ty owner)
 | (CABinLP op lhs rhs ty) => (if ((op =? 0) || (op =? 1)) then ([(TVMInst (if (op =? 0) then TVMJnzOp else TVMJzOp) ((pc + (cm_rvalue_code_count (cm_source_function_policy sp) p fid rhs)) + 4))] ++ ((cm_emit_rvalue (cm_source_function_policy sp) p fid (pc + 1) owner rhs) ++ [(TVMInst TVMPushOp 0); (TVMInst TVMNeOp 0); (TVMInst TVMJmpOp ((pc + (cm_rvalue_code_count (cm_source_function_policy sp) p fid rhs)) + 5)); (TVMInst TVMPushOp (if (op =? 0) then 1 else 0))])) else ((cm_temp_store_code (cm_source_function_policy sp) p fid owner) ++ ((cm_emit_rvalue (cm_source_function_policy sp) p fid (pc + (Zlength (cm_temp_store_code (cm_source_function_policy sp) p fid owner))) (owner + 1) rhs) ++ (cm_binary_finish_code (cm_source_function_policy sp) p fid op lhs rhs owner))))
 | (CABinRP op lhs rhs value ty) => (if ((op =? 0) || (op =? 1)) then [(TVMInst TVMPushOp 0); (TVMInst TVMNeOp 0); (TVMInst TVMJmpOp (pc + 4)); (TVMInst TVMPushOp (if (op =? 0) then 1 else 0))] else (cm_binary_finish_code (cm_source_function_policy sp) p fid op lhs rhs owner))
 | (CAUnaryP op) => [(TVMInst TVMPushOp (if (op =? 0) then (- 1) else 0)); (TVMInst (if (op =? 0) then TVMMulOp else TVMEqOp) 0)]
 | (CAIndexLP index ty) => ((cm_temp_store_code (cm_source_function_policy sp) p fid owner) ++ ((cm_emit_rvalue (cm_source_function_policy sp) p fid (pc + (Zlength (cm_temp_store_code (cm_source_function_policy sp) p fid owner))) (owner + 1) index) ++ (cm_index_tail_code (cm_source_function_policy sp) p fid ty owner)))
 | (CAIndexRP base ty) => (cm_index_tail_code (cm_source_function_policy sp) p fid ty owner)
 | (CAMemberP mid base_ty) => (cm_member_tail_code p base_ty mid)
 | CAPutcP => [(TVMInst TVMDupOp 0); (TVMInst TVMPutcOp 0)]
 | CAPutiP => [(TVMInst TVMDupOp 0); (TVMInst TVMPutiOp 0)]
 | CAExitP => cm_status_tail_code
 | CAExprStmtP => [(TVMInst TVMPopOp 0)]
 | (CAInitP slot) => (cm_init_tail_code sp p fid slot)
 | (CABlockP env regions jump target) => (if jump then [(TVMInst TVMJmpOp target)] else [])
 | (CASeqP second) => (cm_emit_stmt (cm_source_function_policy sp) p fid pc owner breakpc continuepc second)
 | (CAIfP yes no) => ([(TVMInst TVMJzOp (((pc + 1) + (cm_stmt_code_count (cm_source_function_policy sp) p fid yes)) + 1))] ++ ((cm_emit_stmt (cm_source_function_policy sp) p fid (pc + 1) owner breakpc continuepc yes) ++ ([(TVMInst TVMJmpOp (((pc + 2) + (cm_stmt_code_count (cm_source_function_policy sp) p fid yes)) + (cm_stmt_code_count (cm_source_function_policy sp) p fid no)))] ++ (cm_emit_stmt (cm_source_function_policy sp) p fid ((pc + 2) + (cm_stmt_code_count (cm_source_function_policy sp) p fid yes)) owner breakpc continuepc no))))
 | (CAWhileGuardP guard body loop_start loop_end) => ([(TVMInst TVMJzOp loop_end)] ++ ((cm_emit_stmt (cm_source_function_policy sp) p fid (pc + 1) owner loop_end loop_start body) ++ [(TVMInst TVMJmpOp loop_start)]))
 | (CAWhileBodyP guard body env regions loop_start loop_end) => [(TVMInst TVMJmpOp loop_start)]
 | CAReturnP => (cm_return_tail_code sp p fid)
 | (CAArgP callee rest values ret all_args base_slot current_slot scratch) => ((cm_temp_store_code (cm_source_function_policy sp) p fid current_slot) ++ ((cm_emit_args_store (cm_source_function_policy sp) p fid (pc + (Zlength (cm_temp_store_code (cm_source_function_policy sp) p fid current_slot))) (current_slot + 1) scratch rest) ++ ((cm_emit_args_reload (cm_source_function_policy sp) p fid base_slot all_args) ++ [(TVMInst TVMCallOp (cm_function_pc (cm_source_function_policy sp) p callee))])))
 | (CACallP caller env fp regions ret) => (cm_return_tail_code sp p fid)
end.

Definition cm_phase_stops (phase:cm_aphase) := match phase with
 | CAHaltP => true
 | (CALoadP ty) => false
 | (CAAssignLP src ty) => false
 | (CAAssignRP ptr ty) => false
 | (CABinLP op lhs rhs ty) => false
 | (CABinRP op lhs rhs value ty) => false
 | (CAUnaryP op) => false
 | (CAIndexLP index ty) => false
 | (CAIndexRP base ty) => false
 | (CAMemberP mid base_ty) => false
 | CAPutcP => false
 | CAPutiP => false
 | CAExitP => true
 | CAExprStmtP => false
 | (CAInitP slot) => false
 | (CABlockP env regions jump target) => jump
 | (CASeqP second) => false
 | (CAIfP yes no) => false
 | (CAWhileGuardP guard body loop_start loop_end) => false
 | (CAWhileBodyP guard body env regions loop_start loop_end) => false
 | CAReturnP => true
 | (CAArgP callee rest values ret all_args base_slot current_slot scratch) => false
 | (CACallP caller env fp regions ret) => true
end.

Definition cm_phase_yields_normal (phase:cm_aphase) := match phase with
 | CAHaltP => false
 | (CALoadP ty) => false
 | (CAAssignLP src ty) => false
 | (CAAssignRP ptr ty) => false
 | (CABinLP op lhs rhs ty) => false
 | (CABinRP op lhs rhs value ty) => false
 | (CAUnaryP op) => false
 | (CAIndexLP index ty) => false
 | (CAIndexRP base ty) => false
 | (CAMemberP mid base_ty) => false
 | CAPutcP => false
 | CAPutiP => false
 | CAExitP => false
 | CAExprStmtP => true
 | (CAInitP slot) => true
 | (CABlockP env regions jump target) => true
 | (CASeqP second) => true
 | (CAIfP yes no) => true
 | (CAWhileGuardP guard body loop_start loop_end) => true
 | (CAWhileBodyP guard body env regions loop_start loop_end) => true
 | CAReturnP => false
 | (CAArgP callee rest values ret all_args base_slot current_slot scratch) => false
 | (CACallP caller env fp regions ret) => false
end.

Definition cm_normal_phase_code (sp:cm_source_lookup_policy) (p:cm_program) (fid pc temp owner breakpc continuepc:Z) (phase:cm_aphase) := match phase with
 | CAHaltP => []
 | (CALoadP ty) => []
 | (CAAssignLP src ty) => []
 | (CAAssignRP ptr ty) => []
 | (CABinLP op lhs rhs ty) => []
 | (CABinRP op lhs rhs value ty) => []
 | (CAUnaryP op) => []
 | (CAIndexLP index ty) => []
 | (CAIndexRP base ty) => []
 | (CAMemberP mid base_ty) => []
 | CAPutcP => []
 | CAPutiP => []
 | CAExitP => []
 | CAExprStmtP => []
 | (CAInitP slot) => []
 | (CABlockP env regions jump target) => (if jump then [(TVMInst TVMJmpOp target)] else [])
 | (CASeqP second) => (cm_emit_stmt (cm_source_function_policy sp) p fid pc owner breakpc continuepc second)
 | (CAIfP yes no) => []
 | (CAWhileGuardP guard body loop_start loop_end) => []
 | (CAWhileBodyP guard body env regions loop_start loop_end) => [(TVMInst TVMJmpOp loop_start)]
 | CAReturnP => []
 | (CAArgP callee rest values ret all_args base_slot current_slot scratch) => []
 | (CACallP caller env fp regions ret) => cm_fallthrough_tail_code
end.

Definition cm_normal_phase_stops (phase:cm_aphase) := match phase with
 | CAHaltP => true
 | (CALoadP ty) => false
 | (CAAssignLP src ty) => false
 | (CAAssignRP ptr ty) => false
 | (CABinLP op lhs rhs ty) => false
 | (CABinRP op lhs rhs value ty) => false
 | (CAUnaryP op) => false
 | (CAIndexLP index ty) => false
 | (CAIndexRP base ty) => false
 | (CAMemberP mid base_ty) => false
 | CAPutcP => false
 | CAPutiP => false
 | CAExitP => true
 | CAExprStmtP => false
 | (CAInitP slot) => false
 | (CABlockP env regions jump target) => jump
 | (CASeqP second) => false
 | (CAIfP yes no) => false
 | (CAWhileGuardP guard body loop_start loop_end) => false
 | (CAWhileBodyP guard body env regions loop_start loop_end) => false
 | CAReturnP => false
 | (CAArgP callee rest values ret all_args base_slot current_slot scratch) => false
 | (CACallP caller env fp regions ret) => true
end.

