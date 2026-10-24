(* Generated finite equation tables: see generate_updates.py and metrics/update-equations.json. *)
Require Export SimpleC.EE.QCP_demos_human.cmc_annotation_helpers_migration_lib.
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.
Definition cm_update_r (sp:cm_source_lookup_policy) (ap:cm_annotation_policy) (p:cm_program) (fid:Z) (st:cm_src_state) (ann:cm_annotation) (node:cm_expr) := match node with
 | (CMConstE n ty) =>
   (CMAUpdate 1 (cm_ann_linear (cm_push_code (cm_const_immediate ty n)) ann))
 | (CMStringE sid ty) =>
   (CMAUpdate 1 (cm_ann_linear (cm_push_code (cm_string_address p sid)) ann))
 | (CMVarE scope slot ty) =>
   (if (cm_binding_array sp p fid scope slot) then (CMAUpdate (cm_code_steps (cm_binding_address_code (cm_source_function_policy sp) p fid scope slot)) (cm_ann_linear (cm_binding_address_code (cm_source_function_policy sp) p fid scope slot) ann)) else (CMAUpdate 0 (cm_ann_push (CALoadP ty) (cm_ann_pc ann) (cm_ann_temp ann) (cm_ann_break ann) (cm_ann_continue ann) ann)))
 | (CMAssignE dst src ty) =>
   (CMAUpdate 0 (cm_ann_push (CAAssignLP src ty) (cm_ann_pc ann) (cm_ann_temp ann) (cm_ann_break ann) (cm_ann_continue ann) ann))
 | (CMBinaryE op lhs rhs ty) =>
   (CMAUpdate 0 (cm_ann_push (CABinLP op lhs rhs ty) (cm_ann_pc ann) (cm_ann_temp ann) (cm_ann_break ann) (cm_ann_continue ann) ann))
 | (CMUnaryE op arg ty) =>
   (if (op =? 2) then (CMAUpdate 0 (cm_ann_push (CALoadP ty) (cm_ann_pc ann) (cm_ann_temp ann) (cm_ann_break ann) (cm_ann_continue ann) ann)) else (if (op =? 3) then (CMAUpdate 0 ann) else (CMAUpdate 0 (cm_ann_push (CAUnaryP op) (cm_ann_pc ann) (cm_ann_temp ann) (cm_ann_break ann) (cm_ann_continue ann) ann))))
 | (CMIndexE base index ty) =>
   (CMAUpdate 0 (cm_ann_push (CALoadP ty) (cm_ann_pc ann) (cm_ann_temp ann) (cm_ann_break ann) (cm_ann_continue ann) ann))
 | (CMMemberE base mid ty) =>
   (if (cm_member_array sp p (cm_expr_type base) mid) then (CMAUpdate 0 ann) else (CMAUpdate 0 (cm_ann_push (CALoadP ty) (cm_ann_pc ann) (cm_ann_temp ann) (cm_ann_break ann) (cm_ann_continue ann) ann)))
 | (CMCallE callee args ty) =>
   (if (cm_list_empty args) then (if ((cm_call_ok sp p callee [] st) && ((cm_call_depth (cm_cursor_frames (cm_ann_cursors ann))) <? 65536)) then (CMAUpdate (S (cm_code_steps (cm_emit_prologue (cm_source_function_policy sp) p callee))) (cm_ann_enter_call sp p fid callee st ty ((cm_ann_pc ann) + 1) (cm_ann_temp ann) (cm_ann_break ann) (cm_ann_continue ann) (cm_ann_cursors ann) (cm_ann_spills ann) (cm_ann_saved ann) (cm_ann_calls ann))) else (CMAUpdate 0 ann)) else (CMAUpdate 0 (cm_ann_push (CAArgP callee (tl args) [] ty args (cm_ann_temp ann) (cm_ann_temp ann) ((cm_ann_temp ann) + (Zlength args))) (cm_ann_pc ann) ((cm_ann_temp ann) + (Zlength args)) (cm_ann_break ann) (cm_ann_continue ann) ann)))
 | (CMSizeofE asked ty) =>
   (CMAUpdate 1 (cm_ann_linear (cm_push_code (cm_type_size (cm_program_structs p) asked)) ann))
 | (CMGetcE ty) =>
   (CMAUpdate 1 (cm_ann_plain ((cm_ann_pc ann) + 1) (cm_ann_temp ann) (cm_ann_break ann) (cm_ann_continue ann) ann))
 | (CMPutcE arg ty) =>
   (CMAUpdate 0 (cm_ann_push CAPutcP (cm_ann_pc ann) (cm_ann_temp ann) (cm_ann_break ann) (cm_ann_continue ann) ann))
 | (CMPutiE arg ty) =>
   (CMAUpdate 0 (cm_ann_push CAPutiP (cm_ann_pc ann) (cm_ann_temp ann) (cm_ann_break ann) (cm_ann_continue ann) ann))
 | (CMExitE arg ty) =>
   (CMAUpdate 0 (cm_ann_push CAExitP (cm_ann_pc ann) (cm_ann_temp ann) (cm_ann_break ann) (cm_ann_continue ann) ann))
end.

Definition cm_update_l (sp:cm_source_lookup_policy) (ap:cm_annotation_policy) (p:cm_program) (fid:Z) (st:cm_src_state) (ann:cm_annotation) (node:cm_expr) := match node with
 | (CMConstE n ty) =>
   (CMAUpdate 0 ann)
 | (CMStringE sid ty) =>
   (CMAUpdate 0 ann)
 | (CMVarE scope slot ty) =>
   (CMAUpdate (cm_code_steps (cm_binding_address_code (cm_source_function_policy sp) p fid scope slot)) (cm_ann_linear (cm_binding_address_code (cm_source_function_policy sp) p fid scope slot) ann))
 | (CMAssignE dst src ty) =>
   (CMAUpdate 0 ann)
 | (CMBinaryE op lhs rhs ty) =>
   (CMAUpdate 0 ann)
 | (CMUnaryE op arg ty) =>
   (CMAUpdate 0 ann)
 | (CMIndexE base index ty) =>
   (CMAUpdate 0 (cm_ann_push (CAIndexLP index ty) (cm_ann_pc ann) (cm_ann_temp ann) (cm_ann_break ann) (cm_ann_continue ann) ann))
 | (CMMemberE base mid ty) =>
   (CMAUpdate 0 (cm_ann_push (CAMemberP mid (cm_expr_type base)) (cm_ann_pc ann) (cm_ann_temp ann) (cm_ann_break ann) (cm_ann_continue ann) ann))
 | (CMCallE callee args ty) =>
   (CMAUpdate 0 ann)
 | (CMSizeofE asked ty) =>
   (CMAUpdate 0 ann)
 | (CMGetcE ty) =>
   (CMAUpdate 0 ann)
 | (CMPutcE arg ty) =>
   (CMAUpdate 0 ann)
 | (CMPutiE arg ty) =>
   (CMAUpdate 0 ann)
 | (CMExitE arg ty) =>
   (CMAUpdate 0 ann)
end.

Definition cm_update_s (sp:cm_source_lookup_policy) (ap:cm_annotation_policy) (p:cm_program) (fid:Z) (st:cm_src_state) (ann:cm_annotation) (node:cm_stmt) := match node with
 | CMSkipS =>
   (CMAUpdate 0 ann)
 | (CMExprS expr) =>
   (CMAUpdate 0 (cm_ann_push CAExprStmtP (cm_ann_pc ann) (cm_ann_temp ann) (cm_ann_break ann) (cm_ann_continue ann) ann))
 | (CMDeclS slot) =>
   (CMAUpdate 0 ann)
 | (CMInitS slot expr) =>
   (if (cm_local_slot_ok sp p fid slot) then (CMAUpdate 0 (cm_ann_push (CAInitP slot) (cm_ann_pc ann) (cm_ann_temp ann) (cm_ann_break ann) (cm_ann_continue ann) ann)) else (CMAUpdate 0 ann))
 | (CMSeqS first second) =>
   (CMAUpdate 0 (cm_ann_push (CASeqP second) (cm_ann_pc ann) (cm_ann_temp ann) (cm_ann_break ann) (cm_ann_continue ann) ann))
 | (CMBlockS body) =>
   (CMAUpdate 0 (cm_ann_push (CABlockP (cm_state_env st) (cm_state_regions st) false 0) (cm_ann_pc ann) (cm_ann_temp ann) (cm_ann_break ann) (cm_ann_continue ann) ann))
 | (CMIfS guard yes no) =>
   (CMAUpdate 0 (cm_ann_push (CAIfP yes no) (cm_ann_pc ann) (cm_ann_temp ann) (cm_ann_break ann) (cm_ann_continue ann) ann))
 | (CMWhileS guard body) =>
   (CMAUpdate 0 (cm_ann_push (CAWhileGuardP guard body (cm_ann_pc ann) ((cm_ann_pc ann) + (cm_stmt_code_count (cm_source_function_policy sp) p fid (CMWhileS guard body)))) (cm_ann_pc ann) (cm_ann_temp ann) (cm_ann_break ann) (cm_ann_continue ann) ann))
 | CMBreakS =>
   (CMAUpdate 0 ann)
 | CMContinueS =>
   (CMAUpdate 0 ann)
 | (CMReturnS expr) =>
   (CMAUpdate 0 (cm_ann_push CAReturnP (cm_ann_pc ann) (cm_ann_temp ann) (cm_ann_break ann) (cm_ann_continue ann) ann))
end.

Definition cm_update_v (sp:cm_source_lookup_policy) (ap:cm_annotation_policy) (p:cm_program) (fid:Z) (v:cm_value) (st:cm_src_state) (ann:cm_annotation) (node:cm_aphase) := match node with
 | CAHaltP =>
   (CMAUpdate (cm_code_steps cm_status_tail_code) (cm_ann_pop ap ((cm_ann_pc ann) + (Zlength (cm_char_normalize_code CMCharTy))) ann))
 | (CALoadP ty) =>
   (CMAUpdate (cm_code_steps (cm_load_code ty)) (cm_ann_pop ap ((cm_ann_pc ann) + (Zlength (cm_load_code ty))) ann))
 | (CAAssignLP src ty) =>
   (CMAUpdate (cm_code_steps (cm_temp_store_code (cm_source_function_policy sp) p fid (cm_ann_temp ann))) (cm_ann_put_spill (cm_ann_temp ann) v (cm_ann_replace ap (CAAssignRP v ty) ((cm_ann_pc ann) + (Zlength (cm_temp_store_code (cm_source_function_policy sp) p fid (cm_ann_temp ann)))) ((cm_ann_temp ann) + 1) (cm_ann_break ann) (cm_ann_continue ann) ann)))
 | (CAAssignRP ptr ty) =>
   (CMAUpdate (cm_code_steps (cm_assign_tail_code (cm_source_function_policy sp) p fid ty (cm_cursor_temp (hd (cm_cursor_nil ap) (cm_ann_cursors ann))))) (cm_ann_pop ap ((cm_ann_pc ann) + (Zlength (cm_assign_tail_code (cm_source_function_policy sp) p fid ty (cm_cursor_temp (hd (cm_cursor_nil ap) (cm_ann_cursors ann)))))) ann))
 | (CABinLP op lhs rhs ty) =>
   (if (((op =? 0) && (cm_truth st v)) || ((op =? 1) && (negb (cm_truth st v)))) then (CMAUpdate 2 (cm_ann_pop ap (((cm_ann_pc ann) + (cm_rvalue_code_count (cm_source_function_policy sp) p fid rhs)) + 5) ann)) else (if ((op =? 0) || (op =? 1)) then (CMAUpdate 1 (cm_ann_replace ap (CABinRP op lhs rhs v ty) ((cm_ann_pc ann) + 1) (cm_ann_temp ann) (cm_ann_break ann) (cm_ann_continue ann) ann)) else (CMAUpdate (cm_code_steps (cm_temp_store_code (cm_source_function_policy sp) p fid (cm_ann_temp ann))) (cm_ann_put_spill (cm_ann_temp ann) v (cm_ann_replace ap (CABinRP op lhs rhs v ty) ((cm_ann_pc ann) + (Zlength (cm_temp_store_code (cm_source_function_policy sp) p fid (cm_ann_temp ann)))) ((cm_ann_temp ann) + 1) (cm_ann_break ann) (cm_ann_continue ann) ann)))))
 | (CABinRP op lhs rhs left_value ty) =>
   (if ((op =? 0) || (op =? 1)) then (CMAUpdate 3 (cm_ann_pop ap ((cm_ann_pc ann) + 4) ann)) else (CMAUpdate (cm_code_steps (cm_binary_finish_code (cm_source_function_policy sp) p fid op lhs rhs (cm_cursor_temp (hd (cm_cursor_nil ap) (cm_ann_cursors ann))))) (cm_ann_pop ap ((cm_ann_pc ann) + (Zlength (cm_binary_finish_code (cm_source_function_policy sp) p fid op lhs rhs (cm_cursor_temp (hd (cm_cursor_nil ap) (cm_ann_cursors ann)))))) ann)))
 | (CAUnaryP op) =>
   (CMAUpdate 2 (cm_ann_pop ap ((cm_ann_pc ann) + 2) ann))
 | (CAIndexLP index ty) =>
   (CMAUpdate (cm_code_steps (cm_temp_store_code (cm_source_function_policy sp) p fid (cm_ann_temp ann))) (cm_ann_put_spill (cm_ann_temp ann) v (cm_ann_replace ap (CAIndexRP v ty) ((cm_ann_pc ann) + (Zlength (cm_temp_store_code (cm_source_function_policy sp) p fid (cm_ann_temp ann)))) ((cm_ann_temp ann) + 1) (cm_ann_break ann) (cm_ann_continue ann) ann)))
 | (CAIndexRP base ty) =>
   (CMAUpdate (cm_code_steps (cm_index_tail_code (cm_source_function_policy sp) p fid ty (cm_cursor_temp (hd (cm_cursor_nil ap) (cm_ann_cursors ann))))) (cm_ann_pop ap ((cm_ann_pc ann) + (Zlength (cm_index_tail_code (cm_source_function_policy sp) p fid ty (cm_cursor_temp (hd (cm_cursor_nil ap) (cm_ann_cursors ann)))))) ann))
 | (CAMemberP mid base_ty) =>
   (CMAUpdate (cm_code_steps (cm_member_tail_code p base_ty mid)) (cm_ann_pop ap ((cm_ann_pc ann) + (Zlength (cm_member_tail_code p base_ty mid))) ann))
 | CAPutcP =>
   (CMAUpdate 2 (cm_ann_pop ap ((cm_ann_pc ann) + 2) ann))
 | CAPutiP =>
   (CMAUpdate 2 (cm_ann_pop ap ((cm_ann_pc ann) + 2) ann))
 | CAExitP =>
   (CMAUpdate (cm_code_steps cm_status_tail_code) (cm_ann_pop ap ((cm_ann_pc ann) + (Zlength (cm_char_normalize_code CMCharTy))) ann))
 | CAExprStmtP =>
   (CMAUpdate 1 (cm_ann_pop ap ((cm_ann_pc ann) + 1) ann))
 | (CAInitP slot) =>
   (CMAUpdate (cm_code_steps (cm_init_tail_code sp p fid slot)) (cm_ann_pop ap ((cm_ann_pc ann) + (Zlength (cm_init_tail_code sp p fid slot))) ann))
 | (CABlockP env regions jump target) =>
   (CMAUpdate 0 (cm_ann_pop ap (cm_ann_pc ann) ann))
 | (CASeqP second) =>
   (CMAUpdate 0 (cm_ann_pop ap (cm_ann_pc ann) ann))
 | (CAIfP yes no) =>
   (if (cm_truth st v) then (CMAUpdate 1 (cm_ann_replace ap (CABlockP (cm_state_env st) (cm_state_regions st) true ((((cm_ann_pc ann) + 2) + (cm_stmt_code_count (cm_source_function_policy sp) p fid yes)) + (cm_stmt_code_count (cm_source_function_policy sp) p fid no))) ((cm_ann_pc ann) + 1) (cm_cursor_temp (hd (cm_cursor_nil ap) (cm_ann_cursors ann))) (cm_cursor_break (hd (cm_cursor_nil ap) (cm_ann_cursors ann))) (cm_cursor_continue (hd (cm_cursor_nil ap) (cm_ann_cursors ann))) ann)) else (CMAUpdate 1 (cm_ann_replace ap (CABlockP (cm_state_env st) (cm_state_regions st) false ((((cm_ann_pc ann) + 2) + (cm_stmt_code_count (cm_source_function_policy sp) p fid yes)) + (cm_stmt_code_count (cm_source_function_policy sp) p fid no))) (((cm_ann_pc ann) + 2) + (cm_stmt_code_count (cm_source_function_policy sp) p fid yes)) (cm_cursor_temp (hd (cm_cursor_nil ap) (cm_ann_cursors ann))) (cm_cursor_break (hd (cm_cursor_nil ap) (cm_ann_cursors ann))) (cm_cursor_continue (hd (cm_cursor_nil ap) (cm_ann_cursors ann))) ann)))
 | (CAWhileGuardP guard body loop_start loop_end) =>
   (if (cm_truth st v) then (CMAUpdate 1 (cm_ann_replace ap (CAWhileBodyP guard body (cm_state_env st) (cm_state_regions st) loop_start loop_end) ((cm_ann_pc ann) + 1) (cm_cursor_temp (hd (cm_cursor_nil ap) (cm_ann_cursors ann))) loop_end loop_start ann)) else (CMAUpdate 1 (cm_ann_pop ap loop_end ann)))
 | (CAWhileBodyP guard body env regions loop_start loop_end) =>
   (CMAUpdate 0 (cm_ann_pop ap (cm_ann_pc ann) ann))
 | CAReturnP =>
   (CMAUpdate 0 (cm_ann_pop ap (cm_ann_pc ann) ann))
 | (CAArgP callee rest values ret all_args base_slot current_slot scratch) =>
   (if (cm_list_empty rest) then (if ((cm_call_ok sp p callee (rev (v :: values)) st) && ((cm_call_depth (cm_cursor_frames (tl (cm_ann_cursors ann)))) <? 65536)) then (CMAUpdate (cm_code_steps (cm_arg_final_code (cm_source_function_policy sp) p fid callee all_args base_slot current_slot)) (cm_ann_enter_call sp p fid callee st ret ((((cm_ann_pc ann) + (Zlength (cm_temp_store_code (cm_source_function_policy sp) p fid current_slot))) + (Zlength (cm_emit_args_reload (cm_source_function_policy sp) p fid base_slot all_args))) + 1) (cm_cursor_temp (hd (cm_cursor_nil ap) (cm_ann_cursors ann))) (cm_cursor_break (hd (cm_cursor_nil ap) (cm_ann_cursors ann))) (cm_cursor_continue (hd (cm_cursor_nil ap) (cm_ann_cursors ann))) (tl (cm_ann_cursors ann)) (cm_spill_put current_slot v (cm_ann_spills ann)) (cm_ann_saved ann) (cm_ann_calls ann))) else (CMAUpdate 0 (cm_ann_pop ap (cm_ann_pc ann) ann))) else (CMAUpdate (cm_code_steps (cm_temp_store_code (cm_source_function_policy sp) p fid current_slot)) (cm_ann_put_spill current_slot v (cm_ann_replace ap (CAArgP callee (tl rest) (v :: values) ret all_args base_slot (current_slot + 1) scratch) ((cm_ann_pc ann) + (Zlength (cm_temp_store_code (cm_source_function_policy sp) p fid current_slot))) scratch (cm_ann_break ann) (cm_ann_continue ann) ann))))
 | (CACallP caller env fp regions ret) =>
   (CMAUpdate 0 (cm_ann_pop ap (cm_ann_pc ann) ann))
end.

Definition cm_update_c (sp:cm_source_lookup_policy) (ap:cm_annotation_policy) (p:cm_program) (fid:Z) (ctl:cm_control) (st:cm_src_state) (ann:cm_annotation) (node:cm_aphase) := match node with
 | CAHaltP =>
   (CMAUpdate 0 (cm_ann_pop ap (cm_ann_pc ann) ann))
 | (CALoadP ty) =>
   (CMAUpdate 0 (cm_ann_pop ap (cm_ann_pc ann) ann))
 | (CAAssignLP src ty) =>
   (CMAUpdate 0 (cm_ann_pop ap (cm_ann_pc ann) ann))
 | (CAAssignRP ptr ty) =>
   (CMAUpdate 0 (cm_ann_pop ap (cm_ann_pc ann) ann))
 | (CABinLP op lhs rhs ty) =>
   (CMAUpdate 0 (cm_ann_pop ap (cm_ann_pc ann) ann))
 | (CABinRP op lhs rhs left_value ty) =>
   (CMAUpdate 0 (cm_ann_pop ap (cm_ann_pc ann) ann))
 | (CAUnaryP op) =>
   (CMAUpdate 0 (cm_ann_pop ap (cm_ann_pc ann) ann))
 | (CAIndexLP index ty) =>
   (CMAUpdate 0 (cm_ann_pop ap (cm_ann_pc ann) ann))
 | (CAIndexRP base ty) =>
   (CMAUpdate 0 (cm_ann_pop ap (cm_ann_pc ann) ann))
 | (CAMemberP mid base_ty) =>
   (CMAUpdate 0 (cm_ann_pop ap (cm_ann_pc ann) ann))
 | CAPutcP =>
   (CMAUpdate 0 (cm_ann_pop ap (cm_ann_pc ann) ann))
 | CAPutiP =>
   (CMAUpdate 0 (cm_ann_pop ap (cm_ann_pc ann) ann))
 | CAExitP =>
   (CMAUpdate 0 (cm_ann_pop ap (cm_ann_pc ann) ann))
 | CAExprStmtP =>
   (CMAUpdate 0 (cm_ann_pop ap (cm_ann_pc ann) ann))
 | (CAInitP slot) =>
   (CMAUpdate 0 (cm_ann_pop ap (cm_ann_pc ann) ann))
 | (CABlockP env regions jump target) =>
   (if (((cm_control_kind ctl) =? 0) && jump) then (CMAUpdate 1 (cm_ann_pop ap target ann)) else (CMAUpdate 0 (cm_ann_pop ap (cm_ann_pc ann) ann)))
 | (CASeqP second) =>
   (CMAUpdate 0 (cm_ann_pop ap (cm_ann_pc ann) ann))
 | (CAIfP yes no) =>
   (CMAUpdate 0 (cm_ann_pop ap (cm_ann_pc ann) ann))
 | (CAWhileGuardP guard body loop_start loop_end) =>
   (CMAUpdate 0 (cm_ann_pop ap (cm_ann_pc ann) ann))
 | (CAWhileBodyP guard body env regions loop_start loop_end) =>
   (if (((cm_control_kind ctl) =? 0) || ((cm_control_kind ctl) =? 2)) then (CMAUpdate 1 (cm_ann_replace ap (CAWhileGuardP guard body loop_start loop_end) loop_start (cm_cursor_temp (hd (cm_cursor_nil ap) (cm_ann_cursors ann))) loop_end loop_start ann)) else (if ((cm_control_kind ctl) =? 1) then (CMAUpdate 1 (cm_ann_pop ap loop_end ann)) else (CMAUpdate 0 (cm_ann_pop ap (cm_ann_pc ann) ann))))
 | CAReturnP =>
   (CMAUpdate 0 (cm_ann_pop ap (cm_ann_pc ann) ann))
 | (CAArgP callee rest values ret all_args base_slot current_slot scratch) =>
   (CMAUpdate 0 (cm_ann_pop ap (cm_ann_pc ann) ann))
 | (CACallP caller env fp regions ret) =>
   (if ((cm_control_kind ctl) =? 3) then (CMAUpdate (cm_code_steps (cm_return_tail_code sp p fid)) (cm_ann_leave_call ap (cm_call_sim_return (hd (cm_call_nil ap) (cm_ann_calls ann))) ann)) else (if ((cm_control_kind ctl) =? 0) then (CMAUpdate (cm_code_steps cm_fallthrough_tail_code) (cm_ann_leave_call ap (cm_call_sim_return (hd (cm_call_nil ap) (cm_ann_calls ann))) ann)) else (CMAUpdate 0 (cm_ann_leave_call ap (cm_ann_pc ann) ann))))
end.

