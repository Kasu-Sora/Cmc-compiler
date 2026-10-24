#include "cmc_layout_migration_abi.h"

/*@ Extern Coq
    (bool :: *)
    (cm_type :: *)
    (cm_expr :: *)
    (cm_stmt :: *)
    (cm_slot_d :: *)
    (cm_struct_d :: *)
    (cm_global_d :: *)
    (cm_string_d :: *)
    (cm_function_d :: *)
    (cm_program :: *)
    (cm_lookup_policy :: *)
    (cm_codegen_obligations :: *)
*/
/*@ Extern Coq
    (cm_type_encode : cm_type -> Z)
    (cm_expr_type : cm_expr -> cm_type)
    (cm_expr_rep : Z -> cm_expr -> Assertion)
    (cm_stmt_rep : Z -> cm_stmt -> Assertion)
    (cm_expr_payload : cm_expr -> Z -> Z -> Z -> Assertion)
    (cm_rep_expr_kind : cm_expr -> Z)
    (cm_rep_expr_op : cm_expr -> Z)
    (cm_rep_expr_value : cm_expr -> Z)
    (cm_program_globals : cm_program -> list cm_global_d)
    (cm_program_structs : cm_program -> list cm_struct_d)
    (cm_program_strings : cm_program -> list cm_string_d)
    (cm_program_functions : cm_program -> list cm_function_d)
    (cm_program_main : cm_program -> Z)
    (cm_function_locals : cm_function_d -> list cm_slot_d)
    (cm_function_params : cm_function_d -> list cm_slot_d)
    (cm_function_ret : cm_function_d -> cm_type)
    (cm_function_at : cm_lookup_policy -> Z -> list cm_function_d -> cm_function_d)
    (cm_struct_list_rep : Z -> list cm_struct_d -> Assertion)
    (cm_global_list_rep : Z -> list cm_global_d -> Assertion)
    (cm_string_list_rep : Z -> list cm_string_d -> Assertion)
    (cm_slot_list_rep : Z -> list cm_slot_d -> Assertion)
    (cm_rep_structs_safe : list cm_struct_d -> Prop)
    (cm_wf_program : cm_lookup_policy -> cm_codegen_obligations -> cm_program -> Prop)
    (cm_expr_wf : cm_lookup_policy -> cm_program -> cm_function_d -> cm_expr -> Prop)
    (cm_stmt_wf : cm_lookup_policy -> cm_program -> cm_function_d -> bool -> cm_stmt -> Prop)
    (cm_expr_counts_representable : cm_lookup_policy -> cm_program -> Z -> cm_expr -> Prop)
    (cm_stmt_counts_representable : cm_lookup_policy -> cm_program -> Z -> cm_stmt -> Prop)
    (cm_lvalue_code_count : cm_lookup_policy -> cm_program -> Z -> cm_expr -> Z)
    (cm_rvalue_code_count : cm_lookup_policy -> cm_program -> Z -> cm_expr -> Z)
    (cm_stmt_code_count : cm_lookup_policy -> cm_program -> Z -> cm_stmt -> Z)
    (cm_i32_code_count : Z -> Prop)
    (cm_program_context_rep : Z -> cm_program -> Z -> Assertion)
    (cm_function_context_rep : Z -> cm_function_d -> Z -> Z -> Assertion)
*/
/*@ Import Coq Require Import SimpleC.EE.QCP_demos_human.cmc_count_context_migration_lib */

int cm_expr_lvalue_count(struct cm_program *program, int fid,
                                struct cm_function *fn,
                                struct cm_expr *expr)
/*@ With (policy : cm_lookup_policy) (cg : cm_codegen_obligations) (p : cm_program) (f : cm_function_d) (structs : list cm_struct_d) (globals : list cm_global_d) (locals : list cm_slot_d) (zs : Z) (zg : Z) (zl : Z) (e : cm_expr)
    Require cm_wf_program(policy, cg, p) && f == cm_function_at(policy, fid, cm_program_functions(p)) && structs == cm_program_structs(p) && globals == cm_program_globals(p) && locals == cm_function_locals(f) && cm_rep_structs_safe(structs) && cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) && data_at(&(program->structs), struct cm_struct *, zs) * cm_struct_list_rep(zs, structs) * data_at(&(program->globals), struct cm_global *, zg) * cm_global_list_rep(zg, globals) * data_at(&(fn->locals), struct cm_slot *, zl) * cm_slot_list_rep(zl, locals) * cm_expr_rep(expr, e)
    Ensure cm_wf_program(policy, cg, p) && f == cm_function_at(policy, fid, cm_program_functions(p)) && structs == cm_program_structs(p) && globals == cm_program_globals(p) && locals == cm_function_locals(f) && cm_rep_structs_safe(structs) && cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) && __return == cm_lvalue_code_count(policy, p, fid, e) && cm_i32_code_count(__return) && data_at(&(program->structs), struct cm_struct *, zs) * cm_struct_list_rep(zs, structs) * data_at(&(program->globals), struct cm_global *, zg) * cm_global_list_rep(zg, globals) * data_at(&(fn->locals), struct cm_slot *, zl) * cm_slot_list_rep(zl, locals) * cm_expr_rep(expr, e)
*/
;

int cm_expr_rvalue_count(struct cm_program *program, int fid,
                                struct cm_function *fn,
                                struct cm_expr *expr)
/*@ With (policy : cm_lookup_policy) (cg : cm_codegen_obligations) (p : cm_program) (f : cm_function_d) (structs : list cm_struct_d) (globals : list cm_global_d) (locals : list cm_slot_d) (zs : Z) (zg : Z) (zl : Z) (e : cm_expr)
    Require cm_wf_program(policy, cg, p) && f == cm_function_at(policy, fid, cm_program_functions(p)) && structs == cm_program_structs(p) && globals == cm_program_globals(p) && locals == cm_function_locals(f) && cm_rep_structs_safe(structs) && cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) && data_at(&(program->structs), struct cm_struct *, zs) * cm_struct_list_rep(zs, structs) * data_at(&(program->globals), struct cm_global *, zg) * cm_global_list_rep(zg, globals) * data_at(&(fn->locals), struct cm_slot *, zl) * cm_slot_list_rep(zl, locals) * cm_expr_rep(expr, e)
    Ensure cm_wf_program(policy, cg, p) && f == cm_function_at(policy, fid, cm_program_functions(p)) && structs == cm_program_structs(p) && globals == cm_program_globals(p) && locals == cm_function_locals(f) && cm_rep_structs_safe(structs) && cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) && __return == cm_rvalue_code_count(policy, p, fid, e) && cm_i32_code_count(__return) && data_at(&(program->structs), struct cm_struct *, zs) * cm_struct_list_rep(zs, structs) * data_at(&(program->globals), struct cm_global *, zg) * cm_global_list_rep(zg, globals) * data_at(&(fn->locals), struct cm_slot *, zl) * cm_slot_list_rep(zl, locals) * cm_expr_rep(expr, e)
*/
;

int cmc_stmt_code_count(struct cm_program *program, int fid,
                               struct cm_function *fn,
                               struct cm_stmt *stmt)
/*@ With (policy : cm_lookup_policy) (cg : cm_codegen_obligations) (p : cm_program) (f : cm_function_d) (structs : list cm_struct_d) (globals : list cm_global_d) (locals : list cm_slot_d) (zs : Z) (zg : Z) (zl : Z) (s : cm_stmt) (loop_ : bool)
    Require cm_wf_program(policy, cg, p) && f == cm_function_at(policy, fid, cm_program_functions(p)) && structs == cm_program_structs(p) && globals == cm_program_globals(p) && locals == cm_function_locals(f) && cm_rep_structs_safe(structs) && cm_stmt_wf(policy, p, f, loop_, s) && cm_stmt_counts_representable(policy, p, fid, s) && data_at(&(program->structs), struct cm_struct *, zs) * cm_struct_list_rep(zs, structs) * data_at(&(program->globals), struct cm_global *, zg) * cm_global_list_rep(zg, globals) * data_at(&(fn->locals), struct cm_slot *, zl) * cm_slot_list_rep(zl, locals) * data_at(&(fn->ret_ty), int, cm_type_encode(cm_function_ret(f))) * cm_stmt_rep(stmt, s)
    Ensure cm_wf_program(policy, cg, p) && f == cm_function_at(policy, fid, cm_program_functions(p)) && structs == cm_program_structs(p) && globals == cm_program_globals(p) && locals == cm_function_locals(f) && cm_rep_structs_safe(structs) && cm_stmt_wf(policy, p, f, loop_, s) && cm_stmt_counts_representable(policy, p, fid, s) && __return == cm_stmt_code_count(policy, p, fid, s) && cm_i32_code_count(cm_stmt_code_count(policy, p, fid, s)) && data_at(&(program->structs), struct cm_struct *, zs) * cm_struct_list_rep(zs, structs) * data_at(&(program->globals), struct cm_global *, zg) * cm_global_list_rep(zg, globals) * data_at(&(fn->locals), struct cm_slot *, zl) * cm_slot_list_rep(zl, locals) * data_at(&(fn->ret_ty), int, cm_type_encode(cm_function_ret(f))) * cm_stmt_rep(stmt, s)
*/
;

void cm_expr_type_code_context(struct cm_expr *expr, int *code)
/*@ With (e : cm_expr)
    Require cm_expr_rep(expr, e) * undef_data_at(code, int)
    Ensure cm_expr_rep(expr, e) * data_at(code, int, cm_type_encode(cm_expr_type(e)))
*/
{
  /*@ Assert exists (pa : Z) (pb : Z) (pargs : Z),
    expr == expr@pre &&
    code == code@pre &&
    expr != 0 &&
    data_at(&(expr->kind), int, cm_rep_expr_kind(e)) *
    data_at(&(expr->op), int, cm_rep_expr_op(e)) *
    data_at(&(expr->ty), int, cm_type_encode(cm_expr_type(e))) *
    data_at(&(expr->value), long long, cm_rep_expr_value(e)) *
    data_at(&(expr->a), struct cm_expr *, pa) *
    data_at(&(expr->b), struct cm_expr *, pb) *
    data_at(&(expr->args), struct cm_arg *, pargs) *
    cm_expr_payload(e, pa, pb, pargs) *
    undef_data_at(code, int)
  */
  *code = expr->ty;
}

int cm_expr_lvalue_count_context(struct cm_program *program, int fid,
                                 struct cm_function *fn,
                                 struct cm_expr *expr)
/*@ With (policy : cm_lookup_policy) (cg : cm_codegen_obligations) (p : cm_program) (f : cm_function_d) (e : cm_expr) (body : Z) (next : Z) (functions_ptr : Z)
    Require cm_wf_program(policy, cg, p) && f == cm_function_at(policy, fid, cm_program_functions(p)) && cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) && cm_rep_structs_safe(cm_program_structs(p)) && cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body, next) * cm_expr_rep(expr, e)
    Ensure cm_wf_program(policy, cg, p) && f == cm_function_at(policy, fid, cm_program_functions(p)) && cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) && cm_rep_structs_safe(cm_program_structs(p)) && __return == cm_lvalue_code_count(policy, p, fid, e) && cm_i32_code_count(__return) && cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body, next) * cm_expr_rep(expr, e)
*/
{
  /*@ Assert exists (zs : Z) (zg : Z) (zt : Z) (zp : Z) (zl : Z),
    program == program@pre && fid == fid@pre && fn == fn@pre && expr == expr@pre &&
    program != 0 && fn != 0 &&
    cm_wf_program(policy, cg, p) && f == cm_function_at(policy, fid, cm_program_functions(p)) && cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) && cm_rep_structs_safe(cm_program_structs(p)) &&
    data_at(&(program->structs), struct cm_struct *, zs) *
    data_at(&(program->globals), struct cm_global *, zg) *
    data_at(&(program->strings), struct cm_string *, zt) *
    data_at(&(program->functions), struct cm_function *, functions_ptr) *
    data_at(&(program->main_id), int, cm_program_main(p)) *
    cm_struct_list_rep(zs, cm_program_structs(p)) *
    cm_global_list_rep(zg, cm_program_globals(p)) *
    cm_string_list_rep(zt, cm_program_strings(p)) *
    data_at(&(fn->ret_ty), int, cm_type_encode(cm_function_ret(f))) *
    data_at(&(fn->params), struct cm_slot *, zp) *
    data_at(&(fn->locals), struct cm_slot *, zl) *
    data_at(&(fn->body), struct cm_stmt *, body) *
    data_at(&(fn->next), struct cm_function *, next) *
    cm_slot_list_rep(zp, cm_function_params(f)) *
    cm_slot_list_rep(zl, cm_function_locals(f)) *
    cm_expr_rep(expr, e)
  */
  int result = cm_expr_lvalue_count(program, fid, fn, expr) /*@ where policy = policy, cg = cg, p = p, f = f, structs = cm_program_structs(p), globals = cm_program_globals(p), locals = cm_function_locals(f), e = e */;
  return result;
}

int cm_expr_rvalue_count_context(struct cm_program *program, int fid,
                                 struct cm_function *fn,
                                 struct cm_expr *expr)
/*@ With (policy : cm_lookup_policy) (cg : cm_codegen_obligations) (p : cm_program) (f : cm_function_d) (e : cm_expr) (body : Z) (next : Z) (functions_ptr : Z)
    Require cm_wf_program(policy, cg, p) && f == cm_function_at(policy, fid, cm_program_functions(p)) && cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) && cm_rep_structs_safe(cm_program_structs(p)) && cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body, next) * cm_expr_rep(expr, e)
    Ensure cm_wf_program(policy, cg, p) && f == cm_function_at(policy, fid, cm_program_functions(p)) && cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) && cm_rep_structs_safe(cm_program_structs(p)) && __return == cm_rvalue_code_count(policy, p, fid, e) && cm_i32_code_count(__return) && cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body, next) * cm_expr_rep(expr, e)
*/
{
  /*@ Assert exists (zs : Z) (zg : Z) (zt : Z) (zp : Z) (zl : Z),
    program == program@pre && fid == fid@pre && fn == fn@pre && expr == expr@pre &&
    program != 0 && fn != 0 &&
    cm_wf_program(policy, cg, p) && f == cm_function_at(policy, fid, cm_program_functions(p)) && cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) && cm_rep_structs_safe(cm_program_structs(p)) &&
    data_at(&(program->structs), struct cm_struct *, zs) *
    data_at(&(program->globals), struct cm_global *, zg) *
    data_at(&(program->strings), struct cm_string *, zt) *
    data_at(&(program->functions), struct cm_function *, functions_ptr) *
    data_at(&(program->main_id), int, cm_program_main(p)) *
    cm_struct_list_rep(zs, cm_program_structs(p)) *
    cm_global_list_rep(zg, cm_program_globals(p)) *
    cm_string_list_rep(zt, cm_program_strings(p)) *
    data_at(&(fn->ret_ty), int, cm_type_encode(cm_function_ret(f))) *
    data_at(&(fn->params), struct cm_slot *, zp) *
    data_at(&(fn->locals), struct cm_slot *, zl) *
    data_at(&(fn->body), struct cm_stmt *, body) *
    data_at(&(fn->next), struct cm_function *, next) *
    cm_slot_list_rep(zp, cm_function_params(f)) *
    cm_slot_list_rep(zl, cm_function_locals(f)) *
    cm_expr_rep(expr, e)
  */
  int result = cm_expr_rvalue_count(program, fid, fn, expr) /*@ where policy = policy, cg = cg, p = p, f = f, structs = cm_program_structs(p), globals = cm_program_globals(p), locals = cm_function_locals(f), e = e */;
  return result;
}

int cm_stmt_code_count_context(struct cm_program *program, int fid,
                               struct cm_function *fn,
                               struct cm_stmt *stmt)
/*@ With (policy : cm_lookup_policy) (cg : cm_codegen_obligations) (p : cm_program) (f : cm_function_d) (s : cm_stmt) (loop_ : bool) (body : Z) (next : Z) (functions_ptr : Z)
    Require cm_wf_program(policy, cg, p) && f == cm_function_at(policy, fid, cm_program_functions(p)) && cm_stmt_wf(policy, p, f, loop_, s) && cm_stmt_counts_representable(policy, p, fid, s) && cm_rep_structs_safe(cm_program_structs(p)) && cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body, next) * cm_stmt_rep(stmt, s)
    Ensure cm_wf_program(policy, cg, p) && f == cm_function_at(policy, fid, cm_program_functions(p)) && cm_stmt_wf(policy, p, f, loop_, s) && cm_stmt_counts_representable(policy, p, fid, s) && cm_rep_structs_safe(cm_program_structs(p)) && __return == cm_stmt_code_count(policy, p, fid, s) && cm_i32_code_count(__return) && cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body, next) * cm_stmt_rep(stmt, s)
*/
{
  /*@ Assert exists (zs : Z) (zg : Z) (zt : Z) (zp : Z) (zl : Z),
    program == program@pre && fid == fid@pre && fn == fn@pre && stmt == stmt@pre &&
    program != 0 && fn != 0 &&
    cm_wf_program(policy, cg, p) && f == cm_function_at(policy, fid, cm_program_functions(p)) && cm_stmt_wf(policy, p, f, loop_, s) && cm_stmt_counts_representable(policy, p, fid, s) && cm_rep_structs_safe(cm_program_structs(p)) &&
    data_at(&(program->structs), struct cm_struct *, zs) *
    data_at(&(program->globals), struct cm_global *, zg) *
    data_at(&(program->strings), struct cm_string *, zt) *
    data_at(&(program->functions), struct cm_function *, functions_ptr) *
    data_at(&(program->main_id), int, cm_program_main(p)) *
    cm_struct_list_rep(zs, cm_program_structs(p)) *
    cm_global_list_rep(zg, cm_program_globals(p)) *
    cm_string_list_rep(zt, cm_program_strings(p)) *
    data_at(&(fn->ret_ty), int, cm_type_encode(cm_function_ret(f))) *
    data_at(&(fn->params), struct cm_slot *, zp) *
    data_at(&(fn->locals), struct cm_slot *, zl) *
    data_at(&(fn->body), struct cm_stmt *, body) *
    data_at(&(fn->next), struct cm_function *, next) *
    cm_slot_list_rep(zp, cm_function_params(f)) *
    cm_slot_list_rep(zl, cm_function_locals(f)) *
    cm_stmt_rep(stmt, s)
  */
  int result = cmc_stmt_code_count(program, fid, fn, stmt) /*@ where policy = policy, cg = cg, p = p, f = f, structs = cm_program_structs(p), globals = cm_program_globals(p), locals = cm_function_locals(f), s = s, loop_ = loop_ */;
  return result;
}

