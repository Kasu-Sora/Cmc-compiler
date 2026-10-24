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
    (cm_tpair :: *)
    (cm_apair :: *)
    (cm_lookup_policy :: *)
*/
/*@ Extern Coq
    (cm_type_encode : cm_type -> Z)
    (cm_rep_is_pointer_code : Z -> Z)
    (cm_rep_leaf_size : Z -> Z)
    (cm_rep_nonzero : Z -> Z)
    (cm_normalize_code_value : Z -> Z)
    (cm_rep_expr_kind : cm_expr -> Z)
    (cm_rep_expr_op : cm_expr -> Z)
    (cm_rep_expr_value : cm_expr -> Z)
    (cm_rep_stmt_kind : cm_stmt -> Z)
    (cm_rep_stmt_slot : cm_stmt -> Z)
    (cm_imax : Z -> Z -> Z)
    (cm_rep_code_slot_size : Z -> Z -> Z)
    (cm_slot_ty : cm_slot_d -> cm_type)
    (cm_slot_count : cm_slot_d -> Z)
    (cm_struct_members : cm_struct_d -> list cm_slot_d)
    (cm_global_ty : cm_global_d -> cm_type)
    (cm_global_count : cm_global_d -> Z)
    (cm_global_has_init : cm_global_d -> bool)
    (cm_global_init : cm_global_d -> Z)
    (cm_rep_bool : bool -> Z)
    (cm_string_bytes : cm_string_d -> list Z)
    (cm_rep_string_length : cm_string_d -> Z)
    (cm_rep_string_size : cm_string_d -> Z)
    (cm_expr_type : cm_expr -> cm_type)
    (cm_member_list_rep : Z -> list cm_slot_d -> Assertion)
    (cm_rep_members_safe : list cm_slot_d -> Prop)
    (cm_rep_members_size : list cm_slot_d -> Z)
    (cm_struct_list_rep : Z -> list cm_struct_d -> Assertion)
    (cm_rep_structs_safe : list cm_struct_d -> Prop)
    (cm_rep_struct_size : list cm_struct_d -> Z -> Z)
    (cm_global_list_rep : Z -> list cm_global_d -> Assertion)
    (cm_rep_global_array : list cm_global_d -> Z -> Z)
    (cm_slot_list_rep : Z -> list cm_slot_d -> Assertion)
    (cm_rep_member_array : list cm_slot_d -> Z -> Z)
    (cm_rep_slot_type : list cm_slot_d -> Z -> Z)
    (cm_rep_type_size : list cm_struct_d -> Z -> Z)
    (cm_rep_member_prefix : list cm_slot_d -> Z -> Z)
    (cm_rep_struct_member_prefix : list cm_struct_d -> Z -> Z -> Z)
    (cm_rep_struct_member_array : list cm_struct_d -> Z -> Z -> Z)
    (cm_rep_globals_safe : list cm_global_d -> Prop)
    (cm_rep_globals_size : list cm_global_d -> Z)
    (cm_rep_globals_prefix : list cm_global_d -> Z -> Z)
    (cm_string_list_rep : Z -> list cm_string_d -> Assertion)
    (cm_rep_strings_safe : list cm_string_d -> Prop)
    (cm_rep_strings_size : list cm_string_d -> Z)
    (cm_rep_strings_prefix : list cm_string_d -> Z -> Z)
    (cm_rep_global_address : list cm_global_d -> Z -> Z)
    (cm_rep_string_address : list cm_global_d -> list cm_string_d -> Z -> Z)
    (cm_program_globals : cm_program -> list cm_global_d)
    (cm_program_structs : cm_program -> list cm_struct_d)
    (cm_program_functions : cm_program -> list cm_function_d)
    (cm_function_locals : cm_function_d -> list cm_slot_d)
    (cm_function_at : cm_lookup_policy -> Z -> list cm_function_d -> cm_function_d)
    (cm_binding_valid : cm_program -> cm_function_d -> Z -> Z -> Prop)
    (cm_binding_array_code : cm_lookup_policy -> cm_program -> Z -> Z -> Z -> Z)
    (cm_member_valid : cm_program -> cm_type -> Z -> Prop)
    (cm_member_array_code : cm_program -> cm_type -> Z -> Z)
    (cm_type_code_wf : cm_type -> Prop)
    (cm_rep_args_safe : list cm_expr -> Prop)
    (cm_rep_args_temps_safe : list cm_expr -> Prop)
    (cm_rep_args_length : list cm_expr -> Z)
    (cm_rep_expr_temps_safe : cm_expr -> Prop)
    (cm_rep_stmt_temps_safe : cm_stmt -> Prop)
    (cm_expr_rep : Z -> cm_expr -> Assertion)
    (cm_arg_list_rep : Z -> list cm_expr -> Assertion)
    (cm_stmt_rep : Z -> cm_stmt -> Assertion)
    (cm_expr_payload : cm_expr -> Z -> Z -> Z -> Assertion)
    (cm_stmt_payload : cm_stmt -> Z -> Z -> Z -> Assertion)
    (cm_expr_tpair : cm_expr -> cm_tpair)
    (cm_args_apair : list cm_expr -> cm_apair)
    (cm_tleft : cm_tpair -> Z)
    (cm_tright : cm_tpair -> Z)
    (cm_acount : cm_apair -> Z)
    (cm_adepth : cm_apair -> Z)
    (cm_stemps : cm_stmt -> Z)
    (cm_uint8_buffer : Z -> list Z -> Assertion)
*/
/*@ Extern Coq
    (CMAssignE : cm_expr -> cm_expr -> cm_type -> cm_expr)
    (CMBinaryE : Z -> cm_expr -> cm_expr -> cm_type -> cm_expr)
    (CMUnaryE : Z -> cm_expr -> cm_type -> cm_expr)
    (CMIndexE : cm_expr -> cm_expr -> cm_type -> cm_expr)
    (CMMemberE : cm_expr -> Z -> cm_type -> cm_expr)
    (CMCallE : Z -> list cm_expr -> cm_type -> cm_expr)
    (CMPutcE : cm_expr -> cm_type -> cm_expr)
    (CMPutiE : cm_expr -> cm_type -> cm_expr)
    (CMExitE : cm_expr -> cm_type -> cm_expr)
    (CMExprS : cm_expr -> cm_stmt)
    (CMInitS : Z -> cm_expr -> cm_stmt)
    (CMReturnS : cm_expr -> cm_stmt)
    (CMSeqS : cm_stmt -> cm_stmt -> cm_stmt)
    (CMBlockS : cm_stmt -> cm_stmt)
    (CMIfS : cm_expr -> cm_stmt -> cm_stmt -> cm_stmt)
    (CMWhileS : cm_expr -> cm_stmt -> cm_stmt)
*/
/*@ Extern Coq
    (cm_codegen_obligations :: *)
    (cm_code_counts :: *)
    (cm_args_count :: *)
*/
/*@ Extern Coq
    (false : bool)
    (true : bool)
    (cm_program_strings : cm_program -> list cm_string_d)
    (cm_program_main : cm_program -> Z)
    (cm_function_ret : cm_function_d -> cm_type)
    (cm_function_params : cm_function_d -> list cm_slot_d)
    (cm_function_body : cm_function_d -> cm_stmt)
    (cm_member_base_type : cm_expr -> cm_type)
    (cm_slot_at : Z -> list cm_slot_d -> cm_slot_d)
    (cm_wf_program : cm_lookup_policy -> cm_codegen_obligations -> cm_program -> Prop)
    (cm_expr_wf : cm_lookup_policy -> cm_program -> cm_function_d -> cm_expr -> Prop)
    (cm_args_wf : cm_lookup_policy -> cm_program -> cm_function_d -> list cm_expr -> list cm_slot_d -> Prop)
    (cm_stmt_wf : cm_lookup_policy -> cm_program -> cm_function_d -> bool -> cm_stmt -> Prop)
    (cm_expr_counts_representable : cm_lookup_policy -> cm_program -> Z -> cm_expr -> Prop)
    (cm_args_counts_representable : cm_lookup_policy -> cm_program -> Z -> list cm_expr -> Prop)
    (cm_stmt_counts_representable : cm_lookup_policy -> cm_program -> Z -> cm_stmt -> Prop)
    (cm_expr_code_counts : cm_lookup_policy -> cm_program -> Z -> cm_expr -> cm_code_counts)
    (cm_args_code_counts : cm_lookup_policy -> cm_program -> Z -> list cm_expr -> cm_args_count)
    (cm_args_code_count_of : cm_args_count -> Z)
    (cm_lvalue_code_count : cm_lookup_policy -> cm_program -> Z -> cm_expr -> Z)
    (cm_rvalue_code_count : cm_lookup_policy -> cm_program -> Z -> cm_expr -> Z)
    (cm_stmt_code_count : cm_lookup_policy -> cm_program -> Z -> cm_stmt -> Z)
    (cm_i32_code_count : Z -> Prop)
    (cm_binding_address_count : Z -> Z)
    (cm_param_counts_representable : list cm_slot_d -> Prop)
    (cm_param_stores_count : list cm_slot_d -> Z)
    (cm_function_prologue_count : cm_function_d -> Z)
    (cm_function_counts_representable : cm_lookup_policy -> cm_program -> Z -> cm_function_d -> Prop)
    (cm_functions_counts_representable : cm_lookup_policy -> cm_program -> list cm_function_d -> Z -> Prop)
    (cm_function_code_count : cm_lookup_policy -> cm_program -> Z -> Z)
    (cm_function_prefix : cm_lookup_policy -> cm_program -> list cm_function_d -> Z -> Z)
    (cm_functions_code_size : cm_lookup_policy -> cm_program -> list cm_function_d -> Z -> Z)
    (cm_function_pc : cm_lookup_policy -> cm_program -> Z -> Z)
    (cm_model_code_length : cm_lookup_policy -> cm_program -> Z)
    (cm_model_data_length : cm_program -> Z)
    (cm_program_context_rep : Z -> cm_program -> Z -> Assertion)
    (cm_function_context_rep : Z -> cm_function_d -> Z -> Z -> Assertion)
    (cm_function_list_rep : Z -> list cm_function_d -> Assertion)
    (CMVarE : Z -> Z -> cm_type -> cm_expr)
*/
/*@ Import Coq Require Import SimpleC.EE.QCP_demos_human.cmc_counts_migration_lib */

void cmc_binding_array_value(struct cm_program *program, int fid,
                                    struct cm_function *fn,
                                    int scope, int slot, int *array)
/*@ With (policy : cm_lookup_policy) (p : cm_program) (f : cm_function_d) (globals : list cm_global_d) (locals : list cm_slot_d) (zg : Z) (zl : Z)
    Require 0 <= slot && globals == cm_program_globals(p) && locals == cm_function_locals(f) && f == cm_function_at(policy, fid, cm_program_functions(p)) && cm_binding_valid(p, f, scope, slot) && data_at(&(program->globals), struct cm_global *, zg) * cm_global_list_rep(zg, globals) * data_at(&(fn->locals), struct cm_slot *, zl) * cm_slot_list_rep(zl, locals) * undef_data_at(array, int)
    Ensure 0 <= slot && globals == cm_program_globals(p) && locals == cm_function_locals(f) && f == cm_function_at(policy, fid, cm_program_functions(p)) && cm_binding_valid(p, f, scope, slot) && data_at(&(program->globals), struct cm_global *, zg) * cm_global_list_rep(zg, globals) * data_at(&(fn->locals), struct cm_slot *, zl) * cm_slot_list_rep(zl, locals) * data_at(array, int, cm_binding_array_code(policy, p, fid, scope, slot))
*/
;

void cmc_member_array_value(struct cm_program *program,
                                   int base_ty, int mid, int *array)
/*@ With (p : cm_program) (base : cm_type) (structs : list cm_struct_d) (zs : Z)
    Require 1024 <= base_ty && base_ty <= 2147483647 && 0 <= (base_ty - 1024) % 1024 - 2 && 0 <= mid && structs == cm_program_structs(p) && base_ty == cm_type_encode(base) && cm_type_code_wf(base) && cm_member_valid(p, base, mid) && cm_rep_structs_safe(structs) && data_at(&(program->structs), struct cm_struct *, zs) * cm_struct_list_rep(zs, structs) * undef_data_at(array, int)
    Ensure 1024 <= base_ty && base_ty <= 2147483647 && 0 <= (base_ty - 1024) % 1024 - 2 && 0 <= mid && structs == cm_program_structs(p) && base_ty == cm_type_encode(base) && cm_type_code_wf(base) && cm_member_valid(p, base, mid) && cm_rep_structs_safe(structs) && data_at(&(program->structs), struct cm_struct *, zs) * cm_struct_list_rep(zs, structs) * data_at(array, int, cm_member_array_code(p, base, mid))
*/
;

void cmc_is_pointer_value(int ty, int *pointer)
/*@ Require undef_data_at(pointer, int)
    Ensure data_at(pointer, int, cm_rep_is_pointer_code(ty))
*/
;

int cm_normalize_count(int ty)
/*@ Require emp
    Ensure __return == cm_normalize_code_value(ty) && emp
*/
;

int cmc_slot_type_at(struct cm_slot *item, int index)
/*@ With (slots : list cm_slot_d)
    Require 0 <= index && cm_slot_list_rep(item, slots)
    Ensure 0 <= index && __return == cm_rep_slot_type(slots, index) && cm_slot_list_rep(item, slots)
*/
;

long long cmc_globals_size(struct cm_global *node)
/*@ With (globals : list cm_global_d)
    Require cm_rep_globals_safe(globals) && cm_global_list_rep(node, globals)
    Ensure cm_rep_globals_safe(globals) && __return == cm_rep_globals_size(globals) && 0 <= __return && __return <= 1048560 && cm_global_list_rep(node, globals)
*/
;

long long cmc_strings_size(struct cm_string *node)
/*@ With (strings : list cm_string_d)
    Require cm_rep_strings_safe(strings) && cm_string_list_rep(node, strings)
    Ensure cm_rep_strings_safe(strings) && __return == cm_rep_strings_size(strings) && 0 <= __return && __return <= 1048560 && cm_string_list_rep(node, strings)
*/
;

static void cmc_expr_type_code_value(struct cm_expr *expr, int *code)
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

static void cm_expr_counts(struct cm_program *program, int fid,
                           struct cm_function *fn,
                           struct cm_expr *expr, int *lvalue, int *rvalue)
/*@ With (policy : cm_lookup_policy) (cg : cm_codegen_obligations) (p : cm_program) (f : cm_function_d) (structs : list cm_struct_d) (globals : list cm_global_d) (locals : list cm_slot_d) (zs : Z) (zg : Z) (zl : Z) (e : cm_expr)
    Require cm_wf_program(policy, cg, p) && f == cm_function_at(policy, fid, cm_program_functions(p)) && structs == cm_program_structs(p) && globals == cm_program_globals(p) && locals == cm_function_locals(f) && cm_rep_structs_safe(structs) && cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) && data_at(&(program->structs), struct cm_struct *, zs) * cm_struct_list_rep(zs, structs) * data_at(&(program->globals), struct cm_global *, zg) * cm_global_list_rep(zg, globals) * data_at(&(fn->locals), struct cm_slot *, zl) * cm_slot_list_rep(zl, locals) * cm_expr_rep(expr, e) * undef_data_at(lvalue, int) * undef_data_at(rvalue, int)
    Ensure cm_wf_program(policy, cg, p) && f == cm_function_at(policy, fid, cm_program_functions(p)) && structs == cm_program_structs(p) && globals == cm_program_globals(p) && locals == cm_function_locals(f) && cm_rep_structs_safe(structs) && cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) && cm_type_code_wf(cm_expr_type(e)) && cm_i32_code_count(cm_type_encode(cm_expr_type(e))) && cm_i32_code_count(cm_lvalue_code_count(policy, p, fid, e)) && cm_i32_code_count(cm_rvalue_code_count(policy, p, fid, e)) && data_at(&(program->structs), struct cm_struct *, zs) * cm_struct_list_rep(zs, structs) * data_at(&(program->globals), struct cm_global *, zg) * cm_global_list_rep(zg, globals) * data_at(&(fn->locals), struct cm_slot *, zl) * cm_slot_list_rep(zl, locals) * cm_expr_rep(expr, e) * data_at(lvalue, int, cm_lvalue_code_count(policy, p, fid, e)) * data_at(rvalue, int, cm_rvalue_code_count(policy, p, fid, e))
*/
;

int cm_expr_lvalue_count(struct cm_program *program, int fid,
                                struct cm_function *fn,
                                struct cm_expr *expr)
/*@ With (policy : cm_lookup_policy) (cg : cm_codegen_obligations) (p : cm_program) (f : cm_function_d) (structs : list cm_struct_d) (globals : list cm_global_d) (locals : list cm_slot_d) (zs : Z) (zg : Z) (zl : Z) (e : cm_expr)
    Require cm_wf_program(policy, cg, p) && f == cm_function_at(policy, fid, cm_program_functions(p)) && structs == cm_program_structs(p) && globals == cm_program_globals(p) && locals == cm_function_locals(f) && cm_rep_structs_safe(structs) && cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) && data_at(&(program->structs), struct cm_struct *, zs) * cm_struct_list_rep(zs, structs) * data_at(&(program->globals), struct cm_global *, zg) * cm_global_list_rep(zg, globals) * data_at(&(fn->locals), struct cm_slot *, zl) * cm_slot_list_rep(zl, locals) * cm_expr_rep(expr, e)
    Ensure cm_wf_program(policy, cg, p) && f == cm_function_at(policy, fid, cm_program_functions(p)) && structs == cm_program_structs(p) && globals == cm_program_globals(p) && locals == cm_function_locals(f) && cm_rep_structs_safe(structs) && cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) && __return == cm_lvalue_code_count(policy, p, fid, e) && cm_i32_code_count(__return) && data_at(&(program->structs), struct cm_struct *, zs) * cm_struct_list_rep(zs, structs) * data_at(&(program->globals), struct cm_global *, zg) * cm_global_list_rep(zg, globals) * data_at(&(fn->locals), struct cm_slot *, zl) * cm_slot_list_rep(zl, locals) * cm_expr_rep(expr, e)
*/
{
  int lvalue;
  int rvalue;
  cm_expr_counts(program, fid, fn, expr, &lvalue, &rvalue) /*@ where policy = policy, cg = cg, p = p, f = f, structs = structs, globals = globals, locals = locals, zs = zs, zg = zg, zl = zl, e = e */;
  return lvalue;
}

int cm_expr_rvalue_count(struct cm_program *program, int fid,
                                struct cm_function *fn,
                                struct cm_expr *expr)
/*@ With (policy : cm_lookup_policy) (cg : cm_codegen_obligations) (p : cm_program) (f : cm_function_d) (structs : list cm_struct_d) (globals : list cm_global_d) (locals : list cm_slot_d) (zs : Z) (zg : Z) (zl : Z) (e : cm_expr)
    Require cm_wf_program(policy, cg, p) && f == cm_function_at(policy, fid, cm_program_functions(p)) && structs == cm_program_structs(p) && globals == cm_program_globals(p) && locals == cm_function_locals(f) && cm_rep_structs_safe(structs) && cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) && data_at(&(program->structs), struct cm_struct *, zs) * cm_struct_list_rep(zs, structs) * data_at(&(program->globals), struct cm_global *, zg) * cm_global_list_rep(zg, globals) * data_at(&(fn->locals), struct cm_slot *, zl) * cm_slot_list_rep(zl, locals) * cm_expr_rep(expr, e)
    Ensure cm_wf_program(policy, cg, p) && f == cm_function_at(policy, fid, cm_program_functions(p)) && structs == cm_program_structs(p) && globals == cm_program_globals(p) && locals == cm_function_locals(f) && cm_rep_structs_safe(structs) && cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) && __return == cm_rvalue_code_count(policy, p, fid, e) && cm_i32_code_count(__return) && data_at(&(program->structs), struct cm_struct *, zs) * cm_struct_list_rep(zs, structs) * data_at(&(program->globals), struct cm_global *, zg) * cm_global_list_rep(zg, globals) * data_at(&(fn->locals), struct cm_slot *, zl) * cm_slot_list_rep(zl, locals) * cm_expr_rep(expr, e)
*/
{
  int lvalue;
  int rvalue;
  cm_expr_counts(program, fid, fn, expr, &lvalue, &rvalue) /*@ where policy = policy, cg = cg, p = p, f = f, structs = structs, globals = globals, locals = locals, zs = zs, zg = zg, zl = zl, e = e */;
  return rvalue;
}

static void cmc_args_code_count(struct cm_program *program, int fid,
                                struct cm_function *fn,
                                struct cm_arg *arg, int *count)
/*@ With (policy : cm_lookup_policy) (cg : cm_codegen_obligations) (p : cm_program) (f : cm_function_d) (structs : list cm_struct_d) (globals : list cm_global_d) (locals : list cm_slot_d) (zs : Z) (zg : Z) (zl : Z) (args : list cm_expr) (slots : list cm_slot_d)
    Require cm_wf_program(policy, cg, p) && f == cm_function_at(policy, fid, cm_program_functions(p)) && structs == cm_program_structs(p) && globals == cm_program_globals(p) && locals == cm_function_locals(f) && cm_rep_structs_safe(structs) && cm_args_wf(policy, p, f, args, slots) && cm_args_counts_representable(policy, p, fid, args) && data_at(&(program->structs), struct cm_struct *, zs) * cm_struct_list_rep(zs, structs) * data_at(&(program->globals), struct cm_global *, zg) * cm_global_list_rep(zg, globals) * data_at(&(fn->locals), struct cm_slot *, zl) * cm_slot_list_rep(zl, locals) * cm_arg_list_rep(arg, args) * undef_data_at(count, int)
    Ensure cm_wf_program(policy, cg, p) && f == cm_function_at(policy, fid, cm_program_functions(p)) && structs == cm_program_structs(p) && globals == cm_program_globals(p) && locals == cm_function_locals(f) && cm_rep_structs_safe(structs) && cm_args_wf(policy, p, f, args, slots) && cm_args_counts_representable(policy, p, fid, args) && cm_i32_code_count(cm_args_code_count_of(cm_args_code_counts(policy, p, fid, args))) && data_at(&(program->structs), struct cm_struct *, zs) * cm_struct_list_rep(zs, structs) * data_at(&(program->globals), struct cm_global *, zg) * cm_global_list_rep(zg, globals) * data_at(&(fn->locals), struct cm_slot *, zl) * cm_slot_list_rep(zl, locals) * cm_arg_list_rep(arg, args) * data_at(count, int, cm_args_code_count_of(cm_args_code_counts(policy, p, fid, args)))
*/
{
  if (arg == 0) {
    *count = 1;
    return;
  } else {
  /*@ Assert exists (head : cm_expr) (tail : list cm_expr) (sh : cm_slot_d) (st : list cm_slot_d) (ep : Z) (np : Z),
    program == program@pre &&
    fn == fn@pre &&
    fid == fid@pre &&
    arg == arg@pre &&
    count == count@pre &&
    arg != 0 &&
    cm_wf_program(policy, cg, p) &&
    f == cm_function_at(policy, fid, cm_program_functions(p)) &&
    structs == cm_program_structs(p) &&
    globals == cm_program_globals(p) &&
    locals == cm_function_locals(f) &&
    cm_rep_structs_safe(structs) &&
    cm_args_wf(policy, p, f, args, slots) &&
    cm_args_counts_representable(policy, p, fid, args) &&
    args == cons(head, tail) &&
    slots == cons(sh, st) &&
    cm_expr_wf(policy, p, f, head) &&
    cm_expr_counts_representable(policy, p, fid, head) &&
    cm_args_wf(policy, p, f, tail, st) &&
    cm_args_counts_representable(policy, p, fid, tail) &&
    data_at(&(program->structs), struct cm_struct *, zs) *
    cm_struct_list_rep(zs, structs) *
    data_at(&(program->globals), struct cm_global *, zg) *
    cm_global_list_rep(zg, globals) *
    data_at(&(fn->locals), struct cm_slot *, zl) *
    cm_slot_list_rep(zl, locals) *
    data_at(&(arg->expr), struct cm_expr *, ep) *
    data_at(&(arg->next), struct cm_arg *, np) *
    cm_expr_rep(ep, head) *
    cm_arg_list_rep(np, tail) *
    undef_data_at(count, int)
  */
  int head_lvalue;
  int head_count;
  cm_expr_counts(program, fid, fn, arg->expr,
                 &head_lvalue, &head_count) /*@ where policy = policy, cg = cg, p = p, f = f, structs = structs, globals = globals, locals = locals, zs = zs, zg = zg, zl = zl */;
  int tail_count;
  cmc_args_code_count(program, fid, fn, arg->next, &tail_count) /*@ where policy = policy, cg = cg, p = p, f = f, structs = structs, globals = globals, locals = locals, zs = zs, zg = zg, zl = zl */;
  *count = head_count + 10 + tail_count;
  }
}

static void cm_binding_address_count_value(int scope, int *count)
/*@ Require undef_data_at(count, int)
    Ensure cm_i32_code_count(cm_binding_address_count(scope)) && data_at(count, int, cm_binding_address_count(scope))
*/
{
  if (scope == CMC_BIND_GLOBAL) {
    *count = 1;
  } else {
    *count = 4;
  }
}

static void cm_expr_counts(struct cm_program *program, int fid,
                           struct cm_function *fn,
                           struct cm_expr *expr, int *lvalue, int *rvalue)
/*@ With (policy : cm_lookup_policy) (cg : cm_codegen_obligations) (p : cm_program) (f : cm_function_d) (structs : list cm_struct_d) (globals : list cm_global_d) (locals : list cm_slot_d) (zs : Z) (zg : Z) (zl : Z) (e : cm_expr)
    Require cm_wf_program(policy, cg, p) && f == cm_function_at(policy, fid, cm_program_functions(p)) && structs == cm_program_structs(p) && globals == cm_program_globals(p) && locals == cm_function_locals(f) && cm_rep_structs_safe(structs) && cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) && data_at(&(program->structs), struct cm_struct *, zs) * cm_struct_list_rep(zs, structs) * data_at(&(program->globals), struct cm_global *, zg) * cm_global_list_rep(zg, globals) * data_at(&(fn->locals), struct cm_slot *, zl) * cm_slot_list_rep(zl, locals) * cm_expr_rep(expr, e) * undef_data_at(lvalue, int) * undef_data_at(rvalue, int)
    Ensure cm_wf_program(policy, cg, p) && f == cm_function_at(policy, fid, cm_program_functions(p)) && structs == cm_program_structs(p) && globals == cm_program_globals(p) && locals == cm_function_locals(f) && cm_rep_structs_safe(structs) && cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) && cm_type_code_wf(cm_expr_type(e)) && cm_i32_code_count(cm_type_encode(cm_expr_type(e))) && cm_i32_code_count(cm_lvalue_code_count(policy, p, fid, e)) && cm_i32_code_count(cm_rvalue_code_count(policy, p, fid, e)) && data_at(&(program->structs), struct cm_struct *, zs) * cm_struct_list_rep(zs, structs) * data_at(&(program->globals), struct cm_global *, zg) * cm_global_list_rep(zg, globals) * data_at(&(fn->locals), struct cm_slot *, zl) * cm_slot_list_rep(zl, locals) * cm_expr_rep(expr, e) * data_at(lvalue, int, cm_lvalue_code_count(policy, p, fid, e)) * data_at(rvalue, int, cm_rvalue_code_count(policy, p, fid, e))
*/
{
  /*@ Assert exists (pa : Z) (pb : Z) (pargs : Z),
    program == program@pre &&
    fn == fn@pre &&
    fid == fid@pre &&
    expr == expr@pre &&
    lvalue == lvalue@pre &&
    rvalue == rvalue@pre &&
    expr != 0 &&
    cm_wf_program(policy, cg, p) &&
    f == cm_function_at(policy, fid, cm_program_functions(p)) &&
    structs == cm_program_structs(p) &&
    globals == cm_program_globals(p) &&
    locals == cm_function_locals(f) &&
    cm_rep_structs_safe(structs) &&
    cm_expr_wf(policy, p, f, e) &&
    cm_expr_counts_representable(policy, p, fid, e) &&
    data_at(&(program->structs), struct cm_struct *, zs) *
    cm_struct_list_rep(zs, structs) *
    data_at(&(program->globals), struct cm_global *, zg) *
    cm_global_list_rep(zg, globals) *
    data_at(&(fn->locals), struct cm_slot *, zl) *
    cm_slot_list_rep(zl, locals) *
    data_at(&(expr->kind), int, cm_rep_expr_kind(e)) *
    data_at(&(expr->op), int, cm_rep_expr_op(e)) *
    data_at(&(expr->ty), int, cm_type_encode(cm_expr_type(e))) *
    data_at(&(expr->value), long long, cm_rep_expr_value(e)) *
    data_at(&(expr->a), struct cm_expr *, pa) *
    data_at(&(expr->b), struct cm_expr *, pb) *
    data_at(&(expr->args), struct cm_arg *, pargs) *
    cm_expr_payload(e, pa, pb, pargs) *
    undef_data_at(lvalue, int) *
    undef_data_at(rvalue, int)
  */
  int out_lvalue = 0;
  int out_rvalue = 0;
  if (expr->kind == CMC_EXPR_CONST) {
    out_rvalue = 1;
  } else if (expr->kind == CMC_EXPR_STRING) {
    out_rvalue = 1;
  } else if (expr->kind == CMC_EXPR_SIZEOF) {
    out_rvalue = 1;
  } else if (expr->kind == CMC_EXPR_GETC) {
    out_rvalue = 1;
  } else if (expr->kind == CMC_EXPR_VAR) {
  /*@ Assert exists (pa : Z) (pb : Z) (pargs : Z) (scope : Z) (slot : Z) (ty : cm_type),
    program == program@pre &&
    fn == fn@pre &&
    fid == fid@pre &&
    expr == expr@pre &&
    lvalue == lvalue@pre &&
    rvalue == rvalue@pre &&
    expr != 0 &&
    cm_wf_program(policy, cg, p) &&
    f == cm_function_at(policy, fid, cm_program_functions(p)) &&
    structs == cm_program_structs(p) &&
    globals == cm_program_globals(p) &&
    locals == cm_function_locals(f) &&
    cm_rep_structs_safe(structs) &&
    cm_expr_wf(policy, p, f, e) &&
    cm_expr_counts_representable(policy, p, fid, e) &&
    e == CMVarE(scope, slot, ty) &&
    out_lvalue == 0 &&
    out_rvalue == 0 &&
    cm_binding_valid(p, f, scope, slot) &&
    0 <= slot &&
    slot <= 2147483647 &&
    data_at(&(program->structs), struct cm_struct *, zs) *
    cm_struct_list_rep(zs, structs) *
    data_at(&(program->globals), struct cm_global *, zg) *
    cm_global_list_rep(zg, globals) *
    data_at(&(fn->locals), struct cm_slot *, zl) *
    cm_slot_list_rep(zl, locals) *
    data_at(&(expr->kind), int, cm_rep_expr_kind(e)) *
    data_at(&(expr->op), int, cm_rep_expr_op(e)) *
    data_at(&(expr->ty), int, cm_type_encode(cm_expr_type(e))) *
    data_at(&(expr->value), long long, cm_rep_expr_value(e)) *
    data_at(&(expr->a), struct cm_expr *, pa) *
    data_at(&(expr->b), struct cm_expr *, pb) *
    data_at(&(expr->args), struct cm_arg *, pargs) *
    cm_expr_payload(e, pa, pb, pargs) *
    undef_data_at(lvalue, int) *
    undef_data_at(rvalue, int)
  */
    int address_count;
    cm_binding_address_count_value(expr->op, &address_count);
    out_lvalue = address_count;
    out_rvalue = address_count;
    int array;
    cmc_binding_array_value(program, fid, fn, expr->op,
                            (int)expr->value, &array) /*@ where policy = policy, p = p, f = f, globals = globals, locals = locals, zg = zg, zl = zl */;
    if (!array) {
      out_rvalue = out_rvalue + 1;
    } else {
    }
  } else if (expr->kind == CMC_EXPR_ASSIGN) {
  /*@ Assert exists (pa : Z) (pb : Z) (pargs : Z) (x : cm_expr) (y : cm_expr) (ty : cm_type),
    program == program@pre &&
    fn == fn@pre &&
    fid == fid@pre &&
    expr == expr@pre &&
    lvalue == lvalue@pre &&
    rvalue == rvalue@pre &&
    expr != 0 &&
    cm_wf_program(policy, cg, p) &&
    f == cm_function_at(policy, fid, cm_program_functions(p)) &&
    structs == cm_program_structs(p) &&
    globals == cm_program_globals(p) &&
    locals == cm_function_locals(f) &&
    cm_rep_structs_safe(structs) &&
    cm_expr_wf(policy, p, f, e) &&
    cm_expr_counts_representable(policy, p, fid, e) &&
    e == CMAssignE(x, y, ty) &&
    out_lvalue == 0 &&
    out_rvalue == 0 &&
    cm_expr_wf(policy, p, f, x) &&
    cm_expr_counts_representable(policy, p, fid, x) &&
    cm_expr_wf(policy, p, f, y) &&
    cm_expr_counts_representable(policy, p, fid, y) &&
    pargs == 0 &&
    data_at(&(program->structs), struct cm_struct *, zs) *
    cm_struct_list_rep(zs, structs) *
    data_at(&(program->globals), struct cm_global *, zg) *
    cm_global_list_rep(zg, globals) *
    data_at(&(fn->locals), struct cm_slot *, zl) *
    cm_slot_list_rep(zl, locals) *
    data_at(&(expr->kind), int, cm_rep_expr_kind(e)) *
    data_at(&(expr->op), int, cm_rep_expr_op(e)) *
    data_at(&(expr->ty), int, cm_type_encode(cm_expr_type(e))) *
    data_at(&(expr->value), long long, cm_rep_expr_value(e)) *
    data_at(&(expr->a), struct cm_expr *, pa) *
    data_at(&(expr->b), struct cm_expr *, pb) *
    data_at(&(expr->args), struct cm_arg *, pargs) *
    cm_expr_rep(pa, x) *
    cm_expr_rep(pb, y) *
    undef_data_at(lvalue, int) *
    undef_data_at(rvalue, int)
  */
    int dst_lvalue;
    int dst_rvalue;
    int src_lvalue;
    int src_rvalue;
    cm_expr_counts(program, fid, fn, expr->a,
                   &dst_lvalue, &dst_rvalue) /*@ where policy = policy, cg = cg, p = p, f = f, structs = structs, globals = globals, locals = locals, zs = zs, zg = zg, zl = zl */;
    cm_expr_counts(program, fid, fn, expr->b,
                   &src_lvalue, &src_rvalue) /*@ where policy = policy, cg = cg, p = p, f = f, structs = structs, globals = globals, locals = locals, zs = zs, zg = zg, zl = zl */;
    int normalize_count = cm_normalize_count(expr->ty);
    out_rvalue = dst_lvalue +
                 (5 + (src_rvalue + (normalize_count + 12)));
  } else if (expr->kind == CMC_EXPR_BINARY) {
  /*@ Assert exists (pa : Z) (pb : Z) (pargs : Z) (op : Z) (x : cm_expr) (y : cm_expr) (ty : cm_type),
    program == program@pre &&
    fn == fn@pre &&
    fid == fid@pre &&
    expr == expr@pre &&
    lvalue == lvalue@pre &&
    rvalue == rvalue@pre &&
    expr != 0 &&
    cm_wf_program(policy, cg, p) &&
    f == cm_function_at(policy, fid, cm_program_functions(p)) &&
    structs == cm_program_structs(p) &&
    globals == cm_program_globals(p) &&
    locals == cm_function_locals(f) &&
    cm_rep_structs_safe(structs) &&
    cm_expr_wf(policy, p, f, e) &&
    cm_expr_counts_representable(policy, p, fid, e) &&
    e == CMBinaryE(op, x, y, ty) &&
    out_lvalue == 0 &&
    out_rvalue == 0 &&
    cm_expr_wf(policy, p, f, x) &&
    cm_expr_counts_representable(policy, p, fid, x) &&
    cm_expr_wf(policy, p, f, y) &&
    cm_expr_counts_representable(policy, p, fid, y) &&
    pargs == 0 &&
    data_at(&(program->structs), struct cm_struct *, zs) *
    cm_struct_list_rep(zs, structs) *
    data_at(&(program->globals), struct cm_global *, zg) *
    cm_global_list_rep(zg, globals) *
    data_at(&(fn->locals), struct cm_slot *, zl) *
    cm_slot_list_rep(zl, locals) *
    data_at(&(expr->kind), int, cm_rep_expr_kind(e)) *
    data_at(&(expr->op), int, cm_rep_expr_op(e)) *
    data_at(&(expr->ty), int, cm_type_encode(cm_expr_type(e))) *
    data_at(&(expr->value), long long, cm_rep_expr_value(e)) *
    data_at(&(expr->a), struct cm_expr *, pa) *
    data_at(&(expr->b), struct cm_expr *, pb) *
    data_at(&(expr->args), struct cm_arg *, pargs) *
    cm_expr_rep(pa, x) *
    cm_expr_rep(pb, y) *
    undef_data_at(lvalue, int) *
    undef_data_at(rvalue, int)
  */
    int left_lvalue;
    int left_rvalue;
    int right_lvalue;
    int right_rvalue;
    cm_expr_counts(program, fid, fn, expr->a,
                   &left_lvalue, &left_rvalue) /*@ where policy = policy, cg = cg, p = p, f = f, structs = structs, globals = globals, locals = locals, zs = zs, zg = zg, zl = zl */;
    cm_expr_counts(program, fid, fn, expr->b,
                   &right_lvalue, &right_rvalue) /*@ where policy = policy, cg = cg, p = p, f = f, structs = structs, globals = globals, locals = locals, zs = zs, zg = zg, zl = zl */;
    if (expr->op == CMC_BIN_OR) {
      out_rvalue = left_rvalue + (right_rvalue + 5);
    } else if (expr->op == CMC_BIN_AND) {
      out_rvalue = left_rvalue + (right_rvalue + 5);
    } else {
      if (expr->op == CMC_BIN_ADD) {
        int right_type;
        cmc_expr_type_code_value(expr->b, &right_type);
        int right_pointer;
        cmc_is_pointer_value(right_type, &right_pointer);
        if (right_pointer) {
          out_rvalue = left_rvalue + (right_rvalue + 14);
        } else {
          int left_type;
          cmc_expr_type_code_value(expr->a, &left_type);
          int left_pointer;
          cmc_is_pointer_value(left_type, &left_pointer);
          if (left_pointer) {
            out_rvalue = left_rvalue + (right_rvalue + 14);
          } else {
            out_rvalue = left_rvalue + (right_rvalue + 12);
          }
        }
      } else if (expr->op == CMC_BIN_SUB) {
        int left_type;
        cmc_expr_type_code_value(expr->a, &left_type);
        int left_pointer;
        cmc_is_pointer_value(left_type, &left_pointer);
        if (left_pointer) {
          out_rvalue = left_rvalue + (right_rvalue + 14);
        } else {
          out_rvalue = left_rvalue + (right_rvalue + 12);
        }
      } else {
        out_rvalue = left_rvalue + (right_rvalue + 12);
      }
    }
  } else if (expr->kind == CMC_EXPR_UNARY) {
  /*@ Assert exists (pa : Z) (pb : Z) (pargs : Z) (op : Z) (x : cm_expr) (ty : cm_type),
    program == program@pre &&
    fn == fn@pre &&
    fid == fid@pre &&
    expr == expr@pre &&
    lvalue == lvalue@pre &&
    rvalue == rvalue@pre &&
    expr != 0 &&
    cm_wf_program(policy, cg, p) &&
    f == cm_function_at(policy, fid, cm_program_functions(p)) &&
    structs == cm_program_structs(p) &&
    globals == cm_program_globals(p) &&
    locals == cm_function_locals(f) &&
    cm_rep_structs_safe(structs) &&
    cm_expr_wf(policy, p, f, e) &&
    cm_expr_counts_representable(policy, p, fid, e) &&
    e == CMUnaryE(op, x, ty) &&
    out_lvalue == 0 &&
    out_rvalue == 0 &&
    cm_expr_wf(policy, p, f, x) &&
    cm_expr_counts_representable(policy, p, fid, x) &&
    pa != 0 &&
    pb == 0 &&
    pargs == 0 &&
    data_at(&(program->structs), struct cm_struct *, zs) *
    cm_struct_list_rep(zs, structs) *
    data_at(&(program->globals), struct cm_global *, zg) *
    cm_global_list_rep(zg, globals) *
    data_at(&(fn->locals), struct cm_slot *, zl) *
    cm_slot_list_rep(zl, locals) *
    data_at(&(expr->kind), int, cm_rep_expr_kind(e)) *
    data_at(&(expr->op), int, cm_rep_expr_op(e)) *
    data_at(&(expr->ty), int, cm_type_encode(cm_expr_type(e))) *
    data_at(&(expr->value), long long, cm_rep_expr_value(e)) *
    data_at(&(expr->a), struct cm_expr *, pa) *
    data_at(&(expr->b), struct cm_expr *, pb) *
    data_at(&(expr->args), struct cm_arg *, pargs) *
    cm_expr_rep(pa, x) *
    undef_data_at(lvalue, int) *
    undef_data_at(rvalue, int)
  */
    int child_lvalue;
    int child_rvalue;
    cm_expr_counts(program, fid, fn, expr->a,
                   &child_lvalue, &child_rvalue) /*@ where policy = policy, cg = cg, p = p, f = f, structs = structs, globals = globals, locals = locals, zs = zs, zg = zg, zl = zl */;
    if (expr->op == CMC_UN_DEREF) {
      out_lvalue = child_rvalue;
      out_rvalue = child_rvalue + 1;
    } else if (expr->op == CMC_UN_ADDR) {
      out_rvalue = child_lvalue;
    } else {
      out_rvalue = child_rvalue + 2;
    }
  } else if (expr->kind == CMC_EXPR_INDEX) {
  /*@ Assert exists (pa : Z) (pb : Z) (pargs : Z) (x : cm_expr) (y : cm_expr) (ty : cm_type),
    program == program@pre &&
    fn == fn@pre &&
    fid == fid@pre &&
    expr == expr@pre &&
    lvalue == lvalue@pre &&
    rvalue == rvalue@pre &&
    expr != 0 &&
    cm_wf_program(policy, cg, p) &&
    f == cm_function_at(policy, fid, cm_program_functions(p)) &&
    structs == cm_program_structs(p) &&
    globals == cm_program_globals(p) &&
    locals == cm_function_locals(f) &&
    cm_rep_structs_safe(structs) &&
    cm_expr_wf(policy, p, f, e) &&
    cm_expr_counts_representable(policy, p, fid, e) &&
    e == CMIndexE(x, y, ty) &&
    out_lvalue == 0 &&
    out_rvalue == 0 &&
    cm_expr_wf(policy, p, f, x) &&
    cm_expr_counts_representable(policy, p, fid, x) &&
    cm_expr_wf(policy, p, f, y) &&
    cm_expr_counts_representable(policy, p, fid, y) &&
    pargs == 0 &&
    data_at(&(program->structs), struct cm_struct *, zs) *
    cm_struct_list_rep(zs, structs) *
    data_at(&(program->globals), struct cm_global *, zg) *
    cm_global_list_rep(zg, globals) *
    data_at(&(fn->locals), struct cm_slot *, zl) *
    cm_slot_list_rep(zl, locals) *
    data_at(&(expr->kind), int, cm_rep_expr_kind(e)) *
    data_at(&(expr->op), int, cm_rep_expr_op(e)) *
    data_at(&(expr->ty), int, cm_type_encode(cm_expr_type(e))) *
    data_at(&(expr->value), long long, cm_rep_expr_value(e)) *
    data_at(&(expr->a), struct cm_expr *, pa) *
    data_at(&(expr->b), struct cm_expr *, pb) *
    data_at(&(expr->args), struct cm_arg *, pargs) *
    cm_expr_rep(pa, x) *
    cm_expr_rep(pb, y) *
    undef_data_at(lvalue, int) *
    undef_data_at(rvalue, int)
  */
    int base_lvalue;
    int base_rvalue;
    int index_lvalue;
    int index_rvalue;
    cm_expr_counts(program, fid, fn, expr->a,
                   &base_lvalue, &base_rvalue) /*@ where policy = policy, cg = cg, p = p, f = f, structs = structs, globals = globals, locals = locals, zs = zs, zg = zg, zl = zl */;
    cm_expr_counts(program, fid, fn, expr->b,
                   &index_lvalue, &index_rvalue) /*@ where policy = policy, cg = cg, p = p, f = f, structs = structs, globals = globals, locals = locals, zs = zs, zg = zg, zl = zl */;
    out_lvalue = base_rvalue + (index_rvalue + 13);
    out_rvalue = out_lvalue + 1;
  } else if (expr->kind == CMC_EXPR_MEMBER) {
  /*@ Assert exists (pa : Z) (pb : Z) (pargs : Z) (x : cm_expr) (mid : Z) (ty : cm_type),
    program == program@pre &&
    fn == fn@pre &&
    fid == fid@pre &&
    expr == expr@pre &&
    lvalue == lvalue@pre &&
    rvalue == rvalue@pre &&
    expr != 0 &&
    cm_wf_program(policy, cg, p) &&
    f == cm_function_at(policy, fid, cm_program_functions(p)) &&
    structs == cm_program_structs(p) &&
    globals == cm_program_globals(p) &&
    locals == cm_function_locals(f) &&
    cm_rep_structs_safe(structs) &&
    cm_expr_wf(policy, p, f, e) &&
    cm_expr_counts_representable(policy, p, fid, e) &&
    e == CMMemberE(x, mid, ty) &&
    out_lvalue == 0 &&
    out_rvalue == 0 &&
    cm_member_valid(p, cm_expr_type(x), mid) &&
    0 <= mid &&
    mid <= 2147483647 &&
    cm_expr_wf(policy, p, f, x) &&
    cm_expr_counts_representable(policy, p, fid, x) &&
    pa != 0 &&
    pb == 0 &&
    pargs == 0 &&
    data_at(&(program->structs), struct cm_struct *, zs) *
    cm_struct_list_rep(zs, structs) *
    data_at(&(program->globals), struct cm_global *, zg) *
    cm_global_list_rep(zg, globals) *
    data_at(&(fn->locals), struct cm_slot *, zl) *
    cm_slot_list_rep(zl, locals) *
    data_at(&(expr->kind), int, cm_rep_expr_kind(e)) *
    data_at(&(expr->op), int, cm_rep_expr_op(e)) *
    data_at(&(expr->ty), int, cm_type_encode(cm_expr_type(e))) *
    data_at(&(expr->value), long long, cm_rep_expr_value(e)) *
    data_at(&(expr->a), struct cm_expr *, pa) *
    data_at(&(expr->b), struct cm_expr *, pb) *
    data_at(&(expr->args), struct cm_arg *, pargs) *
    cm_expr_rep(pa, x) *
    undef_data_at(lvalue, int) *
    undef_data_at(rvalue, int)
  */
    int base_lvalue;
    int base_rvalue;
    cm_expr_counts(program, fid, fn, expr->a,
                   &base_lvalue, &base_rvalue) /*@ where policy = policy, cg = cg, p = p, f = f, structs = structs, globals = globals, locals = locals, zs = zs, zg = zg, zl = zl */;
    out_lvalue = base_rvalue + 2;
    out_rvalue = out_lvalue;
    int base_type;
    cmc_expr_type_code_value(expr->a, &base_type);
    int member_id = (int)expr->value;
    int array;
    cmc_member_array_value(
        program, base_type, member_id, &array) /*@ where p = p, base = cm_member_base_type(e), structs = structs, zs = zs */;
    if (!array) {
      out_rvalue = out_rvalue + 1;
    } else {
    }
  } else if (expr->kind == CMC_EXPR_CALL) {
  /*@ Assert exists (pa : Z) (pb : Z) (pargs : Z) (callee : Z) (args : list cm_expr) (ty : cm_type),
    program == program@pre &&
    fn == fn@pre &&
    fid == fid@pre &&
    expr == expr@pre &&
    lvalue == lvalue@pre &&
    rvalue == rvalue@pre &&
    expr != 0 &&
    cm_wf_program(policy, cg, p) &&
    f == cm_function_at(policy, fid, cm_program_functions(p)) &&
    structs == cm_program_structs(p) &&
    globals == cm_program_globals(p) &&
    locals == cm_function_locals(f) &&
    cm_rep_structs_safe(structs) &&
    cm_expr_wf(policy, p, f, e) &&
    cm_expr_counts_representable(policy, p, fid, e) &&
    e == CMCallE(callee, args, ty) &&
    out_lvalue == 0 &&
    out_rvalue == 0 &&
    cm_args_wf(policy, p, f, args, cm_function_params(cm_function_at(policy, callee, cm_program_functions(p)))) &&
    cm_args_counts_representable(policy, p, fid, args) &&
    pa == 0 &&
    pb == 0 &&
    data_at(&(program->structs), struct cm_struct *, zs) *
    cm_struct_list_rep(zs, structs) *
    data_at(&(program->globals), struct cm_global *, zg) *
    cm_global_list_rep(zg, globals) *
    data_at(&(fn->locals), struct cm_slot *, zl) *
    cm_slot_list_rep(zl, locals) *
    data_at(&(expr->kind), int, cm_rep_expr_kind(e)) *
    data_at(&(expr->op), int, cm_rep_expr_op(e)) *
    data_at(&(expr->ty), int, cm_type_encode(cm_expr_type(e))) *
    data_at(&(expr->value), long long, cm_rep_expr_value(e)) *
    data_at(&(expr->a), struct cm_expr *, pa) *
    data_at(&(expr->b), struct cm_expr *, pb) *
    data_at(&(expr->args), struct cm_arg *, pargs) *
    cm_arg_list_rep(pargs, args) *
    undef_data_at(lvalue, int) *
    undef_data_at(rvalue, int)
  */
    int args_count;
    cmc_args_code_count(
        program, fid, fn, expr->args, &args_count) /*@ where policy = policy, cg = cg, p = p, f = f, structs = structs, globals = globals, locals = locals, zs = zs, zg = zg, zl = zl */;
    out_rvalue = args_count;
  } else if (expr->kind == CMC_EXPR_PUTC) {
  /*@ Assert exists (pa : Z) (pb : Z) (pargs : Z) (x : cm_expr) (ty : cm_type),
    program == program@pre &&
    fn == fn@pre &&
    fid == fid@pre &&
    expr == expr@pre &&
    lvalue == lvalue@pre &&
    rvalue == rvalue@pre &&
    expr != 0 &&
    cm_wf_program(policy, cg, p) &&
    f == cm_function_at(policy, fid, cm_program_functions(p)) &&
    structs == cm_program_structs(p) &&
    globals == cm_program_globals(p) &&
    locals == cm_function_locals(f) &&
    cm_rep_structs_safe(structs) &&
    cm_expr_wf(policy, p, f, e) &&
    cm_expr_counts_representable(policy, p, fid, e) &&
    e == CMPutcE(x, ty) &&
    out_lvalue == 0 &&
    out_rvalue == 0 &&
    cm_expr_wf(policy, p, f, x) &&
    cm_expr_counts_representable(policy, p, fid, x) &&
    pa != 0 &&
    pb == 0 &&
    pargs == 0 &&
    data_at(&(program->structs), struct cm_struct *, zs) *
    cm_struct_list_rep(zs, structs) *
    data_at(&(program->globals), struct cm_global *, zg) *
    cm_global_list_rep(zg, globals) *
    data_at(&(fn->locals), struct cm_slot *, zl) *
    cm_slot_list_rep(zl, locals) *
    data_at(&(expr->kind), int, cm_rep_expr_kind(e)) *
    data_at(&(expr->op), int, cm_rep_expr_op(e)) *
    data_at(&(expr->ty), int, cm_type_encode(cm_expr_type(e))) *
    data_at(&(expr->value), long long, cm_rep_expr_value(e)) *
    data_at(&(expr->a), struct cm_expr *, pa) *
    data_at(&(expr->b), struct cm_expr *, pb) *
    data_at(&(expr->args), struct cm_arg *, pargs) *
    cm_expr_rep(pa, x) *
    undef_data_at(lvalue, int) *
    undef_data_at(rvalue, int)
  */
    int child_lvalue;
    int child_rvalue;
    cm_expr_counts(program, fid, fn, expr->a,
                   &child_lvalue, &child_rvalue) /*@ where policy = policy, cg = cg, p = p, f = f, structs = structs, globals = globals, locals = locals, zs = zs, zg = zg, zl = zl */;
    out_rvalue = child_rvalue + 2;
  } else if (expr->kind == CMC_EXPR_PUTI) {
  /*@ Assert exists (pa : Z) (pb : Z) (pargs : Z) (x : cm_expr) (ty : cm_type),
    program == program@pre &&
    fn == fn@pre &&
    fid == fid@pre &&
    expr == expr@pre &&
    lvalue == lvalue@pre &&
    rvalue == rvalue@pre &&
    expr != 0 &&
    cm_wf_program(policy, cg, p) &&
    f == cm_function_at(policy, fid, cm_program_functions(p)) &&
    structs == cm_program_structs(p) &&
    globals == cm_program_globals(p) &&
    locals == cm_function_locals(f) &&
    cm_rep_structs_safe(structs) &&
    cm_expr_wf(policy, p, f, e) &&
    cm_expr_counts_representable(policy, p, fid, e) &&
    e == CMPutiE(x, ty) &&
    out_lvalue == 0 &&
    out_rvalue == 0 &&
    cm_expr_wf(policy, p, f, x) &&
    cm_expr_counts_representable(policy, p, fid, x) &&
    pa != 0 &&
    pb == 0 &&
    pargs == 0 &&
    data_at(&(program->structs), struct cm_struct *, zs) *
    cm_struct_list_rep(zs, structs) *
    data_at(&(program->globals), struct cm_global *, zg) *
    cm_global_list_rep(zg, globals) *
    data_at(&(fn->locals), struct cm_slot *, zl) *
    cm_slot_list_rep(zl, locals) *
    data_at(&(expr->kind), int, cm_rep_expr_kind(e)) *
    data_at(&(expr->op), int, cm_rep_expr_op(e)) *
    data_at(&(expr->ty), int, cm_type_encode(cm_expr_type(e))) *
    data_at(&(expr->value), long long, cm_rep_expr_value(e)) *
    data_at(&(expr->a), struct cm_expr *, pa) *
    data_at(&(expr->b), struct cm_expr *, pb) *
    data_at(&(expr->args), struct cm_arg *, pargs) *
    cm_expr_rep(pa, x) *
    undef_data_at(lvalue, int) *
    undef_data_at(rvalue, int)
  */
    int child_lvalue;
    int child_rvalue;
    cm_expr_counts(program, fid, fn, expr->a,
                   &child_lvalue, &child_rvalue) /*@ where policy = policy, cg = cg, p = p, f = f, structs = structs, globals = globals, locals = locals, zs = zs, zg = zg, zl = zl */;
    out_rvalue = child_rvalue + 2;
  } else {
  /*@ Assert exists (pa : Z) (pb : Z) (pargs : Z) (x : cm_expr) (ty : cm_type),
    program == program@pre &&
    fn == fn@pre &&
    fid == fid@pre &&
    expr == expr@pre &&
    lvalue == lvalue@pre &&
    rvalue == rvalue@pre &&
    expr != 0 &&
    cm_wf_program(policy, cg, p) &&
    f == cm_function_at(policy, fid, cm_program_functions(p)) &&
    structs == cm_program_structs(p) &&
    globals == cm_program_globals(p) &&
    locals == cm_function_locals(f) &&
    cm_rep_structs_safe(structs) &&
    cm_expr_wf(policy, p, f, e) &&
    cm_expr_counts_representable(policy, p, fid, e) &&
    e == CMExitE(x, ty) &&
    out_lvalue == 0 &&
    out_rvalue == 0 &&
    cm_expr_wf(policy, p, f, x) &&
    cm_expr_counts_representable(policy, p, fid, x) &&
    pa != 0 &&
    pb == 0 &&
    pargs == 0 &&
    data_at(&(program->structs), struct cm_struct *, zs) *
    cm_struct_list_rep(zs, structs) *
    data_at(&(program->globals), struct cm_global *, zg) *
    cm_global_list_rep(zg, globals) *
    data_at(&(fn->locals), struct cm_slot *, zl) *
    cm_slot_list_rep(zl, locals) *
    data_at(&(expr->kind), int, cm_rep_expr_kind(e)) *
    data_at(&(expr->op), int, cm_rep_expr_op(e)) *
    data_at(&(expr->ty), int, cm_type_encode(cm_expr_type(e))) *
    data_at(&(expr->value), long long, cm_rep_expr_value(e)) *
    data_at(&(expr->a), struct cm_expr *, pa) *
    data_at(&(expr->b), struct cm_expr *, pb) *
    data_at(&(expr->args), struct cm_arg *, pargs) *
    cm_expr_rep(pa, x) *
    undef_data_at(lvalue, int) *
    undef_data_at(rvalue, int)
  */
    int child_lvalue;
    int child_rvalue;
    cm_expr_counts(program, fid, fn, expr->a,
                   &child_lvalue, &child_rvalue) /*@ where policy = policy, cg = cg, p = p, f = f, structs = structs, globals = globals, locals = locals, zs = zs, zg = zg, zl = zl */;
    out_rvalue = child_rvalue + 7;
  }
  *lvalue = out_lvalue;
  *rvalue = out_rvalue;
}

int cmc_stmt_code_count(struct cm_program *program, int fid,
                               struct cm_function *fn,
                               struct cm_stmt *stmt)
/*@ With (policy : cm_lookup_policy) (cg : cm_codegen_obligations) (p : cm_program) (f : cm_function_d) (structs : list cm_struct_d) (globals : list cm_global_d) (locals : list cm_slot_d) (zs : Z) (zg : Z) (zl : Z) (s : cm_stmt) (loop_ : bool)
    Require cm_wf_program(policy, cg, p) && f == cm_function_at(policy, fid, cm_program_functions(p)) && structs == cm_program_structs(p) && globals == cm_program_globals(p) && locals == cm_function_locals(f) && cm_rep_structs_safe(structs) && cm_stmt_wf(policy, p, f, loop_, s) && cm_stmt_counts_representable(policy, p, fid, s) && data_at(&(program->structs), struct cm_struct *, zs) * cm_struct_list_rep(zs, structs) * data_at(&(program->globals), struct cm_global *, zg) * cm_global_list_rep(zg, globals) * data_at(&(fn->locals), struct cm_slot *, zl) * cm_slot_list_rep(zl, locals) * data_at(&(fn->ret_ty), int, cm_type_encode(cm_function_ret(f))) * cm_stmt_rep(stmt, s)
    Ensure cm_wf_program(policy, cg, p) && f == cm_function_at(policy, fid, cm_program_functions(p)) && structs == cm_program_structs(p) && globals == cm_program_globals(p) && locals == cm_function_locals(f) && cm_rep_structs_safe(structs) && cm_stmt_wf(policy, p, f, loop_, s) && cm_stmt_counts_representable(policy, p, fid, s) && __return == cm_stmt_code_count(policy, p, fid, s) && cm_i32_code_count(cm_stmt_code_count(policy, p, fid, s)) && data_at(&(program->structs), struct cm_struct *, zs) * cm_struct_list_rep(zs, structs) * data_at(&(program->globals), struct cm_global *, zg) * cm_global_list_rep(zg, globals) * data_at(&(fn->locals), struct cm_slot *, zl) * cm_slot_list_rep(zl, locals) * data_at(&(fn->ret_ty), int, cm_type_encode(cm_function_ret(f))) * cm_stmt_rep(stmt, s)
*/
{
  /*@ Assert exists (pe : Z) (pa : Z) (pb : Z),
    program == program@pre &&
    fn == fn@pre &&
    fid == fid@pre &&
    stmt == stmt@pre &&
    stmt != 0 &&
    cm_wf_program(policy, cg, p) &&
    f == cm_function_at(policy, fid, cm_program_functions(p)) &&
    structs == cm_program_structs(p) &&
    globals == cm_program_globals(p) &&
    locals == cm_function_locals(f) &&
    cm_rep_structs_safe(structs) &&
    cm_stmt_wf(policy, p, f, loop_, s) &&
    cm_stmt_counts_representable(policy, p, fid, s) &&
    data_at(&(program->structs), struct cm_struct *, zs) *
    cm_struct_list_rep(zs, structs) *
    data_at(&(program->globals), struct cm_global *, zg) *
    cm_global_list_rep(zg, globals) *
    data_at(&(fn->locals), struct cm_slot *, zl) *
    cm_slot_list_rep(zl, locals) *
    data_at(&(fn->ret_ty), int, cm_type_encode(cm_function_ret(f))) *
    data_at(&(stmt->kind), int, cm_rep_stmt_kind(s)) *
    data_at(&(stmt->slot), int, cm_rep_stmt_slot(s)) *
    data_at(&(stmt->expr), struct cm_expr *, pe) *
    data_at(&(stmt->a), struct cm_stmt *, pa) *
    data_at(&(stmt->b), struct cm_stmt *, pb) *
    cm_stmt_payload(s, pe, pa, pb)
  */
  int result = 0;
  if (stmt->kind == CMC_STMT_SKIP) {
  } else if (stmt->kind == CMC_STMT_DECL) {
  } else if (stmt->kind == CMC_STMT_EXPR) {
  /*@ Assert exists (pe : Z) (pa : Z) (pb : Z) (x : cm_expr),
    program == program@pre &&
    fn == fn@pre &&
    fid == fid@pre &&
    stmt == stmt@pre &&
    stmt != 0 &&
    cm_wf_program(policy, cg, p) &&
    f == cm_function_at(policy, fid, cm_program_functions(p)) &&
    structs == cm_program_structs(p) &&
    globals == cm_program_globals(p) &&
    locals == cm_function_locals(f) &&
    cm_rep_structs_safe(structs) &&
    cm_stmt_wf(policy, p, f, loop_, s) &&
    cm_stmt_counts_representable(policy, p, fid, s) &&
    s == CMExprS(x) &&
    result == 0 &&
    cm_expr_wf(policy, p, f, x) &&
    cm_expr_counts_representable(policy, p, fid, x) &&
    pe != 0 &&
    pa == 0 &&
    pb == 0 &&
    data_at(&(program->structs), struct cm_struct *, zs) *
    cm_struct_list_rep(zs, structs) *
    data_at(&(program->globals), struct cm_global *, zg) *
    cm_global_list_rep(zg, globals) *
    data_at(&(fn->locals), struct cm_slot *, zl) *
    cm_slot_list_rep(zl, locals) *
    data_at(&(fn->ret_ty), int, cm_type_encode(cm_function_ret(f))) *
    data_at(&(stmt->kind), int, cm_rep_stmt_kind(s)) *
    data_at(&(stmt->slot), int, cm_rep_stmt_slot(s)) *
    data_at(&(stmt->expr), struct cm_expr *, pe) *
    data_at(&(stmt->a), struct cm_stmt *, pa) *
    data_at(&(stmt->b), struct cm_stmt *, pb) *
    cm_expr_rep(pe, x)
  */
    int expr_count =
        cm_expr_rvalue_count(program, fid, fn, stmt->expr) /*@ where policy = policy, cg = cg, p = p, f = f, structs = structs, globals = globals, locals = locals, zs = zs, zg = zg, zl = zl */;
    result = expr_count + 1;
  } else if (stmt->kind == CMC_STMT_INIT) {
  /*@ Assert exists (pe : Z) (pa : Z) (pb : Z) (slot : Z) (x : cm_expr),
    program == program@pre &&
    fn == fn@pre &&
    fid == fid@pre &&
    stmt == stmt@pre &&
    stmt != 0 &&
    cm_wf_program(policy, cg, p) &&
    f == cm_function_at(policy, fid, cm_program_functions(p)) &&
    structs == cm_program_structs(p) &&
    globals == cm_program_globals(p) &&
    locals == cm_function_locals(f) &&
    cm_rep_structs_safe(structs) &&
    cm_stmt_wf(policy, p, f, loop_, s) &&
    cm_stmt_counts_representable(policy, p, fid, s) &&
    s == CMInitS(slot, x) &&
    result == 0 &&
    0 <= slot &&
    slot < Zlength(locals) &&
    cm_type_code_wf(cm_slot_ty(cm_slot_at(slot, locals))) &&
    cm_expr_wf(policy, p, f, x) &&
    cm_expr_counts_representable(policy, p, fid, x) &&
    pe != 0 &&
    pa == 0 &&
    pb == 0 &&
    data_at(&(program->structs), struct cm_struct *, zs) *
    cm_struct_list_rep(zs, structs) *
    data_at(&(program->globals), struct cm_global *, zg) *
    cm_global_list_rep(zg, globals) *
    data_at(&(fn->locals), struct cm_slot *, zl) *
    cm_slot_list_rep(zl, locals) *
    data_at(&(fn->ret_ty), int, cm_type_encode(cm_function_ret(f))) *
    data_at(&(stmt->kind), int, cm_rep_stmt_kind(s)) *
    data_at(&(stmt->slot), int, cm_rep_stmt_slot(s)) *
    data_at(&(stmt->expr), struct cm_expr *, pe) *
    data_at(&(stmt->a), struct cm_stmt *, pa) *
    data_at(&(stmt->b), struct cm_stmt *, pb) *
    cm_expr_rep(pe, x)
  */
    int ty_code = cmc_slot_type_at(fn->locals, stmt->slot);
    int expr_count =
        cm_expr_rvalue_count(program, fid, fn, stmt->expr) /*@ where policy = policy, cg = cg, p = p, f = f, structs = structs, globals = globals, locals = locals, zs = zs, zg = zg, zl = zl */;
    int normalize = cm_normalize_count(ty_code);
    result = expr_count + normalize + 5;
  } else if (stmt->kind == CMC_STMT_SEQ) {
  /*@ Assert exists (pe : Z) (pa : Z) (pb : Z) (a : cm_stmt) (b : cm_stmt),
    program == program@pre &&
    fn == fn@pre &&
    fid == fid@pre &&
    stmt == stmt@pre &&
    stmt != 0 &&
    cm_wf_program(policy, cg, p) &&
    f == cm_function_at(policy, fid, cm_program_functions(p)) &&
    structs == cm_program_structs(p) &&
    globals == cm_program_globals(p) &&
    locals == cm_function_locals(f) &&
    cm_rep_structs_safe(structs) &&
    cm_stmt_wf(policy, p, f, loop_, s) &&
    cm_stmt_counts_representable(policy, p, fid, s) &&
    s == CMSeqS(a, b) &&
    result == 0 &&
    cm_stmt_wf(policy, p, f, loop_, a) &&
    cm_stmt_counts_representable(policy, p, fid, a) &&
    cm_stmt_wf(policy, p, f, loop_, b) &&
    cm_stmt_counts_representable(policy, p, fid, b) &&
    pe == 0 &&
    data_at(&(program->structs), struct cm_struct *, zs) *
    cm_struct_list_rep(zs, structs) *
    data_at(&(program->globals), struct cm_global *, zg) *
    cm_global_list_rep(zg, globals) *
    data_at(&(fn->locals), struct cm_slot *, zl) *
    cm_slot_list_rep(zl, locals) *
    data_at(&(fn->ret_ty), int, cm_type_encode(cm_function_ret(f))) *
    data_at(&(stmt->kind), int, cm_rep_stmt_kind(s)) *
    data_at(&(stmt->slot), int, cm_rep_stmt_slot(s)) *
    data_at(&(stmt->expr), struct cm_expr *, pe) *
    data_at(&(stmt->a), struct cm_stmt *, pa) *
    data_at(&(stmt->b), struct cm_stmt *, pb) *
    cm_stmt_rep(pa, a) *
    cm_stmt_rep(pb, b)
  */
    int first_count =
        cmc_stmt_code_count(program, fid, fn, stmt->a) /*@ where policy = policy, cg = cg, p = p, f = f, structs = structs, globals = globals, locals = locals, zs = zs, zg = zg, zl = zl, loop_ = loop_ */;
    int second_count =
        cmc_stmt_code_count(program, fid, fn, stmt->b) /*@ where policy = policy, cg = cg, p = p, f = f, structs = structs, globals = globals, locals = locals, zs = zs, zg = zg, zl = zl, loop_ = loop_ */;
    result = first_count + second_count;
  } else if (stmt->kind == CMC_STMT_BLOCK) {
  /*@ Assert exists (pe : Z) (pa : Z) (pb : Z) (a : cm_stmt),
    program == program@pre &&
    fn == fn@pre &&
    fid == fid@pre &&
    stmt == stmt@pre &&
    stmt != 0 &&
    cm_wf_program(policy, cg, p) &&
    f == cm_function_at(policy, fid, cm_program_functions(p)) &&
    structs == cm_program_structs(p) &&
    globals == cm_program_globals(p) &&
    locals == cm_function_locals(f) &&
    cm_rep_structs_safe(structs) &&
    cm_stmt_wf(policy, p, f, loop_, s) &&
    cm_stmt_counts_representable(policy, p, fid, s) &&
    s == CMBlockS(a) &&
    result == 0 &&
    cm_stmt_wf(policy, p, f, loop_, a) &&
    cm_stmt_counts_representable(policy, p, fid, a) &&
    pe == 0 &&
    pa != 0 &&
    pb == 0 &&
    data_at(&(program->structs), struct cm_struct *, zs) *
    cm_struct_list_rep(zs, structs) *
    data_at(&(program->globals), struct cm_global *, zg) *
    cm_global_list_rep(zg, globals) *
    data_at(&(fn->locals), struct cm_slot *, zl) *
    cm_slot_list_rep(zl, locals) *
    data_at(&(fn->ret_ty), int, cm_type_encode(cm_function_ret(f))) *
    data_at(&(stmt->kind), int, cm_rep_stmt_kind(s)) *
    data_at(&(stmt->slot), int, cm_rep_stmt_slot(s)) *
    data_at(&(stmt->expr), struct cm_expr *, pe) *
    data_at(&(stmt->a), struct cm_stmt *, pa) *
    data_at(&(stmt->b), struct cm_stmt *, pb) *
    cm_stmt_rep(pa, a)
  */
    int first_count =
        cmc_stmt_code_count(program, fid, fn, stmt->a) /*@ where policy = policy, cg = cg, p = p, f = f, structs = structs, globals = globals, locals = locals, zs = zs, zg = zg, zl = zl, loop_ = loop_ */;
    result = first_count;
  } else if (stmt->kind == CMC_STMT_IF) {
  /*@ Assert exists (pe : Z) (pa : Z) (pb : Z) (x : cm_expr) (a : cm_stmt) (b : cm_stmt),
    program == program@pre &&
    fn == fn@pre &&
    fid == fid@pre &&
    stmt == stmt@pre &&
    stmt != 0 &&
    cm_wf_program(policy, cg, p) &&
    f == cm_function_at(policy, fid, cm_program_functions(p)) &&
    structs == cm_program_structs(p) &&
    globals == cm_program_globals(p) &&
    locals == cm_function_locals(f) &&
    cm_rep_structs_safe(structs) &&
    cm_stmt_wf(policy, p, f, loop_, s) &&
    cm_stmt_counts_representable(policy, p, fid, s) &&
    s == CMIfS(x, a, b) &&
    result == 0 &&
    cm_expr_wf(policy, p, f, x) &&
    cm_expr_counts_representable(policy, p, fid, x) &&
    cm_stmt_wf(policy, p, f, loop_, a) &&
    cm_stmt_counts_representable(policy, p, fid, a) &&
    cm_stmt_wf(policy, p, f, loop_, b) &&
    cm_stmt_counts_representable(policy, p, fid, b) &&
    data_at(&(program->structs), struct cm_struct *, zs) *
    cm_struct_list_rep(zs, structs) *
    data_at(&(program->globals), struct cm_global *, zg) *
    cm_global_list_rep(zg, globals) *
    data_at(&(fn->locals), struct cm_slot *, zl) *
    cm_slot_list_rep(zl, locals) *
    data_at(&(fn->ret_ty), int, cm_type_encode(cm_function_ret(f))) *
    data_at(&(stmt->kind), int, cm_rep_stmt_kind(s)) *
    data_at(&(stmt->slot), int, cm_rep_stmt_slot(s)) *
    data_at(&(stmt->expr), struct cm_expr *, pe) *
    data_at(&(stmt->a), struct cm_stmt *, pa) *
    data_at(&(stmt->b), struct cm_stmt *, pb) *
    cm_expr_rep(pe, x) *
    cm_stmt_rep(pa, a) *
    cm_stmt_rep(pb, b)
  */
    int expr_count =
        cm_expr_rvalue_count(program, fid, fn, stmt->expr) /*@ where policy = policy, cg = cg, p = p, f = f, structs = structs, globals = globals, locals = locals, zs = zs, zg = zg, zl = zl */;
    int first_count =
        cmc_stmt_code_count(program, fid, fn, stmt->a) /*@ where policy = policy, cg = cg, p = p, f = f, structs = structs, globals = globals, locals = locals, zs = zs, zg = zg, zl = zl, loop_ = loop_ */;
    int second_count =
        cmc_stmt_code_count(program, fid, fn, stmt->b) /*@ where policy = policy, cg = cg, p = p, f = f, structs = structs, globals = globals, locals = locals, zs = zs, zg = zg, zl = zl, loop_ = loop_ */;
    result = expr_count + 1 + first_count + 1 + second_count;
  } else if (stmt->kind == CMC_STMT_WHILE) {
  /*@ Assert exists (pe : Z) (pa : Z) (pb : Z) (x : cm_expr) (a : cm_stmt),
    program == program@pre &&
    fn == fn@pre &&
    fid == fid@pre &&
    stmt == stmt@pre &&
    stmt != 0 &&
    cm_wf_program(policy, cg, p) &&
    f == cm_function_at(policy, fid, cm_program_functions(p)) &&
    structs == cm_program_structs(p) &&
    globals == cm_program_globals(p) &&
    locals == cm_function_locals(f) &&
    cm_rep_structs_safe(structs) &&
    cm_stmt_wf(policy, p, f, loop_, s) &&
    cm_stmt_counts_representable(policy, p, fid, s) &&
    s == CMWhileS(x, a) &&
    result == 0 &&
    cm_expr_wf(policy, p, f, x) &&
    cm_expr_counts_representable(policy, p, fid, x) &&
    cm_stmt_wf(policy, p, f, true, a) &&
    cm_stmt_counts_representable(policy, p, fid, a) &&
    pe != 0 &&
    pa != 0 &&
    pb == 0 &&
    data_at(&(program->structs), struct cm_struct *, zs) *
    cm_struct_list_rep(zs, structs) *
    data_at(&(program->globals), struct cm_global *, zg) *
    cm_global_list_rep(zg, globals) *
    data_at(&(fn->locals), struct cm_slot *, zl) *
    cm_slot_list_rep(zl, locals) *
    data_at(&(fn->ret_ty), int, cm_type_encode(cm_function_ret(f))) *
    data_at(&(stmt->kind), int, cm_rep_stmt_kind(s)) *
    data_at(&(stmt->slot), int, cm_rep_stmt_slot(s)) *
    data_at(&(stmt->expr), struct cm_expr *, pe) *
    data_at(&(stmt->a), struct cm_stmt *, pa) *
    data_at(&(stmt->b), struct cm_stmt *, pb) *
    cm_expr_rep(pe, x) *
    cm_stmt_rep(pa, a)
  */
    int expr_count =
        cm_expr_rvalue_count(program, fid, fn, stmt->expr) /*@ where policy = policy, cg = cg, p = p, f = f, structs = structs, globals = globals, locals = locals, zs = zs, zg = zg, zl = zl */;
    int first_count =
        cmc_stmt_code_count(program, fid, fn, stmt->a) /*@ where policy = policy, cg = cg, p = p, f = f, structs = structs, globals = globals, locals = locals, zs = zs, zg = zg, zl = zl, loop_ = true */;
    result = expr_count + 1 + first_count + 1;
  } else if (stmt->kind == CMC_STMT_BREAK) {
    result = 1;
  } else if (stmt->kind == CMC_STMT_CONTINUE) {
    result = 1;
  } else {
  /*@ Assert exists (pe : Z) (pa : Z) (pb : Z) (x : cm_expr),
    program == program@pre &&
    fn == fn@pre &&
    fid == fid@pre &&
    stmt == stmt@pre &&
    stmt != 0 &&
    cm_wf_program(policy, cg, p) &&
    f == cm_function_at(policy, fid, cm_program_functions(p)) &&
    structs == cm_program_structs(p) &&
    globals == cm_program_globals(p) &&
    locals == cm_function_locals(f) &&
    cm_rep_structs_safe(structs) &&
    cm_stmt_wf(policy, p, f, loop_, s) &&
    cm_stmt_counts_representable(policy, p, fid, s) &&
    s == CMReturnS(x) &&
    result == 0 &&
    cm_type_code_wf(cm_function_ret(f)) &&
    cm_expr_wf(policy, p, f, x) &&
    cm_expr_counts_representable(policy, p, fid, x) &&
    pe != 0 &&
    pa == 0 &&
    pb == 0 &&
    data_at(&(program->structs), struct cm_struct *, zs) *
    cm_struct_list_rep(zs, structs) *
    data_at(&(program->globals), struct cm_global *, zg) *
    cm_global_list_rep(zg, globals) *
    data_at(&(fn->locals), struct cm_slot *, zl) *
    cm_slot_list_rep(zl, locals) *
    data_at(&(fn->ret_ty), int, cm_type_encode(cm_function_ret(f))) *
    data_at(&(stmt->kind), int, cm_rep_stmt_kind(s)) *
    data_at(&(stmt->slot), int, cm_rep_stmt_slot(s)) *
    data_at(&(stmt->expr), struct cm_expr *, pe) *
    data_at(&(stmt->a), struct cm_stmt *, pa) *
    data_at(&(stmt->b), struct cm_stmt *, pb) *
    cm_expr_rep(pe, x)
  */
    int expr_count =
        cm_expr_rvalue_count(program, fid, fn, stmt->expr) /*@ where policy = policy, cg = cg, p = p, f = f, structs = structs, globals = globals, locals = locals, zs = zs, zg = zg, zl = zl */;
    int normalize = cm_normalize_count(fn->ret_ty);
    result = expr_count + normalize + 6;
  }
  return result;
}

static int cmc_param_stores_count(struct cm_slot *param)
/*@ With (params : list cm_slot_d)
    Require cm_param_counts_representable(params) && cm_slot_list_rep(param, params)
    Ensure cm_param_counts_representable(params) && __return == cm_param_stores_count(params) && cm_i32_code_count(__return) && cm_slot_list_rep(param, params)
*/
{
  int result;
  if (param == 0) {
    result = 0;
  } else {
  /*@ Assert exists (h : cm_slot_d) (t : list cm_slot_d) (np : Z),
    param == param@pre &&
    param != 0 &&
    params == cons(h, t) &&
    cm_param_counts_representable(params) &&
    cm_param_counts_representable(t) &&
    cm_type_code_wf(cm_slot_ty(h)) &&
    data_at(&(param->ty), int, cm_type_encode(cm_slot_ty(h))) *
    data_at(&(param->count), int, cm_slot_count(h)) *
    data_at(&(param->next), struct cm_slot *, np) *
    cm_slot_list_rep(np, t) *
    undef_data_at(&result, int)
  */
    int normalize = cm_normalize_count(param->ty);
    struct cm_slot *next = param->next;
    int rest = cmc_param_stores_count(next);
    result = rest + normalize + 5;
  }
  return result;
}

int cmc_function_prologue_count(struct cm_function *fn)
/*@ With (f : cm_function_d) (body : Z) (next : Z)
    Require cm_param_counts_representable(cm_function_params(f)) && cm_i32_code_count(cm_function_prologue_count(f)) && cm_function_context_rep(fn, f, body, next)
    Ensure cm_param_counts_representable(cm_function_params(f)) && cm_i32_code_count(cm_function_prologue_count(f)) && __return == cm_function_prologue_count(f) && cm_i32_code_count(__return) && cm_function_context_rep(fn, f, body, next)
*/
{
  /*@ Assert exists (pp : Z) (lp : Z),
    fn == fn@pre &&
    fn != 0 &&
    cm_param_counts_representable(cm_function_params(f)) &&
    cm_i32_code_count(cm_function_prologue_count(f)) &&
    data_at(&(fn->ret_ty), int, cm_type_encode(cm_function_ret(f))) *
    data_at(&(fn->params), struct cm_slot *, pp) *
    data_at(&(fn->locals), struct cm_slot *, lp) *
    data_at(&(fn->body), struct cm_stmt *, body) *
    data_at(&(fn->next), struct cm_function *, next) *
    cm_slot_list_rep(pp, cm_function_params(f)) *
    cm_slot_list_rep(lp, cm_function_locals(f))
  */
  int params_count = cmc_param_stores_count(fn->params);
  int result = 14 + params_count;
  return result;
}

int cmc_function_code_count(struct cm_program *program, int fid,
                                   struct cm_function *fn)
/*@ With (policy : cm_lookup_policy) (cg : cm_codegen_obligations) (p : cm_program) (f : cm_function_d) (functions_ptr : Z) (body_ptr : Z) (next_ptr : Z)
    Require cm_wf_program(policy, cg, p) && cm_function_counts_representable(policy, p, fid, f) && cm_stmt_wf(policy, p, f, false, cm_function_body(f)) && cm_rep_structs_safe(cm_program_structs(p)) && cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body_ptr, next_ptr) * cm_stmt_rep(body_ptr, cm_function_body(f))
    Ensure cm_wf_program(policy, cg, p) && cm_function_counts_representable(policy, p, fid, f) && cm_stmt_wf(policy, p, f, false, cm_function_body(f)) && cm_rep_structs_safe(cm_program_structs(p)) && __return == cm_function_code_count(policy, p, fid) && cm_i32_code_count(__return) && cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body_ptr, next_ptr) * cm_stmt_rep(body_ptr, cm_function_body(f))
*/
{
  int prologue_count = cmc_function_prologue_count(fn) /*@ where f = f, body = body_ptr, next = next_ptr */;
  /*@ Assert exists (pp : Z) (lp : Z) (sp : Z) (gp : Z) (tp : Z),
    program == program@pre &&
    fn == fn@pre &&
    fid == fid@pre &&
    program != 0 &&
    fn != 0 &&
    cm_wf_program(policy, cg, p) &&
    cm_function_counts_representable(policy, p, fid, f) &&
    cm_stmt_wf(policy, p, f, false, cm_function_body(f)) &&
    cm_rep_structs_safe(cm_program_structs(p)) &&
    f == cm_function_at(policy, fid, cm_program_functions(p)) &&
    prologue_count == cm_function_prologue_count(f) &&
    cm_i32_code_count(prologue_count) &&
    cm_stmt_counts_representable(policy, p, fid, cm_function_body(f)) &&
    data_at(&(program->structs), struct cm_struct *, sp) *
    data_at(&(program->globals), struct cm_global *, gp) *
    data_at(&(program->strings), struct cm_string *, tp) *
    data_at(&(program->functions), struct cm_function *, functions_ptr) *
    data_at(&(program->main_id), int, cm_program_main(p)) *
    cm_struct_list_rep(sp, cm_program_structs(p)) *
    cm_global_list_rep(gp, cm_program_globals(p)) *
    cm_string_list_rep(tp, cm_program_strings(p)) *
    data_at(&(fn->ret_ty), int, cm_type_encode(cm_function_ret(f))) *
    data_at(&(fn->params), struct cm_slot *, pp) *
    data_at(&(fn->locals), struct cm_slot *, lp) *
    data_at(&(fn->body), struct cm_stmt *, body_ptr) *
    data_at(&(fn->next), struct cm_function *, next_ptr) *
    cm_slot_list_rep(pp, cm_function_params(f)) *
    cm_slot_list_rep(lp, cm_function_locals(f)) *
    cm_stmt_rep(body_ptr, cm_function_body(f))
  */
  int body_count =
      cmc_stmt_code_count(program, fid, fn, fn->body) /*@ where policy = policy, cg = cg, p = p, f = f, structs = cm_program_structs(p), globals = cm_program_globals(p), locals = cm_function_locals(f), s = cm_function_body(f), loop_ = false */;
  int result = prologue_count + body_count + 7;
  return result;
}

static int cmc_function_prefix_count(
    struct cm_program *program, struct cm_function *fn,
    int index, int remaining)
/*@ With (policy : cm_lookup_policy) (cg : cm_codegen_obligations) (p : cm_program) (functions : list cm_function_d) (functions_ptr : Z)
    Require cm_wf_program(policy, cg, p) && cm_rep_structs_safe(cm_program_structs(p)) && 0 <= index && index == Zlength(cm_program_functions(p)) - Zlength(functions) && cm_functions_counts_representable(policy, p, functions, index) && 0 <= remaining && remaining <= Zlength(functions) && index + remaining <= 2147483647 && cm_i32_code_count(11 + cm_function_prefix(policy, p, functions, remaining)) && cm_program_context_rep(program, p, functions_ptr) * cm_function_list_rep(fn, functions)
    Ensure cm_wf_program(policy, cg, p) && cm_rep_structs_safe(cm_program_structs(p)) && 0 <= index && index == Zlength(cm_program_functions(p)) - Zlength(functions) && cm_functions_counts_representable(policy, p, functions, index) && 0 <= remaining && remaining <= Zlength(functions) && index + remaining <= 2147483647 && cm_i32_code_count(11 + cm_function_prefix(policy, p, functions, remaining)) && __return == cm_function_prefix(policy, p, functions, remaining) && cm_i32_code_count(__return) && cm_program_context_rep(program, p, functions_ptr) * cm_function_list_rep(fn, functions)
*/
{
  if (remaining == 0) {
    return 0;
  };
  if (fn == 0) {
    return 0;
  };
  /*@ Assert exists (f : cm_function_d) (rest : list cm_function_d) (bp : Z) (np : Z),
    program == program@pre &&
    fn == fn@pre &&
    index == index@pre &&
    fn != 0 &&
    functions == cons(f, rest) &&
    cm_function_counts_representable(policy, p, index, f) &&
    cm_stmt_wf(policy, p, f, false, cm_function_body(f)) &&
    cm_functions_counts_representable(policy, p, rest, index + 1) &&
    remaining == remaining@pre &&
    remaining != 0 &&
    cm_wf_program(policy, cg, p) &&
    cm_rep_structs_safe(cm_program_structs(p)) &&
    0 <= index &&
    index == Zlength(cm_program_functions(p)) - Zlength(functions) &&
    cm_functions_counts_representable(policy, p, functions, index) &&
    0 <= remaining &&
    remaining <= Zlength(functions) &&
    index + remaining <= 2147483647 &&
    cm_i32_code_count(11 + cm_function_prefix(policy, p, functions, remaining)) &&
    cm_program_context_rep(program, p, functions_ptr) *
    cm_function_context_rep(fn, f, bp, np) *
    cm_stmt_rep(bp, cm_function_body(f)) *
    cm_function_list_rep(np, rest)
  */
  int head_count =
      cmc_function_code_count(program, index, fn) /*@ where policy = policy, cg = cg, p = p, functions_ptr = functions_ptr */;
  /*@ Assert exists (f : cm_function_d) (rest : list cm_function_d) (bp : Z) (np : Z) (pp : Z) (lp : Z),
    program == program@pre &&
    fn == fn@pre &&
    index == index@pre &&
    fn != 0 &&
    functions == cons(f, rest) &&
    cm_function_counts_representable(policy, p, index, f) &&
    cm_stmt_wf(policy, p, f, false, cm_function_body(f)) &&
    cm_functions_counts_representable(policy, p, rest, index + 1) &&
    remaining == remaining@pre &&
    remaining != 0 &&
    cm_wf_program(policy, cg, p) &&
    cm_rep_structs_safe(cm_program_structs(p)) &&
    0 <= index &&
    index == Zlength(cm_program_functions(p)) - Zlength(functions) &&
    cm_functions_counts_representable(policy, p, functions, index) &&
    0 <= remaining &&
    remaining <= Zlength(functions) &&
    index + remaining <= 2147483647 &&
    cm_i32_code_count(11 + cm_function_prefix(policy, p, functions, remaining)) &&
    head_count == cm_function_code_count(policy, p, index) &&
    cm_i32_code_count(head_count) &&
    cm_program_context_rep(program, p, functions_ptr) *
    data_at(&(fn->ret_ty), int, cm_type_encode(cm_function_ret(f))) *
    data_at(&(fn->params), struct cm_slot *, pp) *
    data_at(&(fn->locals), struct cm_slot *, lp) *
    data_at(&(fn->body), struct cm_stmt *, bp) *
    data_at(&(fn->next), struct cm_function *, np) *
    cm_slot_list_rep(pp, cm_function_params(f)) *
    cm_slot_list_rep(lp, cm_function_locals(f)) *
    cm_stmt_rep(bp, cm_function_body(f)) *
    cm_function_list_rep(np, rest)
  */
  struct cm_function *next = fn->next;
  int tail_count = cmc_function_prefix_count(
      program, next, index + 1, remaining - 1) /*@ where policy = policy, cg = cg, p = p, functions_ptr = functions_ptr */;
  int result = head_count + tail_count;
  return result;
}

int cmc_function_pc(struct cm_program *program, int fid)
/*@ With (policy : cm_lookup_policy) (cg : cm_codegen_obligations) (p : cm_program) (functions_ptr : Z)
    Require cm_wf_program(policy, cg, p) && cm_rep_structs_safe(cm_program_structs(p)) && 0 <= fid && fid <= Zlength(cm_program_functions(p)) && cm_i32_code_count(cm_function_pc(policy, p, fid)) && cm_program_context_rep(program, p, functions_ptr) * cm_function_list_rep(functions_ptr, cm_program_functions(p))
    Ensure cm_wf_program(policy, cg, p) && cm_rep_structs_safe(cm_program_structs(p)) && 0 <= fid && fid <= Zlength(cm_program_functions(p)) && cm_i32_code_count(cm_function_pc(policy, p, fid)) && __return == cm_function_pc(policy, p, fid) && cm_i32_code_count(__return) && cm_program_context_rep(program, p, functions_ptr) * cm_function_list_rep(functions_ptr, cm_program_functions(p))
*/
{
  /*@ Assert exists (sp : Z) (gp : Z) (tp : Z),
    program == program@pre &&
    program != 0 &&
    fid == fid@pre &&
    cm_wf_program(policy, cg, p) &&
    cm_rep_structs_safe(cm_program_structs(p)) &&
    0 <= fid &&
    fid <= Zlength(cm_program_functions(p)) &&
    cm_i32_code_count(cm_function_pc(policy, p, fid)) &&
    data_at(&(program->structs), struct cm_struct *, sp) *
    data_at(&(program->globals), struct cm_global *, gp) *
    data_at(&(program->strings), struct cm_string *, tp) *
    data_at(&(program->functions), struct cm_function *, functions_ptr) *
    data_at(&(program->main_id), int, cm_program_main(p)) *
    cm_struct_list_rep(sp, cm_program_structs(p)) *
    cm_global_list_rep(gp, cm_program_globals(p)) *
    cm_string_list_rep(tp, cm_program_strings(p)) *
    cm_function_list_rep(functions_ptr, cm_program_functions(p))
  */
  struct cm_function *fn = program->functions;
  /*@ Assert program == program@pre &&
    program != 0 &&
    fn == functions_ptr &&
    cm_wf_program(policy, cg, p) &&
    cm_rep_structs_safe(cm_program_structs(p)) &&
    cm_functions_counts_representable(policy, p, cm_program_functions(p), 0) &&
    fid == fid@pre &&
    0 <= fid &&
    fid <= Zlength(cm_program_functions(p)) &&
    cm_i32_code_count(cm_function_pc(policy, p, fid)) &&
    cm_program_context_rep(program, p, functions_ptr) *
    cm_function_list_rep(functions_ptr, cm_program_functions(p))
  */
  int prefix =
      cmc_function_prefix_count(program, fn, 0, fid) /*@ where policy = policy, cg = cg, p = p, functions_ptr = functions_ptr, functions = cm_program_functions(p) */;
  int result = 11 + prefix;
  return result;
}

static int cmc_functions_code_size_count(
    struct cm_program *program, struct cm_function *fn, int index)
/*@ With (policy : cm_lookup_policy) (cg : cm_codegen_obligations) (p : cm_program) (functions : list cm_function_d) (functions_ptr : Z)
    Require cm_wf_program(policy, cg, p) && cm_rep_structs_safe(cm_program_structs(p)) && 0 <= index && index == Zlength(cm_program_functions(p)) - Zlength(functions) && cm_functions_counts_representable(policy, p, functions, index) && index + Zlength(functions) <= 2147483647 && cm_i32_code_count(cm_functions_code_size(policy, p, functions, index)) && cm_program_context_rep(program, p, functions_ptr) * cm_function_list_rep(fn, functions)
    Ensure cm_wf_program(policy, cg, p) && cm_rep_structs_safe(cm_program_structs(p)) && 0 <= index && index == Zlength(cm_program_functions(p)) - Zlength(functions) && cm_functions_counts_representable(policy, p, functions, index) && index + Zlength(functions) <= 2147483647 && cm_i32_code_count(cm_functions_code_size(policy, p, functions, index)) && __return == cm_functions_code_size(policy, p, functions, index) && cm_i32_code_count(__return) && cm_program_context_rep(program, p, functions_ptr) * cm_function_list_rep(fn, functions)
*/
{
  if (fn == 0) {
    return 0;
  };
  /*@ Assert exists (f : cm_function_d) (rest : list cm_function_d) (bp : Z) (np : Z),
    program == program@pre &&
    fn == fn@pre &&
    index == index@pre &&
    fn != 0 &&
    functions == cons(f, rest) &&
    cm_function_counts_representable(policy, p, index, f) &&
    cm_stmt_wf(policy, p, f, false, cm_function_body(f)) &&
    cm_functions_counts_representable(policy, p, rest, index + 1) &&
    cm_wf_program(policy, cg, p) &&
    cm_rep_structs_safe(cm_program_structs(p)) &&
    0 <= index &&
    index == Zlength(cm_program_functions(p)) - Zlength(functions) &&
    cm_functions_counts_representable(policy, p, functions, index) &&
    index + Zlength(functions) <= 2147483647 &&
    cm_i32_code_count(cm_functions_code_size(policy, p, functions, index)) &&
    cm_program_context_rep(program, p, functions_ptr) *
    cm_function_context_rep(fn, f, bp, np) *
    cm_stmt_rep(bp, cm_function_body(f)) *
    cm_function_list_rep(np, rest)
  */
  int head_count =
      cmc_function_code_count(program, index, fn) /*@ where policy = policy, cg = cg, p = p, functions_ptr = functions_ptr */;
  /*@ Assert exists (f : cm_function_d) (rest : list cm_function_d) (bp : Z) (np : Z) (pp : Z) (lp : Z),
    program == program@pre &&
    fn == fn@pre &&
    index == index@pre &&
    fn != 0 &&
    functions == cons(f, rest) &&
    cm_function_counts_representable(policy, p, index, f) &&
    cm_stmt_wf(policy, p, f, false, cm_function_body(f)) &&
    cm_functions_counts_representable(policy, p, rest, index + 1) &&
    cm_wf_program(policy, cg, p) &&
    cm_rep_structs_safe(cm_program_structs(p)) &&
    0 <= index &&
    index == Zlength(cm_program_functions(p)) - Zlength(functions) &&
    cm_functions_counts_representable(policy, p, functions, index) &&
    index + Zlength(functions) <= 2147483647 &&
    cm_i32_code_count(cm_functions_code_size(policy, p, functions, index)) &&
    head_count == cm_function_code_count(policy, p, index) &&
    cm_i32_code_count(head_count) &&
    cm_program_context_rep(program, p, functions_ptr) *
    data_at(&(fn->ret_ty), int, cm_type_encode(cm_function_ret(f))) *
    data_at(&(fn->params), struct cm_slot *, pp) *
    data_at(&(fn->locals), struct cm_slot *, lp) *
    data_at(&(fn->body), struct cm_stmt *, bp) *
    data_at(&(fn->next), struct cm_function *, np) *
    cm_slot_list_rep(pp, cm_function_params(f)) *
    cm_slot_list_rep(lp, cm_function_locals(f)) *
    cm_stmt_rep(bp, cm_function_body(f)) *
    cm_function_list_rep(np, rest)
  */
  struct cm_function *next = fn->next;
  int tail_count =
      cmc_functions_code_size_count(program, next, index + 1) /*@ where policy = policy, cg = cg, p = p, functions_ptr = functions_ptr */;
  int result = head_count + tail_count;
  return result;
}

int cmc_model_code_length(struct cm_program *program)
/*@ With (policy : cm_lookup_policy) (cg : cm_codegen_obligations) (p : cm_program) (functions_ptr : Z)
    Require cm_wf_program(policy, cg, p) && cm_rep_structs_safe(cm_program_structs(p)) && cm_program_context_rep(program, p, functions_ptr) * cm_function_list_rep(functions_ptr, cm_program_functions(p))
    Ensure cm_wf_program(policy, cg, p) && cm_rep_structs_safe(cm_program_structs(p)) && __return == cm_model_code_length(policy, p) && cm_i32_code_count(__return) && cm_program_context_rep(program, p, functions_ptr) * cm_function_list_rep(functions_ptr, cm_program_functions(p))
*/
{
  /*@ Assert exists (sp : Z) (gp : Z) (tp : Z),
    program == program@pre &&
    program != 0 &&
    cm_wf_program(policy, cg, p) &&
    cm_rep_structs_safe(cm_program_structs(p)) &&
    data_at(&(program->structs), struct cm_struct *, sp) *
    data_at(&(program->globals), struct cm_global *, gp) *
    data_at(&(program->strings), struct cm_string *, tp) *
    data_at(&(program->functions), struct cm_function *, functions_ptr) *
    data_at(&(program->main_id), int, cm_program_main(p)) *
    cm_struct_list_rep(sp, cm_program_structs(p)) *
    cm_global_list_rep(gp, cm_program_globals(p)) *
    cm_string_list_rep(tp, cm_program_strings(p)) *
    cm_function_list_rep(functions_ptr, cm_program_functions(p))
  */
  struct cm_function *functions = program->functions;
  /*@ Assert program == program@pre &&
    program != 0 &&
    functions == functions_ptr &&
    cm_wf_program(policy, cg, p) &&
    cm_rep_structs_safe(cm_program_structs(p)) &&
    cm_functions_counts_representable(policy, p, cm_program_functions(p), 0) &&
    cm_i32_code_count(cm_model_code_length(policy, p)) &&
    Zlength(cm_program_functions(p)) <= 2147483647 &&
    cm_program_context_rep(program, p, functions_ptr) *
    cm_function_list_rep(functions_ptr, cm_program_functions(p))
  */
  int functions_size =
      cmc_functions_code_size_count(program, functions, 0) /*@ where policy = policy, cg = cg, p = p, functions_ptr = functions_ptr, functions = cm_program_functions(p) */;
  int result = 11 + functions_size;
  return result;
}

int cmc_model_data_length(struct cm_program *program)
/*@ With (policy : cm_lookup_policy) (cg : cm_codegen_obligations) (p : cm_program) (functions_ptr : Z)
    Require cm_wf_program(policy, cg, p) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) && cm_model_data_length(p) == 8 + cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) && cm_program_context_rep(program, p, functions_ptr)
    Ensure cm_wf_program(policy, cg, p) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) && cm_model_data_length(p) == 8 + cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) && __return == cm_model_data_length(p) && cm_i32_code_count(__return) && cm_program_context_rep(program, p, functions_ptr)
*/
{
  /*@ Assert exists (sp : Z) (gp : Z) (tp : Z),
    program == program@pre &&
    program != 0 &&
    cm_wf_program(policy, cg, p) &&
    cm_rep_globals_safe(cm_program_globals(p)) &&
    cm_rep_strings_safe(cm_program_strings(p)) &&
    cm_model_data_length(p) == 8 + cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) &&
    data_at(&(program->structs), struct cm_struct *, sp) *
    data_at(&(program->globals), struct cm_global *, gp) *
    data_at(&(program->strings), struct cm_string *, tp) *
    data_at(&(program->functions), struct cm_function *, functions_ptr) *
    data_at(&(program->main_id), int, cm_program_main(p)) *
    cm_struct_list_rep(sp, cm_program_structs(p)) *
    cm_global_list_rep(gp, cm_program_globals(p)) *
    cm_string_list_rep(tp, cm_program_strings(p))
  */
  struct cm_global *globals = program->globals;
  struct cm_string *strings = program->strings;
  long long global_size = cmc_globals_size(globals);
  long long string_size = cmc_strings_size(strings);
  long long total = 8LL + global_size;
  total = total + string_size;
  int result = (int)total;
  return result;
}
