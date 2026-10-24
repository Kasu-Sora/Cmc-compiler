#include "cmc_layout_migration_abi.h"

struct cm_emitter {
  struct cm_output *output;
  int pc;
};

/*@ Extern Coq
 (cm_type :: *) (cm_expr :: *) (cm_leaf_expr :: *) (cm_program :: *)
 (cm_function_d :: *) (cm_struct_d :: *) (cm_global_d :: *) (cm_string_d :: *)
 (cm_lookup_policy :: *) (tvm_inst :: *) (tvm_opcode :: *)
*/
/*@ Extern Coq
 (CMConstE : Z -> cm_type -> cm_expr)
 (CMStringE : Z -> cm_type -> cm_expr)
 (CMGetcE : cm_type -> cm_expr)
 (CMSizeofE : cm_type -> cm_type -> cm_expr)
 (CMLeafConst : Z -> cm_type -> cm_leaf_expr)
 (CMLeafString : Z -> cm_type -> cm_leaf_expr)
 (CMLeafGetc : cm_type -> cm_leaf_expr)
 (CMLeafSizeof : cm_type -> cm_type -> cm_leaf_expr)
 (cm_leaf_code_for : cm_program -> cm_leaf_expr -> Z -> list tvm_inst)
 (cm_const_immediate : cm_type -> Z -> Z)
 (cm_string_address : cm_program -> Z -> Z)
 (cm_type_encode : cm_type -> Z)
 (cm_type_code_wf : cm_type -> Prop)
 (cm_type_refs : list cm_struct_d -> cm_type -> Prop)
 (cm_type_size : list cm_struct_d -> cm_type -> Z)
 (cm_typed_program : cm_lookup_policy -> cm_program -> Prop)
 (cm_i32_code_count : Z -> Prop)
 (cm_member_valid : cm_program -> cm_type -> Z -> Prop)
 (cm_member_array_code : cm_program -> cm_type -> Z -> Z)
 (cm_member_offset : list cm_struct_d -> Z -> Z -> Z)
 (cm_struct_id : cm_type -> Z)
 (cm_pointee : cm_type -> cm_type)
 (cm_program_structs : cm_program -> list cm_struct_d)
 (cm_program_globals : cm_program -> list cm_global_d)
 (cm_program_strings : cm_program -> list cm_string_d)
 (cm_program_functions : cm_program -> list cm_function_d)
 (cm_program_main : cm_program -> Z)
 (cm_function_at : cm_lookup_policy -> Z -> list cm_function_d -> cm_function_d)
 (cm_rep_structs_safe : list cm_struct_d -> Prop)
 (cm_rep_globals_safe : list cm_global_d -> Prop)
 (cm_rep_strings_safe : list cm_string_d -> Prop)
 (cm_rep_globals_size : list cm_global_d -> Z)
 (cm_rep_strings_size : list cm_string_d -> Z)
 (cm_rep_string_address : list cm_global_d -> list cm_string_d -> Z -> Z)
 (cm_rep_type_size : list cm_struct_d -> Z -> Z)
 (cm_rep_struct_member_prefix : list cm_struct_d -> Z -> Z -> Z)
 (cm_program_context_rep : Z -> cm_program -> Z -> Assertion)
 (cm_function_context_rep : Z -> cm_function_d -> Z -> Z -> Assertion)
 (cm_expr_rep : Z -> cm_expr -> Assertion)
 (cm_struct_list_rep : Z -> list cm_struct_d -> Assertion)
 (cm_global_list_rep : Z -> list cm_global_d -> Assertion)
 (cm_string_list_rep : Z -> list cm_string_d -> Assertion)
 (cm_rep_expr_kind : cm_expr -> Z)
 (cm_rep_expr_op : cm_expr -> Z)
 (cm_rep_expr_value : cm_expr -> Z)
 (cm_expr_type : cm_expr -> cm_type)
 (cm_expr_payload : cm_expr -> Z -> Z -> Z -> Assertion)
 (cm_resolved_emitter_plan_rep : cm_lookup_policy -> cm_program -> Z -> Z -> Z -> list tvm_inst -> list tvm_inst -> Assertion)
 (TVMInst : tvm_opcode -> Z -> tvm_inst)
 (TVMPushOp : tvm_opcode)
 (TVMGetcOp : tvm_opcode)
 (tvm_opcode_code : tvm_opcode -> Z)
*/
/*@ Import Coq Require Import SimpleC.EE.QCP_demos_human.cmc_emit_expr_leaf_migration_lib */

long long cmc_string_address(struct cm_global *globals,
                                    struct cm_string *strings, int index)
/*@ With (global_items : list cm_global_d) (string_items : list cm_string_d)
    Require 0 <= index && cm_rep_globals_safe(global_items) && cm_rep_strings_safe(string_items) && cm_rep_globals_size(global_items) + cm_rep_strings_size(string_items) <= 1048560 && cm_global_list_rep(globals, global_items) * cm_string_list_rep(strings, string_items)
    Ensure 0 <= index && cm_rep_globals_safe(global_items) && cm_rep_strings_safe(string_items) && cm_rep_globals_size(global_items) + cm_rep_strings_size(string_items) <= 1048560 && __return == cm_rep_string_address(global_items, string_items, index) && 16 <= __return && __return <= 1048576 && cm_global_list_rep(globals, global_items) * cm_string_list_rep(strings, string_items)
*/;

long long cmc_type_size_at(struct cm_struct *items, int ty)
/*@ With (structs : list cm_struct_d)
    Require 0 <= ty && cm_rep_structs_safe(structs) && cm_struct_list_rep(items, structs)
    Ensure 0 <= ty && cm_rep_structs_safe(structs) && __return == cm_rep_type_size(structs, ty) && cm_struct_list_rep(items, structs)
*/;

long long cmc_member_offset_at(struct cm_struct *item,
                                      int sid, int index)
/*@ With (structs : list cm_struct_d)
    Require 0 <= sid && 0 <= index && cm_rep_structs_safe(structs) && cm_struct_list_rep(item, structs)
    Ensure 0 <= sid && 0 <= index && cm_rep_structs_safe(structs) && __return == cm_rep_struct_member_prefix(structs, sid, index) && 0 <= __return && __return <= 1048576 && cm_struct_list_rep(item, structs)
*/;

int cmc_pointee(int ty)
/*@ Require 1024 <= ty && ty <= 2147483647 && emp
    Ensure __return == ty - 1024 && emp
*/;

int cmc_member_array(struct cm_program *program, int base_ty, int mid)
/*@ With (p : cm_program) (base : cm_type) (structs : list cm_struct_d) (zs : Z)
    Require 1024 <= base_ty && base_ty <= 2147483647 && 0 <= (base_ty - 1024) % 1024 - 2 && 0 <= mid && structs == cm_program_structs(p) && base_ty == cm_type_encode(base) && cm_type_code_wf(base) && cm_member_valid(p, base, mid) && cm_rep_structs_safe(structs) && data_at(&(program->structs), struct cm_struct *, zs) * cm_struct_list_rep(zs, structs)
    Ensure 1024 <= base_ty && base_ty <= 2147483647 && 0 <= (base_ty - 1024) % 1024 - 2 && 0 <= mid && structs == cm_program_structs(p) && base_ty == cm_type_encode(base) && cm_type_code_wf(base) && cm_member_valid(p, base, mid) && cm_rep_structs_safe(structs) && __return == cm_member_array_code(p, base, mid) && data_at(&(program->structs), struct cm_struct *, zs) * cm_struct_list_rep(zs, structs)
*/;

void cm_emit_plan(struct cm_emitter *emitter, int op,
                  long long immediate)
/*@ With (policy : cm_lookup_policy) (p : cm_program) (done : list tvm_inst) (tail : list tvm_inst) (out : Z) (capacity : Z) (opcode : tvm_opcode)
    Require op == tvm_opcode_code(opcode) && tvm_opcode_code(opcode) != 22 && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, cons(TVMInst(opcode, immediate), tail))
    Ensure cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cons(TVMInst(opcode, immediate), nil)), tail)
*/;

static long long cmc_const_immediate(long long value, int ty)
/*@ With (model_ty : cm_type)
 Require ty == cm_type_encode(model_ty) && cm_type_code_wf(model_ty) && emp
 Ensure ty == cm_type_encode(model_ty) && cm_type_code_wf(model_ty) && __return == cm_const_immediate(model_ty, value) && emp
*/
{
  if (ty == CMC_TYPE_CHAR) {
    unsigned long long bits = (unsigned long long)value;
    unsigned char byte = (unsigned char)(bits % 256ULL);
    return (long long)byte;
  } else {
    return value;
  }
}

void cm_emit_const_expr(struct cm_program *program, int fid,
                        struct cm_function *fn, int pc, int temp,
                        struct cm_expr *expr, int lvalue,
                        struct cm_emitter *emitter)
/*@ With (policy : cm_lookup_policy) (p : cm_program) (f : cm_function_d) (e : cm_expr) (ty : cm_type) (body : Z) (next : Z) (functions_ptr : Z) (done : list tvm_inst) (tail : list tvm_inst) (out : Z) (capacity : Z) (n : Z)
 Require 0 <= lvalue && lvalue <= 1 && f == cm_function_at(policy, fid, cm_program_functions(p)) && e == CMConstE(n, ty) && cm_type_code_wf(ty) && cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body, next) * cm_expr_rep(expr, e) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_leaf_code_for(p, CMLeafConst(n, ty), lvalue), tail))
 Ensure 0 <= lvalue && lvalue <= 1 && f == cm_function_at(policy, fid, cm_program_functions(p)) && e == CMConstE(n, ty) && cm_type_code_wf(ty) && cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body, next) * cm_expr_rep(expr, e) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cm_leaf_code_for(p, CMLeafConst(n, ty), lvalue)), tail)
*/
{
 /*@ Assert program == program@pre && fid == fid@pre && fn == fn@pre && pc == pc@pre && temp == temp@pre && expr == expr@pre && lvalue == lvalue@pre && emitter == emitter@pre && expr != 0 && 0 <= lvalue && lvalue <= 1 && f == cm_function_at(policy, fid, cm_program_functions(p)) && e == CMConstE(n, ty) && cm_type_code_wf(ty) &&
 cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body, next) * data_at(&(expr->kind), int, cm_rep_expr_kind(e)) *
 data_at(&(expr->op), int, cm_rep_expr_op(e)) *
 data_at(&(expr->ty), int, cm_type_encode(ty)) *
 data_at(&(expr->value), long long, n) *
 data_at(&(expr->a), struct cm_expr *, 0) *
 data_at(&(expr->b), struct cm_expr *, 0) *
 data_at(&(expr->args), struct cm_arg *, 0) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_leaf_code_for(p, CMLeafConst(n, ty), lvalue), tail))
 */

  if (!lvalue) {
    long long immediate =
        cmc_const_immediate(expr->value, expr->ty) /*@ where model_ty = ty */;
    /*@ 0 <= lvalue && lvalue <= 0 && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_leaf_code_for(p, CMLeafConst(n, ty), lvalue), tail)) which implies lvalue == 0 && tvm_opcode_code(TVMPushOp) == 0 && tvm_opcode_code(TVMPushOp) != 22 && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, cons(TVMInst(TVMPushOp, cm_const_immediate(ty, n)), tail)) */
    cm_emit_plan(emitter, CMC_OP_PUSH, immediate) /*@ where policy = policy, p = p, done = done, tail = tail, out = out, capacity = capacity, opcode = TVMPushOp */;
  } else {
  }
}

void cm_emit_string_expr(struct cm_program *program, int fid,
                         struct cm_function *fn, int pc, int temp,
                         struct cm_expr *expr, int lvalue,
                         struct cm_emitter *emitter)
/*@ With (policy : cm_lookup_policy) (p : cm_program) (f : cm_function_d) (e : cm_expr) (ty : cm_type) (body : Z) (next : Z) (functions_ptr : Z) (done : list tvm_inst) (tail : list tvm_inst) (out : Z) (capacity : Z) (sid : Z)
 Require 0 <= lvalue && lvalue <= 1 && f == cm_function_at(policy, fid, cm_program_functions(p)) && e == CMStringE(sid, ty) && 0 <= sid && sid <= 2147483647 && cm_typed_program(policy, p) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) && cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 && cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body, next) * cm_expr_rep(expr, e) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_leaf_code_for(p, CMLeafString(sid, ty), lvalue), tail))
 Ensure 0 <= lvalue && lvalue <= 1 && f == cm_function_at(policy, fid, cm_program_functions(p)) && e == CMStringE(sid, ty) && 0 <= sid && sid <= 2147483647 && cm_typed_program(policy, p) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) && cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 && cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body, next) * cm_expr_rep(expr, e) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cm_leaf_code_for(p, CMLeafString(sid, ty), lvalue)), tail)
*/
{
 /*@ Assert program == program@pre && fid == fid@pre && fn == fn@pre && pc == pc@pre && temp == temp@pre && expr == expr@pre && lvalue == lvalue@pre && emitter == emitter@pre && expr != 0 && 0 <= lvalue && lvalue <= 1 && f == cm_function_at(policy, fid, cm_program_functions(p)) && e == CMStringE(sid, ty) && 0 <= sid && sid <= 2147483647 && cm_typed_program(policy, p) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) && cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body, next) * data_at(&(expr->kind), int, cm_rep_expr_kind(e)) *
 data_at(&(expr->op), int, cm_rep_expr_op(e)) *
 data_at(&(expr->ty), int, cm_type_encode(ty)) *
 data_at(&(expr->value), long long, sid) *
 data_at(&(expr->a), struct cm_expr *, 0) *
 data_at(&(expr->b), struct cm_expr *, 0) *
 data_at(&(expr->args), struct cm_arg *, 0) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_leaf_code_for(p, CMLeafString(sid, ty), lvalue), tail))
 */

  int string_id = (int)expr->value;
  if (!lvalue) {
    /*@ cm_program_context_rep(program, p, functions_ptr) which implies exists (sp : Z) (gp : Z) (tp : Z), program != 0 && data_at(&(program->structs), struct cm_struct *, sp) *
 data_at(&(program->globals), struct cm_global *, gp) *
 data_at(&(program->strings), struct cm_string *, tp) *
 data_at(&(program->functions), struct cm_function *, functions_ptr) *
 data_at(&(program->main_id), int, cm_program_main(p)) *
 cm_struct_list_rep(sp, cm_program_structs(p)) *
 cm_global_list_rep(gp, cm_program_globals(p)) *
 cm_string_list_rep(tp, cm_program_strings(p)) */
    long long address = cmc_string_address(
        program->globals, program->strings, string_id) /*@ where global_items = cm_program_globals(p), string_items = cm_program_strings(p) */;
    /*@ cm_typed_program(policy, p) && 0 <= lvalue && lvalue <= 0 && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_leaf_code_for(p, CMLeafString(sid, ty), lvalue), tail)) which implies cm_typed_program(policy, p) && lvalue == 0 && tvm_opcode_code(TVMPushOp) == 0 && tvm_opcode_code(TVMPushOp) != 22 && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, cons(TVMInst(TVMPushOp, cm_rep_string_address(cm_program_globals(p), cm_program_strings(p), sid)), tail)) */
    cm_emit_plan(emitter, CMC_OP_PUSH, address) /*@ where policy = policy, p = p, done = done, tail = tail, out = out, capacity = capacity, opcode = TVMPushOp */;
  } else {
  }
}

void cm_emit_getc_expr(struct cm_program *program, int fid,
                       struct cm_function *fn, int pc, int temp,
                       struct cm_expr *expr, int lvalue,
                       struct cm_emitter *emitter)
/*@ With (policy : cm_lookup_policy) (p : cm_program) (f : cm_function_d) (e : cm_expr) (ty : cm_type) (body : Z) (next : Z) (functions_ptr : Z) (done : list tvm_inst) (tail : list tvm_inst) (out : Z) (capacity : Z) 
 Require 0 <= lvalue && lvalue <= 1 && f == cm_function_at(policy, fid, cm_program_functions(p)) && e == CMGetcE(ty) && cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body, next) * cm_expr_rep(expr, e) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_leaf_code_for(p, CMLeafGetc(ty), lvalue), tail))
 Ensure 0 <= lvalue && lvalue <= 1 && f == cm_function_at(policy, fid, cm_program_functions(p)) && e == CMGetcE(ty) && cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body, next) * cm_expr_rep(expr, e) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cm_leaf_code_for(p, CMLeafGetc(ty), lvalue)), tail)
*/
{
  if (!lvalue) {
    /*@ 0 <= lvalue && lvalue <= 0 && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_leaf_code_for(p, CMLeafGetc(ty), lvalue), tail)) which implies lvalue == 0 && tvm_opcode_code(TVMGetcOp) == 24 && tvm_opcode_code(TVMGetcOp) != 22 && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, cons(TVMInst(TVMGetcOp, 0), tail)) */
    cm_emit_plan(emitter, CMC_OP_GETC, 0) /*@ where policy = policy, p = p, done = done, tail = tail, out = out, capacity = capacity, opcode = TVMGetcOp */;
  } else {
  }
}

static long long cm_sizeof_value(struct cm_program *program,
                                 long long code)
/*@ With (policy : cm_lookup_policy) (p : cm_program) (asked : cm_type) (functions_ptr : Z)
 Require code == cm_type_encode(asked) && cm_typed_program(policy, p) && cm_type_code_wf(asked) && cm_type_refs(cm_program_structs(p), asked) && cm_rep_structs_safe(cm_program_structs(p)) && cm_program_context_rep(program, p, functions_ptr)
 Ensure code == cm_type_encode(asked) && cm_typed_program(policy, p) && cm_type_code_wf(asked) && cm_type_refs(cm_program_structs(p), asked) && cm_rep_structs_safe(cm_program_structs(p)) && __return == cm_type_size(cm_program_structs(p), asked) && cm_program_context_rep(program, p, functions_ptr)
*/
{
  long long result;
  if (code >= 1024) {
    result = 8;
  } else {
    /*@ cm_type_code_wf(asked) && code == cm_type_encode(asked) which implies cm_type_code_wf(asked) && code == cm_type_encode(asked) && 0 <= code */
    int narrowed = (int)code;
    /*@ cm_program_context_rep(program, p, functions_ptr) which implies exists (sp : Z) (gp : Z) (tp : Z), program != 0 && data_at(&(program->structs), struct cm_struct *, sp) *
 data_at(&(program->globals), struct cm_global *, gp) *
 data_at(&(program->strings), struct cm_string *, tp) *
 data_at(&(program->functions), struct cm_function *, functions_ptr) *
 data_at(&(program->main_id), int, cm_program_main(p)) *
 cm_struct_list_rep(sp, cm_program_structs(p)) *
 cm_global_list_rep(gp, cm_program_globals(p)) *
 cm_string_list_rep(tp, cm_program_strings(p)) */
    result = cmc_type_size_at(program->structs, narrowed) /*@ where structs = cm_program_structs(p) */;
  }
  return result;
}

long long cm_type_size_value(struct cm_program *program,
                             long long code)
/*@ With (policy : cm_lookup_policy) (p : cm_program) (asked : cm_type) (functions_ptr : Z)
 Require code == cm_type_encode(asked) && cm_typed_program(policy, p) && cm_type_code_wf(asked) && cm_type_refs(cm_program_structs(p), asked) && cm_rep_structs_safe(cm_program_structs(p)) && cm_program_context_rep(program, p, functions_ptr)
 Ensure code == cm_type_encode(asked) && cm_typed_program(policy, p) && cm_type_code_wf(asked) && cm_type_refs(cm_program_structs(p), asked) && cm_rep_structs_safe(cm_program_structs(p)) && __return == cm_type_size(cm_program_structs(p), asked) && cm_program_context_rep(program, p, functions_ptr)
*/
{
  return cm_sizeof_value(program, code) /*@ where policy = policy, p = p, asked = asked, functions_ptr = functions_ptr */;
}

void cm_emit_sizeof_expr(struct cm_program *program, int fid,
                         struct cm_function *fn, int pc, int temp,
                         struct cm_expr *expr, int lvalue,
                         struct cm_emitter *emitter)
/*@ With (policy : cm_lookup_policy) (p : cm_program) (f : cm_function_d) (e : cm_expr) (ty : cm_type) (body : Z) (next : Z) (functions_ptr : Z) (done : list tvm_inst) (tail : list tvm_inst) (out : Z) (capacity : Z) (asked : cm_type)
 Require 0 <= lvalue && lvalue <= 1 && f == cm_function_at(policy, fid, cm_program_functions(p)) && e == CMSizeofE(asked, ty) && cm_typed_program(policy, p) && cm_type_code_wf(asked) && cm_type_refs(cm_program_structs(p), asked) && cm_rep_structs_safe(cm_program_structs(p)) && cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body, next) * cm_expr_rep(expr, e) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_leaf_code_for(p, CMLeafSizeof(asked, ty), lvalue), tail))
 Ensure 0 <= lvalue && lvalue <= 1 && f == cm_function_at(policy, fid, cm_program_functions(p)) && e == CMSizeofE(asked, ty) && cm_typed_program(policy, p) && cm_type_code_wf(asked) && cm_type_refs(cm_program_structs(p), asked) && cm_rep_structs_safe(cm_program_structs(p)) && cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body, next) * cm_expr_rep(expr, e) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cm_leaf_code_for(p, CMLeafSizeof(asked, ty), lvalue)), tail)
*/
{
 /*@ Assert program == program@pre && fid == fid@pre && fn == fn@pre && pc == pc@pre && temp == temp@pre && expr == expr@pre && lvalue == lvalue@pre && emitter == emitter@pre && expr != 0 && 0 <= lvalue && lvalue <= 1 && f == cm_function_at(policy, fid, cm_program_functions(p)) && e == CMSizeofE(asked, ty) && cm_typed_program(policy, p) && cm_type_code_wf(asked) && cm_type_refs(cm_program_structs(p), asked) && cm_rep_structs_safe(cm_program_structs(p)) &&
 cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body, next) * data_at(&(expr->kind), int, cm_rep_expr_kind(e)) *
 data_at(&(expr->op), int, cm_rep_expr_op(e)) *
 data_at(&(expr->ty), int, cm_type_encode(ty)) *
 data_at(&(expr->value), long long, cm_type_encode(asked)) *
 data_at(&(expr->a), struct cm_expr *, 0) *
 data_at(&(expr->b), struct cm_expr *, 0) *
 data_at(&(expr->args), struct cm_arg *, 0) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_leaf_code_for(p, CMLeafSizeof(asked, ty), lvalue), tail))
 */

  if (!lvalue) {
    long long size = cm_sizeof_value(program, expr->value) /*@ where policy = policy, p = p, asked = asked, functions_ptr = functions_ptr */;
    /*@ 0 <= lvalue && lvalue <= 0 && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_leaf_code_for(p, CMLeafSizeof(asked, ty), lvalue), tail)) which implies lvalue == 0 && tvm_opcode_code(TVMPushOp) == 0 && tvm_opcode_code(TVMPushOp) != 22 && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, cons(TVMInst(TVMPushOp, cm_type_size(cm_program_structs(p), asked)), tail)) */
    cm_emit_plan(emitter, CMC_OP_PUSH, size) /*@ where policy = policy, p = p, done = done, tail = tail, out = out, capacity = capacity, opcode = TVMPushOp */;
  } else {
  }
}

int cm_member_array_value_context(struct cm_program *program,
                                  int base_ty, int mid)
/*@ With (policy : cm_lookup_policy) (p : cm_program) (base : cm_type) (functions_ptr : Z)
 Require base_ty == cm_type_encode(base) && cm_i32_code_count(base_ty) && cm_typed_program(policy, p) && cm_type_code_wf(base) && cm_member_valid(p, base, mid) && cm_rep_structs_safe(cm_program_structs(p)) && cm_program_context_rep(program, p, functions_ptr)
 Ensure base_ty == cm_type_encode(base) && cm_i32_code_count(base_ty) && cm_typed_program(policy, p) && cm_type_code_wf(base) && cm_member_valid(p, base, mid) && cm_rep_structs_safe(cm_program_structs(p)) && __return == cm_member_array_code(p, base, mid) && cm_program_context_rep(program, p, functions_ptr)
*/
{
 /*@ Assert exists (sp : Z) (gp : Z) (tp : Z), program == program@pre && base_ty == base_ty@pre && mid == mid@pre && program != 0 && base_ty == cm_type_encode(base) && cm_i32_code_count(base_ty) && cm_typed_program(policy, p) && cm_type_code_wf(base) && cm_member_valid(p, base, mid) && cm_rep_structs_safe(cm_program_structs(p)) && 1024 <= base_ty && base_ty <= 2147483647 && 0 <= (base_ty - 1024) % 1024 - 2 && 0 <= mid &&
 data_at(&(program->structs), struct cm_struct *, sp) *
 data_at(&(program->globals), struct cm_global *, gp) *
 data_at(&(program->strings), struct cm_string *, tp) *
 data_at(&(program->functions), struct cm_function *, functions_ptr) *
 data_at(&(program->main_id), int, cm_program_main(p)) *
 cm_struct_list_rep(sp, cm_program_structs(p)) *
 cm_global_list_rep(gp, cm_program_globals(p)) *
 cm_string_list_rep(tp, cm_program_strings(p))
 */

  int result = cmc_member_array(program, base_ty, mid) /*@ where p = p, base = base, structs = cm_program_structs(p) */;
  return result;
}

long long cm_member_offset_value_context(struct cm_program *program,
                                         int base_ty, int mid)
/*@ With (policy : cm_lookup_policy) (p : cm_program) (base : cm_type) (functions_ptr : Z)
 Require base_ty == cm_type_encode(base) && cm_i32_code_count(base_ty) && cm_typed_program(policy, p) && cm_type_code_wf(base) && cm_member_valid(p, base, mid) && cm_rep_structs_safe(cm_program_structs(p)) && cm_program_context_rep(program, p, functions_ptr)
 Ensure base_ty == cm_type_encode(base) && cm_i32_code_count(base_ty) && cm_typed_program(policy, p) && cm_type_code_wf(base) && cm_member_valid(p, base, mid) && cm_rep_structs_safe(cm_program_structs(p)) && __return == cm_member_offset(cm_program_structs(p), cm_struct_id(cm_pointee(base)), mid) && cm_program_context_rep(program, p, functions_ptr)
*/
{
 /*@ Assert exists (sp : Z) (gp : Z) (tp : Z), program == program@pre && base_ty == base_ty@pre && mid == mid@pre && program != 0 && base_ty == cm_type_encode(base) && cm_i32_code_count(base_ty) && cm_typed_program(policy, p) && cm_type_code_wf(base) && cm_member_valid(p, base, mid) && cm_rep_structs_safe(cm_program_structs(p)) && 1024 <= base_ty && base_ty <= 2147483647 && 0 <= (base_ty - 1024) % 1024 - 2 && 0 <= mid &&
 data_at(&(program->structs), struct cm_struct *, sp) *
 data_at(&(program->globals), struct cm_global *, gp) *
 data_at(&(program->strings), struct cm_string *, tp) *
 data_at(&(program->functions), struct cm_function *, functions_ptr) *
 data_at(&(program->main_id), int, cm_program_main(p)) *
 cm_struct_list_rep(sp, cm_program_structs(p)) *
 cm_global_list_rep(gp, cm_program_globals(p)) *
 cm_string_list_rep(tp, cm_program_strings(p))
 */

  int pointee = cmc_pointee(base_ty);
  int sid = (pointee % 1024) - 2;
  long long result = cmc_member_offset_at(program->structs, sid, mid) /*@ where structs = cm_program_structs(p) */;
  return result;
}
