#include "cmc_layout_migration_abi.h"
struct cm_emitter {
  struct cm_output *output;
  int pc;
};

/*@ Extern Coq
 (cm_type :: *) (cm_expr :: *) (cm_leaf_expr :: *) (cm_program :: *)
 (cm_function_d :: *) (cm_struct_d :: *) (cm_global_d :: *) (cm_string_d :: *)
 (cm_lookup_policy :: *) (cm_codegen_obligations :: *) (tvm_inst :: *) (tvm_opcode :: *)
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
 (cm_type_encode : cm_type -> Z)
 (cm_type_code_wf : cm_type -> Prop)
 (cm_type_refs : list cm_struct_d -> cm_type -> Prop)
 (cm_typed_program : cm_lookup_policy -> cm_program -> Prop)
 (cm_program_structs : cm_program -> list cm_struct_d)
 (cm_program_globals : cm_program -> list cm_global_d)
 (cm_program_strings : cm_program -> list cm_string_d)
 (cm_program_functions : cm_program -> list cm_function_d)
 (cm_function_at : cm_lookup_policy -> Z -> list cm_function_d -> cm_function_d)
 (cm_rep_structs_safe : list cm_struct_d -> Prop)
 (cm_rep_globals_safe : list cm_global_d -> Prop)
 (cm_rep_strings_safe : list cm_string_d -> Prop)
 (cm_rep_globals_size : list cm_global_d -> Z)
 (cm_rep_strings_size : list cm_string_d -> Z)
 (cm_program_context_rep : Z -> cm_program -> Z -> Assertion)
 (cm_function_context_rep : Z -> cm_function_d -> Z -> Z -> Assertion)
 (cm_expr_rep : Z -> cm_expr -> Assertion)
 (cm_rep_expr_kind : cm_expr -> Z)
 (cm_rep_expr_op : cm_expr -> Z)
 (cm_rep_expr_value : cm_expr -> Z)
 (cm_expr_type : cm_expr -> cm_type)
 (cm_expr_payload : cm_expr -> Z -> Z -> Z -> Assertion)
 (cm_resolved_emitter_plan_rep : cm_lookup_policy -> cm_program -> Z -> Z -> Z -> list tvm_inst -> list tvm_inst -> Assertion)
*/
/*@ Import Coq Require Import SimpleC.EE.QCP_demos_human.cmc_emit_expr_dispatch_migration_lib */

/*@ Extern Coq
 (cm_dispatch_leaf : cm_expr -> Prop)
 (cm_leaf_source_expr : cm_leaf_expr -> cm_expr)
 (cm_wf_program : cm_lookup_policy -> cm_codegen_obligations -> cm_program -> Prop)
 (cm_expr_wf : cm_lookup_policy -> cm_program -> cm_function_d -> cm_expr -> Prop)
 (cm_expr_counts_representable : cm_lookup_policy -> cm_program -> Z -> cm_expr -> Prop)
*/
void cm_emit_const_expr(struct cm_program *program, int fid,
                        struct cm_function *fn, int pc, int temp,
                        struct cm_expr *expr, int lvalue,
                        struct cm_emitter *emitter)
/*@ With (policy : cm_lookup_policy) (p : cm_program) (f : cm_function_d) (e : cm_expr) (ty : cm_type) (body : Z) (next : Z) (functions_ptr : Z) (done : list tvm_inst) (tail : list tvm_inst) (out : Z) (capacity : Z) (n : Z)
 Require 0 <= lvalue && lvalue <= 1 && f == cm_function_at(policy, fid, cm_program_functions(p)) && e == CMConstE(n, ty) && cm_type_code_wf(ty) && cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body, next) * cm_expr_rep(expr, e) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_leaf_code_for(p, CMLeafConst(n, ty), lvalue), tail))
 Ensure 0 <= lvalue && lvalue <= 1 && f == cm_function_at(policy, fid, cm_program_functions(p)) && e == CMConstE(n, ty) && cm_type_code_wf(ty) && cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body, next) * cm_expr_rep(expr, e) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cm_leaf_code_for(p, CMLeafConst(n, ty), lvalue)), tail)
*/;

void cm_emit_string_expr(struct cm_program *program, int fid,
                         struct cm_function *fn, int pc, int temp,
                         struct cm_expr *expr, int lvalue,
                         struct cm_emitter *emitter)
/*@ With (policy : cm_lookup_policy) (p : cm_program) (f : cm_function_d) (e : cm_expr) (ty : cm_type) (body : Z) (next : Z) (functions_ptr : Z) (done : list tvm_inst) (tail : list tvm_inst) (out : Z) (capacity : Z) (sid : Z)
 Require 0 <= lvalue && lvalue <= 1 && f == cm_function_at(policy, fid, cm_program_functions(p)) && e == CMStringE(sid, ty) && 0 <= sid && sid <= 2147483647 && cm_typed_program(policy, p) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) && cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 && cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body, next) * cm_expr_rep(expr, e) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_leaf_code_for(p, CMLeafString(sid, ty), lvalue), tail))
 Ensure 0 <= lvalue && lvalue <= 1 && f == cm_function_at(policy, fid, cm_program_functions(p)) && e == CMStringE(sid, ty) && 0 <= sid && sid <= 2147483647 && cm_typed_program(policy, p) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) && cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 && cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body, next) * cm_expr_rep(expr, e) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cm_leaf_code_for(p, CMLeafString(sid, ty), lvalue)), tail)
*/;

void cm_emit_sizeof_expr(struct cm_program *program, int fid,
                         struct cm_function *fn, int pc, int temp,
                         struct cm_expr *expr, int lvalue,
                         struct cm_emitter *emitter)
/*@ With (policy : cm_lookup_policy) (p : cm_program) (f : cm_function_d) (e : cm_expr) (ty : cm_type) (body : Z) (next : Z) (functions_ptr : Z) (done : list tvm_inst) (tail : list tvm_inst) (out : Z) (capacity : Z) (asked : cm_type)
 Require 0 <= lvalue && lvalue <= 1 && f == cm_function_at(policy, fid, cm_program_functions(p)) && e == CMSizeofE(asked, ty) && cm_typed_program(policy, p) && cm_type_code_wf(asked) && cm_type_refs(cm_program_structs(p), asked) && cm_rep_structs_safe(cm_program_structs(p)) && cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body, next) * cm_expr_rep(expr, e) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_leaf_code_for(p, CMLeafSizeof(asked, ty), lvalue), tail))
 Ensure 0 <= lvalue && lvalue <= 1 && f == cm_function_at(policy, fid, cm_program_functions(p)) && e == CMSizeofE(asked, ty) && cm_typed_program(policy, p) && cm_type_code_wf(asked) && cm_type_refs(cm_program_structs(p), asked) && cm_rep_structs_safe(cm_program_structs(p)) && cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body, next) * cm_expr_rep(expr, e) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cm_leaf_code_for(p, CMLeafSizeof(asked, ty), lvalue)), tail)
*/;

void cm_emit_getc_expr(struct cm_program *program, int fid,
                       struct cm_function *fn, int pc, int temp,
                       struct cm_expr *expr, int lvalue,
                       struct cm_emitter *emitter)
/*@ With (policy : cm_lookup_policy) (p : cm_program) (f : cm_function_d) (e : cm_expr) (ty : cm_type) (body : Z) (next : Z) (functions_ptr : Z) (done : list tvm_inst) (tail : list tvm_inst) (out : Z) (capacity : Z) 
 Require 0 <= lvalue && lvalue <= 1 && f == cm_function_at(policy, fid, cm_program_functions(p)) && e == CMGetcE(ty) && cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body, next) * cm_expr_rep(expr, e) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_leaf_code_for(p, CMLeafGetc(ty), lvalue), tail))
 Ensure 0 <= lvalue && lvalue <= 1 && f == cm_function_at(policy, fid, cm_program_functions(p)) && e == CMGetcE(ty) && cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body, next) * cm_expr_rep(expr, e) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cm_leaf_code_for(p, CMLeafGetc(ty), lvalue)), tail)
*/;

void cm_emit_leaf_expr(struct cm_program *program, int fid,
                       struct cm_function *fn, int pc, int temp,
                       struct cm_expr *expr, int lvalue,
                       struct cm_emitter *emitter)
/*@ With (policy : cm_lookup_policy) (cg : cm_codegen_obligations) (p : cm_program) (f : cm_function_d) (e : cm_expr) (leaf : cm_leaf_expr)
 (body : Z) (next : Z) (functions_ptr : Z) (done : list tvm_inst) (tail : list tvm_inst) (out : Z) (capacity : Z)
 Require 0 <= lvalue && lvalue <= 1 && e == cm_leaf_source_expr(leaf) && cm_dispatch_leaf(e) &&
 cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) && f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 && cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body, next) * cm_expr_rep(expr, e) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_leaf_code_for(p, leaf, lvalue), tail))
 Ensure 0 <= lvalue && lvalue <= 1 && e == cm_leaf_source_expr(leaf) && cm_dispatch_leaf(e) &&
 cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) && f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 && cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body, next) * cm_expr_rep(expr, e) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cm_leaf_code_for(p, leaf, lvalue)), tail)
*/
{
 /*@ cm_expr_rep(expr, e) which implies exists (xa : Z) (xb : Z) (xargs : Z), expr != 0 && data_at(&(expr->kind), int, cm_rep_expr_kind(e)) *
 data_at(&(expr->op), int, cm_rep_expr_op(e)) *
 data_at(&(expr->ty), int, cm_type_encode(cm_expr_type(e))) *
 data_at(&(expr->value), long long, cm_rep_expr_value(e)) *
 data_at(&(expr->a), struct cm_expr *, xa) *
 data_at(&(expr->b), struct cm_expr *, xb) *
 data_at(&(expr->args), struct cm_arg *, xargs) * cm_expr_payload(e, xa, xb, xargs) */
  if (expr->kind == CMC_EXPR_CONST) {
 /*@ e == cm_leaf_source_expr(leaf) && cm_dispatch_leaf(e) && cm_rep_expr_kind(e) == 0 && cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_leaf_code_for(p, leaf, lvalue), tail))
 which implies exists (n : Z) (ty : cm_type), e == CMConstE(n, ty) && e == cm_leaf_source_expr(leaf) && cm_dispatch_leaf(e) && leaf == CMLeafConst(n, ty) && cm_type_code_wf(ty) && cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_leaf_code_for(p, CMLeafConst(n, ty), lvalue), tail)) */
 /*@ exists (xa : Z) (xb : Z) (xargs : Z), expr != 0 && data_at(&(expr->kind), int, cm_rep_expr_kind(e)) *
 data_at(&(expr->op), int, cm_rep_expr_op(e)) *
 data_at(&(expr->ty), int, cm_type_encode(cm_expr_type(e))) *
 data_at(&(expr->value), long long, cm_rep_expr_value(e)) *
 data_at(&(expr->a), struct cm_expr *, xa) *
 data_at(&(expr->b), struct cm_expr *, xb) *
 data_at(&(expr->args), struct cm_arg *, xargs) * cm_expr_payload(e, xa, xb, xargs)
 which implies cm_expr_rep(expr, e) */
    cm_emit_const_expr(program, fid, fn, pc, temp, expr, lvalue, emitter) /*@ where policy = policy, p = p, f = f, e = e, body = body, next = next, functions_ptr = functions_ptr, done = done, tail = tail, out = out, capacity = capacity */;
  } else if (expr->kind == CMC_EXPR_STRING) {
 /*@ e == cm_leaf_source_expr(leaf) && cm_dispatch_leaf(e) && cm_rep_expr_kind(e) == 1 && cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_leaf_code_for(p, leaf, lvalue), tail))
 which implies exists (sid : Z) (ty : cm_type), e == CMStringE(sid, ty) && e == cm_leaf_source_expr(leaf) && cm_dispatch_leaf(e) && leaf == CMLeafString(sid, ty) && 0 <= sid && sid <= 2147483647 && cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_leaf_code_for(p, CMLeafString(sid, ty), lvalue), tail)) */
 /*@ exists (xa : Z) (xb : Z) (xargs : Z), expr != 0 && data_at(&(expr->kind), int, cm_rep_expr_kind(e)) *
 data_at(&(expr->op), int, cm_rep_expr_op(e)) *
 data_at(&(expr->ty), int, cm_type_encode(cm_expr_type(e))) *
 data_at(&(expr->value), long long, cm_rep_expr_value(e)) *
 data_at(&(expr->a), struct cm_expr *, xa) *
 data_at(&(expr->b), struct cm_expr *, xb) *
 data_at(&(expr->args), struct cm_arg *, xargs) * cm_expr_payload(e, xa, xb, xargs)
 which implies cm_expr_rep(expr, e) */
    cm_emit_string_expr(program, fid, fn, pc, temp, expr, lvalue, emitter) /*@ where policy = policy, p = p, f = f, e = e, body = body, next = next, functions_ptr = functions_ptr, done = done, tail = tail, out = out, capacity = capacity */;
  } else if (expr->kind == CMC_EXPR_SIZEOF) {
 /*@ e == cm_leaf_source_expr(leaf) && cm_dispatch_leaf(e) && cm_rep_expr_kind(e) == 9 && cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_leaf_code_for(p, leaf, lvalue), tail))
 which implies exists (asked : cm_type) (ty : cm_type), e == CMSizeofE(asked, ty) && e == cm_leaf_source_expr(leaf) && cm_dispatch_leaf(e) && leaf == CMLeafSizeof(asked, ty) && cm_type_code_wf(asked) && cm_type_refs(cm_program_structs(p), asked) && cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_leaf_code_for(p, CMLeafSizeof(asked, ty), lvalue), tail)) */
 /*@ exists (xa : Z) (xb : Z) (xargs : Z), expr != 0 && data_at(&(expr->kind), int, cm_rep_expr_kind(e)) *
 data_at(&(expr->op), int, cm_rep_expr_op(e)) *
 data_at(&(expr->ty), int, cm_type_encode(cm_expr_type(e))) *
 data_at(&(expr->value), long long, cm_rep_expr_value(e)) *
 data_at(&(expr->a), struct cm_expr *, xa) *
 data_at(&(expr->b), struct cm_expr *, xb) *
 data_at(&(expr->args), struct cm_arg *, xargs) * cm_expr_payload(e, xa, xb, xargs)
 which implies cm_expr_rep(expr, e) */
    cm_emit_sizeof_expr(program, fid, fn, pc, temp, expr, lvalue, emitter) /*@ where policy = policy, p = p, f = f, e = e, body = body, next = next, functions_ptr = functions_ptr, done = done, tail = tail, out = out, capacity = capacity */;
  } else {
 /*@ e == cm_leaf_source_expr(leaf) && cm_dispatch_leaf(e) && cm_rep_expr_kind(e) != 0 && cm_rep_expr_kind(e) != 1 && cm_rep_expr_kind(e) != 9 && cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_leaf_code_for(p, leaf, lvalue), tail))
 which implies exists (ty : cm_type), e == CMGetcE(ty) && e == cm_leaf_source_expr(leaf) && cm_dispatch_leaf(e) && leaf == CMLeafGetc(ty) && cm_dispatch_leaf(e) && cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_leaf_code_for(p, CMLeafGetc(ty), lvalue), tail)) */
 /*@ exists (xa : Z) (xb : Z) (xargs : Z), expr != 0 && data_at(&(expr->kind), int, cm_rep_expr_kind(e)) *
 data_at(&(expr->op), int, cm_rep_expr_op(e)) *
 data_at(&(expr->ty), int, cm_type_encode(cm_expr_type(e))) *
 data_at(&(expr->value), long long, cm_rep_expr_value(e)) *
 data_at(&(expr->a), struct cm_expr *, xa) *
 data_at(&(expr->b), struct cm_expr *, xb) *
 data_at(&(expr->args), struct cm_arg *, xargs) * cm_expr_payload(e, xa, xb, xargs)
 which implies cm_expr_rep(expr, e) */
    cm_emit_getc_expr(program, fid, fn, pc, temp, expr, lvalue, emitter) /*@ where policy = policy, p = p, f = f, e = e, body = body, next = next, functions_ptr = functions_ptr, done = done, tail = tail, out = out, capacity = capacity */;
  }
}
