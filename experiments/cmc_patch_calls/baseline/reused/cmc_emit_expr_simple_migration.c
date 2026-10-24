#include "cmc_layout_migration_abi.h"
struct cm_emitter {
  struct cm_output *output;
  int pc;
};

/*@ Extern Coq
 (cm_type :: *)
 (cm_expr :: *)
 (cm_leaf_expr :: *)
 (cm_program :: *)
 (cm_function_d :: *)
 (cm_struct_d :: *)
 (cm_global_d :: *)
 (cm_string_d :: *)
 (cm_lookup_policy :: *)
 (cm_codegen_obligations :: *)
 (tvm_inst :: *)
 (tvm_opcode :: *)
 (cm_slot_d :: *)
 (cm_simple_view :: *)
*/
/*@ Extern Coq
 (cm_leaf_code_for : cm_program -> cm_leaf_expr -> Z -> list tvm_inst)
 (cm_type_encode : cm_type -> Z)
 (cm_type_code_wf : cm_type -> Prop)
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
 (cm_dispatch_leaf : cm_expr -> Prop)
 (cm_leaf_source_expr : cm_leaf_expr -> cm_expr)
 (cm_wf_program : cm_lookup_policy -> cm_codegen_obligations -> cm_program -> Prop)
 (cm_expr_wf : cm_lookup_policy -> cm_program -> cm_function_d -> cm_expr -> Prop)
 (cm_expr_counts_representable : cm_lookup_policy -> cm_program -> Z -> cm_expr -> Prop)
 (cm_function_params : cm_function_d -> list cm_slot_d)
 (cm_function_locals : cm_function_d -> list cm_slot_d)
 (cm_binding_valid : cm_program -> cm_function_d -> Z -> Z -> Prop)
 (cm_slots_wf : list cm_struct_d -> list cm_slot_d -> Prop)
 (cm_rep_members_safe : list cm_slot_d -> Prop)
 (CMVarE : Z -> Z -> cm_type -> cm_expr)
 (cm_var_code_for : cm_lookup_policy -> cm_program -> Z -> Z -> Z -> cm_type -> Z -> list tvm_inst)
 (CMSimpleLeaf : cm_leaf_expr -> cm_simple_view)
 (CMSimpleVar : Z -> Z -> cm_type -> cm_simple_view)
 (cm_simple_expr : cm_expr -> Prop)
 (cm_simple_source_expr : cm_simple_view -> cm_expr)
 (cm_simple_code_for : cm_lookup_policy -> cm_program -> Z -> cm_simple_view -> Z -> list tvm_inst)
*/
/*@ Import Coq Require Import SimpleC.EE.QCP_demos_human.cmc_emit_expr_simple_migration_lib */

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
*/;

void cm_emit_var_expr(struct cm_program *program, int fid,
                      struct cm_function *fn, int pc, int temp,
                      struct cm_expr *expr, int lvalue,
                      struct cm_emitter *emitter)
/*@ With (policy : cm_lookup_policy) (cg : cm_codegen_obligations) (p : cm_program) (f : cm_function_d) (e : cm_expr)
 (scope : Z) (slot : Z) (ty : cm_type) (body : Z) (next : Z) (functions_ptr : Z)
 (done : list tvm_inst) (tail : list tvm_inst) (out : Z) (capacity : Z)
 Require 0 <= lvalue && lvalue <= 1 && e == CMVarE(scope, slot, ty) &&
 cm_wf_program(policy, cg, p) && f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 0 <= slot && slot <= 2147483647 && cm_binding_valid(p, f, scope, slot) && cm_type_code_wf(ty) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) && cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body, next) * cm_expr_rep(expr, e) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_var_code_for(policy, p, fid, scope, slot, ty, lvalue), tail))
 Ensure 0 <= lvalue && lvalue <= 1 && e == CMVarE(scope, slot, ty) &&
 cm_wf_program(policy, cg, p) && f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 0 <= slot && slot <= 2147483647 && cm_binding_valid(p, f, scope, slot) && cm_type_code_wf(ty) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) && cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body, next) * cm_expr_rep(expr, e) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cm_var_code_for(policy, p, fid, scope, slot, ty, lvalue)), tail)
*/;

void cm_emit_simple_expr(struct cm_program *program, int fid,
                         struct cm_function *fn, int pc, int temp,
                         struct cm_expr *expr, int lvalue,
                         struct cm_emitter *emitter)
/*@ With (policy : cm_lookup_policy) (cg : cm_codegen_obligations) (p : cm_program) (f : cm_function_d) (e : cm_expr) (simple : cm_simple_view)
 (body : Z) (next : Z) (functions_ptr : Z) (done : list tvm_inst) (tail : list tvm_inst) (out : Z) (capacity : Z)
 Require 0 <= lvalue && lvalue <= 1 && e == cm_simple_source_expr(simple) && cm_simple_expr(e) &&
 cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) && f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 && cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body, next) * cm_expr_rep(expr, e) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_simple_code_for(policy, p, fid, simple, lvalue), tail))
 Ensure 0 <= lvalue && lvalue <= 1 && e == cm_simple_source_expr(simple) && cm_simple_expr(e) &&
 cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) && f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 && cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body, next) * cm_expr_rep(expr, e) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cm_simple_code_for(policy, p, fid, simple, lvalue)), tail)
*/
{
 /*@ cm_expr_rep(expr, e) which implies exists (xa : Z) (xb : Z) (xargs : Z), expr != 0 && data_at(&(expr->kind), int, cm_rep_expr_kind(e)) *
 data_at(&(expr->op), int, cm_rep_expr_op(e)) *
 data_at(&(expr->ty), int, cm_type_encode(cm_expr_type(e))) *
 data_at(&(expr->value), long long, cm_rep_expr_value(e)) *
 data_at(&(expr->a), struct cm_expr *, xa) *
 data_at(&(expr->b), struct cm_expr *, xb) *
 data_at(&(expr->args), struct cm_arg *, xargs) * cm_expr_payload(e, xa, xb, xargs) */
  if (expr->kind == CMC_EXPR_VAR) {
 /*@ e == cm_simple_source_expr(simple) && cm_simple_expr(e) && cm_rep_expr_kind(e) == 2 && cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_simple_code_for(policy, p, fid, simple, lvalue), tail))
 which implies exists (scope : Z) (slot : Z) (ty : cm_type), e == cm_simple_source_expr(simple) && cm_simple_expr(e) && e == CMVarE(scope, slot, ty) && simple == CMSimpleVar(scope, slot, ty) && 0 <= slot && slot <= 2147483647 && cm_binding_valid(p, f, scope, slot) && cm_type_code_wf(ty) && cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_var_code_for(policy, p, fid, scope, slot, ty, lvalue), tail)) */
 /*@ exists (xa : Z) (xb : Z) (xargs : Z), expr != 0 && data_at(&(expr->kind), int, cm_rep_expr_kind(e)) *
 data_at(&(expr->op), int, cm_rep_expr_op(e)) *
 data_at(&(expr->ty), int, cm_type_encode(cm_expr_type(e))) *
 data_at(&(expr->value), long long, cm_rep_expr_value(e)) *
 data_at(&(expr->a), struct cm_expr *, xa) *
 data_at(&(expr->b), struct cm_expr *, xb) *
 data_at(&(expr->args), struct cm_arg *, xargs) * cm_expr_payload(e, xa, xb, xargs)
 which implies cm_expr_rep(expr, e) */
    cm_emit_var_expr(program, fid, fn, pc, temp, expr, lvalue, emitter) /*@ where policy = policy, cg = cg, p = p, f = f, e = e, body = body, next = next, functions_ptr = functions_ptr, done = done, tail = tail, out = out, capacity = capacity */;
  } else {
 /*@ e == cm_simple_source_expr(simple) && cm_simple_expr(e) && cm_rep_expr_kind(e) != 2 && cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_simple_code_for(policy, p, fid, simple, lvalue), tail))
 which implies exists (leaf : cm_leaf_expr), e == cm_simple_source_expr(simple) && cm_simple_expr(e) && e == cm_leaf_source_expr(leaf) && simple == CMSimpleLeaf(leaf) && cm_dispatch_leaf(e) && cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_leaf_code_for(p, leaf, lvalue), tail)) */
 /*@ exists (xa : Z) (xb : Z) (xargs : Z), expr != 0 && data_at(&(expr->kind), int, cm_rep_expr_kind(e)) *
 data_at(&(expr->op), int, cm_rep_expr_op(e)) *
 data_at(&(expr->ty), int, cm_type_encode(cm_expr_type(e))) *
 data_at(&(expr->value), long long, cm_rep_expr_value(e)) *
 data_at(&(expr->a), struct cm_expr *, xa) *
 data_at(&(expr->b), struct cm_expr *, xb) *
 data_at(&(expr->args), struct cm_arg *, xargs) * cm_expr_payload(e, xa, xb, xargs)
 which implies cm_expr_rep(expr, e) */
    cm_emit_leaf_expr(program, fid, fn, pc, temp, expr, lvalue, emitter) /*@ where policy = policy, cg = cg, p = p, f = f, e = e, body = body, next = next, functions_ptr = functions_ptr, done = done, tail = tail, out = out, capacity = capacity */;
  }
}
