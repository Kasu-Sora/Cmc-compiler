#include "cmc_layout_migration_abi.h"

struct cm_emitter {
  struct cm_output *output;
  int pc;
};

/*@ Extern Coq
    (cm_expr :: *) (cm_type :: *) (cm_slot_d :: *) (cm_struct_d :: *)
    (cm_global_d :: *) (cm_string_d :: *) (cm_function_d :: *)
    (cm_program :: *) (cm_lookup_policy :: *) (cm_codegen_obligations :: *)
    (tvm_opcode :: *) (tvm_inst :: *)
*/
/*@ Extern Coq
    (cm_wf_program : cm_lookup_policy -> cm_codegen_obligations -> cm_program -> Prop)
    (cm_function_at : cm_lookup_policy -> Z -> list cm_function_d -> cm_function_d)
    (cm_program_structs : cm_program -> list cm_struct_d)
    (cm_program_globals : cm_program -> list cm_global_d)
    (cm_program_strings : cm_program -> list cm_string_d)
    (cm_program_functions : cm_program -> list cm_function_d)
    (cm_program_main : cm_program -> Z)
    (cm_function_params : cm_function_d -> list cm_slot_d)
    (cm_function_locals : cm_function_d -> list cm_slot_d)
    (cm_function_ret : cm_function_d -> cm_type)
    (cm_type_encode : cm_type -> Z)
    (cm_binding_valid : cm_program -> cm_function_d -> Z -> Z -> Prop)
    (cm_slots_wf : list cm_struct_d -> list cm_slot_d -> Prop)
    (cm_rep_globals_safe : list cm_global_d -> Prop)
    (cm_rep_members_safe : list cm_slot_d -> Prop)
    (cm_rep_members_size : list cm_slot_d -> Z)
    (cm_rep_member_prefix : list cm_slot_d -> Z -> Z)
    (cm_rep_global_address : list cm_global_d -> Z -> Z)
    (cm_program_context_rep : Z -> cm_program -> Z -> Assertion)
    (cm_function_context_rep : Z -> cm_function_d -> Z -> Z -> Assertion)
    (cm_struct_list_rep : Z -> list cm_struct_d -> Assertion)
    (cm_global_list_rep : Z -> list cm_global_d -> Assertion)
    (cm_string_list_rep : Z -> list cm_string_d -> Assertion)
    (cm_slot_list_rep : Z -> list cm_slot_d -> Assertion)
    (TVMInst : tvm_opcode -> Z -> tvm_inst)
    (TVMPushOp : tvm_opcode)
    (tvm_opcode_code : tvm_opcode -> Z)
    (cm_fp_relative_address_code : Z -> list tvm_inst)
    (cm_binding_address_code : cm_lookup_policy -> cm_program -> Z -> Z -> Z -> list tvm_inst)
    (cm_resolved_emitter_rep : cm_lookup_policy -> cm_program -> Z -> Z -> Z -> list tvm_inst -> Assertion)
    (cm_resolved_emitter_plan_rep : cm_lookup_policy -> cm_program -> Z -> Z -> Z -> list tvm_inst -> list tvm_inst -> Assertion)
*/
/*@ Extern Coq
 (CMVarE : Z -> Z -> cm_type -> cm_expr)
 (cm_type_code_wf : cm_type -> Prop)
 (cm_expr_rep : Z -> cm_expr -> Assertion)
 (cm_binding_array_code : cm_lookup_policy -> cm_program -> Z -> Z -> Z -> Z)
 (cm_load_code : cm_type -> list tvm_inst)
 (cm_var_code_for : cm_lookup_policy -> cm_program -> Z -> Z -> Z -> cm_type -> Z -> list tvm_inst)
*/
/*@ Import Coq Require Import SimpleC.EE.QCP_demos_human.cmc_emit_expr_var_migration_lib */

int cmc_binding_array(struct cm_program *program, int fid,
                             struct cm_function *fn,
                             int scope, int slot)
/*@ With (policy : cm_lookup_policy) (p : cm_program) (f : cm_function_d) (globals : list cm_global_d) (locals : list cm_slot_d) (zg : Z) (zl : Z)
    Require 0 <= slot && globals == cm_program_globals(p) && locals == cm_function_locals(f) && f == cm_function_at(policy, fid, cm_program_functions(p)) && cm_binding_valid(p, f, scope, slot) && data_at(&(program->globals), struct cm_global *, zg) * cm_global_list_rep(zg, globals) * data_at(&(fn->locals), struct cm_slot *, zl) * cm_slot_list_rep(zl, locals)
    Ensure 0 <= slot && globals == cm_program_globals(p) && locals == cm_function_locals(f) && f == cm_function_at(policy, fid, cm_program_functions(p)) && cm_binding_valid(p, f, scope, slot) && __return == cm_binding_array_code(policy, p, fid, scope, slot) && data_at(&(program->globals), struct cm_global *, zg) * cm_global_list_rep(zg, globals) * data_at(&(fn->locals), struct cm_slot *, zl) * cm_slot_list_rep(zl, locals)
*/;

void cm_emit_binding_address_plan(struct cm_program *program,
                             struct cm_function *fn,
                             int scope, int slot,
                             struct cm_emitter *emitter)
/*@ With (policy : cm_lookup_policy) (cg : cm_codegen_obligations)
    (p : cm_program) (f : cm_function_d) (fid : Z)
    (structs : list cm_struct_d) (globals : list cm_global_d)
    (functions_ptr : Z) (body : Z) (next : Z)
    (done : list tvm_inst) (out : Z) (capacity : Z) (tail : list tvm_inst)
    Require cm_wf_program(policy, cg, p) &&
      f == cm_function_at(policy, fid, cm_program_functions(p)) &&
      structs == cm_program_structs(p) && globals == cm_program_globals(p) &&
      cm_binding_valid(p, f, scope, slot) &&
      cm_slots_wf(structs, cm_function_params(f)) &&
      cm_slots_wf(structs, cm_function_locals(f)) &&
      cm_rep_globals_safe(globals) &&
      cm_rep_members_safe(cm_function_params(f)) &&
      cm_rep_members_safe(cm_function_locals(f)) && cm_program_context_rep(program, p, functions_ptr) *
      cm_function_context_rep(fn, f, body, next) *
      cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_binding_address_code(policy, p, fid, scope, slot), tail))
    Ensure cm_wf_program(policy, cg, p) &&
      f == cm_function_at(policy, fid, cm_program_functions(p)) &&
      structs == cm_program_structs(p) && globals == cm_program_globals(p) &&
      cm_binding_valid(p, f, scope, slot) &&
      cm_slots_wf(structs, cm_function_params(f)) &&
      cm_slots_wf(structs, cm_function_locals(f)) &&
      cm_rep_globals_safe(globals) &&
      cm_rep_members_safe(cm_function_params(f)) &&
      cm_rep_members_safe(cm_function_locals(f)) && cm_program_context_rep(program, p, functions_ptr) *
      cm_function_context_rep(fn, f, body, next) *
      cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cm_binding_address_code(policy, p, fid, scope, slot)), tail)
*/;

void cm_emit_load_plan(struct cm_emitter *emitter, int ty)
/*@ With (policy : cm_lookup_policy) (p : cm_program) (done : list tvm_inst) (tail : list tvm_inst) (out : Z) (capacity : Z) (model_ty : cm_type)
    Require ty == cm_type_encode(model_ty) && cm_type_code_wf(model_ty) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_load_code(model_ty), tail))
    Ensure cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cm_load_code(model_ty)), tail)
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
*/
{
  /*@ e == CMVarE(scope, slot, ty) && cm_expr_rep(expr, e)
    which implies e == CMVarE(scope, slot, ty) && expr != 0 && data_at(&(expr->kind), int, 2) * data_at(&(expr->op), int, scope) *
 data_at(&(expr->ty), int, cm_type_encode(ty)) * data_at(&(expr->value), long long, slot) *
 data_at(&(expr->a), struct cm_expr *, 0) * data_at(&(expr->b), struct cm_expr *, 0) * data_at(&(expr->args), struct cm_arg *, 0) */
  /*@ cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body, next)
    which implies exists (sp : Z) (gp : Z) (tp : Z) (pp : Z) (lp : Z),
    program != 0 && fn != 0 && data_at(&(program->structs), struct cm_struct *, sp) * data_at(&(program->globals), struct cm_global *, gp) *
 data_at(&(program->strings), struct cm_string *, tp) * data_at(&(program->functions), struct cm_function *, functions_ptr) *
 data_at(&(program->main_id), int, cm_program_main(p)) * cm_struct_list_rep(sp, cm_program_structs(p)) *
 cm_global_list_rep(gp, cm_program_globals(p)) * cm_string_list_rep(tp, cm_program_strings(p)) * data_at(&(fn->ret_ty), int, cm_type_encode(cm_function_ret(f))) * data_at(&(fn->params), struct cm_slot *, pp) *
 data_at(&(fn->locals), struct cm_slot *, lp) * data_at(&(fn->body), struct cm_stmt *, body) * data_at(&(fn->next), struct cm_function *, next) *
 cm_slot_list_rep(pp, cm_function_params(f)) * cm_slot_list_rep(lp, cm_function_locals(f)) */
  int array = cmc_binding_array(program, fid, fn,
                                expr->op, (int)expr->value) /*@ where policy = policy, p = p, f = f, globals = cm_program_globals(p), locals = cm_function_locals(f) */;
  /*@ exists (sp : Z) (gp : Z) (tp : Z) (pp : Z) (lp : Z), program != 0 && fn != 0 && data_at(&(program->structs), struct cm_struct *, sp) * data_at(&(program->globals), struct cm_global *, gp) *
 data_at(&(program->strings), struct cm_string *, tp) * data_at(&(program->functions), struct cm_function *, functions_ptr) *
 data_at(&(program->main_id), int, cm_program_main(p)) * cm_struct_list_rep(sp, cm_program_structs(p)) *
 cm_global_list_rep(gp, cm_program_globals(p)) * cm_string_list_rep(tp, cm_program_strings(p)) * data_at(&(fn->ret_ty), int, cm_type_encode(cm_function_ret(f))) * data_at(&(fn->params), struct cm_slot *, pp) *
 data_at(&(fn->locals), struct cm_slot *, lp) * data_at(&(fn->body), struct cm_stmt *, body) * data_at(&(fn->next), struct cm_function *, next) *
 cm_slot_list_rep(pp, cm_function_params(f)) * cm_slot_list_rep(lp, cm_function_locals(f))
    which implies cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body, next) */
  if (!lvalue) {
    if (array == 0) {
      /*@ 0 <= lvalue && lvalue <= 0 && cm_binding_array_code(policy, p, fid, scope, slot) == 0 && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_var_code_for(policy, p, fid, scope, slot, ty, lvalue), tail)) which implies lvalue == 0 && cm_binding_array_code(policy, p, fid, scope, slot) == 0 && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_binding_address_code(policy, p, fid, scope, slot), app(cm_load_code(ty), tail))) */
      cm_emit_binding_address_plan(program, fn, expr->op,
                                   (int)expr->value, emitter) /*@ where policy = policy, cg = cg, p = p, f = f, fid = fid, structs = cm_program_structs(p), globals = cm_program_globals(p), functions_ptr = functions_ptr, body = body, next = next, done = done, out = out, capacity = capacity, tail = app(cm_load_code(ty), tail) */;
      cm_emit_load_plan(emitter, expr->ty) /*@ where policy = policy, p = p, done = app(done, cm_binding_address_code(policy, p, fid, scope, slot)), tail = tail, out = out, capacity = capacity, model_ty = ty */;
    } else {
      /*@ 0 <= lvalue && lvalue <= 0 && cm_binding_array_code(policy, p, fid, scope, slot) != 0 && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_var_code_for(policy, p, fid, scope, slot, ty, lvalue), tail)) which implies lvalue == 0 && cm_binding_array_code(policy, p, fid, scope, slot) != 0 && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_binding_address_code(policy, p, fid, scope, slot), tail)) */
      cm_emit_binding_address_plan(program, fn, expr->op,
                                   (int)expr->value, emitter) /*@ where policy = policy, cg = cg, p = p, f = f, fid = fid, structs = cm_program_structs(p), globals = cm_program_globals(p), functions_ptr = functions_ptr, body = body, next = next, done = done, out = out, capacity = capacity, tail = tail */;
    }
  } else {
      /*@ lvalue != 0 && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_var_code_for(policy, p, fid, scope, slot, ty, lvalue), tail)) which implies lvalue != 0 && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_binding_address_code(policy, p, fid, scope, slot), tail)) */
    cm_emit_binding_address_plan(program, fn, expr->op,
                                 (int)expr->value, emitter) /*@ where policy = policy, cg = cg, p = p, f = f, fid = fid, structs = cm_program_structs(p), globals = cm_program_globals(p), functions_ptr = functions_ptr, body = body, next = next, done = done, out = out, capacity = capacity, tail = tail */;
  }
}
