#include "cmc_layout_migration_abi.h"

struct cm_emitter {
  struct cm_output *output;
  int pc;
};

/*@ Extern Coq
    (cm_type :: *) (cm_slot_d :: *) (cm_struct_d :: *)
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
/*@ Import Coq Require Import SimpleC.EE.QCP_demos_human.cmc_emit_ast_migration_lib */

long long cmc_global_address(struct cm_global *globals, int index)
/*@ With (items : list cm_global_d)
    Require 0 <= index && cm_rep_globals_safe(items) && cm_global_list_rep(globals, items)
    Ensure 0 <= index && cm_rep_globals_safe(items) && __return == cm_rep_global_address(items, index) && 16 <= __return && __return <= 1048576 && cm_global_list_rep(globals, items)
*/;

long long cmc_local_offset(struct cm_function *fn, int slot)
/*@ With (params : list cm_slot_d) (zp : Z) (locals : list cm_slot_d) (zl : Z)
    Require cm_rep_members_safe(params) && cm_rep_members_safe(locals) && 0 <= slot && data_at(&(fn->params), struct cm_slot *, zp) * cm_slot_list_rep(zp, params) * data_at(&(fn->locals), struct cm_slot *, zl) * cm_slot_list_rep(zl, locals)
    Ensure cm_rep_members_safe(params) && cm_rep_members_safe(locals) && 0 <= slot && __return == 8 + cm_rep_members_size(params) + cm_rep_member_prefix(locals, slot) && data_at(&(fn->params), struct cm_slot *, zp) * cm_slot_list_rep(zp, params) * data_at(&(fn->locals), struct cm_slot *, zl) * cm_slot_list_rep(zl, locals)
*/;

long long cmc_param_offset(struct cm_function *fn, int slot)
/*@ With (params : list cm_slot_d) (zp : Z)
    Require cm_rep_members_safe(params) && 0 <= slot && data_at(&(fn->params), struct cm_slot *, zp) * cm_slot_list_rep(zp, params)
    Ensure cm_rep_members_safe(params) && 0 <= slot && __return == 8 + cm_rep_member_prefix(params, slot) && data_at(&(fn->params), struct cm_slot *, zp) * cm_slot_list_rep(zp, params)
*/;

void cm_emit_resolved(struct cm_emitter *emitter, int op,
                      long long immediate)
/*@ With (policy : cm_lookup_policy) (p : cm_program) (done : list tvm_inst) (out : Z) (capacity : Z) (opcode : tvm_opcode)
    Require op == tvm_opcode_code(opcode) && tvm_opcode_code(opcode) != 22 && Zlength(done) + 1 <= capacity && cm_resolved_emitter_rep(policy, p, emitter, out, capacity, done)
    Ensure cm_resolved_emitter_rep(policy, p, emitter, out, capacity, app(done, cons(TVMInst(opcode, immediate), nil)))
*/;

void cm_emit_resolved_fp_address(struct cm_emitter *emitter,
                                 long long offset)
/*@ With (policy : cm_lookup_policy) (p : cm_program) (done : list tvm_inst) (out : Z) (capacity : Z)
    Require Zlength(done) + Zlength(cm_fp_relative_address_code(offset)) <= capacity && cm_resolved_emitter_rep(policy, p, emitter, out, capacity, done)
    Ensure cm_resolved_emitter_rep(policy, p, emitter, out, capacity, app(done, cm_fp_relative_address_code(offset)))
*/;

void cm_emit_binding_address(struct cm_program *program,
                             struct cm_function *fn,
                             int scope, int slot,
                             struct cm_emitter *emitter)
/*@ With (policy : cm_lookup_policy) (cg : cm_codegen_obligations)
    (p : cm_program) (f : cm_function_d) (fid : Z)
    (structs : list cm_struct_d) (globals : list cm_global_d)
    (functions_ptr : Z) (body : Z) (next : Z)
    (done : list tvm_inst) (out : Z) (capacity : Z)
    Require cm_wf_program(policy, cg, p) &&
      f == cm_function_at(policy, fid, cm_program_functions(p)) &&
      structs == cm_program_structs(p) && globals == cm_program_globals(p) &&
      cm_binding_valid(p, f, scope, slot) &&
      cm_slots_wf(structs, cm_function_params(f)) &&
      cm_slots_wf(structs, cm_function_locals(f)) &&
      cm_rep_globals_safe(globals) &&
      cm_rep_members_safe(cm_function_params(f)) &&
      cm_rep_members_safe(cm_function_locals(f)) &&
      Zlength(done) + Zlength(cm_binding_address_code(policy, p, fid, scope, slot)) <= capacity && cm_program_context_rep(program, p, functions_ptr) *
      cm_function_context_rep(fn, f, body, next) *
      cm_resolved_emitter_rep(policy, p, emitter, out, capacity, done)
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
      cm_resolved_emitter_rep(policy, p, emitter, out, capacity, app(done, cm_binding_address_code(policy, p, fid, scope, slot)))
*/
{
  /*@ Assert exists (sp : Z) (gp : Z) (tp : Z) (zp : Z) (zl : Z),
    program == program@pre && fn == fn@pre && scope == scope@pre &&
    slot == slot@pre && emitter == emitter@pre &&
    program != 0 && fn != 0 && 0 <= slot &&
    cm_wf_program(policy, cg, p) &&
      f == cm_function_at(policy, fid, cm_program_functions(p)) &&
      structs == cm_program_structs(p) && globals == cm_program_globals(p) &&
      cm_binding_valid(p, f, scope, slot) &&
      cm_slots_wf(structs, cm_function_params(f)) &&
      cm_slots_wf(structs, cm_function_locals(f)) &&
      cm_rep_globals_safe(globals) &&
      cm_rep_members_safe(cm_function_params(f)) &&
      cm_rep_members_safe(cm_function_locals(f)) && Zlength(done) + Zlength(cm_binding_address_code(policy, p, fid, scope, slot)) <= capacity &&
    data_at(&(program->structs), struct cm_struct *, sp) *
    data_at(&(program->globals), struct cm_global *, gp) *
    data_at(&(program->strings), struct cm_string *, tp) *
    data_at(&(program->functions), struct cm_function *, functions_ptr) *
    data_at(&(program->main_id), int, cm_program_main(p)) *
    cm_struct_list_rep(sp, cm_program_structs(p)) *
    cm_global_list_rep(gp, cm_program_globals(p)) *
    cm_string_list_rep(tp, cm_program_strings(p)) *
    data_at(&(fn->ret_ty), int, cm_type_encode(cm_function_ret(f))) *
    data_at(&(fn->params), struct cm_slot *, zp) *
    data_at(&(fn->locals), struct cm_slot *, zl) *
    data_at(&(fn->body), struct cm_stmt *, body) *
    data_at(&(fn->next), struct cm_function *, next) *
    cm_slot_list_rep(zp, cm_function_params(f)) *
    cm_slot_list_rep(zl, cm_function_locals(f)) *
    cm_resolved_emitter_rep(policy, p, emitter, out, capacity, done)
  */
  if (scope == CMC_BIND_GLOBAL) {
    long long address = cmc_global_address(program->globals, slot) /*@ where items = cm_program_globals(p) */;
    cm_emit_resolved(emitter, CMC_OP_PUSH, address) /*@ where policy = policy, p = p, done = done, out = out, capacity = capacity, opcode = TVMPushOp */;
  } else if (scope == CMC_BIND_LOCAL) {
    long long offset = cmc_local_offset(fn, slot) /*@ where params = cm_function_params(f), locals = cm_function_locals(f) */;
    cm_emit_resolved_fp_address(emitter, offset) /*@ where policy = policy, p = p, done = done, out = out, capacity = capacity */;
  } else {
    long long offset = cmc_param_offset(fn, slot) /*@ where params = cm_function_params(f) */;
    cm_emit_resolved_fp_address(emitter, offset) /*@ where policy = policy, p = p, done = done, out = out, capacity = capacity */;
  }
}

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
*/
{
  /*@ Assert program == program@pre && fn == fn@pre && scope == scope@pre &&
    slot == slot@pre && emitter == emitter@pre &&
    Zlength(app(done, cm_binding_address_code(policy, p, fid, scope, slot))) + Zlength(tail) <= capacity &&
    cm_wf_program(policy, cg, p) &&
      f == cm_function_at(policy, fid, cm_program_functions(p)) &&
      structs == cm_program_structs(p) && globals == cm_program_globals(p) &&
      cm_binding_valid(p, f, scope, slot) &&
      cm_slots_wf(structs, cm_function_params(f)) &&
      cm_slots_wf(structs, cm_function_locals(f)) &&
      cm_rep_globals_safe(globals) &&
      cm_rep_members_safe(cm_function_params(f)) &&
      cm_rep_members_safe(cm_function_locals(f)) && Zlength(done) + Zlength(cm_binding_address_code(policy, p, fid, scope, slot)) <= capacity && cm_program_context_rep(program, p, functions_ptr) *
      cm_function_context_rep(fn, f, body, next) *
    cm_resolved_emitter_rep(policy, p, emitter, out, capacity, done)
  */
  cm_emit_binding_address(program, fn, scope, slot, emitter) /*@ where policy = policy, cg = cg, p = p, f = f, fid = fid, structs = structs, globals = globals, functions_ptr = functions_ptr, body = body, next = next, done = done, out = out, capacity = capacity */;
}
