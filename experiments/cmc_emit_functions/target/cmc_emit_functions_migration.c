#include "cmc_layout_migration_abi.h"
struct cm_emitter { struct cm_output *output; int pc; };

/*@ Extern Coq
 (cm_type :: *)
 (cm_program :: *)
 (cm_function_d :: *)
 (cm_struct_d :: *)
 (cm_global_d :: *)
 (cm_string_d :: *)
 (cm_lookup_policy :: *)
 (cm_codegen_obligations :: *)
 (tvm_inst :: *)
 (cm_slot_d :: *)
 (bool :: *)
 (cm_stmt :: *)
*/
/*@ Extern Coq
 (cm_type_encode : cm_type -> Z)
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
 (cm_resolved_emitter_plan_rep : cm_lookup_policy -> cm_program -> Z -> Z -> Z -> list tvm_inst -> list tvm_inst -> Assertion)
 (cm_wf_program : cm_lookup_policy -> cm_codegen_obligations -> cm_program -> Prop)
 (cm_function_params : cm_function_d -> list cm_slot_d)
 (cm_function_locals : cm_function_d -> list cm_slot_d)
 (cm_slots_wf : list cm_struct_d -> list cm_slot_d -> Prop)
 (cm_rep_members_safe : list cm_slot_d -> Prop)
 (cm_temp_offset : cm_lookup_policy -> cm_program -> Z -> Z -> Z)
 (cm_i32_code_count : Z -> Prop)
 (cm_function_ret : cm_function_d -> cm_type)
 (cm_slot_list_rep : Z -> list cm_slot_d -> Assertion)
 (cm_stmt_rep : Z -> cm_stmt -> Assertion)
 (cm_stmt_wf : cm_lookup_policy -> cm_program -> cm_function_d -> bool -> cm_stmt -> Prop)
 (cm_stmt_counts_representable : cm_lookup_policy -> cm_program -> Z -> cm_stmt -> Prop)
 (cm_emit_stmt : cm_lookup_policy -> cm_program -> Z -> Z -> Z -> Z -> Z -> cm_stmt -> list tvm_inst)
 (cm_stemps : cm_stmt -> Z)
 (cm_function_body : cm_function_d -> cm_stmt)
 (cm_function_pc : cm_lookup_policy -> cm_program -> Z -> Z)
 (cm_function_prologue_count : cm_function_d -> Z)
 (cm_param_counts_representable : list cm_slot_d -> Prop)
 (cm_rep_stmt_temps_safe : cm_stmt -> Prop)
 (cm_rep_members_size : list cm_slot_d -> Z)
 (cm_emit_function : cm_lookup_policy -> cm_program -> Z -> list tvm_inst)
 (false : bool)
 (cm_emit_functions : cm_lookup_policy -> cm_program -> Z -> list cm_function_d -> list tvm_inst)
 (cm_emit_functions_tail : list cm_function_d -> list cm_function_d)
 (cm_concrete_functions_ready : cm_lookup_policy -> cm_program -> Z -> list cm_function_d -> Prop)
 (cm_function_counts_representable : cm_lookup_policy -> cm_program -> Z -> cm_function_d -> Prop)
 (cm_function_code_count : cm_lookup_policy -> cm_program -> Z -> Z)
 (cm_function_list_rep : Z -> list cm_function_d -> Assertion)
*/
/*@ Import Coq Require Import SimpleC.EE.QCP_demos_human.cmc_emit_functions_migration_lib */

int cmc_function_code_count(struct cm_program *program, int fid,
                                   struct cm_function *fn)
/*@ With (policy : cm_lookup_policy) (cg : cm_codegen_obligations) (p : cm_program) (f : cm_function_d) (functions_ptr : Z) (body_ptr : Z) (next_ptr : Z)
    Require cm_wf_program(policy, cg, p) && cm_function_counts_representable(policy, p, fid, f) && cm_stmt_wf(policy, p, f, false, cm_function_body(f)) && cm_rep_structs_safe(cm_program_structs(p)) && cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body_ptr, next_ptr) * cm_stmt_rep(body_ptr, cm_function_body(f))
    Ensure cm_wf_program(policy, cg, p) && cm_function_counts_representable(policy, p, fid, f) && cm_stmt_wf(policy, p, f, false, cm_function_body(f)) && cm_rep_structs_safe(cm_program_structs(p)) && __return == cm_function_code_count(policy, p, fid) && cm_i32_code_count(__return) && cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body_ptr, next_ptr) * cm_stmt_rep(body_ptr, cm_function_body(f))
*/;

void cmc_emit_function(
    struct cm_program *program, struct cm_function *fn,
    int fid, int function_pc, struct cm_emitter *emitter)
/*@ With (policy : cm_lookup_policy) (p : cm_program) (f : cm_function_d) (cg : cm_codegen_obligations) (s : cm_stmt) (body : Z) (next : Z) (functions_ptr : Z) (done : list tvm_inst) (tail : list tvm_inst) (out : Z) (capacity : Z)
 Require cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) && f == cm_function_at(policy, fid, cm_program_functions(p)) && s == cm_function_body(f) && function_pc == cm_function_pc(policy, p, fid) && cm_stmt_wf(policy, p, f, false, s) && cm_stmt_counts_representable(policy, p, fid, s) && cm_param_counts_representable(cm_function_params(f)) && cm_i32_code_count(cm_function_prologue_count(f)) && cm_i32_code_count(function_pc) && cm_i32_code_count(cm_function_pc(policy, p, fid) + cm_function_prologue_count(f)) && cm_i32_code_count(cm_function_pc(policy, p, fid) + cm_function_prologue_count(f) + Zlength(cm_emit_stmt(policy, p, fid, cm_function_pc(policy, p, fid) + cm_function_prologue_count(f), 0, 0, 0, s))) && cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) && cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) && cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) && cm_rep_stmt_temps_safe(s) && cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 && 8 + cm_rep_members_size(cm_function_params(f)) + cm_rep_members_size(cm_function_locals(f)) + 8 * cm_stemps(s) <= 2147483647 && cm_temp_offset(policy, p, fid, cm_stemps(s)) <= 2147483647 && cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body, next) * cm_stmt_rep(body, s) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_emit_function(policy, p, fid), tail))
 Ensure cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) && f == cm_function_at(policy, fid, cm_program_functions(p)) && s == cm_function_body(f) && function_pc == cm_function_pc(policy, p, fid) && cm_stmt_wf(policy, p, f, false, s) && cm_stmt_counts_representable(policy, p, fid, s) && cm_param_counts_representable(cm_function_params(f)) && cm_i32_code_count(cm_function_prologue_count(f)) && cm_i32_code_count(function_pc) && cm_i32_code_count(cm_function_pc(policy, p, fid) + cm_function_prologue_count(f)) && cm_i32_code_count(cm_function_pc(policy, p, fid) + cm_function_prologue_count(f) + Zlength(cm_emit_stmt(policy, p, fid, cm_function_pc(policy, p, fid) + cm_function_prologue_count(f), 0, 0, 0, s))) && cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) && cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) && cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) && cm_rep_stmt_temps_safe(s) && cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 && 8 + cm_rep_members_size(cm_function_params(f)) + cm_rep_members_size(cm_function_locals(f)) + 8 * cm_stemps(s) <= 2147483647 && cm_temp_offset(policy, p, fid, cm_stemps(s)) <= 2147483647 && cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body, next) * cm_stmt_rep(body, s) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cm_emit_function(policy, p, fid)), tail)
*/;

void cmc_emit_functions(
    struct cm_program *program, struct cm_function *fn,
    int fid, int function_pc, struct cm_emitter *emitter)
/*@ With (policy : cm_lookup_policy) (cg : cm_codegen_obligations) (p : cm_program) (functions : list cm_function_d) (functions_ptr : Z) (done : list tvm_inst) (tail : list tvm_inst) (out : Z) (capacity : Z)
 Require cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) && function_pc == cm_function_pc(policy, p, fid) && cm_concrete_functions_ready(policy, p, fid, functions) && cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) && cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 && cm_program_context_rep(program, p, functions_ptr) * cm_function_list_rep(fn, functions) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_emit_functions(policy, p, fid, functions), tail))
 Ensure cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) && function_pc == cm_function_pc(policy, p, fid) && cm_concrete_functions_ready(policy, p, fid, functions) && cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) && cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 && cm_program_context_rep(program, p, functions_ptr) * cm_function_list_rep(fn, functions) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cm_emit_functions(policy, p, fid, functions)), tail)
*/
{
  if (fn == 0) {
    return;
  };
  /*@ fn != 0 && cm_concrete_functions_ready(policy, p, fid, functions) && cm_function_list_rep(fn, functions)
      which implies exists (bp : Z) (np : Z), fn != 0 && functions == cons(cm_function_at(policy, fid, cm_program_functions(p)), cm_emit_functions_tail(functions)) && cm_concrete_functions_ready(policy, p, fid, functions) && cm_function_context_rep(fn, cm_function_at(policy, fid, cm_program_functions(p)), bp, np) * cm_stmt_rep(bp, cm_function_body(cm_function_at(policy, fid, cm_program_functions(p)))) * cm_function_list_rep(np, cm_emit_functions_tail(functions)) */
  /*@ cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) && function_pc == cm_function_pc(policy, p, fid) && cm_concrete_functions_ready(policy, p, fid, functions) && cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) && cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 && functions == cons(cm_function_at(policy, fid, cm_program_functions(p)), cm_emit_functions_tail(functions)) && emp
      which implies cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) && function_pc == cm_function_pc(policy, p, fid) && cm_concrete_functions_ready(policy, p, fid, functions) && cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) && cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 && functions == cons(cm_function_at(policy, fid, cm_program_functions(p)), cm_emit_functions_tail(functions)) && cm_function_counts_representable(policy, p, fid, cm_function_at(policy, fid, cm_program_functions(p))) && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) && function_pc == cm_function_pc(policy, p, fid) && cm_stmt_wf(policy, p, cm_function_at(policy, fid, cm_program_functions(p)), false, cm_function_body(cm_function_at(policy, fid, cm_program_functions(p)))) && cm_stmt_counts_representable(policy, p, fid, cm_function_body(cm_function_at(policy, fid, cm_program_functions(p)))) && cm_param_counts_representable(cm_function_params(cm_function_at(policy, fid, cm_program_functions(p)))) && cm_i32_code_count(cm_function_prologue_count(cm_function_at(policy, fid, cm_program_functions(p)))) && cm_i32_code_count(function_pc) && cm_i32_code_count(cm_function_pc(policy, p, fid) + cm_function_prologue_count(cm_function_at(policy, fid, cm_program_functions(p)))) && cm_i32_code_count(cm_function_pc(policy, p, fid) + cm_function_prologue_count(cm_function_at(policy, fid, cm_program_functions(p))) + Zlength(cm_emit_stmt(policy, p, fid, cm_function_pc(policy, p, fid) + cm_function_prologue_count(cm_function_at(policy, fid, cm_program_functions(p))), 0, 0, 0, cm_function_body(cm_function_at(policy, fid, cm_program_functions(p)))))) && cm_slots_wf(cm_program_structs(p), cm_function_params(cm_function_at(policy, fid, cm_program_functions(p)))) && cm_slots_wf(cm_program_structs(p), cm_function_locals(cm_function_at(policy, fid, cm_program_functions(p)))) && cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) && cm_rep_members_safe(cm_function_params(cm_function_at(policy, fid, cm_program_functions(p)))) && cm_rep_members_safe(cm_function_locals(cm_function_at(policy, fid, cm_program_functions(p)))) && cm_rep_stmt_temps_safe(cm_function_body(cm_function_at(policy, fid, cm_program_functions(p)))) && cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 && 8 + cm_rep_members_size(cm_function_params(cm_function_at(policy, fid, cm_program_functions(p)))) + cm_rep_members_size(cm_function_locals(cm_function_at(policy, fid, cm_program_functions(p)))) + 8 * cm_stemps(cm_function_body(cm_function_at(policy, fid, cm_program_functions(p)))) <= 2147483647 && cm_temp_offset(policy, p, fid, cm_stemps(cm_function_body(cm_function_at(policy, fid, cm_program_functions(p))))) <= 2147483647 && cm_i32_code_count(fid + 1) && cm_concrete_functions_ready(policy, p, fid + 1, cm_emit_functions_tail(functions)) && cm_function_pc(policy, p, fid + 1) == cm_function_pc(policy, p, fid) + cm_function_code_count(policy, p, fid) && cm_i32_code_count(cm_function_pc(policy, p, fid + 1)) && emp */
  int head_count = cmc_function_code_count(program, fid, fn) /*@ where policy = policy, cg = cg, p = p, f = cm_function_at(policy, fid, cm_program_functions(p)), functions_ptr = functions_ptr */;
  /*@ head_count == cm_function_code_count(policy, p, fid) && emp
      which implies data_at(&head_count, int, cm_function_code_count(policy, p, fid)) */
  /*@ fid == fid@pre && functions == cons(cm_function_at(policy, fid, cm_program_functions(p)), cm_emit_functions_tail(functions)) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_emit_functions(policy, p, fid, functions), tail))
      which implies fid == fid@pre && functions == cons(cm_function_at(policy, fid, cm_program_functions(p)), cm_emit_functions_tail(functions)) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_emit_function(policy, p, fid), app(cm_emit_functions(policy, p, fid + 1, cm_emit_functions_tail(functions)), tail))) */
  cmc_emit_function(program, fn, fid, function_pc, emitter) /*@ where policy = policy, cg = cg, p = p, f = cm_function_at(policy, fid, cm_program_functions(p)), s = cm_function_body(cm_function_at(policy, fid, cm_program_functions(p))), functions_ptr = functions_ptr, done = done, tail = app(cm_emit_functions(policy, p, fid + 1, cm_emit_functions_tail(functions)), tail), out = out, capacity = capacity */;
  struct cm_function *next_fn;
  /*@ exists (bp : Z) (np : Z), cm_function_context_rep(fn, cm_function_at(policy, fid, cm_program_functions(p)), bp, np) * cm_stmt_rep(bp, cm_function_body(cm_function_at(policy, fid, cm_program_functions(p)))) * cm_function_list_rep(np, cm_emit_functions_tail(functions))
      which implies exists (bp : Z) (np : Z) (pp : Z) (lp : Z), fn != 0 && data_at(&(fn->ret_ty), int, cm_type_encode(cm_function_ret(cm_function_at(policy, fid, cm_program_functions(p))))) * data_at(&(fn->params), struct cm_slot *, pp) * data_at(&(fn->locals), struct cm_slot *, lp) * data_at(&(fn->body), struct cm_stmt *, bp) * data_at(&(fn->next), struct cm_function *, np) * cm_slot_list_rep(pp, cm_function_params(cm_function_at(policy, fid, cm_program_functions(p)))) * cm_slot_list_rep(lp, cm_function_locals(cm_function_at(policy, fid, cm_program_functions(p)))) * cm_stmt_rep(bp, cm_function_body(cm_function_at(policy, fid, cm_program_functions(p)))) * cm_function_list_rep(np, cm_emit_functions_tail(functions)) */
  next_fn = fn->next;
  /*@ exists (bp : Z) (pp : Z) (lp : Z), fn != 0 && data_at(&(fn->ret_ty), int, cm_type_encode(cm_function_ret(cm_function_at(policy, fid, cm_program_functions(p))))) * data_at(&(fn->params), struct cm_slot *, pp) * data_at(&(fn->locals), struct cm_slot *, lp) * data_at(&(fn->body), struct cm_stmt *, bp) * data_at(&(fn->next), struct cm_function *, next_fn) * cm_slot_list_rep(pp, cm_function_params(cm_function_at(policy, fid, cm_program_functions(p)))) * cm_slot_list_rep(lp, cm_function_locals(cm_function_at(policy, fid, cm_program_functions(p)))) * cm_stmt_rep(bp, cm_function_body(cm_function_at(policy, fid, cm_program_functions(p))))
      which implies exists (bp : Z), cm_function_context_rep(fn, cm_function_at(policy, fid, cm_program_functions(p)), bp, next_fn) * cm_stmt_rep(bp, cm_function_body(cm_function_at(policy, fid, cm_program_functions(p)))) */
  int next_pc = function_pc + head_count;
  cmc_emit_functions(program, next_fn, fid + 1, next_pc, emitter) /*@ where policy = policy, cg = cg, p = p, functions = cm_emit_functions_tail(functions), functions_ptr = functions_ptr, done = app(done, cm_emit_function(policy, p, fid)), tail = tail, out = out, capacity = capacity */;
  /*@ fid == fid@pre && functions == cons(cm_function_at(policy, fid, cm_program_functions(p)), cm_emit_functions_tail(functions)) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(app(done, cm_emit_function(policy, p, fid)), cm_emit_functions(policy, p, fid + 1, cm_emit_functions_tail(functions))), tail)
      which implies fid == fid@pre && functions == cons(cm_function_at(policy, fid, cm_program_functions(p)), cm_emit_functions_tail(functions)) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cm_emit_functions(policy, p, fid, functions)), tail) */
}
