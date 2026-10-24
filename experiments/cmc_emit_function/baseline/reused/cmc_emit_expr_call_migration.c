#include "cmc_layout_migration_abi.h"
struct cm_emitter { struct cm_output *output; int pc; };

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
 (bool :: *)
 (cm_stmt :: *)
 (cm_tpair :: *)
 (cm_apair :: *)
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
 (cm_expr_rep : Z -> cm_expr -> Assertion)
 (cm_rep_expr_kind : cm_expr -> Z)
 (cm_rep_expr_op : cm_expr -> Z)
 (cm_rep_expr_value : cm_expr -> Z)
 (cm_expr_type : cm_expr -> cm_type)
 (cm_expr_payload : cm_expr -> Z -> Z -> Z -> Assertion)
 (cm_resolved_emitter_plan_rep : cm_lookup_policy -> cm_program -> Z -> Z -> Z -> list tvm_inst -> list tvm_inst -> Assertion)
 (cm_wf_program : cm_lookup_policy -> cm_codegen_obligations -> cm_program -> Prop)
 (cm_expr_wf : cm_lookup_policy -> cm_program -> cm_function_d -> cm_expr -> Prop)
 (cm_expr_counts_representable : cm_lookup_policy -> cm_program -> Z -> cm_expr -> Prop)
 (cm_function_params : cm_function_d -> list cm_slot_d)
 (cm_function_locals : cm_function_d -> list cm_slot_d)
 (cm_slots_wf : list cm_struct_d -> list cm_slot_d -> Prop)
 (cm_rep_members_safe : list cm_slot_d -> Prop)
 (TVMInst : tvm_opcode -> Z -> tvm_inst)
 (cm_temp_store_code : cm_lookup_policy -> cm_program -> Z -> Z -> list tvm_inst)
 (cm_temp_load_code : cm_lookup_policy -> cm_program -> Z -> Z -> list tvm_inst)
 (cm_temp_offset : cm_lookup_policy -> cm_program -> Z -> Z -> Z)
 (TVMCallOp : tvm_opcode)
 (cm_function_pc : cm_lookup_policy -> cm_program -> Z -> Z)
 (cm_rvalue_code_count : cm_lookup_policy -> cm_program -> Z -> cm_expr -> Z)
 (cm_i32_code_count : Z -> Prop)
 (cm_rep_args_safe : list cm_expr -> Prop)
 (cm_rep_args_length : list cm_expr -> Z)
 (cm_arg_list_rep : Z -> list cm_expr -> Assertion)
 (cm_args_apair : list cm_expr -> cm_apair)
 (cm_adepth : cm_apair -> Z)
 (cm_args_head : list cm_expr -> cm_expr)
 (cm_args_tail : list cm_expr -> list cm_expr)
 (cm_call_slots_tail : list cm_slot_d -> list cm_slot_d)
 (cm_call_args : cm_expr -> list cm_expr)
 (CMCallE : Z -> list cm_expr -> cm_type -> cm_expr)
 (cm_emit_args_reload : cm_lookup_policy -> cm_program -> Z -> Z -> list cm_expr -> list tvm_inst)
 (cm_emit_args_store : cm_lookup_policy -> cm_program -> Z -> Z -> Z -> Z -> list cm_expr -> list tvm_inst)
 (cm_expr_code_for : cm_lookup_policy -> cm_program -> Z -> Z -> Z -> cm_expr -> Z -> list tvm_inst)
 (cm_expr_temps_for : cm_expr -> Z -> Z)
 (cm_args_wf : cm_lookup_policy -> cm_program -> cm_function_d -> list cm_expr -> list cm_slot_d -> Prop)
 (cm_args_counts_representable : cm_lookup_policy -> cm_program -> Z -> list cm_expr -> Prop)
*/
/*@ Import Coq Require Import SimpleC.EE.QCP_demos_human.cmc_emit_expr_call_migration_lib */

void cm_emit_call_plan(struct cm_emitter *emitter, int function_id)
/*@ With (policy : cm_lookup_policy) (p : cm_program) (done : list tvm_inst) (tail : list tvm_inst) (out : Z) (capacity : Z)
    Require cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, cons(TVMInst(TVMCallOp, cm_function_pc(policy, p, function_id)), tail))
    Ensure cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cons(TVMInst(TVMCallOp, cm_function_pc(policy, p, function_id)), nil)), tail)
*/;

void cm_emit_temp_store_plan(struct cm_function *fn, int temp,
                             struct cm_emitter *emitter)
/*@ With (policy : cm_lookup_policy) (p : cm_program) (done : list tvm_inst) (tail : list tvm_inst) (out : Z) (capacity : Z) (f : cm_function_d) (fid : Z) (structs : list cm_struct_d) (body : Z) (next : Z)
    Require 0 <= temp && structs == cm_program_structs(p) && f == cm_function_at(policy, fid, cm_program_functions(p)) && cm_slots_wf(structs, cm_function_params(f)) && cm_slots_wf(structs, cm_function_locals(f)) && cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) && cm_temp_offset(policy, p, fid, temp) <= 2147483647 && cm_function_context_rep(fn, f, body, next) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_temp_store_code(policy, p, fid, temp), tail))
    Ensure 0 <= temp && structs == cm_program_structs(p) && f == cm_function_at(policy, fid, cm_program_functions(p)) && cm_slots_wf(structs, cm_function_params(f)) && cm_slots_wf(structs, cm_function_locals(f)) && cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) && cm_temp_offset(policy, p, fid, temp) <= 2147483647 && cm_function_context_rep(fn, f, body, next) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cm_temp_store_code(policy, p, fid, temp)), tail)
*/;

void cm_emit_temp_load_plan(struct cm_function *fn, int temp,
                            struct cm_emitter *emitter)
/*@ With (policy : cm_lookup_policy) (p : cm_program) (done : list tvm_inst) (tail : list tvm_inst) (out : Z) (capacity : Z) (f : cm_function_d) (fid : Z) (structs : list cm_struct_d) (body : Z) (next : Z)
    Require 0 <= temp && structs == cm_program_structs(p) && f == cm_function_at(policy, fid, cm_program_functions(p)) && cm_slots_wf(structs, cm_function_params(f)) && cm_slots_wf(structs, cm_function_locals(f)) && cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) && cm_temp_offset(policy, p, fid, temp) <= 2147483647 && cm_function_context_rep(fn, f, body, next) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_temp_load_code(policy, p, fid, temp), tail))
    Ensure 0 <= temp && structs == cm_program_structs(p) && f == cm_function_at(policy, fid, cm_program_functions(p)) && cm_slots_wf(structs, cm_function_params(f)) && cm_slots_wf(structs, cm_function_locals(f)) && cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) && cm_temp_offset(policy, p, fid, temp) <= 2147483647 && cm_function_context_rep(fn, f, body, next) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cm_temp_load_code(policy, p, fid, temp)), tail)
*/;

int cm_expr_rvalue_count_context(struct cm_program *program, int fid,
                                 struct cm_function *fn,
                                 struct cm_expr *expr)
/*@ With (policy : cm_lookup_policy) (cg : cm_codegen_obligations) (p : cm_program) (f : cm_function_d) (e : cm_expr) (body : Z) (next : Z) (functions_ptr : Z)
    Require cm_wf_program(policy, cg, p) && f == cm_function_at(policy, fid, cm_program_functions(p)) && cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) && cm_rep_structs_safe(cm_program_structs(p)) && cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body, next) * cm_expr_rep(expr, e)
    Ensure cm_wf_program(policy, cg, p) && f == cm_function_at(policy, fid, cm_program_functions(p)) && cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) && cm_rep_structs_safe(cm_program_structs(p)) && __return == cm_rvalue_code_count(policy, p, fid, e) && cm_i32_code_count(__return) && cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body, next) * cm_expr_rep(expr, e)
*/;

int cm_args_length(struct cm_arg *arg)
/*@ With (args : list cm_expr)
    Require cm_rep_args_safe(args) && cm_arg_list_rep(arg, args)
    Ensure cm_rep_args_safe(args) && __return == cm_rep_args_length(args) && cm_arg_list_rep(arg, args)
*/;

/* Original external module dependency: implementation proof pending. */
void cm_emit_expr(struct cm_program *program, int fid, struct cm_function *fn,
 int pc, int temp, int temp_limit, struct cm_expr *expr, int lvalue, struct cm_emitter *emitter)
/*@ With (policy : cm_lookup_policy) (cg : cm_codegen_obligations) (p : cm_program) (f : cm_function_d) (e : cm_expr) (body : Z) (next : Z) (functions_ptr : Z) (done : list tvm_inst) (tail : list tvm_inst) (out : Z) (capacity : Z)
 Require 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body, next) * cm_expr_rep(expr, e) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue), tail))
 Ensure 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body, next) * cm_expr_rep(expr, e) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue)), tail)
*/;

static void cm_emit_args_reload_plan(struct cm_function *fn, int slot,
                                     int temp_limit, struct cm_arg *arg,
                                     struct cm_emitter *emitter)
/*@ With (policy : cm_lookup_policy) (p : cm_program) (f : cm_function_d) (fid : Z) (args : list cm_expr) (body : Z) (next : Z) (done : list tvm_inst) (tail : list tvm_inst) (out : Z) (capacity : Z)
 Require 0 <= slot && slot + Zlength(args) <= temp_limit && 0 <= temp_limit && temp_limit <= 2147483647 &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) && cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_function_context_rep(fn, f, body, next) * cm_arg_list_rep(arg, args) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_emit_args_reload(policy, p, fid, slot, args), tail))
 Ensure 0 <= slot && slot + Zlength(args) <= temp_limit && 0 <= temp_limit && temp_limit <= 2147483647 &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) && cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_function_context_rep(fn, f, body, next) * cm_arg_list_rep(arg, args) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cm_emit_args_reload(policy, p, fid, slot, args)), tail)
*/
{
  if (arg == 0) {

 /*@ arg@pre == 0 && cm_arg_list_rep(arg@pre, args)
 which implies args == nil && cm_arg_list_rep(arg@pre, args) */
    return;
  } else {
  }

 /*@ arg != 0 && cm_arg_list_rep(arg, args)
 which implies exists (ep : Z) (np : Z), arg != 0 && args == cons(cm_args_head(args), cm_args_tail(args)) && data_at(&(arg->expr), struct cm_expr *, ep) * data_at(&(arg->next), struct cm_arg *, np) * cm_expr_rep(ep, cm_args_head(args)) * cm_arg_list_rep(np, cm_args_tail(args)) */

 /*@ 0 <= slot && slot + Zlength(args) <= temp_limit && temp_limit <= 2147483647 && cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && args == cons(cm_args_head(args), cm_args_tail(args)) && emp
 which implies 0 <= slot + 1 && slot + 1 <= 2147483647 && slot + 1 + Zlength(cm_args_tail(args)) <= temp_limit && cm_temp_offset(policy, p, fid, slot) <= 2147483647 && emp */

 /*@ args == cons(cm_args_head(args), cm_args_tail(args)) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_emit_args_reload(policy, p, fid, slot, args), tail))
 which implies cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_temp_load_code(policy, p, fid, slot), app(cm_emit_args_reload(policy, p, fid, slot + 1, cm_args_tail(args)), tail))) */
  cm_emit_temp_load_plan(fn, slot, emitter) /*@ where policy = policy, p = p, f = f, fid = fid, structs = cm_program_structs(p), body = body, next = next, done = done, tail = app(cm_emit_args_reload(policy, p, fid, slot + 1, cm_args_tail(args)), tail), out = out, capacity = capacity */;
  cm_emit_args_reload_plan(fn, slot + 1, temp_limit,
                           arg->next, emitter) /*@ where policy = policy, p = p, f = f, fid = fid, args = cm_args_tail(args), body = body, next = next, done = app(done, cm_temp_load_code(policy, p, fid, slot)), tail = tail, out = out, capacity = capacity */;
 /*@ exists (ep : Z) (np : Z), arg != 0 && args == cons(cm_args_head(args), cm_args_tail(args)) && data_at(&(arg->expr), struct cm_expr *, ep) * data_at(&(arg->next), struct cm_arg *, np) * cm_expr_rep(ep, cm_args_head(args)) * cm_arg_list_rep(np, cm_args_tail(args))
 which implies cm_arg_list_rep(arg, args) */

}

static void cm_emit_args_store_plan(struct cm_program *program, int fid,
                                    struct cm_function *fn, int pc,
                                    int slot, int scratch, int temp_limit,
                                    struct cm_arg *arg,
                                    struct cm_emitter *emitter)
/*@ With (policy : cm_lookup_policy) (cg : cm_codegen_obligations) (p : cm_program) (f : cm_function_d) (args : list cm_expr) (slots : list cm_slot_d) (body : Z) (next : Z) (functions_ptr : Z) (done : list tvm_inst) (tail : list tvm_inst) (out : Z) (capacity : Z)
 Require cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 && cm_args_wf(policy, p, f, args, slots) && cm_args_counts_representable(policy, p, fid, args) &&
 0 <= slot && slot + Zlength(args) == scratch && 0 <= scratch && scratch <= temp_limit &&
 scratch + cm_adepth(cm_args_apair(args)) <= temp_limit && 0 <= temp_limit && temp_limit <= 2147483647 &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_emit_args_store(policy, p, fid, pc, slot, scratch, args))) && cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body, next) * cm_arg_list_rep(arg, args) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_emit_args_store(policy, p, fid, pc, slot, scratch, args), tail))
 Ensure cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 && cm_args_wf(policy, p, f, args, slots) && cm_args_counts_representable(policy, p, fid, args) &&
 0 <= slot && slot + Zlength(args) == scratch && 0 <= scratch && scratch <= temp_limit &&
 scratch + cm_adepth(cm_args_apair(args)) <= temp_limit && 0 <= temp_limit && temp_limit <= 2147483647 &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_emit_args_store(policy, p, fid, pc, slot, scratch, args))) && cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body, next) * cm_arg_list_rep(arg, args) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cm_emit_args_store(policy, p, fid, pc, slot, scratch, args)), tail)
*/
{
  if (arg == 0) {

 /*@ arg@pre == 0 && cm_arg_list_rep(arg@pre, args)
 which implies args == nil && cm_arg_list_rep(arg@pre, args) */
    return;
  } else {
  }

 /*@ arg != 0 && cm_arg_list_rep(arg, args)
 which implies exists (ep : Z) (np : Z), arg != 0 && args == cons(cm_args_head(args), cm_args_tail(args)) && data_at(&(arg->expr), struct cm_expr *, ep) * data_at(&(arg->next), struct cm_arg *, np) * cm_expr_rep(ep, cm_args_head(args)) * cm_arg_list_rep(np, cm_args_tail(args)) */

 /*@ args == cons(cm_args_head(args), cm_args_tail(args)) && cm_args_wf(policy, p, f, args, slots) && cm_args_counts_representable(policy, p, fid, args) && emp
 which implies cm_expr_wf(policy, p, f, cm_args_head(args)) && cm_expr_counts_representable(policy, p, fid, cm_args_head(args)) && cm_args_wf(policy, p, f, cm_args_tail(args), cm_call_slots_tail(slots)) && cm_args_counts_representable(policy, p, fid, cm_args_tail(args)) && emp */
  int head_count =
      cm_expr_rvalue_count_context(program, fid, fn, arg->expr) /*@ where policy = policy, cg = cg, p = p, f = f, e = cm_args_head(args), body = body, next = next, functions_ptr = functions_ptr */;

 /*@ args == cons(cm_args_head(args), cm_args_tail(args)) && head_count == cm_rvalue_code_count(policy, p, fid, cm_args_head(args)) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_emit_args_store(policy, p, fid, pc, slot, scratch, args), tail))
 which implies cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_expr_code_for(policy, p, fid, pc, scratch, cm_args_head(args), 0), app(cm_temp_store_code(policy, p, fid, slot), app(cm_emit_args_store(policy, p, fid, pc + head_count + 5, slot + 1, scratch, cm_args_tail(args)), tail)))) */

 /*@ args == cons(cm_args_head(args), cm_args_tail(args)) && 0 <= slot && slot + Zlength(args) == scratch && scratch <= temp_limit && scratch + cm_adepth(cm_args_apair(args)) <= temp_limit && temp_limit <= 2147483647 && cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) && cm_i32_code_count(pc + Zlength(cm_emit_args_store(policy, p, fid, pc, slot, scratch, args))) && head_count == cm_rvalue_code_count(policy, p, fid, cm_args_head(args)) && emp
 which implies 0 <= slot + 1 && slot + 1 <= 2147483647 && slot + 1 + Zlength(cm_args_tail(args)) == scratch && scratch + cm_expr_temps_for(cm_args_head(args), 0) <= temp_limit && scratch + cm_adepth(cm_args_apair(cm_args_tail(args))) <= temp_limit && cm_temp_offset(policy, p, fid, slot) <= 2147483647 && cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, scratch, cm_args_head(args), 0))) && 0 <= pc + head_count && pc + head_count <= 2147483647 && 0 <= pc + head_count + 5 && pc + head_count + 5 <= 2147483647 && cm_i32_code_count(pc + head_count + 5) && cm_i32_code_count(pc + head_count + 5 + Zlength(cm_emit_args_store(policy, p, fid, pc + head_count + 5, slot + 1, scratch, cm_args_tail(args)))) && emp */
  cm_emit_expr(program, fid, fn, pc, scratch, temp_limit,
               arg->expr, 0, emitter) /*@ where policy = policy, cg = cg, p = p, f = f, e = cm_args_head(args), body = body, next = next, functions_ptr = functions_ptr, done = done, tail = app(cm_temp_store_code(policy, p, fid, slot), app(cm_emit_args_store(policy, p, fid, pc + head_count + 5, slot + 1, scratch, cm_args_tail(args)), tail)), out = out, capacity = capacity */;
  cm_emit_temp_store_plan(fn, slot, emitter) /*@ where policy = policy, p = p, f = f, fid = fid, structs = cm_program_structs(p), body = body, next = next, done = app(done, cm_expr_code_for(policy, p, fid, pc, scratch, cm_args_head(args), 0)), tail = app(cm_emit_args_store(policy, p, fid, pc + head_count + 5, slot + 1, scratch, cm_args_tail(args)), tail), out = out, capacity = capacity */;
  cm_emit_args_store_plan(program, fid, fn,
      pc + head_count + 5, slot + 1, scratch, temp_limit,
      arg->next, emitter) /*@ where policy = policy, cg = cg, p = p, f = f, args = cm_args_tail(args), slots = cm_call_slots_tail(slots), body = body, next = next, functions_ptr = functions_ptr, done = app(app(done, cm_expr_code_for(policy, p, fid, pc, scratch, cm_args_head(args), 0)), cm_temp_store_code(policy, p, fid, slot)), tail = tail, out = out, capacity = capacity */;
 /*@ exists (ep : Z) (np : Z), arg != 0 && args == cons(cm_args_head(args), cm_args_tail(args)) && data_at(&(arg->expr), struct cm_expr *, ep) * data_at(&(arg->next), struct cm_arg *, np) * cm_expr_rep(ep, cm_args_head(args)) * cm_arg_list_rep(np, cm_args_tail(args))
 which implies cm_arg_list_rep(arg, args) */

}

void cm_emit_call_expr(struct cm_program *program, int fid,
                       struct cm_function *fn, int pc, int temp,
                       int temp_limit, struct cm_expr *expr,
                       int lvalue, struct cm_emitter *emitter)
/*@ With (policy : cm_lookup_policy) (cg : cm_codegen_obligations) (p : cm_program) (f : cm_function_d) (e : cm_expr) (body : Z) (next : Z) (functions_ptr : Z) (done : list tvm_inst) (tail : list tvm_inst) (out : Z) (capacity : Z)
 Require cm_rep_expr_kind(e) == 8 && 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body, next) * cm_expr_rep(expr, e) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue), tail))
 Ensure cm_rep_expr_kind(e) == 8 && 0 <= lvalue && lvalue <= 1 && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) &&
 f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) &&
 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) &&
 cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue))) && cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body, next) * cm_expr_rep(expr, e) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue)), tail)
*/
{

 

 

 
  if (!lvalue) {

 

 

 /*@ cm_rep_expr_kind(e) == 8 && cm_expr_rep(expr, e)
 which implies exists (xargs : Z), expr != 0 && data_at(&(expr->kind), int, cm_rep_expr_kind(e)) * data_at(&(expr->op), int, cm_rep_expr_op(e)) * data_at(&(expr->ty), int, cm_type_encode(cm_expr_type(e))) * data_at(&(expr->value), long long, cm_rep_expr_value(e)) * data_at(&(expr->a), struct cm_expr *, 0) * data_at(&(expr->b), struct cm_expr *, 0) * data_at(&(expr->args), struct cm_arg *, xargs) * cm_arg_list_rep(xargs, cm_call_args(e)) */

 /*@ cm_rep_expr_kind(e) == 8 && lvalue@pre == 0 && cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) && 0 <= temp && temp <= temp_limit && temp + cm_expr_temps_for(e, lvalue@pre) <= temp_limit && cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && f == cm_function_at(policy, fid, cm_program_functions(p)) && cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) && cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) && emp
 which implies 0 <= cm_rep_expr_value(e) && cm_rep_expr_value(e) <= 2147483647 && cm_args_wf(policy, p, f, cm_call_args(e), cm_function_params(cm_function_at(policy, cm_rep_expr_value(e), cm_program_functions(p)))) && cm_args_counts_representable(policy, p, fid, cm_call_args(e)) && cm_rep_args_safe(cm_call_args(e)) && cm_rep_args_length(cm_call_args(e)) == Zlength(cm_call_args(e)) && 0 <= temp_limit && temp_limit <= 2147483647 && 0 <= temp + Zlength(cm_call_args(e)) && temp + Zlength(cm_call_args(e)) <= temp_limit && temp + Zlength(cm_call_args(e)) <= 2147483647 && temp + Zlength(cm_call_args(e)) + cm_adepth(cm_args_apair(cm_call_args(e))) <= temp_limit && emp */
    int count = cm_args_length(expr->args) /*@ where args = cm_call_args(e) */;

 

 /*@ cm_rep_expr_kind(e) == 8 && lvalue@pre == 0 && count == Zlength(cm_call_args(e)) && cm_i32_code_count(pc) && cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue@pre))) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_expr_code_for(policy, p, fid, pc, temp, e, lvalue@pre), tail))
 which implies cm_i32_code_count(pc + Zlength(cm_emit_args_store(policy, p, fid, pc, temp, temp + count, cm_call_args(e)))) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_emit_args_store(policy, p, fid, pc, temp, temp + count, cm_call_args(e)), app(cm_emit_args_reload(policy, p, fid, temp, cm_call_args(e)), cons(TVMInst(TVMCallOp, cm_function_pc(policy, p, cm_rep_expr_value(e))), tail)))) */
    cm_emit_args_store_plan(program, fid, fn, pc, temp,
        temp + count, temp_limit, expr->args, emitter) /*@ where policy = policy, cg = cg, p = p, f = f, args = cm_call_args(e), slots = cm_function_params(cm_function_at(policy, cm_rep_expr_value(e), cm_program_functions(p))), body = body, next = next, functions_ptr = functions_ptr, done = done, tail = app(cm_emit_args_reload(policy, p, fid, temp, cm_call_args(e)), cons(TVMInst(TVMCallOp, cm_function_pc(policy, p, cm_rep_expr_value(e))), tail)), out = out, capacity = capacity */;
    cm_emit_args_reload_plan(fn, temp, temp_limit,
        expr->args, emitter) /*@ where policy = policy, p = p, f = f, fid = fid, args = cm_call_args(e), body = body, next = next, done = app(done, cm_emit_args_store(policy, p, fid, pc, temp, temp + count, cm_call_args(e))), tail = cons(TVMInst(TVMCallOp, cm_function_pc(policy, p, cm_rep_expr_value(e))), tail), out = out, capacity = capacity */;
    cm_emit_call_plan(emitter, expr->value) /*@ where policy = policy, p = p, done = app(app(done, cm_emit_args_store(policy, p, fid, pc, temp, temp + count, cm_call_args(e))), cm_emit_args_reload(policy, p, fid, temp, cm_call_args(e))), tail = tail, out = out, capacity = capacity */;
 /*@ exists (xargs : Z), cm_rep_expr_kind(e) == 8 && expr != 0 && data_at(&(expr->kind), int, cm_rep_expr_kind(e)) * data_at(&(expr->op), int, cm_rep_expr_op(e)) * data_at(&(expr->ty), int, cm_type_encode(cm_expr_type(e))) * data_at(&(expr->value), long long, cm_rep_expr_value(e)) * data_at(&(expr->a), struct cm_expr *, 0) * data_at(&(expr->b), struct cm_expr *, 0) * data_at(&(expr->args), struct cm_arg *, xargs) * cm_arg_list_rep(xargs, cm_call_args(e))
 which implies cm_expr_rep(expr, e) */

 

  } else {
  }

 
}
