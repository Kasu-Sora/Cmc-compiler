#include "cmc_layout_migration_abi.h"
struct cm_emitter { struct cm_output *output; int pc; };

/*@ Extern Coq
 (cm_type :: *)
 (cm_expr :: *)
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
 (cm_expr_rep : Z -> cm_expr -> Assertion)
 (cm_resolved_emitter_plan_rep : cm_lookup_policy -> cm_program -> Z -> Z -> Z -> list tvm_inst -> list tvm_inst -> Assertion)
 (cm_wf_program : cm_lookup_policy -> cm_codegen_obligations -> cm_program -> Prop)
 (cm_expr_wf : cm_lookup_policy -> cm_program -> cm_function_d -> cm_expr -> Prop)
 (cm_expr_counts_representable : cm_lookup_policy -> cm_program -> Z -> cm_expr -> Prop)
 (cm_function_params : cm_function_d -> list cm_slot_d)
 (cm_function_locals : cm_function_d -> list cm_slot_d)
 (cm_slots_wf : list cm_struct_d -> list cm_slot_d -> Prop)
 (cm_rep_members_safe : list cm_slot_d -> Prop)
 (TVMInst : tvm_opcode -> Z -> tvm_inst)
 (cm_temp_offset : cm_lookup_policy -> cm_program -> Z -> Z -> Z)
 (cm_rvalue_code_count : cm_lookup_policy -> cm_program -> Z -> cm_expr -> Z)
 (cm_i32_code_count : Z -> Prop)
 (cm_expr_code_for : cm_lookup_policy -> cm_program -> Z -> Z -> Z -> cm_expr -> Z -> list tvm_inst)
 (cm_expr_temps_for : cm_expr -> Z -> Z)
 (cm_type_code_wf : cm_type -> Prop)
 (cm_binding_valid : cm_program -> cm_function_d -> Z -> Z -> Prop)
 (tvm_opcode_code : tvm_opcode -> Z)
 (cm_char_normalize_code : cm_type -> list tvm_inst)
 (cm_store_code : cm_type -> list tvm_inst)
 (cm_function_ret : cm_function_d -> cm_type)
 (cm_slot_list_rep : Z -> list cm_slot_d -> Assertion)
 (cm_stmt_rep : Z -> cm_stmt -> Assertion)
 (cm_stmt_wf : cm_lookup_policy -> cm_program -> cm_function_d -> bool -> cm_stmt -> Prop)
 (cm_stmt_counts_representable : cm_lookup_policy -> cm_program -> Z -> cm_stmt -> Prop)
 (cm_stmt_code_count : cm_lookup_policy -> cm_program -> Z -> cm_stmt -> Z)
 (TVMJzOp : tvm_opcode)
 (TVMJmpOp : tvm_opcode)
*/
/*@ Import Coq Require Import SimpleC.EE.QCP_demos_human.cmc_emit_function_migration_lib */

/*@ Extern Coq
 (cm_emit_stmt : cm_lookup_policy -> cm_program -> Z -> Z -> Z -> Z -> Z -> cm_stmt -> list tvm_inst)
 (cm_stmt_expr : cm_stmt -> cm_expr)
 (cm_stmt_first : cm_stmt -> cm_stmt)
 (cm_stmt_second : cm_stmt -> cm_stmt)
 (cm_stemps : cm_stmt -> Z)
 (cm_stmt_payload : cm_stmt -> Z -> Z -> Z -> Assertion)
 (cm_rep_stmt_kind : cm_stmt -> Z)
 (cm_rep_stmt_slot : cm_stmt -> Z)
 (CMSkipS : cm_stmt)
 (CMExprS : cm_expr -> cm_stmt)
 (CMDeclS : Z -> cm_stmt)
 (CMInitS : Z -> cm_expr -> cm_stmt)
 (CMSeqS : cm_stmt -> cm_stmt -> cm_stmt)
 (CMBlockS : cm_stmt -> cm_stmt)
 (CMIfS : cm_expr -> cm_stmt -> cm_stmt -> cm_stmt)
 (CMWhileS : cm_expr -> cm_stmt -> cm_stmt)
 (CMBreakS : cm_stmt)
 (CMContinueS : cm_stmt)
 (CMReturnS : cm_expr -> cm_stmt)
 (true : bool)
 (cm_binding_address_code : cm_lookup_policy -> cm_program -> Z -> Z -> Z -> list tvm_inst)
 (cm_slot_at : Z -> list cm_slot_d -> cm_slot_d)
 (cm_slot_ty : cm_slot_d -> cm_type)
 (cm_rep_slot_type : list cm_slot_d -> Z -> Z)
 (cm_return_epilogue : list tvm_inst)
 (TVMPopOp : tvm_opcode)
*/
/*@ Extern Coq
 (cm_function_body : cm_function_d -> cm_stmt)
 (cm_function_pc : cm_lookup_policy -> cm_program -> Z -> Z)
 (cm_function_prologue_count : cm_function_d -> Z)
 (cm_param_counts_representable : list cm_slot_d -> Prop)
 (cm_rep_stmt_temps_safe : cm_stmt -> Prop)
 (cm_rep_members_size : list cm_slot_d -> Z)
 (cm_slots_size : list cm_struct_d -> list cm_slot_d -> Z)
 (cm_slot_size : list cm_struct_d -> cm_slot_d -> Z)
 (cm_frame_size : list cm_struct_d -> cm_function_d -> Z)
 (cm_rep_code_slot_size : Z -> Z -> Z)
 (cm_slot_count : cm_slot_d -> Z)
 (cm_emit_param_stores : cm_lookup_policy -> cm_program -> Z -> Z -> list cm_slot_d -> list tvm_inst)
 (cm_emit_prologue : cm_lookup_policy -> cm_program -> Z -> list tvm_inst)
 (cm_emit_function : cm_lookup_policy -> cm_program -> Z -> list tvm_inst)
 (cm_emit_params_head : list cm_slot_d -> cm_slot_d)
 (cm_emit_params_tail : list cm_slot_d -> list cm_slot_d)
 (cm_fp_relative_address_code : Z -> list tvm_inst)
 (false : bool)
 (TVMPushOp : tvm_opcode)
 (TVMLoadOp : tvm_opcode)
 (TVMDupOp : tvm_opcode)
 (TVMSubOp : tvm_opcode)
 (TVMStoreOp : tvm_opcode)
*/
long long cmc_code_slot_size(int code, int count)
/*@ Require emp
    Ensure __return == cm_rep_code_slot_size(code, count) && emp
*/;

long long cmc_frame_size(struct cm_function *fn)
/*@ With (params : list cm_slot_d) (zp : Z) (locals : list cm_slot_d) (zl : Z) (body : cm_stmt) (zb : Z)
    Require cm_rep_members_safe(params) && cm_rep_members_safe(locals) && cm_rep_stmt_temps_safe(body) && 8 + cm_rep_members_size(params) + cm_rep_members_size(locals) + 8 * cm_stemps(body) <= 2147483647 && data_at(&(fn->params), struct cm_slot *, zp) * cm_slot_list_rep(zp, params) * data_at(&(fn->locals), struct cm_slot *, zl) * cm_slot_list_rep(zl, locals) * data_at(&(fn->body), struct cm_stmt *, zb) * cm_stmt_rep(zb, body)
    Ensure cm_rep_members_safe(params) && cm_rep_members_safe(locals) && cm_rep_stmt_temps_safe(body) && 8 + cm_rep_members_size(params) + cm_rep_members_size(locals) + 8 * cm_stemps(body) <= 2147483647 && __return == 8 + cm_rep_members_size(params) + cm_rep_members_size(locals) + 8 * cm_stemps(body) && data_at(&(fn->params), struct cm_slot *, zp) * cm_slot_list_rep(zp, params) * data_at(&(fn->locals), struct cm_slot *, zl) * cm_slot_list_rep(zl, locals) * data_at(&(fn->body), struct cm_stmt *, zb) * cm_stmt_rep(zb, body)
*/;

int cmc_stmt_temps(struct cm_stmt *stmt)
/*@ With (s : cm_stmt)
    Require cm_rep_stmt_temps_safe(s) && cm_stmt_rep(stmt, s)
    Ensure cm_rep_stmt_temps_safe(s) && __return == cm_stemps(s) && 0 <= cm_stemps(s) && cm_stemps(s) <= 2147483647 && cm_stmt_rep(stmt, s)
*/;

int cmc_function_prologue_count(struct cm_function *fn)
/*@ With (f : cm_function_d) (body : Z) (next : Z)
    Require cm_param_counts_representable(cm_function_params(f)) && cm_i32_code_count(cm_function_prologue_count(f)) && cm_function_context_rep(fn, f, body, next)
    Ensure cm_param_counts_representable(cm_function_params(f)) && cm_i32_code_count(cm_function_prologue_count(f)) && __return == cm_function_prologue_count(f) && cm_i32_code_count(__return) && cm_function_context_rep(fn, f, body, next)
*/;

void cm_emit_fp_address_plan(struct cm_emitter *emitter,
                             long long offset)
/*@ With (policy : cm_lookup_policy) (p : cm_program) (done : list tvm_inst) (tail : list tvm_inst) (out : Z) (capacity : Z)
    Require cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_fp_relative_address_code(offset), tail))
    Ensure cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cm_fp_relative_address_code(offset)), tail)
*/;

void cm_emit_plan(struct cm_emitter *emitter, int op,
                  long long immediate)
/*@ With (policy : cm_lookup_policy) (p : cm_program) (done : list tvm_inst) (tail : list tvm_inst) (out : Z) (capacity : Z) (opcode : tvm_opcode)
    Require op == tvm_opcode_code(opcode) && tvm_opcode_code(opcode) != 22 && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, cons(TVMInst(opcode, immediate), tail))
    Ensure cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cons(TVMInst(opcode, immediate), nil)), tail)
*/;

void cm_emit_normalize_plan(struct cm_emitter *emitter, int ty)
/*@ With (policy : cm_lookup_policy) (p : cm_program) (done : list tvm_inst) (tail : list tvm_inst) (out : Z) (capacity : Z) (model_ty : cm_type)
    Require ty == cm_type_encode(model_ty) && cm_type_code_wf(model_ty) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_char_normalize_code(model_ty), tail))
    Ensure cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cm_char_normalize_code(model_ty)), tail)
*/;

void cm_emit_store_plan(struct cm_emitter *emitter, int ty)
/*@ With (policy : cm_lookup_policy) (p : cm_program) (done : list tvm_inst) (tail : list tvm_inst) (out : Z) (capacity : Z) (model_ty : cm_type)
    Require ty == cm_type_encode(model_ty) && cm_type_code_wf(model_ty) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_store_code(model_ty), tail))
    Ensure cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cm_store_code(model_ty)), tail)
*/;

void cmc_emit_stmt(struct cm_program *program, int fid,
                  struct cm_function *fn, int pc, int temp,
                  int temp_limit, int break_pc, int continue_pc,
                  struct cm_stmt *stmt, struct cm_emitter *emitter)
/*@ With (policy : cm_lookup_policy) (cg : cm_codegen_obligations) (p : cm_program) (f : cm_function_d) (s : cm_stmt) (loop_ : bool) (body : Z) (next : Z) (functions_ptr : Z) (done : list tvm_inst) (tail : list tvm_inst) (out : Z) (capacity : Z)
 Require cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) && f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_stmt_wf(policy, p, f, loop_, s) && cm_stmt_counts_representable(policy, p, fid, s) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 0 <= temp && temp <= temp_limit && temp + cm_stemps(s) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) && cm_i32_code_count(break_pc) && cm_i32_code_count(continue_pc) &&
 cm_i32_code_count(pc + Zlength(cm_emit_stmt(policy, p, fid, pc, temp, break_pc, continue_pc, s))) && cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body, next) * cm_stmt_rep(stmt, s) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_emit_stmt(policy, p, fid, pc, temp, break_pc, continue_pc, s), tail))
 Ensure cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) && f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_stmt_wf(policy, p, f, loop_, s) && cm_stmt_counts_representable(policy, p, fid, s) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 0 <= temp && temp <= temp_limit && temp + cm_stemps(s) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) && cm_i32_code_count(break_pc) && cm_i32_code_count(continue_pc) &&
 cm_i32_code_count(pc + Zlength(cm_emit_stmt(policy, p, fid, pc, temp, break_pc, continue_pc, s))) && cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body, next) * cm_stmt_rep(stmt, s) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cm_emit_stmt(policy, p, fid, pc, temp, break_pc, continue_pc, s)), tail)
*/;

void cm_emit_return_epilogue_plan(struct cm_emitter *emitter)
/*@ With (policy : cm_lookup_policy) (p : cm_program) (done : list tvm_inst) (tail : list tvm_inst) (out : Z) (capacity : Z)
    Require cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_return_epilogue, tail))
    Ensure cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cm_return_epilogue), tail)
*/;

static void cmc_emit_param_stores_from(
    struct cm_slot *param, int slot, long long offset,
    struct cm_emitter *emitter)
/*@ With (policy : cm_lookup_policy) (p : cm_program) (f : cm_function_d) (fid : Z) (structs : list cm_struct_d) (full : list cm_slot_d) (prefix : list cm_slot_d) (params : list cm_slot_d) (done : list tvm_inst) (tail : list tvm_inst) (out : Z) (capacity : Z)
 Require structs == cm_program_structs(p) && f == cm_function_at(policy, fid, cm_program_functions(p)) && full == cm_function_params(f) && full == app(prefix, params) && slot == Zlength(prefix) && offset == 8 + cm_slots_size(structs, prefix) && 0 <= slot && slot + Zlength(params) <= 2147483647 && 0 <= offset && offset + cm_slots_size(structs, params) <= 1048584 && cm_slots_wf(structs, params) && cm_rep_members_safe(params) && cm_param_counts_representable(params) && cm_slot_list_rep(param, params) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_emit_param_stores(policy, p, fid, slot, params), tail))
 Ensure structs == cm_program_structs(p) && f == cm_function_at(policy, fid, cm_program_functions(p)) && full == cm_function_params(f) && full == app(prefix, params) && slot == Zlength(prefix) && offset == 8 + cm_slots_size(structs, prefix) && 0 <= slot && slot + Zlength(params) <= 2147483647 && 0 <= offset && offset + cm_slots_size(structs, params) <= 1048584 && cm_slots_wf(structs, params) && cm_rep_members_safe(params) && cm_param_counts_representable(params) && cm_slot_list_rep(param, params) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cm_emit_param_stores(policy, p, fid, slot, params)), tail)
*/
{
  if (param == 0) {
    return;
  } else {
  /*@ param != 0 && cm_slot_list_rep(param, params)
      which implies exists (np : Z), params == cons(cm_emit_params_head(params), cm_emit_params_tail(params)) && param != 0 && data_at(&(param->ty), int, cm_type_encode(cm_slot_ty(cm_emit_params_head(params)))) * data_at(&(param->count), int, cm_slot_count(cm_emit_params_head(params))) * data_at(&(param->next), struct cm_slot *, np) * cm_slot_list_rep(np, cm_emit_params_tail(params)) */
  }
  long long member_size = cmc_code_slot_size(param->ty, param->count);
  /*@ params == cons(cm_emit_params_head(params), cm_emit_params_tail(params)) && cm_slots_wf(structs, params) && member_size == cm_rep_code_slot_size(cm_type_encode(cm_slot_ty(cm_emit_params_head(params))), cm_slot_count(cm_emit_params_head(params))) && emp
      which implies params == cons(cm_emit_params_head(params), cm_emit_params_tail(params)) && cm_slots_wf(structs, params) && data_at(&member_size, long long, cm_slot_size(structs, cm_emit_params_head(params))) */
  struct cm_slot *next = param->next;
  /*@ structs == cm_program_structs(p) && f == cm_function_at(policy, fid, cm_program_functions(p)) && full == cm_function_params(f) && full == app(prefix, params) && slot == Zlength(prefix) && offset == 8 + cm_slots_size(structs, prefix) && 0 <= slot && slot + Zlength(params) <= 2147483647 && 0 <= offset && offset + cm_slots_size(structs, params) <= 1048584 && cm_slots_wf(structs, params) && cm_rep_members_safe(params) && cm_param_counts_representable(params) && params == cons(cm_emit_params_head(params), cm_emit_params_tail(params)) && member_size == cm_slot_size(structs, cm_emit_params_head(params)) && emp
      which implies structs == cm_program_structs(p) && f == cm_function_at(policy, fid, cm_program_functions(p)) && full == cm_function_params(f) && full == app(prefix, params) && slot == Zlength(prefix) && offset == 8 + cm_slots_size(structs, prefix) && 0 <= slot && slot + Zlength(params) <= 2147483647 && 0 <= offset && offset + cm_slots_size(structs, params) <= 1048584 && cm_slots_wf(structs, params) && cm_rep_members_safe(params) && cm_param_counts_representable(params) && params == cons(cm_emit_params_head(params), cm_emit_params_tail(params)) && member_size == cm_slot_size(structs, cm_emit_params_head(params)) && full == app(app(prefix, cons(cm_emit_params_head(params), nil)), cm_emit_params_tail(params)) && slot + 1 == Zlength(app(prefix, cons(cm_emit_params_head(params), nil))) && offset + member_size == 8 + cm_slots_size(structs, app(prefix, cons(cm_emit_params_head(params), nil))) && 0 <= slot + 1 && slot + 1 <= 2147483647 && slot + 1 + Zlength(cm_emit_params_tail(params)) <= 2147483647 && 0 <= offset + member_size && offset + member_size <= 1048584 && offset + member_size + cm_slots_size(structs, cm_emit_params_tail(params)) <= 1048584 && cm_slots_wf(structs, cm_emit_params_tail(params)) && cm_rep_members_safe(cm_emit_params_tail(params)) && cm_param_counts_representable(cm_emit_params_tail(params)) && cm_type_code_wf(cm_slot_ty(cm_emit_params_head(params))) && emp */
  /*@ slot == slot@pre && offset == offset@pre && structs == cm_program_structs(p) && f == cm_function_at(policy, fid, cm_program_functions(p)) && full == cm_function_params(f) && full == app(prefix, params) && slot == Zlength(prefix) && offset == 8 + cm_slots_size(structs, prefix) && 0 <= slot && slot + Zlength(params) <= 2147483647 && 0 <= offset && offset + cm_slots_size(structs, params) <= 1048584 && cm_slots_wf(structs, params) && cm_rep_members_safe(params) && cm_param_counts_representable(params) && params == cons(cm_emit_params_head(params), cm_emit_params_tail(params)) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_emit_param_stores(policy, p, fid, slot, params), tail))
      which implies slot == slot@pre && offset == offset@pre && structs == cm_program_structs(p) && f == cm_function_at(policy, fid, cm_program_functions(p)) && full == cm_function_params(f) && full == app(prefix, params) && slot == Zlength(prefix) && offset == 8 + cm_slots_size(structs, prefix) && 0 <= slot && slot + Zlength(params) <= 2147483647 && 0 <= offset && offset + cm_slots_size(structs, params) <= 1048584 && cm_slots_wf(structs, params) && cm_rep_members_safe(params) && cm_param_counts_representable(params) && params == cons(cm_emit_params_head(params), cm_emit_params_tail(params)) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_emit_param_stores(policy, p, fid, slot + 1, cm_emit_params_tail(params)), app(cm_char_normalize_code(cm_slot_ty(cm_emit_params_head(params))), app(cm_fp_relative_address_code(offset), app(cm_store_code(cm_slot_ty(cm_emit_params_head(params))), tail))))) */
  cmc_emit_param_stores_from(next, slot + 1,
                             offset + member_size, emitter) /*@ where policy = policy, p = p, f = f, fid = fid, structs = structs, full = full, prefix = app(prefix, cons(cm_emit_params_head(params), nil)), params = cm_emit_params_tail(params), done = done, tail = app(cm_char_normalize_code(cm_slot_ty(cm_emit_params_head(params))), app(cm_fp_relative_address_code(offset), app(cm_store_code(cm_slot_ty(cm_emit_params_head(params))), tail))), out = out, capacity = capacity */;
  cm_emit_normalize_plan(emitter, param->ty) /*@ where policy = policy, p = p, model_ty = cm_slot_ty(cm_emit_params_head(params)), done = app(done, cm_emit_param_stores(policy, p, fid, slot + 1, cm_emit_params_tail(params))), tail = app(cm_fp_relative_address_code(offset), app(cm_store_code(cm_slot_ty(cm_emit_params_head(params))), tail)), out = out, capacity = capacity */;
  cm_emit_fp_address_plan(emitter, offset) /*@ where policy = policy, p = p, done = app(app(done, cm_emit_param_stores(policy, p, fid, slot + 1, cm_emit_params_tail(params))), cm_char_normalize_code(cm_slot_ty(cm_emit_params_head(params)))), tail = app(cm_store_code(cm_slot_ty(cm_emit_params_head(params))), tail), out = out, capacity = capacity */;
  cm_emit_store_plan(emitter, param->ty) /*@ where policy = policy, p = p, model_ty = cm_slot_ty(cm_emit_params_head(params)), done = app(app(app(done, cm_emit_param_stores(policy, p, fid, slot + 1, cm_emit_params_tail(params))), cm_char_normalize_code(cm_slot_ty(cm_emit_params_head(params)))), cm_fp_relative_address_code(offset)), tail = tail, out = out, capacity = capacity */;
  /*@ slot == slot@pre && offset == offset@pre && structs == cm_program_structs(p) && f == cm_function_at(policy, fid, cm_program_functions(p)) && full == cm_function_params(f) && full == app(prefix, params) && slot == Zlength(prefix) && offset == 8 + cm_slots_size(structs, prefix) && 0 <= slot && slot + Zlength(params) <= 2147483647 && 0 <= offset && offset + cm_slots_size(structs, params) <= 1048584 && cm_slots_wf(structs, params) && cm_rep_members_safe(params) && cm_param_counts_representable(params) && params == cons(cm_emit_params_head(params), cm_emit_params_tail(params)) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(app(app(app(done, cm_emit_param_stores(policy, p, fid, slot + 1, cm_emit_params_tail(params))), cm_char_normalize_code(cm_slot_ty(cm_emit_params_head(params)))), cm_fp_relative_address_code(offset)), cm_store_code(cm_slot_ty(cm_emit_params_head(params)))), tail)
      which implies slot == slot@pre && offset == offset@pre && structs == cm_program_structs(p) && f == cm_function_at(policy, fid, cm_program_functions(p)) && full == cm_function_params(f) && full == app(prefix, params) && slot == Zlength(prefix) && offset == 8 + cm_slots_size(structs, prefix) && 0 <= slot && slot + Zlength(params) <= 2147483647 && 0 <= offset && offset + cm_slots_size(structs, params) <= 1048584 && cm_slots_wf(structs, params) && cm_rep_members_safe(params) && cm_param_counts_representable(params) && params == cons(cm_emit_params_head(params), cm_emit_params_tail(params)) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cm_emit_param_stores(policy, p, fid, slot, params)), tail) */
  /*@ exists (np : Z), params == cons(cm_emit_params_head(params), cm_emit_params_tail(params)) && param != 0 && data_at(&(param->ty), int, cm_type_encode(cm_slot_ty(cm_emit_params_head(params)))) * data_at(&(param->count), int, cm_slot_count(cm_emit_params_head(params))) * data_at(&(param->next), struct cm_slot *, np) * cm_slot_list_rep(np, cm_emit_params_tail(params))
      which implies cm_slot_list_rep(param, params) */
}

static void cmc_emit_prologue(
    struct cm_function *fn, int fid, struct cm_emitter *emitter)
/*@ With (policy : cm_lookup_policy) (p : cm_program) (f : cm_function_d) (s : cm_stmt) (body : Z) (next : Z) (structs : list cm_struct_d) (done : list tvm_inst) (tail : list tvm_inst) (out : Z) (capacity : Z)
 Require f == cm_function_at(policy, fid, cm_program_functions(p)) && structs == cm_program_structs(p) && s == cm_function_body(f) && cm_slots_wf(structs, cm_function_params(f)) && cm_slots_wf(structs, cm_function_locals(f)) && cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) && cm_rep_stmt_temps_safe(s) && 8 + cm_rep_members_size(cm_function_params(f)) + cm_rep_members_size(cm_function_locals(f)) + 8 * cm_stemps(s) <= 2147483647 && cm_param_counts_representable(cm_function_params(f)) && cm_function_context_rep(fn, f, body, next) * cm_stmt_rep(body, s) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_emit_prologue(policy, p, fid), tail))
 Ensure f == cm_function_at(policy, fid, cm_program_functions(p)) && structs == cm_program_structs(p) && s == cm_function_body(f) && cm_slots_wf(structs, cm_function_params(f)) && cm_slots_wf(structs, cm_function_locals(f)) && cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) && cm_rep_stmt_temps_safe(s) && 8 + cm_rep_members_size(cm_function_params(f)) + cm_rep_members_size(cm_function_locals(f)) + 8 * cm_stemps(s) <= 2147483647 && cm_param_counts_representable(cm_function_params(f)) && cm_function_context_rep(fn, f, body, next) * cm_stmt_rep(body, s) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cm_emit_prologue(policy, p, fid)), tail)
*/
{
  /*@ cm_function_context_rep(fn, f, body, next)
      which implies exists (zp : Z) (zl : Z), fn != 0 && data_at(&(fn->ret_ty), int, cm_type_encode(cm_function_ret(f))) * data_at(&(fn->params), struct cm_slot *, zp) * data_at(&(fn->locals), struct cm_slot *, zl) * data_at(&(fn->body), struct cm_stmt *, body) * data_at(&(fn->next), struct cm_function *, next) * cm_slot_list_rep(zp, cm_function_params(f)) * cm_slot_list_rep(zl, cm_function_locals(f)) */
  long long frame_size = cmc_frame_size(fn) /*@ where params = cm_function_params(f), locals = cm_function_locals(f), body = s */;
  /*@ f == cm_function_at(policy, fid, cm_program_functions(p)) && structs == cm_program_structs(p) && s == cm_function_body(f) && cm_slots_wf(structs, cm_function_params(f)) && cm_slots_wf(structs, cm_function_locals(f)) && cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) && cm_rep_stmt_temps_safe(s) && 8 + cm_rep_members_size(cm_function_params(f)) + cm_rep_members_size(cm_function_locals(f)) + 8 * cm_stemps(s) <= 2147483647 && cm_param_counts_representable(cm_function_params(f)) && frame_size == 8 + cm_rep_members_size(cm_function_params(f)) + cm_rep_members_size(cm_function_locals(f)) + 8 * cm_stemps(s) && emp
      which implies f == cm_function_at(policy, fid, cm_program_functions(p)) && structs == cm_program_structs(p) && s == cm_function_body(f) && cm_slots_wf(structs, cm_function_params(f)) && cm_slots_wf(structs, cm_function_locals(f)) && cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) && cm_rep_stmt_temps_safe(s) && 8 + cm_rep_members_size(cm_function_params(f)) + cm_rep_members_size(cm_function_locals(f)) + 8 * cm_stemps(s) <= 2147483647 && cm_param_counts_representable(cm_function_params(f)) && data_at(&frame_size, long long, cm_frame_size(cm_program_structs(p), f)) */
  /*@ fid == fid@pre && f == cm_function_at(policy, fid, cm_program_functions(p)) && structs == cm_program_structs(p) && s == cm_function_body(f) && cm_slots_wf(structs, cm_function_params(f)) && cm_slots_wf(structs, cm_function_locals(f)) && cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) && cm_rep_stmt_temps_safe(s) && 8 + cm_rep_members_size(cm_function_params(f)) + cm_rep_members_size(cm_function_locals(f)) + 8 * cm_stemps(s) <= 2147483647 && cm_param_counts_representable(cm_function_params(f)) && frame_size == cm_frame_size(cm_program_structs(p), f) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_emit_prologue(policy, p, fid), tail))
      which implies fid == fid@pre && f == cm_function_at(policy, fid, cm_program_functions(p)) && structs == cm_program_structs(p) && s == cm_function_body(f) && cm_slots_wf(structs, cm_function_params(f)) && cm_slots_wf(structs, cm_function_locals(f)) && cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) && cm_rep_stmt_temps_safe(s) && 8 + cm_rep_members_size(cm_function_params(f)) + cm_rep_members_size(cm_function_locals(f)) + 8 * cm_stemps(s) <= 2147483647 && cm_param_counts_representable(cm_function_params(f)) && frame_size == cm_frame_size(cm_program_structs(p), f) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, cons(TVMInst(TVMPushOp, 8), cons(TVMInst(TVMLoadOp, 0), cons(TVMInst(TVMDupOp, 0), cons(TVMInst(TVMPushOp, frame_size), cons(TVMInst(TVMSubOp, 0), cons(TVMInst(TVMStoreOp, 0), cons(TVMInst(TVMPushOp, 8), cons(TVMInst(TVMLoadOp, 0), cons(TVMInst(TVMPushOp, frame_size), cons(TVMInst(TVMSubOp, 0), cons(TVMInst(TVMDupOp, 0), cons(TVMInst(TVMPushOp, 8), cons(TVMInst(TVMStoreOp, 0), cons(TVMInst(TVMPopOp, 0), app(cm_emit_param_stores(policy, p, fid, 0, cm_function_params(f)), tail)))))))))))))))) */
  cm_emit_plan(emitter, CMC_OP_PUSH, 8) /*@ where policy = policy, p = p, opcode = TVMPushOp, done = done, tail = cons(TVMInst(TVMLoadOp, 0), cons(TVMInst(TVMDupOp, 0), cons(TVMInst(TVMPushOp, frame_size), cons(TVMInst(TVMSubOp, 0), cons(TVMInst(TVMStoreOp, 0), cons(TVMInst(TVMPushOp, 8), cons(TVMInst(TVMLoadOp, 0), cons(TVMInst(TVMPushOp, frame_size), cons(TVMInst(TVMSubOp, 0), cons(TVMInst(TVMDupOp, 0), cons(TVMInst(TVMPushOp, 8), cons(TVMInst(TVMStoreOp, 0), cons(TVMInst(TVMPopOp, 0), app(cm_emit_param_stores(policy, p, fid, 0, cm_function_params(f)), tail)))))))))))))), out = out, capacity = capacity */;
  cm_emit_plan(emitter, CMC_OP_LOAD, 0) /*@ where policy = policy, p = p, opcode = TVMLoadOp, done = app(done, cons(TVMInst(TVMPushOp, 8), nil)), tail = cons(TVMInst(TVMDupOp, 0), cons(TVMInst(TVMPushOp, frame_size), cons(TVMInst(TVMSubOp, 0), cons(TVMInst(TVMStoreOp, 0), cons(TVMInst(TVMPushOp, 8), cons(TVMInst(TVMLoadOp, 0), cons(TVMInst(TVMPushOp, frame_size), cons(TVMInst(TVMSubOp, 0), cons(TVMInst(TVMDupOp, 0), cons(TVMInst(TVMPushOp, 8), cons(TVMInst(TVMStoreOp, 0), cons(TVMInst(TVMPopOp, 0), app(cm_emit_param_stores(policy, p, fid, 0, cm_function_params(f)), tail))))))))))))), out = out, capacity = capacity */;
  cm_emit_plan(emitter, CMC_OP_DUP, 0) /*@ where policy = policy, p = p, opcode = TVMDupOp, done = app(app(done, cons(TVMInst(TVMPushOp, 8), nil)), cons(TVMInst(TVMLoadOp, 0), nil)), tail = cons(TVMInst(TVMPushOp, frame_size), cons(TVMInst(TVMSubOp, 0), cons(TVMInst(TVMStoreOp, 0), cons(TVMInst(TVMPushOp, 8), cons(TVMInst(TVMLoadOp, 0), cons(TVMInst(TVMPushOp, frame_size), cons(TVMInst(TVMSubOp, 0), cons(TVMInst(TVMDupOp, 0), cons(TVMInst(TVMPushOp, 8), cons(TVMInst(TVMStoreOp, 0), cons(TVMInst(TVMPopOp, 0), app(cm_emit_param_stores(policy, p, fid, 0, cm_function_params(f)), tail)))))))))))), out = out, capacity = capacity */;
  cm_emit_plan(emitter, CMC_OP_PUSH, frame_size) /*@ where policy = policy, p = p, opcode = TVMPushOp, done = app(app(app(done, cons(TVMInst(TVMPushOp, 8), nil)), cons(TVMInst(TVMLoadOp, 0), nil)), cons(TVMInst(TVMDupOp, 0), nil)), tail = cons(TVMInst(TVMSubOp, 0), cons(TVMInst(TVMStoreOp, 0), cons(TVMInst(TVMPushOp, 8), cons(TVMInst(TVMLoadOp, 0), cons(TVMInst(TVMPushOp, frame_size), cons(TVMInst(TVMSubOp, 0), cons(TVMInst(TVMDupOp, 0), cons(TVMInst(TVMPushOp, 8), cons(TVMInst(TVMStoreOp, 0), cons(TVMInst(TVMPopOp, 0), app(cm_emit_param_stores(policy, p, fid, 0, cm_function_params(f)), tail))))))))))), out = out, capacity = capacity */;
  cm_emit_plan(emitter, CMC_OP_SUB, 0) /*@ where policy = policy, p = p, opcode = TVMSubOp, done = app(app(app(app(done, cons(TVMInst(TVMPushOp, 8), nil)), cons(TVMInst(TVMLoadOp, 0), nil)), cons(TVMInst(TVMDupOp, 0), nil)), cons(TVMInst(TVMPushOp, frame_size), nil)), tail = cons(TVMInst(TVMStoreOp, 0), cons(TVMInst(TVMPushOp, 8), cons(TVMInst(TVMLoadOp, 0), cons(TVMInst(TVMPushOp, frame_size), cons(TVMInst(TVMSubOp, 0), cons(TVMInst(TVMDupOp, 0), cons(TVMInst(TVMPushOp, 8), cons(TVMInst(TVMStoreOp, 0), cons(TVMInst(TVMPopOp, 0), app(cm_emit_param_stores(policy, p, fid, 0, cm_function_params(f)), tail)))))))))), out = out, capacity = capacity */;
  cm_emit_plan(emitter, CMC_OP_STORE, 0) /*@ where policy = policy, p = p, opcode = TVMStoreOp, done = app(app(app(app(app(done, cons(TVMInst(TVMPushOp, 8), nil)), cons(TVMInst(TVMLoadOp, 0), nil)), cons(TVMInst(TVMDupOp, 0), nil)), cons(TVMInst(TVMPushOp, frame_size), nil)), cons(TVMInst(TVMSubOp, 0), nil)), tail = cons(TVMInst(TVMPushOp, 8), cons(TVMInst(TVMLoadOp, 0), cons(TVMInst(TVMPushOp, frame_size), cons(TVMInst(TVMSubOp, 0), cons(TVMInst(TVMDupOp, 0), cons(TVMInst(TVMPushOp, 8), cons(TVMInst(TVMStoreOp, 0), cons(TVMInst(TVMPopOp, 0), app(cm_emit_param_stores(policy, p, fid, 0, cm_function_params(f)), tail))))))))), out = out, capacity = capacity */;
  cm_emit_plan(emitter, CMC_OP_PUSH, 8) /*@ where policy = policy, p = p, opcode = TVMPushOp, done = app(app(app(app(app(app(done, cons(TVMInst(TVMPushOp, 8), nil)), cons(TVMInst(TVMLoadOp, 0), nil)), cons(TVMInst(TVMDupOp, 0), nil)), cons(TVMInst(TVMPushOp, frame_size), nil)), cons(TVMInst(TVMSubOp, 0), nil)), cons(TVMInst(TVMStoreOp, 0), nil)), tail = cons(TVMInst(TVMLoadOp, 0), cons(TVMInst(TVMPushOp, frame_size), cons(TVMInst(TVMSubOp, 0), cons(TVMInst(TVMDupOp, 0), cons(TVMInst(TVMPushOp, 8), cons(TVMInst(TVMStoreOp, 0), cons(TVMInst(TVMPopOp, 0), app(cm_emit_param_stores(policy, p, fid, 0, cm_function_params(f)), tail)))))))), out = out, capacity = capacity */;
  cm_emit_plan(emitter, CMC_OP_LOAD, 0) /*@ where policy = policy, p = p, opcode = TVMLoadOp, done = app(app(app(app(app(app(app(done, cons(TVMInst(TVMPushOp, 8), nil)), cons(TVMInst(TVMLoadOp, 0), nil)), cons(TVMInst(TVMDupOp, 0), nil)), cons(TVMInst(TVMPushOp, frame_size), nil)), cons(TVMInst(TVMSubOp, 0), nil)), cons(TVMInst(TVMStoreOp, 0), nil)), cons(TVMInst(TVMPushOp, 8), nil)), tail = cons(TVMInst(TVMPushOp, frame_size), cons(TVMInst(TVMSubOp, 0), cons(TVMInst(TVMDupOp, 0), cons(TVMInst(TVMPushOp, 8), cons(TVMInst(TVMStoreOp, 0), cons(TVMInst(TVMPopOp, 0), app(cm_emit_param_stores(policy, p, fid, 0, cm_function_params(f)), tail))))))), out = out, capacity = capacity */;
  cm_emit_plan(emitter, CMC_OP_PUSH, frame_size) /*@ where policy = policy, p = p, opcode = TVMPushOp, done = app(app(app(app(app(app(app(app(done, cons(TVMInst(TVMPushOp, 8), nil)), cons(TVMInst(TVMLoadOp, 0), nil)), cons(TVMInst(TVMDupOp, 0), nil)), cons(TVMInst(TVMPushOp, frame_size), nil)), cons(TVMInst(TVMSubOp, 0), nil)), cons(TVMInst(TVMStoreOp, 0), nil)), cons(TVMInst(TVMPushOp, 8), nil)), cons(TVMInst(TVMLoadOp, 0), nil)), tail = cons(TVMInst(TVMSubOp, 0), cons(TVMInst(TVMDupOp, 0), cons(TVMInst(TVMPushOp, 8), cons(TVMInst(TVMStoreOp, 0), cons(TVMInst(TVMPopOp, 0), app(cm_emit_param_stores(policy, p, fid, 0, cm_function_params(f)), tail)))))), out = out, capacity = capacity */;
  cm_emit_plan(emitter, CMC_OP_SUB, 0) /*@ where policy = policy, p = p, opcode = TVMSubOp, done = app(app(app(app(app(app(app(app(app(done, cons(TVMInst(TVMPushOp, 8), nil)), cons(TVMInst(TVMLoadOp, 0), nil)), cons(TVMInst(TVMDupOp, 0), nil)), cons(TVMInst(TVMPushOp, frame_size), nil)), cons(TVMInst(TVMSubOp, 0), nil)), cons(TVMInst(TVMStoreOp, 0), nil)), cons(TVMInst(TVMPushOp, 8), nil)), cons(TVMInst(TVMLoadOp, 0), nil)), cons(TVMInst(TVMPushOp, frame_size), nil)), tail = cons(TVMInst(TVMDupOp, 0), cons(TVMInst(TVMPushOp, 8), cons(TVMInst(TVMStoreOp, 0), cons(TVMInst(TVMPopOp, 0), app(cm_emit_param_stores(policy, p, fid, 0, cm_function_params(f)), tail))))), out = out, capacity = capacity */;
  cm_emit_plan(emitter, CMC_OP_DUP, 0) /*@ where policy = policy, p = p, opcode = TVMDupOp, done = app(app(app(app(app(app(app(app(app(app(done, cons(TVMInst(TVMPushOp, 8), nil)), cons(TVMInst(TVMLoadOp, 0), nil)), cons(TVMInst(TVMDupOp, 0), nil)), cons(TVMInst(TVMPushOp, frame_size), nil)), cons(TVMInst(TVMSubOp, 0), nil)), cons(TVMInst(TVMStoreOp, 0), nil)), cons(TVMInst(TVMPushOp, 8), nil)), cons(TVMInst(TVMLoadOp, 0), nil)), cons(TVMInst(TVMPushOp, frame_size), nil)), cons(TVMInst(TVMSubOp, 0), nil)), tail = cons(TVMInst(TVMPushOp, 8), cons(TVMInst(TVMStoreOp, 0), cons(TVMInst(TVMPopOp, 0), app(cm_emit_param_stores(policy, p, fid, 0, cm_function_params(f)), tail)))), out = out, capacity = capacity */;
  cm_emit_plan(emitter, CMC_OP_PUSH, 8) /*@ where policy = policy, p = p, opcode = TVMPushOp, done = app(app(app(app(app(app(app(app(app(app(app(done, cons(TVMInst(TVMPushOp, 8), nil)), cons(TVMInst(TVMLoadOp, 0), nil)), cons(TVMInst(TVMDupOp, 0), nil)), cons(TVMInst(TVMPushOp, frame_size), nil)), cons(TVMInst(TVMSubOp, 0), nil)), cons(TVMInst(TVMStoreOp, 0), nil)), cons(TVMInst(TVMPushOp, 8), nil)), cons(TVMInst(TVMLoadOp, 0), nil)), cons(TVMInst(TVMPushOp, frame_size), nil)), cons(TVMInst(TVMSubOp, 0), nil)), cons(TVMInst(TVMDupOp, 0), nil)), tail = cons(TVMInst(TVMStoreOp, 0), cons(TVMInst(TVMPopOp, 0), app(cm_emit_param_stores(policy, p, fid, 0, cm_function_params(f)), tail))), out = out, capacity = capacity */;
  cm_emit_plan(emitter, CMC_OP_STORE, 0) /*@ where policy = policy, p = p, opcode = TVMStoreOp, done = app(app(app(app(app(app(app(app(app(app(app(app(done, cons(TVMInst(TVMPushOp, 8), nil)), cons(TVMInst(TVMLoadOp, 0), nil)), cons(TVMInst(TVMDupOp, 0), nil)), cons(TVMInst(TVMPushOp, frame_size), nil)), cons(TVMInst(TVMSubOp, 0), nil)), cons(TVMInst(TVMStoreOp, 0), nil)), cons(TVMInst(TVMPushOp, 8), nil)), cons(TVMInst(TVMLoadOp, 0), nil)), cons(TVMInst(TVMPushOp, frame_size), nil)), cons(TVMInst(TVMSubOp, 0), nil)), cons(TVMInst(TVMDupOp, 0), nil)), cons(TVMInst(TVMPushOp, 8), nil)), tail = cons(TVMInst(TVMPopOp, 0), app(cm_emit_param_stores(policy, p, fid, 0, cm_function_params(f)), tail)), out = out, capacity = capacity */;
  cm_emit_plan(emitter, CMC_OP_POP, 0) /*@ where policy = policy, p = p, opcode = TVMPopOp, done = app(app(app(app(app(app(app(app(app(app(app(app(app(done, cons(TVMInst(TVMPushOp, 8), nil)), cons(TVMInst(TVMLoadOp, 0), nil)), cons(TVMInst(TVMDupOp, 0), nil)), cons(TVMInst(TVMPushOp, frame_size), nil)), cons(TVMInst(TVMSubOp, 0), nil)), cons(TVMInst(TVMStoreOp, 0), nil)), cons(TVMInst(TVMPushOp, 8), nil)), cons(TVMInst(TVMLoadOp, 0), nil)), cons(TVMInst(TVMPushOp, frame_size), nil)), cons(TVMInst(TVMSubOp, 0), nil)), cons(TVMInst(TVMDupOp, 0), nil)), cons(TVMInst(TVMPushOp, 8), nil)), cons(TVMInst(TVMStoreOp, 0), nil)), tail = app(cm_emit_param_stores(policy, p, fid, 0, cm_function_params(f)), tail), out = out, capacity = capacity */;
  /*@ f == cm_function_at(policy, fid, cm_program_functions(p)) && structs == cm_program_structs(p) && s == cm_function_body(f) && cm_slots_wf(structs, cm_function_params(f)) && cm_slots_wf(structs, cm_function_locals(f)) && cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) && cm_rep_stmt_temps_safe(s) && 8 + cm_rep_members_size(cm_function_params(f)) + cm_rep_members_size(cm_function_locals(f)) + 8 * cm_stemps(s) <= 2147483647 && cm_param_counts_representable(cm_function_params(f)) && emp
      which implies f == cm_function_at(policy, fid, cm_program_functions(p)) && structs == cm_program_structs(p) && s == cm_function_body(f) && cm_slots_wf(structs, cm_function_params(f)) && cm_slots_wf(structs, cm_function_locals(f)) && cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) && cm_rep_stmt_temps_safe(s) && 8 + cm_rep_members_size(cm_function_params(f)) + cm_rep_members_size(cm_function_locals(f)) + 8 * cm_stemps(s) <= 2147483647 && cm_param_counts_representable(cm_function_params(f)) && 0 + Zlength(cm_function_params(f)) <= 2147483647 && 8 + cm_slots_size(structs, cm_function_params(f)) <= 1048584 && emp */
  cmc_emit_param_stores_from(fn->params, 0, 8, emitter) /*@ where policy = policy, p = p, f = f, fid = fid, structs = structs, full = cm_function_params(f), prefix = sublist(0, 0, cm_function_params(f)), params = cm_function_params(f), done = app(app(app(app(app(app(app(app(app(app(app(app(app(app(done, cons(TVMInst(TVMPushOp, 8), nil)), cons(TVMInst(TVMLoadOp, 0), nil)), cons(TVMInst(TVMDupOp, 0), nil)), cons(TVMInst(TVMPushOp, frame_size), nil)), cons(TVMInst(TVMSubOp, 0), nil)), cons(TVMInst(TVMStoreOp, 0), nil)), cons(TVMInst(TVMPushOp, 8), nil)), cons(TVMInst(TVMLoadOp, 0), nil)), cons(TVMInst(TVMPushOp, frame_size), nil)), cons(TVMInst(TVMSubOp, 0), nil)), cons(TVMInst(TVMDupOp, 0), nil)), cons(TVMInst(TVMPushOp, 8), nil)), cons(TVMInst(TVMStoreOp, 0), nil)), cons(TVMInst(TVMPopOp, 0), nil)), tail = tail, out = out, capacity = capacity */;
  /*@ fid == fid@pre && f == cm_function_at(policy, fid, cm_program_functions(p)) && structs == cm_program_structs(p) && s == cm_function_body(f) && cm_slots_wf(structs, cm_function_params(f)) && cm_slots_wf(structs, cm_function_locals(f)) && cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) && cm_rep_stmt_temps_safe(s) && 8 + cm_rep_members_size(cm_function_params(f)) + cm_rep_members_size(cm_function_locals(f)) + 8 * cm_stemps(s) <= 2147483647 && cm_param_counts_representable(cm_function_params(f)) && frame_size == cm_frame_size(cm_program_structs(p), f) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(app(app(app(app(app(app(app(app(app(app(app(app(app(app(done, cons(TVMInst(TVMPushOp, 8), nil)), cons(TVMInst(TVMLoadOp, 0), nil)), cons(TVMInst(TVMDupOp, 0), nil)), cons(TVMInst(TVMPushOp, frame_size), nil)), cons(TVMInst(TVMSubOp, 0), nil)), cons(TVMInst(TVMStoreOp, 0), nil)), cons(TVMInst(TVMPushOp, 8), nil)), cons(TVMInst(TVMLoadOp, 0), nil)), cons(TVMInst(TVMPushOp, frame_size), nil)), cons(TVMInst(TVMSubOp, 0), nil)), cons(TVMInst(TVMDupOp, 0), nil)), cons(TVMInst(TVMPushOp, 8), nil)), cons(TVMInst(TVMStoreOp, 0), nil)), cons(TVMInst(TVMPopOp, 0), nil)), cm_emit_param_stores(policy, p, fid, 0, cm_function_params(f))), tail)
      which implies fid == fid@pre && f == cm_function_at(policy, fid, cm_program_functions(p)) && structs == cm_program_structs(p) && s == cm_function_body(f) && cm_slots_wf(structs, cm_function_params(f)) && cm_slots_wf(structs, cm_function_locals(f)) && cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) && cm_rep_stmt_temps_safe(s) && 8 + cm_rep_members_size(cm_function_params(f)) + cm_rep_members_size(cm_function_locals(f)) + 8 * cm_stemps(s) <= 2147483647 && cm_param_counts_representable(cm_function_params(f)) && frame_size == cm_frame_size(cm_program_structs(p), f) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cm_emit_prologue(policy, p, fid)), tail) */
  /*@ exists (zp : Z) (zl : Z), fn != 0 && data_at(&(fn->ret_ty), int, cm_type_encode(cm_function_ret(f))) * data_at(&(fn->params), struct cm_slot *, zp) * data_at(&(fn->locals), struct cm_slot *, zl) * data_at(&(fn->body), struct cm_stmt *, body) * data_at(&(fn->next), struct cm_function *, next) * cm_slot_list_rep(zp, cm_function_params(f)) * cm_slot_list_rep(zl, cm_function_locals(f))
      which implies cm_function_context_rep(fn, f, body, next) */
}

void cmc_emit_function(
    struct cm_program *program, struct cm_function *fn,
    int fid, int function_pc, struct cm_emitter *emitter)
/*@ With (policy : cm_lookup_policy) (p : cm_program) (f : cm_function_d) (cg : cm_codegen_obligations) (s : cm_stmt) (body : Z) (next : Z) (functions_ptr : Z) (done : list tvm_inst) (tail : list tvm_inst) (out : Z) (capacity : Z)
 Require cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) && f == cm_function_at(policy, fid, cm_program_functions(p)) && s == cm_function_body(f) && function_pc == cm_function_pc(policy, p, fid) && cm_stmt_wf(policy, p, f, false, s) && cm_stmt_counts_representable(policy, p, fid, s) && cm_param_counts_representable(cm_function_params(f)) && cm_i32_code_count(cm_function_prologue_count(f)) && cm_i32_code_count(function_pc) && cm_i32_code_count(cm_function_pc(policy, p, fid) + cm_function_prologue_count(f)) && cm_i32_code_count(cm_function_pc(policy, p, fid) + cm_function_prologue_count(f) + Zlength(cm_emit_stmt(policy, p, fid, cm_function_pc(policy, p, fid) + cm_function_prologue_count(f), 0, 0, 0, s))) && cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) && cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) && cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) && cm_rep_stmt_temps_safe(s) && cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 && 8 + cm_rep_members_size(cm_function_params(f)) + cm_rep_members_size(cm_function_locals(f)) + 8 * cm_stemps(s) <= 2147483647 && cm_temp_offset(policy, p, fid, cm_stemps(s)) <= 2147483647 && cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body, next) * cm_stmt_rep(body, s) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_emit_function(policy, p, fid), tail))
 Ensure cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) && f == cm_function_at(policy, fid, cm_program_functions(p)) && s == cm_function_body(f) && function_pc == cm_function_pc(policy, p, fid) && cm_stmt_wf(policy, p, f, false, s) && cm_stmt_counts_representable(policy, p, fid, s) && cm_param_counts_representable(cm_function_params(f)) && cm_i32_code_count(cm_function_prologue_count(f)) && cm_i32_code_count(function_pc) && cm_i32_code_count(cm_function_pc(policy, p, fid) + cm_function_prologue_count(f)) && cm_i32_code_count(cm_function_pc(policy, p, fid) + cm_function_prologue_count(f) + Zlength(cm_emit_stmt(policy, p, fid, cm_function_pc(policy, p, fid) + cm_function_prologue_count(f), 0, 0, 0, s))) && cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) && cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) && cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) && cm_rep_stmt_temps_safe(s) && cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 && 8 + cm_rep_members_size(cm_function_params(f)) + cm_rep_members_size(cm_function_locals(f)) + 8 * cm_stemps(s) <= 2147483647 && cm_temp_offset(policy, p, fid, cm_stemps(s)) <= 2147483647 && cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body, next) * cm_stmt_rep(body, s) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cm_emit_function(policy, p, fid)), tail)
*/
{
  int prologue_count = cmc_function_prologue_count(fn) /*@ where f = f, body = body, next = next */;
  /*@ prologue_count == cm_function_prologue_count(f) && emp
      which implies data_at(&prologue_count, int, cm_function_prologue_count(f)) */
  int body_pc = function_pc + prologue_count;
  struct cm_stmt *body_stmt;
  /*@ cm_function_context_rep(fn, f, body, next)
      which implies exists (zp : Z) (zl : Z), fn != 0 && data_at(&(fn->ret_ty), int, cm_type_encode(cm_function_ret(f))) * data_at(&(fn->params), struct cm_slot *, zp) * data_at(&(fn->locals), struct cm_slot *, zl) * data_at(&(fn->body), struct cm_stmt *, body) * data_at(&(fn->next), struct cm_function *, next) * cm_slot_list_rep(zp, cm_function_params(f)) * cm_slot_list_rep(zl, cm_function_locals(f)) */
  body_stmt = fn->body;
  /*@ exists (zp : Z) (zl : Z), fn != 0 && data_at(&(fn->ret_ty), int, cm_type_encode(cm_function_ret(f))) * data_at(&(fn->params), struct cm_slot *, zp) * data_at(&(fn->locals), struct cm_slot *, zl) * data_at(&(fn->body), struct cm_stmt *, body) * data_at(&(fn->next), struct cm_function *, next) * cm_slot_list_rep(zp, cm_function_params(f)) * cm_slot_list_rep(zl, cm_function_locals(f))
      which implies cm_function_context_rep(fn, f, body, next) */
  int temp_limit = cmc_stmt_temps(body_stmt) /*@ where s = s */;
  /*@ temp_limit == cm_stemps(s) && emp
      which implies data_at(&temp_limit, int, cm_stemps(s)) */
  /*@ fid == fid@pre && function_pc == function_pc@pre && f == cm_function_at(policy, fid, cm_program_functions(p)) && s == cm_function_body(f) && body_pc == cm_function_pc(policy, p, fid) + cm_function_prologue_count(f) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_emit_function(policy, p, fid), tail))
      which implies fid == fid@pre && function_pc == function_pc@pre && f == cm_function_at(policy, fid, cm_program_functions(p)) && s == cm_function_body(f) && body_pc == cm_function_pc(policy, p, fid) + cm_function_prologue_count(f) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_emit_prologue(policy, p, fid), app(cm_emit_stmt(policy, p, fid, body_pc, 0, 0, 0, s), app(cons(TVMInst(TVMPushOp, 0), nil), app(cm_return_epilogue, tail))))) */
  cmc_emit_prologue(fn, fid, emitter) /*@ where policy = policy, p = p, f = f, s = s, body = body, next = next, structs = cm_program_structs(p), done = done, tail = app(cm_emit_stmt(policy, p, fid, body_pc, 0, 0, 0, s), app(cons(TVMInst(TVMPushOp, 0), nil), app(cm_return_epilogue, tail))), out = out, capacity = capacity */;
  cmc_emit_stmt(program, fid, fn, body_pc, 0, temp_limit,
                0, 0, body_stmt, emitter) /*@ where policy = policy, cg = cg, p = p, f = f, s = s, loop_ = false, body = body, next = next, functions_ptr = functions_ptr, done = app(done, cm_emit_prologue(policy, p, fid)), tail = app(cons(TVMInst(TVMPushOp, 0), nil), app(cm_return_epilogue, tail)), out = out, capacity = capacity */;
  /*@ cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(app(done, cm_emit_prologue(policy, p, fid)), cm_emit_stmt(policy, p, fid, body_pc, 0, 0, 0, s)), app(cons(TVMInst(TVMPushOp, 0), nil), app(cm_return_epilogue, tail)))
      which implies cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(app(done, cm_emit_prologue(policy, p, fid)), cm_emit_stmt(policy, p, fid, body_pc, 0, 0, 0, s)), cons(TVMInst(TVMPushOp, 0), app(cm_return_epilogue, tail))) */
  cm_emit_plan(emitter, CMC_OP_PUSH, 0) /*@ where policy = policy, p = p, opcode = TVMPushOp, done = app(app(done, cm_emit_prologue(policy, p, fid)), cm_emit_stmt(policy, p, fid, body_pc, 0, 0, 0, s)), tail = app(cm_return_epilogue, tail), out = out, capacity = capacity */;
  cm_emit_return_epilogue_plan(emitter) /*@ where policy = policy, p = p, done = app(app(app(done, cm_emit_prologue(policy, p, fid)), cm_emit_stmt(policy, p, fid, body_pc, 0, 0, 0, s)), cons(TVMInst(TVMPushOp, 0), nil)), tail = tail, out = out, capacity = capacity */;
  /*@ fid == fid@pre && function_pc == function_pc@pre && f == cm_function_at(policy, fid, cm_program_functions(p)) && s == cm_function_body(f) && body_pc == cm_function_pc(policy, p, fid) + cm_function_prologue_count(f) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(app(app(app(done, cm_emit_prologue(policy, p, fid)), cm_emit_stmt(policy, p, fid, body_pc, 0, 0, 0, s)), cons(TVMInst(TVMPushOp, 0), nil)), cm_return_epilogue), tail)
      which implies fid == fid@pre && function_pc == function_pc@pre && f == cm_function_at(policy, fid, cm_program_functions(p)) && s == cm_function_body(f) && body_pc == cm_function_pc(policy, p, fid) + cm_function_prologue_count(f) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cm_emit_function(policy, p, fid)), tail) */
}
