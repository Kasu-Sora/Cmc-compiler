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
/*@ Import Coq Require Import SimpleC.EE.QCP_demos_human.cmc_emit_stmt_migration_lib */

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
void cm_emit_expr(struct cm_program *program, int fid,
                  struct cm_function *fn, int pc, int temp,
                  int temp_limit, struct cm_expr *expr, int lvalue,
                  struct cm_emitter *emitter)
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

void cm_emit_return_epilogue_plan(struct cm_emitter *emitter)
/*@ With (policy : cm_lookup_policy) (p : cm_program) (done : list tvm_inst) (tail : list tvm_inst) (out : Z) (capacity : Z)
    Require cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_return_epilogue, tail))
    Ensure cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cm_return_epilogue), tail)
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

int cm_expr_rvalue_count_context(struct cm_program *program, int fid,
                                 struct cm_function *fn,
                                 struct cm_expr *expr)
/*@ With (policy : cm_lookup_policy) (cg : cm_codegen_obligations) (p : cm_program) (f : cm_function_d) (e : cm_expr) (body : Z) (next : Z) (functions_ptr : Z)
    Require cm_wf_program(policy, cg, p) && f == cm_function_at(policy, fid, cm_program_functions(p)) && cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) && cm_rep_structs_safe(cm_program_structs(p)) && cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body, next) * cm_expr_rep(expr, e)
    Ensure cm_wf_program(policy, cg, p) && f == cm_function_at(policy, fid, cm_program_functions(p)) && cm_expr_wf(policy, p, f, e) && cm_expr_counts_representable(policy, p, fid, e) && cm_rep_structs_safe(cm_program_structs(p)) && __return == cm_rvalue_code_count(policy, p, fid, e) && cm_i32_code_count(__return) && cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body, next) * cm_expr_rep(expr, e)
*/;

int cm_stmt_code_count_context(struct cm_program *program, int fid,
                               struct cm_function *fn,
                               struct cm_stmt *stmt)
/*@ With (policy : cm_lookup_policy) (cg : cm_codegen_obligations) (p : cm_program) (f : cm_function_d) (s : cm_stmt) (loop_ : bool) (body : Z) (next : Z) (functions_ptr : Z)
    Require cm_wf_program(policy, cg, p) && f == cm_function_at(policy, fid, cm_program_functions(p)) && cm_stmt_wf(policy, p, f, loop_, s) && cm_stmt_counts_representable(policy, p, fid, s) && cm_rep_structs_safe(cm_program_structs(p)) && cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body, next) * cm_stmt_rep(stmt, s)
    Ensure cm_wf_program(policy, cg, p) && f == cm_function_at(policy, fid, cm_program_functions(p)) && cm_stmt_wf(policy, p, f, loop_, s) && cm_stmt_counts_representable(policy, p, fid, s) && cm_rep_structs_safe(cm_program_structs(p)) && __return == cm_stmt_code_count(policy, p, fid, s) && cm_i32_code_count(__return) && cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body, next) * cm_stmt_rep(stmt, s)
*/;

int cmc_slot_type_at(struct cm_slot *item, int index)
/*@ With (slots : list cm_slot_d)
    Require 0 <= index && cm_slot_list_rep(item, slots)
    Ensure 0 <= index && __return == cm_rep_slot_type(slots, index) && cm_slot_list_rep(item, slots)
*/;

void cmc_emit_if_stmt(struct cm_program *program, int fid,
                      struct cm_function *fn, int pc, int temp,
                      int temp_limit, int break_pc, int continue_pc,
                      struct cm_stmt *stmt, struct cm_emitter *emitter)
/*@ With (policy : cm_lookup_policy) (cg : cm_codegen_obligations) (p : cm_program) (f : cm_function_d) (s : cm_stmt) (loop_ : bool) (body : Z) (next : Z) (functions_ptr : Z) (done : list tvm_inst) (tail : list tvm_inst) (out : Z) (capacity : Z) (guard_ : cm_expr) (yes_ : cm_stmt) (no_ : cm_stmt)
 Require s == CMIfS(guard_, yes_, no_) && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) && f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_stmt_wf(policy, p, f, loop_, s) && cm_stmt_counts_representable(policy, p, fid, s) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 0 <= temp && temp <= temp_limit && temp + cm_stemps(s) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) && cm_i32_code_count(break_pc) && cm_i32_code_count(continue_pc) &&
 cm_i32_code_count(pc + Zlength(cm_emit_stmt(policy, p, fid, pc, temp, break_pc, continue_pc, s))) && cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body, next) * cm_stmt_rep(stmt, s) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_emit_stmt(policy, p, fid, pc, temp, break_pc, continue_pc, s), tail))
 Ensure s == CMIfS(guard_, yes_, no_) && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) && f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_stmt_wf(policy, p, f, loop_, s) && cm_stmt_counts_representable(policy, p, fid, s) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 0 <= temp && temp <= temp_limit && temp + cm_stemps(s) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) && cm_i32_code_count(break_pc) && cm_i32_code_count(continue_pc) &&
 cm_i32_code_count(pc + Zlength(cm_emit_stmt(policy, p, fid, pc, temp, break_pc, continue_pc, s))) && cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body, next) * cm_stmt_rep(stmt, s) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cm_emit_stmt(policy, p, fid, pc, temp, break_pc, continue_pc, s)), tail)
*/
;

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
*/
;

void cmc_emit_if_stmt(struct cm_program *program, int fid,
                      struct cm_function *fn, int pc, int temp,
                      int temp_limit, int break_pc, int continue_pc,
                      struct cm_stmt *stmt, struct cm_emitter *emitter)
/*@ With (policy : cm_lookup_policy) (cg : cm_codegen_obligations) (p : cm_program) (f : cm_function_d) (s : cm_stmt) (loop_ : bool) (body : Z) (next : Z) (functions_ptr : Z) (done : list tvm_inst) (tail : list tvm_inst) (out : Z) (capacity : Z) (guard_ : cm_expr) (yes_ : cm_stmt) (no_ : cm_stmt)
 Require s == CMIfS(guard_, yes_, no_) && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) && f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_stmt_wf(policy, p, f, loop_, s) && cm_stmt_counts_representable(policy, p, fid, s) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 0 <= temp && temp <= temp_limit && temp + cm_stemps(s) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) && cm_i32_code_count(break_pc) && cm_i32_code_count(continue_pc) &&
 cm_i32_code_count(pc + Zlength(cm_emit_stmt(policy, p, fid, pc, temp, break_pc, continue_pc, s))) && cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body, next) * cm_stmt_rep(stmt, s) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_emit_stmt(policy, p, fid, pc, temp, break_pc, continue_pc, s), tail))
 Ensure s == CMIfS(guard_, yes_, no_) && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) && f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_stmt_wf(policy, p, f, loop_, s) && cm_stmt_counts_representable(policy, p, fid, s) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 0 <= temp && temp <= temp_limit && temp + cm_stemps(s) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) && cm_i32_code_count(break_pc) && cm_i32_code_count(continue_pc) &&
 cm_i32_code_count(pc + Zlength(cm_emit_stmt(policy, p, fid, pc, temp, break_pc, continue_pc, s))) && cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body, next) * cm_stmt_rep(stmt, s) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cm_emit_stmt(policy, p, fid, pc, temp, break_pc, continue_pc, s)), tail)
*/
{
  /*@ cm_stmt_rep(stmt, s)
      which implies exists (xe : Z) (xa : Z) (xb : Z), stmt != 0 && data_at(&(stmt->kind), int, cm_rep_stmt_kind(s)) * data_at(&(stmt->slot), int, cm_rep_stmt_slot(s)) * data_at(&(stmt->expr), struct cm_expr *, xe) * data_at(&(stmt->a), struct cm_stmt *, xa) * data_at(&(stmt->b), struct cm_stmt *, xb) * cm_stmt_payload(s, xe, xa, xb) */
  /*@ exists (xe : Z) (xa : Z) (xb : Z), stmt != 0 && data_at(&(stmt->kind), int, cm_rep_stmt_kind(s)) * data_at(&(stmt->slot), int, cm_rep_stmt_slot(s)) * data_at(&(stmt->expr), struct cm_expr *, xe) * data_at(&(stmt->a), struct cm_stmt *, xa) * data_at(&(stmt->b), struct cm_stmt *, xb) * (s == CMIfS(guard_, yes_, no_) && cm_stmt_payload(s, xe, xa, xb))
      which implies exists (xe : Z) (xa : Z) (xb : Z), stmt != 0 && data_at(&(stmt->kind), int, cm_rep_stmt_kind(s)) * data_at(&(stmt->slot), int, cm_rep_stmt_slot(s)) * data_at(&(stmt->expr), struct cm_expr *, xe) * data_at(&(stmt->a), struct cm_stmt *, xa) * data_at(&(stmt->b), struct cm_stmt *, xb) * (s == CMIfS(guard_, yes_, no_) && cm_expr_rep(xe, guard_) * cm_stmt_rep(xa, yes_) * cm_stmt_rep(xb, no_)) */
  /*@ s == CMIfS(guard_, yes_, no_) && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) && f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_stmt_wf(policy, p, f, loop_, s) && cm_stmt_counts_representable(policy, p, fid, s) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 0 <= temp && temp <= temp_limit && temp + cm_stemps(s) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) && cm_i32_code_count(break_pc) && cm_i32_code_count(continue_pc) &&
 cm_i32_code_count(pc + Zlength(cm_emit_stmt(policy, p, fid, pc, temp, break_pc, continue_pc, s))) && emp
      which implies s == CMIfS(guard_, yes_, no_) && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) && f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_stmt_wf(policy, p, f, loop_, s) && cm_stmt_counts_representable(policy, p, fid, s) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 0 <= temp && temp <= temp_limit && temp + cm_stemps(s) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) && cm_i32_code_count(break_pc) && cm_i32_code_count(continue_pc) &&
 cm_i32_code_count(pc + Zlength(cm_emit_stmt(policy, p, fid, pc, temp, break_pc, continue_pc, s))) && cm_expr_wf(policy, p, f, guard_) && cm_expr_counts_representable(policy, p, fid, guard_) && temp + cm_expr_temps_for(guard_, 0) <= temp_limit && cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, guard_, 0))) && cm_stmt_wf(policy, p, f, loop_, yes_) && cm_stmt_counts_representable(policy, p, fid, yes_) && temp + cm_stemps(yes_) <= temp_limit && cm_i32_code_count(pc + cm_rvalue_code_count(policy, p, fid, guard_) + 1) && cm_i32_code_count(break_pc) && cm_i32_code_count(continue_pc) && cm_i32_code_count((pc + cm_rvalue_code_count(policy, p, fid, guard_) + 1) + Zlength(cm_emit_stmt(policy, p, fid, pc + cm_rvalue_code_count(policy, p, fid, guard_) + 1, temp, break_pc, continue_pc, yes_))) && cm_stmt_wf(policy, p, f, loop_, no_) && cm_stmt_counts_representable(policy, p, fid, no_) && temp + cm_stemps(no_) <= temp_limit && cm_i32_code_count(pc + cm_rvalue_code_count(policy, p, fid, guard_) + 1 + cm_stmt_code_count(policy, p, fid, yes_) + 1) && cm_i32_code_count(break_pc) && cm_i32_code_count(continue_pc) && cm_i32_code_count((pc + cm_rvalue_code_count(policy, p, fid, guard_) + 1 + cm_stmt_code_count(policy, p, fid, yes_) + 1) + Zlength(cm_emit_stmt(policy, p, fid, pc + cm_rvalue_code_count(policy, p, fid, guard_) + 1 + cm_stmt_code_count(policy, p, fid, yes_) + 1, temp, break_pc, continue_pc, no_))) && cm_i32_code_count(pc + cm_stmt_code_count(policy, p, fid, s)) && tvm_opcode_code(TVMJzOp) == 20 && tvm_opcode_code(TVMJzOp) != 22 && tvm_opcode_code(TVMJmpOp) == 19 && tvm_opcode_code(TVMJmpOp) != 22 && emp */
    int guard_count = cm_expr_rvalue_count_context(
        program, fid, fn, stmt->expr) /*@ where policy = policy, cg = cg, p = p, f = f, body = body, next = next, functions_ptr = functions_ptr, e = guard_ */;
  /*@ exists (count_value : Z), count_value == cm_rvalue_code_count(policy, p, fid, guard_) && data_at(&guard_count, int, count_value)
      which implies data_at(&guard_count, int, cm_rvalue_code_count(policy, p, fid, guard_)) */
    int yes_count = cm_stmt_code_count_context(
        program, fid, fn, stmt->a) /*@ where policy = policy, cg = cg, p = p, f = f, body = body, next = next, functions_ptr = functions_ptr, s = yes_, loop_ = loop_ */;
  /*@ exists (count_value : Z), count_value == cm_stmt_code_count(policy, p, fid, yes_) && data_at(&yes_count, int, count_value)
      which implies data_at(&yes_count, int, cm_stmt_code_count(policy, p, fid, yes_)) */
    int no_count = cm_stmt_code_count_context(
        program, fid, fn, stmt->b) /*@ where policy = policy, cg = cg, p = p, f = f, body = body, next = next, functions_ptr = functions_ptr, s = no_, loop_ = loop_ */;
  /*@ exists (count_value : Z), count_value == cm_stmt_code_count(policy, p, fid, no_) && data_at(&no_count, int, count_value)
      which implies data_at(&no_count, int, cm_stmt_code_count(policy, p, fid, no_)) */
    long long no_target =
        (long long)pc +
        ((long long)guard_count + ((long long)yes_count + 2LL));
    long long end_target =
        (long long)pc +
        ((long long)guard_count +
         ((long long)yes_count + ((long long)no_count + 2LL)));
    int yes_pc = pc + (guard_count + 1);
    int no_pc = pc + (guard_count + (1 + (yes_count + 1)));
    int end_pc =
        pc + (guard_count + (1 + (yes_count + (1 + no_count))));
  /*@ s == CMIfS(guard_, yes_, no_) && guard_count == cm_rvalue_code_count(policy, p, fid, guard_) && yes_count == cm_stmt_code_count(policy, p, fid, yes_) && no_count == cm_stmt_code_count(policy, p, fid, no_) && no_target == pc + guard_count + yes_count + 2 && end_target == pc + guard_count + yes_count + no_count + 2 && yes_pc == pc + guard_count + 1 && no_pc == pc + guard_count + yes_count + 2 && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_emit_stmt(policy, p, fid, pc, temp, break_pc, continue_pc, s), tail))
      which implies s == CMIfS(guard_, yes_, no_) && guard_count == cm_rvalue_code_count(policy, p, fid, guard_) && yes_count == cm_stmt_code_count(policy, p, fid, yes_) && no_count == cm_stmt_code_count(policy, p, fid, no_) && no_target == pc + guard_count + yes_count + 2 && end_target == pc + guard_count + yes_count + no_count + 2 && yes_pc == pc + guard_count + 1 && no_pc == pc + guard_count + yes_count + 2 && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_expr_code_for(policy, p, fid, pc, temp, guard_, 0), app(cons(TVMInst(TVMJzOp, no_target), nil), app(cm_emit_stmt(policy, p, fid, yes_pc, temp, break_pc, continue_pc, yes_), app(cons(TVMInst(TVMJmpOp, end_target), nil), app(cm_emit_stmt(policy, p, fid, no_pc, temp, break_pc, continue_pc, no_), tail)))))) */
    cm_emit_expr(program, fid, fn, pc, temp, temp_limit,
                 stmt->expr, 0, emitter) /*@ where policy = policy, cg = cg, p = p, f = f, body = body, next = next, functions_ptr = functions_ptr, e = guard_, done = done, tail = app(cons(TVMInst(TVMJzOp, no_target), nil), app(cm_emit_stmt(policy, p, fid, yes_pc, temp, break_pc, continue_pc, yes_), app(cons(TVMInst(TVMJmpOp, end_target), nil), app(cm_emit_stmt(policy, p, fid, no_pc, temp, break_pc, continue_pc, no_), tail)))), out = out, capacity = capacity */;
  /*@ s == CMIfS(guard_, yes_, no_) && guard_count == cm_rvalue_code_count(policy, p, fid, guard_) && yes_count == cm_stmt_code_count(policy, p, fid, yes_) && no_count == cm_stmt_code_count(policy, p, fid, no_) && no_target == pc + guard_count + yes_count + 2 && end_target == pc + guard_count + yes_count + no_count + 2 && yes_pc == pc + guard_count + 1 && no_pc == pc + guard_count + yes_count + 2 && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cm_expr_code_for(policy, p, fid, pc, temp, guard_, 0)), app(cons(TVMInst(TVMJzOp, no_target), nil), app(cm_emit_stmt(policy, p, fid, yes_pc, temp, break_pc, continue_pc, yes_), app(cons(TVMInst(TVMJmpOp, end_target), nil), app(cm_emit_stmt(policy, p, fid, no_pc, temp, break_pc, continue_pc, no_), tail)))))
      which implies s == CMIfS(guard_, yes_, no_) && guard_count == cm_rvalue_code_count(policy, p, fid, guard_) && yes_count == cm_stmt_code_count(policy, p, fid, yes_) && no_count == cm_stmt_code_count(policy, p, fid, no_) && no_target == pc + guard_count + yes_count + 2 && end_target == pc + guard_count + yes_count + no_count + 2 && yes_pc == pc + guard_count + 1 && no_pc == pc + guard_count + yes_count + 2 && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cm_expr_code_for(policy, p, fid, pc, temp, guard_, 0)), cons(TVMInst(TVMJzOp, no_target), app(cm_emit_stmt(policy, p, fid, yes_pc, temp, break_pc, continue_pc, yes_), app(cons(TVMInst(TVMJmpOp, end_target), nil), app(cm_emit_stmt(policy, p, fid, no_pc, temp, break_pc, continue_pc, no_), tail))))) */
    cm_emit_plan(emitter, CMC_OP_JZ, no_target) /*@ where policy = policy, p = p, out = out, capacity = capacity, opcode = TVMJzOp, done = app(done, cm_expr_code_for(policy, p, fid, pc, temp, guard_, 0)), tail = app(cm_emit_stmt(policy, p, fid, yes_pc, temp, break_pc, continue_pc, yes_), app(cons(TVMInst(TVMJmpOp, end_target), nil), app(cm_emit_stmt(policy, p, fid, no_pc, temp, break_pc, continue_pc, no_), tail))) */;
  
    cmc_emit_stmt(program, fid, fn, yes_pc, temp, temp_limit,
                 break_pc, continue_pc, stmt->a, emitter) /*@ where policy = policy, cg = cg, p = p, f = f, body = body, next = next, functions_ptr = functions_ptr, s = yes_, loop_ = loop_, done = app(app(done, cm_expr_code_for(policy, p, fid, pc, temp, guard_, 0)), cons(TVMInst(TVMJzOp, no_target), nil)), tail = app(cons(TVMInst(TVMJmpOp, end_target), nil), app(cm_emit_stmt(policy, p, fid, no_pc, temp, break_pc, continue_pc, no_), tail)), out = out, capacity = capacity */;
  /*@ s == CMIfS(guard_, yes_, no_) && guard_count == cm_rvalue_code_count(policy, p, fid, guard_) && yes_count == cm_stmt_code_count(policy, p, fid, yes_) && no_count == cm_stmt_code_count(policy, p, fid, no_) && no_target == pc + guard_count + yes_count + 2 && end_target == pc + guard_count + yes_count + no_count + 2 && yes_pc == pc + guard_count + 1 && no_pc == pc + guard_count + yes_count + 2 && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(app(app(done, cm_expr_code_for(policy, p, fid, pc, temp, guard_, 0)), cons(TVMInst(TVMJzOp, no_target), nil)), cm_emit_stmt(policy, p, fid, yes_pc, temp, break_pc, continue_pc, yes_)), app(cons(TVMInst(TVMJmpOp, end_target), nil), app(cm_emit_stmt(policy, p, fid, no_pc, temp, break_pc, continue_pc, no_), tail)))
      which implies s == CMIfS(guard_, yes_, no_) && guard_count == cm_rvalue_code_count(policy, p, fid, guard_) && yes_count == cm_stmt_code_count(policy, p, fid, yes_) && no_count == cm_stmt_code_count(policy, p, fid, no_) && no_target == pc + guard_count + yes_count + 2 && end_target == pc + guard_count + yes_count + no_count + 2 && yes_pc == pc + guard_count + 1 && no_pc == pc + guard_count + yes_count + 2 && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(app(app(done, cm_expr_code_for(policy, p, fid, pc, temp, guard_, 0)), cons(TVMInst(TVMJzOp, no_target), nil)), cm_emit_stmt(policy, p, fid, yes_pc, temp, break_pc, continue_pc, yes_)), cons(TVMInst(TVMJmpOp, end_target), app(cm_emit_stmt(policy, p, fid, no_pc, temp, break_pc, continue_pc, no_), tail))) */
    cm_emit_plan(emitter, CMC_OP_JMP, end_target) /*@ where policy = policy, p = p, out = out, capacity = capacity, opcode = TVMJmpOp, done = app(app(app(done, cm_expr_code_for(policy, p, fid, pc, temp, guard_, 0)), cons(TVMInst(TVMJzOp, no_target), nil)), cm_emit_stmt(policy, p, fid, yes_pc, temp, break_pc, continue_pc, yes_)), tail = app(cm_emit_stmt(policy, p, fid, no_pc, temp, break_pc, continue_pc, no_), tail) */;
  
    cmc_emit_stmt(program, fid, fn, no_pc, temp, temp_limit,
                 break_pc, continue_pc, stmt->b, emitter) /*@ where policy = policy, cg = cg, p = p, f = f, body = body, next = next, functions_ptr = functions_ptr, s = no_, loop_ = loop_, done = app(app(app(app(done, cm_expr_code_for(policy, p, fid, pc, temp, guard_, 0)), cons(TVMInst(TVMJzOp, no_target), nil)), cm_emit_stmt(policy, p, fid, yes_pc, temp, break_pc, continue_pc, yes_)), cons(TVMInst(TVMJmpOp, end_target), nil)), tail = tail, out = out, capacity = capacity */;

  /*@ s == CMIfS(guard_, yes_, no_) && guard_count == cm_rvalue_code_count(policy, p, fid, guard_) && yes_count == cm_stmt_code_count(policy, p, fid, yes_) && no_count == cm_stmt_code_count(policy, p, fid, no_) && no_target == pc + guard_count + yes_count + 2 && end_target == pc + guard_count + yes_count + no_count + 2 && yes_pc == pc + guard_count + 1 && no_pc == pc + guard_count + yes_count + 2 && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(app(app(app(app(done, cm_expr_code_for(policy, p, fid, pc, temp, guard_, 0)), cons(TVMInst(TVMJzOp, no_target), nil)), cm_emit_stmt(policy, p, fid, yes_pc, temp, break_pc, continue_pc, yes_)), cons(TVMInst(TVMJmpOp, end_target), nil)), cm_emit_stmt(policy, p, fid, no_pc, temp, break_pc, continue_pc, no_)), tail)
      which implies s == CMIfS(guard_, yes_, no_) && guard_count == cm_rvalue_code_count(policy, p, fid, guard_) && yes_count == cm_stmt_code_count(policy, p, fid, yes_) && no_count == cm_stmt_code_count(policy, p, fid, no_) && no_target == pc + guard_count + yes_count + 2 && end_target == pc + guard_count + yes_count + no_count + 2 && yes_pc == pc + guard_count + 1 && no_pc == pc + guard_count + yes_count + 2 && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cm_emit_stmt(policy, p, fid, pc, temp, break_pc, continue_pc, s)), tail) */
  /*@ exists (xe : Z) (xa : Z) (xb : Z), stmt != 0 && data_at(&(stmt->kind), int, cm_rep_stmt_kind(s)) * data_at(&(stmt->slot), int, cm_rep_stmt_slot(s)) * data_at(&(stmt->expr), struct cm_expr *, xe) * data_at(&(stmt->a), struct cm_stmt *, xa) * data_at(&(stmt->b), struct cm_stmt *, xb) * (s == CMIfS(guard_, yes_, no_) && cm_expr_rep(xe, guard_) * cm_stmt_rep(xa, yes_) * cm_stmt_rep(xb, no_))
      which implies cm_stmt_rep(stmt, s) */
  
}

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
*/
{
  /*@ cm_stmt_rep(stmt, s)
      which implies exists (xe : Z) (xa : Z) (xb : Z), stmt != 0 && data_at(&(stmt->kind), int, cm_rep_stmt_kind(s)) * data_at(&(stmt->slot), int, cm_rep_stmt_slot(s)) * data_at(&(stmt->expr), struct cm_expr *, xe) * data_at(&(stmt->a), struct cm_stmt *, xa) * data_at(&(stmt->b), struct cm_stmt *, xb) * cm_stmt_payload(s, xe, xa, xb) */
  if (stmt->kind == CMC_STMT_SKIP) {
  /*@ exists (xe : Z) (xa : Z) (xb : Z), stmt != 0 && data_at(&(stmt->kind), int, cm_rep_stmt_kind(s)) * data_at(&(stmt->slot), int, cm_rep_stmt_slot(s)) * data_at(&(stmt->expr), struct cm_expr *, xe) * data_at(&(stmt->a), struct cm_stmt *, xa) * data_at(&(stmt->b), struct cm_stmt *, xb) * (cm_rep_stmt_kind(s) == 0 && cm_stmt_payload(s, xe, xa, xb))
      which implies exists (xe : Z) (xa : Z) (xb : Z), stmt != 0 && data_at(&(stmt->kind), int, cm_rep_stmt_kind(s)) * data_at(&(stmt->slot), int, cm_rep_stmt_slot(s)) * data_at(&(stmt->expr), struct cm_expr *, xe) * data_at(&(stmt->a), struct cm_stmt *, xa) * data_at(&(stmt->b), struct cm_stmt *, xb) * (s == CMSkipS && xe == 0 && xa == 0 && xb == 0 && emp) */
  /*@ s == CMSkipS && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) && f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_stmt_wf(policy, p, f, loop_, s) && cm_stmt_counts_representable(policy, p, fid, s) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 0 <= temp && temp <= temp_limit && temp + cm_stemps(s) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) && cm_i32_code_count(break_pc) && cm_i32_code_count(continue_pc) &&
 cm_i32_code_count(pc + Zlength(cm_emit_stmt(policy, p, fid, pc, temp, break_pc, continue_pc, s))) && emp
      which implies s == CMSkipS && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) && f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_stmt_wf(policy, p, f, loop_, s) && cm_stmt_counts_representable(policy, p, fid, s) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 0 <= temp && temp <= temp_limit && temp + cm_stemps(s) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) && cm_i32_code_count(break_pc) && cm_i32_code_count(continue_pc) &&
 cm_i32_code_count(pc + Zlength(cm_emit_stmt(policy, p, fid, pc, temp, break_pc, continue_pc, s))) && cm_i32_code_count(pc + cm_stmt_code_count(policy, p, fid, s)) && emp */


  /*@ s == CMSkipS && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_emit_stmt(policy, p, fid, pc, temp, break_pc, continue_pc, s), tail))
      which implies s == CMSkipS && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cm_emit_stmt(policy, p, fid, pc, temp, break_pc, continue_pc, s)), tail) */
  /*@ exists (xe : Z) (xa : Z) (xb : Z), stmt != 0 && data_at(&(stmt->kind), int, cm_rep_stmt_kind(s)) * data_at(&(stmt->slot), int, cm_rep_stmt_slot(s)) * data_at(&(stmt->expr), struct cm_expr *, xe) * data_at(&(stmt->a), struct cm_stmt *, xa) * data_at(&(stmt->b), struct cm_stmt *, xb) * (s == CMSkipS && xe == 0 && xa == 0 && xb == 0 && emp)
      which implies cm_stmt_rep(stmt, s) */
  
  } else if (stmt->kind == CMC_STMT_EXPR) {
  /*@ exists (xe : Z) (xa : Z) (xb : Z), stmt != 0 && data_at(&(stmt->kind), int, cm_rep_stmt_kind(s)) * data_at(&(stmt->slot), int, cm_rep_stmt_slot(s)) * data_at(&(stmt->expr), struct cm_expr *, xe) * data_at(&(stmt->a), struct cm_stmt *, xa) * data_at(&(stmt->b), struct cm_stmt *, xb) * (cm_rep_stmt_kind(s) == 1 && cm_stmt_payload(s, xe, xa, xb))
      which implies exists (xe : Z) (xa : Z) (xb : Z), stmt != 0 && data_at(&(stmt->kind), int, cm_rep_stmt_kind(s)) * data_at(&(stmt->slot), int, cm_rep_stmt_slot(s)) * data_at(&(stmt->expr), struct cm_expr *, xe) * data_at(&(stmt->a), struct cm_stmt *, xa) * data_at(&(stmt->b), struct cm_stmt *, xb) * (s == CMExprS(cm_stmt_expr(s)) && xe != 0 && xa == 0 && xb == 0 && cm_expr_rep(xe, cm_stmt_expr(s))) */
  /*@ s == CMExprS(cm_stmt_expr(s)) && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) && f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_stmt_wf(policy, p, f, loop_, s) && cm_stmt_counts_representable(policy, p, fid, s) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 0 <= temp && temp <= temp_limit && temp + cm_stemps(s) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) && cm_i32_code_count(break_pc) && cm_i32_code_count(continue_pc) &&
 cm_i32_code_count(pc + Zlength(cm_emit_stmt(policy, p, fid, pc, temp, break_pc, continue_pc, s))) && emp
      which implies s == CMExprS(cm_stmt_expr(s)) && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) && f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_stmt_wf(policy, p, f, loop_, s) && cm_stmt_counts_representable(policy, p, fid, s) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 0 <= temp && temp <= temp_limit && temp + cm_stemps(s) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) && cm_i32_code_count(break_pc) && cm_i32_code_count(continue_pc) &&
 cm_i32_code_count(pc + Zlength(cm_emit_stmt(policy, p, fid, pc, temp, break_pc, continue_pc, s))) && cm_expr_wf(policy, p, f, cm_stmt_expr(s)) && cm_expr_counts_representable(policy, p, fid, cm_stmt_expr(s)) && temp + cm_expr_temps_for(cm_stmt_expr(s), 0) <= temp_limit && cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, cm_stmt_expr(s), 0))) && cm_i32_code_count(pc + cm_stmt_code_count(policy, p, fid, s)) && tvm_opcode_code(TVMPopOp) == 1 && tvm_opcode_code(TVMPopOp) != 22 && emp */

  /*@ break_pc == break_pc@pre && continue_pc == continue_pc@pre && s == CMExprS(cm_stmt_expr(s)) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_emit_stmt(policy, p, fid, pc, temp, break_pc, continue_pc, s), tail))
      which implies break_pc == break_pc@pre && continue_pc == continue_pc@pre && s == CMExprS(cm_stmt_expr(s)) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_expr_code_for(policy, p, fid, pc, temp, cm_stmt_expr(s), 0), app(cons(TVMInst(TVMPopOp, 0), nil), tail))) */
    cm_emit_expr(program, fid, fn, pc, temp, temp_limit,
                 stmt->expr, 0, emitter) /*@ where policy = policy, cg = cg, p = p, f = f, body = body, next = next, functions_ptr = functions_ptr, e = cm_stmt_expr(s), done = done, tail = app(cons(TVMInst(TVMPopOp, 0), nil), tail), out = out, capacity = capacity */;
  /*@ s == CMExprS(cm_stmt_expr(s)) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cm_expr_code_for(policy, p, fid, pc, temp, cm_stmt_expr(s), 0)), app(cons(TVMInst(TVMPopOp, 0), nil), tail))
      which implies s == CMExprS(cm_stmt_expr(s)) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cm_expr_code_for(policy, p, fid, pc, temp, cm_stmt_expr(s), 0)), cons(TVMInst(TVMPopOp, 0), tail)) */
    cm_emit_plan(emitter, CMC_OP_POP, 0) /*@ where policy = policy, p = p, out = out, capacity = capacity, opcode = TVMPopOp, done = app(done, cm_expr_code_for(policy, p, fid, pc, temp, cm_stmt_expr(s), 0)), tail = tail */;

  /*@ break_pc == break_pc@pre && continue_pc == continue_pc@pre && s == CMExprS(cm_stmt_expr(s)) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(app(done, cm_expr_code_for(policy, p, fid, pc, temp, cm_stmt_expr(s), 0)), cons(TVMInst(TVMPopOp, 0), nil)), tail)
      which implies break_pc == break_pc@pre && continue_pc == continue_pc@pre && s == CMExprS(cm_stmt_expr(s)) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cm_emit_stmt(policy, p, fid, pc, temp, break_pc, continue_pc, s)), tail) */
  /*@ exists (xe : Z) (xa : Z) (xb : Z), stmt != 0 && data_at(&(stmt->kind), int, cm_rep_stmt_kind(s)) * data_at(&(stmt->slot), int, cm_rep_stmt_slot(s)) * data_at(&(stmt->expr), struct cm_expr *, xe) * data_at(&(stmt->a), struct cm_stmt *, xa) * data_at(&(stmt->b), struct cm_stmt *, xb) * (s == CMExprS(cm_stmt_expr(s)) && xe != 0 && xa == 0 && xb == 0 && cm_expr_rep(xe, cm_stmt_expr(s)))
      which implies cm_stmt_rep(stmt, s) */
  
  } else if (stmt->kind == CMC_STMT_DECL) {
  /*@ exists (xe : Z) (xa : Z) (xb : Z), stmt != 0 && data_at(&(stmt->kind), int, cm_rep_stmt_kind(s)) * data_at(&(stmt->slot), int, cm_rep_stmt_slot(s)) * data_at(&(stmt->expr), struct cm_expr *, xe) * data_at(&(stmt->a), struct cm_stmt *, xa) * data_at(&(stmt->b), struct cm_stmt *, xb) * (cm_rep_stmt_kind(s) == 2 && cm_stmt_payload(s, xe, xa, xb))
      which implies exists (xe : Z) (xa : Z) (xb : Z), stmt != 0 && data_at(&(stmt->kind), int, cm_rep_stmt_kind(s)) * data_at(&(stmt->slot), int, cm_rep_stmt_slot(s)) * data_at(&(stmt->expr), struct cm_expr *, xe) * data_at(&(stmt->a), struct cm_stmt *, xa) * data_at(&(stmt->b), struct cm_stmt *, xb) * (s == CMDeclS(cm_rep_stmt_slot(s)) && xe == 0 && xa == 0 && xb == 0 && emp) */
  /*@ s == CMDeclS(cm_rep_stmt_slot(s)) && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) && f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_stmt_wf(policy, p, f, loop_, s) && cm_stmt_counts_representable(policy, p, fid, s) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 0 <= temp && temp <= temp_limit && temp + cm_stemps(s) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) && cm_i32_code_count(break_pc) && cm_i32_code_count(continue_pc) &&
 cm_i32_code_count(pc + Zlength(cm_emit_stmt(policy, p, fid, pc, temp, break_pc, continue_pc, s))) && emp
      which implies s == CMDeclS(cm_rep_stmt_slot(s)) && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) && f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_stmt_wf(policy, p, f, loop_, s) && cm_stmt_counts_representable(policy, p, fid, s) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 0 <= temp && temp <= temp_limit && temp + cm_stemps(s) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) && cm_i32_code_count(break_pc) && cm_i32_code_count(continue_pc) &&
 cm_i32_code_count(pc + Zlength(cm_emit_stmt(policy, p, fid, pc, temp, break_pc, continue_pc, s))) && cm_i32_code_count(pc + cm_stmt_code_count(policy, p, fid, s)) && emp */


  /*@ s == CMDeclS(cm_rep_stmt_slot(s)) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_emit_stmt(policy, p, fid, pc, temp, break_pc, continue_pc, s), tail))
      which implies s == CMDeclS(cm_rep_stmt_slot(s)) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cm_emit_stmt(policy, p, fid, pc, temp, break_pc, continue_pc, s)), tail) */
  /*@ exists (xe : Z) (xa : Z) (xb : Z), stmt != 0 && data_at(&(stmt->kind), int, cm_rep_stmt_kind(s)) * data_at(&(stmt->slot), int, cm_rep_stmt_slot(s)) * data_at(&(stmt->expr), struct cm_expr *, xe) * data_at(&(stmt->a), struct cm_stmt *, xa) * data_at(&(stmt->b), struct cm_stmt *, xb) * (s == CMDeclS(cm_rep_stmt_slot(s)) && xe == 0 && xa == 0 && xb == 0 && emp)
      which implies cm_stmt_rep(stmt, s) */
  
  } else if (stmt->kind == CMC_STMT_INIT) {
  /*@ exists (xe : Z) (xa : Z) (xb : Z), stmt != 0 && data_at(&(stmt->kind), int, cm_rep_stmt_kind(s)) * data_at(&(stmt->slot), int, cm_rep_stmt_slot(s)) * data_at(&(stmt->expr), struct cm_expr *, xe) * data_at(&(stmt->a), struct cm_stmt *, xa) * data_at(&(stmt->b), struct cm_stmt *, xb) * (cm_rep_stmt_kind(s) == 3 && cm_stmt_payload(s, xe, xa, xb))
      which implies exists (xe : Z) (xa : Z) (xb : Z), stmt != 0 && data_at(&(stmt->kind), int, cm_rep_stmt_kind(s)) * data_at(&(stmt->slot), int, cm_rep_stmt_slot(s)) * data_at(&(stmt->expr), struct cm_expr *, xe) * data_at(&(stmt->a), struct cm_stmt *, xa) * data_at(&(stmt->b), struct cm_stmt *, xb) * (s == CMInitS(cm_rep_stmt_slot(s), cm_stmt_expr(s)) && xe != 0 && xa == 0 && xb == 0 && cm_expr_rep(xe, cm_stmt_expr(s))) */
  /*@ s == CMInitS(cm_rep_stmt_slot(s), cm_stmt_expr(s)) && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) && f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_stmt_wf(policy, p, f, loop_, s) && cm_stmt_counts_representable(policy, p, fid, s) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 0 <= temp && temp <= temp_limit && temp + cm_stemps(s) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) && cm_i32_code_count(break_pc) && cm_i32_code_count(continue_pc) &&
 cm_i32_code_count(pc + Zlength(cm_emit_stmt(policy, p, fid, pc, temp, break_pc, continue_pc, s))) && emp
      which implies s == CMInitS(cm_rep_stmt_slot(s), cm_stmt_expr(s)) && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) && f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_stmt_wf(policy, p, f, loop_, s) && cm_stmt_counts_representable(policy, p, fid, s) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 0 <= temp && temp <= temp_limit && temp + cm_stemps(s) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) && cm_i32_code_count(break_pc) && cm_i32_code_count(continue_pc) &&
 cm_i32_code_count(pc + Zlength(cm_emit_stmt(policy, p, fid, pc, temp, break_pc, continue_pc, s))) && cm_expr_wf(policy, p, f, cm_stmt_expr(s)) && cm_expr_counts_representable(policy, p, fid, cm_stmt_expr(s)) && temp + cm_expr_temps_for(cm_stmt_expr(s), 0) <= temp_limit && cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, cm_stmt_expr(s), 0))) && cm_i32_code_count(pc + cm_stmt_code_count(policy, p, fid, s)) && 0 <= cm_rep_stmt_slot(s) && cm_binding_valid(p, f, 1, cm_rep_stmt_slot(s)) && cm_type_code_wf(cm_slot_ty(cm_slot_at(cm_rep_stmt_slot(s), cm_function_locals(f)))) && cm_rep_slot_type(cm_function_locals(f), cm_rep_stmt_slot(s)) == cm_type_encode(cm_slot_ty(cm_slot_at(cm_rep_stmt_slot(s), cm_function_locals(f)))) && emp */

      /*@ cm_function_context_rep(fn, f, body, next)
      which implies exists (zp : Z) (zl : Z), fn != 0 && data_at(&(fn->ret_ty), int, cm_type_encode(cm_function_ret(f))) * data_at(&(fn->params), struct cm_slot *, zp) * data_at(&(fn->locals), struct cm_slot *, zl) * data_at(&(fn->body), struct cm_stmt *, body) * data_at(&(fn->next), struct cm_function *, next) * cm_slot_list_rep(zp, cm_function_params(f)) * cm_slot_list_rep(zl, cm_function_locals(f)) */
    int local_ty = cmc_slot_type_at(fn->locals, stmt->slot) /*@ where slots = cm_function_locals(f) */;
  /*@ exists (zp : Z) (zl : Z), fn != 0 && data_at(&(fn->ret_ty), int, cm_type_encode(cm_function_ret(f))) * data_at(&(fn->params), struct cm_slot *, zp) * data_at(&(fn->locals), struct cm_slot *, zl) * data_at(&(fn->body), struct cm_stmt *, body) * data_at(&(fn->next), struct cm_function *, next) * cm_slot_list_rep(zp, cm_function_params(f)) * cm_slot_list_rep(zl, cm_function_locals(f))
      which implies cm_function_context_rep(fn, f, body, next) */

  /*@ break_pc == break_pc@pre && continue_pc == continue_pc@pre && s == CMInitS(cm_rep_stmt_slot(s), cm_stmt_expr(s)) && f == cm_function_at(policy, fid, cm_program_functions(p)) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_emit_stmt(policy, p, fid, pc, temp, break_pc, continue_pc, s), tail))
      which implies break_pc == break_pc@pre && continue_pc == continue_pc@pre && s == CMInitS(cm_rep_stmt_slot(s), cm_stmt_expr(s)) && f == cm_function_at(policy, fid, cm_program_functions(p)) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_expr_code_for(policy, p, fid, pc, temp, cm_stmt_expr(s), 0), app(cm_char_normalize_code(cm_slot_ty(cm_slot_at(cm_rep_stmt_slot(s), cm_function_locals(f)))), app(cm_binding_address_code(policy, p, fid, 1, cm_rep_stmt_slot(s)), app(cm_store_code(cm_slot_ty(cm_slot_at(cm_rep_stmt_slot(s), cm_function_locals(f)))), tail))))) */
    cm_emit_expr(program, fid, fn, pc, temp, temp_limit,
                 stmt->expr, 0, emitter) /*@ where policy = policy, cg = cg, p = p, f = f, body = body, next = next, functions_ptr = functions_ptr, e = cm_stmt_expr(s), done = done, tail = app(cm_char_normalize_code(cm_slot_ty(cm_slot_at(cm_rep_stmt_slot(s), cm_function_locals(f)))), app(cm_binding_address_code(policy, p, fid, 1, cm_rep_stmt_slot(s)), app(cm_store_code(cm_slot_ty(cm_slot_at(cm_rep_stmt_slot(s), cm_function_locals(f)))), tail))), out = out, capacity = capacity */;
  
    cm_emit_normalize_plan(emitter, local_ty) /*@ where policy = policy, p = p, out = out, capacity = capacity, model_ty = cm_slot_ty(cm_slot_at(cm_rep_stmt_slot(s), cm_function_locals(f))), done = app(done, cm_expr_code_for(policy, p, fid, pc, temp, cm_stmt_expr(s), 0)), tail = app(cm_binding_address_code(policy, p, fid, 1, cm_rep_stmt_slot(s)), app(cm_store_code(cm_slot_ty(cm_slot_at(cm_rep_stmt_slot(s), cm_function_locals(f)))), tail)) */;
  
    cm_emit_binding_address_plan(program, fn, CMC_BIND_LOCAL,
                                 stmt->slot, emitter) /*@ where policy = policy, cg = cg, p = p, f = f, body = body, next = next, functions_ptr = functions_ptr, fid = fid, structs = cm_program_structs(p), globals = cm_program_globals(p), done = app(app(done, cm_expr_code_for(policy, p, fid, pc, temp, cm_stmt_expr(s), 0)), cm_char_normalize_code(cm_slot_ty(cm_slot_at(cm_rep_stmt_slot(s), cm_function_locals(f))))), tail = app(cm_store_code(cm_slot_ty(cm_slot_at(cm_rep_stmt_slot(s), cm_function_locals(f)))), tail), out = out, capacity = capacity */;
  
    cm_emit_store_plan(emitter, local_ty) /*@ where policy = policy, p = p, out = out, capacity = capacity, model_ty = cm_slot_ty(cm_slot_at(cm_rep_stmt_slot(s), cm_function_locals(f))), done = app(app(app(done, cm_expr_code_for(policy, p, fid, pc, temp, cm_stmt_expr(s), 0)), cm_char_normalize_code(cm_slot_ty(cm_slot_at(cm_rep_stmt_slot(s), cm_function_locals(f))))), cm_binding_address_code(policy, p, fid, 1, cm_rep_stmt_slot(s))), tail = tail */;

  /*@ break_pc == break_pc@pre && continue_pc == continue_pc@pre && s == CMInitS(cm_rep_stmt_slot(s), cm_stmt_expr(s)) && f == cm_function_at(policy, fid, cm_program_functions(p)) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(app(app(app(done, cm_expr_code_for(policy, p, fid, pc, temp, cm_stmt_expr(s), 0)), cm_char_normalize_code(cm_slot_ty(cm_slot_at(cm_rep_stmt_slot(s), cm_function_locals(f))))), cm_binding_address_code(policy, p, fid, 1, cm_rep_stmt_slot(s))), cm_store_code(cm_slot_ty(cm_slot_at(cm_rep_stmt_slot(s), cm_function_locals(f))))), tail)
      which implies break_pc == break_pc@pre && continue_pc == continue_pc@pre && s == CMInitS(cm_rep_stmt_slot(s), cm_stmt_expr(s)) && f == cm_function_at(policy, fid, cm_program_functions(p)) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cm_emit_stmt(policy, p, fid, pc, temp, break_pc, continue_pc, s)), tail) */
  /*@ exists (xe : Z) (xa : Z) (xb : Z), stmt != 0 && data_at(&(stmt->kind), int, cm_rep_stmt_kind(s)) * data_at(&(stmt->slot), int, cm_rep_stmt_slot(s)) * data_at(&(stmt->expr), struct cm_expr *, xe) * data_at(&(stmt->a), struct cm_stmt *, xa) * data_at(&(stmt->b), struct cm_stmt *, xb) * (s == CMInitS(cm_rep_stmt_slot(s), cm_stmt_expr(s)) && xe != 0 && xa == 0 && xb == 0 && cm_expr_rep(xe, cm_stmt_expr(s)))
      which implies cm_stmt_rep(stmt, s) */
  
  } else if (stmt->kind == CMC_STMT_SEQ) {
  /*@ exists (xe : Z) (xa : Z) (xb : Z), stmt != 0 && data_at(&(stmt->kind), int, cm_rep_stmt_kind(s)) * data_at(&(stmt->slot), int, cm_rep_stmt_slot(s)) * data_at(&(stmt->expr), struct cm_expr *, xe) * data_at(&(stmt->a), struct cm_stmt *, xa) * data_at(&(stmt->b), struct cm_stmt *, xb) * (cm_rep_stmt_kind(s) == 4 && cm_stmt_payload(s, xe, xa, xb))
      which implies exists (xe : Z) (xa : Z) (xb : Z), stmt != 0 && data_at(&(stmt->kind), int, cm_rep_stmt_kind(s)) * data_at(&(stmt->slot), int, cm_rep_stmt_slot(s)) * data_at(&(stmt->expr), struct cm_expr *, xe) * data_at(&(stmt->a), struct cm_stmt *, xa) * data_at(&(stmt->b), struct cm_stmt *, xb) * (s == CMSeqS(cm_stmt_first(s), cm_stmt_second(s)) && xe == 0 && cm_stmt_rep(xa, cm_stmt_first(s)) * cm_stmt_rep(xb, cm_stmt_second(s))) */
  /*@ s == CMSeqS(cm_stmt_first(s), cm_stmt_second(s)) && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) && f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_stmt_wf(policy, p, f, loop_, s) && cm_stmt_counts_representable(policy, p, fid, s) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 0 <= temp && temp <= temp_limit && temp + cm_stemps(s) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) && cm_i32_code_count(break_pc) && cm_i32_code_count(continue_pc) &&
 cm_i32_code_count(pc + Zlength(cm_emit_stmt(policy, p, fid, pc, temp, break_pc, continue_pc, s))) && emp
      which implies s == CMSeqS(cm_stmt_first(s), cm_stmt_second(s)) && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) && f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_stmt_wf(policy, p, f, loop_, s) && cm_stmt_counts_representable(policy, p, fid, s) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 0 <= temp && temp <= temp_limit && temp + cm_stemps(s) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) && cm_i32_code_count(break_pc) && cm_i32_code_count(continue_pc) &&
 cm_i32_code_count(pc + Zlength(cm_emit_stmt(policy, p, fid, pc, temp, break_pc, continue_pc, s))) && cm_stmt_wf(policy, p, f, loop_, cm_stmt_first(s)) && cm_stmt_counts_representable(policy, p, fid, cm_stmt_first(s)) && temp + cm_stemps(cm_stmt_first(s)) <= temp_limit && cm_i32_code_count(pc) && cm_i32_code_count(break_pc) && cm_i32_code_count(continue_pc) && cm_i32_code_count((pc) + Zlength(cm_emit_stmt(policy, p, fid, pc, temp, break_pc, continue_pc, cm_stmt_first(s)))) && cm_stmt_wf(policy, p, f, loop_, cm_stmt_second(s)) && cm_stmt_counts_representable(policy, p, fid, cm_stmt_second(s)) && temp + cm_stemps(cm_stmt_second(s)) <= temp_limit && cm_i32_code_count(pc + cm_stmt_code_count(policy, p, fid, cm_stmt_first(s))) && cm_i32_code_count(break_pc) && cm_i32_code_count(continue_pc) && cm_i32_code_count((pc + cm_stmt_code_count(policy, p, fid, cm_stmt_first(s))) + Zlength(cm_emit_stmt(policy, p, fid, pc + cm_stmt_code_count(policy, p, fid, cm_stmt_first(s)), temp, break_pc, continue_pc, cm_stmt_second(s)))) && cm_i32_code_count(pc + cm_stmt_code_count(policy, p, fid, s)) && emp */

    int first_count = cm_stmt_code_count_context(
        program, fid, fn, stmt->a) /*@ where policy = policy, cg = cg, p = p, f = f, body = body, next = next, functions_ptr = functions_ptr, s = cm_stmt_first(s), loop_ = loop_ */;
  /*@ exists (count_value : Z), count_value == cm_stmt_code_count(policy, p, fid, cm_stmt_first(s)) && data_at(&first_count, int, count_value)
      which implies data_at(&first_count, int, cm_stmt_code_count(policy, p, fid, cm_stmt_first(s))) */
  /*@ s == CMSeqS(cm_stmt_first(s), cm_stmt_second(s)) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_emit_stmt(policy, p, fid, pc, temp, break_pc, continue_pc, s), tail))
      which implies s == CMSeqS(cm_stmt_first(s), cm_stmt_second(s)) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_emit_stmt(policy, p, fid, pc, temp, break_pc, continue_pc, cm_stmt_first(s)), app(cm_emit_stmt(policy, p, fid, pc + cm_stmt_code_count(policy, p, fid, cm_stmt_first(s)), temp, break_pc, continue_pc, cm_stmt_second(s)), tail))) */
    cmc_emit_stmt(program, fid, fn, pc, temp, temp_limit,
                 break_pc, continue_pc, stmt->a, emitter) /*@ where policy = policy, cg = cg, p = p, f = f, body = body, next = next, functions_ptr = functions_ptr, s = cm_stmt_first(s), loop_ = loop_, done = done, tail = app(cm_emit_stmt(policy, p, fid, pc + cm_stmt_code_count(policy, p, fid, cm_stmt_first(s)), temp, break_pc, continue_pc, cm_stmt_second(s)), tail), out = out, capacity = capacity */;
    int second_pc = pc + first_count;
  
    cmc_emit_stmt(program, fid, fn, second_pc, temp, temp_limit,
                 break_pc, continue_pc, stmt->b, emitter) /*@ where policy = policy, cg = cg, p = p, f = f, body = body, next = next, functions_ptr = functions_ptr, s = cm_stmt_second(s), loop_ = loop_, done = app(done, cm_emit_stmt(policy, p, fid, pc, temp, break_pc, continue_pc, cm_stmt_first(s))), tail = tail, out = out, capacity = capacity */;

  /*@ s == CMSeqS(cm_stmt_first(s), cm_stmt_second(s)) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(app(done, cm_emit_stmt(policy, p, fid, pc, temp, break_pc, continue_pc, cm_stmt_first(s))), cm_emit_stmt(policy, p, fid, pc + cm_stmt_code_count(policy, p, fid, cm_stmt_first(s)), temp, break_pc, continue_pc, cm_stmt_second(s))), tail)
      which implies s == CMSeqS(cm_stmt_first(s), cm_stmt_second(s)) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cm_emit_stmt(policy, p, fid, pc, temp, break_pc, continue_pc, s)), tail) */
  /*@ exists (xe : Z) (xa : Z) (xb : Z), stmt != 0 && data_at(&(stmt->kind), int, cm_rep_stmt_kind(s)) * data_at(&(stmt->slot), int, cm_rep_stmt_slot(s)) * data_at(&(stmt->expr), struct cm_expr *, xe) * data_at(&(stmt->a), struct cm_stmt *, xa) * data_at(&(stmt->b), struct cm_stmt *, xb) * (s == CMSeqS(cm_stmt_first(s), cm_stmt_second(s)) && xe == 0 && cm_stmt_rep(xa, cm_stmt_first(s)) * cm_stmt_rep(xb, cm_stmt_second(s)))
      which implies cm_stmt_rep(stmt, s) */
  
  } else if (stmt->kind == CMC_STMT_BLOCK) {
  /*@ exists (xe : Z) (xa : Z) (xb : Z), stmt != 0 && data_at(&(stmt->kind), int, cm_rep_stmt_kind(s)) * data_at(&(stmt->slot), int, cm_rep_stmt_slot(s)) * data_at(&(stmt->expr), struct cm_expr *, xe) * data_at(&(stmt->a), struct cm_stmt *, xa) * data_at(&(stmt->b), struct cm_stmt *, xb) * (cm_rep_stmt_kind(s) == 5 && cm_stmt_payload(s, xe, xa, xb))
      which implies exists (xe : Z) (xa : Z) (xb : Z), stmt != 0 && data_at(&(stmt->kind), int, cm_rep_stmt_kind(s)) * data_at(&(stmt->slot), int, cm_rep_stmt_slot(s)) * data_at(&(stmt->expr), struct cm_expr *, xe) * data_at(&(stmt->a), struct cm_stmt *, xa) * data_at(&(stmt->b), struct cm_stmt *, xb) * (s == CMBlockS(cm_stmt_first(s)) && xe == 0 && xa != 0 && xb == 0 && cm_stmt_rep(xa, cm_stmt_first(s))) */
  /*@ s == CMBlockS(cm_stmt_first(s)) && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) && f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_stmt_wf(policy, p, f, loop_, s) && cm_stmt_counts_representable(policy, p, fid, s) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 0 <= temp && temp <= temp_limit && temp + cm_stemps(s) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) && cm_i32_code_count(break_pc) && cm_i32_code_count(continue_pc) &&
 cm_i32_code_count(pc + Zlength(cm_emit_stmt(policy, p, fid, pc, temp, break_pc, continue_pc, s))) && emp
      which implies s == CMBlockS(cm_stmt_first(s)) && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) && f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_stmt_wf(policy, p, f, loop_, s) && cm_stmt_counts_representable(policy, p, fid, s) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 0 <= temp && temp <= temp_limit && temp + cm_stemps(s) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) && cm_i32_code_count(break_pc) && cm_i32_code_count(continue_pc) &&
 cm_i32_code_count(pc + Zlength(cm_emit_stmt(policy, p, fid, pc, temp, break_pc, continue_pc, s))) && cm_stmt_wf(policy, p, f, loop_, cm_stmt_first(s)) && cm_stmt_counts_representable(policy, p, fid, cm_stmt_first(s)) && temp + cm_stemps(cm_stmt_first(s)) <= temp_limit && cm_i32_code_count(pc) && cm_i32_code_count(break_pc) && cm_i32_code_count(continue_pc) && cm_i32_code_count((pc) + Zlength(cm_emit_stmt(policy, p, fid, pc, temp, break_pc, continue_pc, cm_stmt_first(s)))) && cm_i32_code_count(pc + cm_stmt_code_count(policy, p, fid, s)) && emp */

  /*@ s == CMBlockS(cm_stmt_first(s)) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_emit_stmt(policy, p, fid, pc, temp, break_pc, continue_pc, s), tail))
      which implies s == CMBlockS(cm_stmt_first(s)) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_emit_stmt(policy, p, fid, pc, temp, break_pc, continue_pc, cm_stmt_first(s)), tail)) */
    cmc_emit_stmt(program, fid, fn, pc, temp, temp_limit,
                 break_pc, continue_pc, stmt->a, emitter) /*@ where policy = policy, cg = cg, p = p, f = f, body = body, next = next, functions_ptr = functions_ptr, s = cm_stmt_first(s), loop_ = loop_, done = done, tail = tail, out = out, capacity = capacity */;

  /*@ s == CMBlockS(cm_stmt_first(s)) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cm_emit_stmt(policy, p, fid, pc, temp, break_pc, continue_pc, cm_stmt_first(s))), tail)
      which implies s == CMBlockS(cm_stmt_first(s)) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cm_emit_stmt(policy, p, fid, pc, temp, break_pc, continue_pc, s)), tail) */
  /*@ exists (xe : Z) (xa : Z) (xb : Z), stmt != 0 && data_at(&(stmt->kind), int, cm_rep_stmt_kind(s)) * data_at(&(stmt->slot), int, cm_rep_stmt_slot(s)) * data_at(&(stmt->expr), struct cm_expr *, xe) * data_at(&(stmt->a), struct cm_stmt *, xa) * data_at(&(stmt->b), struct cm_stmt *, xb) * (s == CMBlockS(cm_stmt_first(s)) && xe == 0 && xa != 0 && xb == 0 && cm_stmt_rep(xa, cm_stmt_first(s)))
      which implies cm_stmt_rep(stmt, s) */
  
  } else if (stmt->kind == CMC_STMT_IF) {
  /*@ cm_rep_stmt_kind(s) == 6 && emp
      which implies s == CMIfS(cm_stmt_expr(s), cm_stmt_first(s), cm_stmt_second(s)) && emp */
  /*@ exists (xe : Z) (xa : Z) (xb : Z), stmt != 0 && data_at(&(stmt->kind), int, cm_rep_stmt_kind(s)) * data_at(&(stmt->slot), int, cm_rep_stmt_slot(s)) * data_at(&(stmt->expr), struct cm_expr *, xe) * data_at(&(stmt->a), struct cm_stmt *, xa) * data_at(&(stmt->b), struct cm_stmt *, xb) * cm_stmt_payload(s, xe, xa, xb)
      which implies cm_stmt_rep(stmt, s) */

    cmc_emit_if_stmt(program, fid, fn, pc, temp, temp_limit,
                     break_pc, continue_pc, stmt, emitter) /*@ where policy = policy, cg = cg, p = p, f = f, body = body, next = next, functions_ptr = functions_ptr, s = s, loop_ = loop_, guard_ = cm_stmt_expr(s), yes_ = cm_stmt_first(s), no_ = cm_stmt_second(s), done = done, tail = tail, out = out, capacity = capacity */;
  } else if (stmt->kind == CMC_STMT_WHILE) {
  /*@ exists (xe : Z) (xa : Z) (xb : Z), stmt != 0 && data_at(&(stmt->kind), int, cm_rep_stmt_kind(s)) * data_at(&(stmt->slot), int, cm_rep_stmt_slot(s)) * data_at(&(stmt->expr), struct cm_expr *, xe) * data_at(&(stmt->a), struct cm_stmt *, xa) * data_at(&(stmt->b), struct cm_stmt *, xb) * (cm_rep_stmt_kind(s) == 7 && cm_stmt_payload(s, xe, xa, xb))
      which implies exists (xe : Z) (xa : Z) (xb : Z), stmt != 0 && data_at(&(stmt->kind), int, cm_rep_stmt_kind(s)) * data_at(&(stmt->slot), int, cm_rep_stmt_slot(s)) * data_at(&(stmt->expr), struct cm_expr *, xe) * data_at(&(stmt->a), struct cm_stmt *, xa) * data_at(&(stmt->b), struct cm_stmt *, xb) * (s == CMWhileS(cm_stmt_expr(s), cm_stmt_first(s)) && xe != 0 && xa != 0 && xb == 0 && cm_expr_rep(xe, cm_stmt_expr(s)) * cm_stmt_rep(xa, cm_stmt_first(s))) */
  /*@ s == CMWhileS(cm_stmt_expr(s), cm_stmt_first(s)) && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) && f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_stmt_wf(policy, p, f, loop_, s) && cm_stmt_counts_representable(policy, p, fid, s) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 0 <= temp && temp <= temp_limit && temp + cm_stemps(s) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) && cm_i32_code_count(break_pc) && cm_i32_code_count(continue_pc) &&
 cm_i32_code_count(pc + Zlength(cm_emit_stmt(policy, p, fid, pc, temp, break_pc, continue_pc, s))) && emp
      which implies s == CMWhileS(cm_stmt_expr(s), cm_stmt_first(s)) && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) && f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_stmt_wf(policy, p, f, loop_, s) && cm_stmt_counts_representable(policy, p, fid, s) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 0 <= temp && temp <= temp_limit && temp + cm_stemps(s) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) && cm_i32_code_count(break_pc) && cm_i32_code_count(continue_pc) &&
 cm_i32_code_count(pc + Zlength(cm_emit_stmt(policy, p, fid, pc, temp, break_pc, continue_pc, s))) && cm_expr_wf(policy, p, f, cm_stmt_expr(s)) && cm_expr_counts_representable(policy, p, fid, cm_stmt_expr(s)) && temp + cm_expr_temps_for(cm_stmt_expr(s), 0) <= temp_limit && cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, cm_stmt_expr(s), 0))) && cm_stmt_wf(policy, p, f, true, cm_stmt_first(s)) && cm_stmt_counts_representable(policy, p, fid, cm_stmt_first(s)) && temp + cm_stemps(cm_stmt_first(s)) <= temp_limit && cm_i32_code_count(pc + cm_rvalue_code_count(policy, p, fid, cm_stmt_expr(s)) + 1) && cm_i32_code_count(pc + cm_stmt_code_count(policy, p, fid, CMWhileS(cm_stmt_expr(s), cm_stmt_first(s)))) && cm_i32_code_count(pc) && cm_i32_code_count((pc + cm_rvalue_code_count(policy, p, fid, cm_stmt_expr(s)) + 1) + Zlength(cm_emit_stmt(policy, p, fid, pc + cm_rvalue_code_count(policy, p, fid, cm_stmt_expr(s)) + 1, temp, pc + cm_stmt_code_count(policy, p, fid, CMWhileS(cm_stmt_expr(s), cm_stmt_first(s))), pc, cm_stmt_first(s)))) && cm_i32_code_count(pc + cm_stmt_code_count(policy, p, fid, s)) && tvm_opcode_code(TVMJzOp) == 20 && tvm_opcode_code(TVMJzOp) != 22 && tvm_opcode_code(TVMJmpOp) == 19 && tvm_opcode_code(TVMJmpOp) != 22 && emp */

    int guard_count = cm_expr_rvalue_count_context(
        program, fid, fn, stmt->expr) /*@ where policy = policy, cg = cg, p = p, f = f, body = body, next = next, functions_ptr = functions_ptr, e = cm_stmt_expr(s) */;
  /*@ exists (count_value : Z), count_value == cm_rvalue_code_count(policy, p, fid, cm_stmt_expr(s)) && data_at(&guard_count, int, count_value)
      which implies data_at(&guard_count, int, cm_rvalue_code_count(policy, p, fid, cm_stmt_expr(s))) */
    int body_count = cm_stmt_code_count_context(
        program, fid, fn, stmt->a) /*@ where policy = policy, cg = cg, p = p, f = f, body = body, next = next, functions_ptr = functions_ptr, s = cm_stmt_first(s), loop_ = true */;
  /*@ exists (count_value : Z), count_value == cm_stmt_code_count(policy, p, fid, cm_stmt_first(s)) && data_at(&body_count, int, count_value)
      which implies data_at(&body_count, int, cm_stmt_code_count(policy, p, fid, cm_stmt_first(s))) */
    int body_pc = pc + (guard_count + 1);
    int loop_end = pc + (guard_count + (1 + (body_count + 1)));
  /*@ break_pc == break_pc@pre && continue_pc == continue_pc@pre && s == CMWhileS(cm_stmt_expr(s), cm_stmt_first(s)) && guard_count == cm_rvalue_code_count(policy, p, fid, cm_stmt_expr(s)) && body_count == cm_stmt_code_count(policy, p, fid, cm_stmt_first(s)) && body_pc == pc + guard_count + 1 && loop_end == pc + guard_count + body_count + 2 && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_emit_stmt(policy, p, fid, pc, temp, break_pc, continue_pc, s), tail))
      which implies break_pc == break_pc@pre && continue_pc == continue_pc@pre && s == CMWhileS(cm_stmt_expr(s), cm_stmt_first(s)) && guard_count == cm_rvalue_code_count(policy, p, fid, cm_stmt_expr(s)) && body_count == cm_stmt_code_count(policy, p, fid, cm_stmt_first(s)) && body_pc == pc + guard_count + 1 && loop_end == pc + guard_count + body_count + 2 && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_expr_code_for(policy, p, fid, pc, temp, cm_stmt_expr(s), 0), app(cons(TVMInst(TVMJzOp, loop_end), nil), app(cm_emit_stmt(policy, p, fid, body_pc, temp, loop_end, pc, cm_stmt_first(s)), app(cons(TVMInst(TVMJmpOp, pc), nil), tail))))) */
    cm_emit_expr(program, fid, fn, pc, temp, temp_limit,
                 stmt->expr, 0, emitter) /*@ where policy = policy, cg = cg, p = p, f = f, body = body, next = next, functions_ptr = functions_ptr, e = cm_stmt_expr(s), done = done, tail = app(cons(TVMInst(TVMJzOp, loop_end), nil), app(cm_emit_stmt(policy, p, fid, body_pc, temp, loop_end, pc, cm_stmt_first(s)), app(cons(TVMInst(TVMJmpOp, pc), nil), tail))), out = out, capacity = capacity */;
  /*@ s == CMWhileS(cm_stmt_expr(s), cm_stmt_first(s)) && guard_count == cm_rvalue_code_count(policy, p, fid, cm_stmt_expr(s)) && body_count == cm_stmt_code_count(policy, p, fid, cm_stmt_first(s)) && body_pc == pc + guard_count + 1 && loop_end == pc + guard_count + body_count + 2 && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cm_expr_code_for(policy, p, fid, pc, temp, cm_stmt_expr(s), 0)), app(cons(TVMInst(TVMJzOp, loop_end), nil), app(cm_emit_stmt(policy, p, fid, body_pc, temp, loop_end, pc, cm_stmt_first(s)), app(cons(TVMInst(TVMJmpOp, pc), nil), tail))))
      which implies s == CMWhileS(cm_stmt_expr(s), cm_stmt_first(s)) && guard_count == cm_rvalue_code_count(policy, p, fid, cm_stmt_expr(s)) && body_count == cm_stmt_code_count(policy, p, fid, cm_stmt_first(s)) && body_pc == pc + guard_count + 1 && loop_end == pc + guard_count + body_count + 2 && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cm_expr_code_for(policy, p, fid, pc, temp, cm_stmt_expr(s), 0)), cons(TVMInst(TVMJzOp, loop_end), app(cm_emit_stmt(policy, p, fid, body_pc, temp, loop_end, pc, cm_stmt_first(s)), app(cons(TVMInst(TVMJmpOp, pc), nil), tail)))) */
    cm_emit_plan(emitter, CMC_OP_JZ, (long long)loop_end) /*@ where policy = policy, p = p, out = out, capacity = capacity, opcode = TVMJzOp, done = app(done, cm_expr_code_for(policy, p, fid, pc, temp, cm_stmt_expr(s), 0)), tail = app(cm_emit_stmt(policy, p, fid, body_pc, temp, loop_end, pc, cm_stmt_first(s)), app(cons(TVMInst(TVMJmpOp, pc), nil), tail)) */;
  
    cmc_emit_stmt(program, fid, fn, body_pc, temp, temp_limit,
                 loop_end, pc, stmt->a, emitter) /*@ where policy = policy, cg = cg, p = p, f = f, body = body, next = next, functions_ptr = functions_ptr, s = cm_stmt_first(s), loop_ = true, done = app(app(done, cm_expr_code_for(policy, p, fid, pc, temp, cm_stmt_expr(s), 0)), cons(TVMInst(TVMJzOp, loop_end), nil)), tail = app(cons(TVMInst(TVMJmpOp, pc), nil), tail), out = out, capacity = capacity */;
  /*@ s == CMWhileS(cm_stmt_expr(s), cm_stmt_first(s)) && guard_count == cm_rvalue_code_count(policy, p, fid, cm_stmt_expr(s)) && body_count == cm_stmt_code_count(policy, p, fid, cm_stmt_first(s)) && body_pc == pc + guard_count + 1 && loop_end == pc + guard_count + body_count + 2 && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(app(app(done, cm_expr_code_for(policy, p, fid, pc, temp, cm_stmt_expr(s), 0)), cons(TVMInst(TVMJzOp, loop_end), nil)), cm_emit_stmt(policy, p, fid, body_pc, temp, loop_end, pc, cm_stmt_first(s))), app(cons(TVMInst(TVMJmpOp, pc), nil), tail))
      which implies s == CMWhileS(cm_stmt_expr(s), cm_stmt_first(s)) && guard_count == cm_rvalue_code_count(policy, p, fid, cm_stmt_expr(s)) && body_count == cm_stmt_code_count(policy, p, fid, cm_stmt_first(s)) && body_pc == pc + guard_count + 1 && loop_end == pc + guard_count + body_count + 2 && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(app(app(done, cm_expr_code_for(policy, p, fid, pc, temp, cm_stmt_expr(s), 0)), cons(TVMInst(TVMJzOp, loop_end), nil)), cm_emit_stmt(policy, p, fid, body_pc, temp, loop_end, pc, cm_stmt_first(s))), cons(TVMInst(TVMJmpOp, pc), tail)) */
    cm_emit_plan(emitter, CMC_OP_JMP, (long long)pc) /*@ where policy = policy, p = p, out = out, capacity = capacity, opcode = TVMJmpOp, done = app(app(app(done, cm_expr_code_for(policy, p, fid, pc, temp, cm_stmt_expr(s), 0)), cons(TVMInst(TVMJzOp, loop_end), nil)), cm_emit_stmt(policy, p, fid, body_pc, temp, loop_end, pc, cm_stmt_first(s))), tail = tail */;

  /*@ break_pc == break_pc@pre && continue_pc == continue_pc@pre && s == CMWhileS(cm_stmt_expr(s), cm_stmt_first(s)) && guard_count == cm_rvalue_code_count(policy, p, fid, cm_stmt_expr(s)) && body_count == cm_stmt_code_count(policy, p, fid, cm_stmt_first(s)) && body_pc == pc + guard_count + 1 && loop_end == pc + guard_count + body_count + 2 && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(app(app(app(done, cm_expr_code_for(policy, p, fid, pc, temp, cm_stmt_expr(s), 0)), cons(TVMInst(TVMJzOp, loop_end), nil)), cm_emit_stmt(policy, p, fid, body_pc, temp, loop_end, pc, cm_stmt_first(s))), cons(TVMInst(TVMJmpOp, pc), nil)), tail)
      which implies break_pc == break_pc@pre && continue_pc == continue_pc@pre && s == CMWhileS(cm_stmt_expr(s), cm_stmt_first(s)) && guard_count == cm_rvalue_code_count(policy, p, fid, cm_stmt_expr(s)) && body_count == cm_stmt_code_count(policy, p, fid, cm_stmt_first(s)) && body_pc == pc + guard_count + 1 && loop_end == pc + guard_count + body_count + 2 && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cm_emit_stmt(policy, p, fid, pc, temp, break_pc, continue_pc, s)), tail) */
  /*@ exists (xe : Z) (xa : Z) (xb : Z), stmt != 0 && data_at(&(stmt->kind), int, cm_rep_stmt_kind(s)) * data_at(&(stmt->slot), int, cm_rep_stmt_slot(s)) * data_at(&(stmt->expr), struct cm_expr *, xe) * data_at(&(stmt->a), struct cm_stmt *, xa) * data_at(&(stmt->b), struct cm_stmt *, xb) * (s == CMWhileS(cm_stmt_expr(s), cm_stmt_first(s)) && xe != 0 && xa != 0 && xb == 0 && cm_expr_rep(xe, cm_stmt_expr(s)) * cm_stmt_rep(xa, cm_stmt_first(s)))
      which implies cm_stmt_rep(stmt, s) */
  
  } else if (stmt->kind == CMC_STMT_BREAK) {
  /*@ exists (xe : Z) (xa : Z) (xb : Z), stmt != 0 && data_at(&(stmt->kind), int, cm_rep_stmt_kind(s)) * data_at(&(stmt->slot), int, cm_rep_stmt_slot(s)) * data_at(&(stmt->expr), struct cm_expr *, xe) * data_at(&(stmt->a), struct cm_stmt *, xa) * data_at(&(stmt->b), struct cm_stmt *, xb) * (cm_rep_stmt_kind(s) == 8 && cm_stmt_payload(s, xe, xa, xb))
      which implies exists (xe : Z) (xa : Z) (xb : Z), stmt != 0 && data_at(&(stmt->kind), int, cm_rep_stmt_kind(s)) * data_at(&(stmt->slot), int, cm_rep_stmt_slot(s)) * data_at(&(stmt->expr), struct cm_expr *, xe) * data_at(&(stmt->a), struct cm_stmt *, xa) * data_at(&(stmt->b), struct cm_stmt *, xb) * (s == CMBreakS && xe == 0 && xa == 0 && xb == 0 && emp) */
  /*@ s == CMBreakS && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) && f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_stmt_wf(policy, p, f, loop_, s) && cm_stmt_counts_representable(policy, p, fid, s) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 0 <= temp && temp <= temp_limit && temp + cm_stemps(s) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) && cm_i32_code_count(break_pc) && cm_i32_code_count(continue_pc) &&
 cm_i32_code_count(pc + Zlength(cm_emit_stmt(policy, p, fid, pc, temp, break_pc, continue_pc, s))) && emp
      which implies s == CMBreakS && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) && f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_stmt_wf(policy, p, f, loop_, s) && cm_stmt_counts_representable(policy, p, fid, s) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 0 <= temp && temp <= temp_limit && temp + cm_stemps(s) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) && cm_i32_code_count(break_pc) && cm_i32_code_count(continue_pc) &&
 cm_i32_code_count(pc + Zlength(cm_emit_stmt(policy, p, fid, pc, temp, break_pc, continue_pc, s))) && cm_i32_code_count(pc + cm_stmt_code_count(policy, p, fid, s)) && tvm_opcode_code(TVMJmpOp) == 19 && tvm_opcode_code(TVMJmpOp) != 22 && emp */

  /*@ fid == fid@pre && pc == pc@pre && temp == temp@pre && continue_pc == continue_pc@pre && s == CMBreakS && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_emit_stmt(policy, p, fid, pc, temp, break_pc, continue_pc, s), tail))
      which implies fid == fid@pre && pc == pc@pre && temp == temp@pre && continue_pc == continue_pc@pre && s == CMBreakS && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, cons(TVMInst(TVMJmpOp, break_pc), tail)) */
    cm_emit_plan(emitter, CMC_OP_JMP, (long long)break_pc) /*@ where policy = policy, p = p, out = out, capacity = capacity, opcode = TVMJmpOp, done = done, tail = tail */;

  /*@ fid == fid@pre && pc == pc@pre && temp == temp@pre && continue_pc == continue_pc@pre && s == CMBreakS && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cons(TVMInst(TVMJmpOp, break_pc), nil)), tail)
      which implies fid == fid@pre && pc == pc@pre && temp == temp@pre && continue_pc == continue_pc@pre && s == CMBreakS && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cm_emit_stmt(policy, p, fid, pc, temp, break_pc, continue_pc, s)), tail) */
  /*@ exists (xe : Z) (xa : Z) (xb : Z), stmt != 0 && data_at(&(stmt->kind), int, cm_rep_stmt_kind(s)) * data_at(&(stmt->slot), int, cm_rep_stmt_slot(s)) * data_at(&(stmt->expr), struct cm_expr *, xe) * data_at(&(stmt->a), struct cm_stmt *, xa) * data_at(&(stmt->b), struct cm_stmt *, xb) * (s == CMBreakS && xe == 0 && xa == 0 && xb == 0 && emp)
      which implies cm_stmt_rep(stmt, s) */
  
  } else if (stmt->kind == CMC_STMT_CONTINUE) {
  /*@ exists (xe : Z) (xa : Z) (xb : Z), stmt != 0 && data_at(&(stmt->kind), int, cm_rep_stmt_kind(s)) * data_at(&(stmt->slot), int, cm_rep_stmt_slot(s)) * data_at(&(stmt->expr), struct cm_expr *, xe) * data_at(&(stmt->a), struct cm_stmt *, xa) * data_at(&(stmt->b), struct cm_stmt *, xb) * (cm_rep_stmt_kind(s) == 9 && cm_stmt_payload(s, xe, xa, xb))
      which implies exists (xe : Z) (xa : Z) (xb : Z), stmt != 0 && data_at(&(stmt->kind), int, cm_rep_stmt_kind(s)) * data_at(&(stmt->slot), int, cm_rep_stmt_slot(s)) * data_at(&(stmt->expr), struct cm_expr *, xe) * data_at(&(stmt->a), struct cm_stmt *, xa) * data_at(&(stmt->b), struct cm_stmt *, xb) * (s == CMContinueS && xe == 0 && xa == 0 && xb == 0 && emp) */
  /*@ s == CMContinueS && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) && f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_stmt_wf(policy, p, f, loop_, s) && cm_stmt_counts_representable(policy, p, fid, s) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 0 <= temp && temp <= temp_limit && temp + cm_stemps(s) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) && cm_i32_code_count(break_pc) && cm_i32_code_count(continue_pc) &&
 cm_i32_code_count(pc + Zlength(cm_emit_stmt(policy, p, fid, pc, temp, break_pc, continue_pc, s))) && emp
      which implies s == CMContinueS && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) && f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_stmt_wf(policy, p, f, loop_, s) && cm_stmt_counts_representable(policy, p, fid, s) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 0 <= temp && temp <= temp_limit && temp + cm_stemps(s) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) && cm_i32_code_count(break_pc) && cm_i32_code_count(continue_pc) &&
 cm_i32_code_count(pc + Zlength(cm_emit_stmt(policy, p, fid, pc, temp, break_pc, continue_pc, s))) && cm_i32_code_count(pc + cm_stmt_code_count(policy, p, fid, s)) && tvm_opcode_code(TVMJmpOp) == 19 && tvm_opcode_code(TVMJmpOp) != 22 && emp */

  /*@ fid == fid@pre && pc == pc@pre && temp == temp@pre && break_pc == break_pc@pre && s == CMContinueS && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_emit_stmt(policy, p, fid, pc, temp, break_pc, continue_pc, s), tail))
      which implies fid == fid@pre && pc == pc@pre && temp == temp@pre && break_pc == break_pc@pre && s == CMContinueS && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, cons(TVMInst(TVMJmpOp, continue_pc), tail)) */
    cm_emit_plan(emitter, CMC_OP_JMP, (long long)continue_pc) /*@ where policy = policy, p = p, out = out, capacity = capacity, opcode = TVMJmpOp, done = done, tail = tail */;

  /*@ fid == fid@pre && pc == pc@pre && temp == temp@pre && break_pc == break_pc@pre && s == CMContinueS && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cons(TVMInst(TVMJmpOp, continue_pc), nil)), tail)
      which implies fid == fid@pre && pc == pc@pre && temp == temp@pre && break_pc == break_pc@pre && s == CMContinueS && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cm_emit_stmt(policy, p, fid, pc, temp, break_pc, continue_pc, s)), tail) */
  /*@ exists (xe : Z) (xa : Z) (xb : Z), stmt != 0 && data_at(&(stmt->kind), int, cm_rep_stmt_kind(s)) * data_at(&(stmt->slot), int, cm_rep_stmt_slot(s)) * data_at(&(stmt->expr), struct cm_expr *, xe) * data_at(&(stmt->a), struct cm_stmt *, xa) * data_at(&(stmt->b), struct cm_stmt *, xb) * (s == CMContinueS && xe == 0 && xa == 0 && xb == 0 && emp)
      which implies cm_stmt_rep(stmt, s) */
  
  } else {
  /*@ exists (xe : Z) (xa : Z) (xb : Z), stmt != 0 && data_at(&(stmt->kind), int, cm_rep_stmt_kind(s)) * data_at(&(stmt->slot), int, cm_rep_stmt_slot(s)) * data_at(&(stmt->expr), struct cm_expr *, xe) * data_at(&(stmt->a), struct cm_stmt *, xa) * data_at(&(stmt->b), struct cm_stmt *, xb) * (cm_rep_stmt_kind(s) != 0 && cm_rep_stmt_kind(s) != 1 && cm_rep_stmt_kind(s) != 2 && cm_rep_stmt_kind(s) != 3 && cm_rep_stmt_kind(s) != 4 && cm_rep_stmt_kind(s) != 5 && cm_rep_stmt_kind(s) != 6 && cm_rep_stmt_kind(s) != 7 && cm_rep_stmt_kind(s) != 8 && cm_rep_stmt_kind(s) != 9 && cm_stmt_payload(s, xe, xa, xb))
      which implies exists (xe : Z) (xa : Z) (xb : Z), stmt != 0 && data_at(&(stmt->kind), int, cm_rep_stmt_kind(s)) * data_at(&(stmt->slot), int, cm_rep_stmt_slot(s)) * data_at(&(stmt->expr), struct cm_expr *, xe) * data_at(&(stmt->a), struct cm_stmt *, xa) * data_at(&(stmt->b), struct cm_stmt *, xb) * (s == CMReturnS(cm_stmt_expr(s)) && xe != 0 && xa == 0 && xb == 0 && cm_expr_rep(xe, cm_stmt_expr(s))) */
  /*@ s == CMReturnS(cm_stmt_expr(s)) && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) && f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_stmt_wf(policy, p, f, loop_, s) && cm_stmt_counts_representable(policy, p, fid, s) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 0 <= temp && temp <= temp_limit && temp + cm_stemps(s) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) && cm_i32_code_count(break_pc) && cm_i32_code_count(continue_pc) &&
 cm_i32_code_count(pc + Zlength(cm_emit_stmt(policy, p, fid, pc, temp, break_pc, continue_pc, s))) && emp
      which implies s == CMReturnS(cm_stmt_expr(s)) && cm_wf_program(policy, cg, p) && cm_typed_program(policy, p) && f == cm_function_at(policy, fid, cm_program_functions(p)) &&
 cm_stmt_wf(policy, p, f, loop_, s) && cm_stmt_counts_representable(policy, p, fid, s) &&
 cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) &&
 cm_rep_structs_safe(cm_program_structs(p)) && cm_rep_globals_safe(cm_program_globals(p)) && cm_rep_strings_safe(cm_program_strings(p)) &&
 cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) &&
 cm_rep_globals_size(cm_program_globals(p)) + cm_rep_strings_size(cm_program_strings(p)) <= 1048560 &&
 0 <= temp && temp <= temp_limit && temp + cm_stemps(s) <= temp_limit &&
 cm_temp_offset(policy, p, fid, temp_limit) <= 2147483647 && cm_i32_code_count(pc) && cm_i32_code_count(break_pc) && cm_i32_code_count(continue_pc) &&
 cm_i32_code_count(pc + Zlength(cm_emit_stmt(policy, p, fid, pc, temp, break_pc, continue_pc, s))) && cm_expr_wf(policy, p, f, cm_stmt_expr(s)) && cm_expr_counts_representable(policy, p, fid, cm_stmt_expr(s)) && temp + cm_expr_temps_for(cm_stmt_expr(s), 0) <= temp_limit && cm_i32_code_count(pc + Zlength(cm_expr_code_for(policy, p, fid, pc, temp, cm_stmt_expr(s), 0))) && cm_i32_code_count(pc + cm_stmt_code_count(policy, p, fid, s)) && cm_type_code_wf(cm_function_ret(f)) && emp */

      /*@ cm_function_context_rep(fn, f, body, next)
      which implies exists (zp : Z) (zl : Z), fn != 0 && data_at(&(fn->ret_ty), int, cm_type_encode(cm_function_ret(f))) * data_at(&(fn->params), struct cm_slot *, zp) * data_at(&(fn->locals), struct cm_slot *, zl) * data_at(&(fn->body), struct cm_stmt *, body) * data_at(&(fn->next), struct cm_function *, next) * cm_slot_list_rep(zp, cm_function_params(f)) * cm_slot_list_rep(zl, cm_function_locals(f)) */
    int return_ty = fn->ret_ty;
  /*@ exists (zp : Z) (zl : Z), fn != 0 && data_at(&(fn->ret_ty), int, cm_type_encode(cm_function_ret(f))) * data_at(&(fn->params), struct cm_slot *, zp) * data_at(&(fn->locals), struct cm_slot *, zl) * data_at(&(fn->body), struct cm_stmt *, body) * data_at(&(fn->next), struct cm_function *, next) * cm_slot_list_rep(zp, cm_function_params(f)) * cm_slot_list_rep(zl, cm_function_locals(f))
      which implies cm_function_context_rep(fn, f, body, next) */

  /*@ break_pc == break_pc@pre && continue_pc == continue_pc@pre && s == CMReturnS(cm_stmt_expr(s)) && f == cm_function_at(policy, fid, cm_program_functions(p)) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_emit_stmt(policy, p, fid, pc, temp, break_pc, continue_pc, s), tail))
      which implies break_pc == break_pc@pre && continue_pc == continue_pc@pre && s == CMReturnS(cm_stmt_expr(s)) && f == cm_function_at(policy, fid, cm_program_functions(p)) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_expr_code_for(policy, p, fid, pc, temp, cm_stmt_expr(s), 0), app(cm_char_normalize_code(cm_function_ret(f)), app(cm_return_epilogue, tail)))) */
    cm_emit_expr(program, fid, fn, pc, temp, temp_limit,
                 stmt->expr, 0, emitter) /*@ where policy = policy, cg = cg, p = p, f = f, body = body, next = next, functions_ptr = functions_ptr, e = cm_stmt_expr(s), done = done, tail = app(cm_char_normalize_code(cm_function_ret(f)), app(cm_return_epilogue, tail)), out = out, capacity = capacity */;
  
    cm_emit_normalize_plan(emitter, return_ty) /*@ where policy = policy, p = p, out = out, capacity = capacity, model_ty = cm_function_ret(f), done = app(done, cm_expr_code_for(policy, p, fid, pc, temp, cm_stmt_expr(s), 0)), tail = app(cm_return_epilogue, tail) */;
  
    cm_emit_return_epilogue_plan(emitter) /*@ where policy = policy, p = p, out = out, capacity = capacity, done = app(app(done, cm_expr_code_for(policy, p, fid, pc, temp, cm_stmt_expr(s), 0)), cm_char_normalize_code(cm_function_ret(f))), tail = tail */;

  /*@ break_pc == break_pc@pre && continue_pc == continue_pc@pre && s == CMReturnS(cm_stmt_expr(s)) && f == cm_function_at(policy, fid, cm_program_functions(p)) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(app(app(done, cm_expr_code_for(policy, p, fid, pc, temp, cm_stmt_expr(s), 0)), cm_char_normalize_code(cm_function_ret(f))), cm_return_epilogue), tail)
      which implies break_pc == break_pc@pre && continue_pc == continue_pc@pre && s == CMReturnS(cm_stmt_expr(s)) && f == cm_function_at(policy, fid, cm_program_functions(p)) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cm_emit_stmt(policy, p, fid, pc, temp, break_pc, continue_pc, s)), tail) */
  /*@ exists (xe : Z) (xa : Z) (xb : Z), stmt != 0 && data_at(&(stmt->kind), int, cm_rep_stmt_kind(s)) * data_at(&(stmt->slot), int, cm_rep_stmt_slot(s)) * data_at(&(stmt->expr), struct cm_expr *, xe) * data_at(&(stmt->a), struct cm_stmt *, xa) * data_at(&(stmt->b), struct cm_stmt *, xb) * (s == CMReturnS(cm_stmt_expr(s)) && xe != 0 && xa == 0 && xb == 0 && cm_expr_rep(xe, cm_stmt_expr(s)))
      which implies cm_stmt_rep(stmt, s) */
  
  }
}
