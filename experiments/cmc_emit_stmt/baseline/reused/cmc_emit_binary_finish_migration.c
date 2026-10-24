#include "cmc_layout_migration_abi.h"
struct cm_emitter { struct cm_output *output; int pc; };

/*@ Extern Coq
 (cm_type :: *) (cm_expr :: *) (cm_program :: *) (cm_function_d :: *)
 (cm_struct_d :: *) (cm_slot_d :: *) (cm_lookup_policy :: *) (tvm_inst :: *) (tvm_opcode :: *)
*/
/*@ Extern Coq
 (cm_expr_type : cm_expr -> cm_type)
 (cm_type_encode : cm_type -> Z)
 (cm_type_code_wf : cm_type -> Prop)
 (cm_type_refs : list cm_struct_d -> cm_type -> Prop)
 (cm_type_size : list cm_struct_d -> cm_type -> Z)
 (cm_typed_program : cm_lookup_policy -> cm_program -> Prop)
 (cm_i32_code_count : Z -> Prop)
 (cm_is_pointer : cm_type -> Prop)
 (cm_pointee : cm_type -> cm_type)
 (cm_rep_is_pointer_code : Z -> Z)
 (cm_program_structs : cm_program -> list cm_struct_d)
 (cm_program_functions : cm_program -> list cm_function_d)
 (cm_function_at : cm_lookup_policy -> Z -> list cm_function_d -> cm_function_d)
 (cm_function_params : cm_function_d -> list cm_slot_d)
 (cm_function_locals : cm_function_d -> list cm_slot_d)
 (cm_slots_wf : list cm_struct_d -> list cm_slot_d -> Prop)
 (cm_rep_members_safe : list cm_slot_d -> Prop)
 (cm_rep_structs_safe : list cm_struct_d -> Prop)
 (cm_program_context_rep : Z -> cm_program -> Z -> Assertion)
 (cm_function_context_rep : Z -> cm_function_d -> Z -> Z -> Assertion)
 (cm_expr_rep : Z -> cm_expr -> Assertion)
 (cm_resolved_emitter_plan_rep : cm_lookup_policy -> cm_program -> Z -> Z -> Z -> list tvm_inst -> list tvm_inst -> Assertion)
 (cm_temp_load_code : cm_lookup_policy -> cm_program -> Z -> Z -> list tvm_inst)
 (cm_temp_offset : cm_lookup_policy -> cm_program -> Z -> Z -> Z)
 (cm_pointer_scale : cm_program -> cm_expr -> Z)
 (cm_binary_finish_code : cm_lookup_policy -> cm_program -> Z -> Z -> cm_expr -> cm_expr -> Z -> list tvm_inst)
 (cm_binary_opcode : Z -> tvm_opcode)
 (tvm_opcode_code : tvm_opcode -> Z)
 (TVMInst : tvm_opcode -> Z -> tvm_inst)
 (TVMPushOp : tvm_opcode) (TVMSwapOp : tvm_opcode) (TVMAddOp : tvm_opcode)
 (TVMSubOp : tvm_opcode) (TVMMulOp : tvm_opcode) (TVMDivOp : tvm_opcode)
*/
/*@ Import Coq Require Import SimpleC.EE.QCP_demos_human.cmc_emit_binary_finish_migration_lib */

void cm_expr_type_code_context(struct cm_expr *expr, int *code)
/*@ With (e : cm_expr)
    Require cm_expr_rep(expr, e) * undef_data_at(code, int)
    Ensure cm_expr_rep(expr, e) * data_at(code, int, cm_type_encode(cm_expr_type(e)))
*/;

long long cm_type_size_value(struct cm_program *program,
                             long long code)
/*@ With (policy : cm_lookup_policy) (p : cm_program) (asked : cm_type) (functions_ptr : Z)
 Require code == cm_type_encode(asked) && cm_typed_program(policy, p) && cm_type_code_wf(asked) && cm_type_refs(cm_program_structs(p), asked) && cm_rep_structs_safe(cm_program_structs(p)) && cm_program_context_rep(program, p, functions_ptr)
 Ensure code == cm_type_encode(asked) && cm_typed_program(policy, p) && cm_type_code_wf(asked) && cm_type_refs(cm_program_structs(p), asked) && cm_rep_structs_safe(cm_program_structs(p)) && __return == cm_type_size(cm_program_structs(p), asked) && cm_program_context_rep(program, p, functions_ptr)
*/;

int cmc_pointee(int ty)
/*@ Require 1024 <= ty && ty <= 2147483647 && emp
    Ensure __return == ty - 1024 && emp
*/;

void cmc_is_pointer_value(int ty, int *pointer)
/*@ Require undef_data_at(pointer, int)
    Ensure data_at(pointer, int, cm_rep_is_pointer_code(ty))
*/;

int cmc_binary_opcode(int op)
/*@ Require emp
    Ensure __return == tvm_opcode_code(cm_binary_opcode(op)) && __return != 22 && emp
*/;

void cm_emit_plan(struct cm_emitter *emitter, int op,
                  long long immediate)
/*@ With (policy : cm_lookup_policy) (p : cm_program) (done : list tvm_inst) (tail : list tvm_inst) (out : Z) (capacity : Z) (opcode : tvm_opcode)
    Require op == tvm_opcode_code(opcode) && tvm_opcode_code(opcode) != 22 && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, cons(TVMInst(opcode, immediate), tail))
    Ensure cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cons(TVMInst(opcode, immediate), nil)), tail)
*/;

void cm_emit_temp_load_plan(struct cm_function *fn, int temp,
                            struct cm_emitter *emitter)
/*@ With (policy : cm_lookup_policy) (p : cm_program) (done : list tvm_inst) (tail : list tvm_inst) (out : Z) (capacity : Z) (f : cm_function_d) (fid : Z) (structs : list cm_struct_d) (body : Z) (next : Z)
    Require 0 <= temp && structs == cm_program_structs(p) && f == cm_function_at(policy, fid, cm_program_functions(p)) && cm_slots_wf(structs, cm_function_params(f)) && cm_slots_wf(structs, cm_function_locals(f)) && cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) && cm_temp_offset(policy, p, fid, temp) <= 2147483647 && cm_function_context_rep(fn, f, body, next) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_temp_load_code(policy, p, fid, temp), tail))
    Ensure 0 <= temp && structs == cm_program_structs(p) && f == cm_function_at(policy, fid, cm_program_functions(p)) && cm_slots_wf(structs, cm_function_params(f)) && cm_slots_wf(structs, cm_function_locals(f)) && cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) && cm_temp_offset(policy, p, fid, temp) <= 2147483647 && cm_function_context_rep(fn, f, body, next) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cm_temp_load_code(policy, p, fid, temp)), tail)
*/;

static long long cm_pointer_scale_value(struct cm_program *program,
                                        struct cm_expr *expr)
/*@ With (policy : cm_lookup_policy) (p : cm_program) (e : cm_expr) (functions_ptr : Z)
 Require cm_typed_program(policy, p) && cm_rep_structs_safe(cm_program_structs(p)) && cm_type_code_wf(cm_expr_type(e)) && cm_type_refs(cm_program_structs(p), cm_expr_type(e)) && cm_i32_code_count(cm_type_encode(cm_expr_type(e))) && cm_is_pointer(cm_expr_type(e)) && cm_program_context_rep(program, p, functions_ptr) * cm_expr_rep(expr, e)
 Ensure cm_typed_program(policy, p) && cm_rep_structs_safe(cm_program_structs(p)) && cm_type_code_wf(cm_expr_type(e)) && cm_type_refs(cm_program_structs(p), cm_expr_type(e)) && cm_i32_code_count(cm_type_encode(cm_expr_type(e))) && cm_is_pointer(cm_expr_type(e)) && __return == cm_pointer_scale(p, e) && cm_program_context_rep(program, p, functions_ptr) * cm_expr_rep(expr, e)
*/
{
  int type_code;
  cm_expr_type_code_context(expr, &type_code) /*@ where e = e */;
  int pointee_code = cmc_pointee(type_code);
  long long result = cm_type_size_value(program, pointee_code) /*@ where policy = policy, p = p, asked = cm_pointee(cm_expr_type(e)), functions_ptr = functions_ptr */;
  return result;
}

static void cm_emit_binary_generic_fragment(struct cm_function *fn,
                                            int temp, int op,
                                            struct cm_emitter *emitter)
/*@ With (policy : cm_lookup_policy) (p : cm_program) (f : cm_function_d) (body : Z) (next : Z) (done : list tvm_inst) (tail : list tvm_inst) (out : Z) (capacity : Z) (fid : Z)
 Require f == cm_function_at(policy, fid, cm_program_functions(p)) && cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) && cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) && 0 <= temp && cm_temp_offset(policy, p, fid, temp) <= 2147483647 && cm_function_context_rep(fn, f, body, next) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_temp_load_code(policy, p, fid, temp), app(cons(TVMInst(TVMSwapOp, 0), cons(TVMInst(cm_binary_opcode(op), 0), nil)), tail)))
 Ensure f == cm_function_at(policy, fid, cm_program_functions(p)) && cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) && cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) && 0 <= temp && cm_temp_offset(policy, p, fid, temp) <= 2147483647 && cm_function_context_rep(fn, f, body, next) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, app(cm_temp_load_code(policy, p, fid, temp), cons(TVMInst(TVMSwapOp, 0), cons(TVMInst(cm_binary_opcode(op), 0), nil)))), tail)
*/
{
  /*@ cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_temp_load_code(policy, p, fid, temp), app(cons(TVMInst(TVMSwapOp, 0), cons(TVMInst(cm_binary_opcode(op), 0), nil)), tail))) which implies cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_temp_load_code(policy, p, fid, temp), cons(TVMInst(TVMSwapOp, 0), cons(TVMInst(cm_binary_opcode(op), 0), tail)))) */
  cm_emit_temp_load_plan(fn, temp, emitter) /*@ where policy = policy, p = p, f = f, fid = fid, structs = cm_program_structs(p), body = body, next = next, done = done, tail = cons(TVMInst(TVMSwapOp, 0), cons(TVMInst(cm_binary_opcode(op), 0), tail)), out = out, capacity = capacity */;
  cm_emit_plan(emitter, CMC_OP_SWAP, 0) /*@ where policy = policy, p = p, done = app(done, cm_temp_load_code(policy, p, fid, temp)), tail = cons(TVMInst(cm_binary_opcode(op), 0), tail), out = out, capacity = capacity, opcode = TVMSwapOp */;
  int opcode = cmc_binary_opcode(op);
  cm_emit_plan(emitter, opcode, 0) /*@ where policy = policy, p = p, done = app(app(done, cm_temp_load_code(policy, p, fid, temp)), cons(TVMInst(TVMSwapOp, 0), nil)), tail = tail, out = out, capacity = capacity, opcode = cm_binary_opcode(op) */;
}

void cm_emit_binary_finish_plan(struct cm_program *program, int fid,
                                struct cm_function *fn, int temp, int op,
                                struct cm_expr *left,
                                struct cm_expr *right,
                                struct cm_emitter *emitter)
/*@ With (policy : cm_lookup_policy) (p : cm_program) (f : cm_function_d) (body : Z) (next : Z) (done : list tvm_inst) (tail : list tvm_inst) (out : Z) (capacity : Z) (left_e : cm_expr) (right_e : cm_expr) (functions_ptr : Z)
 Require cm_typed_program(policy, p) && f == cm_function_at(policy, fid, cm_program_functions(p)) && cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) && cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) && 0 <= temp && cm_temp_offset(policy, p, fid, temp) <= 2147483647 && cm_rep_structs_safe(cm_program_structs(p)) && cm_type_code_wf(cm_expr_type(left_e)) && cm_type_refs(cm_program_structs(p), cm_expr_type(left_e)) && cm_i32_code_count(cm_type_encode(cm_expr_type(left_e))) && cm_type_code_wf(cm_expr_type(right_e)) && cm_type_refs(cm_program_structs(p), cm_expr_type(right_e)) && cm_i32_code_count(cm_type_encode(cm_expr_type(right_e))) && cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body, next) * cm_expr_rep(left, left_e) * cm_expr_rep(right, right_e) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_binary_finish_code(policy, p, fid, op, left_e, right_e, temp), tail))
 Ensure cm_typed_program(policy, p) && f == cm_function_at(policy, fid, cm_program_functions(p)) && cm_slots_wf(cm_program_structs(p), cm_function_params(f)) && cm_slots_wf(cm_program_structs(p), cm_function_locals(f)) && cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) && 0 <= temp && cm_temp_offset(policy, p, fid, temp) <= 2147483647 && cm_rep_structs_safe(cm_program_structs(p)) && cm_type_code_wf(cm_expr_type(left_e)) && cm_type_refs(cm_program_structs(p), cm_expr_type(left_e)) && cm_i32_code_count(cm_type_encode(cm_expr_type(left_e))) && cm_type_code_wf(cm_expr_type(right_e)) && cm_type_refs(cm_program_structs(p), cm_expr_type(right_e)) && cm_i32_code_count(cm_type_encode(cm_expr_type(right_e))) && cm_program_context_rep(program, p, functions_ptr) * cm_function_context_rep(fn, f, body, next) * cm_expr_rep(left, left_e) * cm_expr_rep(right, right_e) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cm_binary_finish_code(policy, p, fid, op, left_e, right_e, temp)), tail)
*/
{
  int left_type;
  int right_type;
  cm_expr_type_code_context(left, &left_type) /*@ where e = left_e */;
  cm_expr_type_code_context(right, &right_type) /*@ where e = right_e */;
  int left_pointer;
  int right_pointer;
  cmc_is_pointer_value(left_type, &left_pointer);
  cmc_is_pointer_value(right_type, &right_pointer);
  if (op == CMC_BIN_ADD && right_pointer) {
    long long scale = cm_pointer_scale_value(program, right) /*@ where policy = policy, p = p, e = right_e, functions_ptr = functions_ptr */;
  /*@ cm_type_code_wf(cm_expr_type(left_e)) && cm_type_code_wf(cm_expr_type(right_e)) && 8 <= op && op <= 8 && cm_rep_is_pointer_code(cm_type_encode(cm_expr_type(right_e))) != 0 && scale == cm_pointer_scale(p, right_e) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_binary_finish_code(policy, p, fid, op, left_e, right_e, temp), tail)) which implies cm_type_code_wf(cm_expr_type(left_e)) && cm_type_code_wf(cm_expr_type(right_e)) && 8 <= op && op <= 8 && cm_rep_is_pointer_code(cm_type_encode(cm_expr_type(right_e))) != 0 && scale == cm_pointer_scale(p, right_e) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_temp_load_code(policy, p, fid, temp), cons(TVMInst(TVMPushOp, scale), cons(TVMInst(TVMMulOp, 0), cons(TVMInst(TVMSwapOp, 0), cons(TVMInst(TVMAddOp, 0), tail)))))) */
    cm_emit_temp_load_plan(fn, temp, emitter) /*@ where policy = policy, p = p, f = f, fid = fid, structs = cm_program_structs(p), body = body, next = next, done = done, tail = cons(TVMInst(TVMPushOp, scale), cons(TVMInst(TVMMulOp, 0), cons(TVMInst(TVMSwapOp, 0), cons(TVMInst(TVMAddOp, 0), tail)))), out = out, capacity = capacity */;
    cm_emit_plan(emitter, CMC_OP_PUSH, scale) /*@ where policy = policy, p = p, done = app(done, cm_temp_load_code(policy, p, fid, temp)), tail = cons(TVMInst(TVMMulOp, 0), cons(TVMInst(TVMSwapOp, 0), cons(TVMInst(TVMAddOp, 0), tail))), out = out, capacity = capacity, opcode = TVMPushOp */;
    cm_emit_plan(emitter, CMC_OP_MUL, 0) /*@ where policy = policy, p = p, done = app(app(done, cm_temp_load_code(policy, p, fid, temp)), cons(TVMInst(TVMPushOp, scale), nil)), tail = cons(TVMInst(TVMSwapOp, 0), cons(TVMInst(TVMAddOp, 0), tail)), out = out, capacity = capacity, opcode = TVMMulOp */;
    cm_emit_plan(emitter, CMC_OP_SWAP, 0) /*@ where policy = policy, p = p, done = app(app(app(done, cm_temp_load_code(policy, p, fid, temp)), cons(TVMInst(TVMPushOp, scale), nil)), cons(TVMInst(TVMMulOp, 0), nil)), tail = cons(TVMInst(TVMAddOp, 0), tail), out = out, capacity = capacity, opcode = TVMSwapOp */;
    cm_emit_plan(emitter, CMC_OP_ADD, 0) /*@ where policy = policy, p = p, done = app(app(app(app(done, cm_temp_load_code(policy, p, fid, temp)), cons(TVMInst(TVMPushOp, scale), nil)), cons(TVMInst(TVMMulOp, 0), nil)), cons(TVMInst(TVMSwapOp, 0), nil)), tail = tail, out = out, capacity = capacity, opcode = TVMAddOp */;
  } else {
    if (op == CMC_BIN_ADD && left_pointer) {
      long long scale = cm_pointer_scale_value(program, left) /*@ where policy = policy, p = p, e = left_e, functions_ptr = functions_ptr */;
  /*@ cm_type_code_wf(cm_expr_type(left_e)) && cm_type_code_wf(cm_expr_type(right_e)) && 8 <= op && op <= 8 && cm_rep_is_pointer_code(cm_type_encode(cm_expr_type(left_e))) != 0 && cm_rep_is_pointer_code(cm_type_encode(cm_expr_type(right_e))) == 0 && scale == cm_pointer_scale(p, left_e) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_binary_finish_code(policy, p, fid, op, left_e, right_e, temp), tail)) which implies cm_type_code_wf(cm_expr_type(left_e)) && cm_type_code_wf(cm_expr_type(right_e)) && 8 <= op && op <= 8 && cm_rep_is_pointer_code(cm_type_encode(cm_expr_type(left_e))) != 0 && cm_rep_is_pointer_code(cm_type_encode(cm_expr_type(right_e))) == 0 && scale == cm_pointer_scale(p, left_e) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_temp_load_code(policy, p, fid, temp), cons(TVMInst(TVMSwapOp, 0), cons(TVMInst(TVMPushOp, scale), cons(TVMInst(TVMMulOp, 0), cons(TVMInst(TVMAddOp, 0), tail)))))) */
      cm_emit_temp_load_plan(fn, temp, emitter) /*@ where policy = policy, p = p, f = f, fid = fid, structs = cm_program_structs(p), body = body, next = next, done = done, tail = cons(TVMInst(TVMSwapOp, 0), cons(TVMInst(TVMPushOp, scale), cons(TVMInst(TVMMulOp, 0), cons(TVMInst(TVMAddOp, 0), tail)))), out = out, capacity = capacity */;
      cm_emit_plan(emitter, CMC_OP_SWAP, 0) /*@ where policy = policy, p = p, done = app(done, cm_temp_load_code(policy, p, fid, temp)), tail = cons(TVMInst(TVMPushOp, scale), cons(TVMInst(TVMMulOp, 0), cons(TVMInst(TVMAddOp, 0), tail))), out = out, capacity = capacity, opcode = TVMSwapOp */;
      cm_emit_plan(emitter, CMC_OP_PUSH, scale) /*@ where policy = policy, p = p, done = app(app(done, cm_temp_load_code(policy, p, fid, temp)), cons(TVMInst(TVMSwapOp, 0), nil)), tail = cons(TVMInst(TVMMulOp, 0), cons(TVMInst(TVMAddOp, 0), tail)), out = out, capacity = capacity, opcode = TVMPushOp */;
      cm_emit_plan(emitter, CMC_OP_MUL, 0) /*@ where policy = policy, p = p, done = app(app(app(done, cm_temp_load_code(policy, p, fid, temp)), cons(TVMInst(TVMSwapOp, 0), nil)), cons(TVMInst(TVMPushOp, scale), nil)), tail = cons(TVMInst(TVMAddOp, 0), tail), out = out, capacity = capacity, opcode = TVMMulOp */;
      cm_emit_plan(emitter, CMC_OP_ADD, 0) /*@ where policy = policy, p = p, done = app(app(app(app(done, cm_temp_load_code(policy, p, fid, temp)), cons(TVMInst(TVMSwapOp, 0), nil)), cons(TVMInst(TVMPushOp, scale), nil)), cons(TVMInst(TVMMulOp, 0), nil)), tail = tail, out = out, capacity = capacity, opcode = TVMAddOp */;
    } else if (op == CMC_BIN_SUB && left_pointer && right_pointer) {
      long long scale = cm_pointer_scale_value(program, left) /*@ where policy = policy, p = p, e = left_e, functions_ptr = functions_ptr */;
  /*@ cm_type_code_wf(cm_expr_type(left_e)) && cm_type_code_wf(cm_expr_type(right_e)) && 9 <= op && op <= 9 && cm_rep_is_pointer_code(cm_type_encode(cm_expr_type(left_e))) != 0 && cm_rep_is_pointer_code(cm_type_encode(cm_expr_type(right_e))) != 0 && scale == cm_pointer_scale(p, left_e) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_binary_finish_code(policy, p, fid, op, left_e, right_e, temp), tail)) which implies cm_type_code_wf(cm_expr_type(left_e)) && cm_type_code_wf(cm_expr_type(right_e)) && 9 <= op && op <= 9 && cm_rep_is_pointer_code(cm_type_encode(cm_expr_type(left_e))) != 0 && cm_rep_is_pointer_code(cm_type_encode(cm_expr_type(right_e))) != 0 && scale == cm_pointer_scale(p, left_e) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_temp_load_code(policy, p, fid, temp), cons(TVMInst(TVMSwapOp, 0), cons(TVMInst(TVMSubOp, 0), cons(TVMInst(TVMPushOp, scale), cons(TVMInst(TVMDivOp, 0), tail)))))) */
      cm_emit_temp_load_plan(fn, temp, emitter) /*@ where policy = policy, p = p, f = f, fid = fid, structs = cm_program_structs(p), body = body, next = next, done = done, tail = cons(TVMInst(TVMSwapOp, 0), cons(TVMInst(TVMSubOp, 0), cons(TVMInst(TVMPushOp, scale), cons(TVMInst(TVMDivOp, 0), tail)))), out = out, capacity = capacity */;
      cm_emit_plan(emitter, CMC_OP_SWAP, 0) /*@ where policy = policy, p = p, done = app(done, cm_temp_load_code(policy, p, fid, temp)), tail = cons(TVMInst(TVMSubOp, 0), cons(TVMInst(TVMPushOp, scale), cons(TVMInst(TVMDivOp, 0), tail))), out = out, capacity = capacity, opcode = TVMSwapOp */;
      cm_emit_plan(emitter, CMC_OP_SUB, 0) /*@ where policy = policy, p = p, done = app(app(done, cm_temp_load_code(policy, p, fid, temp)), cons(TVMInst(TVMSwapOp, 0), nil)), tail = cons(TVMInst(TVMPushOp, scale), cons(TVMInst(TVMDivOp, 0), tail)), out = out, capacity = capacity, opcode = TVMSubOp */;
      cm_emit_plan(emitter, CMC_OP_PUSH, scale) /*@ where policy = policy, p = p, done = app(app(app(done, cm_temp_load_code(policy, p, fid, temp)), cons(TVMInst(TVMSwapOp, 0), nil)), cons(TVMInst(TVMSubOp, 0), nil)), tail = cons(TVMInst(TVMDivOp, 0), tail), out = out, capacity = capacity, opcode = TVMPushOp */;
      cm_emit_plan(emitter, CMC_OP_DIV, 0) /*@ where policy = policy, p = p, done = app(app(app(app(done, cm_temp_load_code(policy, p, fid, temp)), cons(TVMInst(TVMSwapOp, 0), nil)), cons(TVMInst(TVMSubOp, 0), nil)), cons(TVMInst(TVMPushOp, scale), nil)), tail = tail, out = out, capacity = capacity, opcode = TVMDivOp */;
    } else if (op == CMC_BIN_SUB && left_pointer) {
      long long scale = cm_pointer_scale_value(program, left) /*@ where policy = policy, p = p, e = left_e, functions_ptr = functions_ptr */;
  /*@ cm_type_code_wf(cm_expr_type(left_e)) && cm_type_code_wf(cm_expr_type(right_e)) && 9 <= op && op <= 9 && cm_rep_is_pointer_code(cm_type_encode(cm_expr_type(left_e))) != 0 && cm_rep_is_pointer_code(cm_type_encode(cm_expr_type(right_e))) == 0 && scale == cm_pointer_scale(p, left_e) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_binary_finish_code(policy, p, fid, op, left_e, right_e, temp), tail)) which implies cm_type_code_wf(cm_expr_type(left_e)) && cm_type_code_wf(cm_expr_type(right_e)) && 9 <= op && op <= 9 && cm_rep_is_pointer_code(cm_type_encode(cm_expr_type(left_e))) != 0 && cm_rep_is_pointer_code(cm_type_encode(cm_expr_type(right_e))) == 0 && scale == cm_pointer_scale(p, left_e) && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_temp_load_code(policy, p, fid, temp), cons(TVMInst(TVMSwapOp, 0), cons(TVMInst(TVMPushOp, scale), cons(TVMInst(TVMMulOp, 0), cons(TVMInst(TVMSubOp, 0), tail)))))) */
      cm_emit_temp_load_plan(fn, temp, emitter) /*@ where policy = policy, p = p, f = f, fid = fid, structs = cm_program_structs(p), body = body, next = next, done = done, tail = cons(TVMInst(TVMSwapOp, 0), cons(TVMInst(TVMPushOp, scale), cons(TVMInst(TVMMulOp, 0), cons(TVMInst(TVMSubOp, 0), tail)))), out = out, capacity = capacity */;
      cm_emit_plan(emitter, CMC_OP_SWAP, 0) /*@ where policy = policy, p = p, done = app(done, cm_temp_load_code(policy, p, fid, temp)), tail = cons(TVMInst(TVMPushOp, scale), cons(TVMInst(TVMMulOp, 0), cons(TVMInst(TVMSubOp, 0), tail))), out = out, capacity = capacity, opcode = TVMSwapOp */;
      cm_emit_plan(emitter, CMC_OP_PUSH, scale) /*@ where policy = policy, p = p, done = app(app(done, cm_temp_load_code(policy, p, fid, temp)), cons(TVMInst(TVMSwapOp, 0), nil)), tail = cons(TVMInst(TVMMulOp, 0), cons(TVMInst(TVMSubOp, 0), tail)), out = out, capacity = capacity, opcode = TVMPushOp */;
      cm_emit_plan(emitter, CMC_OP_MUL, 0) /*@ where policy = policy, p = p, done = app(app(app(done, cm_temp_load_code(policy, p, fid, temp)), cons(TVMInst(TVMSwapOp, 0), nil)), cons(TVMInst(TVMPushOp, scale), nil)), tail = cons(TVMInst(TVMSubOp, 0), tail), out = out, capacity = capacity, opcode = TVMMulOp */;
      cm_emit_plan(emitter, CMC_OP_SUB, 0) /*@ where policy = policy, p = p, done = app(app(app(app(done, cm_temp_load_code(policy, p, fid, temp)), cons(TVMInst(TVMSwapOp, 0), nil)), cons(TVMInst(TVMPushOp, scale), nil)), cons(TVMInst(TVMMulOp, 0), nil)), tail = tail, out = out, capacity = capacity, opcode = TVMSubOp */;
    } else {
      if (op == CMC_BIN_ADD) {
        /*@ cm_type_code_wf(cm_expr_type(left_e)) && cm_type_code_wf(cm_expr_type(right_e)) && 8 <= op && op <= 8 && cm_rep_is_pointer_code(cm_type_encode(cm_expr_type(left_e))) == 0 && cm_rep_is_pointer_code(cm_type_encode(cm_expr_type(right_e))) == 0 && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_binary_finish_code(policy, p, fid, op, left_e, right_e, temp), tail)) which implies cm_type_code_wf(cm_expr_type(left_e)) && cm_type_code_wf(cm_expr_type(right_e)) && 8 <= op && op <= 8 && cm_rep_is_pointer_code(cm_type_encode(cm_expr_type(left_e))) == 0 && cm_rep_is_pointer_code(cm_type_encode(cm_expr_type(right_e))) == 0 && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_temp_load_code(policy, p, fid, temp), app(cons(TVMInst(TVMSwapOp, 0), cons(TVMInst(cm_binary_opcode(op), 0), nil)), tail))) */
        cm_emit_binary_generic_fragment(fn, temp, op, emitter) /*@ where policy = policy, p = p, f = f, fid = fid, body = body, next = next, done = done, tail = tail, out = out, capacity = capacity */;
      } else if (op == CMC_BIN_SUB) {
        /*@ cm_type_code_wf(cm_expr_type(left_e)) && cm_type_code_wf(cm_expr_type(right_e)) && 9 <= op && op <= 9 && cm_rep_is_pointer_code(cm_type_encode(cm_expr_type(left_e))) == 0 && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_binary_finish_code(policy, p, fid, op, left_e, right_e, temp), tail)) which implies cm_type_code_wf(cm_expr_type(left_e)) && cm_type_code_wf(cm_expr_type(right_e)) && 9 <= op && op <= 9 && cm_rep_is_pointer_code(cm_type_encode(cm_expr_type(left_e))) == 0 && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_temp_load_code(policy, p, fid, temp), app(cons(TVMInst(TVMSwapOp, 0), cons(TVMInst(cm_binary_opcode(op), 0), nil)), tail))) */
        cm_emit_binary_generic_fragment(fn, temp, op, emitter) /*@ where policy = policy, p = p, f = f, fid = fid, body = body, next = next, done = done, tail = tail, out = out, capacity = capacity */;
      } else {
        /*@ cm_type_code_wf(cm_expr_type(left_e)) && cm_type_code_wf(cm_expr_type(right_e)) && op != 8 && op != 9 && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_binary_finish_code(policy, p, fid, op, left_e, right_e, temp), tail)) which implies cm_type_code_wf(cm_expr_type(left_e)) && cm_type_code_wf(cm_expr_type(right_e)) && op != 8 && op != 9 && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_temp_load_code(policy, p, fid, temp), app(cons(TVMInst(TVMSwapOp, 0), cons(TVMInst(cm_binary_opcode(op), 0), nil)), tail))) */
        cm_emit_binary_generic_fragment(fn, temp, op, emitter) /*@ where policy = policy, p = p, f = f, fid = fid, body = body, next = next, done = done, tail = tail, out = out, capacity = capacity */;
      }
    }
  }
}
