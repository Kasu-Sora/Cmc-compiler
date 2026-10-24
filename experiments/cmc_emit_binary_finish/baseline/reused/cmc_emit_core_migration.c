#include "cmc_layout_migration_abi.h"

struct cm_emitter {
  struct cm_output *output;
  int pc;
};

/*@ Extern Coq
    (cm_type :: *) (cm_slot_d :: *) (cm_struct_d :: *)
    (cm_function_d :: *) (cm_program :: *) (cm_lookup_policy :: *)
    (tvm_opcode :: *) (tvm_inst :: *)
*/
/*@ Extern Coq
    (CMCharTy : cm_type)
    (TVMInst : tvm_opcode -> Z -> tvm_inst)
    (tvm_opcode_code : tvm_opcode -> Z)
    (cm_binary_opcode : Z -> tvm_opcode)
    (cm_type_encode : cm_type -> Z)
    (cm_type_code_wf : cm_type -> Prop)
    (cm_rep_ops : list tvm_inst -> list Z)
    (cm_rep_imms : list tvm_inst -> list Z)
    (cm_emitter_rep : Z -> Z -> Z -> list Z -> list Z -> Assertion)
    (cm_emitter_plan_rep : Z -> Z -> Z -> list tvm_inst -> list tvm_inst -> Assertion)
    (cm_char_normalize_code : cm_type -> list tvm_inst)
    (cm_load_code : cm_type -> list tvm_inst)
    (cm_store_code : cm_type -> list tvm_inst)
    (cm_fp_relative_address_code : Z -> list tvm_inst)
    (cm_temp_store_code : cm_lookup_policy -> cm_program -> Z -> Z -> list tvm_inst)
    (cm_temp_load_code : cm_lookup_policy -> cm_program -> Z -> Z -> list tvm_inst)
    (cm_temp_offset : cm_lookup_policy -> cm_program -> Z -> Z -> Z)
    (cm_function_at : cm_lookup_policy -> Z -> list cm_function_d -> cm_function_d)
    (cm_program_structs : cm_program -> list cm_struct_d)
    (cm_program_functions : cm_program -> list cm_function_d)
    (cm_function_params : cm_function_d -> list cm_slot_d)
    (cm_function_locals : cm_function_d -> list cm_slot_d)
    (cm_function_ret : cm_function_d -> cm_type)
    (cm_slots_wf : list cm_struct_d -> list cm_slot_d -> Prop)
    (cm_rep_members_safe : list cm_slot_d -> Prop)
    (cm_rep_members_size : list cm_slot_d -> Z)
    (cm_function_context_rep : Z -> cm_function_d -> Z -> Z -> Assertion)
    (cm_slot_list_rep : Z -> list cm_slot_d -> Assertion)
    (TVMPushOp : tvm_opcode)
    (TVMModOp : tvm_opcode)
    (TVMAddOp : tvm_opcode)
    (TVMLoadOp : tvm_opcode)
    (TVMLoadBOp : tvm_opcode)
    (TVMStoreOp : tvm_opcode)
    (TVMStoreBOp : tvm_opcode)
    (IntArray::seg : Z -> Z -> Z -> list Z -> Assertion)
    (IntArray::undef_seg : Z -> Z -> Z -> Assertion)
    (Int64Array::seg : Z -> Z -> Z -> list Z -> Assertion)
    (Int64Array::undef_seg : Z -> Z -> Z -> Assertion)
*/
/*@ Import Coq Require Import SimpleC.EE.QCP_demos_human.cmc_emit_core_migration_lib */

long long cmc_temp_offset(struct cm_function *fn, int temp)
/*@ With (params : list cm_slot_d) (zp : Z) (locals : list cm_slot_d) (zl : Z)
    Require cm_rep_members_safe(params) && cm_rep_members_safe(locals) && 0 <= temp && 8 + cm_rep_members_size(params) + cm_rep_members_size(locals) + 8 * temp <= 2147483647 && data_at(&(fn->params), struct cm_slot *, zp) * cm_slot_list_rep(zp, params) * data_at(&(fn->locals), struct cm_slot *, zl) * cm_slot_list_rep(zl, locals)
    Ensure cm_rep_members_safe(params) && cm_rep_members_safe(locals) && 0 <= temp && 8 + cm_rep_members_size(params) + cm_rep_members_size(locals) + 8 * temp <= 2147483647 && __return == 8 + cm_rep_members_size(params) + cm_rep_members_size(locals) + 8 * temp && data_at(&(fn->params), struct cm_slot *, zp) * cm_slot_list_rep(zp, params) * data_at(&(fn->locals), struct cm_slot *, zl) * cm_slot_list_rep(zl, locals)
*/;

static void cm_emit_raw(struct cm_emitter *emitter, int op,
                        long long immediate)
/*@ With (ops_prefix : list Z) (imms_prefix : list Z) (out : Z) (capacity : Z)
    Require Zlength(ops_prefix) < capacity && cm_emitter_rep(emitter, out, capacity, ops_prefix, imms_prefix)
    Ensure cm_emitter_rep(emitter, out, capacity, app(ops_prefix, cons(op, nil)), app(imms_prefix, cons(immediate, nil)))
*/
{
  /*@ Assert exists (ops : Z) (imms : Z),
    emitter == emitter@pre && op == op@pre && immediate == immediate@pre &&
    out != 0 && ops != 0 && imms != 0 &&
    Zlength(ops_prefix) == Zlength(imms_prefix) &&
    0 <= Zlength(ops_prefix) && Zlength(ops_prefix) < capacity && capacity <= 2147483647 &&
    data_at(&(emitter->output), struct cm_output *, out) *
    data_at(&(emitter->pc), int, Zlength(ops_prefix)) *
    data_at(&(((struct cm_output *)out)->ops), int *, ops) *
    data_at(&(((struct cm_output *)out)->imms), long long *, imms) *
    data_at(&(((struct cm_output *)out)->code_capacity), int, capacity) *
    IntArray::seg(ops, 0, Zlength(ops_prefix), ops_prefix) *
    IntArray::undef_seg(ops, Zlength(ops_prefix), capacity) *
    Int64Array::seg(imms, 0, Zlength(ops_prefix), imms_prefix) *
    Int64Array::undef_seg(imms, Zlength(ops_prefix), capacity)
  */
  emitter->output->ops[emitter->pc] = op;
  emitter->output->imms[emitter->pc] = immediate;
  emitter->pc = emitter->pc + 1;
}

void cm_emit(struct cm_emitter *emitter, int op, long long immediate)
/*@ With (done : list tvm_inst) (tail : list tvm_inst) (out : Z) (capacity : Z) (opcode : tvm_opcode)
    Require op == tvm_opcode_code(opcode) && cm_emitter_plan_rep(emitter, out, capacity, done, cons(TVMInst(opcode, immediate), tail))
    Ensure cm_emitter_plan_rep(emitter, out, capacity, app(done, cons(TVMInst(opcode, immediate), nil)), tail)
*/
{
  /*@ Assert emitter == emitter@pre && op == op@pre && immediate == immediate@pre &&
    op == tvm_opcode_code(opcode) &&
    Zlength(done) + 1 + Zlength(tail) <= capacity &&
    Zlength(cm_rep_ops(done)) < capacity &&
    cm_emitter_rep(emitter, out, capacity, cm_rep_ops(done), cm_rep_imms(done))
  */
  cm_emit_raw(emitter, op, immediate) /*@ where ops_prefix = cm_rep_ops(done), imms_prefix = cm_rep_imms(done), out = out, capacity = capacity */;
}

void cm_emit_normalize(struct cm_emitter *emitter, int ty)
/*@ With (done : list tvm_inst) (tail : list tvm_inst) (out : Z) (capacity : Z) (model_ty : cm_type)
    Require ty == cm_type_encode(model_ty) && cm_type_code_wf(model_ty) && cm_emitter_plan_rep(emitter, out, capacity, done, app(cm_char_normalize_code(model_ty), tail))
    Ensure cm_emitter_plan_rep(emitter, out, capacity, app(done, cm_char_normalize_code(model_ty)), tail)
*/
{
  if (ty == CMC_TYPE_CHAR) {
    /*@ Assert emitter == emitter@pre && ty == ty@pre && model_ty == CMCharTy && cm_emitter_plan_rep(emitter, out, capacity, done, cons(TVMInst(TVMPushOp, 256), cons(TVMInst(TVMModOp, 0), cons(TVMInst(TVMPushOp, 256), cons(TVMInst(TVMAddOp, 0), cons(TVMInst(TVMPushOp, 256), cons(TVMInst(TVMModOp, 0), tail))))))) */
    cm_emit(emitter, CMC_OP_PUSH, 256) /*@ where done = done, tail = cons(TVMInst(TVMModOp, 0), cons(TVMInst(TVMPushOp, 256), cons(TVMInst(TVMAddOp, 0), cons(TVMInst(TVMPushOp, 256), cons(TVMInst(TVMModOp, 0), tail))))), out = out, capacity = capacity, opcode = TVMPushOp */;
    cm_emit(emitter, CMC_OP_MOD, 0) /*@ where done = app(done, cons(TVMInst(TVMPushOp, 256), nil)), tail = cons(TVMInst(TVMPushOp, 256), cons(TVMInst(TVMAddOp, 0), cons(TVMInst(TVMPushOp, 256), cons(TVMInst(TVMModOp, 0), tail)))), out = out, capacity = capacity, opcode = TVMModOp */;
    cm_emit(emitter, CMC_OP_PUSH, 256) /*@ where done = app(app(done, cons(TVMInst(TVMPushOp, 256), nil)), cons(TVMInst(TVMModOp, 0), nil)), tail = cons(TVMInst(TVMAddOp, 0), cons(TVMInst(TVMPushOp, 256), cons(TVMInst(TVMModOp, 0), tail))), out = out, capacity = capacity, opcode = TVMPushOp */;
    cm_emit(emitter, CMC_OP_ADD, 0) /*@ where done = app(app(app(done, cons(TVMInst(TVMPushOp, 256), nil)), cons(TVMInst(TVMModOp, 0), nil)), cons(TVMInst(TVMPushOp, 256), nil)), tail = cons(TVMInst(TVMPushOp, 256), cons(TVMInst(TVMModOp, 0), tail)), out = out, capacity = capacity, opcode = TVMAddOp */;
    cm_emit(emitter, CMC_OP_PUSH, 256) /*@ where done = app(app(app(app(done, cons(TVMInst(TVMPushOp, 256), nil)), cons(TVMInst(TVMModOp, 0), nil)), cons(TVMInst(TVMPushOp, 256), nil)), cons(TVMInst(TVMAddOp, 0), nil)), tail = cons(TVMInst(TVMModOp, 0), tail), out = out, capacity = capacity, opcode = TVMPushOp */;
    cm_emit(emitter, CMC_OP_MOD, 0) /*@ where done = app(app(app(app(app(done, cons(TVMInst(TVMPushOp, 256), nil)), cons(TVMInst(TVMModOp, 0), nil)), cons(TVMInst(TVMPushOp, 256), nil)), cons(TVMInst(TVMAddOp, 0), nil)), cons(TVMInst(TVMPushOp, 256), nil)), tail = tail, out = out, capacity = capacity, opcode = TVMModOp */;
  } else {
  }
}

void cm_emit_load(struct cm_emitter *emitter, int ty)
/*@ With (done : list tvm_inst) (tail : list tvm_inst) (out : Z) (capacity : Z) (model_ty : cm_type)
    Require ty == cm_type_encode(model_ty) && cm_type_code_wf(model_ty) && cm_emitter_plan_rep(emitter, out, capacity, done, app(cm_load_code(model_ty), tail))
    Ensure cm_emitter_plan_rep(emitter, out, capacity, app(done, cm_load_code(model_ty)), tail)
*/
{
  if (ty == CMC_TYPE_CHAR) {
    /*@ Assert emitter == emitter@pre && ty == ty@pre && model_ty == CMCharTy && cm_emitter_plan_rep(emitter, out, capacity, done, cons(TVMInst(TVMLoadBOp, 0), tail)) */
    cm_emit(emitter, CMC_OP_LOADB, 0) /*@ where done = done, tail = tail, out = out, capacity = capacity, opcode = TVMLoadBOp */;
  } else {
    /*@ Assert emitter == emitter@pre && ty == ty@pre && model_ty != CMCharTy && cm_emitter_plan_rep(emitter, out, capacity, done, cons(TVMInst(TVMLoadOp, 0), tail)) */
    cm_emit(emitter, CMC_OP_LOAD, 0) /*@ where done = done, tail = tail, out = out, capacity = capacity, opcode = TVMLoadOp */;
  }
}

void cm_emit_store(struct cm_emitter *emitter, int ty)
/*@ With (done : list tvm_inst) (tail : list tvm_inst) (out : Z) (capacity : Z) (model_ty : cm_type)
    Require ty == cm_type_encode(model_ty) && cm_type_code_wf(model_ty) && cm_emitter_plan_rep(emitter, out, capacity, done, app(cm_store_code(model_ty), tail))
    Ensure cm_emitter_plan_rep(emitter, out, capacity, app(done, cm_store_code(model_ty)), tail)
*/
{
  if (ty == CMC_TYPE_CHAR) {
    /*@ Assert emitter == emitter@pre && ty == ty@pre && model_ty == CMCharTy && cm_emitter_plan_rep(emitter, out, capacity, done, cons(TVMInst(TVMStoreBOp, 0), tail)) */
    cm_emit(emitter, CMC_OP_STOREB, 0) /*@ where done = done, tail = tail, out = out, capacity = capacity, opcode = TVMStoreBOp */;
  } else {
    /*@ Assert emitter == emitter@pre && ty == ty@pre && model_ty != CMCharTy && cm_emitter_plan_rep(emitter, out, capacity, done, cons(TVMInst(TVMStoreOp, 0), tail)) */
    cm_emit(emitter, CMC_OP_STORE, 0) /*@ where done = done, tail = tail, out = out, capacity = capacity, opcode = TVMStoreOp */;
  }
}

void cm_emit_fp_address(struct cm_emitter *emitter, long long offset)
/*@ With (done : list tvm_inst) (tail : list tvm_inst) (out : Z) (capacity : Z)
    Require cm_emitter_plan_rep(emitter, out, capacity, done, app(cm_fp_relative_address_code(offset), tail))
    Ensure cm_emitter_plan_rep(emitter, out, capacity, app(done, cm_fp_relative_address_code(offset)), tail)
*/
{
  /*@ Assert emitter == emitter@pre && offset == offset@pre && cm_emitter_plan_rep(emitter, out, capacity, done, cons(TVMInst(TVMPushOp, 8), cons(TVMInst(TVMLoadOp, 0), cons(TVMInst(TVMPushOp, offset), cons(TVMInst(TVMAddOp, 0), tail))))) */
  cm_emit(emitter, CMC_OP_PUSH, 8) /*@ where done = done, tail = cons(TVMInst(TVMLoadOp, 0), cons(TVMInst(TVMPushOp, offset), cons(TVMInst(TVMAddOp, 0), tail))), out = out, capacity = capacity, opcode = TVMPushOp */;
  cm_emit(emitter, CMC_OP_LOAD, 0) /*@ where done = app(done, cons(TVMInst(TVMPushOp, 8), nil)), tail = cons(TVMInst(TVMPushOp, offset), cons(TVMInst(TVMAddOp, 0), tail)), out = out, capacity = capacity, opcode = TVMLoadOp */;
  cm_emit(emitter, CMC_OP_PUSH, offset) /*@ where done = app(app(done, cons(TVMInst(TVMPushOp, 8), nil)), cons(TVMInst(TVMLoadOp, 0), nil)), tail = cons(TVMInst(TVMAddOp, 0), tail), out = out, capacity = capacity, opcode = TVMPushOp */;
  cm_emit(emitter, CMC_OP_ADD, 0) /*@ where done = app(app(app(done, cons(TVMInst(TVMPushOp, 8), nil)), cons(TVMInst(TVMLoadOp, 0), nil)), cons(TVMInst(TVMPushOp, offset), nil)), tail = tail, out = out, capacity = capacity, opcode = TVMAddOp */;
}

void cm_emit_temp_store(struct cm_function *fn, int temp,
                               struct cm_emitter *emitter)
/*@ With (policy : cm_lookup_policy) (p : cm_program) (f : cm_function_d) (fid : Z) (structs : list cm_struct_d) (body : Z) (next : Z) (done : list tvm_inst) (tail : list tvm_inst) (out : Z) (capacity : Z)
    Require 0 <= temp && structs == cm_program_structs(p) && f == cm_function_at(policy, fid, cm_program_functions(p)) && cm_slots_wf(structs, cm_function_params(f)) && cm_slots_wf(structs, cm_function_locals(f)) && cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) && cm_temp_offset(policy, p, fid, temp) <= 2147483647 && cm_function_context_rep(fn, f, body, next) * cm_emitter_plan_rep(emitter, out, capacity, done, app(cm_temp_store_code(policy, p, fid, temp), tail))
    Ensure 0 <= temp && structs == cm_program_structs(p) && f == cm_function_at(policy, fid, cm_program_functions(p)) && cm_slots_wf(structs, cm_function_params(f)) && cm_slots_wf(structs, cm_function_locals(f)) && cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) && cm_temp_offset(policy, p, fid, temp) <= 2147483647 && cm_function_context_rep(fn, f, body, next) * cm_emitter_plan_rep(emitter, out, capacity, app(done, cm_temp_store_code(policy, p, fid, temp)), tail)
*/
{
  /*@ Assert exists (pp : Z) (lp : Z),
    fn == fn@pre && temp == temp@pre && emitter == emitter@pre && fn != 0 &&
    0 <= temp && structs == cm_program_structs(p) && f == cm_function_at(policy, fid, cm_program_functions(p)) && cm_slots_wf(structs, cm_function_params(f)) && cm_slots_wf(structs, cm_function_locals(f)) && cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) && cm_temp_offset(policy, p, fid, temp) <= 2147483647 &&
    8 + cm_rep_members_size(cm_function_params(f)) + cm_rep_members_size(cm_function_locals(f)) + 8 * temp == cm_temp_offset(policy, p, fid, temp) &&
    8 + cm_rep_members_size(cm_function_params(f)) + cm_rep_members_size(cm_function_locals(f)) + 8 * temp <= 2147483647 &&
    data_at(&(fn->ret_ty), int, cm_type_encode(cm_function_ret(f))) *
    data_at(&(fn->params), struct cm_slot *, pp) *
    data_at(&(fn->locals), struct cm_slot *, lp) *
    data_at(&(fn->body), struct cm_stmt *, body) *
    data_at(&(fn->next), struct cm_function *, next) *
    cm_slot_list_rep(pp, cm_function_params(f)) * cm_slot_list_rep(lp, cm_function_locals(f)) *
    cm_emitter_plan_rep(emitter, out, capacity, done, app(cm_temp_store_code(policy, p, fid, temp), tail))
  */
  long long offset = cmc_temp_offset(fn, temp) /*@ where params = cm_function_params(f), locals = cm_function_locals(f) */;
  /*@ Assert fn == fn@pre && temp == temp@pre && emitter == emitter@pre &&
    0 <= temp && structs == cm_program_structs(p) && f == cm_function_at(policy, fid, cm_program_functions(p)) && cm_slots_wf(structs, cm_function_params(f)) && cm_slots_wf(structs, cm_function_locals(f)) && cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) && cm_temp_offset(policy, p, fid, temp) <= 2147483647 && offset == cm_temp_offset(policy, p, fid, temp) &&
    cm_function_context_rep(fn, f, body, next) * cm_emitter_plan_rep(emitter, out, capacity, done, app(cm_fp_relative_address_code(offset), cons(TVMInst(TVMStoreOp, 0), tail)))
  */
  cm_emit_fp_address(emitter, offset) /*@ where done = done, tail = cons(TVMInst(TVMStoreOp, 0), tail), out = out, capacity = capacity */;
  cm_emit(emitter, CMC_OP_STORE, 0) /*@ where done = app(done, cm_fp_relative_address_code(offset)), tail = tail, out = out, capacity = capacity, opcode = TVMStoreOp */;
}

void cm_emit_temp_load(struct cm_function *fn, int temp,
                              struct cm_emitter *emitter)
/*@ With (policy : cm_lookup_policy) (p : cm_program) (f : cm_function_d) (fid : Z) (structs : list cm_struct_d) (body : Z) (next : Z) (done : list tvm_inst) (tail : list tvm_inst) (out : Z) (capacity : Z)
    Require 0 <= temp && structs == cm_program_structs(p) && f == cm_function_at(policy, fid, cm_program_functions(p)) && cm_slots_wf(structs, cm_function_params(f)) && cm_slots_wf(structs, cm_function_locals(f)) && cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) && cm_temp_offset(policy, p, fid, temp) <= 2147483647 && cm_function_context_rep(fn, f, body, next) * cm_emitter_plan_rep(emitter, out, capacity, done, app(cm_temp_load_code(policy, p, fid, temp), tail))
    Ensure 0 <= temp && structs == cm_program_structs(p) && f == cm_function_at(policy, fid, cm_program_functions(p)) && cm_slots_wf(structs, cm_function_params(f)) && cm_slots_wf(structs, cm_function_locals(f)) && cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) && cm_temp_offset(policy, p, fid, temp) <= 2147483647 && cm_function_context_rep(fn, f, body, next) * cm_emitter_plan_rep(emitter, out, capacity, app(done, cm_temp_load_code(policy, p, fid, temp)), tail)
*/
{
  /*@ Assert exists (pp : Z) (lp : Z),
    fn == fn@pre && temp == temp@pre && emitter == emitter@pre && fn != 0 &&
    0 <= temp && structs == cm_program_structs(p) && f == cm_function_at(policy, fid, cm_program_functions(p)) && cm_slots_wf(structs, cm_function_params(f)) && cm_slots_wf(structs, cm_function_locals(f)) && cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) && cm_temp_offset(policy, p, fid, temp) <= 2147483647 &&
    8 + cm_rep_members_size(cm_function_params(f)) + cm_rep_members_size(cm_function_locals(f)) + 8 * temp == cm_temp_offset(policy, p, fid, temp) &&
    8 + cm_rep_members_size(cm_function_params(f)) + cm_rep_members_size(cm_function_locals(f)) + 8 * temp <= 2147483647 &&
    data_at(&(fn->ret_ty), int, cm_type_encode(cm_function_ret(f))) *
    data_at(&(fn->params), struct cm_slot *, pp) *
    data_at(&(fn->locals), struct cm_slot *, lp) *
    data_at(&(fn->body), struct cm_stmt *, body) *
    data_at(&(fn->next), struct cm_function *, next) *
    cm_slot_list_rep(pp, cm_function_params(f)) * cm_slot_list_rep(lp, cm_function_locals(f)) *
    cm_emitter_plan_rep(emitter, out, capacity, done, app(cm_temp_load_code(policy, p, fid, temp), tail))
  */
  long long offset = cmc_temp_offset(fn, temp) /*@ where params = cm_function_params(f), locals = cm_function_locals(f) */;
  /*@ Assert fn == fn@pre && temp == temp@pre && emitter == emitter@pre &&
    0 <= temp && structs == cm_program_structs(p) && f == cm_function_at(policy, fid, cm_program_functions(p)) && cm_slots_wf(structs, cm_function_params(f)) && cm_slots_wf(structs, cm_function_locals(f)) && cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) && cm_temp_offset(policy, p, fid, temp) <= 2147483647 && offset == cm_temp_offset(policy, p, fid, temp) &&
    cm_function_context_rep(fn, f, body, next) * cm_emitter_plan_rep(emitter, out, capacity, done, app(cm_fp_relative_address_code(offset), cons(TVMInst(TVMLoadOp, 0), tail)))
  */
  cm_emit_fp_address(emitter, offset) /*@ where done = done, tail = cons(TVMInst(TVMLoadOp, 0), tail), out = out, capacity = capacity */;
  cm_emit(emitter, CMC_OP_LOAD, 0) /*@ where done = app(done, cm_fp_relative_address_code(offset)), tail = tail, out = out, capacity = capacity, opcode = TVMLoadOp */;
}

int cmc_binary_opcode(int op)
/*@ Require emp
    Ensure __return == tvm_opcode_code(cm_binary_opcode(op)) && __return != 22 && emp
*/
{
  int result;
  if (op == CMC_BIN_EQ) {
    result = CMC_OP_EQ;
  } else if (op == CMC_BIN_NE) {
    result = CMC_OP_NE;
  } else if (op == CMC_BIN_LT) {
    result = CMC_OP_LT;
  } else if (op == CMC_BIN_LE) {
    result = CMC_OP_LE;
  } else if (op == CMC_BIN_GT) {
    result = CMC_OP_GT;
  } else if (op == CMC_BIN_GE) {
    result = CMC_OP_GE;
  } else if (op == CMC_BIN_ADD) {
    result = CMC_OP_ADD;
  } else if (op == CMC_BIN_SUB) {
    result = CMC_OP_SUB;
  } else if (op == CMC_BIN_MUL) {
    result = CMC_OP_MUL;
  } else if (op == CMC_BIN_DIV) {
    result = CMC_OP_DIV;
  } else {
    result = CMC_OP_MOD;
  }
  return result;
}
