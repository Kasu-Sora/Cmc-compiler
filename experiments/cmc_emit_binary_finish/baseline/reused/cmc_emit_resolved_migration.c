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
/*@ Import Coq Require Import SimpleC.EE.QCP_demos_human.cmc_emit_resolved_migration_lib */

/*@ Extern Coq
    (TVMCallOp : tvm_opcode)
    (cm_function_pc : cm_lookup_policy -> cm_program -> Z -> Z)
    (cm_patch_code : cm_lookup_policy -> cm_program -> list tvm_inst -> list tvm_inst)
    (cm_resolved_emitter_rep : cm_lookup_policy -> cm_program -> Z -> Z -> Z -> list tvm_inst -> Assertion)
*/

void cm_emit(struct cm_emitter *emitter, int op, long long immediate)
/*@ With (done : list tvm_inst) (tail : list tvm_inst) (out : Z) (capacity : Z) (opcode : tvm_opcode)
    Require op == tvm_opcode_code(opcode) && cm_emitter_plan_rep(emitter, out, capacity, done, cons(TVMInst(opcode, immediate), tail))
    Ensure cm_emitter_plan_rep(emitter, out, capacity, app(done, cons(TVMInst(opcode, immediate), nil)), tail)
*/;

void cm_emit_normalize(struct cm_emitter *emitter, int ty)
/*@ With (done : list tvm_inst) (tail : list tvm_inst) (out : Z) (capacity : Z) (model_ty : cm_type)
    Require ty == cm_type_encode(model_ty) && cm_type_code_wf(model_ty) && cm_emitter_plan_rep(emitter, out, capacity, done, app(cm_char_normalize_code(model_ty), tail))
    Ensure cm_emitter_plan_rep(emitter, out, capacity, app(done, cm_char_normalize_code(model_ty)), tail)
*/;

void cm_emit_load(struct cm_emitter *emitter, int ty)
/*@ With (done : list tvm_inst) (tail : list tvm_inst) (out : Z) (capacity : Z) (model_ty : cm_type)
    Require ty == cm_type_encode(model_ty) && cm_type_code_wf(model_ty) && cm_emitter_plan_rep(emitter, out, capacity, done, app(cm_load_code(model_ty), tail))
    Ensure cm_emitter_plan_rep(emitter, out, capacity, app(done, cm_load_code(model_ty)), tail)
*/;

void cm_emit_store(struct cm_emitter *emitter, int ty)
/*@ With (done : list tvm_inst) (tail : list tvm_inst) (out : Z) (capacity : Z) (model_ty : cm_type)
    Require ty == cm_type_encode(model_ty) && cm_type_code_wf(model_ty) && cm_emitter_plan_rep(emitter, out, capacity, done, app(cm_store_code(model_ty), tail))
    Ensure cm_emitter_plan_rep(emitter, out, capacity, app(done, cm_store_code(model_ty)), tail)
*/;

void cm_emit_fp_address(struct cm_emitter *emitter, long long offset)
/*@ With (done : list tvm_inst) (tail : list tvm_inst) (out : Z) (capacity : Z)
    Require cm_emitter_plan_rep(emitter, out, capacity, done, app(cm_fp_relative_address_code(offset), tail))
    Ensure cm_emitter_plan_rep(emitter, out, capacity, app(done, cm_fp_relative_address_code(offset)), tail)
*/;

void cm_emit_temp_store(struct cm_function *fn, int temp,
                               struct cm_emitter *emitter)
/*@ With (policy : cm_lookup_policy) (p : cm_program) (f : cm_function_d) (fid : Z) (structs : list cm_struct_d) (body : Z) (next : Z) (done : list tvm_inst) (tail : list tvm_inst) (out : Z) (capacity : Z)
    Require 0 <= temp && structs == cm_program_structs(p) && f == cm_function_at(policy, fid, cm_program_functions(p)) && cm_slots_wf(structs, cm_function_params(f)) && cm_slots_wf(structs, cm_function_locals(f)) && cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) && cm_temp_offset(policy, p, fid, temp) <= 2147483647 && cm_function_context_rep(fn, f, body, next) * cm_emitter_plan_rep(emitter, out, capacity, done, app(cm_temp_store_code(policy, p, fid, temp), tail))
    Ensure 0 <= temp && structs == cm_program_structs(p) && f == cm_function_at(policy, fid, cm_program_functions(p)) && cm_slots_wf(structs, cm_function_params(f)) && cm_slots_wf(structs, cm_function_locals(f)) && cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) && cm_temp_offset(policy, p, fid, temp) <= 2147483647 && cm_function_context_rep(fn, f, body, next) * cm_emitter_plan_rep(emitter, out, capacity, app(done, cm_temp_store_code(policy, p, fid, temp)), tail)
*/;

void cm_emit_temp_load(struct cm_function *fn, int temp,
                              struct cm_emitter *emitter)
/*@ With (policy : cm_lookup_policy) (p : cm_program) (f : cm_function_d) (fid : Z) (structs : list cm_struct_d) (body : Z) (next : Z) (done : list tvm_inst) (tail : list tvm_inst) (out : Z) (capacity : Z)
    Require 0 <= temp && structs == cm_program_structs(p) && f == cm_function_at(policy, fid, cm_program_functions(p)) && cm_slots_wf(structs, cm_function_params(f)) && cm_slots_wf(structs, cm_function_locals(f)) && cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) && cm_temp_offset(policy, p, fid, temp) <= 2147483647 && cm_function_context_rep(fn, f, body, next) * cm_emitter_plan_rep(emitter, out, capacity, done, app(cm_temp_load_code(policy, p, fid, temp), tail))
    Ensure 0 <= temp && structs == cm_program_structs(p) && f == cm_function_at(policy, fid, cm_program_functions(p)) && cm_slots_wf(structs, cm_function_params(f)) && cm_slots_wf(structs, cm_function_locals(f)) && cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) && cm_temp_offset(policy, p, fid, temp) <= 2147483647 && cm_function_context_rep(fn, f, body, next) * cm_emitter_plan_rep(emitter, out, capacity, app(done, cm_temp_load_code(policy, p, fid, temp)), tail)
*/;

void cm_emit_resolved(struct cm_emitter *emitter, int op,
                      long long immediate)
/*@ With (policy : cm_lookup_policy) (p : cm_program) (done : list tvm_inst) (out : Z) (capacity : Z) (opcode : tvm_opcode)
    Require op == tvm_opcode_code(opcode) && tvm_opcode_code(opcode) != 22 && Zlength(done) + 1 <= capacity && cm_resolved_emitter_rep(policy, p, emitter, out, capacity, done)
    Ensure cm_resolved_emitter_rep(policy, p, emitter, out, capacity, app(done, cons(TVMInst(opcode, immediate), nil)))
*/
{
  /*@ Assert exists (raw_prefix : list tvm_inst),
    emitter == emitter@pre &&
    op == op@pre &&
    immediate == immediate@pre &&
    op == tvm_opcode_code(opcode) &&
    tvm_opcode_code(opcode) != 22 &&
    cm_patch_code(policy, p, raw_prefix) == done &&
    cm_emitter_plan_rep(emitter, out, capacity, raw_prefix, cons(TVMInst(opcode, immediate), nil))
  */
  cm_emit(emitter, op, immediate) /*@ where out = out, capacity = capacity, opcode = opcode */;
}

void cm_emit_resolved_call(struct cm_emitter *emitter, int function_id)
/*@ With (policy : cm_lookup_policy) (p : cm_program) (done : list tvm_inst) (out : Z) (capacity : Z)
    Require Zlength(done) + 1 <= capacity && cm_resolved_emitter_rep(policy, p, emitter, out, capacity, done)
    Ensure cm_resolved_emitter_rep(policy, p, emitter, out, capacity, app(done, cons(TVMInst(TVMCallOp, cm_function_pc(policy, p, function_id)), nil)))
*/
{
  /*@ Assert exists (raw_prefix : list tvm_inst),
    emitter == emitter@pre &&
    function_id == function_id@pre &&
    22 == tvm_opcode_code(TVMCallOp) &&
    cm_patch_code(policy, p, raw_prefix) == done &&
    cm_emitter_plan_rep(emitter, out, capacity, raw_prefix, cons(TVMInst(TVMCallOp, function_id), nil))
  */
  cm_emit(emitter, CMC_OP_CALL, function_id) /*@ where out = out, capacity = capacity, opcode = TVMCallOp */;
}

void cm_emit_resolved_normalize(struct cm_emitter *emitter, int ty)
/*@ With (policy : cm_lookup_policy) (p : cm_program) (done : list tvm_inst) (out : Z) (capacity : Z) (model_ty : cm_type)
    Require ty == cm_type_encode(model_ty) && cm_type_code_wf(model_ty) && Zlength(done) + Zlength(cm_char_normalize_code(model_ty)) <= capacity && cm_resolved_emitter_rep(policy, p, emitter, out, capacity, done)
    Ensure cm_resolved_emitter_rep(policy, p, emitter, out, capacity, app(done, cm_char_normalize_code(model_ty)))
*/
{
  /*@ Assert exists (raw_prefix : list tvm_inst),
    emitter == emitter@pre &&
    ty == ty@pre &&
    ty == cm_type_encode(model_ty) &&
    cm_type_code_wf(model_ty) &&
    cm_patch_code(policy, p, raw_prefix) == done &&
    cm_emitter_plan_rep(emitter, out, capacity, raw_prefix, app(cm_char_normalize_code(model_ty), nil))
  */
  cm_emit_normalize(emitter, ty) /*@ where out = out, capacity = capacity, model_ty = model_ty */;
}

void cm_emit_resolved_load(struct cm_emitter *emitter, int ty)
/*@ With (policy : cm_lookup_policy) (p : cm_program) (done : list tvm_inst) (out : Z) (capacity : Z) (model_ty : cm_type)
    Require ty == cm_type_encode(model_ty) && cm_type_code_wf(model_ty) && Zlength(done) + Zlength(cm_load_code(model_ty)) <= capacity && cm_resolved_emitter_rep(policy, p, emitter, out, capacity, done)
    Ensure cm_resolved_emitter_rep(policy, p, emitter, out, capacity, app(done, cm_load_code(model_ty)))
*/
{
  /*@ Assert exists (raw_prefix : list tvm_inst),
    emitter == emitter@pre &&
    ty == ty@pre &&
    ty == cm_type_encode(model_ty) &&
    cm_type_code_wf(model_ty) &&
    cm_patch_code(policy, p, raw_prefix) == done &&
    cm_emitter_plan_rep(emitter, out, capacity, raw_prefix, app(cm_load_code(model_ty), nil))
  */
  cm_emit_load(emitter, ty) /*@ where out = out, capacity = capacity, model_ty = model_ty */;
}

void cm_emit_resolved_store(struct cm_emitter *emitter, int ty)
/*@ With (policy : cm_lookup_policy) (p : cm_program) (done : list tvm_inst) (out : Z) (capacity : Z) (model_ty : cm_type)
    Require ty == cm_type_encode(model_ty) && cm_type_code_wf(model_ty) && Zlength(done) + Zlength(cm_store_code(model_ty)) <= capacity && cm_resolved_emitter_rep(policy, p, emitter, out, capacity, done)
    Ensure cm_resolved_emitter_rep(policy, p, emitter, out, capacity, app(done, cm_store_code(model_ty)))
*/
{
  /*@ Assert exists (raw_prefix : list tvm_inst),
    emitter == emitter@pre &&
    ty == ty@pre &&
    ty == cm_type_encode(model_ty) &&
    cm_type_code_wf(model_ty) &&
    cm_patch_code(policy, p, raw_prefix) == done &&
    cm_emitter_plan_rep(emitter, out, capacity, raw_prefix, app(cm_store_code(model_ty), nil))
  */
  cm_emit_store(emitter, ty) /*@ where out = out, capacity = capacity, model_ty = model_ty */;
}

void cm_emit_resolved_fp_address(struct cm_emitter *emitter,
                                 long long offset)
/*@ With (policy : cm_lookup_policy) (p : cm_program) (done : list tvm_inst) (out : Z) (capacity : Z)
    Require Zlength(done) + Zlength(cm_fp_relative_address_code(offset)) <= capacity && cm_resolved_emitter_rep(policy, p, emitter, out, capacity, done)
    Ensure cm_resolved_emitter_rep(policy, p, emitter, out, capacity, app(done, cm_fp_relative_address_code(offset)))
*/
{
  /*@ Assert exists (raw_prefix : list tvm_inst),
    emitter == emitter@pre &&
    offset == offset@pre &&
    cm_patch_code(policy, p, raw_prefix) == done &&
    cm_emitter_plan_rep(emitter, out, capacity, raw_prefix, app(cm_fp_relative_address_code(offset), nil))
  */
  cm_emit_fp_address(emitter, offset) /*@ where out = out, capacity = capacity */;
}

void cm_emit_resolved_temp_store(struct cm_function *fn, int temp,
                                 struct cm_emitter *emitter)
/*@ With (policy : cm_lookup_policy) (p : cm_program) (done : list tvm_inst) (out : Z) (capacity : Z) (f : cm_function_d) (fid : Z) (structs : list cm_struct_d) (body : Z) (next : Z)
    Require 0 <= temp && structs == cm_program_structs(p) && f == cm_function_at(policy, fid, cm_program_functions(p)) && cm_slots_wf(structs, cm_function_params(f)) && cm_slots_wf(structs, cm_function_locals(f)) && cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) && cm_temp_offset(policy, p, fid, temp) <= 2147483647 && Zlength(done) + Zlength(cm_temp_store_code(policy, p, fid, temp)) <= capacity && cm_function_context_rep(fn, f, body, next) * cm_resolved_emitter_rep(policy, p, emitter, out, capacity, done)
    Ensure 0 <= temp && structs == cm_program_structs(p) && f == cm_function_at(policy, fid, cm_program_functions(p)) && cm_slots_wf(structs, cm_function_params(f)) && cm_slots_wf(structs, cm_function_locals(f)) && cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) && cm_temp_offset(policy, p, fid, temp) <= 2147483647 && cm_function_context_rep(fn, f, body, next) * cm_resolved_emitter_rep(policy, p, emitter, out, capacity, app(done, cm_temp_store_code(policy, p, fid, temp)))
*/
{
  /*@ Assert exists (raw_prefix : list tvm_inst),
    emitter == emitter@pre &&
    fn == fn@pre &&
    temp == temp@pre &&
    0 <= temp && structs == cm_program_structs(p) && f == cm_function_at(policy, fid, cm_program_functions(p)) && cm_slots_wf(structs, cm_function_params(f)) && cm_slots_wf(structs, cm_function_locals(f)) && cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) && cm_temp_offset(policy, p, fid, temp) <= 2147483647 &&
    cm_patch_code(policy, p, raw_prefix) == done &&
    cm_function_context_rep(fn, f, body, next) * cm_emitter_plan_rep(emitter, out, capacity, raw_prefix, app(cm_temp_store_code(policy, p, fid, temp), nil))
  */
  cm_emit_temp_store(fn, temp, emitter) /*@ where out = out, capacity = capacity, policy = policy, p = p, f = f, fid = fid, structs = structs, body = body, next = next */;
}

void cm_emit_resolved_temp_load(struct cm_function *fn, int temp,
                                struct cm_emitter *emitter)
/*@ With (policy : cm_lookup_policy) (p : cm_program) (done : list tvm_inst) (out : Z) (capacity : Z) (f : cm_function_d) (fid : Z) (structs : list cm_struct_d) (body : Z) (next : Z)
    Require 0 <= temp && structs == cm_program_structs(p) && f == cm_function_at(policy, fid, cm_program_functions(p)) && cm_slots_wf(structs, cm_function_params(f)) && cm_slots_wf(structs, cm_function_locals(f)) && cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) && cm_temp_offset(policy, p, fid, temp) <= 2147483647 && Zlength(done) + Zlength(cm_temp_load_code(policy, p, fid, temp)) <= capacity && cm_function_context_rep(fn, f, body, next) * cm_resolved_emitter_rep(policy, p, emitter, out, capacity, done)
    Ensure 0 <= temp && structs == cm_program_structs(p) && f == cm_function_at(policy, fid, cm_program_functions(p)) && cm_slots_wf(structs, cm_function_params(f)) && cm_slots_wf(structs, cm_function_locals(f)) && cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) && cm_temp_offset(policy, p, fid, temp) <= 2147483647 && cm_function_context_rep(fn, f, body, next) * cm_resolved_emitter_rep(policy, p, emitter, out, capacity, app(done, cm_temp_load_code(policy, p, fid, temp)))
*/
{
  /*@ Assert exists (raw_prefix : list tvm_inst),
    emitter == emitter@pre &&
    fn == fn@pre &&
    temp == temp@pre &&
    0 <= temp && structs == cm_program_structs(p) && f == cm_function_at(policy, fid, cm_program_functions(p)) && cm_slots_wf(structs, cm_function_params(f)) && cm_slots_wf(structs, cm_function_locals(f)) && cm_rep_members_safe(cm_function_params(f)) && cm_rep_members_safe(cm_function_locals(f)) && cm_temp_offset(policy, p, fid, temp) <= 2147483647 &&
    cm_patch_code(policy, p, raw_prefix) == done &&
    cm_function_context_rep(fn, f, body, next) * cm_emitter_plan_rep(emitter, out, capacity, raw_prefix, app(cm_temp_load_code(policy, p, fid, temp), nil))
  */
  cm_emit_temp_load(fn, temp, emitter) /*@ where out = out, capacity = capacity, policy = policy, p = p, f = f, fid = fid, structs = structs, body = body, next = next */;
}
