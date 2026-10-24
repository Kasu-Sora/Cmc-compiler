#pragma once

#include "cmc_concrete_emit_resolved.h"
#require "cmc_concrete_emit_resolved.c"

void cm_emit_plan(struct cm_emitter *emitter, int op,
                  long long immediate)
    [[cst::param(`p:cm_program`, `done:(tvm_inst)list`,
                 `tail:(tvm_inst)list`, `opcode:tvm_opcode`,
                 `out:int`, `capacity:int`)]]
    [[cst::require(
      `fact(op == tvm_opcode_code opcode) **
       fact(~(tvm_opcode_code opcode == 22i)) **
       cm_resolved_emitter_plan_rep p emitter out capacity done
         (TVMInst opcode immediate :: tail)`)]]
    [[cst::ensure(
      `cm_resolved_emitter_plan_rep p emitter out capacity
         (done ++ [TVMInst opcode immediate]) tail`)]];

void cm_emit_call_plan(struct cm_emitter *emitter, int function_id)
    [[cst::param(`p:cm_program`, `done:(tvm_inst)list`,
                 `tail:(tvm_inst)list`, `out:int`, `capacity:int`)]]
    [[cst::require(
      `cm_resolved_emitter_plan_rep p emitter out capacity done
         (TVMInst TVMCallOp (cm_function_pc p function_id) :: tail)`)]]
    [[cst::ensure(
      `cm_resolved_emitter_plan_rep p emitter out capacity
         (done ++ [TVMInst TVMCallOp
                    (cm_function_pc p function_id)]) tail`)]];

void cm_emit_normalize_plan(struct cm_emitter *emitter, int ty)
    [[cst::param(`p:cm_program`, `model_ty:cm_type`,
                 `done:(tvm_inst)list`, `tail:(tvm_inst)list`,
                 `out:int`, `capacity:int`)]]
    [[cst::require(
      `fact(ty == cm_type_encode model_ty) **
       fact(cm_type_code_wf model_ty <=> true) **
       cm_resolved_emitter_plan_rep p emitter out capacity done
         (cm_char_normalize_code model_ty ++ tail)`)]]
    [[cst::ensure(
      `cm_resolved_emitter_plan_rep p emitter out capacity
         (done ++ cm_char_normalize_code model_ty) tail`)]];

void cm_emit_load_plan(struct cm_emitter *emitter, int ty)
    [[cst::param(`p:cm_program`, `model_ty:cm_type`,
                 `done:(tvm_inst)list`, `tail:(tvm_inst)list`,
                 `out:int`, `capacity:int`)]]
    [[cst::require(
      `fact(ty == cm_type_encode model_ty) **
       fact(cm_type_code_wf model_ty <=> true) **
       cm_resolved_emitter_plan_rep p emitter out capacity done
         (cm_load_code model_ty ++ tail)`)]]
    [[cst::ensure(
      `cm_resolved_emitter_plan_rep p emitter out capacity
         (done ++ cm_load_code model_ty) tail`)]];

void cm_emit_store_plan(struct cm_emitter *emitter, int ty)
    [[cst::param(`p:cm_program`, `model_ty:cm_type`,
                 `done:(tvm_inst)list`, `tail:(tvm_inst)list`,
                 `out:int`, `capacity:int`)]]
    [[cst::require(
      `fact(ty == cm_type_encode model_ty) **
       fact(cm_type_code_wf model_ty <=> true) **
       cm_resolved_emitter_plan_rep p emitter out capacity done
         (cm_store_code model_ty ++ tail)`)]]
    [[cst::ensure(
      `cm_resolved_emitter_plan_rep p emitter out capacity
         (done ++ cm_store_code model_ty) tail`)]];

void cm_emit_fp_address_plan(struct cm_emitter *emitter,
                             long long offset)
    [[cst::param(`p:cm_program`, `done:(tvm_inst)list`,
                 `tail:(tvm_inst)list`, `out:int`, `capacity:int`)]]
    [[cst::require(
      `cm_resolved_emitter_plan_rep p emitter out capacity done
         (cm_fp_relative_address_code offset ++ tail)`)]]
    [[cst::ensure(
      `cm_resolved_emitter_plan_rep p emitter out capacity
         (done ++ cm_fp_relative_address_code offset) tail`)]];

void cm_emit_temp_store_plan(struct cm_function *fn, int temp,
                             struct cm_emitter *emitter)
    [[cst::param(`p:cm_program`, `f:cm_function_d`, `fid:int`,
                 `structs:(cm_struct_d)list`, `body:int`, `next:int`,
                 `done:(tvm_inst)list`, `tail:(tvm_inst)list`,
                 `out:int`, `capacity:int`)]]
    [[cst::require(
      `fact(0i <= temp) **
       fact(structs == cm_program_structs p) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(cm_slots_wf structs (cm_function_params f) <=> true) **
       fact(cm_slots_wf structs (cm_function_locals f) <=> true) **
       fact(cm_rep_members_safe (cm_function_params f) <=> true) **
       fact(cm_rep_members_safe (cm_function_locals f) <=> true) **
       fact(cm_temp_offset p fid temp <= 2147483647i) **
       cm_function_context_rep fn f body next **
       cm_resolved_emitter_plan_rep p emitter out capacity done
         (cm_temp_store_code p fid temp ++ tail)`)]]
    [[cst::ensure(
      `fact(0i <= temp) **
       fact(structs == cm_program_structs p) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(cm_slots_wf structs (cm_function_params f) <=> true) **
       fact(cm_slots_wf structs (cm_function_locals f) <=> true) **
       fact(cm_rep_members_safe (cm_function_params f) <=> true) **
       fact(cm_rep_members_safe (cm_function_locals f) <=> true) **
       fact(cm_temp_offset p fid temp <= 2147483647i) **
       cm_function_context_rep fn f body next **
       cm_resolved_emitter_plan_rep p emitter out capacity
         (done ++ cm_temp_store_code p fid temp) tail`)]];

void cm_emit_temp_load_plan(struct cm_function *fn, int temp,
                            struct cm_emitter *emitter)
    [[cst::param(`p:cm_program`, `f:cm_function_d`, `fid:int`,
                 `structs:(cm_struct_d)list`, `body:int`, `next:int`,
                 `done:(tvm_inst)list`, `tail:(tvm_inst)list`,
                 `out:int`, `capacity:int`)]]
    [[cst::require(
      `fact(0i <= temp) **
       fact(structs == cm_program_structs p) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(cm_slots_wf structs (cm_function_params f) <=> true) **
       fact(cm_slots_wf structs (cm_function_locals f) <=> true) **
       fact(cm_rep_members_safe (cm_function_params f) <=> true) **
       fact(cm_rep_members_safe (cm_function_locals f) <=> true) **
       fact(cm_temp_offset p fid temp <= 2147483647i) **
       cm_function_context_rep fn f body next **
       cm_resolved_emitter_plan_rep p emitter out capacity done
         (cm_temp_load_code p fid temp ++ tail)`)]]
    [[cst::ensure(
      `fact(0i <= temp) **
       fact(structs == cm_program_structs p) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(cm_slots_wf structs (cm_function_params f) <=> true) **
       fact(cm_slots_wf structs (cm_function_locals f) <=> true) **
       fact(cm_rep_members_safe (cm_function_params f) <=> true) **
       fact(cm_rep_members_safe (cm_function_locals f) <=> true) **
       fact(cm_temp_offset p fid temp <= 2147483647i) **
       cm_function_context_rep fn f body next **
       cm_resolved_emitter_plan_rep p emitter out capacity
         (done ++ cm_temp_load_code p fid temp) tail`)]];
