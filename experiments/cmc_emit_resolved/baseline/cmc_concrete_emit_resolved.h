#pragma once

#include "cmc_concrete_emit_core.h"
#require "cmc_concrete_emit_core.c"

void cm_emit_resolved(struct cm_emitter *emitter, int op,
                      long long immediate)
    [[cst::param(`p:cm_program`, `done:(tvm_inst)list`,
                 `opcode:tvm_opcode`, `out:int`, `capacity:int`)]]
    [[cst::require(
      `fact(op == tvm_opcode_code opcode) **
       fact(~(tvm_opcode_code opcode == 22i)) **
       fact(ilength done + 1i <= capacity) **
       cm_resolved_emitter_rep p emitter out capacity done`)]]
    [[cst::ensure(
      `cm_resolved_emitter_rep p emitter out capacity
         (done ++ [TVMInst opcode immediate])`)]];

void cm_emit_resolved_call(struct cm_emitter *emitter, int function_id)
    [[cst::param(`p:cm_program`, `done:(tvm_inst)list`,
                 `out:int`, `capacity:int`)]]
    [[cst::require(
      `fact(ilength done + 1i <= capacity) **
       cm_resolved_emitter_rep p emitter out capacity done`)]]
    [[cst::ensure(
      `cm_resolved_emitter_rep p emitter out capacity
         (done ++ [TVMInst TVMCallOp
                    (cm_function_pc p function_id)])`)]];

void cm_emit_resolved_normalize(struct cm_emitter *emitter, int ty)
    [[cst::param(`p:cm_program`, `model_ty:cm_type`,
                 `done:(tvm_inst)list`, `out:int`, `capacity:int`)]]
    [[cst::require(
      `fact(ty == cm_type_encode model_ty) **
       fact(cm_type_code_wf model_ty <=> true) **
       fact(ilength done + ilength (cm_char_normalize_code model_ty) <=
              capacity) **
       cm_resolved_emitter_rep p emitter out capacity done`)]]
    [[cst::ensure(
      `cm_resolved_emitter_rep p emitter out capacity
         (done ++ cm_char_normalize_code model_ty)`)]];

void cm_emit_resolved_load(struct cm_emitter *emitter, int ty)
    [[cst::param(`p:cm_program`, `model_ty:cm_type`,
                 `done:(tvm_inst)list`, `out:int`, `capacity:int`)]]
    [[cst::require(
      `fact(ty == cm_type_encode model_ty) **
       fact(cm_type_code_wf model_ty <=> true) **
       fact(ilength done + ilength (cm_load_code model_ty) <= capacity) **
       cm_resolved_emitter_rep p emitter out capacity done`)]]
    [[cst::ensure(
      `cm_resolved_emitter_rep p emitter out capacity
         (done ++ cm_load_code model_ty)`)]];

void cm_emit_resolved_store(struct cm_emitter *emitter, int ty)
    [[cst::param(`p:cm_program`, `model_ty:cm_type`,
                 `done:(tvm_inst)list`, `out:int`, `capacity:int`)]]
    [[cst::require(
      `fact(ty == cm_type_encode model_ty) **
       fact(cm_type_code_wf model_ty <=> true) **
       fact(ilength done + ilength (cm_store_code model_ty) <= capacity) **
       cm_resolved_emitter_rep p emitter out capacity done`)]]
    [[cst::ensure(
      `cm_resolved_emitter_rep p emitter out capacity
         (done ++ cm_store_code model_ty)`)]];

void cm_emit_resolved_fp_address(struct cm_emitter *emitter,
                                 long long offset)
    [[cst::param(`p:cm_program`, `done:(tvm_inst)list`,
                 `out:int`, `capacity:int`)]]
    [[cst::require(
      `fact(ilength done +
              ilength (cm_fp_relative_address_code offset) <= capacity) **
       cm_resolved_emitter_rep p emitter out capacity done`)]]
    [[cst::ensure(
      `cm_resolved_emitter_rep p emitter out capacity
         (done ++ cm_fp_relative_address_code offset)`)]];

void cm_emit_resolved_temp_store(struct cm_function *fn, int temp,
                                 struct cm_emitter *emitter)
    [[cst::param(`p:cm_program`, `f:cm_function_d`, `fid:int`,
                 `structs:(cm_struct_d)list`, `body:int`, `next:int`,
                 `done:(tvm_inst)list`, `out:int`, `capacity:int`)]]
    [[cst::require(
      `fact(0i <= temp) **
       fact(structs == cm_program_structs p) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(cm_slots_wf structs (cm_function_params f) <=> true) **
       fact(cm_slots_wf structs (cm_function_locals f) <=> true) **
       fact(cm_rep_members_safe (cm_function_params f) <=> true) **
       fact(cm_rep_members_safe (cm_function_locals f) <=> true) **
       fact(cm_temp_offset p fid temp <= 2147483647i) **
       fact(ilength done + ilength (cm_temp_store_code p fid temp) <=
              capacity) **
       cm_function_context_rep fn f body next **
       cm_resolved_emitter_rep p emitter out capacity done`)]]
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
       cm_resolved_emitter_rep p emitter out capacity
         (done ++ cm_temp_store_code p fid temp)`)]];

void cm_emit_resolved_temp_load(struct cm_function *fn, int temp,
                                struct cm_emitter *emitter)
    [[cst::param(`p:cm_program`, `f:cm_function_d`, `fid:int`,
                 `structs:(cm_struct_d)list`, `body:int`, `next:int`,
                 `done:(tvm_inst)list`, `out:int`, `capacity:int`)]]
    [[cst::require(
      `fact(0i <= temp) **
       fact(structs == cm_program_structs p) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(cm_slots_wf structs (cm_function_params f) <=> true) **
       fact(cm_slots_wf structs (cm_function_locals f) <=> true) **
       fact(cm_rep_members_safe (cm_function_params f) <=> true) **
       fact(cm_rep_members_safe (cm_function_locals f) <=> true) **
       fact(cm_temp_offset p fid temp <= 2147483647i) **
       fact(ilength done + ilength (cm_temp_load_code p fid temp) <=
              capacity) **
       cm_function_context_rep fn f body next **
       cm_resolved_emitter_rep p emitter out capacity done`)]]
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
       cm_resolved_emitter_rep p emitter out capacity
         (done ++ cm_temp_load_code p fid temp)`)]];
