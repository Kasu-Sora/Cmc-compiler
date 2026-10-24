#pragma once

#include "cmc_concrete_counts.h"
#require "cmc_concrete_counts.c"


void cm_emit(struct cm_emitter *emitter, int op, long long immediate)
    [[cst::param(`done:(tvm_inst)list`, `tail:(tvm_inst)list`,
                 `opcode:tvm_opcode`, `out:int`, `capacity:int`)]]
    [[cst::require(
      `fact(op == tvm_opcode_code opcode) **
       cm_emitter_plan_rep emitter out capacity done
         (TVMInst opcode immediate :: tail)`)]]
    [[cst::ensure(
      `cm_emitter_plan_rep emitter out capacity
         (done ++ [TVMInst opcode immediate]) tail`)]];

void cm_emit_normalize(struct cm_emitter *emitter, int ty)
    [[cst::param(`model_ty:cm_type`, `done:(tvm_inst)list`,
                 `tail:(tvm_inst)list`, `out:int`, `capacity:int`)]]
    [[cst::require(
      `fact(ty == cm_type_encode model_ty) **
       fact(cm_type_code_wf model_ty <=> true) **
       cm_emitter_plan_rep emitter out capacity done
         (cm_char_normalize_code model_ty ++ tail)`)]]
    [[cst::ensure(
      `cm_emitter_plan_rep emitter out capacity
         (done ++ cm_char_normalize_code model_ty) tail`)]];

void cm_emit_load(struct cm_emitter *emitter, int ty)
    [[cst::param(`model_ty:cm_type`, `done:(tvm_inst)list`,
                 `tail:(tvm_inst)list`, `out:int`, `capacity:int`)]]
    [[cst::require(
      `fact(ty == cm_type_encode model_ty) **
       fact(cm_type_code_wf model_ty <=> true) **
       cm_emitter_plan_rep emitter out capacity done
         (cm_load_code model_ty ++ tail)`)]]
    [[cst::ensure(
      `cm_emitter_plan_rep emitter out capacity
         (done ++ cm_load_code model_ty) tail`)]];

void cm_emit_store(struct cm_emitter *emitter, int ty)
    [[cst::param(`model_ty:cm_type`, `done:(tvm_inst)list`,
                 `tail:(tvm_inst)list`, `out:int`, `capacity:int`)]]
    [[cst::require(
      `fact(ty == cm_type_encode model_ty) **
       fact(cm_type_code_wf model_ty <=> true) **
       cm_emitter_plan_rep emitter out capacity done
         (cm_store_code model_ty ++ tail)`)]]
    [[cst::ensure(
      `cm_emitter_plan_rep emitter out capacity
         (done ++ cm_store_code model_ty) tail`)]];

void cm_emit_fp_address(struct cm_emitter *emitter, long long offset)
    [[cst::param(`done:(tvm_inst)list`, `tail:(tvm_inst)list`,
                 `out:int`, `capacity:int`)]]
    [[cst::require(
      `cm_emitter_plan_rep emitter out capacity done
         (cm_fp_relative_address_code offset ++ tail)`)]]
    [[cst::ensure(
      `cm_emitter_plan_rep emitter out capacity
         (done ++ cm_fp_relative_address_code offset) tail`)]];

void cm_emit_temp_store(struct cm_function *fn, int temp,
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
       cm_emitter_plan_rep emitter out capacity done
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
       cm_emitter_plan_rep emitter out capacity
         (done ++ cm_temp_store_code p fid temp) tail`)]];

void cm_emit_temp_load(struct cm_function *fn, int temp,
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
       cm_emitter_plan_rep emitter out capacity done
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
       cm_emitter_plan_rep emitter out capacity
         (done ++ cm_temp_load_code p fid temp) tail`)]];

int cmc_binary_opcode(int op)
    [[cst::require(`emp`)]]
    [[cst::ensure(
      `fact((__return:int) ==
         tvm_opcode_code (cm_binary_opcode op)) **
       fact(~(tvm_opcode_code (cm_binary_opcode op) == 22i))`)]];
