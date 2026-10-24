#pragma once

#include "cmc_concrete_emit_resolved.h"
#require "cmc_concrete_emit_resolved.c"

void cm_emit_binding_address(struct cm_program *program,
                             struct cm_function *fn,
                             int scope, int slot,
                             struct cm_emitter *emitter)
    [[cst::param(`p:cm_program`, `f:cm_function_d`, `fid:int`,
                 `structs:(cm_struct_d)list`,
                 `globals:(cm_global_d)list`,
                 `functions_ptr:int`, `body:int`, `next:int`,
                 `done:(tvm_inst)list`, `out:int`, `capacity:int`)]]
    [[cst::require(
      `fact(cm_wf_program p <=> true) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(structs == cm_program_structs p) **
       fact(globals == cm_program_globals p) **
       fact(cm_binding_valid p f scope slot <=> true) **
       fact(cm_slots_wf structs (cm_function_params f) <=> true) **
       fact(cm_slots_wf structs (cm_function_locals f) <=> true) **
       fact(cm_rep_globals_safe globals <=> true) **
       fact(cm_rep_members_safe (cm_function_params f) <=> true) **
       fact(cm_rep_members_safe (cm_function_locals f) <=> true) **
       fact(ilength done +
              ilength (cm_binding_address_code p fid scope slot) <=
              capacity) **
       cm_program_context_rep program p functions_ptr **
       cm_function_context_rep fn f body next **
       cm_resolved_emitter_rep p emitter out capacity done`)]]
    [[cst::ensure(
      `fact(cm_wf_program p <=> true) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(structs == cm_program_structs p) **
       fact(globals == cm_program_globals p) **
       fact(cm_binding_valid p f scope slot <=> true) **
       fact(cm_slots_wf structs (cm_function_params f) <=> true) **
       fact(cm_slots_wf structs (cm_function_locals f) <=> true) **
       fact(cm_rep_globals_safe globals <=> true) **
       fact(cm_rep_members_safe (cm_function_params f) <=> true) **
       fact(cm_rep_members_safe (cm_function_locals f) <=> true) **
       cm_program_context_rep program p functions_ptr **
       cm_function_context_rep fn f body next **
       cm_resolved_emitter_rep p emitter out capacity
         (done ++ cm_binding_address_code p fid scope slot)`)]];

void cm_emit_binding_address_plan(struct cm_program *program,
                                  struct cm_function *fn,
                                  int scope, int slot,
                                  struct cm_emitter *emitter)
    [[cst::param(`p:cm_program`, `f:cm_function_d`, `fid:int`,
                 `structs:(cm_struct_d)list`,
                 `globals:(cm_global_d)list`,
                 `functions_ptr:int`, `body:int`, `next:int`,
                 `done:(tvm_inst)list`, `tail:(tvm_inst)list`,
                 `out:int`, `capacity:int`)]]
    [[cst::require(
      `fact(cm_wf_program p <=> true) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(structs == cm_program_structs p) **
       fact(globals == cm_program_globals p) **
       fact(cm_binding_valid p f scope slot <=> true) **
       fact(cm_slots_wf structs (cm_function_params f) <=> true) **
       fact(cm_slots_wf structs (cm_function_locals f) <=> true) **
       fact(cm_rep_globals_safe globals <=> true) **
       fact(cm_rep_members_safe (cm_function_params f) <=> true) **
       fact(cm_rep_members_safe (cm_function_locals f) <=> true) **
       cm_program_context_rep program p functions_ptr **
       cm_function_context_rep fn f body next **
       cm_resolved_emitter_plan_rep p emitter out capacity done
         (cm_binding_address_code p fid scope slot ++ tail)`)]]
    [[cst::ensure(
      `fact(cm_wf_program p <=> true) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(structs == cm_program_structs p) **
       fact(globals == cm_program_globals p) **
       fact(cm_binding_valid p f scope slot <=> true) **
       fact(cm_slots_wf structs (cm_function_params f) <=> true) **
       fact(cm_slots_wf structs (cm_function_locals f) <=> true) **
       fact(cm_rep_globals_safe globals <=> true) **
       fact(cm_rep_members_safe (cm_function_params f) <=> true) **
       fact(cm_rep_members_safe (cm_function_locals f) <=> true) **
       cm_program_context_rep program p functions_ptr **
       cm_function_context_rep fn f body next **
       cm_resolved_emitter_plan_rep p emitter out capacity
         (done ++ cm_binding_address_code p fid scope slot) tail`)]];
