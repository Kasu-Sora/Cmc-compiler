#pragma once

#include "cmc_concrete_emit_function.h"

void cmc_emit_functions(
    struct cm_program *program, struct cm_function *fn,
    int fid, int function_pc, struct cm_emitter *emitter)
    [[cst::param(`p:cm_program`, `functions:(cm_function_d)list`,
                 `functions_ptr:int`,
                 `done:(tvm_inst)list`, `tail:(tvm_inst)list`,
                 `out:int`, `capacity:int`)]]
    [[cst::require(
      `fact(cm_wf_program p <=> true) **
       fact(cm_typed_program p <=> true) **
       fact(function_pc == cm_function_pc p fid) **
       fact(cm_concrete_functions_ready p fid functions <=> true) **
       fact(cm_rep_structs_safe
              (cm_program_structs p) <=> true) **
       fact(cm_rep_globals_safe
              (cm_program_globals p) <=> true) **
       fact(cm_rep_strings_safe
              (cm_program_strings p) <=> true) **
       fact(cm_rep_globals_size (cm_program_globals p) +
              cm_rep_strings_size (cm_program_strings p) <=
              1048560i) **
       cm_program_context_rep program p functions_ptr **
       cm_function_list_rep fn functions **
       cm_resolved_emitter_plan_rep p emitter out capacity done
         (cm_emit_functions p fid functions ++ tail)`)]]
    [[cst::ensure(
      `fact(cm_wf_program p <=> true) **
       fact(cm_typed_program p <=> true) **
       fact(function_pc == cm_function_pc p fid) **
       fact(cm_concrete_functions_ready p fid functions <=> true) **
       fact(cm_rep_structs_safe
              (cm_program_structs p) <=> true) **
       fact(cm_rep_globals_safe
              (cm_program_globals p) <=> true) **
       fact(cm_rep_strings_safe
              (cm_program_strings p) <=> true) **
       fact(cm_rep_globals_size (cm_program_globals p) +
              cm_rep_strings_size (cm_program_strings p) <=
              1048560i) **
       cm_program_context_rep program p functions_ptr **
       cm_function_list_rep fn functions **
       cm_resolved_emitter_plan_rep p emitter out capacity
         (done ++ cm_emit_functions p fid functions) tail`)]];
