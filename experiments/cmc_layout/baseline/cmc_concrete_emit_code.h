#pragma once

#include "cmc_concrete_emit_prelude.h"

void cmc_emit_code(struct cm_program *program,
                   struct cm_emitter *emitter)
    [[cst::param(`p:cm_program`, `functions_ptr:int`,
                 `done:(tvm_inst)list`, `tail:(tvm_inst)list`,
                 `out:int`, `capacity:int`)]]
    [[cst::require(
      `fact(cm_wf_program p <=> true) **
       fact(cm_typed_program p <=> true) **
       fact(cm_concrete_functions_ready p 0i
              (cm_program_functions p) <=> true) **
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
       cm_function_list_rep functions_ptr
         (cm_program_functions p) **
       cm_resolved_emitter_plan_rep p emitter out capacity done
         (cm_model_code p ++ tail)`)]]
    [[cst::ensure(
      `fact(cm_wf_program p <=> true) **
       fact(cm_typed_program p <=> true) **
       fact(cm_concrete_functions_ready p 0i
              (cm_program_functions p) <=> true) **
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
       cm_function_list_rep functions_ptr
         (cm_program_functions p) **
       cm_resolved_emitter_plan_rep p emitter out capacity
         (done ++ cm_model_code p) tail`)]];
