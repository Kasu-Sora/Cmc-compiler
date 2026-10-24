#pragma once

#include "cmc_concrete_defs.h"
#require "cmc_concrete_defs.c"
#include "cmc_concrete_function_pc_total.h"
#include "cmc_concrete_emit_core.h"

void cmc_patch_resolved_calls(struct cm_program *program,
                              struct cm_emitter *emitter)
    [[cst::param(`p:cm_program`, `resolved:(tvm_inst)list`,
                 `functions_ptr:int`, `out:int`, `capacity:int`)]]
    [[cst::require(
      `fact(cm_wf_program p <=> true) **
       fact(cm_concrete_code_ready p <=> true) **
       cm_program_context_rep program p functions_ptr **
       cm_function_list_rep functions_ptr (cm_program_functions p) **
       cm_resolved_emitter_rep p emitter out capacity resolved`)]]
    [[cst::ensure(
      `fact(cm_wf_program p <=> true) **
       fact(cm_concrete_code_ready p <=> true) **
       cm_program_context_rep program p functions_ptr **
       cm_function_list_rep functions_ptr (cm_program_functions p) **
       cm_emitter_rep emitter out capacity
         (cm_rep_ops resolved) (cm_rep_imms resolved)`)]];
