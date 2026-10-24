#pragma once

#include "cmc_concrete_emit_functions.h"

void cmc_emit_prelude(struct cm_program *program,
                      struct cm_emitter *emitter)
    [[cst::param(`p:cm_program`, `functions_ptr:int`,
                 `done:(tvm_inst)list`, `tail:(tvm_inst)list`,
                 `out:int`, `capacity:int`)]]
    [[cst::require(
      `cm_program_context_rep program p functions_ptr **
       cm_resolved_emitter_plan_rep p emitter out capacity done
         (cm_emit_prelude p ++ tail)`)]]
    [[cst::ensure(
      `cm_program_context_rep program p functions_ptr **
       cm_resolved_emitter_plan_rep p emitter out capacity
         (done ++ cm_emit_prelude p) tail`)]];
