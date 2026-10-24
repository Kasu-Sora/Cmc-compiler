#pragma once

#include "cmc_concrete_emit_plan.h"
#require "cmc_concrete_emit_plan.c"

void cm_emit_return_epilogue_plan(struct cm_emitter *emitter)
    [[cst::param(`p:cm_program`, `done:(tvm_inst)list`,
                 `tail:(tvm_inst)list`, `out:int`, `capacity:int`)]]
    [[cst::require(
      `cm_resolved_emitter_plan_rep p emitter out capacity done
         (cm_return_epilogue ++ tail)`)]]
    [[cst::ensure(
      `cm_resolved_emitter_plan_rep p emitter out capacity
         (done ++ cm_return_epilogue) tail`)]];
