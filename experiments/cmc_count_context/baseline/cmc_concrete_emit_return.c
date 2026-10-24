#include "cmc_concrete_emit_return.h"
#include "userlib/proof.h"
#include "userlib/operational.h"
#require "cmc_concrete_emit_plan.c"

void cm_emit_return_epilogue_plan(struct cm_emitter *emitter)
    [[cst::param(`p:cm_program`, `done:(tvm_inst)list`,
                 `tail:(tvm_inst)list`, `out:int`, `capacity:int`)]]
    [[cst::require(
      `cm_resolved_emitter_plan_rep p emitter out capacity done
         (cm_return_epilogue ++ tail)`)]]
    [[cst::ensure(
      `cm_resolved_emitter_plan_rep p emitter out capacity
         (done ++ cm_return_epilogue) tail`)]]
{
  [[cst::proof]] {
    cm_select_code_plan_st(get_cm_return_epilogue_def());
    rewrite_st(THM_LIST(get_theorem_by_name("APPEND")));
    cm_add_opcode_facts_st(`0i`, `TVMPushOp`);
  }
  [[cst::where(`p`, `(p:cm_program)`)]]
  [[cst::where(`opcode`, `TVMPushOp`)]]
  cm_emit_plan(emitter, CMC_OP_PUSH, 8);
  [[cst::proof]] { cm_add_opcode_facts_st(`4i`, `TVMLoadOp`); }
  [[cst::where(`p`, `(p:cm_program)`)]]
  [[cst::where(`opcode`, `TVMLoadOp`)]]
  cm_emit_plan(emitter, CMC_OP_LOAD, 0);
  [[cst::where(`p`, `(p:cm_program)`)]]
  [[cst::where(`opcode`, `TVMLoadOp`)]]
  cm_emit_plan(emitter, CMC_OP_LOAD, 0);
  [[cst::proof]] { cm_add_opcode_facts_st(`0i`, `TVMPushOp`); }
  [[cst::where(`p`, `(p:cm_program)`)]]
  [[cst::where(`opcode`, `TVMPushOp`)]]
  cm_emit_plan(emitter, CMC_OP_PUSH, 8);
  [[cst::proof]] { cm_add_opcode_facts_st(`5i`, `TVMStoreOp`); }
  [[cst::where(`p`, `(p:cm_program)`)]]
  [[cst::where(`opcode`, `TVMStoreOp`)]]
  cm_emit_plan(emitter, CMC_OP_STORE, 0);
  [[cst::proof]] { cm_add_opcode_facts_st(`23i`, `TVMRetOp`); }
  [[cst::where(`p`, `(p:cm_program)`)]]
  [[cst::where(`opcode`, `TVMRetOp`)]]
  cm_emit_plan(emitter, CMC_OP_RET, 0);
  [[cst::proof]] {
    cm_restore_code_plan_st(get_cm_return_epilogue_def());
  }
}
