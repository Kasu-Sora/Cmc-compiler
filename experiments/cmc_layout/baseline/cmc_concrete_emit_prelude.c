#include "cmc_concrete_emit_prelude.h"
#include "userlib/proof.h"
#include "userlib/operational.h"
#require "cmc_concrete_emit_functions.c"

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
         (done ++ cm_emit_prelude p) tail`)]]
{
  int main_id;
  [[cst::proof]] { cm_open_program_context_st(); }
  main_id = program->main_id;
  [[cst::proof]] {
    cm_close_program_context_st();
    thm code_shape = apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          get_cm_emit_prelude_def(),
          get_theorem_by_name("APPEND"))),
        `cm_emit_prelude (p:cm_program)`);
    cm_select_code_plan_st(code_shape);
    rewrite_st(THM_LIST(get_theorem_by_name("APPEND")));
    cm_add_opcode_facts_st(`0i`, `TVMPushOp`);
    cm_add_opcode_facts_st(`5i`, `TVMStoreOp`);
    cm_add_opcode_facts_st(`12i`, `TVMModOp`);
    cm_add_opcode_facts_st(`8i`, `TVMAddOp`);
    cm_add_opcode_facts_st(`27i`, `TVMHaltOp`);
  }
  [[cst::where(`p`, `(p:cm_program)`)]]
  [[cst::where(`opcode`, `TVMPushOp`)]]
  cm_emit_plan(emitter, CMC_OP_PUSH, 1048576);
  [[cst::where(`p`, `(p:cm_program)`)]]
  [[cst::where(`opcode`, `TVMPushOp`)]]
  cm_emit_plan(emitter, CMC_OP_PUSH, 8);
  [[cst::where(`p`, `(p:cm_program)`)]]
  [[cst::where(`opcode`, `TVMStoreOp`)]]
  cm_emit_plan(emitter, CMC_OP_STORE, 0);
  [[cst::where(`p`, `(p:cm_program)`)]]
  cm_emit_call_plan(emitter, main_id);
  [[cst::where(`p`, `(p:cm_program)`)]]
  [[cst::where(`opcode`, `TVMPushOp`)]]
  cm_emit_plan(emitter, CMC_OP_PUSH, 256);
  [[cst::where(`p`, `(p:cm_program)`)]]
  [[cst::where(`opcode`, `TVMModOp`)]]
  cm_emit_plan(emitter, CMC_OP_MOD, 0);
  [[cst::where(`p`, `(p:cm_program)`)]]
  [[cst::where(`opcode`, `TVMPushOp`)]]
  cm_emit_plan(emitter, CMC_OP_PUSH, 256);
  [[cst::where(`p`, `(p:cm_program)`)]]
  [[cst::where(`opcode`, `TVMAddOp`)]]
  cm_emit_plan(emitter, CMC_OP_ADD, 0);
  [[cst::where(`p`, `(p:cm_program)`)]]
  [[cst::where(`opcode`, `TVMPushOp`)]]
  cm_emit_plan(emitter, CMC_OP_PUSH, 256);
  [[cst::where(`p`, `(p:cm_program)`)]]
  [[cst::where(`opcode`, `TVMModOp`)]]
  cm_emit_plan(emitter, CMC_OP_MOD, 0);
  [[cst::where(`p`, `(p:cm_program)`)]]
  [[cst::where(`opcode`, `TVMHaltOp`)]]
  cm_emit_plan(emitter, CMC_OP_HALT, 0);
  [[cst::proof]] {
    thm code_shape = apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          get_cm_emit_prelude_def(),
          get_theorem_by_name("APPEND"))),
        `cm_emit_prelude (p:cm_program)`);
    cm_restore_code_plan_st(code_shape);
  }
}
