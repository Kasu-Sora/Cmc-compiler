#include "cmc_layout_migration_abi.h"

struct cm_emitter {
  struct cm_output *output;
  int pc;
};

/*@ Extern Coq
    (cm_program :: *) (cm_lookup_policy :: *)
    (tvm_opcode :: *) (tvm_inst :: *)
*/
/*@ Extern Coq
    (TVMInst : tvm_opcode -> Z -> tvm_inst)
    (tvm_opcode_code : tvm_opcode -> Z)
    (TVMPushOp : tvm_opcode) (TVMLoadOp : tvm_opcode)
    (TVMStoreOp : tvm_opcode) (TVMRetOp : tvm_opcode)
    (cm_return_epilogue : list tvm_inst)
    (cm_resolved_emitter_plan_rep : cm_lookup_policy -> cm_program -> Z -> Z -> Z -> list tvm_inst -> list tvm_inst -> Assertion)
*/
/*@ Import Coq Require Import SimpleC.EE.QCP_demos_human.cmc_emit_return_migration_lib */

void cm_emit_plan(struct cm_emitter *emitter, int op, long long immediate)
/*@ With (policy : cm_lookup_policy) (p : cm_program) (done : list tvm_inst) (tail : list tvm_inst) (out : Z) (capacity : Z) (opcode : tvm_opcode)
    Require op == tvm_opcode_code(opcode) && tvm_opcode_code(opcode) != 22 && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, cons(TVMInst(opcode, immediate), tail))
    Ensure cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cons(TVMInst(opcode, immediate), nil)), tail)
*/;

void cm_emit_return_epilogue_plan(struct cm_emitter *emitter)
/*@ With (policy : cm_lookup_policy) (p : cm_program) (done : list tvm_inst) (tail : list tvm_inst) (out : Z) (capacity : Z)
    Require cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_return_epilogue, tail))
    Ensure cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cm_return_epilogue), tail)
*/
{
  /*@ Assert emitter == emitter@pre &&
      tvm_opcode_code(TVMPushOp) == 0 && tvm_opcode_code(TVMPushOp) != 22 &&
      tvm_opcode_code(TVMLoadOp) == 4 && tvm_opcode_code(TVMLoadOp) != 22 &&
      tvm_opcode_code(TVMStoreOp) == 5 && tvm_opcode_code(TVMStoreOp) != 22 &&
      tvm_opcode_code(TVMRetOp) == 23 && tvm_opcode_code(TVMRetOp) != 22 &&
      cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done,
        cons(TVMInst(TVMPushOp, 8), cons(TVMInst(TVMLoadOp, 0), cons(TVMInst(TVMLoadOp, 0),
        cons(TVMInst(TVMPushOp, 8), cons(TVMInst(TVMStoreOp, 0), cons(TVMInst(TVMRetOp, 0), tail)))))))
  */
  cm_emit_plan(emitter, CMC_OP_PUSH, 8) /*@ where policy = policy, p = p, done = done, tail = cons(TVMInst(TVMLoadOp, 0), cons(TVMInst(TVMLoadOp, 0), cons(TVMInst(TVMPushOp, 8), cons(TVMInst(TVMStoreOp, 0), cons(TVMInst(TVMRetOp, 0), tail))))), out = out, capacity = capacity, opcode = TVMPushOp */;
  cm_emit_plan(emitter, CMC_OP_LOAD, 0) /*@ where policy = policy, p = p, done = app(done, cons(TVMInst(TVMPushOp, 8), nil)), tail = cons(TVMInst(TVMLoadOp, 0), cons(TVMInst(TVMPushOp, 8), cons(TVMInst(TVMStoreOp, 0), cons(TVMInst(TVMRetOp, 0), tail)))), out = out, capacity = capacity, opcode = TVMLoadOp */;
  cm_emit_plan(emitter, CMC_OP_LOAD, 0) /*@ where policy = policy, p = p, done = app(app(done, cons(TVMInst(TVMPushOp, 8), nil)), cons(TVMInst(TVMLoadOp, 0), nil)), tail = cons(TVMInst(TVMPushOp, 8), cons(TVMInst(TVMStoreOp, 0), cons(TVMInst(TVMRetOp, 0), tail))), out = out, capacity = capacity, opcode = TVMLoadOp */;
  cm_emit_plan(emitter, CMC_OP_PUSH, 8) /*@ where policy = policy, p = p, done = app(app(app(done, cons(TVMInst(TVMPushOp, 8), nil)), cons(TVMInst(TVMLoadOp, 0), nil)), cons(TVMInst(TVMLoadOp, 0), nil)), tail = cons(TVMInst(TVMStoreOp, 0), cons(TVMInst(TVMRetOp, 0), tail)), out = out, capacity = capacity, opcode = TVMPushOp */;
  cm_emit_plan(emitter, CMC_OP_STORE, 0) /*@ where policy = policy, p = p, done = app(app(app(app(done, cons(TVMInst(TVMPushOp, 8), nil)), cons(TVMInst(TVMLoadOp, 0), nil)), cons(TVMInst(TVMLoadOp, 0), nil)), cons(TVMInst(TVMPushOp, 8), nil)), tail = cons(TVMInst(TVMRetOp, 0), tail), out = out, capacity = capacity, opcode = TVMStoreOp */;
  cm_emit_plan(emitter, CMC_OP_RET, 0) /*@ where policy = policy, p = p, done = app(app(app(app(app(done, cons(TVMInst(TVMPushOp, 8), nil)), cons(TVMInst(TVMLoadOp, 0), nil)), cons(TVMInst(TVMLoadOp, 0), nil)), cons(TVMInst(TVMPushOp, 8), nil)), cons(TVMInst(TVMStoreOp, 0), nil)), tail = tail, out = out, capacity = capacity, opcode = TVMRetOp */;
}
