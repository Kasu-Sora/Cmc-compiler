#include "cmc_layout_migration_abi.h"

struct cm_emitter {
  struct cm_output *output;
  int pc;
};

/*@ Extern Coq
 (cm_program :: *) (cm_lookup_policy :: *) (tvm_opcode :: *) (tvm_inst :: *)
 (cm_struct_d :: *) (cm_global_d :: *) (cm_string_d :: *)
*/
/*@ Extern Coq
 (TVMInst : tvm_opcode -> Z -> tvm_inst)
 (TVMPushOp : tvm_opcode) (TVMStoreOp : tvm_opcode) (TVMCallOp : tvm_opcode)
 (TVMModOp : tvm_opcode) (TVMAddOp : tvm_opcode) (TVMHaltOp : tvm_opcode)
 (tvm_opcode_code : tvm_opcode -> Z)
 (cm_program_main : cm_program -> Z)
 (cm_program_structs : cm_program -> list cm_struct_d)
 (cm_program_globals : cm_program -> list cm_global_d)
 (cm_program_strings : cm_program -> list cm_string_d)
 (cm_struct_list_rep : Z -> list cm_struct_d -> Assertion)
 (cm_global_list_rep : Z -> list cm_global_d -> Assertion)
 (cm_string_list_rep : Z -> list cm_string_d -> Assertion)
 (cm_program_context_rep : Z -> cm_program -> Z -> Assertion)
 (cm_function_pc : cm_lookup_policy -> cm_program -> Z -> Z)
 (cm_emit_prelude : cm_lookup_policy -> cm_program -> list tvm_inst)
 (cm_resolved_emitter_plan_rep : cm_lookup_policy -> cm_program -> Z -> Z -> Z -> list tvm_inst -> list tvm_inst -> Assertion)
*/
/*@ Import Coq Require Import SimpleC.EE.QCP_demos_human.cmc_emit_prelude_migration_lib */

void cm_emit_plan(struct cm_emitter *emitter, int op, long long immediate)
/*@ With (policy : cm_lookup_policy) (p : cm_program) (done : list tvm_inst) (tail : list tvm_inst) (out : Z) (capacity : Z) (opcode : tvm_opcode)
    Require op == tvm_opcode_code(opcode) && tvm_opcode_code(opcode) != 22 && cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, cons(TVMInst(opcode, immediate), tail))
    Ensure cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cons(TVMInst(opcode, immediate), nil)), tail)
*/;
void cm_emit_call_plan(struct cm_emitter *emitter, int function_id)
/*@ With (policy : cm_lookup_policy) (p : cm_program) (done : list tvm_inst) (tail : list tvm_inst) (out : Z) (capacity : Z)
    Require cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, cons(TVMInst(TVMCallOp, cm_function_pc(policy, p, function_id)), tail))
    Ensure cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cons(TVMInst(TVMCallOp, cm_function_pc(policy, p, function_id)), nil)), tail)
*/;

void cmc_emit_prelude(struct cm_program *program,
                      struct cm_emitter *emitter)
/*@ With (policy : cm_lookup_policy) (p : cm_program) (functions_ptr : Z) (done : list tvm_inst) (tail : list tvm_inst) (out : Z) (capacity : Z)
 Require cm_program_context_rep(program, p, functions_ptr) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_emit_prelude(policy, p), tail))
 Ensure cm_program_context_rep(program, p, functions_ptr) * cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, app(done, cm_emit_prelude(policy, p)), tail)
*/
{
  int main_id;
  /*@ Assert exists (sp : Z) (gp : Z) (tp : Z),
    program == program@pre && emitter == emitter@pre && program != 0 &&
    undef_data_at(&main_id, int) *
    data_at(&(program->structs), struct cm_struct *, sp) *
    data_at(&(program->globals), struct cm_global *, gp) *
    data_at(&(program->strings), struct cm_string *, tp) *
    data_at(&(program->functions), struct cm_function *, functions_ptr) *
    data_at(&(program->main_id), int, cm_program_main(p)) *
    cm_struct_list_rep(sp, cm_program_structs(p)) *
    cm_global_list_rep(gp, cm_program_globals(p)) *
    cm_string_list_rep(tp, cm_program_strings(p)) *
    cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, app(cm_emit_prelude(policy, p), tail))
  */
  main_id = program->main_id;
  /*@ Assert program == program@pre && emitter == emitter@pre && main_id == cm_program_main(p) &&
    tvm_opcode_code(TVMPushOp) == 0 && tvm_opcode_code(TVMStoreOp) == 5 &&
    tvm_opcode_code(TVMModOp) == 12 && tvm_opcode_code(TVMAddOp) == 8 && tvm_opcode_code(TVMHaltOp) == 27 &&
    cm_program_context_rep(program, p, functions_ptr) *
    cm_resolved_emitter_plan_rep(policy, p, emitter, out, capacity, done, cons(TVMInst(TVMPushOp, 1048576), cons(TVMInst(TVMPushOp, 8), cons(TVMInst(TVMStoreOp, 0), cons(TVMInst(TVMCallOp, cm_function_pc(policy, p, main_id)), cons(TVMInst(TVMPushOp, 256), cons(TVMInst(TVMModOp, 0), cons(TVMInst(TVMPushOp, 256), cons(TVMInst(TVMAddOp, 0), cons(TVMInst(TVMPushOp, 256), cons(TVMInst(TVMModOp, 0), cons(TVMInst(TVMHaltOp, 0), tail))))))))))))
  */
  cm_emit_plan(emitter, CMC_OP_PUSH, 1048576) /*@ where policy = policy, p = p, done = done, tail = cons(TVMInst(TVMPushOp, 8), cons(TVMInst(TVMStoreOp, 0), cons(TVMInst(TVMCallOp, cm_function_pc(policy, p, main_id)), cons(TVMInst(TVMPushOp, 256), cons(TVMInst(TVMModOp, 0), cons(TVMInst(TVMPushOp, 256), cons(TVMInst(TVMAddOp, 0), cons(TVMInst(TVMPushOp, 256), cons(TVMInst(TVMModOp, 0), cons(TVMInst(TVMHaltOp, 0), tail)))))))))), out = out, capacity = capacity, opcode = TVMPushOp */;
  cm_emit_plan(emitter, CMC_OP_PUSH, 8) /*@ where policy = policy, p = p, done = app(done, cons(TVMInst(TVMPushOp, 1048576), nil)), tail = cons(TVMInst(TVMStoreOp, 0), cons(TVMInst(TVMCallOp, cm_function_pc(policy, p, main_id)), cons(TVMInst(TVMPushOp, 256), cons(TVMInst(TVMModOp, 0), cons(TVMInst(TVMPushOp, 256), cons(TVMInst(TVMAddOp, 0), cons(TVMInst(TVMPushOp, 256), cons(TVMInst(TVMModOp, 0), cons(TVMInst(TVMHaltOp, 0), tail))))))))), out = out, capacity = capacity, opcode = TVMPushOp */;
  cm_emit_plan(emitter, CMC_OP_STORE, 0) /*@ where policy = policy, p = p, done = app(app(done, cons(TVMInst(TVMPushOp, 1048576), nil)), cons(TVMInst(TVMPushOp, 8), nil)), tail = cons(TVMInst(TVMCallOp, cm_function_pc(policy, p, main_id)), cons(TVMInst(TVMPushOp, 256), cons(TVMInst(TVMModOp, 0), cons(TVMInst(TVMPushOp, 256), cons(TVMInst(TVMAddOp, 0), cons(TVMInst(TVMPushOp, 256), cons(TVMInst(TVMModOp, 0), cons(TVMInst(TVMHaltOp, 0), tail)))))))), out = out, capacity = capacity, opcode = TVMStoreOp */;
  cm_emit_call_plan(emitter, main_id) /*@ where policy = policy, p = p, done = app(app(app(done, cons(TVMInst(TVMPushOp, 1048576), nil)), cons(TVMInst(TVMPushOp, 8), nil)), cons(TVMInst(TVMStoreOp, 0), nil)), tail = cons(TVMInst(TVMPushOp, 256), cons(TVMInst(TVMModOp, 0), cons(TVMInst(TVMPushOp, 256), cons(TVMInst(TVMAddOp, 0), cons(TVMInst(TVMPushOp, 256), cons(TVMInst(TVMModOp, 0), cons(TVMInst(TVMHaltOp, 0), tail))))))), out = out, capacity = capacity */;
  cm_emit_plan(emitter, CMC_OP_PUSH, 256) /*@ where policy = policy, p = p, done = app(app(app(app(done, cons(TVMInst(TVMPushOp, 1048576), nil)), cons(TVMInst(TVMPushOp, 8), nil)), cons(TVMInst(TVMStoreOp, 0), nil)), cons(TVMInst(TVMCallOp, cm_function_pc(policy, p, main_id)), nil)), tail = cons(TVMInst(TVMModOp, 0), cons(TVMInst(TVMPushOp, 256), cons(TVMInst(TVMAddOp, 0), cons(TVMInst(TVMPushOp, 256), cons(TVMInst(TVMModOp, 0), cons(TVMInst(TVMHaltOp, 0), tail)))))), out = out, capacity = capacity, opcode = TVMPushOp */;
  cm_emit_plan(emitter, CMC_OP_MOD, 0) /*@ where policy = policy, p = p, done = app(app(app(app(app(done, cons(TVMInst(TVMPushOp, 1048576), nil)), cons(TVMInst(TVMPushOp, 8), nil)), cons(TVMInst(TVMStoreOp, 0), nil)), cons(TVMInst(TVMCallOp, cm_function_pc(policy, p, main_id)), nil)), cons(TVMInst(TVMPushOp, 256), nil)), tail = cons(TVMInst(TVMPushOp, 256), cons(TVMInst(TVMAddOp, 0), cons(TVMInst(TVMPushOp, 256), cons(TVMInst(TVMModOp, 0), cons(TVMInst(TVMHaltOp, 0), tail))))), out = out, capacity = capacity, opcode = TVMModOp */;
  cm_emit_plan(emitter, CMC_OP_PUSH, 256) /*@ where policy = policy, p = p, done = app(app(app(app(app(app(done, cons(TVMInst(TVMPushOp, 1048576), nil)), cons(TVMInst(TVMPushOp, 8), nil)), cons(TVMInst(TVMStoreOp, 0), nil)), cons(TVMInst(TVMCallOp, cm_function_pc(policy, p, main_id)), nil)), cons(TVMInst(TVMPushOp, 256), nil)), cons(TVMInst(TVMModOp, 0), nil)), tail = cons(TVMInst(TVMAddOp, 0), cons(TVMInst(TVMPushOp, 256), cons(TVMInst(TVMModOp, 0), cons(TVMInst(TVMHaltOp, 0), tail)))), out = out, capacity = capacity, opcode = TVMPushOp */;
  cm_emit_plan(emitter, CMC_OP_ADD, 0) /*@ where policy = policy, p = p, done = app(app(app(app(app(app(app(done, cons(TVMInst(TVMPushOp, 1048576), nil)), cons(TVMInst(TVMPushOp, 8), nil)), cons(TVMInst(TVMStoreOp, 0), nil)), cons(TVMInst(TVMCallOp, cm_function_pc(policy, p, main_id)), nil)), cons(TVMInst(TVMPushOp, 256), nil)), cons(TVMInst(TVMModOp, 0), nil)), cons(TVMInst(TVMPushOp, 256), nil)), tail = cons(TVMInst(TVMPushOp, 256), cons(TVMInst(TVMModOp, 0), cons(TVMInst(TVMHaltOp, 0), tail))), out = out, capacity = capacity, opcode = TVMAddOp */;
  cm_emit_plan(emitter, CMC_OP_PUSH, 256) /*@ where policy = policy, p = p, done = app(app(app(app(app(app(app(app(done, cons(TVMInst(TVMPushOp, 1048576), nil)), cons(TVMInst(TVMPushOp, 8), nil)), cons(TVMInst(TVMStoreOp, 0), nil)), cons(TVMInst(TVMCallOp, cm_function_pc(policy, p, main_id)), nil)), cons(TVMInst(TVMPushOp, 256), nil)), cons(TVMInst(TVMModOp, 0), nil)), cons(TVMInst(TVMPushOp, 256), nil)), cons(TVMInst(TVMAddOp, 0), nil)), tail = cons(TVMInst(TVMModOp, 0), cons(TVMInst(TVMHaltOp, 0), tail)), out = out, capacity = capacity, opcode = TVMPushOp */;
  cm_emit_plan(emitter, CMC_OP_MOD, 0) /*@ where policy = policy, p = p, done = app(app(app(app(app(app(app(app(app(done, cons(TVMInst(TVMPushOp, 1048576), nil)), cons(TVMInst(TVMPushOp, 8), nil)), cons(TVMInst(TVMStoreOp, 0), nil)), cons(TVMInst(TVMCallOp, cm_function_pc(policy, p, main_id)), nil)), cons(TVMInst(TVMPushOp, 256), nil)), cons(TVMInst(TVMModOp, 0), nil)), cons(TVMInst(TVMPushOp, 256), nil)), cons(TVMInst(TVMAddOp, 0), nil)), cons(TVMInst(TVMPushOp, 256), nil)), tail = cons(TVMInst(TVMHaltOp, 0), tail), out = out, capacity = capacity, opcode = TVMModOp */;
  cm_emit_plan(emitter, CMC_OP_HALT, 0) /*@ where policy = policy, p = p, done = app(app(app(app(app(app(app(app(app(app(done, cons(TVMInst(TVMPushOp, 1048576), nil)), cons(TVMInst(TVMPushOp, 8), nil)), cons(TVMInst(TVMStoreOp, 0), nil)), cons(TVMInst(TVMCallOp, cm_function_pc(policy, p, main_id)), nil)), cons(TVMInst(TVMPushOp, 256), nil)), cons(TVMInst(TVMModOp, 0), nil)), cons(TVMInst(TVMPushOp, 256), nil)), cons(TVMInst(TVMAddOp, 0), nil)), cons(TVMInst(TVMPushOp, 256), nil)), cons(TVMInst(TVMModOp, 0), nil)), tail = tail, out = out, capacity = capacity, opcode = TVMHaltOp */;
}
