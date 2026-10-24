#include "cmc_layout_migration_abi.h"

struct cm_emitter {
  struct cm_output *output;
  int pc;
};

/*@ Extern Coq
    (cm_function_d :: *) (cm_program :: *) (cm_lookup_policy :: *)
    (cm_codegen_obligations :: *) (tvm_opcode :: *) (tvm_inst :: *)
*/
/*@ Extern Coq
    (TVMInst : tvm_opcode -> Z -> tvm_inst)
    (tvm_opcode_code : tvm_opcode -> Z)
    (cm_rep_ops : list tvm_inst -> list Z)
    (cm_rep_imms : list tvm_inst -> list Z)
    (cm_patch_arrays_rep : Z -> Z -> Z -> list tvm_inst -> Assertion)
    (cm_patch_tail : list tvm_inst -> list tvm_inst)
    (cm_patch_code : cm_lookup_policy -> cm_program -> list tvm_inst -> list tvm_inst)
    (cm_program_functions : cm_program -> list cm_function_d)
    (cm_wf_program : cm_lookup_policy -> cm_codegen_obligations -> cm_program -> Prop)
    (cm_concrete_code_ready : cm_lookup_policy -> cm_program -> Prop)
    (cm_function_pc : cm_lookup_policy -> cm_program -> Z -> Z)
    (cm_i32_code_count : Z -> Prop)
    (cm_program_context_rep : Z -> cm_program -> Z -> Assertion)
    (cm_function_list_rep : Z -> list cm_function_d -> Assertion)
    (cm_emitter_rep : Z -> Z -> Z -> list Z -> list Z -> Assertion)
    (cm_resolved_emitter_rep : cm_lookup_policy -> cm_program -> Z -> Z -> Z -> list tvm_inst -> Assertion)
    (Int64Array::full : Z -> Z -> list Z -> Assertion)
    (IntArray::seg : Z -> Z -> Z -> list Z -> Assertion)
    (IntArray::undef_seg : Z -> Z -> Z -> Assertion)
    (Int64Array::seg : Z -> Z -> Z -> list Z -> Assertion)
    (Int64Array::undef_seg : Z -> Z -> Z -> Assertion)
*/
/*@ Import Coq Require Import SimpleC.EE.QCP_demos_human.cmc_patch_calls_migration_lib */

int cmc_function_pc_total(struct cm_program *program, long long target)
/*@ With (policy : cm_lookup_policy) (cg : cm_codegen_obligations) (p : cm_program) (functions_ptr : Z)
    Require cm_wf_program(policy, cg, p) && cm_concrete_code_ready(policy, p) && cm_program_context_rep(program, p, functions_ptr) * cm_function_list_rep(functions_ptr, cm_program_functions(p))
    Ensure cm_wf_program(policy, cg, p) && cm_concrete_code_ready(policy, p) && __return == cm_function_pc(policy, p, target) && cm_i32_code_count(__return) && cm_program_context_rep(program, p, functions_ptr) * cm_function_list_rep(functions_ptr, cm_program_functions(p))
*/;

static void cmc_patch_code_arrays(
    struct cm_program *program, int *ops, long long *imms, int length)
/*@ With (policy : cm_lookup_policy) (cg : cm_codegen_obligations) (p : cm_program) (raw : list tvm_inst) (functions_ptr : Z)
    Require cm_wf_program(policy, cg, p) && cm_concrete_code_ready(policy, p) && 0 <= length && length <= 2147483647 && length == Zlength(raw) && cm_program_context_rep(program, p, functions_ptr) * cm_function_list_rep(functions_ptr, cm_program_functions(p)) * cm_patch_arrays_rep(ops, imms, length, raw)
    Ensure cm_wf_program(policy, cg, p) && cm_concrete_code_ready(policy, p) && 0 <= length && length <= 2147483647 && length == Zlength(raw) && cm_program_context_rep(program, p, functions_ptr) * cm_function_list_rep(functions_ptr, cm_program_functions(p)) * cm_patch_arrays_rep(ops, imms, length, cm_patch_code(policy, p, raw))
*/
{
  if (length == 0) {
    return;
  };
  /*@ Assert exists (opcode : tvm_opcode) (model_imm : Z),
    program == program@pre && ops == ops@pre && imms == imms@pre && length == length@pre &&
    cm_wf_program(policy, cg, p) && cm_concrete_code_ready(policy, p) && 1 <= length && length <= 2147483647 && length == Zlength(raw) &&
    raw == cons(TVMInst(opcode, model_imm), cm_patch_tail(raw)) &&
    length - 1 == Zlength(cm_patch_tail(raw)) &&
    cm_program_context_rep(program, p, functions_ptr) * cm_function_list_rep(functions_ptr, cm_program_functions(p)) *
    data_at(ops, int, tvm_opcode_code(opcode)) *
    data_at(imms, long long, model_imm) *
    cm_patch_arrays_rep(ops + 1, imms + 1, length - 1, cm_patch_tail(raw))
  */
  int op = *ops;
  long long immediate = *imms;
  int *remaining_ops = ops + 1;
  long long *remaining_imms = imms + 1;
  int remaining_length = length - 1;
  if (op == CMC_OP_CALL) {
    int pc = cmc_function_pc_total(program, immediate) /*@ where policy = policy, cg = cg, p = p, functions_ptr = functions_ptr */;
    *imms = pc;
    cmc_patch_code_arrays(
        program, remaining_ops, remaining_imms, remaining_length) /*@ where policy = policy, cg = cg, p = p, raw = cm_patch_tail(raw), functions_ptr = functions_ptr */;
  } else {
    cmc_patch_code_arrays(
        program, remaining_ops, remaining_imms, remaining_length) /*@ where policy = policy, cg = cg, p = p, raw = cm_patch_tail(raw), functions_ptr = functions_ptr */;
  };
}

void cmc_patch_resolved_calls(struct cm_program *program,
                              struct cm_emitter *emitter)
/*@ With (policy : cm_lookup_policy) (cg : cm_codegen_obligations) (p : cm_program) (resolved : list tvm_inst) (functions_ptr : Z) (out : Z) (capacity : Z)
    Require cm_wf_program(policy, cg, p) && cm_concrete_code_ready(policy, p) && cm_program_context_rep(program, p, functions_ptr) * cm_function_list_rep(functions_ptr, cm_program_functions(p)) * cm_resolved_emitter_rep(policy, p, emitter, out, capacity, resolved)
    Ensure cm_wf_program(policy, cg, p) && cm_concrete_code_ready(policy, p) && cm_program_context_rep(program, p, functions_ptr) * cm_function_list_rep(functions_ptr, cm_program_functions(p)) * cm_emitter_rep(emitter, out, capacity, cm_rep_ops(resolved), cm_rep_imms(resolved))
*/
{
  /*@ Assert exists (raw_prefix : list tvm_inst) (ops_ptr : Z) (imms_ptr : Z),
    program == program@pre && emitter == emitter@pre &&
    cm_wf_program(policy, cg, p) && cm_concrete_code_ready(policy, p) && cm_patch_code(policy, p, raw_prefix) == resolved &&
    out != 0 && ops_ptr != 0 && imms_ptr != 0 &&
    0 <= Zlength(raw_prefix) && Zlength(raw_prefix) <= capacity && capacity <= 2147483647 &&
    cm_program_context_rep(program, p, functions_ptr) * cm_function_list_rep(functions_ptr, cm_program_functions(p)) *
    data_at(&(emitter->output), struct cm_output *, out) *
    data_at(&(emitter->pc), int, Zlength(raw_prefix)) *
    data_at(&(((struct cm_output *)out)->ops), int *, ops_ptr) *
    data_at(&(((struct cm_output *)out)->imms), long long *, imms_ptr) *
    data_at(&(((struct cm_output *)out)->code_capacity), int, capacity) *
    cm_patch_arrays_rep(ops_ptr, imms_ptr, Zlength(raw_prefix), raw_prefix) *
    IntArray::undef_seg(ops_ptr, Zlength(raw_prefix), capacity) *
    Int64Array::undef_seg(imms_ptr, Zlength(raw_prefix), capacity)
  */
  struct cm_output *output = emitter->output;
  int length = emitter->pc;
  int *ops = output->ops;
  long long *imms = output->imms;
  cmc_patch_code_arrays(program, ops, imms, length) /*@ where policy = policy, cg = cg, p = p, functions_ptr = functions_ptr */;
}
