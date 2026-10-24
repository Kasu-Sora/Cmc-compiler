#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_target_jump_valid.h"

#require "cmc_preservation_code.c"

PROOF static size_t _cmc_preservation_target_jump_valid_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_jump_valid_pick(thm fact, term wanted) {
  if (alpha_compare(concl(fact), wanted) == 0) return fact;
  if (!is_conj(concl(fact))) return empty_theorem;
  thm left = cm_jump_valid_pick(conjunct1_rule(fact), wanted);
  if (!IS_NULL(left)) return left;
  return cm_jump_valid_pick(conjunct2_rule(fact), wanted);
}

PROOF static thm cm_prove_model_jump_valid(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (pc:int) (op:tvm_opcode) (imm:int)
         (rest:(tvm_inst)list).
         cm_wf_program p ==>
         cm_code_at (cm_model_code p) pc
           (TVMInst op imm :: rest) ==>
         tvm_opcode_is_target op ==>
         tvm_target_valid (cm_model_code p) imm`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm code_at = assume_rule(
      `cm_code_at (cm_model_code (p:cm_program)) (pc:int)
        (TVMInst (op:tvm_opcode) (imm:int) :: (rest:(tvm_inst)list))`);
  thm head = match_mp_rule(get_cm_code_at_head(), code_at);
  thm wf_open = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_wf_program_def(), get_cm_codegen_admissible_def(),
      get_cm_codegen_fields_representable_def())), assume_rule(
        `cm_wf_program (p:cm_program)`));
  thm targets = cm_jump_valid_pick(wf_open,
      `tvm_targets_valid (cm_model_code (p:cm_program))`);
  targets = conv_rule(rewrite_conv(THM_LIST(
      get_tvm_targets_valid_def())), targets);
  thm at_pc = spec_rule(`pc:int`, targets);
  at_pc = match_mp_rule(at_pc, conjunct1_rule(head));
  at_pc = match_mp_rule(at_pc, conjunct1_rule(conjunct2_rule(head)));
  thm instruction = conjunct2_rule(conjunct2_rule(head));
  thm target_opcode = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        instruction, get_tvm_inst_op_def(),
        assume_rule(`tvm_opcode_is_target (op:tvm_opcode)`))),
      `tvm_opcode_is_target
        (tvm_inst_op
          (inth (pc:int) (cm_model_code (p:cm_program))))`));
  at_pc = match_mp_rule(at_pc, target_opcode);
  thm normalized = conv_rule(reduce_rewrite_conv(THM_LIST(
      instruction, get_tvm_inst_imm_def())), at_pc);
  ACCEPT_TAC(leaf, normalized);
  return gnode_prove(root);
}
PROOF thm cm_model_jump_valid = cm_prove_model_jump_valid();

PROOF thm get_cm_model_jump_valid(void) {
  return cm_model_jump_valid;
}

PROOF static int cmc_preservation_target_jump_valid_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_target_jump_valid_axioms_before,
      "cmc_preservation_target_jump_valid introduced an axiom");
  ENSURE_COND(vector_size(hyp(cm_model_jump_valid)) == 0,
      "model jump-validity theorem has hypotheses");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_target_jump_valid_checks =
    cmc_preservation_target_jump_valid_final_checks();
