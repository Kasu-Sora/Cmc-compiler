#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_layout.h"
#require "cmc_preservation_layout.c"
#include "cmc_preservation_tvm.h"

PROOF static size_t _cmc_preservation_tvm_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_prove_tvm_code_step(void) {
  gnode root = gnode_new_with_ccl(
      `!(obj:tvm_object) (st:tvm_state) (op:tvm_opcode)
         (imm:int) (rest:(tvm_inst)list).
         cm_code_at (tvm_object_code obj) (tvm_pc st)
           (TVMInst op imm :: rest) ==>
         tvm_step (TVMRunTask obj st) ==
           tvm_action_task obj
             (tvm_inst_step (tvm_object_code obj) op imm st)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm at = assume_rule(
      `cm_code_at (tvm_object_code (obj:tvm_object))
         (tvm_pc (st:tvm_state))
         (TVMInst (op:tvm_opcode) (imm:int) ::
           (rest:(tvm_inst)list))`);
  thm head = mp_rule(ispecl_rule(TERM_LIST(
      `tvm_object_code (obj:tvm_object)`,
      `tvm_pc (st:tvm_state)`,
      `TVMInst (op:tvm_opcode) (imm:int)`,
      `rest:(tvm_inst)list`), get_cm_code_at_head()), at);
  thm valid = eq_mp_rule(sym_rule(apply_conversion(
      rewrite_conv(THM_LIST(get_tvm_target_valid_def())),
      `tvm_target_valid (tvm_object_code (obj:tvm_object))
         (tvm_pc (st:tvm_state))`)),
      conj_rule(conjunct1_rule(head),
        conjunct1_rule(conjunct2_rule(head))));
  thm instruction = conjunct2_rule(conjunct2_rule(head));
  CONV_WITH_ASMP_TAC(leaf, reduce_rewrite_conv, THM_LIST(
      get_tvm_step_def(), get_tvm_inst_op_def(),
      get_tvm_inst_imm_def(), valid, instruction));
  return gnode_prove(root);
}
PROOF thm cm_tvm_code_step = cm_prove_tvm_code_step();

PROOF static thm cm_prove_tvm_iter_add(void) {
  gnode root = gnode_new_with_ccl(
      `!(m:num) (n:num) (task:tvm_task).
         tvm_iter (m + n) task ==
         tvm_iter n (tvm_iter m task)`);
  gnode_list cases = INDUCT_TAC(root, `m:num`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        get_tvm_iter_def(), get_theorem_by_name("ADD_CLAUSES"))));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm ih = specl_rule(TERM_LIST(
        `n:num`, `tvm_step (task:tvm_task)`),
        assume_rule(goal_lasmps(leaf->g)[0].tm));
    CONV_WITH_ASMP_TAC(leaf, reduce_rewrite_conv, THM_LIST(
        get_tvm_iter_def(), get_theorem_by_name("ADD_CLAUSES"), ih));
  }
  return gnode_prove(root);
}
PROOF thm cm_tvm_iter_add = cm_prove_tvm_iter_add();

PROOF static thm cm_prove_tvm_state_step(void) {
  gnode root = gnode_new_with_ccl(
      `!(obj:tvm_object) (st:tvm_state) (op:tvm_opcode)
         (imm:int) (rest:(tvm_inst)list) (next:tvm_state).
         cm_code_at (tvm_object_code obj) (tvm_pc st)
           (TVMInst op imm :: rest) ==>
         tvm_inst_step (tvm_object_code obj) op imm st ==
           TVMStepState next ==>
         tvm_step (TVMRunTask obj st) == TVMRunTask obj next`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm at = assume_rule(
      `cm_code_at (tvm_object_code (obj:tvm_object))
         (tvm_pc (st:tvm_state))
         (TVMInst (op:tvm_opcode) (imm:int) ::
           (rest:(tvm_inst)list))`);
  thm step = mp_rule(specl_rule(TERM_LIST(
      `obj:tvm_object`, `st:tvm_state`, `op:tvm_opcode`,
      `imm:int`, `rest:(tvm_inst)list`), cm_tvm_code_step), at);
  ACCEPT_TAC(leaf, conv_rule(rewrite_conv(THM_LIST(
      assume_rule(
        `tvm_inst_step (tvm_object_code (obj:tvm_object))
           (op:tvm_opcode) (imm:int) (st:tvm_state) ==
         TVMStepState (next:tvm_state)`),
      get_tvm_action_task_def())), step));
  return gnode_prove(root);
}
PROOF thm cm_tvm_state_step = cm_prove_tvm_state_step();

PROOF static thm cm_prove_tvm_halt_step(void) {
  gnode root = gnode_new_with_ccl(
      `!(obj:tvm_object) (st:tvm_state) (op:tvm_opcode)
         (imm:int) (rest:(tvm_inst)list) (next:tvm_state)
         (status:int).
         cm_code_at (tvm_object_code obj) (tvm_pc st)
           (TVMInst op imm :: rest) ==>
         tvm_inst_step (tvm_object_code obj) op imm st ==
           TVMStepHalt next status ==>
         tvm_step (TVMRunTask obj st) ==
           TVMDoneTask next status 0i`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm at = assume_rule(
      `cm_code_at (tvm_object_code (obj:tvm_object))
         (tvm_pc (st:tvm_state))
         (TVMInst (op:tvm_opcode) (imm:int) ::
           (rest:(tvm_inst)list))`);
  thm step = mp_rule(specl_rule(TERM_LIST(
      `obj:tvm_object`, `st:tvm_state`, `op:tvm_opcode`,
      `imm:int`, `rest:(tvm_inst)list`), cm_tvm_code_step), at);
  ACCEPT_TAC(leaf, conv_rule(rewrite_conv(THM_LIST(
      assume_rule(
        `tvm_inst_step (tvm_object_code (obj:tvm_object))
           (op:tvm_opcode) (imm:int) (st:tvm_state) ==
         TVMStepHalt (next:tvm_state) (status:int)`),
      get_tvm_action_task_def())), step));
  return gnode_prove(root);
}
PROOF thm cm_tvm_halt_step = cm_prove_tvm_halt_step();

PROOF static thm cm_prove_tvm_state_iter_one(void) {
  gnode root = gnode_new_with_ccl(
      `!(obj:tvm_object) (st:tvm_state) (op:tvm_opcode)
         (imm:int) (rest:(tvm_inst)list) (next:tvm_state).
         cm_code_at (tvm_object_code obj) (tvm_pc st)
           (TVMInst op imm :: rest) ==>
         tvm_inst_step (tvm_object_code obj) op imm st ==
           TVMStepState next ==>
         tvm_iter 1 (TVMRunTask obj st) ==
           TVMRunTask obj next`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm step = match_mp_rule(
      match_mp_rule(specl_rule(TERM_LIST(
        `obj:tvm_object`, `st:tvm_state`, `op:tvm_opcode`,
        `imm:int`, `rest:(tvm_inst)list`, `next:tvm_state`),
        cm_tvm_state_step),
        assume_rule(
          `cm_code_at (tvm_object_code (obj:tvm_object))
             (tvm_pc (st:tvm_state))
             (TVMInst (op:tvm_opcode) (imm:int) ::
               (rest:(tvm_inst)list))`)),
      assume_rule(
        `tvm_inst_step (tvm_object_code (obj:tvm_object))
           (op:tvm_opcode) (imm:int) (st:tvm_state) ==
         TVMStepState (next:tvm_state)`));
  gnode opened = CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
      get_tvm_iter_def(), get_theorem_by_name("ONE"))));
  ACCEPT_TAC(opened, step);
  return gnode_prove(root);
}
PROOF thm cm_tvm_state_iter_one =
    cm_prove_tvm_state_iter_one();

PROOF static thm cm_prove_tvm_halt_iter_one(void) {
  gnode root = gnode_new_with_ccl(
      `!(obj:tvm_object) (st:tvm_state) (op:tvm_opcode)
         (imm:int) (rest:(tvm_inst)list) (next:tvm_state)
         (status:int).
         cm_code_at (tvm_object_code obj) (tvm_pc st)
           (TVMInst op imm :: rest) ==>
         tvm_inst_step (tvm_object_code obj) op imm st ==
           TVMStepHalt next status ==>
         tvm_iter 1 (TVMRunTask obj st) ==
           TVMDoneTask next status 0i`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm step = match_mp_rule(
      match_mp_rule(specl_rule(TERM_LIST(
        `obj:tvm_object`, `st:tvm_state`, `op:tvm_opcode`,
        `imm:int`, `rest:(tvm_inst)list`, `next:tvm_state`,
        `status:int`), cm_tvm_halt_step),
        assume_rule(
          `cm_code_at (tvm_object_code (obj:tvm_object))
             (tvm_pc (st:tvm_state))
             (TVMInst (op:tvm_opcode) (imm:int) ::
               (rest:(tvm_inst)list))`)),
      assume_rule(
        `tvm_inst_step (tvm_object_code (obj:tvm_object))
           (op:tvm_opcode) (imm:int) (st:tvm_state) ==
         TVMStepHalt (next:tvm_state) (status:int)`));
  gnode opened = CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
      get_tvm_iter_def(), get_theorem_by_name("ONE"))));
  ACCEPT_TAC(opened, step);
  return gnode_prove(root);
}
PROOF thm cm_tvm_halt_iter_one =
    cm_prove_tvm_halt_iter_one();

PROOF static thm cm_prove_tvm_iter_compose(void) {
  gnode root = gnode_new_with_ccl(
      `!(m:num) (n:num) (start:tvm_task)
         (middle:tvm_task) (finish:tvm_task).
         tvm_iter m start == middle ==>
         tvm_iter n middle == finish ==>
         tvm_iter (m + n) start == finish`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm split = specl_rule(TERM_LIST(
      `m:num`, `n:num`, `start:tvm_task`), cm_tvm_iter_add);
  ACCEPT_TAC(leaf, conv_rule(rewrite_conv(THM_LIST(
      assume_rule(
        `tvm_iter (m:num) (start:tvm_task) == (middle:tvm_task)`),
      assume_rule(
        `tvm_iter (n:num) (middle:tvm_task) == (finish:tvm_task)`))),
      split));
  return gnode_prove(root);
}
PROOF thm cm_tvm_iter_compose =
    cm_prove_tvm_iter_compose();

PROOF thm get_cm_tvm_code_step(void) { return cm_tvm_code_step; }
PROOF thm get_cm_tvm_iter_add(void) { return cm_tvm_iter_add; }
PROOF thm get_cm_tvm_state_step(void) { return cm_tvm_state_step; }
PROOF thm get_cm_tvm_halt_step(void) { return cm_tvm_halt_step; }

PROOF static int cmc_preservation_tvm_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_tvm_axioms_before,
      "cmc_preservation_tvm introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_tvm_checks =
    cmc_preservation_tvm_final_checks();
