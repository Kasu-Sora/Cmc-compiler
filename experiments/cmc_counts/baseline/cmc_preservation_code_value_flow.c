#include "proof/proof.h"
#include "userlib/proof.h"
#include "cmc_preservation_code_expr.h"
#include "cmc_preservation_code_value_flow.h"

#require "cmc_preservation_code_value_linear.c"

PROOF size_t _cmc_preservation_code_value_flow_axioms_before =
    vector_size(get_all_axioms());

PROOF static term cm_v_bin_l_task_term(void) {
  return `CMVTask (p:cm_program) (fid:int) (v:cm_value)
      (st:cm_src_state)
      (CMBinLK (op:int) (right:cm_expr) (ty:cm_type) ::
       cm_cursor_frames (rest:(cm_acursor)list))`;
}

PROOF static term cm_v_bin_l_annotation_term(void) {
  return `CMAnnotation (pc:int) (temp:int) (breakpc:int)
      (continuepc:int)
      (CMACursor
        (CABinLP (op:int) (left:cm_expr) (right:cm_expr)
          (ty:cm_type))
        (owner:int) (saved_break:int) (saved_continue:int) ::
       (rest:(cm_acursor)list))
      (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
      (calls:(cm_call_sim_frame)list)`;
}

PROOF static thm cm_prove_v_bin_l_branch(
    const term_list conditions, const term prefix,
    const thm_list extra_rules) {
  term task = cm_v_bin_l_task_term();
  term annotation = cm_v_bin_l_annotation_term();
  term old_layout =
      `cm_task_layout (p:cm_program) ${task:cm_task}
        ${annotation:cm_annotation}`;
  term target =
      `cm_task_layout (p:cm_program) (cm_step ${task:cm_task})
        (cm_update_annotation
          (cm_annotation_step ${task:cm_task}
            ${annotation:cm_annotation}))`;
  term_list antecedents = vector_copy(conditions);
  vector_add(&antecedents, old_layout);
  term body = imp_chain(antecedents, target);
  term statement = list_mk_forall(free_vars(body), body);
  return cm_prove_v_linear_layout_step(
      statement, task, annotation, prefix, conditions, extra_rules);
}

PROOF thm cm_v_bin_l_short_zero_layout_step =
    cm_prove_v_bin_l_branch(
      TERM_LIST(`(temp:int) == (owner:int)`, `(op:int) == 0i`,
        `cm_truth (st:cm_src_state) (v:cm_value)`),
      `cm_value_phase_code (p:cm_program) (fid:int) (pc:int)
         (temp:int) (owner:int) (saved_break:int) (saved_continue:int)
         (CABinLP (op:int) (left:cm_expr) (right:cm_expr)
           (ty:cm_type))`,
      THM_LIST(get_cm_layout_binary_phase_length(),
        int_ring_rule(
          `(a:int) + (b:int) + 5i == a + 1i + b + 4i`)));

PROOF thm cm_v_bin_l_eval_zero_layout_step =
    cm_prove_v_bin_l_branch(
      TERM_LIST(`(temp:int) == (owner:int)`, `(op:int) == 0i`,
        `~(cm_truth (st:cm_src_state) (v:cm_value))`),
      `[TVMInst TVMJnzOp
          ((pc:int) +
           cm_rvalue_code_count (p:cm_program) (fid:int)
             (right:cm_expr) + 4i)]:(tvm_inst)list`,
      THM_LIST(int_ring_rule(
        `(a:int) + (b:int) + 5i == a + 1i + b + 4i`)));

PROOF thm cm_v_bin_l_eval_one_layout_step =
    cm_prove_v_bin_l_branch(
      TERM_LIST(`(temp:int) == (owner:int)`, `(op:int) == 1i`,
        `cm_truth (st:cm_src_state) (v:cm_value)`),
      `[TVMInst TVMJzOp
          ((pc:int) +
           cm_rvalue_code_count (p:cm_program) (fid:int)
             (right:cm_expr) + 4i)]:(tvm_inst)list`,
      THM_LIST(int_ring_rule(
        `(a:int) + (b:int) + 5i == a + 1i + b + 4i`)));

PROOF thm cm_v_bin_l_short_one_layout_step =
    cm_prove_v_bin_l_branch(
      TERM_LIST(`(temp:int) == (owner:int)`, `(op:int) == 1i`,
        `~(cm_truth (st:cm_src_state) (v:cm_value))`),
      `cm_value_phase_code (p:cm_program) (fid:int) (pc:int)
         (temp:int) (owner:int) (saved_break:int) (saved_continue:int)
         (CABinLP (op:int) (left:cm_expr) (right:cm_expr)
           (ty:cm_type))`,
      THM_LIST(get_cm_layout_binary_phase_length(),
        int_ring_rule(
          `(a:int) + (b:int) + 5i == a + 1i + b + 4i`)));

PROOF thm cm_v_bin_l_other_layout_step =
    cm_prove_v_bin_l_branch(
      TERM_LIST(`(temp:int) == (owner:int)`, `~((op:int) == 0i)`,
        `~((op:int) == 1i)`),
      `cm_temp_store_code (p:cm_program) (fid:int) (owner:int)`,
      THM_LIST());

PROOF void cm_accept_v_flow_branch(
    const gnode branch, thm rule, const term_list conditions,
    const term old_layout) {
  for (size_t i = 0; i < vector_size(conditions); ++i) {
    rule = match_mp_rule(rule, assume_rule(conditions[i]));
  }
  rule = match_mp_rule(rule, assume_rule(old_layout));
  ACCEPT_TAC(branch, rule);
}

PROOF static thm cm_prove_v_bin_l_layout_step(void) {
  term task = cm_v_bin_l_task_term();
  term annotation = cm_v_bin_l_annotation_term();
  term aligned = `(temp:int) == (owner:int)`;
  term old_layout =
      `cm_task_layout (p:cm_program) ${task:cm_task}
        ${annotation:cm_annotation}`;
  term target =
      `cm_task_layout (p:cm_program) (cm_step ${task:cm_task})
        (cm_update_annotation
          (cm_annotation_step ${task:cm_task}
            ${annotation:cm_annotation}))`;
  term body = imp_chain(TERM_LIST(aligned, old_layout), target);
  gnode root = gnode_new_with_ccl(
      list_mk_forall(free_vars(body), body));
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list zero = BOOL_CASES_TAC(
      leaf, `(op:int) == 0i`, "Hopzero");
  gnode_list zero_truth = BOOL_CASES_TAC(
      zero[0], `cm_truth (st:cm_src_state) (v:cm_value)`, "Htruth");
  cm_accept_v_flow_branch(zero_truth[0],
      cm_v_bin_l_short_zero_layout_step,
      TERM_LIST(aligned, `(op:int) == 0i`,
        `cm_truth (st:cm_src_state) (v:cm_value)`), old_layout);
  cm_accept_v_flow_branch(zero_truth[1],
      cm_v_bin_l_eval_zero_layout_step,
      TERM_LIST(aligned, `(op:int) == 0i`,
        `~(cm_truth (st:cm_src_state) (v:cm_value))`), old_layout);

  gnode_list one = BOOL_CASES_TAC(
      zero[1], `(op:int) == 1i`, "Hopone");
  gnode_list one_truth = BOOL_CASES_TAC(
      one[0], `cm_truth (st:cm_src_state) (v:cm_value)`, "Htruth");
  cm_accept_v_flow_branch(one_truth[0],
      cm_v_bin_l_eval_one_layout_step,
      TERM_LIST(aligned, `(op:int) == 1i`,
        `cm_truth (st:cm_src_state) (v:cm_value)`), old_layout);
  cm_accept_v_flow_branch(one_truth[1],
      cm_v_bin_l_short_one_layout_step,
      TERM_LIST(aligned, `(op:int) == 1i`,
        `~(cm_truth (st:cm_src_state) (v:cm_value))`), old_layout);
  cm_accept_v_flow_branch(one[1],
      cm_v_bin_l_other_layout_step,
      TERM_LIST(aligned, `~((op:int) == 0i)`,
        `~((op:int) == 1i)`), old_layout);
  return gnode_prove(root);
}
PROOF thm cm_v_bin_l_layout_step =
    cm_prove_v_bin_l_layout_step();

PROOF static term cm_v_bin_r_task_term(void) {
  return `CMVTask (p:cm_program) (fid:int) (v:cm_value)
      (st:cm_src_state)
      (CMBinRK (op:int) (left_value:cm_value) (ty:cm_type) ::
       cm_cursor_frames (rest:(cm_acursor)list))`;
}

PROOF static term cm_v_bin_r_annotation_term(void) {
  return `CMAnnotation (pc:int) (temp:int) (breakpc:int)
      (continuepc:int)
      (CMACursor
        (CABinRP (op:int) (left:cm_expr) (right:cm_expr)
          (left_value:cm_value) (ty:cm_type))
        (owner:int) (saved_break:int) (saved_continue:int) ::
       (rest:(cm_acursor)list))
      (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
      (calls:(cm_call_sim_frame)list)`;
}

PROOF static thm cm_prove_v_bin_r_branch(
    const term_list conditions, const term prefix) {
  term task = cm_v_bin_r_task_term();
  term annotation = cm_v_bin_r_annotation_term();
  term old_layout =
      `cm_task_layout (p:cm_program) ${task:cm_task}
        ${annotation:cm_annotation}`;
  term target =
      `cm_task_layout (p:cm_program) (cm_step ${task:cm_task})
        (cm_update_annotation
          (cm_annotation_step ${task:cm_task}
            ${annotation:cm_annotation}))`;
  term_list antecedents = vector_copy(conditions);
  vector_add(&antecedents, old_layout);
  term body = imp_chain(antecedents, target);
  return cm_prove_v_linear_layout_step(
      list_mk_forall(free_vars(body), body), task, annotation,
      prefix, conditions, THM_LIST());
}

PROOF thm cm_v_bin_r_zero_layout_step =
    cm_prove_v_bin_r_branch(
      TERM_LIST(`(op:int) == 0i`,
        `cm_binary_ok (p:cm_program) 0i
          (left_value:cm_value) (v:cm_value) (st:cm_src_state)`),
      `[TVMInst TVMPushOp 0i; TVMInst TVMNeOp 0i;
        TVMInst TVMJmpOp ((pc:int) + 4i);
        TVMInst TVMPushOp 1i]:(tvm_inst)list`);

PROOF thm cm_v_bin_r_one_layout_step =
    cm_prove_v_bin_r_branch(
      TERM_LIST(`(op:int) == 1i`,
        `cm_binary_ok (p:cm_program) 1i
          (left_value:cm_value) (v:cm_value) (st:cm_src_state)`),
      `[TVMInst TVMPushOp 0i; TVMInst TVMNeOp 0i;
        TVMInst TVMJmpOp ((pc:int) + 4i);
        TVMInst TVMPushOp 0i]:(tvm_inst)list`);

PROOF thm cm_v_bin_r_other_layout_step =
    cm_prove_v_bin_r_branch(
      TERM_LIST(`~((op:int) == 0i)`, `~((op:int) == 1i)`,
        `cm_binary_ok (p:cm_program) (op:int)
          (left_value:cm_value) (v:cm_value) (st:cm_src_state)`),
      `cm_binary_finish_code (p:cm_program) (fid:int) (op:int)
         (left:cm_expr) (right:cm_expr) (owner:int)`);

PROOF static void cm_accept_v_bin_r_equal_branch(
    const gnode branch, thm rule, const term op_equal,
    const term ready, const term old_layout) {
  thm op_fact = assume_rule(op_equal);
  thm literal_ready = conv_rule(
      rewrite_conv(THM_LIST(op_fact)), assume_rule(ready));
  rule = match_mp_rule(rule, op_fact);
  rule = match_mp_rule(rule, literal_ready);
  rule = match_mp_rule(rule, assume_rule(old_layout));
  ACCEPT_TAC(branch, rule);
}

PROOF static thm cm_prove_v_bin_r_layout_step(void) {
  term task = cm_v_bin_r_task_term();
  term annotation = cm_v_bin_r_annotation_term();
  term ready =
      `cm_binary_ok (p:cm_program) (op:int)
        (left_value:cm_value) (v:cm_value) (st:cm_src_state)`;
  term old_layout =
      `cm_task_layout (p:cm_program) ${task:cm_task}
        ${annotation:cm_annotation}`;
  term target =
      `cm_task_layout (p:cm_program) (cm_step ${task:cm_task})
        (cm_update_annotation
          (cm_annotation_step ${task:cm_task}
            ${annotation:cm_annotation}))`;
  term body = imp_chain(TERM_LIST(ready, old_layout), target);
  gnode root = gnode_new_with_ccl(
      list_mk_forall(free_vars(body), body));
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list zero = BOOL_CASES_TAC(
      leaf, `(op:int) == 0i`, "Hopzero");
  cm_accept_v_bin_r_equal_branch(
      zero[0], cm_v_bin_r_zero_layout_step,
      `(op:int) == 0i`, ready, old_layout);
  gnode_list one = BOOL_CASES_TAC(
      zero[1], `(op:int) == 1i`, "Hopone");
  cm_accept_v_bin_r_equal_branch(
      one[0], cm_v_bin_r_one_layout_step,
      `(op:int) == 1i`, ready, old_layout);
  cm_accept_v_flow_branch(one[1], cm_v_bin_r_other_layout_step,
      TERM_LIST(`~((op:int) == 0i)`, `~((op:int) == 1i)`, ready),
      old_layout);
  return gnode_prove(root);
}
PROOF thm cm_v_bin_r_layout_step =
    cm_prove_v_bin_r_layout_step();

PROOF static int cmc_preservation_code_value_flow_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_code_value_flow_axioms_before,
      "cmc_preservation_code_value_flow introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_code_value_flow_checks =
    cmc_preservation_code_value_flow_final_checks();
