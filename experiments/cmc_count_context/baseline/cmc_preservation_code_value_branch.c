#include "proof/proof.h"
#include "userlib/proof.h"
#include "cmc_codegen.h"
#include "cmc_preservation_layout.h"
#include "cmc_preservation_code_value_branch.h"

#require "cmc_preservation_code_value_flow.c"

PROOF size_t _cmc_preservation_code_value_branch_axioms_before =
    vector_size(get_all_axioms());

PROOF static term cm_v_if_task_term(void) {
  return `CMVTask (p:cm_program) (fid:int) (v:cm_value)
      (st:cm_src_state)
      (CMIfK (yes:cm_stmt) (no:cm_stmt) ::
       cm_cursor_frames (rest:(cm_acursor)list))`;
}

PROOF static term cm_v_if_annotation_term(void) {
  return `CMAnnotation (pc:int) (temp:int) (breakpc:int)
      (continuepc:int)
      (CMACursor (CAIfP (yes:cm_stmt) (no:cm_stmt))
        (owner:int) (saved_break:int) (saved_continue:int) ::
       (rest:(cm_acursor)list))
      (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
      (calls:(cm_call_sim_frame)list)`;
}

PROOF static thm cm_prove_v_if_false_layout_step(void) {
  term task = cm_v_if_task_term();
  term annotation = cm_v_if_annotation_term();
  term aligned = `(temp:int) == (owner:int)`;
  term false_guard = `~(cm_truth (st:cm_src_state) (v:cm_value))`;
  term old_layout =
      `cm_task_layout (p:cm_program) ${task:cm_task}
        ${annotation:cm_annotation}`;
  term target =
      `cm_task_layout (p:cm_program) (cm_step ${task:cm_task})
        (cm_update_annotation
          (cm_annotation_step ${task:cm_task}
            ${annotation:cm_annotation}))`;
  term body = imp_chain(
      TERM_LIST(aligned, false_guard, old_layout), target);
  term prefix =
      `[TVMInst TVMJzOp
          ((pc:int) + 1i +
           cm_stmt_code_count (p:cm_program) (fid:int)
             (yes:cm_stmt) + 1i)] ++
       cm_emit_stmt (p:cm_program) (fid:int) ((pc:int) + 1i)
         (owner:int) (saved_break:int) (saved_continue:int)
         (yes:cm_stmt) ++
       [TVMInst TVMJmpOp
          ((pc:int) + 2i +
           cm_stmt_code_count p fid yes +
           cm_stmt_code_count p fid (no:cm_stmt))]`;
  return cm_prove_v_linear_layout_step(
      list_mk_forall(free_vars(body), body), task, annotation,
      prefix, TERM_LIST(aligned, false_guard),
      THM_LIST(get_cm_stmt_code_length(),
        int_ring_rule(
          `(a:int) + 1i + (b:int) + 1i == a + 2i + b`),
        int_ring_rule(
          `(a:int) + 1i + (b:int) + 1i + (c:int) ==
           a + 2i + b + c`)));
}
PROOF thm cm_v_if_false_layout_step =
    cm_prove_v_if_false_layout_step();

PROOF static thm cm_prove_v_if_true_layout_step(void) {
  term task = cm_v_if_task_term();
  term annotation = cm_v_if_annotation_term();
  term aligned = `(temp:int) == (owner:int)`;
  term true_guard = `cm_truth (st:cm_src_state) (v:cm_value)`;
  term old_layout =
      `cm_task_layout (p:cm_program) ${task:cm_task}
        ${annotation:cm_annotation}`;
  term target =
      `cm_task_layout (p:cm_program) (cm_step ${task:cm_task})
        (cm_update_annotation
          (cm_annotation_step ${task:cm_task}
            ${annotation:cm_annotation}))`;
  term body = imp_chain(
      TERM_LIST(aligned, true_guard, old_layout), target);
  gnode root = gnode_new_with_ccl(
      list_mk_forall(free_vars(body), body));
  gnode leaf = AUTO_INTROS_TAC(root);
  thm_list rules = THM_LIST(
      assume_rule(aligned), assume_rule(true_guard));
  thm_list base = cm_v_layout_rules();
  for (size_t i = 0; i < vector_size(base); ++i) {
    vector_add(&rules, base[i]);
  }
  vector_add(&rules, get_cm_stmt_code_length());
  vector_add(&rules, int_ring_rule(
      `(a:int) + 1i + (b:int) + 1i == a + 2i + b`));
  vector_add(&rules, int_ring_rule(
      `(a:int) + 2i + (b:int) + (c:int) ==
       a + 2i + b + c`));
  vector_add(&rules, int_ring_rule(
      `(a:int) + 1i + (b:int) + 1i + (c:int) ==
       a + 2i + b + c`));

  thm opened = conv_rule(reduce_rewrite_conv(rules),
      assume_rule(old_layout));
  opened = conv_rule(reduce_rewrite_conv(rules), opened);
  thm old_code = conjunct1_rule(opened);
  thm old_sites = conjunct2_rule(opened);

  term branch_code =
      `cm_emit_stmt (p:cm_program) (fid:int) ((pc:int) + 1i)
         (owner:int) (saved_break:int) (saved_continue:int)
         (yes:cm_stmt) ++
       [TVMInst TVMJmpOp
          ((pc:int) + 2i +
           cm_stmt_code_count p fid yes +
           cm_stmt_code_count p fid (no:cm_stmt))]`;
  term skipped_code =
      `cm_emit_stmt (p:cm_program) (fid:int)
         ((pc:int) + 2i +
          cm_stmt_code_count p fid (yes:cm_stmt))
         (owner:int) (saved_break:int) (saved_continue:int)
         (no:cm_stmt)`;
  term outer_code =
      `cm_normal_cont_code (p:cm_program) (fid:int)
         ((pc:int) + 2i +
          cm_stmt_code_count p fid (yes:cm_stmt) +
          cm_stmt_code_count p fid (no:cm_stmt))
         (owner:int) (rest:(cm_acursor)list)`;
  term branch_prefix =
      `[TVMInst TVMJzOp
          ((pc:int) + 1i +
           cm_stmt_code_count (p:cm_program) (fid:int)
             (yes:cm_stmt) + 1i)]`;
  thm crop_rule = ispecl_rule(TERM_LIST(
      `cm_model_code (p:cm_program)`, `pc:int`,
      `(${branch_prefix:(tvm_inst)list} ++
        ${branch_code:(tvm_inst)list})`,
      `(${skipped_code:(tvm_inst)list} ++
        ${outer_code:(tvm_inst)list})`),
      cm_code_at_append_left);
  thm cropped = mp_rule(
      conv_rule(reduce_rewrite_conv(rules), crop_rule), old_code);
  thm branch_rule = ispecl_rule(TERM_LIST(
      `cm_model_code (p:cm_program)`, `pc:int`,
      branch_prefix, branch_code), cm_code_at_append_right);
  thm branch_at = mp_rule(
      conv_rule(reduce_rewrite_conv(rules), branch_rule), cropped);

  thm target_rule = ispecl_rule(TERM_LIST(
      `cm_model_code (p:cm_program)`, `pc:int`,
      `(${branch_prefix:(tvm_inst)list} ++
        ${branch_code:(tvm_inst)list} ++
        ${skipped_code:(tvm_inst)list})`,
      outer_code), cm_code_at_append_right);
  thm target_at = mp_rule(
      conv_rule(reduce_rewrite_conv(rules), target_rule), old_code);

  thm result = conj_rule(branch_at,
      conj_rule(target_at, old_sites));
  result = conv_rule(reduce_rewrite_conv(rules), result);
  result = conv_rule(reduce_rewrite_conv(rules), result);
  gnode reduced = CONV_TAC(leaf, reduce_rewrite_conv(rules));
  reduced = CONV_TAC(reduced, reduce_rewrite_conv(rules));
  ACCEPT_TAC(reduced, result);
  return gnode_prove(root);
}
PROOF thm cm_v_if_true_layout_step =
    cm_prove_v_if_true_layout_step();

PROOF static thm cm_prove_v_if_layout_step(void) {
  term task = cm_v_if_task_term();
  term annotation = cm_v_if_annotation_term();
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
  gnode_list cases = BOOL_CASES_TAC(
      leaf, `cm_truth (st:cm_src_state) (v:cm_value)`, "Htruth");
  cm_accept_v_flow_branch(cases[0], cm_v_if_true_layout_step,
      TERM_LIST(aligned,
        `cm_truth (st:cm_src_state) (v:cm_value)`), old_layout);
  cm_accept_v_flow_branch(cases[1], cm_v_if_false_layout_step,
      TERM_LIST(aligned,
        `~(cm_truth (st:cm_src_state) (v:cm_value))`), old_layout);
  return gnode_prove(root);
}
PROOF thm cm_v_if_layout_step =
    cm_prove_v_if_layout_step();

PROOF static term cm_v_while_task_term(void) {
  return `CMVTask (p:cm_program) (fid:int) (v:cm_value)
      (st:cm_src_state)
      (CMWhileGuardK (guard:cm_expr) (body:cm_stmt) ::
       cm_cursor_frames (rest:(cm_acursor)list))`;
}

PROOF static term cm_v_while_annotation_term(void) {
  return `CMAnnotation (pc:int) (temp:int) (breakpc:int)
      (continuepc:int)
      (CMACursor
        (CAWhileGuardP (guard:cm_expr) (body:cm_stmt)
          (loop_start:int) (loop_end:int))
        (owner:int) (saved_break:int) (saved_continue:int) ::
       (rest:(cm_acursor)list))
      (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
      (calls:(cm_call_sim_frame)list)`;
}

PROOF static thm cm_prove_v_while_true_layout_step(void) {
  term task = cm_v_while_task_term();
  term annotation = cm_v_while_annotation_term();
  term aligned = `(temp:int) == (owner:int)`;
  term true_guard = `cm_truth (st:cm_src_state) (v:cm_value)`;
  term old_layout =
      `cm_task_layout (p:cm_program) ${task:cm_task}
        ${annotation:cm_annotation}`;
  term target =
      `cm_task_layout (p:cm_program) (cm_step ${task:cm_task})
        (cm_update_annotation
          (cm_annotation_step ${task:cm_task}
            ${annotation:cm_annotation}))`;
  term body = imp_chain(
      TERM_LIST(aligned, true_guard, old_layout), target);
  return cm_prove_v_linear_layout_step(
      list_mk_forall(free_vars(body), body), task, annotation,
      `[TVMInst TVMJzOp (loop_end:int)]:(tvm_inst)list`,
      TERM_LIST(aligned, true_guard),
      THM_LIST(get_cm_stmt_code_length()));
}
PROOF thm cm_v_while_true_layout_step =
    cm_prove_v_while_true_layout_step();

PROOF static thm cm_prove_v_while_false_layout_step(void) {
  term task = cm_v_while_task_term();
  term annotation = cm_v_while_annotation_term();
  term aligned = `(temp:int) == (owner:int)`;
  term false_guard = `~(cm_truth (st:cm_src_state) (v:cm_value))`;
  term old_layout =
      `cm_task_layout (p:cm_program) ${task:cm_task}
        ${annotation:cm_annotation}`;
  term target =
      `cm_task_layout (p:cm_program) (cm_step ${task:cm_task})
        (cm_update_annotation
          (cm_annotation_step ${task:cm_task}
            ${annotation:cm_annotation}))`;
  term body = imp_chain(
      TERM_LIST(aligned, false_guard, old_layout), target);
  gnode root = gnode_new_with_ccl(
      list_mk_forall(free_vars(body), body));
  gnode leaf = AUTO_INTROS_TAC(root);
  thm_list rules = THM_LIST(
      assume_rule(aligned), assume_rule(false_guard));
  thm_list base = cm_v_layout_rules();
  for (size_t i = 0; i < vector_size(base); ++i) {
    vector_add(&rules, base[i]);
  }
  thm opened = conv_rule(reduce_rewrite_conv(rules),
      assume_rule(old_layout));
  opened = conv_rule(reduce_rewrite_conv(rules), opened);
  thm old_sites = conjunct2_rule(opened);
  thm loop_end_at =
      conjunct2_rule(conjunct1_rule(old_sites));
  thm saved_tail = conjunct2_rule(old_sites);
  thm result = conj_rule(loop_end_at, saved_tail);
  result = conv_rule(reduce_rewrite_conv(rules), result);
  result = conv_rule(reduce_rewrite_conv(rules), result);
  gnode reduced = CONV_TAC(leaf, reduce_rewrite_conv(rules));
  reduced = CONV_TAC(reduced, reduce_rewrite_conv(rules));
  ACCEPT_TAC(reduced, result);
  return gnode_prove(root);
}
PROOF thm cm_v_while_false_layout_step =
    cm_prove_v_while_false_layout_step();

PROOF static thm cm_prove_v_while_layout_step(void) {
  term task = cm_v_while_task_term();
  term annotation = cm_v_while_annotation_term();
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
  gnode_list cases = BOOL_CASES_TAC(
      leaf, `cm_truth (st:cm_src_state) (v:cm_value)`, "Htruth");
  cm_accept_v_flow_branch(cases[0], cm_v_while_true_layout_step,
      TERM_LIST(aligned,
        `cm_truth (st:cm_src_state) (v:cm_value)`), old_layout);
  cm_accept_v_flow_branch(cases[1], cm_v_while_false_layout_step,
      TERM_LIST(aligned,
        `~(cm_truth (st:cm_src_state) (v:cm_value))`), old_layout);
  return gnode_prove(root);
}
PROOF thm cm_v_while_layout_step =
    cm_prove_v_while_layout_step();

PROOF static int cmc_preservation_code_value_branch_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_code_value_branch_axioms_before,
      "cmc_preservation_code_value_branch introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_code_value_branch_checks =
    cmc_preservation_code_value_branch_final_checks();
