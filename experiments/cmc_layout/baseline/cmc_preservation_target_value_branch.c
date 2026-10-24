#include "proof/proof.h"
#include "userlib/proof.h"
#include "cmc_preservation_target_value_branch.h"
#include "cmc_preservation_code_value_branch.h"
#include "cmc_preservation_target_machine.h"

#require "cmc_preservation_target_value_control.c"
#require "cmc_preservation_code_value_branch.c"

PROOF static size_t _cmc_preservation_target_value_branch_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_prove_target_v_branch_step(const bool while_guard) {
  term frame = while_guard
      ? `CMWhileGuardK (guard:cm_expr) (body:cm_stmt):cm_frame`
      : `CMIfK (yes:cm_stmt) (no:cm_stmt):cm_frame`;
  term phase = while_guard
      ? `CAWhileGuardP (guard:cm_expr) (body:cm_stmt)
          (loop_start:int) (loop_end:int):cm_aphase`
      : `CAIfP (yes:cm_stmt) (no:cm_stmt):cm_aphase`;
  term task =
      `CMVTask (p:cm_program) (fid:int) (v:cm_value)
        (st:cm_src_state)
        (${frame:cm_frame} ::
         cm_cursor_frames (rest:(cm_acursor)list))`;
  term ann =
      `CMAnnotation (pc:int) (temp:int) (breakpc:int) (continuepc:int)
        (CMACursor ${phase:cm_aphase} (owner:int)
          (saved_break:int) (saved_continue:int) ::
         (rest:(cm_acursor)list))
        (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
        (calls:(cm_call_sim_frame)list)`;
  term jump_pc = while_guard
      ? `loop_end:int`
      : `(pc:int) + 1i +
          cm_stmt_code_count (p:cm_program) (fid:int) (yes:cm_stmt) +
          1i`;
  term end_pc = while_guard
      ? `loop_end:int`
      : `(pc:int) + 2i +
          cm_stmt_code_count (p:cm_program) (fid:int) (yes:cm_stmt) +
          cm_stmt_code_count p fid (no:cm_stmt)`;
  term rest_code = while_guard
      ? `cm_emit_stmt (p:cm_program) (fid:int) ((pc:int) + 1i)
           (owner:int) (loop_end:int) (loop_start:int) (body:cm_stmt) ++
         [TVMInst TVMJmpOp (loop_start:int)] ++
         cm_normal_cont_code p fid
           ((pc:int) + 1i + cm_stmt_code_count p fid body + 1i)
           owner (rest:(cm_acursor)list)`
      : `cm_emit_stmt (p:cm_program) (fid:int) ((pc:int) + 1i)
           (owner:int) (saved_break:int) (saved_continue:int)
           (yes:cm_stmt) ++
         [TVMInst TVMJmpOp ${end_pc:int}] ++
         cm_emit_stmt p fid
           ((pc:int) + 2i + cm_stmt_code_count p fid yes)
           owner saved_break saved_continue (no:cm_stmt) ++
         cm_normal_cont_code p fid ${end_pc:int} owner
           (rest:(cm_acursor)list)`;
  term body = imp_chain(TERM_LIST(
      `cm_task_layout (p:cm_program) ${task:cm_task}
        ${ann:cm_annotation}`,
      `cm_task_target_sim (p:cm_program) ${task:cm_task}
        (target:tvm_task) ${ann:cm_annotation}`,
      `tvm_target_valid (cm_model_code (p:cm_program)) ${jump_pc:int}`),
      `cm_task_target_sim (p:cm_program)
        (cm_step ${task:cm_task})
        (tvm_iter
          (cm_update_steps
            (cm_annotation_step ${task:cm_task} ${ann:cm_annotation}))
          (target:tvm_task))
        (cm_update_annotation
          (cm_annotation_step ${task:cm_task} ${ann:cm_annotation}))`);
  gnode root = gnode_new_with_ccl(
      list_mk_forall(free_vars(body), body));
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list cases = BOOL_CASES_TAC(
      leaf, `cm_truth (st:cm_src_state) (v:cm_value)`, "Htruth");
  for (size_t index = 0; index < 2; ++index) {
    bool truth = index == 0;
    gnode branch = cases[index];
    term truth_term = truth
        ? `cm_truth (st:cm_src_state) (v:cm_value)`
        : `~cm_truth (st:cm_src_state) (v:cm_value)`;
    thm truth_fact = assume_rule(truth_term);
    thm branch_end = int_ring_rule(
        `(a:int) + 2i + (b:int) + (c:int) ==
         a + 1i + b + 1i + c`);
    thm branch_else = int_ring_rule(
        `(a:int) + 2i + (b:int) == a + 1i + b + 1i`);
    thm layout = assume_rule(
        `cm_task_layout (p:cm_program) ${task:cm_task}
          ${ann:cm_annotation}`);
    thm_list rules = cm_v_layout_rules();
    vector_add(&rules, truth_fact);
    vector_add(&rules, get_cm_stmt_code_length());
    vector_add(&rules, branch_end);
    vector_add(&rules, get_theorem_by_name("ILENGTH_DEF"));
    vector_add(&rules, get_theorem_by_name("APPEND"));
    vector_add(&rules, branch_else);
    vector_add(&rules, get_theorem_by_name("APPEND_NIL"));
    thm opened = conv_rule(reduce_rewrite_conv(rules), layout);
    opened = conv_rule(reduce_rewrite_conv(rules), opened);
    thm code_at = conjunct1_rule(opened);
    thm running = conv_rule(reduce_rewrite_conv(THM_LIST(
        cm_task_target_sim_def)), assume_rule(
          `cm_task_target_sim (p:cm_program) ${task:cm_task}
            (target:tvm_task) ${ann:cm_annotation}`));
    thm stepped = specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `st:cm_src_state`, `v:cm_value`,
        `[]:(cm_value)list`, ann, `target:tvm_task`, jump_pc,
        rest_code), get_cm_target_jz());
    stepped = conv_rule(reduce_rewrite_conv(rules), stepped);
    code_at = conv_rule(reduce_rewrite_conv(rules), code_at);
    stepped = match_mp_rule(stepped, code_at);
    stepped = match_mp_rule(stepped, assume_rule(
        `tvm_target_valid (cm_model_code (p:cm_program))
          ${jump_pc:int}`));
    stepped = match_mp_rule(stepped, running);

    term branch_ann = truth
        ? `cm_ann_linear [TVMInst TVMJzOp ${jump_pc:int}]
            ${ann:cm_annotation}`
        : `cm_ann_plain ${jump_pc:int} (cm_ann_temp ${ann:cm_annotation})
            (cm_ann_break ${ann:cm_annotation})
            (cm_ann_continue ${ann:cm_annotation})
            ${ann:cm_annotation}`;
    term next_ann =
        `cm_update_annotation
          (cm_annotation_step ${task:cm_task} ${ann:cm_annotation})`;
    thm reannotated = specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `st:cm_src_state`,
        `[]:(cm_value)list`, branch_ann, next_ann,
        `tvm_iter 1 (target:tvm_task)`), get_cm_target_reannotate());
    thm_list ann_rules = cm_v_layout_rules();
    vector_add(&ann_rules, truth_fact);
    vector_add(&ann_rules, get_cm_stmt_code_length());
    vector_add(&ann_rules, cm_ann_linear_def);
    vector_add(&ann_rules, cm_ann_plain_def);
    vector_add(&ann_rules, branch_end);
    vector_add(&ann_rules, branch_else);
    vector_add(&ann_rules, get_theorem_by_name("ILENGTH_DEF"));
    conv ann_normalize = then_conv(
        reduce_rewrite_conv(ann_rules),
        then_conv(reduce_rewrite_conv(ann_rules),
          reduce_rewrite_conv(ann_rules)));
    for (size_t premise = 0; premise < 4; ++premise) {
      reannotated = match_mp_rule(reannotated,
          eqt_elim_rule(apply_conversion(
            ann_normalize, dest_imp(concl(reannotated)).tm1)));
    }
    reannotated = conv_rule(ann_normalize, reannotated);
    stepped = conv_rule(ann_normalize, stepped);
    stepped = match_mp_rule(reannotated, stepped);

    thm_list finish_rules = cm_v_layout_rules();
    vector_add(&finish_rules, truth_fact);
    vector_add(&finish_rules, cm_task_target_sim_def);
    vector_add(&finish_rules, cm_running_target_sim_def);
    vector_add(&finish_rules, cm_active_spill_frames_def);
    vector_add(&finish_rules, cm_code_steps_def);
    vector_add(&finish_rules, cm_update_steps_def);
    vector_add(&finish_rules, get_cm_stmt_code_length());
    vector_add(&finish_rules, branch_end);
    vector_add(&finish_rules, branch_else);
    vector_add(&finish_rules, get_theorem_by_name("ILENGTH_DEF"));
    gnode reduced = CONV_TAC(
        branch, reduce_rewrite_conv(finish_rules));
    reduced = CONV_TAC(reduced, rewrite_conv(THM_LIST(
        spec_rule(`1:num`, get_theorem_by_name("NUM_OF_INT_OF_NUM")))));
    reduced = CONV_TAC(
        reduced, reduce_rewrite_conv(finish_rules));
    thm normalized = conv_rule(
        reduce_rewrite_conv(finish_rules), stepped);
    normalized = conv_rule(
        reduce_rewrite_conv(finish_rules), normalized);
    ACCEPT_TAC(reduced, normalized);
  }
  return gnode_prove(root);
}

PROOF thm cm_target_v_if_step =
    cm_prove_target_v_branch_step(false);
PROOF thm cm_target_v_while_guard_step =
    cm_prove_target_v_branch_step(true);

PROOF thm get_cm_target_v_if_step(void) {
  return cm_target_v_if_step;
}
PROOF thm get_cm_target_v_while_guard_step(void) {
  return cm_target_v_while_guard_step;
}

PROOF static int cmc_preservation_target_value_branch_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_target_value_branch_axioms_before,
      "cmc_preservation_target_value_branch introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_target_value_branch_checks =
    cmc_preservation_target_value_branch_final_checks();
