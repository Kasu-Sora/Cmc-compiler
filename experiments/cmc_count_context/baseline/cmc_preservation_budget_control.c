#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "userlib/proof_patterns.h"
#include "cmc_preservation_budget_control.h"
#include "cmc_preservation_budget_defs.h"
#include "cmc_preservation_generation.h"

#require "userlib/proof_patterns.c"
#require "cmc_preservation_budget_defs.c"
#require "cmc_preservation_generation.c"

PROOF static size_t _cmc_preservation_budget_control_axioms_before =
    vector_size(get_all_axioms());

PROOF static term cm_bc_app_arg_from_right(
    term application, size_t offset) {
  for (size_t i = 0; i < offset; ++i) {
    application = dest_comb(application).tm1;
  }
  return dest_comb(application).tm2;
}

PROOF static term cm_bc_constructor_arg(
    term constructor, size_t arity, size_t index) {
  return cm_bc_app_arg_from_right(
      constructor, arity - index - 1);
}

PROOF static void cm_bc_add_fact_rules(thm_list *rules, thm fact) {
  if (is_conj(concl(fact))) {
    cm_bc_add_fact_rules(rules, conjunct1_rule(fact));
    cm_bc_add_fact_rules(rules, conjunct2_rule(fact));
    return;
  }
  vector_add(rules, fact);
}

PROOF static thm cm_bc_normalize(
    const thm_list rules, thm fact) {
  for (size_t pass = 0; pass < 5; ++pass) {
    fact = conv_rule(reduce_rewrite_conv(rules), fact);
  }
  return fact;
}

PROOF static thm_list cm_bc_base_rules(void) {
  return THM_LIST(
      get_cm_step_def(), get_cm_capply_def(),
      get_cm_control_kind_def(),
      cm_annotation_step_def, cm_update_annotation_def, cm_update_c_def,
      cm_ann_done_def, cm_ann_plain_def, cm_ann_replace_def,
      cm_ann_pop_def, cm_ann_leave_call_def,
      cm_ann_pc_def, cm_ann_temp_def, cm_ann_break_def,
      cm_ann_continue_def, cm_ann_cursors_def,
      cm_ann_spills_def, cm_ann_saved_def, cm_ann_calls_def,
      cm_cursor_phase_def, cm_cursor_temp_def,
      cm_cursor_break_def, cm_cursor_continue_def,
      cm_annotation_erases_def, cm_cursor_frames_def,
      cm_phase_frame_def, cm_frame_parent_fid_def,
      get_cm_task_budget_def(), get_cm_cursors_budget_def(),
      get_cm_phase_budget_def(), get_cm_temp_slots_def(),
      get_cm_stemps_def(), get_cm_rtemps_def(),
      get_theorem_by_name("HD"), get_theorem_by_name("TL"),
      get_theorem_by_name("ILENGTH_DEF"),
      get_theorem_by_name("COND_ID"),
      get_theorem_by_name("NOT_CONS_NIL"),
      get_datatype_distinctness("cm_frame"),
      get_datatype_injectivity("cm_frame"));
}

PROOF static void cm_bc_close(
    gnode node, const thm_list structural,
    const thm_list supplied_facts) {
  thm_list normalized_facts = (thm_list)vector_create();
  thm_list rules = (thm_list)vector_copy(structural);
  for (size_t i = 0; i < vector_size(supplied_facts); ++i) {
    thm normalized = cm_bc_normalize(structural, supplied_facts[i]);
    vector_add(&normalized_facts, normalized);
    cm_bc_add_fact_rules(&rules, normalized);
  }
  thm_list branch_rules = (thm_list)vector_copy(structural);
  thm_list normalized_assumptions = (thm_list)vector_create();
  labeled_term_list assumptions = goal_lasmps(node->g);
  for (size_t i = 0; i < vector_size(assumptions); ++i) {
    thm normalized = cm_bc_normalize(
        structural, assume_rule(assumptions[i].tm));
    vector_add(&normalized_assumptions, normalized);
    cm_bc_add_fact_rules(&rules, normalized);
    cm_bc_add_fact_rules(&branch_rules, normalized);
  }
  for (size_t pass = 0; pass < 5 && IS_NULL(node->solved); ++pass) {
    node = CONV_WITH_ASMP_TAC(node, reduce_rewrite_conv, rules);
  }
  if (!IS_NULL(node->solved)) return;
  if (is_conj(goal_ccl(node->g))) {
    gnode_list parts = CONJ_TAC(node);
    cm_bc_close(parts[0], structural, supplied_facts);
    cm_bc_close(parts[1], structural, supplied_facts);
    return;
  }
  thm_list arithmetic = (thm_list)vector_create();
  for (size_t i = 0; i < vector_size(normalized_facts); ++i) {
    vector_add(&arithmetic,
        cm_bc_normalize(branch_rules, normalized_facts[i]));
  }
  for (size_t i = 0;
       i < vector_size(normalized_assumptions); ++i) {
    vector_add(&arithmetic, normalized_assumptions[i]);
  }
  thm joined = list_conj_rule(arithmetic);
  ACCEPT_TAC(node, mp_rule(int_arith_rule(
      mk_imp(concl(joined), goal_ccl(node->g))), joined));
}

PROOF static thm cm_bc_assumption(const char *label, gnode node) {
  labeled_term_list assumptions = goal_lasmps(node->g);
  return assume_rule(assumptions[
      labeled_term_list_index(assumptions, label)].tm);
}

PROOF static void cm_bc_leaf(
    gnode node, thm control_shape,
    const thm_list extra_structural) {
  thm_list structural = cm_bc_base_rules();
  vector_add(&structural, control_shape);
  for (size_t i = 0; i < vector_size(extra_structural); ++i) {
    vector_add(&structural, extra_structural[i]);
  }
  cm_bc_close(node, structural, THM_LIST(
      assume_rule(`cm_task_budget (p:cm_program)
        (CMCTask p (fid:int) (ctl:cm_control) (st:cm_src_state)
          (ks:(cm_frame)list)) (ann:cm_annotation)`)));
}

PROOF static void cm_bc_phase_cases(
    gnode node, thm control_shape, thm cursors_shape,
    thm frames_shape, term head_cursor) {
  term phase = `cm_cursor_phase (${head_cursor:cm_acursor})`;
  gnode_list phase_cases = DISJ_CASES_TAC(node,
      ispec_rule(phase, get_datatype_cases("cm_aphase")),
      "Hbudget_c_phase");
  for (size_t i = 0; i < vector_size(phase_cases); ++i) {
    gnode branch = phase_cases[i];
    while (is_exists(concl(cm_bc_assumption("Hbudget_c_phase", branch)))) {
      branch = ASMP_EXISTS_TAC(branch, "Hbudget_c_phase", NULL);
    }
    thm phase_shape = cm_bc_assumption("Hbudget_c_phase", branch);
    if (i == 15) {
      term concrete_phase = rhs_of(phase_shape);
      term jump = cm_bc_constructor_arg(concrete_phase, 4, 2);
      gnode_list jump_cases = BOOL_CASES_TAC(
          branch, jump, "Hbudget_c_block_jump");
      for (size_t j = 0; j < vector_size(jump_cases); ++j) {
        cm_bc_leaf(jump_cases[j], control_shape,
            THM_LIST(cursors_shape, phase_shape, frames_shape));
      }
    } else {
      cm_bc_leaf(branch, control_shape,
          THM_LIST(cursors_shape, phase_shape, frames_shape));
    }
  }
}

PROOF static void cm_bc_nonexit(
    gnode node, thm control_shape) {
  term cursors = `cm_ann_cursors (ann:cm_annotation)`;
  gnode_list cursor_cases = DISJ_CASES_TAC(node,
      ispec_rule(cursors, get_theorem_by_name("list_CASES")),
      "Hbudget_c_cursors");
  thm nil_shape = cm_bc_assumption(
      "Hbudget_c_cursors", cursor_cases[0]);
  thm frames_nil = cm_bc_normalize(THM_LIST(
      nil_shape, cm_annotation_erases_def,
      cm_cursor_frames_def, cm_ann_cursors_def),
      assume_rule(`cm_annotation_erases
        (CMCTask (p:cm_program) (fid:int) (ctl:cm_control)
          (st:cm_src_state) (ks:(cm_frame)list))
        (ann:cm_annotation)`));
  cm_bc_leaf(cursor_cases[0], control_shape,
      THM_LIST(nil_shape, sym_rule(frames_nil)));

  gnode cons = ASMP_EXISTS_TAC(
      cursor_cases[1], "Hbudget_c_cursors", NULL);
  cons = ASMP_EXISTS_TAC(cons, "Hbudget_c_cursors", NULL);
  thm cursors_shape = cm_bc_assumption("Hbudget_c_cursors", cons);
  term concrete_cursors = rhs_of(cursors_shape);
  term head_cursor = cm_bc_constructor_arg(concrete_cursors, 2, 0);
  thm frames_forward = cm_bc_normalize(THM_LIST(
      cursors_shape, cm_annotation_erases_def,
      cm_cursor_frames_def, cm_ann_cursors_def,
      cm_cursor_phase_def, cm_phase_frame_def),
      assume_rule(`cm_annotation_erases
        (CMCTask (p:cm_program) (fid:int) (ctl:cm_control)
          (st:cm_src_state) (ks:(cm_frame)list))
        (ann:cm_annotation)`));
  cm_bc_phase_cases(cons, control_shape, cursors_shape,
      sym_rule(frames_forward), head_cursor);
}

PROOF static thm cm_prove_task_budget_c_step(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (ctl:cm_control)
          (st:cm_src_state) (ks:(cm_frame)list) (ann:cm_annotation).
         cm_annotation_erases (CMCTask p fid ctl st ks) ann ==>
         cm_task_budget p (CMCTask p fid ctl st ks) ann ==>
         cm_task_budget p
           (cm_step (CMCTask p fid ctl st ks))
           (cm_update_annotation
             (cm_annotation_step (CMCTask p fid ctl st ks) ann))`);
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list control_cases = DISJ_CASES_TAC(introduced,
      ispec_rule(`ctl:cm_control`, get_datatype_cases("cm_control")),
      "Hbudget_c_control");
  for (size_t i = 0; i < vector_size(control_cases); ++i) {
    gnode branch = control_cases[i];
    while (is_exists(concl(cm_bc_assumption(
        "Hbudget_c_control", branch)))) {
      branch = ASMP_EXISTS_TAC(branch, "Hbudget_c_control", NULL);
    }
    thm control_shape = cm_bc_assumption("Hbudget_c_control", branch);
    if (i == 4) {
      cm_bc_leaf(branch, control_shape, THM_LIST());
    } else {
      cm_bc_nonexit(branch, control_shape);
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_task_budget_c_step =
    cm_prove_task_budget_c_step();

PROOF static int cmc_preservation_budget_control_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_budget_control_axioms_before,
      "cmc_preservation_budget_control introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_budget_control_checks =
    cmc_preservation_budget_control_final_checks();
