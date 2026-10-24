#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "userlib/proof_patterns.h"
#include "cmc_preservation_budget_ready.h"
#include "cmc_preservation_budget_defs.h"
#include "cmc_preservation_ready_coordinate.h"
#include "cmc_preservation_invariant_transition.h"
#include "cmc_temp_algebra.h"

#require "userlib/proof_patterns.c"
#require "cmc_preservation_budget_defs.c"
#require "cmc_preservation_ready_coordinate.c"
#require "cmc_preservation_invariant_transition.c"
#require "cmc_temp_algebra.c"

PROOF static size_t _cmc_preservation_budget_ready_axioms_before =
    vector_size(get_all_axioms());

PROOF static term cm_br_app_arg_from_right(
    term application, size_t offset) {
  for (size_t i = 0; i < offset; ++i) {
    application = dest_comb(application).tm1;
  }
  return dest_comb(application).tm2;
}

PROOF static term cm_br_constructor_arg(
    term constructor, size_t arity, size_t index) {
  return cm_br_app_arg_from_right(
      constructor, arity - index - 1);
}

PROOF static thm cm_br_named_shape(
    gnode *node, const char *label) {
  while (true) {
    labeled_term_list assumptions = goal_lasmps((*node)->g);
    int index = labeled_term_list_index(assumptions, label);
    if (!is_exists(assumptions[index].tm)) {
      return assume_rule(assumptions[index].tm);
    }
    *node = ASMP_EXISTS_TAC(*node, label, NULL);
  }
}

PROOF static void cm_br_close(
    gnode node, thm_list structural, thm_list established) {
  thm_list rules = (thm_list)vector_copy(structural);
  thm_list normalizers = (thm_list)vector_copy(structural);
  thm_list facts = (thm_list)vector_copy(established);
  for (size_t i = 0; i < vector_size(established); ++i) {
    vector_add(&rules, established[i]);
    vector_add(&normalizers, established[i]);
  }
  labeled_term_list assumptions = goal_lasmps(node->g);
  for (size_t i = 0; i < vector_size(assumptions); ++i) {
    thm fact = assume_rule(assumptions[i].tm);
    thm normalized = conv_rule(
        reduce_rewrite_conv(normalizers), fact);
    vector_add(&facts, normalized);
    vector_add(&rules, fact);
    vector_add(&rules, normalized);
  }
  for (size_t pass = 0; pass < 6 && IS_NULL(node->solved); ++pass) {
    node = CONV_WITH_ASMP_TAC(node, reduce_rewrite_conv, rules);
  }
  if (!IS_NULL(node->solved)) return;
  if (is_conj(goal_ccl(node->g))) {
    gnode_list parts = CONJ_TAC(node);
    cm_br_close(parts[0], structural, established);
    cm_br_close(parts[1], structural, established);
    return;
  }
  thm joined = list_conj_rule(facts);
  ACCEPT_TAC(node, mp_rule(int_arith_rule(
      mk_imp(concl(joined), goal_ccl(node->g))), joined));
}

PROOF static void cm_br_close_phase(
    gnode node, thm phase_shape, thm_list established) {
  cm_br_close(node, THM_LIST(
      phase_shape, get_cm_phase_budget_def(),
      cm_v_spill_ready_def, cm_phase_child_temp_def,
      get_theorem_by_name("COND_ID")), established);
}

PROOF static thm cm_prove_phase_budget_spill_ready(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (ann:cm_annotation)
         (phase:cm_aphase) (owner:int).
         cm_phase_budget p fid phase owner ==>
         cm_ann_temp ann == cm_phase_child_temp phase owner ==>
         cm_v_spill_ready p fid ann phase`);
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list cases = DISJ_CASES_TAC(introduced,
      ispec_rule(`phase:cm_aphase`, get_datatype_cases("cm_aphase")),
      "Hbudget_phase");
  size_t arities[23] = {
      0, 1, 2, 2, 4, 5, 1, 2, 2, 2, 0, 0,
      0, 0, 1, 4, 1, 2, 4, 6, 0, 8, 5};
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode branch = cases[i];
    thm phase_shape = cm_br_named_shape(&branch, "Hbudget_phase");
    term concrete_phase = rhs_of(phase_shape);
    thm_list established = THM_LIST();
    if (i == 2) {
      term expr = cm_br_constructor_arg(concrete_phase, arities[i], 0);
      vector_add(&established,
          ispec_rule(expr, cm_rtemps_nonnegative));
    } else if (i == 4) {
      term op = cm_br_constructor_arg(concrete_phase, arities[i], 0);
      term right = cm_br_constructor_arg(concrete_phase, arities[i], 2);
      vector_add(&established,
          ispec_rule(right, cm_rtemps_nonnegative));
      gnode_list zero_cases = BOOL_CASES_TAC(
          branch, mk_eq(op, `0i`), "Hbudget_op_zero");
      cm_br_close_phase(zero_cases[0], phase_shape, established);
      gnode_list one_cases = BOOL_CASES_TAC(
          zero_cases[1], mk_eq(op, `1i`), "Hbudget_op_one");
      cm_br_close_phase(one_cases[0], phase_shape, established);
      cm_br_close_phase(one_cases[1], phase_shape, established);
      continue;
    } else if (i == 7) {
      term expr = cm_br_constructor_arg(concrete_phase, arities[i], 0);
      vector_add(&established,
          ispec_rule(expr, cm_rtemps_nonnegative));
    }
    cm_br_close_phase(branch, phase_shape, established);
  }
  return gnode_prove(root);
}
PROOF thm cm_phase_budget_spill_ready =
    cm_prove_phase_budget_spill_ready();

PROOF static thm cm_prove_task_budget_v_spill_ready(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (v:cm_value)
         (st:cm_src_state) (ks:(cm_frame)list)
         (ann:cm_annotation).
         cm_task_coordinate_ready p (CMVTask p fid v st ks) ann ==>
         cm_task_budget p (CMVTask p fid v st ks) ann ==>
         ~(cm_ann_cursors ann == []) ==>
         cm_v_spill_ready p fid ann
           (cm_cursor_phase (HD (cm_ann_cursors ann)))`);
  gnode introduced = AUTO_INTROS_TAC(root);
  thm coordinate = assume_rule(
      `cm_task_coordinate_ready (p:cm_program)
        (CMVTask p (fid:int) (v:cm_value) (st:cm_src_state)
          (ks:(cm_frame)list)) (ann:cm_annotation)`);
  thm budget = assume_rule(
      `cm_task_budget (p:cm_program)
        (CMVTask p (fid:int) (v:cm_value) (st:cm_src_state)
          (ks:(cm_frame)list)) (ann:cm_annotation)`);
  thm nonempty = assume_rule(
      `~(cm_ann_cursors (ann:cm_annotation) == [])`);
  gnode_list ann_cases = DISJ_CASES_TAC(introduced,
      ispec_rule(`ann:cm_annotation`,
        get_datatype_cases("cm_annotation")), "Hbudget_ann");
  gnode branch = ann_cases[0];
  thm ann_shape = cm_br_named_shape(&branch, "Hbudget_ann");
  term shaped_ann = rhs_of(ann_shape);
  term cursors = cm_br_constructor_arg(shaped_ann, 8, 4);
  gnode_list cursor_cases = DISJ_CASES_TAC(branch,
      ispec_rule(cursors, get_theorem_by_name("list_CASES")),
      "Hbudget_cursors");
  {
    thm cursors_nil = cm_br_named_shape(
        &cursor_cases[0], "Hbudget_cursors");
    thm impossible = conv_rule(reduce_rewrite_conv(THM_LIST(
        ann_shape, cursors_nil, cm_ann_cursors_def)), nonempty);
    CONTR_TAC(cursor_cases[0], impossible);
  }
  gnode cons = cursor_cases[1];
  thm cursors_cons = cm_br_named_shape(&cons, "Hbudget_cursors");
  term cursor = cm_br_app_arg_from_right(rhs_of(cursors_cons), 1);
  gnode_list cursor_shapes = DISJ_CASES_TAC(cons,
      ispec_rule(cursor, get_datatype_cases("cm_acursor")),
      "Hbudget_cursor");
  gnode cursor_branch = cursor_shapes[0];
  thm cursor_shape = cm_br_named_shape(
      &cursor_branch, "Hbudget_cursor");
  thm full_shape = conv_rule(rewrite_conv(THM_LIST(
      cursors_cons, cursor_shape)), ann_shape);
  shaped_ann = rhs_of(full_shape);
  term shaped_cursor = rhs_of(cursor_shape);
  term phase = cm_br_constructor_arg(shaped_cursor, 4, 0);
  term owner = cm_br_constructor_arg(shaped_cursor, 4, 1);
  thm shaped_budget = conv_rule(reduce_rewrite_conv(THM_LIST(
      full_shape, get_cm_task_budget_def(), cm_ann_cursors_def,
      get_cm_cursors_budget_def(), cm_cursor_phase_def,
      cm_cursor_temp_def)), budget);
  thm phase_budget = conjunct1_rule(shaped_budget);
  thm shaped_coordinate = conv_rule(reduce_rewrite_conv(THM_LIST(
      full_shape, cm_task_coordinate_ready_def,
      cm_annotation_child_ready_def)), coordinate);
  shaped_coordinate = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_ann_temp_def, cm_ann_break_def, cm_ann_continue_def,
      cm_ann_cursors_def, cm_cursors_coordinate_def,
      cm_cursor_phase_def, cm_cursor_temp_def,
      cm_cursor_break_def, cm_cursor_continue_def)),
      shaped_coordinate);
  thm child_temp = conjunct1_rule(shaped_coordinate);
  thm result = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, shaped_ann, phase, owner),
      cm_phase_budget_spill_ready);
  result = match_mp_rule(result, phase_budget);
  result = conv_rule(rewrite_conv(THM_LIST(cm_ann_temp_def)),
      result);
  result = match_mp_rule(result, child_temp);
  thm target_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
      full_shape, cm_ann_cursors_def, cm_cursor_phase_def,
      get_theorem_by_name("HD"),
      get_theorem_by_name("NOT_CONS_NIL"))),
      goal_ccl(cursor_branch->g));
  ACCEPT_TAC(cursor_branch,
      eq_mp_rule(sym_rule(target_view), result));
  return gnode_prove(root);
}
PROOF thm cm_task_budget_v_spill_ready =
    cm_prove_task_budget_v_spill_ready();

PROOF static int cmc_preservation_budget_ready_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_budget_ready_axioms_before,
      "cmc_preservation_budget_ready introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_budget_ready_checks =
    cmc_preservation_budget_ready_final_checks();
