#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "userlib/proof_patterns.h"
#include "cmc_preservation_budget_step.h"
#include "cmc_preservation_budget_defs.h"
#include "cmc_preservation_budget_start.h"
#include "cmc_preservation_budget_value.h"
#include "cmc_preservation_budget_control.h"
#include "cmc_preservation_type_ready.h"
#include "cmc_preservation_ready_coordinate.h"
#include "cmc_preservation_generation.h"

#require "userlib/proof_patterns.c"
#require "cmc_preservation_budget_defs.c"
#require "cmc_preservation_budget_start.c"
#require "cmc_preservation_budget_value.c"
#require "cmc_preservation_budget_control.c"
#require "cmc_preservation_type_ready.c"
#require "cmc_preservation_ready_coordinate.c"
#require "cmc_preservation_generation.c"

PROOF static size_t _cmc_preservation_budget_step_axioms_before =
    vector_size(get_all_axioms());

PROOF static term cm_bt_app_arg_from_right(
    term application, size_t offset) {
  for (size_t i = 0; i < offset; ++i) {
    application = dest_comb(application).tm1;
  }
  return dest_comb(application).tm2;
}

PROOF static term cm_bt_constructor_arg(
    term constructor, size_t arity, size_t index) {
  return cm_bt_app_arg_from_right(
      constructor, arity - index - 1);
}

PROOF static void cm_bt_close(
    gnode node, const thm_list structural) {
  thm_list rules = (thm_list)vector_copy(structural);
  labeled_term_list assumptions = goal_lasmps(node->g);
  thm_list facts = (thm_list)vector_create();
  for (size_t i = 0; i < vector_size(assumptions); ++i) {
    thm fact = assume_rule(assumptions[i].tm);
    vector_add(&facts, fact);
    vector_add(&rules, fact);
  }
  for (size_t pass = 0; pass < 6 && IS_NULL(node->solved); ++pass) {
    node = CONV_WITH_ASMP_TAC(node, reduce_rewrite_conv, rules);
  }
  if (!IS_NULL(node->solved)) return;
  if (is_conj(goal_ccl(node->g))) {
    gnode_list parts = CONJ_TAC(node);
    cm_bt_close(parts[0], structural);
    cm_bt_close(parts[1], structural);
    return;
  }
  thm joined = list_conj_rule(facts);
  ACCEPT_TAC(node, mp_rule(int_arith_rule(
      mk_imp(concl(joined), goal_ccl(node->g))), joined));
}

PROOF static thm cm_prove_task_budget_initial(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (input:(int)list).
         cm_task_budget p (CMStartTask p input)
           cm_initial_annotation`);
  CONV_TAC(root, reduce_rewrite_conv(THM_LIST(
      get_cm_task_budget_def(), get_cm_cursors_budget_def(),
      cm_initial_annotation_def, cm_ann_cursors_def)));
  return gnode_prove(root);
}
PROOF thm cm_task_budget_initial =
    cm_prove_task_budget_initial();

PROOF static thm cm_prove_task_budget_start_step(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (input:(int)list) (ann:cm_annotation).
         cm_task_budget p (CMStartTask p input) ann ==>
         cm_task_budget p
           (cm_step (CMStartTask p input))
           (cm_update_annotation
             (cm_annotation_step (CMStartTask p input) ann))`);
  gnode introduced = AUTO_INTROS_TAC(root);
  term call_ready = `cm_call_ok (p:cm_program)
      (cm_program_main p) ([]:(cm_value)list)
      (cm_initial_state p (input:(int)list))`;
  gnode_list call_cases = BOOL_CASES_TAC(
      introduced, call_ready, "Hbudget_start_call");
  for (size_t i = 0; i < vector_size(call_cases); ++i) {
    gnode_list depth_cases = BOOL_CASES_TAC(call_cases[i],
        `cm_call_depth ([CMHaltK]:(cm_frame)list) < 65536i`,
        i == 0 ? "Hbudget_start_depth_yes" :
                 "Hbudget_start_depth_no");
    for (size_t j = 0; j < vector_size(depth_cases); ++j) {
      cm_bt_close(depth_cases[j], THM_LIST(
          get_cm_step_def(), get_cm_begin_call_def(),
          cm_annotation_step_def, cm_update_annotation_def,
          cm_ann_enter_call_def, cm_ann_pc_def, cm_ann_temp_def,
          cm_ann_break_def, cm_ann_continue_def, cm_ann_cursors_def,
          cm_cursor_phase_def, cm_cursor_temp_def,
          cm_phase_frame_def, cm_frame_parent_fid_def,
          get_cm_task_budget_def(), get_cm_cursors_budget_def(),
          get_cm_phase_budget_def(), get_cm_temp_slots_def(),
          get_cm_stemps_def(), get_cm_call_depth_def(),
          get_theorem_by_name("HD"), get_theorem_by_name("TL"),
          get_theorem_by_name("ILENGTH_DEF"),
          get_theorem_by_name("COND_ID")));
    }
  }
  return gnode_prove(root);
}
PROOF static thm cm_task_budget_start_step =
    cm_prove_task_budget_start_step();


PROOF static thm cm_bt_shaped_assumption(
    term proposition, thm task_shape, thm same_program) {
  return conv_rule(rewrite_conv(THM_LIST(
      task_shape, same_program)), assume_rule(proposition));
}

PROOF static thm cm_prove_task_budget_step(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (task:cm_task) (ann:cm_annotation).
         cm_annotation_erases task ann ==>
         cm_task_type_ready p task ann ==>
         cm_task_coordinate_ready p task ann ==>
         cm_task_budget p task ann ==>
         cm_task_budget p (cm_step task)
           (cm_update_annotation
             (cm_annotation_step task ann))`);
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list cases = DISJ_CASES_TAC(introduced,
      ispec_rule(`task:cm_task`, get_datatype_cases("cm_task")),
      "Hbudget_task");
  size_t arities[7] = {2, 5, 5, 5, 5, 5, 3};
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode branch = cases[i];
    labeled_term_list assumptions = goal_lasmps(branch->g);
    while (is_exists(assumptions[
        labeled_term_list_index(assumptions, "Hbudget_task")].tm)) {
      branch = ASMP_EXISTS_TAC(branch, "Hbudget_task", NULL);
      assumptions = goal_lasmps(branch->g);
    }
    thm task_shape = assume_rule(assumptions[
        labeled_term_list_index(assumptions, "Hbudget_task")].tm);
    term concrete_task = rhs_of(task_shape);
    if (i == 6) {
      CONV_TAC(branch, reduce_rewrite_conv(THM_LIST(
          task_shape, get_cm_step_def(), cm_annotation_step_def,
          cm_update_annotation_def, get_cm_task_budget_def())));
      continue;
    }
    term q = cm_bt_constructor_arg(concrete_task, arities[i], 0);
    thm opened_type = conv_rule(reduce_rewrite_conv(THM_LIST(
        task_shape, get_cm_task_type_ready_def())),
        assume_rule(`cm_task_type_ready (p:cm_program)
          (task:cm_task) (ann:cm_annotation)`));
    thm same_program = find_conjunct_rule(opened_type,
        mk_eq(q, `p:cm_program`));
    thm erases = cm_bt_shaped_assumption(
        `cm_annotation_erases (task:cm_task) (ann:cm_annotation)`,
        task_shape, same_program);
    thm typed = cm_bt_shaped_assumption(
        `cm_task_type_ready (p:cm_program)
          (task:cm_task) (ann:cm_annotation)`,
        task_shape, same_program);
    thm coordinate = cm_bt_shaped_assumption(
        `cm_task_coordinate_ready (p:cm_program)
          (task:cm_task) (ann:cm_annotation)`,
        task_shape, same_program);
    thm budget = cm_bt_shaped_assumption(
        `cm_task_budget (p:cm_program)
          (task:cm_task) (ann:cm_annotation)`,
        task_shape, same_program);
    thm result = empty_theorem;
    if (i == 0) {
      result = specl_rule(TERM_LIST(
          `p:cm_program`, cm_bt_constructor_arg(concrete_task, 2, 1),
          `ann:cm_annotation`), cm_task_budget_start_step);
      result = match_mp_rule(result, budget);
    } else {
      term fid = cm_bt_constructor_arg(concrete_task, 5, 1);
      term payload = cm_bt_constructor_arg(concrete_task, 5, 2);
      term state = cm_bt_constructor_arg(concrete_task, 5, 3);
      term frames = cm_bt_constructor_arg(concrete_task, 5, 4);
      thm constructor_step = i == 1 ? cm_task_budget_r_step :
          i == 2 ? cm_task_budget_l_step :
          i == 3 ? cm_task_budget_s_step :
          i == 4 ? cm_task_budget_v_step :
                   cm_task_budget_c_step;
      result = specl_rule(TERM_LIST(
          `p:cm_program`, fid, payload, state, frames,
          `ann:cm_annotation`), constructor_step);
      result = match_mp_rule(result, erases);
      if (i == 4) {
        result = match_mp_rule(result, typed);
        result = match_mp_rule(result, coordinate);
      }
      result = match_mp_rule(result, budget);
    }
    gnode reduced = CONV_TAC(branch,
        rewrite_conv(THM_LIST(task_shape, same_program)));
    ACCEPT_TAC(reduced, result);
  }
  return gnode_prove(root);
}
PROOF thm cm_task_budget_step =
    cm_prove_task_budget_step();

PROOF static int cmc_preservation_budget_step_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_budget_step_axioms_before,
      "cmc_preservation_budget_step introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_budget_step_checks =
    cmc_preservation_budget_step_final_checks();
