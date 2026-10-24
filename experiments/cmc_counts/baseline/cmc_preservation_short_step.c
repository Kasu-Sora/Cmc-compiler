#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_short_step.h"
#include "cmc_preservation_short_start.h"
#include "cmc_preservation_short_value.h"
#include "cmc_preservation_short_control.h"
#include "cmc_preservation_short_defs.h"
#include "cmc_preservation_generation.h"
#include "cmc_lang.h"

#require "cmc_preservation_short_control.c"

PROOF static size_t _cmc_preservation_short_step_axioms_before =
    vector_size(get_all_axioms());

PROOF static term cm_sd_app_arg_from_right(
    term application, size_t offset) {
  for (size_t i = 0; i < offset; ++i) {
    application = dest_comb(application).tm1;
  }
  return dest_comb(application).tm2;
}

PROOF static term cm_sd_constructor_arg(
    term constructor, size_t arity, size_t index) {
  return cm_sd_app_arg_from_right(
      constructor, arity - index - 1);
}

PROOF static thm cm_sd_named_shape(
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

PROOF static thm cm_prove_sd_task_cond(void) {
  gnode root = gnode_new_with_ccl(
      `!(condition:bool) (yes:cm_task) (no:cm_task).
         cm_task_short_ready (if condition then yes else no) <=>
         (if condition
          then cm_task_short_ready yes
          else cm_task_short_ready no)`);
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list cases = BOOL_CASES_TAC(
      introduced, `condition:bool`, "Hsd_condition");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    CONV_WITH_ASMP_TAC(cases[i], reduce_rewrite_conv, THM_LIST());
  }
  return gnode_prove(root);
}
PROOF static thm cm_sd_task_cond = cm_prove_sd_task_cond();

PROOF static thm cm_prove_task_short_step(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (task:cm_task) (ann:cm_annotation).
         cm_task_generation_safe p task ann ==>
         cm_annotation_erases task ann ==>
         cm_task_runtime_invariant p task ann ==>
         cm_task_short_ready task ==>
         cm_task_short_ready (cm_step task)`);
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list cases = DISJ_CASES_TAC(introduced,
      ispec_rule(`task:cm_task`, get_datatype_cases("cm_task")),
      "Hsd_task");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode branch = cases[i];
    thm task_shape = cm_sd_named_shape(&branch, "Hsd_task");
    term concrete_task = rhs_of(task_shape);
    thm_list shapes = THM_LIST(task_shape);
    thm program_eq = empty_theorem;
    if (i < 6) {
      thm shaped_generation = conv_rule(
          rewrite_conv(THM_LIST(task_shape)), assume_rule(
            `cm_task_generation_safe (p:cm_program)
              (task:cm_task) (ann:cm_annotation)`));
      thm task_generation = conjunct1_rule(conv_rule(
          rewrite_conv(THM_LIST(cm_task_generation_safe_def)),
          shaped_generation));
      thm opened_generation = conv_rule(
          reduce_rewrite_conv(THM_LIST(
            cm_task_generation_below_def)), task_generation);
      program_eq = i == 0
          ? opened_generation
          : conjunct1_rule(opened_generation);
      vector_add(&shapes, program_eq);
    }
    if (i == 0 || i == 6) {
      thm_list rules = (thm_list)vector_copy(shapes);
      vector_add(&rules, get_cm_step_def());
      vector_add(&rules, get_cm_begin_call_def());
      vector_add(&rules, cm_sd_task_cond);
      vector_add(&rules, cm_task_short_ready_def);
      vector_add(&rules, cm_frames_short_ready_def);
      vector_add(&rules, cm_frame_short_ready_def);
      vector_add(&rules, get_theorem_by_name("COND_CLAUSES"));
      vector_add(&rules, get_theorem_by_name("COND_ID"));
      vector_add(&rules, get_theorem_by_name("NOT_CONS_NIL"));
      ACCEPT_TAC(branch, eqt_elim_rule(apply_conversion(
          reduce_rewrite_conv(rules), goal_ccl(branch->g))));
      continue;
    }
    term fid = cm_sd_constructor_arg(concrete_task, 5, 1);
    term payload = cm_sd_constructor_arg(concrete_task, 5, 2);
    term st = cm_sd_constructor_arg(concrete_task, 5, 3);
    term ks = cm_sd_constructor_arg(concrete_task, 5, 4);
    thm rooted_generation = conv_rule(rewrite_conv(shapes),
        assume_rule(
          `cm_task_generation_safe (p:cm_program)
            (task:cm_task) (ann:cm_annotation)`));
    thm rooted_short = conv_rule(rewrite_conv(shapes),
        assume_rule(`cm_task_short_ready (task:cm_task)`));
    thm result = empty_theorem;
    if (i == 1) {
      result = specl_rule(TERM_LIST(
          `p:cm_program`, fid, payload, st, ks,
          `ann:cm_annotation`), cm_task_short_r_step);
      result = match_mp_rule(result, rooted_generation);
      result = match_mp_rule(result, rooted_short);
    } else if (i == 2) {
      result = specl_rule(TERM_LIST(
          `p:cm_program`, fid, payload, st, ks,
          `ann:cm_annotation`), cm_task_short_l_step);
      result = match_mp_rule(result, rooted_generation);
      result = match_mp_rule(result, rooted_short);
    } else if (i == 3) {
      result = specl_rule(TERM_LIST(
          `p:cm_program`, fid, payload, st, ks,
          `ann:cm_annotation`), cm_task_short_s_step);
      result = match_mp_rule(result, rooted_generation);
      result = match_mp_rule(result, rooted_short);
    } else if (i == 4) {
      result = specl_rule(TERM_LIST(
          `p:cm_program`, fid, payload, st, ks,
          `ann:cm_annotation`), cm_task_short_v_step);
      result = match_mp_rule(result, rooted_generation);
      result = match_mp_rule(result, conv_rule(rewrite_conv(shapes),
          assume_rule(
            `cm_annotation_erases (task:cm_task)
              (ann:cm_annotation)`)));
      result = match_mp_rule(result, conv_rule(rewrite_conv(shapes),
          assume_rule(
            `cm_task_runtime_invariant (p:cm_program)
              (task:cm_task) (ann:cm_annotation)`)));
      result = match_mp_rule(result, rooted_short);
    } else {
      result = specl_rule(TERM_LIST(
          `p:cm_program`, fid, payload, st, ks,
          `ann:cm_annotation`), cm_task_short_c_step);
      result = match_mp_rule(result, rooted_generation);
      result = match_mp_rule(result, conv_rule(rewrite_conv(shapes),
          assume_rule(
            `cm_annotation_erases (task:cm_task)
              (ann:cm_annotation)`)));
      result = match_mp_rule(result, conv_rule(rewrite_conv(shapes),
          assume_rule(
            `cm_task_runtime_invariant (p:cm_program)
              (task:cm_task) (ann:cm_annotation)`)));
      result = match_mp_rule(result, rooted_short);
    }
    gnode reduced = CONV_TAC(branch, rewrite_conv(shapes));
    ACCEPT_TAC(reduced, result);
  }
  return gnode_prove(root);
}
PROOF thm cm_task_short_step = cm_prove_task_short_step();

PROOF static int cmc_preservation_short_step_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_short_step_axioms_before,
      "cmc_preservation_short_step introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_short_step_checks =
    cmc_preservation_short_step_final_checks();
