#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_invariant_task.h"

#require "cmc_preservation_invariant_control.c"

PROOF static size_t _cmc_preservation_invariant_task_axioms_before =
    vector_size(get_all_axioms());

PROOF static term cm_ti_app_arg_from_right(
    term application, size_t offset) {
  for (size_t i = 0; i < offset; ++i) {
    application = dest_comb(application).tm1;
  }
  return dest_comb(application).tm2;
}

PROOF static term cm_ti_constructor_arg(
    term constructor, size_t arity, size_t index) {
  return cm_ti_app_arg_from_right(
      constructor, arity - index - 1);
}

PROOF static thm cm_ti_runtime_core(const thm opened_invariant) {
  return conv_rule(rewrite_conv(THM_LIST(
      gsym_rule(cm_runtime_core_def))),
      conjunct2_rule(opened_invariant));
}

PROOF static thm cm_prove_task_runtime_step(void) {
  term typed = `cm_typed_program (root:cm_program)`;
  term erases =
      `cm_annotation_erases (task:cm_task) (ann:cm_annotation)`;
  term ready =
      `cm_runtime_step_ready (root:cm_program)
        (task:cm_task) (ann:cm_annotation)`;
  term invariant =
      `cm_task_runtime_invariant (root:cm_program)
        (task:cm_task) (ann:cm_annotation)`;
  term target =
      `cm_task_runtime_invariant (root:cm_program)
        (cm_step (task:cm_task))
        (cm_update_annotation
          (cm_annotation_step (task:cm_task)
            (ann:cm_annotation)))`;
  term body = imp_chain(
      TERM_LIST(typed, erases, ready, invariant), target);
  gnode root_node = gnode_new_with_ccl(
      list_mk_forall(free_vars(body), body));
  gnode introduced = AUTO_INTROS_TAC(root_node);
  gnode_list cases = DISJ_CASES_TAC(
      introduced,
      ispec_rule(`task:cm_task`, get_datatype_cases("cm_task")),
      "Htask");

  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode branch = cases[i];
    while (true) {
      labeled_term_list assumptions = goal_lasmps(branch->g);
      int index = labeled_term_list_index(assumptions, "Htask");
      if (!is_exists(assumptions[index].tm)) break;
      branch = ASMP_EXISTS_TAC(branch, "Htask", NULL);
    }
    thm task_shape = assume_rule(
        goal_lasmps(branch->g)[labeled_term_list_index(
          goal_lasmps(branch->g), "Htask")].tm);
    term concrete_task = rhs_of(task_shape);
    thm runtime_open = conv_rule(
        reduce_rewrite_conv(THM_LIST(
          task_shape, cm_runtime_step_ready_def)),
        assume_rule(ready));
    thm invariant_open = conv_rule(
        reduce_rewrite_conv(THM_LIST(
          task_shape, cm_task_runtime_invariant_def)),
        assume_rule(invariant));
    thm shaped_erases = conv_rule(
        rewrite_conv(THM_LIST(task_shape)), assume_rule(erases));
    thm_list shapes = THM_LIST(task_shape);
    thm result = empty_theorem;

    if (i == 0) {
      term input = cm_ti_constructor_arg(concrete_task, 2, 1);
      thm layout_open = conv_rule(
          reduce_rewrite_conv(THM_LIST(
            task_shape, cm_task_layout_ready_def)),
          conjunct2_rule(runtime_open));
      thm program_eq = conjunct1_rule(layout_open);
      thm annotation_eq =
          conjunct1_rule(conjunct2_rule(layout_open));
      thm call_ok = conjunct2_rule(conjunct2_rule(layout_open));
      result = specl_rule(TERM_LIST(`root:cm_program`, input),
          cm_task_runtime_start_step);
      result = match_mp_rule(result, assume_rule(typed));
      result = match_mp_rule(result, call_ok);
      vector_add(&shapes, program_eq);
      vector_add(&shapes, annotation_eq);
    } else if (i == 1 || i == 2) {
      term fid = cm_ti_constructor_arg(concrete_task, 5, 1);
      term expr = cm_ti_constructor_arg(concrete_task, 5, 2);
      term st = cm_ti_constructor_arg(concrete_task, 5, 3);
      term ks = cm_ti_constructor_arg(concrete_task, 5, 4);
      thm fid_nonnegative = conjunct1_rule(runtime_open);
      thm layout_open = conv_rule(
          reduce_rewrite_conv(THM_LIST(
            task_shape, cm_task_layout_ready_def)),
          conjunct2_rule(runtime_open));
      thm program_eq = conjunct1_rule(layout_open);
      thm local_ready = conjunct2_rule(layout_open);
      thm core = cm_ti_runtime_core(invariant_open);
      if (i == 1) {
        result = specl_rule(TERM_LIST(
            `root:cm_program`, fid, expr, st, ks,
            `ann:cm_annotation`), cm_task_runtime_r_step);
        result = match_mp_rule(result, assume_rule(typed));
        result = match_mp_rule(result, fid_nonnegative);
        result = match_mp_rule(result, local_ready);
        result = match_mp_rule(result, core);
      } else {
        result = specl_rule(TERM_LIST(
            `root:cm_program`, fid, expr, st, ks,
            `ann:cm_annotation`), cm_task_runtime_l_step);
        result = match_mp_rule(result, local_ready);
        result = match_mp_rule(result, core);
      }
      vector_add(&shapes, program_eq);
    } else if (i == 3) {
      term fid = cm_ti_constructor_arg(concrete_task, 5, 1);
      term stmt = cm_ti_constructor_arg(concrete_task, 5, 2);
      term st = cm_ti_constructor_arg(concrete_task, 5, 3);
      term ks = cm_ti_constructor_arg(concrete_task, 5, 4);
      thm readiness_tail = conjunct2_rule(runtime_open);
      thm fid_nonnegative = conjunct1_rule(readiness_tail);
      thm layout_open = conv_rule(
          reduce_rewrite_conv(THM_LIST(
            task_shape, cm_task_layout_ready_def)),
          conjunct2_rule(readiness_tail));
      thm program_eq = conjunct1_rule(layout_open);
      thm stmt_ready = conjunct2_rule(layout_open);
      thm core = cm_ti_runtime_core(invariant_open);
      result = specl_rule(TERM_LIST(
          `root:cm_program`, fid, stmt, st, ks,
          `ann:cm_annotation`), cm_task_runtime_s_step);
      result = match_mp_rule(result, assume_rule(typed));
      result = match_mp_rule(result, fid_nonnegative);
      result = match_mp_rule(result, stmt_ready);
      result = match_mp_rule(result, core);
      vector_add(&shapes, program_eq);
    } else if (i == 4) {
      term fid = cm_ti_constructor_arg(concrete_task, 5, 1);
      term value = cm_ti_constructor_arg(concrete_task, 5, 2);
      term st = cm_ti_constructor_arg(concrete_task, 5, 3);
      term ks = cm_ti_constructor_arg(concrete_task, 5, 4);
      thm readiness_tail = conjunct2_rule(runtime_open);
      thm layout_open = conv_rule(
          reduce_rewrite_conv(THM_LIST(
            task_shape, cm_task_layout_ready_def)),
          conjunct1_rule(runtime_open));
      thm program_eq = conjunct1_rule(layout_open);
      thm value_ready = conjunct2_rule(layout_open);
      thm fid_ready = conjunct1_rule(readiness_tail);
      thm spill_ready = conjunct1_rule(conjunct2_rule(readiness_tail));
      thm source_ready = conjunct2_rule(conjunct2_rule(readiness_tail));
      thm core = cm_ti_runtime_core(invariant_open);
      thm rooted_erases = conv_rule(
          rewrite_conv(THM_LIST(program_eq)), shaped_erases);
      result = specl_rule(TERM_LIST(
          `root:cm_program`, fid, value, st, ks,
          `ann:cm_annotation`), cm_task_runtime_v_step);
      result = match_mp_rule(result, assume_rule(typed));
      result = match_mp_rule(result, fid_ready);
      result = match_mp_rule(result, rooted_erases);
      result = match_mp_rule(result, value_ready);
      result = match_mp_rule(result, spill_ready);
      result = match_mp_rule(result, source_ready);
      result = match_mp_rule(result, core);
      vector_add(&shapes, program_eq);
    } else if (i == 5) {
      term fid = cm_ti_constructor_arg(concrete_task, 5, 1);
      term control = cm_ti_constructor_arg(concrete_task, 5, 2);
      term st = cm_ti_constructor_arg(concrete_task, 5, 3);
      term ks = cm_ti_constructor_arg(concrete_task, 5, 4);
      thm layout_open = conv_rule(
          reduce_rewrite_conv(THM_LIST(
            task_shape, cm_task_layout_ready_def)), runtime_open);
      thm program_eq = conjunct1_rule(layout_open);
      thm core = cm_ti_runtime_core(invariant_open);
      thm rooted_erases = conv_rule(
          rewrite_conv(THM_LIST(program_eq)), shaped_erases);
      result = specl_rule(TERM_LIST(
          `root:cm_program`, fid, control, st, ks,
          `ann:cm_annotation`), cm_task_runtime_c_step);
      result = match_mp_rule(result, rooted_erases);
      result = match_mp_rule(result, core);
      vector_add(&shapes, program_eq);
    } else {
      thm_list rules = THM_LIST(
          task_shape, get_cm_step_def(), cm_annotation_step_def,
          cm_update_annotation_def, cm_task_runtime_invariant_def);
      result = conv_rule(reduce_rewrite_conv(rules),
          assume_rule(invariant));
      gnode reduced =
          CONV_TAC(branch, reduce_rewrite_conv(rules));
      ACCEPT_TAC(reduced, result);
      continue;
    }

    result = conv_rule(rewrite_conv(shapes), result);
    gnode reduced = CONV_TAC(branch, rewrite_conv(shapes));
    ACCEPT_TAC(reduced, result);
  }
  return gnode_prove(root_node);
}
PROOF thm cm_task_runtime_step = cm_prove_task_runtime_step();

PROOF static int cmc_preservation_invariant_task_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_invariant_task_axioms_before,
      "cmc_preservation_invariant_task introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_invariant_task_checks =
    cmc_preservation_invariant_task_final_checks();
