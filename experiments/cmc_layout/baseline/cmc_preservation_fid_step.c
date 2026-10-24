#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_fid_step.h"
#include "cmc_preservation_generation_task.h"

#require "cmc_preservation_fid_apply.c"
#require "cmc_preservation_type_ready.c"
#require "cmc_preservation_code_task.c"
#require "cmc_preservation_generation_task.c"

PROOF static size_t _cmc_preservation_fid_step_axioms_before =
    vector_size(get_all_axioms());

PROOF static term cm_fid_step_app_arg_from_right(
    term application, size_t offset) {
  for (size_t i = 0; i < offset; ++i) {
    application = dest_comb(application).tm1;
  }
  return dest_comb(application).tm2;
}

PROOF static term cm_fid_step_constructor_arg(
    term constructor, size_t arity, size_t index) {
  return cm_fid_step_app_arg_from_right(
      constructor, arity - index - 1);
}

PROOF static thm cm_fid_step_pick_conjunct(
    thm source, term wanted) {
  if (alpha_compare(concl(source), wanted) == 0) return source;
  if (!is_conj(concl(source))) return empty_theorem;
  thm left = cm_fid_step_pick_conjunct(
      conjunct1_rule(source), wanted);
  if (!IS_NULL(left)) return left;
  return cm_fid_step_pick_conjunct(
      conjunct2_rule(source), wanted);
}

PROOF static thm cm_fid_step_cond = ispecl_rule(TERM_LIST(
    `condition:bool`, `cm_task_fid_ready (p:cm_program)`,
    `yes_task:cm_task`, `no_task:cm_task`),
    get_theorem_by_name("COND_RAND"));

PROOF static void cm_fid_step_accept(
    gnode branch, thm_list rules, thm result) {
  thm normalized = conv_rule(rewrite_conv(rules), result);
  vector_add(&rules, cm_fid_step_cond);
  vector_add(&rules, cm_task_fid_ready_def);
  vector_add(&rules, normalized);
  vector_add(&rules, get_theorem_by_name("COND_ID"));
  thm target_view = apply_conversion(
      reduce_rewrite_conv(rules), goal_ccl(branch->g));
  ACCEPT_TAC(branch, eqt_elim_rule(target_view));
}

PROOF static void cm_fid_step_accept_true(
    gnode branch, thm_list rules) {
  vector_add(&rules, cm_fid_step_cond);
  vector_add(&rules, cm_task_fid_ready_def);
  vector_add(&rules, get_theorem_by_name("COND_ID"));
  thm target_view = apply_conversion(
      reduce_rewrite_conv(rules), goal_ccl(branch->g));
  ACCEPT_TAC(branch, eqt_elim_rule(target_view));
}

PROOF static thm cm_prove_task_fid_ready_step(void) {
  term typed = `cm_typed_program (p:cm_program)`;
  term static_ready = `cm_task_static_valid (task:cm_task)`;
  term layout = `cm_task_layout_ready (p:cm_program)
      (task:cm_task) (ann:cm_annotation)`;
  term type_ready = `cm_task_type_ready (p:cm_program)
      (task:cm_task) (ann:cm_annotation)`;
  term fid_ready = `cm_task_fid_ready (p:cm_program) (task:cm_task)`;
  term succeeds = `cm_task_succeeds (task:cm_task)`;
  term target = `cm_task_fid_ready (p:cm_program)
      (cm_step (task:cm_task))`;
  term body = imp_chain(TERM_LIST(
      typed, static_ready, layout, type_ready, fid_ready, succeeds),
      target);
  gnode root = gnode_new_with_ccl(
      list_mk_forall(free_vars(body), body));
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list cases = DISJ_CASES_TAC(introduced,
      ispec_rule(`task:cm_task`, get_datatype_cases("cm_task")),
      "Htask");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode branch = cases[i];
    while (is_exists(goal_lasmps(branch->g)[
        labeled_term_list_index(
          goal_lasmps(branch->g), "Htask")].tm)) {
      branch = ASMP_EXISTS_TAC(branch, "Htask", NULL);
    }
    thm shape = assume_rule(goal_lasmps(branch->g)[
        labeled_term_list_index(
          goal_lasmps(branch->g), "Htask")].tm);
    term concrete = rhs_of(shape);
    thm layout_open = conv_rule(reduce_rewrite_conv(THM_LIST(
        shape, cm_task_layout_ready_def)), assume_rule(layout));
    if (i == 0) {
      term q = cm_fid_step_constructor_arg(concrete, 2, 0);
      term input = cm_fid_step_constructor_arg(concrete, 2, 1);
      thm same_program = cm_fid_step_pick_conjunct(
          layout_open, mk_eq(q, `p:cm_program`));
      thm typed_open = conv_rule(rewrite_conv(THM_LIST(
          get_cm_typed_program_def())), assume_rule(typed));
      thm main_low = cm_fid_step_pick_conjunct(
          typed_open, `0i <= cm_program_main (p:cm_program)`);
      thm main_high = cm_fid_step_pick_conjunct(typed_open,
          `cm_program_main (p:cm_program) <
           ilength (cm_program_functions p)`);
      thm main_ready = conj_rule(main_low, main_high);
      thm halt_frames = eqt_elim_rule(apply_conversion(
          reduce_rewrite_conv(THM_LIST(
            cm_frames_fid_ready_def, cm_frame_fid_ready_def,
            cm_frame_parent_fid_def,
            get_datatype_distinctness("cm_frame"))),
          `cm_frames_fid_ready (p:cm_program) (--1i) [CMHaltK]`));
      thm result = specl_rule(TERM_LIST(
          `p:cm_program`, `--1i`, `cm_program_main (p:cm_program)`,
          `[]:(cm_value)list`,
          `cm_initial_state (p:cm_program) ${input:(int)list}`,
          `CMIntTy:cm_type`, `[CMHaltK]:(cm_frame)list`),
          cm_begin_call_fid_ready);
      result = match_mp_rule(result, main_ready);
      result = match_mp_rule(result, halt_frames);
      cm_fid_step_accept(branch, THM_LIST(
          shape, same_program, get_cm_step_def()), result);
      continue;
    }
    if (i == 6) {
      cm_fid_step_accept_true(branch, THM_LIST(
          shape, get_cm_step_def(), cm_task_fid_ready_def));
      continue;
    }
    term q = cm_fid_step_constructor_arg(concrete, 5, 0);
    term fid = cm_fid_step_constructor_arg(concrete, 5, 1);
    term payload = cm_fid_step_constructor_arg(concrete, 5, 2);
    term st = cm_fid_step_constructor_arg(concrete, 5, 3);
    term ks = cm_fid_step_constructor_arg(concrete, 5, 4);
    thm same_program = cm_fid_step_pick_conjunct(
        layout_open, mk_eq(q, `p:cm_program`));
    thm shaped_fid = conv_rule(reduce_rewrite_conv(THM_LIST(
        shape, cm_task_fid_ready_def)), assume_rule(fid_ready));
    if (i == 1 || i == 2 || i == 3) {
      thm ready_open = conv_rule(reduce_rewrite_conv(THM_LIST(
          shape, get_cm_task_type_ready_def())),
          assume_rule(type_ready));
      thm fid_low = cm_fid_step_pick_conjunct(
          ready_open, `0i <= ${fid:int}`);
      thm fid_high = cm_fid_step_pick_conjunct(ready_open,
          `(${fid:int}) < ilength
            (cm_program_functions (p:cm_program))`);
      thm current_ready = conj_rule(fid_low, fid_high);
      thm result = empty_theorem;
      if (i == 1) {
        thm static_open = conv_rule(reduce_rewrite_conv(THM_LIST(
            shape, same_program, cm_task_static_valid_def)),
            assume_rule(static_ready));
        thm expression_static = cm_fid_step_pick_conjunct(
            static_open,
            `cm_expr_static_valid (p:cm_program)
              (inth ${fid:int} (cm_program_functions p))
              ${payload:cm_expr}`);
        result = specl_rule(TERM_LIST(
            `p:cm_program`, fid, payload, st, ks),
            cm_rstart_fid_ready);
        result = match_mp_rule(result, expression_static);
      } else if (i == 2) {
        result = specl_rule(TERM_LIST(
            `p:cm_program`, fid, payload, st, ks),
            cm_lstart_fid_ready);
      } else {
        result = specl_rule(TERM_LIST(
            `p:cm_program`, fid, payload, st, ks),
            cm_sstart_fid_ready);
      }
      result = match_mp_rule(result, current_ready);
      result = match_mp_rule(result, shaped_fid);
      cm_fid_step_accept(branch, THM_LIST(
          shape, same_program, get_cm_step_def()), result);
      continue;
    }
    gnode_list stack_cases = DISJ_CASES_TAC(branch,
        ispec_rule(ks, get_datatype_cases("list")), "Hstack");
    for (size_t j = 0; j < vector_size(stack_cases); ++j) {
      gnode stack_branch = stack_cases[j];
      while (is_exists(goal_lasmps(stack_branch->g)[
          labeled_term_list_index(
            goal_lasmps(stack_branch->g), "Hstack")].tm)) {
        stack_branch = ASMP_EXISTS_TAC(stack_branch, "Hstack", NULL);
      }
      thm stack_shape = assume_rule(goal_lasmps(stack_branch->g)[
          labeled_term_list_index(
            goal_lasmps(stack_branch->g), "Hstack")].tm);
      if (j == 0) {
        cm_fid_step_accept_true(stack_branch, THM_LIST(
            shape, same_program, stack_shape, get_cm_step_def(),
            get_theorem_by_name("HD"), get_theorem_by_name("TL"),
            cm_task_fid_ready_def));
        continue;
      }
      term head = cm_fid_step_app_arg_from_right(
          rhs_of(stack_shape), 1);
      term tail = cm_fid_step_app_arg_from_right(
          rhs_of(stack_shape), 0);
      thm stack_fid = conv_rule(rewrite_conv(THM_LIST(
          stack_shape)), shaped_fid);
      thm result = empty_theorem;
      if (i == 4) {
        thm shaped_static = conv_rule(rewrite_conv(THM_LIST(
            shape, same_program, stack_shape)),
            assume_rule(static_ready));
        thm static_open = conv_rule(reduce_rewrite_conv(THM_LIST(
            cm_task_static_valid_def, cm_frames_static_valid_def)),
            shaped_static);
        thm head_static = cm_fid_step_pick_conjunct(
            static_open,
            `cm_frame_static_valid (p:cm_program) ${fid:int}
              ${head:cm_frame}`);
        thm shaped_succeeds = conv_rule(rewrite_conv(THM_LIST(
            shape, same_program, stack_shape)),
            assume_rule(succeeds));
        result = specl_rule(TERM_LIST(
            `p:cm_program`, fid, head, payload, st, tail),
            cm_vapply_fid_ready);
        result = match_mp_rule(result, head_static);
        result = match_mp_rule(result, stack_fid);
        result = match_mp_rule(result, shaped_succeeds);
      } else {
        result = specl_rule(TERM_LIST(
            `p:cm_program`, fid, head, payload, st, tail),
            cm_capply_fid_ready);
        result = match_mp_rule(result, stack_fid);
      }
      cm_fid_step_accept(stack_branch, THM_LIST(
          shape, same_program, stack_shape, get_cm_step_def(),
          get_theorem_by_name("NOT_CONS_NIL"),
          get_theorem_by_name("HD"), get_theorem_by_name("TL")),
          result);
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_task_fid_ready_step =
    cm_prove_task_fid_ready_step();

PROOF thm get_cm_task_fid_ready_step(void) {
  return cm_task_fid_ready_step;
}

PROOF static int cmc_preservation_fid_step_final_checks(void) {
  ENSURE_COND(vector_size(hyp(cm_task_fid_ready_step)) == 0,
      "task fid-step theorem has assumptions");
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_fid_step_axioms_before,
      "cmc_preservation_fid_step introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_fid_step_checks =
    cmc_preservation_fid_step_final_checks();
