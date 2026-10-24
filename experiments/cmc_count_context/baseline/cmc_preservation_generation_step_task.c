#include "proof/proof.h"
#include "userlib/proof.h"
#include "cmc_preservation_generation_step_task.h"
#include "cmc_preservation_generation_step_apply.h"
#include "cmc_preservation_generation_step_start.h"
#include "cmc_preservation_generation_task.h"
#include "cmc_preservation_source.h"

#require "cmc_preservation_generation_step_apply.c"
#require "cmc_preservation_source.c"

PROOF static size_t _cmc_preservation_generation_step_task_axioms_before =
    vector_size(get_all_axioms());

PROOF static term cm_ggt_app_arg_from_right(
    term application, size_t offset) {
  for (size_t i = 0; i < offset; ++i) {
    application = dest_comb(application).tm1;
  }
  return dest_comb(application).tm2;
}

PROOF static term cm_ggt_constructor_arg(
    term constructor, size_t arity, size_t index) {
  return cm_ggt_app_arg_from_right(
      constructor, arity - index - 1);
}

PROOF static thm cm_prove_ggt_v_success_top_not_call(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (v:cm_value) (st:cm_src_state)
         (head:cm_frame) (tail:(cm_frame)list).
         cm_task_succeeds
           (CMVTask p fid v st (head :: tail)) ==>
         ~(cm_is_call_frame head)`);
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list cases = DISJ_CASES_TAC(introduced,
      ispec_rule(`head:cm_frame`, get_datatype_cases("cm_frame")),
      "Hhead");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode branch = cases[i];
    while (true) {
      labeled_term_list assumptions = goal_lasmps(branch->g);
      int index = labeled_term_list_index(assumptions, "Hhead");
      if (!is_exists(assumptions[index].tm)) break;
      branch = ASMP_EXISTS_TAC(branch, "Hhead", NULL);
    }
    thm shape = assume_rule(
        goal_lasmps(branch->g)[labeled_term_list_index(
          goal_lasmps(branch->g), "Hhead")].tm);
    if (i != 22) {
      term concrete = rhs_of(shape);
      thm concrete_not_call = eqt_elim_rule(apply_conversion(
          reduce_rewrite_conv(THM_LIST(get_cm_is_call_frame_def())),
          `~(cm_is_call_frame ${concrete:cm_frame})`));
      thm not_call = conv_rule(
          rewrite_conv(THM_LIST(gsym_rule(shape))), concrete_not_call);
      CONTR_TAC(branch, contra(not_call, assume_rule(
          `cm_is_call_frame (head:cm_frame)`)));
      continue;
    }
    term task =
        `CMVTask (p:cm_program) (fid:int) (v:cm_value)
          (st:cm_src_state) ((head:cm_frame) :: (tail:(cm_frame)list))`;
    thm not_done = eqf_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(get_cm_task_done_def())),
        `cm_task_done ${task:cm_task}`));
    thm next_success = match_mp_rule(match_mp_rule(
        spec_rule(task, cm_task_succeeds_step), not_done),
        assume_rule(`cm_task_succeeds ${task:cm_task}`));
    term next = `cm_step ${task:cm_task}`;
    thm no_error = match_mp_rule(specl_rule(TERM_LIST(
        `1i`, next), cm_task_succeeds_not_error), next_success);
    thm impossible = conv_rule(reduce_rewrite_conv(THM_LIST(
        shape, get_cm_step_def(), get_cm_vapply_def(),
        get_theorem_by_name("NOT_CONS_NIL"),
        get_theorem_by_name("HD"), get_theorem_by_name("TL"),
        cm_error_task_def)), no_error);
    CONTR_TAC(branch, impossible);
  }
  return gnode_prove(root);
}
PROOF static thm cm_ggt_v_success_top_not_call =
    cm_prove_ggt_v_success_top_not_call();

PROOF static thm cm_prove_task_generation_below_step(void) {
  term static_valid = `cm_task_static_valid (task:cm_task)`;
  term generation =
      `cm_task_generation_below (root:cm_program) (task:cm_task)`;
  term succeeds = `cm_task_succeeds (task:cm_task)`;
  term target =
      `cm_task_generation_below (root:cm_program) (cm_step task)`;
  term body = imp_chain(
      TERM_LIST(static_valid, generation, succeeds), target);
  gnode root_node = gnode_new_with_ccl(
      list_mk_forall(free_vars(body), body));
  gnode introduced = AUTO_INTROS_TAC(root_node);
  gnode_list cases = DISJ_CASES_TAC(introduced,
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
    term concrete = rhs_of(task_shape);
    thm generation_open = conv_rule(reduce_rewrite_conv(THM_LIST(
        task_shape, cm_task_generation_below_def)), assume_rule(
          `cm_task_generation_below (root:cm_program) (task:cm_task)`));
    if (i == 6) {
      thm target_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
          task_shape, get_cm_step_def(), cm_task_generation_below_def)),
          goal_ccl(branch->g));
      ACCEPT_TAC(branch,
          eq_mp_rule(sym_rule(target_view), generation_open));
      continue;
    }
    thm result = empty_theorem;
    if (i == 0) {
      term program = cm_ggt_constructor_arg(concrete, 2, 0);
      term input = cm_ggt_constructor_arg(concrete, 2, 1);
      thm program_eq = generation_open;
      thm initial_state = spec_rule(input,
          spec_rule(`root:cm_program`, cm_state_generation_initial));
      thm empty_values = eqt_elim_rule(apply_conversion(
          reduce_rewrite_conv(THM_LIST(cm_values_generation_below_def)),
          `cm_values_generation_below
            (cm_state_nextgen
              (cm_initial_state (root:cm_program) ${input:(int)list}))
            ([]:(cm_value)list)`));
      thm halt_frames = eqt_elim_rule(apply_conversion(
          reduce_rewrite_conv(THM_LIST(
            cm_frames_generation_below_def,
            cm_frame_generation_below_def, cm_frame_parent_fid_def)),
          `cm_frames_generation_below (root:cm_program) (--1i)
            (cm_state_nextgen
              (cm_initial_state root ${input:(int)list})) [CMHaltK]`));
      result = specl_rule(TERM_LIST(
          `root:cm_program`, `--1i`,
          `cm_program_main (root:cm_program)`, `[]:(cm_value)list`,
          `cm_initial_state (root:cm_program) ${input:(int)list}`,
          `CMIntTy`, `[CMHaltK]`), cm_begin_call_generation_below);
      result = match_mp_rule(result, initial_state);
      result = match_mp_rule(result, empty_values);
      result = match_mp_rule(result, halt_frames);
      result = conv_rule(rewrite_conv(THM_LIST(
          task_shape, program_eq, get_cm_step_def())), result);
      gnode reduced = CONV_TAC(branch, rewrite_conv(THM_LIST(
          task_shape, program_eq, get_cm_step_def())));
      ACCEPT_TAC(reduced, result);
      continue;
    }
    term program = cm_ggt_constructor_arg(concrete, 5, 0);
    term fid = cm_ggt_constructor_arg(concrete, 5, 1);
    term payload = cm_ggt_constructor_arg(concrete, 5, 2);
    term state = cm_ggt_constructor_arg(concrete, 5, 3);
    term frames = cm_ggt_constructor_arg(concrete, 5, 4);
    thm program_eq = conjunct1_rule(generation_open);
    thm state_below = conjunct1_rule(conjunct2_rule(generation_open));
    thm static_open = conv_rule(reduce_rewrite_conv(THM_LIST(
        task_shape, program_eq, cm_task_static_valid_def)), assume_rule(
          `cm_task_static_valid (task:cm_task)`));
    if (i == 1 || i == 2 || i == 3) {
      thm frames_below = conjunct2_rule(conjunct2_rule(generation_open));
      if (i == 1) {
        result = specl_rule(TERM_LIST(
            `root:cm_program`, fid, payload, state, frames),
            cm_rstart_generation_below);
      } else if (i == 2) {
        result = specl_rule(TERM_LIST(
            `root:cm_program`, fid, payload, state, frames),
            cm_lstart_generation_below);
      } else {
        result = specl_rule(TERM_LIST(
            `root:cm_program`, fid, payload, state, frames),
            cm_sstart_generation_below);
      }
      result = match_mp_rule(result, conjunct1_rule(static_open));
      result = match_mp_rule(result, state_below);
      result = match_mp_rule(result, frames_below);
      result = conv_rule(rewrite_conv(THM_LIST(
          task_shape, program_eq, get_cm_step_def())), result);
      gnode reduced = CONV_TAC(branch, rewrite_conv(THM_LIST(
          task_shape, program_eq, get_cm_step_def())));
      ACCEPT_TAC(reduced, result);
      continue;
    }
    thm payload_below = conjunct1_rule(
        conjunct2_rule(conjunct2_rule(generation_open)));
    thm frames_below = conjunct2_rule(
        conjunct2_rule(conjunct2_rule(generation_open)));
    thm state_open = conv_rule(rewrite_conv(THM_LIST(
        cm_state_generation_below_def)), state_below);
    thm terminal_control = i == 4
        ? eqt_elim_rule(apply_conversion(
            reduce_rewrite_conv(THM_LIST(
              cm_control_generation_below_def)),
            `cm_control_generation_below
              (cm_state_nextgen ${state:cm_src_state}) (CMError 2i)`))
        : payload_below;
    thm terminal_generation = conj_rule(
        conjunct1_rule(state_open),
        conj_rule(conjunct2_rule(conjunct2_rule(state_open)),
          terminal_control));
    gnode_list frame_cases = DISJ_CASES_TAC(branch,
        ispec_rule(frames, get_theorem_by_name("list_CASES")),
        "Hframes");
    {
      thm nil_shape = assume_rule(
          goal_lasmps(frame_cases[0]->g)[labeled_term_list_index(
            goal_lasmps(frame_cases[0]->g), "Hframes")].tm);
      thm_list finish_rules = THM_LIST(
          task_shape, program_eq, nil_shape, get_cm_step_def(),
          cm_task_generation_below_def, cm_control_generation_below_def,
          conjunct1_rule(terminal_generation),
          conjunct1_rule(conjunct2_rule(terminal_generation)),
          conjunct2_rule(conjunct2_rule(terminal_generation)),
          ispecl_rule(TERM_LIST(
            `condition:bool`, `cm_task_generation_below (root:cm_program)`,
            `yes_task:cm_task`, `no_task:cm_task`),
            get_theorem_by_name("COND_RAND")),
          get_theorem_by_name("COND_ID"));
      thm target_view = apply_conversion(
          reduce_rewrite_conv(finish_rules), goal_ccl(frame_cases[0]->g));
      ACCEPT_TAC(frame_cases[0], eqt_elim_rule(target_view));
    }
    {
      gnode cons_case = ASMP_EXISTS_TAC(
          frame_cases[1], "Hframes", "head");
      cons_case = ASMP_EXISTS_TAC(cons_case, "Hframes", "tail");
      thm cons_shape = assume_rule(
          goal_lasmps(cons_case->g)[labeled_term_list_index(
            goal_lasmps(cons_case->g), "Hframes")].tm);
      thm frames_open = conv_rule(reduce_rewrite_conv(THM_LIST(
          cons_shape, cm_frames_generation_below_def)), frames_below);
      term head = `head:cm_frame`;
      term tail = `tail:(cm_frame)list`;
      thm not_exit = empty_theorem;
      if (i == 5) {
        gnode_list exit_cases = BOOL_CASES_TAC(
            cons_case,
            `cm_control_kind ${payload:cm_control} == 4i`,
            "Hexit_cons");
        thm is_exit = assume_rule(
            goal_lasmps(exit_cases[0]->g)[labeled_term_list_index(
              goal_lasmps(exit_cases[0]->g), "Hexit_cons")].tm);
        thm_list exit_rules = THM_LIST(
            task_shape, program_eq, cons_shape, is_exit,
            get_cm_step_def(), cm_task_generation_below_def,
            cm_control_generation_below_def);
        thm normalized = conv_rule(
            reduce_rewrite_conv(exit_rules), terminal_generation);
        thm target_view = apply_conversion(
            reduce_rewrite_conv(exit_rules),
            goal_ccl(exit_cases[0]->g));
        ACCEPT_TAC(exit_cases[0],
            eq_mp_rule(sym_rule(target_view), normalized));
        cons_case = exit_cases[1];
        not_exit = assume_rule(
            goal_lasmps(cons_case->g)[labeled_term_list_index(
              goal_lasmps(cons_case->g), "Hexit_cons")].tm);
      }
      if (i == 4) {
        thm active_success = conv_rule(rewrite_conv(THM_LIST(
            task_shape, program_eq, cons_shape)), assume_rule(succeeds));
        thm not_call = match_mp_rule(specl_rule(TERM_LIST(
            `root:cm_program`, fid, payload, state, head, tail),
            cm_ggt_v_success_top_not_call), active_success);
        result = specl_rule(TERM_LIST(
            `root:cm_program`, fid, head, payload, state, tail),
            cm_vapply_generation_below);
        result = match_mp_rule(result, not_call);
      } else {
        result = specl_rule(TERM_LIST(
            `root:cm_program`, fid, head, payload, state, tail),
            cm_capply_generation_below);
      }
      result = match_mp_rule(result, state_below);
      result = match_mp_rule(result, payload_below);
      result = match_mp_rule(result, conjunct1_rule(frames_open));
      result = match_mp_rule(result, conjunct2_rule(frames_open));
      thm_list step_rules = THM_LIST(
          task_shape, program_eq, cons_shape, get_cm_step_def(),
          get_theorem_by_name("NOT_CONS_NIL"),
          get_theorem_by_name("HD"), get_theorem_by_name("TL"));
      if (i == 5) vector_add(&step_rules, not_exit);
      result = conv_rule(rewrite_conv(step_rules), result);
      gnode reduced = CONV_TAC(cons_case, rewrite_conv(step_rules));
      ACCEPT_TAC(reduced, result);
    }
  }
  return gnode_prove(root_node);
}
PROOF thm cm_task_generation_below_step =
    cm_prove_task_generation_below_step();

PROOF static int cmc_preservation_generation_step_task_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_generation_step_task_axioms_before,
      "cmc_preservation_generation_step_task introduced an axiom");
  ENSURE_COND(vector_size(hyp(cm_task_generation_below_step)) == 0,
      "task generation-step theorem is not closed");
  return 0;
err:
  return -1;
}

PROOF static int _cmc_preservation_generation_step_task_checks =
    cmc_preservation_generation_step_task_final_checks();
