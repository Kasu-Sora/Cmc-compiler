#include "proof/proof.h"
#include "userlib/proof.h"
#include "cmc_preservation_generation_static_task.h"
#include "cmc_preservation_generation_static_apply.h"
#include "cmc_preservation_code_task.h"
#include "cmc_preservation_generation_static_start.h"
#include "cmc_preservation_generation_syntax.h"
#include "cmc_preservation_source.h"

#require "cmc_preservation_generation_static_apply.c"
#require "cmc_preservation_code_task.c"
#require "cmc_preservation_source.c"

PROOF static size_t _cmc_preservation_generation_static_task_axioms_before =
    vector_size(get_all_axioms());

PROOF static term cm_gst_app_arg_from_right(
    term application, size_t offset) {
  for (size_t i = 0; i < offset; ++i) {
    application = dest_comb(application).tm1;
  }
  return dest_comb(application).tm2;
}

PROOF static term cm_gst_constructor_arg(
    term constructor, size_t arity, size_t index) {
  return cm_gst_app_arg_from_right(
      constructor, arity - index - 1);
}

PROOF static thm cm_gst_pick_conjunct(
    const thm fact, const term wanted) {
  if (alpha_compare(concl(fact), wanted) == 0) return fact;
  struct dest_conj_results parts = dest_conj(concl(fact));
  thm left = conjunct1_rule(fact);
  if (is_conj(parts.tm1)) {
    thm found = cm_gst_pick_conjunct(left, wanted);
    if (!IS_NULL(found)) return found;
  } else if (alpha_compare(parts.tm1, wanted) == 0) {
    return left;
  }
  return cm_gst_pick_conjunct(conjunct2_rule(fact), wanted);
}

PROOF static thm cm_prove_v_success_top_not_call(void) {
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
PROOF static thm cm_v_success_top_not_call =
    cm_prove_v_success_top_not_call();

PROOF static thm cm_prove_task_static_valid_step(void) {
  term typed = `cm_typed_program (root:cm_program)`;
  term ready = `cm_task_layout_ready (root:cm_program)
      (task:cm_task) (ann:cm_annotation)`;
  term source = `cm_task_static_valid (task:cm_task)`;
  term succeeds = `cm_task_succeeds (task:cm_task)`;
  term target = `cm_task_static_valid (cm_step (task:cm_task))`;
  term body = imp_chain(
      TERM_LIST(typed, ready, source, succeeds), target);
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
    if (i == 6) {
      CONV_TAC(branch, reduce_rewrite_conv(THM_LIST(
          task_shape, get_cm_step_def(), cm_task_static_valid_def)));
      continue;
    }
    thm layout_open = conv_rule(reduce_rewrite_conv(THM_LIST(
        task_shape, cm_task_layout_ready_def)), assume_rule(ready));
    thm program_eq = conjunct1_rule(layout_open);
    thm result = empty_theorem;
    if (i == 0) {
      term input = cm_gst_constructor_arg(concrete, 2, 1);
      thm call_ok = conjunct2_rule(conjunct2_rule(layout_open));
      thm rooted_call_ok = conv_rule(
          rewrite_conv(THM_LIST(program_eq)), call_ok);
      thm call_open = conv_rule(reduce_rewrite_conv(THM_LIST(
          get_cm_call_ok_def())), rooted_call_ok);
      term main_id = `cm_program_main (root:cm_program)`;
      thm main_nonnegative = cm_gst_pick_conjunct(call_open,
          `0i <= cm_program_main (root:cm_program)`);
      thm main_bounded = cm_gst_pick_conjunct(call_open,
          `cm_program_main (root:cm_program) <
           ilength (cm_program_functions root)`);
      thm halt_frames = eqt_elim_rule(apply_conversion(
          reduce_rewrite_conv(THM_LIST(
            cm_frames_static_valid_def, cm_frame_static_valid_def)),
          `cm_frames_static_valid
            (root:cm_program) (--1i) [CMHaltK]`));
      result = specl_rule(TERM_LIST(
          `root:cm_program`, `--1i`, main_id,
          `[]:(cm_value)list`,
          `cm_initial_state (root:cm_program) ${input:(int)list}`,
          `CMIntTy`, `[CMHaltK]`), cm_begin_call_static_valid);
      result = match_mp_rule(result, assume_rule(typed));
      result = match_mp_rule(result, main_nonnegative);
      result = match_mp_rule(result, main_bounded);
      result = match_mp_rule(result, halt_frames);
    } else {
      term fid = cm_gst_constructor_arg(concrete, 5, 1);
      term payload = cm_gst_constructor_arg(concrete, 5, 2);
      term state = cm_gst_constructor_arg(concrete, 5, 3);
      term frames = cm_gst_constructor_arg(concrete, 5, 4);
      thm source_open = conv_rule(reduce_rewrite_conv(THM_LIST(
          task_shape, program_eq, cm_task_static_valid_def)),
          assume_rule(source));
      if (i == 1) {
        result = specl_rule(TERM_LIST(
            `root:cm_program`, fid, payload, state, frames),
            cm_rstart_static_valid);
        result = match_mp_rule(result, assume_rule(typed));
        result = match_mp_rule(result, conjunct1_rule(source_open));
        result = match_mp_rule(result, conjunct2_rule(source_open));
      } else if (i == 2) {
        result = specl_rule(TERM_LIST(
            `root:cm_program`, fid, payload, state, frames),
            cm_lstart_static_valid);
        result = match_mp_rule(result, conjunct1_rule(source_open));
        result = match_mp_rule(result, conjunct2_rule(source_open));
      } else if (i == 3) {
        result = specl_rule(TERM_LIST(
            `root:cm_program`, fid, payload, state, frames),
            cm_sstart_static_valid);
        result = match_mp_rule(result, conjunct1_rule(source_open));
        result = match_mp_rule(result, conjunct2_rule(source_open));
      } else {
        gnode_list frame_cases = DISJ_CASES_TAC(branch,
            ispec_rule(frames, get_theorem_by_name("list_CASES")),
            "Hframes");
        {
          thm nil_shape = assume_rule(
              goal_lasmps(frame_cases[0]->g)[labeled_term_list_index(
                goal_lasmps(frame_cases[0]->g), "Hframes")].tm);
          thm_list nil_rules = THM_LIST(
              task_shape, program_eq, nil_shape, get_cm_step_def(),
              cm_task_static_valid_def);
          if (i == 5) {
            gnode_list exit_cases = BOOL_CASES_TAC(
                frame_cases[0],
                `cm_control_kind ${payload:cm_control} == 4i`,
                "Hexit_nil");
            CONV_WITH_ASMP_TAC(
                exit_cases[0], reduce_rewrite_conv, nil_rules);
            gnode_list error_cases = BOOL_CASES_TAC(
                exit_cases[1],
                `cm_control_kind ${payload:cm_control} == 5i`,
                "Herror_nil");
            CONV_WITH_ASMP_TAC(
                error_cases[0], reduce_rewrite_conv, nil_rules);
            CONV_WITH_ASMP_TAC(
                error_cases[1], reduce_rewrite_conv, nil_rules);
          } else {
            CONV_TAC(frame_cases[0], reduce_rewrite_conv(nil_rules));
          }
        }
        {
          gnode cons_case = ASMP_EXISTS_TAC(
              frame_cases[1], "Hframes", "head");
          cons_case = ASMP_EXISTS_TAC(cons_case, "Hframes", "tail");
          thm cons_shape = assume_rule(
              goal_lasmps(cons_case->g)[labeled_term_list_index(
                goal_lasmps(cons_case->g), "Hframes")].tm);
          thm frames_open = conv_rule(reduce_rewrite_conv(THM_LIST(
              cons_shape, cm_frames_static_valid_def)), source_open);
          term head = `head:cm_frame`;
          term tail = `tail:(cm_frame)list`;
          thm not_exit = empty_theorem;
          if (i == 5) {
            term exit_kind =
                `cm_control_kind ${payload:cm_control} == 4i`;
            gnode_list exit_cases = BOOL_CASES_TAC(
                cons_case, exit_kind, "Hexit_kind");
            thm is_exit = assume_rule(
                goal_lasmps(exit_cases[0]->g)[labeled_term_list_index(
                  goal_lasmps(exit_cases[0]->g), "Hexit_kind")].tm);
            thm exit_view = apply_conversion(
                reduce_rewrite_conv(THM_LIST(
                  task_shape, program_eq, cons_shape, is_exit,
                  get_cm_step_def(), cm_task_static_valid_def)),
                goal_ccl(exit_cases[0]->g));
            ACCEPT_TAC(exit_cases[0], eqt_elim_rule(exit_view));
            cons_case = exit_cases[1];
            not_exit = assume_rule(
                goal_lasmps(cons_case->g)[labeled_term_list_index(
                  goal_lasmps(cons_case->g), "Hexit_kind")].tm);
          }
          if (i == 4) {
            thm active_success = conv_rule(rewrite_conv(THM_LIST(
                task_shape, program_eq, cons_shape)), assume_rule(succeeds));
            thm not_call = match_mp_rule(specl_rule(TERM_LIST(
                `root:cm_program`, fid, payload, state, head, tail),
                cm_v_success_top_not_call), active_success);
            result = specl_rule(TERM_LIST(
                `root:cm_program`, fid, head, payload, state, tail),
                cm_vapply_static_valid);
            result = match_mp_rule(result, assume_rule(typed));
            result = match_mp_rule(result, not_call);
          } else {
            result = specl_rule(TERM_LIST(
                `root:cm_program`, fid, head, payload, state, tail),
                cm_capply_static_valid);
          }
          result = match_mp_rule(result, conjunct1_rule(frames_open));
          result = match_mp_rule(result, conjunct2_rule(frames_open));
          thm_list step_rules = THM_LIST(
              task_shape, program_eq, cons_shape, get_cm_step_def(),
              get_theorem_by_name("NOT_CONS_NIL"),
              get_theorem_by_name("HD"), get_theorem_by_name("TL"));
          if (i == 5) vector_add(&step_rules, not_exit);
          result = conv_rule(rewrite_conv(step_rules), result);
          gnode reduced = CONV_TAC(cons_case,
              rewrite_conv(step_rules));
          ACCEPT_TAC(reduced, result);
        }
        continue;
      }
    }
    result = conv_rule(rewrite_conv(THM_LIST(
        task_shape, program_eq, get_cm_step_def())), result);
    gnode reduced = CONV_TAC(branch, rewrite_conv(THM_LIST(
        task_shape, program_eq, get_cm_step_def())));
    ACCEPT_TAC(reduced, result);
  }
  return gnode_prove(root_node);
}
PROOF thm cm_task_static_valid_step =
    cm_prove_task_static_valid_step();

PROOF static int cmc_preservation_generation_static_task_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_generation_static_task_axioms_before,
      "cmc_preservation_generation_static_task introduced an axiom");
  ENSURE_COND(vector_size(hyp(cm_task_static_valid_step)) == 0,
      "task static-validity step theorem is not closed");
  return 0;
err:
  return -1;
}

PROOF static int _cmc_preservation_generation_static_task_checks =
    cmc_preservation_generation_static_task_final_checks();
