#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_fid_apply.h"

#require "cmc_preservation_fid_start.c"
#require "cmc_preservation_source.c"

PROOF static size_t _cmc_preservation_fid_apply_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_fid_apply_pick_conjunct(
    thm source, term wanted) {
  if (alpha_compare(concl(source), wanted) == 0) return source;
  if (!is_conj(concl(source))) return empty_theorem;
  thm left = cm_fid_apply_pick_conjunct(
      conjunct1_rule(source), wanted);
  if (!IS_NULL(left)) return left;
  return cm_fid_apply_pick_conjunct(
      conjunct2_rule(source), wanted);
}

PROOF static void cm_fid_apply_accept_true(
    gnode branch, thm_list rules) {
  thm target_view = apply_conversion(
      reduce_rewrite_conv(rules), goal_ccl(branch->g));
  ACCEPT_TAC(branch, eqt_elim_rule(target_view));
}

PROOF static thm cm_prove_vapply_fid_ready(void) {
  term frame_static =
      `cm_frame_static_valid (p:cm_program) (fid:int)
        (frame:cm_frame)`;
  term frames_ready =
      `cm_frames_fid_ready (p:cm_program) (fid:int)
        ((frame:cm_frame) :: (ks:(cm_frame)list))`;
  term task =
      `CMVTask (p:cm_program) (fid:int) (incoming:cm_value)
        (st:cm_src_state)
        ((frame:cm_frame) :: (ks:(cm_frame)list))`;
  term succeeds = `cm_task_succeeds ${task:cm_task}`;
  term target =
      `cm_task_fid_ready (p:cm_program)
        (cm_vapply p (fid:int) (frame:cm_frame)
          (incoming:cm_value) (st:cm_src_state)
          (ks:(cm_frame)list))`;
  term body = imp_chain(
      TERM_LIST(frame_static, frames_ready, succeeds), target);
  gnode root = gnode_new_with_ccl(
      list_mk_forall(free_vars(body), body));
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list cases = DISJ_CASES_TAC(introduced,
      ispec_rule(`frame:cm_frame`, get_datatype_cases("cm_frame")),
      "Hframe");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode branch = cases[i];
    while (is_exists(goal_lasmps(branch->g)[
        labeled_term_list_index(
          goal_lasmps(branch->g), "Hframe")].tm)) {
      branch = ASMP_EXISTS_TAC(branch, "Hframe", NULL);
    }
    thm shape = assume_rule(goal_lasmps(branch->g)[
        labeled_term_list_index(
          goal_lasmps(branch->g), "Hframe")].tm);
    thm opened_frames = conv_rule(rewrite_conv(THM_LIST(
        cm_frames_fid_ready_def)), assume_rule(frames_ready));
    thm head_ready = conv_rule(reduce_rewrite_conv(THM_LIST(
        shape, cm_frame_fid_ready_def,
        get_datatype_distinctness("cm_frame"))),
        conjunct1_rule(opened_frames));
    thm tail_ready = conv_rule(reduce_rewrite_conv(THM_LIST(
        shape, cm_frame_parent_fid_def)),
        conjunct2_rule(opened_frames));
    if (i == 21) {
      thm static_open = conv_rule(reduce_rewrite_conv(THM_LIST(
          shape, cm_frame_static_valid_def)),
          assume_rule(frame_static));
      thm callee_low = cm_fid_apply_pick_conjunct(
          static_open, `0i <= (a0:int)`);
      thm callee_high = cm_fid_apply_pick_conjunct(static_open,
          `(a0:int) < ilength
            (cm_program_functions (p:cm_program))`);
      thm callee_ready = conj_rule(callee_low, callee_high);
      term no_more = `(a1:(cm_expr)list) == []`;
      gnode_list rest_cases = BOOL_CASES_TAC(
          branch, no_more, "Hrest");
      for (size_t j = 0; j < vector_size(rest_cases); ++j) {
        thm rest_fact = assume_rule(goal_lasmps(rest_cases[j]->g)[
            labeled_term_list_index(
              goal_lasmps(rest_cases[j]->g), "Hrest")].tm);
        if (j == 0) {
          thm result = specl_rule(TERM_LIST(
              `p:cm_program`, `fid:int`, `a0:int`,
              `REVERSE ((incoming:cm_value) :: (a2:(cm_value)list))`,
              `st:cm_src_state`, `a3:cm_type`,
              `ks:(cm_frame)list`), cm_begin_call_fid_ready);
          result = match_mp_rule(result, callee_ready);
          result = match_mp_rule(result, tail_ready);
          thm target_view = apply_conversion(
              reduce_rewrite_conv(THM_LIST(
                shape, rest_fact, get_cm_vapply_def())),
              goal_ccl(rest_cases[j]->g));
          ACCEPT_TAC(rest_cases[j],
              eq_mp_rule(sym_rule(target_view), result));
        } else {
          cm_fid_apply_accept_true(rest_cases[j], THM_LIST(
              shape, rest_fact, get_cm_vapply_def(),
              cm_task_fid_ready_cond, cm_task_fid_ready_def,
              cm_frames_fid_ready_def, cm_frame_fid_ready_def,
              cm_frame_parent_fid_def,
              get_datatype_distinctness("cm_frame"),
              head_ready, tail_ready,
              get_theorem_by_name("COND_ID")));
        }
      }
      continue;
    }
    if (i == 22) {
      thm not_done = eqf_elim_rule(apply_conversion(
          reduce_rewrite_conv(THM_LIST(get_cm_task_done_def())),
          `cm_task_done ${task:cm_task}`));
      thm next_success = match_mp_rule(match_mp_rule(
          spec_rule(task, cm_task_succeeds_step), not_done),
          assume_rule(succeeds));
      term next = `cm_step ${task:cm_task}`;
      thm no_error = match_mp_rule(specl_rule(TERM_LIST(
          `1i`, next), cm_task_succeeds_not_error), next_success);
      thm impossible = conv_rule(reduce_rewrite_conv(THM_LIST(
          shape, get_cm_step_def(), get_cm_vapply_def(),
          get_theorem_by_name("NOT_CONS_NIL"),
          get_theorem_by_name("HD"), get_theorem_by_name("TL"),
          cm_error_task_def)), no_error);
      CONTR_TAC(branch, impossible);
      continue;
    }
    cm_fid_apply_accept_true(branch, THM_LIST(
        shape, get_cm_vapply_def(), cm_task_fid_ready_cond,
        cm_task_fid_ready_def, cm_frames_fid_ready_def,
        cm_frame_fid_ready_def, cm_frame_parent_fid_def,
        get_datatype_distinctness("cm_frame"),
        head_ready, tail_ready, get_theorem_by_name("COND_ID")));
  }
  return gnode_prove(root);
}
PROOF thm cm_vapply_fid_ready =
    cm_prove_vapply_fid_ready();

PROOF static thm cm_prove_capply_fid_ready(void) {
  term frames_ready =
      `cm_frames_fid_ready (p:cm_program) (fid:int)
        ((frame:cm_frame) :: (ks:(cm_frame)list))`;
  term target =
      `cm_task_fid_ready (p:cm_program)
        (cm_capply p (fid:int) (frame:cm_frame)
          (control:cm_control) (st:cm_src_state)
          (ks:(cm_frame)list))`;
  term body = mk_imp(frames_ready, target);
  gnode root = gnode_new_with_ccl(
      list_mk_forall(free_vars(body), body));
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list cases = DISJ_CASES_TAC(introduced,
      ispec_rule(`frame:cm_frame`, get_datatype_cases("cm_frame")),
      "Hframe");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode branch = cases[i];
    while (is_exists(goal_lasmps(branch->g)[
        labeled_term_list_index(
          goal_lasmps(branch->g), "Hframe")].tm)) {
      branch = ASMP_EXISTS_TAC(branch, "Hframe", NULL);
    }
    thm shape = assume_rule(goal_lasmps(branch->g)[
        labeled_term_list_index(
          goal_lasmps(branch->g), "Hframe")].tm);
    thm opened_frames = conv_rule(rewrite_conv(THM_LIST(
        cm_frames_fid_ready_def)), assume_rule(frames_ready));
    thm head_ready = conv_rule(reduce_rewrite_conv(THM_LIST(
        shape, cm_frame_fid_ready_def,
        get_datatype_distinctness("cm_frame"))),
        conjunct1_rule(opened_frames));
    thm tail_ready = conv_rule(reduce_rewrite_conv(THM_LIST(
        shape, cm_frame_parent_fid_def)),
        conjunct2_rule(opened_frames));
    cm_fid_apply_accept_true(branch, THM_LIST(
        shape, get_cm_capply_def(), cm_task_fid_ready_cond,
        cm_task_fid_ready_def, cm_frames_fid_ready_def,
        cm_frame_fid_ready_def, cm_frame_parent_fid_def,
        get_datatype_distinctness("cm_frame"),
        head_ready, tail_ready, get_theorem_by_name("COND_ID")));
  }
  return gnode_prove(root);
}
PROOF thm cm_capply_fid_ready =
    cm_prove_capply_fid_ready();

PROOF static int cmc_preservation_fid_apply_final_checks(void) {
  ENSURE_COND(vector_size(hyp(cm_vapply_fid_ready)) == 0 &&
      vector_size(hyp(cm_capply_fid_ready)) == 0,
      "fid-apply theorem has assumptions");
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_fid_apply_axioms_before,
      "cmc_preservation_fid_apply introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_fid_apply_checks =
    cmc_preservation_fid_apply_final_checks();
