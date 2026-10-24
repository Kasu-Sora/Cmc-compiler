#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_fid_start.h"

#require "cmc_preservation_fid.c"
#require "cmc_preservation_generation_task.c"

PROOF static size_t _cmc_preservation_fid_start_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_fid_pick_conjunct(thm source, term wanted) {
  if (alpha_compare(concl(source), wanted) == 0) {
    return source;
  }
  if (is_conj(concl(source))) {
    thm left = cm_fid_pick_conjunct(conjunct1_rule(source), wanted);
    if (!IS_NULL(left)) {
      return left;
    }
    return cm_fid_pick_conjunct(conjunct2_rule(source), wanted);
  }
  return empty_theorem;
}

PROOF static void cm_fid_accept_true(
    gnode branch, thm_list rules) {
  thm target_view = apply_conversion(
      reduce_rewrite_conv(rules), goal_ccl(branch->g));
  ACCEPT_TAC(branch, eqt_elim_rule(target_view));
}

PROOF static thm cm_prove_task_fid_ready_cond(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (condition:bool)
         (yes:cm_task) (no:cm_task).
       cm_task_fid_ready p (if condition then yes else no) <=>
       (if condition
        then cm_task_fid_ready p yes
        else cm_task_fid_ready p no)`);
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list cases = BOOL_CASES_TAC(
      introduced, `condition:bool`, "Hcondition");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    thm condition = assume_rule(goal_lasmps(cases[i]->g)[
        labeled_term_list_index(
          goal_lasmps(cases[i]->g), "Hcondition")].tm);
    cm_fid_accept_true(cases[i], THM_LIST(condition));
  }
  return gnode_prove(root);
}
PROOF thm cm_task_fid_ready_cond =
    cm_prove_task_fid_ready_cond();

PROOF static thm cm_prove_frames_fid_ready_cond(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (condition:bool)
         (yes:(cm_frame)list) (no:(cm_frame)list).
       cm_frames_fid_ready p fid
         (if condition then yes else no) <=>
       (if condition
        then cm_frames_fid_ready p fid yes
        else cm_frames_fid_ready p fid no)`);
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list cases = BOOL_CASES_TAC(
      introduced, `condition:bool`, "Hcondition");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    thm condition = assume_rule(goal_lasmps(cases[i]->g)[
        labeled_term_list_index(
          goal_lasmps(cases[i]->g), "Hcondition")].tm);
    cm_fid_accept_true(cases[i], THM_LIST(condition));
  }
  return gnode_prove(root);
}
PROOF static thm cm_frames_fid_ready_cond =
    cm_prove_frames_fid_ready_cond();

PROOF static thm cm_prove_begin_call_fid_ready(void) {
  term callee_ready =
      `0i <= (callee:int) &&
       callee < ilength (cm_program_functions (p:cm_program))`;
  term frames_ready =
      `cm_frames_fid_ready (p:cm_program) (caller:int)
        (ks:(cm_frame)list)`;
  term target =
      `cm_task_fid_ready (p:cm_program)
        (cm_begin_call p (caller:int) (callee:int)
          (values:(cm_value)list) (st:cm_src_state) (ret:cm_type)
          (ks:(cm_frame)list))`;
  term body = imp_chain(TERM_LIST(callee_ready, frames_ready), target);
  gnode root = gnode_new_with_ccl(
      list_mk_forall(free_vars(body), body));
  gnode introduced = AUTO_INTROS_TAC(root);
  term condition =
      `cm_call_ok (p:cm_program) (callee:int)
         (values:(cm_value)list) (st:cm_src_state) &&
       cm_call_depth (ks:(cm_frame)list) < 65536i`;
  gnode_list cases = BOOL_CASES_TAC(
      introduced, condition, "Hcondition");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    thm condition_fact = assume_rule(goal_lasmps(cases[i]->g)[
        labeled_term_list_index(
          goal_lasmps(cases[i]->g), "Hcondition")].tm);
    cm_fid_accept_true(cases[i], THM_LIST(
        condition_fact, get_cm_begin_call_def(), cm_task_fid_ready_def,
        cm_frames_fid_ready_def, cm_frame_fid_ready_def,
        cm_frame_parent_fid_def,
        get_datatype_distinctness("cm_frame"),
        assume_rule(callee_ready), assume_rule(frames_ready)));
  }
  return gnode_prove(root);
}
PROOF thm cm_begin_call_fid_ready =
    cm_prove_begin_call_fid_ready();

PROOF static thm cm_prove_rstart_fid_ready(void) {
  term static_ready =
      `cm_expr_static_valid (p:cm_program)
        (inth (fid:int) (cm_program_functions p)) (expr:cm_expr)`;
  term current_ready =
      `0i <= (fid:int) &&
       fid < ilength (cm_program_functions (p:cm_program))`;
  term frames_ready =
      `cm_frames_fid_ready (p:cm_program) (fid:int)
        (ks:(cm_frame)list)`;
  term target =
      `cm_task_fid_ready (p:cm_program)
        (cm_rstart p (fid:int) (expr:cm_expr)
          (st:cm_src_state) (ks:(cm_frame)list))`;
  term body = imp_chain(
      TERM_LIST(static_ready, current_ready, frames_ready), target);
  gnode root = gnode_new_with_ccl(
      list_mk_forall(free_vars(body), body));
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list cases = DISJ_CASES_TAC(introduced,
      ispec_rule(`expr:cm_expr`, get_cm_expr_cases()), "Hexpr");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode branch = cases[i];
    while (is_exists(goal_lasmps(branch->g)[
        labeled_term_list_index(
          goal_lasmps(branch->g), "Hexpr")].tm)) {
      branch = ASMP_EXISTS_TAC(branch, "Hexpr", NULL);
    }
    thm shape = assume_rule(goal_lasmps(branch->g)[
        labeled_term_list_index(
          goal_lasmps(branch->g), "Hexpr")].tm);
    if (i == 8) {
      thm static_open = conv_rule(reduce_rewrite_conv(THM_LIST(
          shape, cm_expr_static_valid_def)), assume_rule(static_ready));
      thm callee_low = cm_fid_pick_conjunct(
          static_open, `0i <= (a0:int)`);
      thm callee_high = cm_fid_pick_conjunct(static_open,
          `(a0:int) < ilength
            (cm_program_functions (p:cm_program))`);
      thm callee_ready = conj_rule(callee_low, callee_high);
      gnode_list arg_cases = DISJ_CASES_TAC(branch,
          ispec_rule(`a1:(cm_expr)list`,
            get_datatype_cases("list")), "Hargs");
      for (size_t j = 0; j < vector_size(arg_cases); ++j) {
        gnode arg_branch = arg_cases[j];
        while (is_exists(goal_lasmps(arg_branch->g)[
            labeled_term_list_index(
              goal_lasmps(arg_branch->g), "Hargs")].tm)) {
          arg_branch = ASMP_EXISTS_TAC(arg_branch, "Hargs", NULL);
        }
        thm arg_shape = assume_rule(goal_lasmps(arg_branch->g)[
            labeled_term_list_index(
              goal_lasmps(arg_branch->g), "Hargs")].tm);
        if (j == 0) {
          thm result = specl_rule(TERM_LIST(
              `p:cm_program`, `fid:int`, `a0:int`,
              `[]:(cm_value)list`, `st:cm_src_state`, `a2:cm_type`,
              `ks:(cm_frame)list`), cm_begin_call_fid_ready);
          result = match_mp_rule(result, callee_ready);
          result = match_mp_rule(result, assume_rule(frames_ready));
          thm target_view = apply_conversion(
              reduce_rewrite_conv(THM_LIST(
                shape, arg_shape, get_cm_rstart_def())),
              goal_ccl(arg_branch->g));
          ACCEPT_TAC(arg_branch,
              eq_mp_rule(sym_rule(target_view), result));
        } else {
          cm_fid_accept_true(arg_branch, THM_LIST(
              shape, arg_shape, get_cm_rstart_def(),
              cm_task_fid_ready_cond, cm_frames_fid_ready_cond,
              cm_task_fid_ready_def,
              cm_frames_fid_ready_def, cm_frame_fid_ready_def,
              cm_frame_parent_fid_def,
              get_datatype_distinctness("cm_frame"),
              assume_rule(current_ready), assume_rule(frames_ready),
              get_theorem_by_name("COND_ID")));
        }
      }
      continue;
    }
    cm_fid_accept_true(branch, THM_LIST(
        shape, get_cm_rstart_def(), cm_task_fid_ready_cond,
        cm_frames_fid_ready_cond,
        cm_task_fid_ready_def, cm_frames_fid_ready_def,
        cm_frame_fid_ready_def, cm_frame_parent_fid_def,
        get_datatype_distinctness("cm_frame"),
        assume_rule(current_ready), assume_rule(frames_ready),
        get_theorem_by_name("COND_ID")));
  }
  return gnode_prove(root);
}
PROOF thm cm_rstart_fid_ready =
    cm_prove_rstart_fid_ready();

PROOF static thm cm_prove_lstart_fid_ready(void) {
  term current_ready =
      `0i <= (fid:int) &&
       fid < ilength (cm_program_functions (p:cm_program))`;
  term frames_ready =
      `cm_frames_fid_ready (p:cm_program) (fid:int)
        (ks:(cm_frame)list)`;
  term target =
      `cm_task_fid_ready (p:cm_program)
        (cm_lstart p (fid:int) (expr:cm_expr)
          (st:cm_src_state) (ks:(cm_frame)list))`;
  term body = imp_chain(TERM_LIST(current_ready, frames_ready), target);
  gnode root = gnode_new_with_ccl(
      list_mk_forall(free_vars(body), body));
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list cases = DISJ_CASES_TAC(introduced,
      ispec_rule(`expr:cm_expr`, get_cm_expr_cases()), "Hexpr");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode branch = cases[i];
    while (is_exists(goal_lasmps(branch->g)[
        labeled_term_list_index(
          goal_lasmps(branch->g), "Hexpr")].tm)) {
      branch = ASMP_EXISTS_TAC(branch, "Hexpr", NULL);
    }
    thm shape = assume_rule(goal_lasmps(branch->g)[
        labeled_term_list_index(
          goal_lasmps(branch->g), "Hexpr")].tm);
    cm_fid_accept_true(branch, THM_LIST(
        shape, get_cm_lstart_def(), cm_task_fid_ready_cond,
        cm_frames_fid_ready_cond,
        cm_task_fid_ready_def, cm_frames_fid_ready_def,
        cm_frame_fid_ready_def, cm_frame_parent_fid_def,
        get_datatype_distinctness("cm_frame"),
        assume_rule(current_ready), assume_rule(frames_ready),
        get_theorem_by_name("COND_ID")));
  }
  return gnode_prove(root);
}
PROOF thm cm_lstart_fid_ready =
    cm_prove_lstart_fid_ready();

PROOF static thm cm_prove_sstart_fid_ready(void) {
  term current_ready =
      `0i <= (fid:int) &&
       fid < ilength (cm_program_functions (p:cm_program))`;
  term frames_ready =
      `cm_frames_fid_ready (p:cm_program) (fid:int)
        (ks:(cm_frame)list)`;
  term target =
      `cm_task_fid_ready (p:cm_program)
        (cm_sstart p (fid:int) (stmt:cm_stmt)
          (st:cm_src_state) (ks:(cm_frame)list))`;
  term body = imp_chain(TERM_LIST(current_ready, frames_ready), target);
  gnode root = gnode_new_with_ccl(
      list_mk_forall(free_vars(body), body));
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list cases = DISJ_CASES_TAC(introduced,
      ispec_rule(`stmt:cm_stmt`, get_cm_stmt_cases()), "Hstmt");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode branch = cases[i];
    while (is_exists(goal_lasmps(branch->g)[
        labeled_term_list_index(
          goal_lasmps(branch->g), "Hstmt")].tm)) {
      branch = ASMP_EXISTS_TAC(branch, "Hstmt", NULL);
    }
    thm shape = assume_rule(goal_lasmps(branch->g)[
        labeled_term_list_index(
          goal_lasmps(branch->g), "Hstmt")].tm);
    cm_fid_accept_true(branch, THM_LIST(
        shape, get_cm_sstart_def(), cm_task_fid_ready_cond,
        cm_frames_fid_ready_cond,
        cm_task_fid_ready_def, cm_frames_fid_ready_def,
        cm_frame_fid_ready_def, cm_frame_parent_fid_def,
        get_datatype_distinctness("cm_frame"),
        assume_rule(current_ready), assume_rule(frames_ready),
        get_theorem_by_name("COND_ID")));
  }
  return gnode_prove(root);
}
PROOF thm cm_sstart_fid_ready =
    cm_prove_sstart_fid_ready();

PROOF static int cmc_preservation_fid_start_final_checks(void) {
  ENSURE_COND(vector_size(hyp(cm_task_fid_ready_cond)) == 0 &&
      vector_size(hyp(cm_begin_call_fid_ready)) == 0 &&
      vector_size(hyp(cm_rstart_fid_ready)) == 0 &&
      vector_size(hyp(cm_lstart_fid_ready)) == 0 &&
      vector_size(hyp(cm_sstart_fid_ready)) == 0,
      "fid-start theorem has assumptions");
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_fid_start_axioms_before,
      "cmc_preservation_fid_start introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_fid_start_checks =
    cmc_preservation_fid_start_final_checks();
