#include "proof/proof.h"
#include "userlib/proof.h"
#include "cmc_preservation_generation_static_apply.h"
#include "cmc_preservation_generation_static_start.h"
#include "cmc_preservation_generation_syntax.h"

#require "cmc_preservation_generation_static_start.c"

PROOF static size_t _cmc_preservation_generation_static_apply_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_prove_static_apply_cond(void) {
  gnode root = gnode_new_with_ccl(
      `!(condition:bool) (yes:cm_task) (no:cm_task).
         cm_task_static_valid (if condition then yes else no) <=>
         (if condition
          then cm_task_static_valid yes
          else cm_task_static_valid no)`);
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list cases = BOOL_CASES_TAC(
      introduced, `condition:bool`, "Hcondition");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    CONV_WITH_ASMP_TAC(cases[i], reduce_rewrite_conv, THM_LIST());
  }
  return gnode_prove(root);
}
PROOF static thm cm_static_apply_cond =
    cm_prove_static_apply_cond();

PROOF static term cm_gsa_app_arg_from_right(
    term application, size_t offset) {
  for (size_t i = 0; i < offset; ++i) {
    application = dest_comb(application).tm1;
  }
  return dest_comb(application).tm2;
}

PROOF static term cm_gsa_constructor_arg(
    term constructor, size_t arity, size_t index) {
  return cm_gsa_app_arg_from_right(
      constructor, arity - index - 1);
}

PROOF static thm cm_prove_vapply_static_valid(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (frame:cm_frame)
         (v:cm_value) (st:cm_src_state) (ks:(cm_frame)list).
         cm_typed_program p ==>
         ~(cm_is_call_frame frame) ==>
         cm_frame_static_valid p fid frame ==>
         cm_frames_static_valid p
           (cm_frame_parent_fid frame fid) ks ==>
         cm_task_static_valid
           (cm_vapply p fid frame v st ks)`);
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list cases = DISJ_CASES_TAC(introduced,
      ispec_rule(`frame:cm_frame`, get_datatype_cases("cm_frame")),
      "Hframe");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode branch = cases[i];
    while (true) {
      labeled_term_list assumptions = goal_lasmps(branch->g);
      int index = labeled_term_list_index(assumptions, "Hframe");
      if (!is_exists(assumptions[index].tm)) break;
      branch = ASMP_EXISTS_TAC(branch, "Hframe", NULL);
    }
    thm shape = assume_rule(
        goal_lasmps(branch->g)[labeled_term_list_index(
          goal_lasmps(branch->g), "Hframe")].tm);
    thm frame_static = conv_rule(reduce_rewrite_conv(THM_LIST(
        shape, cm_frame_static_valid_def)), assume_rule(
          `cm_frame_static_valid (p:cm_program) (fid:int)
            (frame:cm_frame)`));
    thm frames_static = conv_rule(reduce_rewrite_conv(THM_LIST(
        shape, cm_frame_parent_fid_def)), assume_rule(
          `cm_frames_static_valid (p:cm_program)
            (cm_frame_parent_fid (frame:cm_frame) (fid:int))
            (ks:(cm_frame)list)`));
    if (i == 21) {
      term concrete = rhs_of(shape);
      term callee = cm_gsa_constructor_arg(concrete, 4, 0);
      term rest = cm_gsa_constructor_arg(concrete, 4, 1);
      term values = cm_gsa_constructor_arg(concrete, 4, 2);
      term ret = cm_gsa_constructor_arg(concrete, 4, 3);
      gnode_list rest_cases = DISJ_CASES_TAC(branch,
          ispec_rule(rest, get_theorem_by_name("list_CASES")),
          "Hrest");
      {
        thm rest_shape = assume_rule(
            goal_lasmps(rest_cases[0]->g)[labeled_term_list_index(
              goal_lasmps(rest_cases[0]->g), "Hrest")].tm);
        thm result = specl_rule(TERM_LIST(
            `p:cm_program`, `fid:int`, callee,
            `REVERSE ((v:cm_value) :: ${values:(cm_value)list})`,
            `st:cm_src_state`, ret, `ks:(cm_frame)list`),
            cm_begin_call_static_valid);
        result = match_mp_rule(result,
            assume_rule(`cm_typed_program (p:cm_program)`));
        result = match_mp_rule(result, conjunct1_rule(frame_static));
        result = match_mp_rule(result,
            conjunct1_rule(conjunct2_rule(frame_static)));
        result = match_mp_rule(result, frames_static);
        result = conv_rule(rewrite_conv(THM_LIST(
            shape, rest_shape, get_cm_vapply_def())), result);
        gnode reduced = CONV_TAC(rest_cases[0], rewrite_conv(THM_LIST(
            shape, rest_shape, get_cm_vapply_def())));
        ACCEPT_TAC(reduced, result);
      }
      {
        gnode cons_case = ASMP_EXISTS_TAC(
            rest_cases[1], "Hrest", "head");
        cons_case = ASMP_EXISTS_TAC(cons_case, "Hrest", "tail");
        thm rest_shape = assume_rule(
            goal_lasmps(cons_case->g)[labeled_term_list_index(
              goal_lasmps(cons_case->g), "Hrest")].tm);
        thm concrete_static = conv_rule(reduce_rewrite_conv(THM_LIST(
            rest_shape, cm_args_static_valid_def)), frame_static);
        gnode reduced = CONV_TAC(cons_case,
            reduce_rewrite_conv(THM_LIST(
              shape, rest_shape, get_cm_vapply_def(),
              cm_static_apply_cond, get_cm_is_call_frame_def(),
              cm_task_static_valid_def,
              cm_frames_static_valid_def, cm_frame_static_valid_def,
              cm_frame_parent_fid_def, cm_expr_static_valid_def,
              cm_args_static_valid_def,
              get_theorem_by_name("NOT_CONS_NIL"),
              get_theorem_by_name("HD"), get_theorem_by_name("TL"),
              concrete_static, frames_static,
              conjunct1_rule(frame_static),
              conjunct1_rule(conjunct2_rule(frame_static)))));
        if (IS_NULL(reduced->solved)) {
          ACCEPT_TAC(reduced, taut_rule(goal_ccl(reduced->g)));
        }
      }
      continue;
    }
    if (i == 22) {
      thm impossible = conv_rule(reduce_rewrite_conv(THM_LIST(
          shape, get_cm_is_call_frame_def())), assume_rule(
            `~(cm_is_call_frame (frame:cm_frame))`));
      CONTR_TAC(branch, impossible);
      continue;
    }
    gnode reduced = CONV_TAC(branch,
        reduce_rewrite_conv(THM_LIST(
          shape, get_cm_vapply_def(), cm_static_apply_cond,
          get_cm_is_call_frame_def(), cm_task_static_valid_def,
          cm_frames_static_valid_def,
          cm_frame_static_valid_def, cm_frame_parent_fid_def,
          cm_expr_static_valid_def, cm_stmt_static_valid_def,
          assume_rule(`~(cm_is_call_frame (frame:cm_frame))`),
          frame_static, frames_static)));
    if (IS_NULL(reduced->solved)) {
      ACCEPT_TAC(reduced, taut_rule(goal_ccl(reduced->g)));
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_vapply_static_valid =
    cm_prove_vapply_static_valid();

PROOF static thm cm_prove_capply_static_valid(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (frame:cm_frame)
         (ctl:cm_control) (st:cm_src_state) (ks:(cm_frame)list).
         cm_frame_static_valid p fid frame ==>
         cm_frames_static_valid p
           (cm_frame_parent_fid frame fid) ks ==>
         cm_task_static_valid
           (cm_capply p fid frame ctl st ks)`);
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list cases = DISJ_CASES_TAC(introduced,
      ispec_rule(`frame:cm_frame`, get_datatype_cases("cm_frame")),
      "Hframe");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode branch = cases[i];
    while (true) {
      labeled_term_list assumptions = goal_lasmps(branch->g);
      int index = labeled_term_list_index(assumptions, "Hframe");
      if (!is_exists(assumptions[index].tm)) break;
      branch = ASMP_EXISTS_TAC(branch, "Hframe", NULL);
    }
    thm shape = assume_rule(
        goal_lasmps(branch->g)[labeled_term_list_index(
          goal_lasmps(branch->g), "Hframe")].tm);
    thm frame_static = conv_rule(reduce_rewrite_conv(THM_LIST(
        shape, cm_frame_static_valid_def)), assume_rule(
          `cm_frame_static_valid (p:cm_program) (fid:int)
            (frame:cm_frame)`));
    thm frames_static = conv_rule(reduce_rewrite_conv(THM_LIST(
        shape, cm_frame_parent_fid_def)), assume_rule(
          `cm_frames_static_valid (p:cm_program)
            (cm_frame_parent_fid (frame:cm_frame) (fid:int))
            (ks:(cm_frame)list)`));
    gnode reduced = CONV_TAC(branch,
        reduce_rewrite_conv(THM_LIST(
          shape, get_cm_capply_def(), cm_static_apply_cond,
          cm_task_static_valid_def, cm_frames_static_valid_def,
          cm_frame_static_valid_def, cm_frame_parent_fid_def,
          cm_expr_static_valid_def, cm_stmt_static_valid_def,
          frame_static, frames_static)));
    if (IS_NULL(reduced->solved)) {
      ACCEPT_TAC(reduced, taut_rule(goal_ccl(reduced->g)));
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_capply_static_valid =
    cm_prove_capply_static_valid();

PROOF static int cmc_preservation_generation_static_apply_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_generation_static_apply_axioms_before,
      "cmc_preservation_generation_static_apply introduced an axiom");
  ENSURE_COND(vector_size(hyp(cm_capply_static_valid)) == 0,
      "static-apply theorem is not closed");
  return 0;
err:
  return -1;
}

PROOF static int _cmc_preservation_generation_static_apply_checks =
    cmc_preservation_generation_static_apply_final_checks();
