#include "proof/proof.h"
#include "userlib/proof.h"
#include "cmc_preservation_generation_static_start.h"
#include "cmc_preservation_generation_syntax.h"

#require "cmc_preservation_generation_syntax.c"

PROOF static size_t _cmc_preservation_generation_static_start_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_prove_task_static_valid_cond(void) {
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
PROOF static thm cm_task_static_valid_cond =
    cm_prove_task_static_valid_cond();

PROOF static thm cm_prove_frames_static_valid_cond(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (condition:bool)
         (yes:(cm_frame)list) (no:(cm_frame)list).
         cm_frames_static_valid p fid
           (if condition then yes else no) <=>
         (if condition
          then cm_frames_static_valid p fid yes
          else cm_frames_static_valid p fid no)`);
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list cases = BOOL_CASES_TAC(
      introduced, `condition:bool`, "Hcondition");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    CONV_WITH_ASMP_TAC(cases[i], reduce_rewrite_conv, THM_LIST());
  }
  return gnode_prove(root);
}
PROOF static thm cm_frames_static_valid_cond =
    cm_prove_frames_static_valid_cond();

PROOF static thm cm_prove_begin_call_static_valid(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (caller:int) (fid:int)
         (values:(cm_value)list) (st:cm_src_state) (ret:cm_type)
         (ks:(cm_frame)list).
         cm_typed_program p ==>
         0i <= fid ==>
         fid < ilength (cm_program_functions p) ==>
         cm_frames_static_valid p caller ks ==>
         cm_task_static_valid
           (cm_begin_call p caller fid values st ret ks)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm body_static = match_mp_rule(match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(`p:cm_program`, `fid:int`),
        cm_typed_function_body_static_valid),
      assume_rule(`cm_typed_program (p:cm_program)`)),
      assume_rule(`0i <= (fid:int)`)),
      assume_rule(`(fid:int) < ilength
        (cm_program_functions (p:cm_program))`));
  thm frames_static = assume_rule(
      `cm_frames_static_valid (p:cm_program) (caller:int)
        (ks:(cm_frame)list)`);
  gnode reduced = CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
      get_cm_begin_call_def(), cm_task_static_valid_cond,
      cm_task_static_valid_def, cm_frames_static_valid_def,
      cm_frame_static_valid_def, cm_frame_parent_fid_def,
      body_static, frames_static)));
  if (IS_NULL(reduced->solved)) {
    ACCEPT_TAC(reduced, taut_rule(goal_ccl(reduced->g)));
  }
  return gnode_prove(root);
}
PROOF thm cm_begin_call_static_valid =
    cm_prove_begin_call_static_valid();

PROOF static term cm_gss_app_arg_from_right(
    term application, size_t offset) {
  for (size_t i = 0; i < offset; ++i) {
    application = dest_comb(application).tm1;
  }
  return dest_comb(application).tm2;
}

PROOF static term cm_gss_constructor_arg(
    term constructor, size_t arity, size_t index) {
  return cm_gss_app_arg_from_right(
      constructor, arity - index - 1);
}

PROOF static thm cm_prove_args_start_static_valid(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (caller:int) (args:(cm_expr)list)
         (st:cm_src_state) (ks:(cm_frame)list) (callee:int)
         (ret:cm_type).
         cm_typed_program p ==>
         0i <= callee ==>
         callee < ilength (cm_program_functions p) ==>
         cm_args_static_valid p
           (inth caller (cm_program_functions p)) args ==>
         cm_frames_static_valid p caller ks ==>
         cm_task_static_valid
           (cm_args_start p caller args st ks callee ret)`);
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list cases = DISJ_CASES_TAC(introduced,
      ispec_rule(`args:(cm_expr)list`,
        get_theorem_by_name("list_CASES")), "Hargs");
  {
    thm shape = assume_rule(
        goal_lasmps(cases[0]->g)[labeled_term_list_index(
          goal_lasmps(cases[0]->g), "Hargs")].tm);
    thm result = specl_rule(TERM_LIST(
        `p:cm_program`, `caller:int`, `callee:int`,
        `[]:(cm_value)list`, `st:cm_src_state`, `ret:cm_type`,
        `ks:(cm_frame)list`), cm_begin_call_static_valid);
    result = match_mp_rule(result,
        assume_rule(`cm_typed_program (p:cm_program)`));
    result = match_mp_rule(result, assume_rule(`0i <= (callee:int)`));
    result = match_mp_rule(result, assume_rule(
        `(callee:int) < ilength
          (cm_program_functions (p:cm_program))`));
    result = match_mp_rule(result, assume_rule(
        `cm_frames_static_valid (p:cm_program) (caller:int)
          (ks:(cm_frame)list)`));
    result = conv_rule(rewrite_conv(THM_LIST(
        shape, get_cm_rstart_def())), result);
    gnode reduced = CONV_TAC(cases[0], rewrite_conv(THM_LIST(
        shape, get_cm_rstart_def())));
    ACCEPT_TAC(reduced, result);
  }
  {
    gnode cons_case = ASMP_EXISTS_TAC(cases[1], "Hargs", "head");
    cons_case = ASMP_EXISTS_TAC(cons_case, "Hargs", "tail");
    thm shape = assume_rule(
        goal_lasmps(cons_case->g)[labeled_term_list_index(
          goal_lasmps(cons_case->g), "Hargs")].tm);
    thm args_static = conv_rule(reduce_rewrite_conv(THM_LIST(
        shape, cm_args_static_valid_def)), assume_rule(
          `cm_args_static_valid (p:cm_program)
            (inth (caller:int) (cm_program_functions p))
            (args:(cm_expr)list)`));
    thm frames_static = assume_rule(
        `cm_frames_static_valid (p:cm_program) (caller:int)
          (ks:(cm_frame)list)`);
    gnode reduced = CONV_TAC(cons_case, reduce_rewrite_conv(THM_LIST(
        shape, get_cm_rstart_def(), cm_task_static_valid_def,
        cm_frames_static_valid_def, cm_frame_static_valid_def,
        cm_frame_parent_fid_def, args_static, frames_static,
        assume_rule(`0i <= (callee:int)`),
        assume_rule(`(callee:int) < ilength
          (cm_program_functions (p:cm_program))`))));
    if (IS_NULL(reduced->solved)) {
      ACCEPT_TAC(reduced, taut_rule(goal_ccl(reduced->g)));
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_args_start_static_valid =
    cm_prove_args_start_static_valid();

PROOF static thm cm_prove_rstart_static_valid(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (expr:cm_expr)
         (st:cm_src_state) (ks:(cm_frame)list).
         cm_typed_program p ==>
         cm_expr_static_valid p
           (inth fid (cm_program_functions p)) expr ==>
         cm_frames_static_valid p fid ks ==>
         cm_task_static_valid (cm_rstart p fid expr st ks)`);
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list cases = DISJ_CASES_TAC(introduced,
      ispec_rule(`expr:cm_expr`, get_cm_expr_cases()), "Hex");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode branch = cases[i];
    while (true) {
      labeled_term_list assumptions = goal_lasmps(branch->g);
      int index = labeled_term_list_index(assumptions, "Hex");
      if (!is_exists(assumptions[index].tm)) break;
      branch = ASMP_EXISTS_TAC(branch, "Hex", NULL);
    }
    thm shape = assume_rule(
        goal_lasmps(branch->g)[labeled_term_list_index(
          goal_lasmps(branch->g), "Hex")].tm);
    if (i == 8) {
      term concrete = rhs_of(shape);
      term callee = cm_gss_constructor_arg(concrete, 3, 0);
      term args = cm_gss_constructor_arg(concrete, 3, 1);
      thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
          shape, cm_expr_static_valid_def)), assume_rule(
            `cm_expr_static_valid (p:cm_program)
              (inth (fid:int) (cm_program_functions p))
              (expr:cm_expr)`));
      thm result = specl_rule(TERM_LIST(
          `p:cm_program`, `fid:int`, args, `st:cm_src_state`,
          `ks:(cm_frame)list`, callee,
          cm_gss_constructor_arg(concrete, 3, 2)),
          cm_args_start_static_valid);
      result = match_mp_rule(result,
          assume_rule(`cm_typed_program (p:cm_program)`));
      result = match_mp_rule(result, conjunct1_rule(opened));
      result = match_mp_rule(result,
          conjunct1_rule(conjunct2_rule(opened)));
      result = match_mp_rule(result,
          conjunct2_rule(conjunct2_rule(opened)));
      result = match_mp_rule(result, assume_rule(
          `cm_frames_static_valid (p:cm_program) (fid:int)
            (ks:(cm_frame)list)`));
      result = conv_rule(rewrite_conv(THM_LIST(
          shape, get_cm_rstart_def())), result);
      gnode reduced = CONV_TAC(branch, rewrite_conv(THM_LIST(
          shape, get_cm_rstart_def())));
      ACCEPT_TAC(reduced, result);
      continue;
    }
    thm expr_static = conv_rule(reduce_rewrite_conv(THM_LIST(
        shape, cm_expr_static_valid_def)), assume_rule(
          `cm_expr_static_valid (p:cm_program)
            (inth (fid:int) (cm_program_functions p))
            (expr:cm_expr)`));
    thm frames_static = assume_rule(
        `cm_frames_static_valid (p:cm_program) (fid:int)
          (ks:(cm_frame)list)`);
    gnode reduced = CONV_TAC(branch, reduce_rewrite_conv(THM_LIST(
        shape, get_cm_rstart_def(), cm_task_static_valid_cond,
        cm_frames_static_valid_cond, cm_task_static_valid_def,
        cm_frames_static_valid_def,
        cm_frame_static_valid_def, cm_frame_parent_fid_def,
        cm_expr_static_valid_def,
        expr_static, frames_static)));
    if (IS_NULL(reduced->solved)) {
      ACCEPT_TAC(reduced, taut_rule(goal_ccl(reduced->g)));
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_rstart_static_valid =
    cm_prove_rstart_static_valid();

PROOF static thm cm_prove_lstart_static_valid(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (expr:cm_expr)
         (st:cm_src_state) (ks:(cm_frame)list).
         cm_expr_static_valid p
           (inth fid (cm_program_functions p)) expr ==>
         cm_frames_static_valid p fid ks ==>
         cm_task_static_valid (cm_lstart p fid expr st ks)`);
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list cases = DISJ_CASES_TAC(introduced,
      ispec_rule(`expr:cm_expr`, get_cm_expr_cases()), "Hex");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode branch = cases[i];
    while (true) {
      labeled_term_list assumptions = goal_lasmps(branch->g);
      int index = labeled_term_list_index(assumptions, "Hex");
      if (!is_exists(assumptions[index].tm)) break;
      branch = ASMP_EXISTS_TAC(branch, "Hex", NULL);
    }
    thm shape = assume_rule(
        goal_lasmps(branch->g)[labeled_term_list_index(
          goal_lasmps(branch->g), "Hex")].tm);
    thm expr_static = conv_rule(reduce_rewrite_conv(THM_LIST(
        shape, cm_expr_static_valid_def)), assume_rule(
          `cm_expr_static_valid (p:cm_program)
            (inth (fid:int) (cm_program_functions p))
            (expr:cm_expr)`));
    thm frames_static = assume_rule(
        `cm_frames_static_valid (p:cm_program) (fid:int)
          (ks:(cm_frame)list)`);
    gnode reduced = CONV_TAC(branch, reduce_rewrite_conv(THM_LIST(
        shape, get_cm_lstart_def(), cm_task_static_valid_cond,
        cm_task_static_valid_def, cm_frames_static_valid_def,
        cm_frame_static_valid_def, cm_frame_parent_fid_def,
        cm_expr_static_valid_def,
        expr_static, frames_static)));
    if (IS_NULL(reduced->solved)) {
      ACCEPT_TAC(reduced, taut_rule(goal_ccl(reduced->g)));
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_lstart_static_valid =
    cm_prove_lstart_static_valid();

PROOF static thm cm_prove_sstart_static_valid(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (stmt:cm_stmt)
         (st:cm_src_state) (ks:(cm_frame)list).
         cm_stmt_static_valid p
           (inth fid (cm_program_functions p)) stmt ==>
         cm_frames_static_valid p fid ks ==>
         cm_task_static_valid (cm_sstart p fid stmt st ks)`);
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list cases = DISJ_CASES_TAC(introduced,
      ispec_rule(`stmt:cm_stmt`, get_cm_stmt_cases()), "Hstmt");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode branch = cases[i];
    while (true) {
      labeled_term_list assumptions = goal_lasmps(branch->g);
      int index = labeled_term_list_index(assumptions, "Hstmt");
      if (!is_exists(assumptions[index].tm)) break;
      branch = ASMP_EXISTS_TAC(branch, "Hstmt", NULL);
    }
    thm shape = assume_rule(
        goal_lasmps(branch->g)[labeled_term_list_index(
          goal_lasmps(branch->g), "Hstmt")].tm);
    thm stmt_static = conv_rule(reduce_rewrite_conv(THM_LIST(
        shape, cm_stmt_static_valid_def)), assume_rule(
          `cm_stmt_static_valid (p:cm_program)
            (inth (fid:int) (cm_program_functions p))
            (stmt:cm_stmt)`));
    thm frames_static = assume_rule(
        `cm_frames_static_valid (p:cm_program) (fid:int)
          (ks:(cm_frame)list)`);
    gnode reduced = CONV_TAC(branch, reduce_rewrite_conv(THM_LIST(
        shape, get_cm_sstart_def(), cm_task_static_valid_cond,
        cm_task_static_valid_def, cm_frames_static_valid_def,
        cm_frame_static_valid_def, cm_frame_parent_fid_def,
        cm_expr_static_valid_def,
        cm_stmt_static_valid_def, stmt_static, frames_static)));
    if (IS_NULL(reduced->solved)) {
      ACCEPT_TAC(reduced, taut_rule(goal_ccl(reduced->g)));
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_sstart_static_valid =
    cm_prove_sstart_static_valid();

PROOF static int cmc_preservation_generation_static_start_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_generation_static_start_axioms_before,
      "cmc_preservation_generation_static_start introduced an axiom");
  ENSURE_COND(vector_size(hyp(cm_sstart_static_valid)) == 0,
      "static-start theorem is not closed");
  return 0;
err:
  return -1;
}

PROOF static int _cmc_preservation_generation_static_start_checks =
    cmc_preservation_generation_static_start_final_checks();
