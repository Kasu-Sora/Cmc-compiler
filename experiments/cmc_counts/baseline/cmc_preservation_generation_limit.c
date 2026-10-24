#include "proof/proof.h"
#include "userlib/proof.h"
#include "cmc_preservation_generation_limit.h"
#include "cmc_preservation_generation_step_start.h"
#include "cmc_preservation_generation_task.h"
#include "cmc_preservation_source.h"

#require "cmc_preservation_generation_step_start.c"
#require "cmc_preservation_source.c"

PROOF static size_t _cmc_preservation_generation_limit_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_prove_limit_task_cond(void) {
  gnode root = gnode_new_with_ccl(
      `!(condition:bool) (yes:cm_task) (no:cm_task).
         cm_task_generation_limit (if condition then yes else no) ==
         (if condition then cm_task_generation_limit yes
          else cm_task_generation_limit no)`);
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list cases = BOOL_CASES_TAC(
      introduced, `condition:bool`, "Hcondition");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    CONV_WITH_ASMP_TAC(cases[i], reduce_rewrite_conv, THM_LIST());
  }
  return gnode_prove(root);
}
PROOF static thm cm_limit_task_cond = cm_prove_limit_task_cond();
PROOF static thm cm_prove_limit_task_le_cond(void) {
  gnode root = gnode_new_with_ccl(
      `!(condition:bool) (x:int) (yes:cm_task) (no:cm_task).
         x <= cm_task_generation_limit
           (if condition then yes else no) <=>
         (if condition
          then x <= cm_task_generation_limit yes
          else x <= cm_task_generation_limit no)`);
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list cases = BOOL_CASES_TAC(
      introduced, `condition:bool`, "Hcondition");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    CONV_WITH_ASMP_TAC(cases[i], reduce_rewrite_conv, THM_LIST());
  }
  return gnode_prove(root);
}
PROOF static thm cm_limit_task_le_cond =
    cm_prove_limit_task_le_cond();


PROOF static thm cm_prove_limit_le_cond(void) {
  gnode root = gnode_new_with_ccl(
      `!(condition:bool) (x:int) (yes:int) (no:int).
         x <= (if condition then yes else no) <=>
         (if condition then x <= yes else x <= no)`);
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list cases = BOOL_CASES_TAC(
      introduced, `condition:bool`, "Hcondition");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    CONV_WITH_ASMP_TAC(cases[i], reduce_rewrite_conv, THM_LIST());
  }
  return gnode_prove(root);
}
PROOF static thm cm_limit_le_cond = cm_prove_limit_le_cond();

PROOF static thm cm_prove_limit_add_ilength(void) {
  gnode root = gnode_new_with_ccl(
      `!(x:int) (items:(A)list). x <= x + ilength items`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm nonnegative = ispec_rule(
      `items:(A)list`, get_theorem_by_name("ILENGTH_NONNEG"));
  ACCEPT_TAC(leaf, mp_rule(int_arith_rule(
      `0i <= ilength (items:(A)list) ==>
       (x:int) <= x + ilength items`), nonnegative));
  return gnode_prove(root);
}
PROOF static thm cm_limit_add_ilength =
    cm_prove_limit_add_ilength();

PROOF static thm cm_prove_state_nextgen_restore_scope_limit(void) {
  gnode root = gnode_new_with_ccl(
      `!(st:cm_src_state) (oldenv:int->int->cm_value)
         (oldregions:(cm_region)list).
         cm_state_nextgen (cm_restore_scope st oldenv oldregions) ==
         cm_state_nextgen st`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm_list rules = get_cm_state_core_defs();
  vector_add(&rules, get_cm_restore_scope_def());
  CONV_TAC(leaf, reduce_rewrite_conv(rules));
  return gnode_prove(root);
}
PROOF static thm cm_state_nextgen_restore_scope_limit =
    cm_prove_state_nextgen_restore_scope_limit();

PROOF static thm cm_prove_state_nextgen_restore_call_limit(void) {
  gnode root = gnode_new_with_ccl(
      `!(st:cm_src_state) (oldenv:int->int->cm_value) (oldfp:int)
         (oldregions:(cm_region)list).
         cm_state_nextgen
           (cm_restore_call st oldenv oldfp oldregions) ==
         cm_state_nextgen st`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm_list rules = get_cm_state_core_defs();
  vector_add(&rules, get_cm_restore_call_def());
  CONV_TAC(leaf, reduce_rewrite_conv(rules));
  return gnode_prove(root);
}
PROOF static thm cm_state_nextgen_restore_call_limit =
    cm_prove_state_nextgen_restore_call_limit();

PROOF static thm cm_prove_begin_call_generation_limit_mono(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (caller:int) (fid:int)
         (values:(cm_value)list) (st:cm_src_state) (ret:cm_type)
         (ks:(cm_frame)list).
         cm_state_nextgen st <=
           cm_task_generation_limit
             (cm_begin_call p caller fid values st ret ks)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
      get_cm_begin_call_def(), cm_limit_task_cond,
      cm_task_generation_limit_def, cm_state_nextgen_enter_call,
      cm_limit_le_cond, cm_limit_add_ilength,
      int_arith_rule(`!(x:int). x <= x`),
      get_theorem_by_name("COND_ID"))));
  return gnode_prove(root);
}
PROOF static thm cm_begin_call_generation_limit_mono =
    cm_prove_begin_call_generation_limit_mono();

PROOF static thm cm_prove_args_start_generation_limit_mono(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (caller:int) (args:(cm_expr)list)
         (st:cm_src_state) (ks:(cm_frame)list) (callee:int)
         (ret:cm_type).
         cm_state_nextgen st <=
           cm_task_generation_limit
             (cm_args_start p caller args st ks callee ret)`);
  gnode_list cases = INDUCT_TAC(root, `args:(cm_expr)list`);
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode leaf = AUTO_INTROS_TAC(cases[i]);
    thm_list rules = THM_LIST(get_cm_args_start_def(),
        cm_task_generation_limit_def,
        cm_begin_call_generation_limit_mono,
        int_arith_rule(`!(x:int). x <= x`));
    ACCEPT_TAC(leaf, eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(rules), goal_ccl(leaf->g))));
  }
  return gnode_prove(root);
}
PROOF static thm cm_args_start_generation_limit_mono =
    cm_prove_args_start_generation_limit_mono();

PROOF static thm cm_prove_rstart_generation_limit_mono(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (expr:cm_expr)
         (st:cm_src_state) (ks:(cm_frame)list).
         cm_state_nextgen st <=
           cm_task_generation_limit (cm_rstart p fid expr st ks)`);
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
    ACCEPT_TAC(branch, eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          shape, get_cm_rstart_def(), cm_limit_task_le_cond,
          cm_task_generation_limit_def, cm_state_nextgen_io,
          cm_args_start_generation_limit_mono,
          int_arith_rule(`!(x:int). x <= x`),
          get_theorem_by_name("COND_ID"))),
        goal_ccl(branch->g))));
  }
  return gnode_prove(root);
}
PROOF static thm cm_rstart_generation_limit_mono =
    cm_prove_rstart_generation_limit_mono();

PROOF static thm cm_prove_lstart_generation_limit_mono(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (expr:cm_expr)
         (st:cm_src_state) (ks:(cm_frame)list).
         cm_state_nextgen st <=
           cm_task_generation_limit (cm_lstart p fid expr st ks)`);
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
    ACCEPT_TAC(branch, eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          shape, get_cm_lstart_def(), cm_limit_task_le_cond,
          cm_task_generation_limit_def,
          int_arith_rule(`!(x:int). x <= x`),
          get_theorem_by_name("COND_ID"))),
        goal_ccl(branch->g))));
  }
  return gnode_prove(root);
}
PROOF static thm cm_lstart_generation_limit_mono =
    cm_prove_lstart_generation_limit_mono();

PROOF static thm cm_prove_sstart_generation_limit_mono(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (stmt:cm_stmt)
         (st:cm_src_state) (ks:(cm_frame)list).
         cm_state_nextgen st <=
           cm_task_generation_limit (cm_sstart p fid stmt st ks)`);
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
    ACCEPT_TAC(branch, eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          shape, get_cm_sstart_def(), cm_limit_task_le_cond,
          cm_task_generation_limit_def,
          cm_state_nextgen_activate_local,
          int_arith_rule(`!(x:int). x <= x`),
          int_arith_rule(`!(x:int). x <= x + 1i`),
          get_theorem_by_name("COND_ID"))),
        goal_ccl(branch->g))));
  }
  return gnode_prove(root);
}
PROOF static thm cm_sstart_generation_limit_mono =
    cm_prove_sstart_generation_limit_mono();

PROOF static thm cm_prove_vapply_generation_limit_mono(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (frame:cm_frame)
         (v:cm_value) (st:cm_src_state) (ks:(cm_frame)list).
         cm_state_nextgen st <=
           cm_task_generation_limit
             (cm_vapply p fid frame v st ks)`);
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list cases = DISJ_CASES_TAC(introduced,
      ispec_rule(`frame:cm_frame`,
        get_datatype_cases("cm_frame")), "Hframe");
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
    ACCEPT_TAC(branch, eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          shape, get_cm_vapply_def(), cm_limit_task_le_cond,
          cm_task_generation_limit_def,
          cm_state_nextgen_io, cm_state_nextgen_store,
          cm_state_nextgen_restore_scope_limit,
          cm_begin_call_generation_limit_mono,
          int_arith_rule(`!(x:int). x <= x`),
          get_theorem_by_name("COND_ID"))),
        goal_ccl(branch->g))));
  }
  return gnode_prove(root);
}
PROOF static thm cm_vapply_generation_limit_mono =
    cm_prove_vapply_generation_limit_mono();

PROOF static thm cm_prove_capply_generation_limit_mono(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (frame:cm_frame)
         (ctl:cm_control) (st:cm_src_state) (ks:(cm_frame)list).
         cm_state_nextgen st <=
           cm_task_generation_limit
             (cm_capply p fid frame ctl st ks)`);
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list cases = DISJ_CASES_TAC(introduced,
      ispec_rule(`frame:cm_frame`,
        get_datatype_cases("cm_frame")), "Hframe");
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
    ACCEPT_TAC(branch, eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          shape, get_cm_capply_def(), cm_limit_task_le_cond,
          cm_task_generation_limit_def,
          cm_state_nextgen_restore_scope_limit,
          cm_state_nextgen_restore_call_limit,
          int_arith_rule(`!(x:int). x <= x`),
          get_theorem_by_name("COND_ID"))),
        goal_ccl(branch->g))));
  }
  return gnode_prove(root);
}
PROOF static thm cm_capply_generation_limit_mono =
    cm_prove_capply_generation_limit_mono();

PROOF static term cm_glm_app_arg_from_right(
    term application, size_t offset) {
  for (size_t i = 0; i < offset; ++i) {
    application = dest_comb(application).tm1;
  }
  return dest_comb(application).tm2;
}

PROOF static term cm_glm_constructor_arg(
    term constructor, size_t arity, size_t index) {
  return cm_glm_app_arg_from_right(
      constructor, arity - index - 1);
}

PROOF static thm cm_prove_initial_state_nextgen_limit(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (input:(int)list).
         cm_state_nextgen (cm_initial_state p input) ==
         cm_first_dynamic_generation p`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm_list rules = get_cm_state_core_defs();
  vector_add(&rules, get_cm_initial_state_def());
  vector_add(&rules, get_cm_first_dynamic_generation_def());
  CONV_TAC(leaf, reduce_rewrite_conv(rules));
  return gnode_prove(root);
}
PROOF static thm cm_initial_state_nextgen_limit =
    cm_prove_initial_state_nextgen_limit();

PROOF static thm cm_prove_task_generation_limit_step_mono(void) {
  gnode root = gnode_new_with_ccl(
      `!(task:cm_task).
         cm_task_generation_limit task <=
         cm_task_generation_limit (cm_step task)`);
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list cases = DISJ_CASES_TAC(introduced,
      ispec_rule(`task:cm_task`,
        get_datatype_cases("cm_task")), "Htask");
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
    if (i == 0) {
      term program = cm_glm_constructor_arg(concrete, 2, 0);
      term input = cm_glm_constructor_arg(concrete, 2, 1);
      thm result = specl_rule(TERM_LIST(
          program, `--1i`, `cm_program_main ${program:cm_program}`,
          `[]:(cm_value)list`,
          `cm_initial_state ${program:cm_program} ${input:(int)list}`,
          `CMIntTy`, `[CMHaltK]`),
          cm_begin_call_generation_limit_mono);
      result = conv_rule(rewrite_conv(THM_LIST(
          cm_initial_state_nextgen_limit)), result);
      thm target_view = apply_conversion(rewrite_conv(THM_LIST(
          task_shape, get_cm_step_def(),
          cm_task_generation_limit_def)), goal_ccl(branch->g));
      ACCEPT_TAC(branch,
          eq_mp_rule(sym_rule(target_view), result));
      continue;
    }
    if (i == 4 || i == 5) {
      thm not_exit = empty_theorem;
      if (i == 5) {
        term control = cm_glm_constructor_arg(concrete, 5, 2);
        gnode_list exit_cases = BOOL_CASES_TAC(
            branch, `cm_control_kind ${control:cm_control} == 4i`,
            "Hexit_limit");
        CONV_WITH_ASMP_TAC(exit_cases[0], reduce_rewrite_conv,
            THM_LIST(task_shape, get_cm_step_def(),
              cm_task_generation_limit_def,
              int_arith_rule(`!(x:int). x <= x`)));
        branch = exit_cases[1];
        not_exit = assume_rule(
            goal_lasmps(branch->g)[labeled_term_list_index(
              goal_lasmps(branch->g), "Hexit_limit")].tm);
      }
      term frames = cm_glm_constructor_arg(concrete, 5, 4);
      gnode_list frame_cases = DISJ_CASES_TAC(branch,
          ispec_rule(frames, get_theorem_by_name("list_CASES")),
          "Hframes");
      for (size_t j = 0; j < vector_size(frame_cases); ++j) {
        gnode frame_branch = frame_cases[j];
        while (true) {
          labeled_term_list assumptions =
              goal_lasmps(frame_branch->g);
          int index =
              labeled_term_list_index(assumptions, "Hframes");
          if (!is_exists(assumptions[index].tm)) break;
          frame_branch = ASMP_EXISTS_TAC(
              frame_branch, "Hframes", NULL);
        }
        thm frame_shape = assume_rule(
            goal_lasmps(frame_branch->g)[labeled_term_list_index(
              goal_lasmps(frame_branch->g), "Hframes")].tm);
        thm_list step_rules = THM_LIST(
            task_shape, frame_shape, get_cm_step_def(),
            get_theorem_by_name("NOT_CONS_NIL"),
            get_theorem_by_name("HD"), get_theorem_by_name("TL"),
            cm_task_generation_limit_def,
            cm_vapply_generation_limit_mono,
            cm_capply_generation_limit_mono,
            int_arith_rule(`!(x:int). x <= x`));
        vector_add(&step_rules, ispecl_rule(TERM_LIST(
            `condition:bool`, `cm_task_generation_limit`,
            `yes_task:cm_task`, `no_task:cm_task`),
            get_theorem_by_name("COND_RAND")));
        vector_add(&step_rules, get_theorem_by_name("COND_ID"));
        if (i == 5) vector_add(&step_rules, not_exit);
        ACCEPT_TAC(frame_branch, eqt_elim_rule(apply_conversion(
            reduce_rewrite_conv(step_rules),
            goal_ccl(frame_branch->g))));
      }
      continue;
    }
    ACCEPT_TAC(branch, eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          task_shape, get_cm_step_def(),
          cm_task_generation_limit_def,
          cm_initial_state_nextgen_limit,
          cm_begin_call_generation_limit_mono,
          cm_rstart_generation_limit_mono,
          cm_lstart_generation_limit_mono,
          cm_sstart_generation_limit_mono,
          int_arith_rule(`!(x:int). x <= x`))),
        goal_ccl(branch->g))));
  }
  return gnode_prove(root);
}
PROOF thm cm_task_generation_limit_step_mono =
    cm_prove_task_generation_limit_step_mono();

PROOF static int cmc_preservation_generation_limit_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_generation_limit_axioms_before,
      "cmc_preservation_generation_limit introduced an axiom");
  ENSURE_COND(vector_size(hyp(cm_task_generation_limit_step_mono)) == 0,
      "task generation-limit monotonicity theorem is not closed");
  return 0;
err:
  return -1;
}

PROOF static int _cmc_preservation_generation_limit_checks =
    cmc_preservation_generation_limit_final_checks();
