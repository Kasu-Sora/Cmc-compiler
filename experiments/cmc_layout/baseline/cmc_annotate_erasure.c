#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_annotate_model.h"
#require "cmc_annotate_model.c"
#include "cmc_annotate_erasure.h"

PROOF thm mk_cm_update_annotation_cond(void) {
  gnode root = gnode_new_with_ccl(
      `!condition yes no.
         cm_update_annotation
           (if condition then (yes:cm_aupdate) else no) ==
         (if condition
          then cm_update_annotation yes
          else cm_update_annotation no)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list cases =
      BOOL_CASES_TAC(leaf, `condition:bool`, "Hcondition");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    CONV_WITH_ASMP_TAC(
        cases[i], reduce_rewrite_conv, THM_LIST());
  }
  return gnode_prove(root);
}
PROOF thm cm_update_annotation_cond =
    mk_cm_update_annotation_cond();

PROOF thm mk_cm_annotation_erases_task_cond(void) {
  gnode root = gnode_new_with_ccl(
      `!condition yes no ann.
         cm_annotation_erases
           (if condition then (yes:cm_task) else no)
           (ann:cm_annotation) <=>
         (if condition
          then cm_annotation_erases yes ann
          else cm_annotation_erases no ann)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list cases =
      BOOL_CASES_TAC(leaf, `condition:bool`, "Hcondition");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    CONV_WITH_ASMP_TAC(
        cases[i], reduce_rewrite_conv, THM_LIST());
  }
  return gnode_prove(root);
}
PROOF thm cm_annotation_erases_task_cond =
    mk_cm_annotation_erases_task_cond();

PROOF thm mk_cm_annotation_erases_ann_cond(void) {
  gnode root = gnode_new_with_ccl(
      `!condition task yes no.
         cm_annotation_erases (task:cm_task)
           (if condition
            then (yes:cm_annotation) else no) <=>
         (if condition
          then cm_annotation_erases task yes
          else cm_annotation_erases task no)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list cases =
      BOOL_CASES_TAC(leaf, `condition:bool`, "Hcondition");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    CONV_WITH_ASMP_TAC(
        cases[i], reduce_rewrite_conv, THM_LIST());
  }
  return gnode_prove(root);
}
PROOF thm cm_annotation_erases_ann_cond =
    mk_cm_annotation_erases_ann_cond();


PROOF thm mk_cm_ann_cursors_cond(void) {
  gnode root = gnode_new_with_ccl(
      `!condition yes no.
         cm_ann_cursors
           (if condition
            then (yes:cm_annotation) else no) ==
         (if condition
          then cm_ann_cursors yes
          else cm_ann_cursors no)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list cases =
      BOOL_CASES_TAC(leaf, `condition:bool`, "Hcondition");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    CONV_WITH_ASMP_TAC(
        cases[i], reduce_rewrite_conv, THM_LIST());
  }
  return gnode_prove(root);
}
PROOF thm cm_ann_cursors_cond = mk_cm_ann_cursors_cond();

PROOF thm mk_cm_cursor_frames_cond(void) {
  gnode root = gnode_new_with_ccl(
      `!condition yes no.
         cm_cursor_frames
           (if condition
            then (yes:(cm_acursor)list) else no) ==
         (if condition
          then cm_cursor_frames yes
          else cm_cursor_frames no)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list cases =
      BOOL_CASES_TAC(leaf, `condition:bool`, "Hcondition");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    CONV_WITH_ASMP_TAC(
        cases[i], reduce_rewrite_conv, THM_LIST());
  }
  return gnode_prove(root);
}
PROOF thm cm_cursor_frames_cond =
    mk_cm_cursor_frames_cond();

PROOF thm mk_cm_cursors_rooted_cond(void) {
  gnode root = gnode_new_with_ccl(
      `!condition yes no.
         cm_cursors_rooted
           (if condition
            then (yes:(cm_acursor)list) else no) <=>
         (if condition
          then cm_cursors_rooted yes
          else cm_cursors_rooted no)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list cases =
      BOOL_CASES_TAC(leaf, `condition:bool`, "Hcondition");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    CONV_WITH_ASMP_TAC(
        cases[i], reduce_rewrite_conv, THM_LIST());
  }
  return gnode_prove(root);
}
PROOF thm cm_cursors_rooted_cond =
    mk_cm_cursors_rooted_cond();

PROOF thm mk_cm_annotation_rooted_cond(void) {
  gnode root = gnode_new_with_ccl(
      `!condition yes no.
         cm_annotation_rooted
           (if condition
            then (yes:cm_annotation) else no) <=>
         (if condition
          then cm_annotation_rooted yes
          else cm_annotation_rooted no)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list cases =
      BOOL_CASES_TAC(leaf, `condition:bool`, "Hcondition");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    CONV_WITH_ASMP_TAC(
        cases[i], reduce_rewrite_conv, THM_LIST());
  }
  return gnode_prove(root);
}
PROOF thm cm_annotation_rooted_cond =
    mk_cm_annotation_rooted_cond();


PROOF thm mk_cm_args_start_nonempty(void) {
  gnode root = gnode_new_with_ccl(
      `!p caller args st ks callee ret.
         ~((args:(cm_expr)list) == []) ==>
         cm_args_start p caller args st ks callee ret ==
         CMRTask p caller (HD args) st
           (CMArgK callee (TL args) [] ret :: ks)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list cases =
      CASES_TAC(leaf, `args:(cm_expr)list`, "Hargs_shape");
  CONTR_TAC(cases[0], contra(
      assume_rule(`~((args:(cm_expr)list) == [])`),
      assume_rule(`(args:(cm_expr)list) == []`)));
  thm_list rules = THM_LIST(
      get_cm_args_start_def(),
      get_theorem_by_name("HD"),
      get_theorem_by_name("TL"));
  gnode reduced = CONV_WITH_ASMP_TAC(
      cases[1], reduce_rewrite_conv, rules);
  if (IS_NULL(reduced->solved)) {
    ACCEPT_TAC(reduced, taut_rule(goal_ccl(reduced->g)));
  }
  return gnode_prove(root);
}
PROOF thm cm_args_start_nonempty =
    mk_cm_args_start_nonempty();

PROOF static thm_list cm_annotation_erasure_rules(void) {
  thm_list rules = THM_LIST(
      get_cm_begin_call_def(), get_cm_rstart_def(),
      get_cm_lstart_def(), get_cm_sstart_def(),
      get_cm_vapply_def(), get_cm_capply_def(),
      get_cm_control_kind_def());
  thm_list local = THM_LIST(
      cm_phase_frame_def, cm_cursor_phase_def,
      cm_cursor_temp_def, cm_cursor_break_def,
      cm_cursor_continue_def, cm_cursor_frames_def,
      cm_ann_pc_def, cm_ann_temp_def, cm_ann_break_def,
      cm_ann_continue_def, cm_ann_cursors_def,
      cm_ann_spills_def, cm_ann_saved_def, cm_ann_calls_def,
      cm_update_annotation_def, cm_ann_plain_def,
      cm_ann_linear_def, cm_ann_push_def,
      cm_ann_replace_def, cm_ann_pop_def,
      cm_ann_spills_set_def, cm_ann_put_spill_def,
      cm_ann_enter_call_def, cm_ann_leave_call_def,
      cm_update_r_def, cm_update_l_def, cm_update_s_def,
      cm_update_v_def, cm_update_c_def,
      cm_annotation_erases_def,
      cm_update_annotation_cond,
      cm_annotation_erases_task_cond,
      cm_annotation_erases_ann_cond,
      cm_ann_cursors_cond, cm_cursor_frames_cond,
      cm_args_start_nonempty);
  for (size_t i = 0; i < vector_size(local); ++i) {
    vector_add(&rules, local[i]);
  }
  return rules;
}

PROOF thm mk_cm_update_r_erases(void) {
  gnode root = gnode_new_with_ccl(
      `!p fid expr st pc temp breakpc continuepc cursors
          spills saved calls.
         cm_annotation_erases
           (cm_rstart (p:cm_program) (fid:int) (expr:cm_expr)
             (st:cm_src_state)
             (cm_cursor_frames (cursors:(cm_acursor)list)))
           (cm_update_annotation
             (cm_update_r p fid st
               (CMAnnotation (pc:int) (temp:int) (breakpc:int)
                 (continuepc:int) cursors
                 (spills:(cm_spill)list)
                 (saved:(cm_spill_frame)list)
                 (calls:(cm_call_sim_frame)list))
               expr))`);
  gnode introduced = AUTO_INTROS_TAC(root);
  thm cases_th = ispec_rule(`expr:cm_expr`, get_cm_expr_cases());
  gnode_list cases = DISJ_CASES_TAC(introduced, cases_th, "Hex");
  thm_list rules = cm_annotation_erasure_rules();
  for (size_t i = 0; i < vector_size(cases); ++i) {
    while (true) {
      labeled_term_list assumptions = goal_lasmps(cases[i]->g);
      int index = labeled_term_list_index(assumptions, "Hex");
      if (!is_exists(assumptions[index].tm)) break;
      cases[i] = ASMP_EXISTS_TAC(cases[i], "Hex", NULL);
    }
    if (i == 8) {
      gnode_list args_cases = BOOL_CASES_TAC(
          cases[i],
          `(a1:(cm_expr)list) == ([]:(cm_expr)list)`,
          "Hargs");
      for (size_t j = 0; j < vector_size(args_cases); ++j) {
        thm_list branch_rules = THM_LIST();
        for (size_t k = 0; k < vector_size(rules); ++k) {
          vector_add(&branch_rules, rules[k]);
        }
        if (j == 1) {
          thm args_start = mp_rule(
              specl_rule(TERM_LIST(
                  `p:cm_program`, `fid:int`,
                  `a1:(cm_expr)list`, `st:cm_src_state`,
                  `cm_cursor_frames
                     (cursors:(cm_acursor)list)`,
                  `a0:int`, `a2:cm_type`),
                  cm_args_start_nonempty),
              assume_rule(
                  `~((a1:(cm_expr)list) ==
                     ([]:(cm_expr)list))`));
          vector_add(&branch_rules, args_start);
        }
        gnode reduced = CONV_WITH_ASMP_TAC(
            args_cases[j], reduce_rewrite_conv, branch_rules);
        if (IS_NULL(reduced->solved)) {
          ACCEPT_TAC(reduced, taut_rule(goal_ccl(reduced->g)));
        }
      }
      continue;
    }
    gnode reduced =
        CONV_WITH_ASMP_TAC(cases[i], reduce_rewrite_conv, rules);
    if (IS_NULL(reduced->solved)) {
      ACCEPT_TAC(reduced, taut_rule(goal_ccl(reduced->g)));
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_update_r_erases = mk_cm_update_r_erases();

PROOF thm mk_cm_update_l_erases(void) {
  gnode root = gnode_new_with_ccl(
      `!p fid expr st pc temp breakpc continuepc cursors
          spills saved calls.
         cm_annotation_erases
           (cm_lstart (p:cm_program) (fid:int) (expr:cm_expr)
             (st:cm_src_state)
             (cm_cursor_frames (cursors:(cm_acursor)list)))
           (cm_update_annotation
             (cm_update_l p fid st
               (CMAnnotation (pc:int) (temp:int) (breakpc:int)
                 (continuepc:int) cursors
                 (spills:(cm_spill)list)
                 (saved:(cm_spill_frame)list)
                 (calls:(cm_call_sim_frame)list))
               expr))`);
  gnode introduced = AUTO_INTROS_TAC(root);
  thm cases_th = ispec_rule(`expr:cm_expr`, get_cm_expr_cases());
  gnode_list cases = DISJ_CASES_TAC(introduced, cases_th, "Hex");
  thm_list rules = cm_annotation_erasure_rules();
  for (size_t i = 0; i < vector_size(cases); ++i) {
    while (true) {
      labeled_term_list assumptions = goal_lasmps(cases[i]->g);
      int index = labeled_term_list_index(assumptions, "Hex");
      if (!is_exists(assumptions[index].tm)) break;
      cases[i] = ASMP_EXISTS_TAC(cases[i], "Hex", NULL);
    }
    gnode reduced =
        CONV_WITH_ASMP_TAC(cases[i], reduce_rewrite_conv, rules);
    if (IS_NULL(reduced->solved)) {
      ACCEPT_TAC(reduced, taut_rule(goal_ccl(reduced->g)));
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_update_l_erases = mk_cm_update_l_erases();

PROOF thm mk_cm_update_s_erases(void) {
  gnode root = gnode_new_with_ccl(
      `!p fid stmt st pc temp breakpc continuepc cursors
          spills saved calls.
         cm_annotation_erases
           (cm_sstart (p:cm_program) (fid:int) (stmt:cm_stmt)
             (st:cm_src_state)
             (cm_cursor_frames (cursors:(cm_acursor)list)))
           (cm_update_annotation
             (cm_update_s p fid st
               (CMAnnotation (pc:int) (temp:int) (breakpc:int)
                 (continuepc:int) cursors
                 (spills:(cm_spill)list)
                 (saved:(cm_spill_frame)list)
                 (calls:(cm_call_sim_frame)list))
               stmt))`);
  gnode introduced = AUTO_INTROS_TAC(root);
  thm cases_th = ispec_rule(`stmt:cm_stmt`, get_cm_stmt_cases());
  gnode_list cases = DISJ_CASES_TAC(introduced, cases_th, "Hst");
  thm_list rules = cm_annotation_erasure_rules();
  for (size_t i = 0; i < vector_size(cases); ++i) {
    while (true) {
      labeled_term_list assumptions = goal_lasmps(cases[i]->g);
      int index = labeled_term_list_index(assumptions, "Hst");
      if (!is_exists(assumptions[index].tm)) break;
      cases[i] = ASMP_EXISTS_TAC(cases[i], "Hst", NULL);
    }
    gnode reduced =
        CONV_WITH_ASMP_TAC(cases[i], reduce_rewrite_conv, rules);
    if (IS_NULL(reduced->solved)) {
      ACCEPT_TAC(reduced, taut_rule(goal_ccl(reduced->g)));
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_update_s_erases = mk_cm_update_s_erases();

PROOF thm_list cm_phase_erasure_rules(void) {
  thm_list rules = cm_annotation_erasure_rules();
  thm_list local = THM_LIST(
      get_datatype_distinctness("cm_aphase"),
      get_datatype_injectivity("cm_aphase"),
      get_theorem_by_name("NOT_CONS_NIL"),
      get_theorem_by_name("HD"),
      get_theorem_by_name("TL"));
  for (size_t i = 0; i < vector_size(local); ++i) {
    vector_add(&rules, local[i]);
  }
  return rules;
}

PROOF thm mk_cm_update_v_erases(void) {
  gnode root = gnode_new_with_ccl(
      `!p fid value st phase pc temp breakpc continuepc
          parent_temp parent_break parent_continue rest
          spills saved calls.
         (phase == CAHaltP ==> rest == []) ==>
         cm_annotation_erases
           (cm_vapply (p:cm_program) (fid:int)
             (cm_phase_frame (phase:cm_aphase))
             (value:cm_value) (st:cm_src_state)
             (cm_cursor_frames (rest:(cm_acursor)list)))
           (cm_update_annotation
             (cm_update_v p fid value st
               (CMAnnotation (pc:int) (temp:int)
                 (breakpc:int) (continuepc:int)
                 (CMACursor phase (parent_temp:int)
                   (parent_break:int) (parent_continue:int) ::
                   rest)
                 (spills:(cm_spill)list)
                 (saved:(cm_spill_frame)list)
                 (calls:(cm_call_sim_frame)list))
               phase))`);
  gnode introduced = AUTO_INTROS_TAC(root);
  thm phase_cases = ispec_rule(
      `phase:cm_aphase`, get_datatype_cases("cm_aphase"));
  gnode_list cases =
      DISJ_CASES_TAC(introduced, phase_cases, "Hphase");
  thm_list rules = cm_phase_erasure_rules();
  for (size_t i = 0; i < vector_size(cases); ++i) {
    while (true) {
      labeled_term_list assumptions = goal_lasmps(cases[i]->g);
      int index =
          labeled_term_list_index(assumptions, "Hphase");
      if (!is_exists(assumptions[index].tm)) break;
      cases[i] =
          ASMP_EXISTS_TAC(cases[i], "Hphase", NULL);
    }
    thm_list branch_rules = THM_LIST();
    for (size_t j = 0; j < vector_size(rules); ++j) {
      vector_add(&branch_rules, rules[j]);
    }
    if (i == 0) {
      thm root_tail = mp_rule(
          assume_rule(
              `(phase:cm_aphase) == CAHaltP ==>
               (rest:(cm_acursor)list) == []`),
          assume_rule(`(phase:cm_aphase) == CAHaltP`));
      vector_add(&branch_rules, root_tail);
    }
    gnode reduced = CONV_WITH_ASMP_TAC(
        cases[i], reduce_rewrite_conv, branch_rules);
    if (IS_NULL(reduced->solved)) {
      ACCEPT_TAC(reduced, taut_rule(goal_ccl(reduced->g)));
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_update_v_erases = mk_cm_update_v_erases();

PROOF thm mk_cm_update_c_erases(void) {
  gnode root = gnode_new_with_ccl(
      `!p fid control st phase pc temp breakpc continuepc
          parent_temp parent_break parent_continue rest
          spills saved calls.
         (phase == CAHaltP ==> rest == []) ==>
         cm_annotation_erases
           (cm_capply (p:cm_program) (fid:int)
             (cm_phase_frame (phase:cm_aphase))
             (control:cm_control) (st:cm_src_state)
             (cm_cursor_frames (rest:(cm_acursor)list)))
           (cm_update_annotation
             (cm_update_c p fid control st
               (CMAnnotation (pc:int) (temp:int)
                 (breakpc:int) (continuepc:int)
                 (CMACursor phase (parent_temp:int)
                   (parent_break:int) (parent_continue:int) ::
                   rest)
                 (spills:(cm_spill)list)
                 (saved:(cm_spill_frame)list)
                 (calls:(cm_call_sim_frame)list))
               phase))`);
  gnode introduced = AUTO_INTROS_TAC(root);
  thm phase_cases = ispec_rule(
      `phase:cm_aphase`, get_datatype_cases("cm_aphase"));
  gnode_list cases =
      DISJ_CASES_TAC(introduced, phase_cases, "Hphase");
  thm_list rules = cm_phase_erasure_rules();
  for (size_t i = 0; i < vector_size(cases); ++i) {
    while (true) {
      labeled_term_list assumptions = goal_lasmps(cases[i]->g);
      int index =
          labeled_term_list_index(assumptions, "Hphase");
      if (!is_exists(assumptions[index].tm)) break;
      cases[i] =
          ASMP_EXISTS_TAC(cases[i], "Hphase", NULL);
    }
    thm_list branch_rules = THM_LIST();
    for (size_t j = 0; j < vector_size(rules); ++j) {
      vector_add(&branch_rules, rules[j]);
    }
    if (i == 0) {
      thm root_tail = mp_rule(
          assume_rule(
              `(phase:cm_aphase) == CAHaltP ==>
               (rest:(cm_acursor)list) == []`),
          assume_rule(`(phase:cm_aphase) == CAHaltP`));
      vector_add(&branch_rules, root_tail);
    }
    gnode reduced = CONV_WITH_ASMP_TAC(
        cases[i], reduce_rewrite_conv, branch_rules);
    if (IS_NULL(reduced->solved)) {
      ACCEPT_TAC(reduced, taut_rule(goal_ccl(reduced->g)));
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_update_c_erases = mk_cm_update_c_erases();
