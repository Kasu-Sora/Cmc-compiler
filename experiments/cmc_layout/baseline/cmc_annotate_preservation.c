#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_annotate_erasure.h"
#require "cmc_annotate_erasure.c"
#include "cmc_annotate_preservation.h"

PROOF static thm_list cm_rooted_update_rules(void) {
  thm_list rules = cm_phase_erasure_rules();
  thm_list local = THM_LIST(
      cm_cursors_rooted_def, cm_annotation_rooted_def,
      cm_cursors_rooted_cond, cm_annotation_rooted_cond);
  for (size_t i = 0; i < vector_size(local); ++i) {
    vector_add(&rules, local[i]);
  }
  return rules;
}

PROOF thm mk_cm_update_r_rooted(void) {
  gnode root = gnode_new_with_ccl(
      `!p fid expr st ann.
         cm_annotation_rooted (ann:cm_annotation) ==>
         cm_annotation_rooted
           (cm_update_annotation
             (cm_update_r (p:cm_program) (fid:int)
               (st:cm_src_state) ann (expr:cm_expr)))`);
  gnode introduced = AUTO_INTROS_TAC(root);
  thm expr_cases =
      ispec_rule(`expr:cm_expr`, get_cm_expr_cases());
  gnode_list cases =
      DISJ_CASES_TAC(introduced, expr_cases, "Hex");
  thm_list rules = cm_rooted_update_rules();
  thm rooted_cursors = conv_rule(
      reduce_rewrite_conv(
          THM_LIST(cm_annotation_rooted_def)),
      assume_rule(
          `cm_annotation_rooted (ann:cm_annotation)`));
  vector_add(&rules, rooted_cursors);
  for (size_t i = 0; i < vector_size(cases); ++i) {
    while (true) {
      labeled_term_list assumptions = goal_lasmps(cases[i]->g);
      int index =
          labeled_term_list_index(assumptions, "Hex");
      if (!is_exists(assumptions[index].tm)) break;
      cases[i] = ASMP_EXISTS_TAC(cases[i], "Hex", NULL);
    }
    gnode reduced = CONV_WITH_ASMP_TAC(
        cases[i], reduce_rewrite_conv, rules);
    if (IS_NULL(reduced->solved)) {
      ACCEPT_TAC(reduced, taut_rule(goal_ccl(reduced->g)));
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_update_r_rooted = mk_cm_update_r_rooted();

PROOF thm mk_cm_update_l_rooted(void) {
  gnode root = gnode_new_with_ccl(
      `!p fid expr st ann.
         cm_annotation_rooted (ann:cm_annotation) ==>
         cm_annotation_rooted
           (cm_update_annotation
             (cm_update_l (p:cm_program) (fid:int)
               (st:cm_src_state) ann (expr:cm_expr)))`);
  gnode introduced = AUTO_INTROS_TAC(root);
  thm expr_cases =
      ispec_rule(`expr:cm_expr`, get_cm_expr_cases());
  gnode_list cases =
      DISJ_CASES_TAC(introduced, expr_cases, "Hex");
  thm_list rules = cm_rooted_update_rules();
  thm rooted_cursors = conv_rule(
      reduce_rewrite_conv(
          THM_LIST(cm_annotation_rooted_def)),
      assume_rule(
          `cm_annotation_rooted (ann:cm_annotation)`));
  vector_add(&rules, rooted_cursors);
  for (size_t i = 0; i < vector_size(cases); ++i) {
    while (true) {
      labeled_term_list assumptions = goal_lasmps(cases[i]->g);
      int index =
          labeled_term_list_index(assumptions, "Hex");
      if (!is_exists(assumptions[index].tm)) break;
      cases[i] = ASMP_EXISTS_TAC(cases[i], "Hex", NULL);
    }
    gnode reduced = CONV_WITH_ASMP_TAC(
        cases[i], reduce_rewrite_conv, rules);
    if (IS_NULL(reduced->solved)) {
      ACCEPT_TAC(reduced, taut_rule(goal_ccl(reduced->g)));
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_update_l_rooted = mk_cm_update_l_rooted();

PROOF thm mk_cm_update_s_rooted(void) {
  gnode root = gnode_new_with_ccl(
      `!p fid stmt st ann.
         cm_annotation_rooted (ann:cm_annotation) ==>
         cm_annotation_rooted
           (cm_update_annotation
             (cm_update_s (p:cm_program) (fid:int)
               (st:cm_src_state) ann (stmt:cm_stmt)))`);
  gnode introduced = AUTO_INTROS_TAC(root);
  thm stmt_cases =
      ispec_rule(`stmt:cm_stmt`, get_cm_stmt_cases());
  gnode_list cases =
      DISJ_CASES_TAC(introduced, stmt_cases, "Hstmt");
  thm_list rules = cm_rooted_update_rules();
  thm rooted_cursors = conv_rule(
      reduce_rewrite_conv(
          THM_LIST(cm_annotation_rooted_def)),
      assume_rule(
          `cm_annotation_rooted (ann:cm_annotation)`));
  vector_add(&rules, rooted_cursors);
  for (size_t i = 0; i < vector_size(cases); ++i) {
    while (true) {
      labeled_term_list assumptions = goal_lasmps(cases[i]->g);
      int index =
          labeled_term_list_index(assumptions, "Hstmt");
      if (!is_exists(assumptions[index].tm)) break;
      cases[i] =
          ASMP_EXISTS_TAC(cases[i], "Hstmt", NULL);
    }
    gnode reduced = CONV_WITH_ASMP_TAC(
        cases[i], reduce_rewrite_conv, rules);
    if (IS_NULL(reduced->solved)) {
      ACCEPT_TAC(reduced, taut_rule(goal_ccl(reduced->g)));
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_update_s_rooted = mk_cm_update_s_rooted();

PROOF thm mk_cm_update_v_rooted(void) {
  gnode root = gnode_new_with_ccl(
      `!p fid value st phase pc temp breakpc continuepc
          parent_temp parent_break parent_continue rest
          spills saved calls.
         cm_annotation_rooted
           (CMAnnotation (pc:int) (temp:int)
             (breakpc:int) (continuepc:int)
             (CMACursor (phase:cm_aphase) (parent_temp:int)
               (parent_break:int) (parent_continue:int) ::
               (rest:(cm_acursor)list))
             (spills:(cm_spill)list)
             (saved:(cm_spill_frame)list)
             (calls:(cm_call_sim_frame)list)) ==>
         cm_annotation_rooted
           (cm_update_annotation
             (cm_update_v (p:cm_program) (fid:int)
               (value:cm_value) (st:cm_src_state)
               (CMAnnotation pc temp breakpc continuepc
                 (CMACursor phase parent_temp parent_break
                   parent_continue :: rest)
                 spills saved calls)
               phase))`);
  gnode introduced = AUTO_INTROS_TAC(root);
  thm rooted_parts = conv_rule(
      reduce_rewrite_conv(THM_LIST(
          cm_annotation_rooted_def, cm_ann_cursors_def,
          cm_cursors_rooted_def, cm_cursor_phase_def)),
      assume_rule(
          `cm_annotation_rooted
             (CMAnnotation (pc:int) (temp:int)
               (breakpc:int) (continuepc:int)
               (CMACursor (phase:cm_aphase)
                 (parent_temp:int) (parent_break:int)
                 (parent_continue:int) ::
                 (rest:(cm_acursor)list))
               (spills:(cm_spill)list)
               (saved:(cm_spill_frame)list)
               (calls:(cm_call_sim_frame)list))`));
  thm phase_cases = ispec_rule(
      `phase:cm_aphase`, get_datatype_cases("cm_aphase"));
  gnode_list cases =
      DISJ_CASES_TAC(introduced, phase_cases, "Hphase");
  thm_list rules = cm_rooted_update_rules();
  vector_add(&rules, conjunct1_rule(rooted_parts));
  vector_add(&rules, conjunct2_rule(rooted_parts));
  for (size_t i = 0; i < vector_size(cases); ++i) {
    while (true) {
      labeled_term_list assumptions = goal_lasmps(cases[i]->g);
      int index =
          labeled_term_list_index(assumptions, "Hphase");
      if (!is_exists(assumptions[index].tm)) break;
      cases[i] =
          ASMP_EXISTS_TAC(cases[i], "Hphase", NULL);
    }
    gnode reduced = CONV_WITH_ASMP_TAC(
        cases[i], reduce_rewrite_conv, rules);
    if (IS_NULL(reduced->solved)) {
      ACCEPT_TAC(reduced, taut_rule(goal_ccl(reduced->g)));
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_update_v_rooted = mk_cm_update_v_rooted();

PROOF thm mk_cm_update_c_rooted(void) {
  gnode root = gnode_new_with_ccl(
      `!p fid control st phase pc temp breakpc continuepc
          parent_temp parent_break parent_continue rest
          spills saved calls.
         cm_annotation_rooted
           (CMAnnotation (pc:int) (temp:int)
             (breakpc:int) (continuepc:int)
             (CMACursor (phase:cm_aphase) (parent_temp:int)
               (parent_break:int) (parent_continue:int) ::
               (rest:(cm_acursor)list))
             (spills:(cm_spill)list)
             (saved:(cm_spill_frame)list)
             (calls:(cm_call_sim_frame)list)) ==>
         cm_annotation_rooted
           (cm_update_annotation
             (cm_update_c (p:cm_program) (fid:int)
               (control:cm_control) (st:cm_src_state)
               (CMAnnotation pc temp breakpc continuepc
                 (CMACursor phase parent_temp parent_break
                   parent_continue :: rest)
                 spills saved calls)
               phase))`);
  gnode introduced = AUTO_INTROS_TAC(root);
  thm rooted_parts = conv_rule(
      reduce_rewrite_conv(THM_LIST(
          cm_annotation_rooted_def, cm_ann_cursors_def,
          cm_cursors_rooted_def, cm_cursor_phase_def)),
      assume_rule(
          `cm_annotation_rooted
             (CMAnnotation (pc:int) (temp:int)
               (breakpc:int) (continuepc:int)
               (CMACursor (phase:cm_aphase)
                 (parent_temp:int) (parent_break:int)
                 (parent_continue:int) ::
                 (rest:(cm_acursor)list))
               (spills:(cm_spill)list)
               (saved:(cm_spill_frame)list)
               (calls:(cm_call_sim_frame)list))`));
  thm phase_cases = ispec_rule(
      `phase:cm_aphase`, get_datatype_cases("cm_aphase"));
  gnode_list cases =
      DISJ_CASES_TAC(introduced, phase_cases, "Hphase");
  thm_list rules = cm_rooted_update_rules();
  vector_add(&rules, conjunct1_rule(rooted_parts));
  vector_add(&rules, conjunct2_rule(rooted_parts));
  for (size_t i = 0; i < vector_size(cases); ++i) {
    while (true) {
      labeled_term_list assumptions = goal_lasmps(cases[i]->g);
      int index =
          labeled_term_list_index(assumptions, "Hphase");
      if (!is_exists(assumptions[index].tm)) break;
      cases[i] =
          ASMP_EXISTS_TAC(cases[i], "Hphase", NULL);
    }
    gnode reduced = CONV_WITH_ASMP_TAC(
        cases[i], reduce_rewrite_conv, rules);
    if (IS_NULL(reduced->solved)) {
      ACCEPT_TAC(reduced, taut_rule(goal_ccl(reduced->g)));
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_update_c_rooted = mk_cm_update_c_rooted();

PROOF thm mk_cm_update_v_cursor_preserves(void) {
  gnode root = gnode_new_with_ccl(
      `!p fid v st cursor pc temp breakpc continuepc
          rest spills saved calls.
         cm_annotation_rooted
           (CMAnnotation (pc:int) (temp:int)
             (breakpc:int) (continuepc:int)
             ((cursor:cm_acursor) ::
               (rest:(cm_acursor)list))
             (spills:(cm_spill)list)
             (saved:(cm_spill_frame)list)
             (calls:(cm_call_sim_frame)list)) ==>
         cm_annotation_erases
           (cm_vapply (p:cm_program) (fid:int)
             (cm_phase_frame (cm_cursor_phase cursor))
             (v:cm_value) (st:cm_src_state)
             (cm_cursor_frames rest))
           (cm_update_annotation
             (cm_update_v p fid v st
               (CMAnnotation pc temp breakpc continuepc
                 (cursor :: rest) spills saved calls)
               (cm_cursor_phase cursor))) &&
         cm_annotation_rooted
           (cm_update_annotation
             (cm_update_v p fid v st
               (CMAnnotation pc temp breakpc continuepc
                 (cursor :: rest) spills saved calls)
               (cm_cursor_phase cursor)))`);
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list cases =
      CASES_TAC(introduced, `cursor:cm_acursor`, "Hcursor");
  thm cursor_case = assume_rule(
      `(cursor:cm_acursor) ==
       CMACursor (a0:cm_aphase) (a1:int) (a2:int) (a3:int)`);
  thm rooted = conv_rule(
      rewrite_conv(THM_LIST(cursor_case)),
      assume_rule(
          `cm_annotation_rooted
             (CMAnnotation (pc:int) (temp:int)
               (breakpc:int) (continuepc:int)
               ((cursor:cm_acursor) ::
                 (rest:(cm_acursor)list))
               (spills:(cm_spill)list)
               (saved:(cm_spill_frame)list)
               (calls:(cm_call_sim_frame)list))`));
  thm rooted_parts = conv_rule(
      reduce_rewrite_conv(THM_LIST(
          cm_annotation_rooted_def, cm_ann_cursors_def,
          cm_cursors_rooted_def, cm_cursor_phase_def)),
      rooted);
  thm erases = mp_rule(
      specl_rule(
          TERM_LIST(`p:cm_program`, `fid:int`, `v:cm_value`,
              `st:cm_src_state`, `a0:cm_aphase`, `pc:int`,
              `temp:int`, `breakpc:int`, `continuepc:int`,
              `a1:int`, `a2:int`, `a3:int`,
              `rest:(cm_acursor)list`,
              `spills:(cm_spill)list`,
              `saved:(cm_spill_frame)list`,
              `calls:(cm_call_sim_frame)list`),
          cm_update_v_erases),
      conjunct1_rule(rooted_parts));
  thm remains_rooted = mp_rule(
      specl_rule(
          TERM_LIST(`p:cm_program`, `fid:int`, `v:cm_value`,
              `st:cm_src_state`, `a0:cm_aphase`, `pc:int`,
              `temp:int`, `breakpc:int`, `continuepc:int`,
              `a1:int`, `a2:int`, `a3:int`,
              `rest:(cm_acursor)list`,
              `spills:(cm_spill)list`,
              `saved:(cm_spill_frame)list`,
              `calls:(cm_call_sim_frame)list`),
          cm_update_v_rooted),
      rooted);
  CONV_WITH_ASMP_TAC(
      cases[0], reduce_rewrite_conv,
      THM_LIST(conj_rule(erases, remains_rooted),
          cm_cursor_phase_def));
  return gnode_prove(root);
}
PROOF thm cm_update_v_cursor_preserves =
    mk_cm_update_v_cursor_preserves();

PROOF thm mk_cm_update_c_cursor_preserves(void) {
  gnode root = gnode_new_with_ccl(
      `!p fid ctl st cursor pc temp breakpc continuepc
          rest spills saved calls.
         cm_annotation_rooted
           (CMAnnotation (pc:int) (temp:int)
             (breakpc:int) (continuepc:int)
             ((cursor:cm_acursor) ::
               (rest:(cm_acursor)list))
             (spills:(cm_spill)list)
             (saved:(cm_spill_frame)list)
             (calls:(cm_call_sim_frame)list)) ==>
         cm_annotation_erases
           (cm_capply (p:cm_program) (fid:int)
             (cm_phase_frame (cm_cursor_phase cursor))
             (ctl:cm_control) (st:cm_src_state)
             (cm_cursor_frames rest))
           (cm_update_annotation
             (cm_update_c p fid ctl st
               (CMAnnotation pc temp breakpc continuepc
                 (cursor :: rest) spills saved calls)
               (cm_cursor_phase cursor))) &&
         cm_annotation_rooted
           (cm_update_annotation
             (cm_update_c p fid ctl st
               (CMAnnotation pc temp breakpc continuepc
                 (cursor :: rest) spills saved calls)
               (cm_cursor_phase cursor)))`);
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list cases =
      CASES_TAC(introduced, `cursor:cm_acursor`, "Hcursor");
  thm cursor_case = assume_rule(
      `(cursor:cm_acursor) ==
       CMACursor (a0:cm_aphase) (a1:int) (a2:int) (a3:int)`);
  thm rooted = conv_rule(
      rewrite_conv(THM_LIST(cursor_case)),
      assume_rule(
          `cm_annotation_rooted
             (CMAnnotation (pc:int) (temp:int)
               (breakpc:int) (continuepc:int)
               ((cursor:cm_acursor) ::
                 (rest:(cm_acursor)list))
               (spills:(cm_spill)list)
               (saved:(cm_spill_frame)list)
               (calls:(cm_call_sim_frame)list))`));
  thm rooted_parts = conv_rule(
      reduce_rewrite_conv(THM_LIST(
          cm_annotation_rooted_def, cm_ann_cursors_def,
          cm_cursors_rooted_def, cm_cursor_phase_def)),
      rooted);
  thm erases = mp_rule(
      specl_rule(
          TERM_LIST(`p:cm_program`, `fid:int`, `ctl:cm_control`,
              `st:cm_src_state`, `a0:cm_aphase`, `pc:int`,
              `temp:int`, `breakpc:int`, `continuepc:int`,
              `a1:int`, `a2:int`, `a3:int`,
              `rest:(cm_acursor)list`,
              `spills:(cm_spill)list`,
              `saved:(cm_spill_frame)list`,
              `calls:(cm_call_sim_frame)list`),
          cm_update_c_erases),
      conjunct1_rule(rooted_parts));
  thm remains_rooted = mp_rule(
      specl_rule(
          TERM_LIST(`p:cm_program`, `fid:int`, `ctl:cm_control`,
              `st:cm_src_state`, `a0:cm_aphase`, `pc:int`,
              `temp:int`, `breakpc:int`, `continuepc:int`,
              `a1:int`, `a2:int`, `a3:int`,
              `rest:(cm_acursor)list`,
              `spills:(cm_spill)list`,
              `saved:(cm_spill_frame)list`,
              `calls:(cm_call_sim_frame)list`),
          cm_update_c_rooted),
      rooted);
  CONV_WITH_ASMP_TAC(
      cases[0], reduce_rewrite_conv,
      THM_LIST(conj_rule(erases, remains_rooted),
          cm_cursor_phase_def));
  return gnode_prove(root);
}
PROOF thm cm_update_c_cursor_preserves =
    mk_cm_update_c_cursor_preserves();

PROOF thm mk_cm_v_step_preserves(void) {
  gnode root = gnode_new_with_ccl(
      `!p fid v st ks pc temp breakpc continuepc
          cursors spills saved calls.
         cm_annotation_rooted
           (CMAnnotation (pc:int) (temp:int)
             (breakpc:int) (continuepc:int)
             (cursors:(cm_acursor)list)
             (spills:(cm_spill)list)
             (saved:(cm_spill_frame)list)
             (calls:(cm_call_sim_frame)list)) &&
         cm_annotation_erases
           (CMVTask (p:cm_program) (fid:int) (v:cm_value)
             (st:cm_src_state) (ks:(cm_frame)list))
           (CMAnnotation pc temp breakpc continuepc
             cursors spills saved calls) ==>
         cm_annotation_erases
           (cm_step (CMVTask p fid v st ks))
           (cm_update_annotation
             (cm_annotation_step
               (CMVTask p fid v st ks)
               (CMAnnotation pc temp breakpc continuepc
                 cursors spills saved calls))) &&
         cm_annotation_rooted
           (cm_update_annotation
             (cm_annotation_step
               (CMVTask p fid v st ks)
               (CMAnnotation pc temp breakpc continuepc
                 cursors spills saved calls)))`);
  gnode_list introduced_cases = AUTO_ASMP_DESTRUCT_TAC(
      AUTO_INTROS_TAC(root));
  gnode introduced = introduced_cases[0];
  thm rooted = assume_rule(
      `cm_annotation_rooted
         (CMAnnotation (pc:int) (temp:int)
           (breakpc:int) (continuepc:int)
           (cursors:(cm_acursor)list)
           (spills:(cm_spill)list)
           (saved:(cm_spill_frame)list)
           (calls:(cm_call_sim_frame)list))`);
  thm erases = assume_rule(
      `cm_annotation_erases
         (CMVTask (p:cm_program) (fid:int) (v:cm_value)
           (st:cm_src_state) (ks:(cm_frame)list))
         (CMAnnotation (pc:int) (temp:int)
           (breakpc:int) (continuepc:int)
           (cursors:(cm_acursor)list)
           (spills:(cm_spill)list)
           (saved:(cm_spill_frame)list)
           (calls:(cm_call_sim_frame)list))`);
  gnode_list cases = CASES_TAC(
      introduced, `cursors:(cm_acursor)list`, "Hlistcase");
  thm nil_case = assume_rule(
      `(cursors:(cm_acursor)list) == []`);
  thm nil_rooted = conv_rule(
      rewrite_conv(THM_LIST(nil_case)), rooted);
  thm nil_erases = conv_rule(
      reduce_rewrite_conv(THM_LIST(
          nil_case, cm_annotation_erases_def,
          cm_ann_cursors_def, cm_cursor_frames_def)),
      erases);
  thm nil_ks = sym_rule(nil_erases);
  gnode nil_reduced = CONV_WITH_ASMP_TAC(
      cases[0], reduce_rewrite_conv,
      THM_LIST(nil_case, nil_ks, nil_rooted,
          get_cm_step_def(), cm_annotation_step_def,
          cm_update_annotation_def, cm_annotation_erases_def,
          cm_annotation_rooted_def, cm_ann_cursors_def,
          cm_cursor_frames_def, cm_cursors_rooted_def));
  if (IS_NULL(nil_reduced->solved)) {
    ACCEPT_TAC(nil_reduced, taut_rule(goal_ccl(nil_reduced->g)));
  }

  thm cons_case = assume_rule(
      `(cursors:(cm_acursor)list) ==
       (a0:cm_acursor) :: (a1:(cm_acursor)list)`);
  thm cons_rooted = conv_rule(
      rewrite_conv(THM_LIST(cons_case)), rooted);
  thm cons_erases = conv_rule(
      reduce_rewrite_conv(THM_LIST(
          cons_case, cm_annotation_erases_def,
          cm_ann_cursors_def, cm_cursor_frames_def)),
      erases);
  thm cons_ks = sym_rule(cons_erases);
  thm preserved = mp_rule(
      specl_rule(
          TERM_LIST(`p:cm_program`, `fid:int`, `v:cm_value`,
              `st:cm_src_state`, `a0:cm_acursor`,
              `pc:int`, `temp:int`, `breakpc:int`,
              `continuepc:int`, `a1:(cm_acursor)list`,
              `spills:(cm_spill)list`,
              `saved:(cm_spill_frame)list`,
              `calls:(cm_call_sim_frame)list`),
          cm_update_v_cursor_preserves),
      cons_rooted);
  gnode cons_reduced = CONV_WITH_ASMP_TAC(
      cases[1], reduce_rewrite_conv,
      THM_LIST(cons_case, cons_ks, preserved,
          get_cm_step_def(), cm_annotation_step_def,
          cm_update_annotation_def, cm_ann_cursors_def,
          cm_cursor_frames_def, get_theorem_by_name("HD"),
          get_theorem_by_name("TL"),
          get_theorem_by_name("NOT_CONS_NIL")));
  if (IS_NULL(cons_reduced->solved)) {
    ACCEPT_TAC(cons_reduced, taut_rule(goal_ccl(cons_reduced->g)));
  }
  return gnode_prove(root);
}
PROOF thm cm_v_step_preserves = mk_cm_v_step_preserves();

PROOF thm mk_cm_c_step_preserves(void) {
  gnode root = gnode_new_with_ccl(
      `!p fid ctl st ks pc temp breakpc continuepc
          cursors spills saved calls.
         cm_annotation_rooted
           (CMAnnotation (pc:int) (temp:int)
             (breakpc:int) (continuepc:int)
             (cursors:(cm_acursor)list)
             (spills:(cm_spill)list)
             (saved:(cm_spill_frame)list)
             (calls:(cm_call_sim_frame)list)) &&
         cm_annotation_erases
           (CMCTask (p:cm_program) (fid:int) (ctl:cm_control)
             (st:cm_src_state) (ks:(cm_frame)list))
           (CMAnnotation pc temp breakpc continuepc
             cursors spills saved calls) ==>
         cm_annotation_erases
           (cm_step (CMCTask p fid ctl st ks))
           (cm_update_annotation
             (cm_annotation_step
               (CMCTask p fid ctl st ks)
               (CMAnnotation pc temp breakpc continuepc
                 cursors spills saved calls))) &&
         cm_annotation_rooted
           (cm_update_annotation
             (cm_annotation_step
               (CMCTask p fid ctl st ks)
               (CMAnnotation pc temp breakpc continuepc
                 cursors spills saved calls)))`);
  gnode_list introduced_cases = AUTO_ASMP_DESTRUCT_TAC(
      AUTO_INTROS_TAC(root));
  gnode introduced = introduced_cases[0];
  thm rooted = assume_rule(
      `cm_annotation_rooted
         (CMAnnotation (pc:int) (temp:int)
           (breakpc:int) (continuepc:int)
           (cursors:(cm_acursor)list)
           (spills:(cm_spill)list)
           (saved:(cm_spill_frame)list)
           (calls:(cm_call_sim_frame)list))`);
  thm erases = assume_rule(
      `cm_annotation_erases
         (CMCTask (p:cm_program) (fid:int) (ctl:cm_control)
           (st:cm_src_state) (ks:(cm_frame)list))
         (CMAnnotation (pc:int) (temp:int)
           (breakpc:int) (continuepc:int)
           (cursors:(cm_acursor)list)
           (spills:(cm_spill)list)
           (saved:(cm_spill_frame)list)
           (calls:(cm_call_sim_frame)list))`);
  gnode_list exit_split = BOOL_CASES_TAC(
      introduced, `cm_control_kind (ctl:cm_control) == 4i`,
      "Hcontrol_exit");
  gnode exit_branch = CONV_WITH_ASMP_TAC(
      exit_split[0], reduce_rewrite_conv,
      THM_LIST(get_cm_step_def(), cm_annotation_step_def,
          cm_update_annotation_def, cm_ann_done_def,
          cm_annotation_erases_def, cm_annotation_rooted_def,
          cm_ann_pc_def, cm_ann_temp_def, cm_ann_break_def,
          cm_ann_continue_def, cm_ann_cursors_def,
          cm_ann_spills_def, cm_ann_saved_def, cm_ann_calls_def,
          cm_cursors_rooted_def));
  if (IS_NULL(exit_branch->solved)) {
    ACCEPT_TAC(exit_branch, taut_rule(goal_ccl(exit_branch->g)));
  }
  gnode nonexit_branch = exit_split[1];
  gnode_list cases = CASES_TAC(
      nonexit_branch, `cursors:(cm_acursor)list`, "Hlistcase");
  thm nil_case = assume_rule(
      `(cursors:(cm_acursor)list) == []`);
  thm nil_rooted = conv_rule(
      rewrite_conv(THM_LIST(nil_case)), rooted);
  thm nil_erases = conv_rule(
      reduce_rewrite_conv(THM_LIST(
          nil_case, cm_annotation_erases_def,
          cm_ann_cursors_def, cm_cursor_frames_def)),
      erases);
  thm nil_ks = sym_rule(nil_erases);
  gnode_list nil_control_cases = BOOL_CASES_TAC(
      cases[0], `cm_control_kind (ctl:cm_control) == 5i`,
      "Hnil_control_error");
  for (size_t i = 0; i < vector_size(nil_control_cases); ++i) {
    gnode nil_reduced = CONV_WITH_ASMP_TAC(
        nil_control_cases[i], reduce_rewrite_conv,
        THM_LIST(nil_case, nil_ks, nil_rooted,
            get_cm_step_def(), cm_annotation_step_def,
            cm_update_annotation_def, cm_annotation_erases_def,
            cm_annotation_rooted_def, cm_ann_cursors_def,
            cm_cursor_frames_def, cm_cursors_rooted_def));
    if (IS_NULL(nil_reduced->solved)) {
      ACCEPT_TAC(nil_reduced, taut_rule(goal_ccl(nil_reduced->g)));
    }
  }
  thm cons_case = assume_rule(
      `(cursors:(cm_acursor)list) ==
       (a0:cm_acursor) :: (a1:(cm_acursor)list)`);
  thm cons_rooted = conv_rule(
      rewrite_conv(THM_LIST(cons_case)), rooted);
  thm cons_erases = conv_rule(
      reduce_rewrite_conv(THM_LIST(
          cons_case, cm_annotation_erases_def,
          cm_ann_cursors_def, cm_cursor_frames_def)),
      erases);
  thm cons_ks = sym_rule(cons_erases);
  thm preserved = mp_rule(
      specl_rule(
          TERM_LIST(`p:cm_program`, `fid:int`, `ctl:cm_control`,
              `st:cm_src_state`, `a0:cm_acursor`,
              `pc:int`, `temp:int`, `breakpc:int`,
              `continuepc:int`, `a1:(cm_acursor)list`,
              `spills:(cm_spill)list`,
              `saved:(cm_spill_frame)list`,
              `calls:(cm_call_sim_frame)list`),
          cm_update_c_cursor_preserves),
      cons_rooted);
  gnode cons_reduced = CONV_WITH_ASMP_TAC(
      cases[1], reduce_rewrite_conv,
      THM_LIST(cons_case, cons_ks, preserved,
          get_cm_step_def(), cm_annotation_step_def,
          cm_update_annotation_def, cm_ann_cursors_def,
          cm_cursor_frames_def, get_theorem_by_name("HD"),
          get_theorem_by_name("TL"),
          get_theorem_by_name("NOT_CONS_NIL")));
  if (IS_NULL(cons_reduced->solved)) {
    ACCEPT_TAC(cons_reduced, taut_rule(goal_ccl(cons_reduced->g)));
  }
  return gnode_prove(root);
}
PROOF thm cm_c_step_preserves = mk_cm_c_step_preserves();

PROOF thm mk_cm_start_step_preserves(void) {
  gnode root = gnode_new_with_ccl(
      `!p input ann.
         cm_annotation_erases
           (cm_step (CMStartTask (p:cm_program) (input:(int)list)))
           (cm_update_annotation
             (cm_annotation_step
               (CMStartTask p input) (ann:cm_annotation))) &&
         cm_annotation_rooted
           (cm_update_annotation
             (cm_annotation_step
               (CMStartTask p input) ann))`);
  gnode introduced = AUTO_INTROS_TAC(root);
  term condition =
      `cm_call_ok (p:cm_program) (cm_program_main p) []
         (cm_initial_state p (input:(int)list)) &&
       cm_call_depth [CMHaltK] < 65536i`;
  gnode_list cases =
      BOOL_CASES_TAC(introduced, condition, "Hcondition");
  thm_list rules = THM_LIST(
      get_cm_step_def(), get_cm_begin_call_def(),
      cm_annotation_step_def, cm_update_annotation_def,
      cm_ann_enter_call_def, cm_annotation_erases_def,
      cm_annotation_rooted_def, cm_ann_cursors_def,
      cm_cursor_frames_def, cm_cursor_phase_def,
      cm_phase_frame_def, cm_cursors_rooted_def,
      get_datatype_distinctness("cm_aphase"),
      get_theorem_by_name("HD"), get_theorem_by_name("TL"),
      get_theorem_by_name("NOT_CONS_NIL"));
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode reduced = CONV_WITH_ASMP_TAC(
        cases[i], reduce_rewrite_conv, rules);
    if (IS_NULL(reduced->solved)) {
      ACCEPT_TAC(reduced, taut_rule(goal_ccl(reduced->g)));
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_start_step_preserves =
    mk_cm_start_step_preserves();
PROOF thm mk_cm_r_step_preserves(void) {
  gnode root = gnode_new_with_ccl(
      `!p fid expr st ks pc temp breakpc continuepc
          cursors spills saved calls.
         cm_annotation_rooted
           (CMAnnotation (pc:int) (temp:int)
             (breakpc:int) (continuepc:int)
             (cursors:(cm_acursor)list)
             (spills:(cm_spill)list)
             (saved:(cm_spill_frame)list)
             (calls:(cm_call_sim_frame)list)) &&
         cm_annotation_erases
           (CMRTask (p:cm_program) (fid:int) (expr:cm_expr)
             (st:cm_src_state) (ks:(cm_frame)list))
           (CMAnnotation pc temp breakpc continuepc
             cursors spills saved calls) ==>
         cm_annotation_erases
           (cm_step (CMRTask p fid expr st ks))
           (cm_update_annotation
             (cm_annotation_step
               (CMRTask p fid expr st ks)
               (CMAnnotation pc temp breakpc continuepc
                 cursors spills saved calls))) &&
         cm_annotation_rooted
           (cm_update_annotation
             (cm_annotation_step
               (CMRTask p fid expr st ks)
               (CMAnnotation pc temp breakpc continuepc
                 cursors spills saved calls)))`);
  gnode_list premises = AUTO_ASMP_DESTRUCT_TAC(
      AUTO_INTROS_TAC(root));
  gnode leaf = premises[0];
  term ann =
      `CMAnnotation (pc:int) (temp:int)
         (breakpc:int) (continuepc:int)
         (cursors:(cm_acursor)list)
         (spills:(cm_spill)list)
         (saved:(cm_spill_frame)list)
         (calls:(cm_call_sim_frame)list)`;
  thm rooted = assume_rule(
      `cm_annotation_rooted
         (CMAnnotation (pc:int) (temp:int)
           (breakpc:int) (continuepc:int)
           (cursors:(cm_acursor)list)
           (spills:(cm_spill)list)
           (saved:(cm_spill_frame)list)
           (calls:(cm_call_sim_frame)list))`);
  thm erases = assume_rule(
      `cm_annotation_erases
         (CMRTask (p:cm_program) (fid:int) (expr:cm_expr)
           (st:cm_src_state) (ks:(cm_frame)list))
         (CMAnnotation (pc:int) (temp:int)
           (breakpc:int) (continuepc:int)
           (cursors:(cm_acursor)list)
           (spills:(cm_spill)list)
           (saved:(cm_spill_frame)list)
           (calls:(cm_call_sim_frame)list))`);
  thm frame_eq = conv_rule(
      reduce_rewrite_conv(THM_LIST(
          cm_annotation_erases_def, cm_ann_cursors_def)),
      erases);
  thm ks_eq = sym_rule(frame_eq);
  thm next_erases = specl_rule(
      TERM_LIST(`p:cm_program`, `fid:int`, `expr:cm_expr`,
          `st:cm_src_state`, `pc:int`, `temp:int`,
          `breakpc:int`, `continuepc:int`,
          `cursors:(cm_acursor)list`,
          `spills:(cm_spill)list`,
          `saved:(cm_spill_frame)list`,
          `calls:(cm_call_sim_frame)list`),
      cm_update_r_erases);
  thm next_rooted = mp_rule(
      specl_rule(
          TERM_LIST(`p:cm_program`, `fid:int`, `expr:cm_expr`,
              `st:cm_src_state`, ann),
          cm_update_r_rooted),
      rooted);
  gnode reduced = CONV_WITH_ASMP_TAC(
      leaf, reduce_rewrite_conv,
      THM_LIST(ks_eq, conj_rule(next_erases, next_rooted),
          get_cm_step_def(), cm_annotation_step_def));
  if (IS_NULL(reduced->solved)) {
    ACCEPT_TAC(reduced, taut_rule(goal_ccl(reduced->g)));
  }
  return gnode_prove(root);
}
PROOF thm cm_r_step_preserves = mk_cm_r_step_preserves();

PROOF thm mk_cm_l_step_preserves(void) {
  gnode root = gnode_new_with_ccl(
      `!p fid expr st ks pc temp breakpc continuepc
          cursors spills saved calls.
         cm_annotation_rooted
           (CMAnnotation (pc:int) (temp:int)
             (breakpc:int) (continuepc:int)
             (cursors:(cm_acursor)list)
             (spills:(cm_spill)list)
             (saved:(cm_spill_frame)list)
             (calls:(cm_call_sim_frame)list)) &&
         cm_annotation_erases
           (CMLTask (p:cm_program) (fid:int) (expr:cm_expr)
             (st:cm_src_state) (ks:(cm_frame)list))
           (CMAnnotation pc temp breakpc continuepc
             cursors spills saved calls) ==>
         cm_annotation_erases
           (cm_step (CMLTask p fid expr st ks))
           (cm_update_annotation
             (cm_annotation_step
               (CMLTask p fid expr st ks)
               (CMAnnotation pc temp breakpc continuepc
                 cursors spills saved calls))) &&
         cm_annotation_rooted
           (cm_update_annotation
             (cm_annotation_step
               (CMLTask p fid expr st ks)
               (CMAnnotation pc temp breakpc continuepc
                 cursors spills saved calls)))`);
  gnode_list premises = AUTO_ASMP_DESTRUCT_TAC(
      AUTO_INTROS_TAC(root));
  gnode leaf = premises[0];
  term ann =
      `CMAnnotation (pc:int) (temp:int)
         (breakpc:int) (continuepc:int)
         (cursors:(cm_acursor)list)
         (spills:(cm_spill)list)
         (saved:(cm_spill_frame)list)
         (calls:(cm_call_sim_frame)list)`;
  thm rooted = assume_rule(
      `cm_annotation_rooted
         (CMAnnotation (pc:int) (temp:int)
           (breakpc:int) (continuepc:int)
           (cursors:(cm_acursor)list)
           (spills:(cm_spill)list)
           (saved:(cm_spill_frame)list)
           (calls:(cm_call_sim_frame)list))`);
  thm erases = assume_rule(
      `cm_annotation_erases
         (CMLTask (p:cm_program) (fid:int) (expr:cm_expr)
           (st:cm_src_state) (ks:(cm_frame)list))
         (CMAnnotation (pc:int) (temp:int)
           (breakpc:int) (continuepc:int)
           (cursors:(cm_acursor)list)
           (spills:(cm_spill)list)
           (saved:(cm_spill_frame)list)
           (calls:(cm_call_sim_frame)list))`);
  thm frame_eq = conv_rule(
      reduce_rewrite_conv(THM_LIST(
          cm_annotation_erases_def, cm_ann_cursors_def)),
      erases);
  thm ks_eq = sym_rule(frame_eq);
  thm next_erases = specl_rule(
      TERM_LIST(`p:cm_program`, `fid:int`, `expr:cm_expr`,
          `st:cm_src_state`, `pc:int`, `temp:int`,
          `breakpc:int`, `continuepc:int`,
          `cursors:(cm_acursor)list`,
          `spills:(cm_spill)list`,
          `saved:(cm_spill_frame)list`,
          `calls:(cm_call_sim_frame)list`),
      cm_update_l_erases);
  thm next_rooted = mp_rule(
      specl_rule(
          TERM_LIST(`p:cm_program`, `fid:int`, `expr:cm_expr`,
              `st:cm_src_state`, ann),
          cm_update_l_rooted),
      rooted);
  gnode reduced = CONV_WITH_ASMP_TAC(
      leaf, reduce_rewrite_conv,
      THM_LIST(ks_eq, conj_rule(next_erases, next_rooted),
          get_cm_step_def(), cm_annotation_step_def));
  if (IS_NULL(reduced->solved)) {
    ACCEPT_TAC(reduced, taut_rule(goal_ccl(reduced->g)));
  }
  return gnode_prove(root);
}
PROOF thm cm_l_step_preserves = mk_cm_l_step_preserves();

PROOF thm mk_cm_s_step_preserves(void) {
  gnode root = gnode_new_with_ccl(
      `!p fid stmt st ks pc temp breakpc continuepc
          cursors spills saved calls.
         cm_annotation_rooted
           (CMAnnotation (pc:int) (temp:int)
             (breakpc:int) (continuepc:int)
             (cursors:(cm_acursor)list)
             (spills:(cm_spill)list)
             (saved:(cm_spill_frame)list)
             (calls:(cm_call_sim_frame)list)) &&
         cm_annotation_erases
           (CMSTask (p:cm_program) (fid:int) (stmt:cm_stmt)
             (st:cm_src_state) (ks:(cm_frame)list))
           (CMAnnotation pc temp breakpc continuepc
             cursors spills saved calls) ==>
         cm_annotation_erases
           (cm_step (CMSTask p fid stmt st ks))
           (cm_update_annotation
             (cm_annotation_step
               (CMSTask p fid stmt st ks)
               (CMAnnotation pc temp breakpc continuepc
                 cursors spills saved calls))) &&
         cm_annotation_rooted
           (cm_update_annotation
             (cm_annotation_step
               (CMSTask p fid stmt st ks)
               (CMAnnotation pc temp breakpc continuepc
                 cursors spills saved calls)))`);
  gnode_list premises = AUTO_ASMP_DESTRUCT_TAC(
      AUTO_INTROS_TAC(root));
  gnode leaf = premises[0];
  term ann =
      `CMAnnotation (pc:int) (temp:int)
         (breakpc:int) (continuepc:int)
         (cursors:(cm_acursor)list)
         (spills:(cm_spill)list)
         (saved:(cm_spill_frame)list)
         (calls:(cm_call_sim_frame)list)`;
  thm rooted = assume_rule(
      `cm_annotation_rooted
         (CMAnnotation (pc:int) (temp:int)
           (breakpc:int) (continuepc:int)
           (cursors:(cm_acursor)list)
           (spills:(cm_spill)list)
           (saved:(cm_spill_frame)list)
           (calls:(cm_call_sim_frame)list))`);
  thm erases = assume_rule(
      `cm_annotation_erases
         (CMSTask (p:cm_program) (fid:int) (stmt:cm_stmt)
           (st:cm_src_state) (ks:(cm_frame)list))
         (CMAnnotation (pc:int) (temp:int)
           (breakpc:int) (continuepc:int)
           (cursors:(cm_acursor)list)
           (spills:(cm_spill)list)
           (saved:(cm_spill_frame)list)
           (calls:(cm_call_sim_frame)list))`);
  thm frame_eq = conv_rule(
      reduce_rewrite_conv(THM_LIST(
          cm_annotation_erases_def, cm_ann_cursors_def)),
      erases);
  thm ks_eq = sym_rule(frame_eq);
  thm next_erases = specl_rule(
      TERM_LIST(`p:cm_program`, `fid:int`, `stmt:cm_stmt`,
          `st:cm_src_state`, `pc:int`, `temp:int`,
          `breakpc:int`, `continuepc:int`,
          `cursors:(cm_acursor)list`,
          `spills:(cm_spill)list`,
          `saved:(cm_spill_frame)list`,
          `calls:(cm_call_sim_frame)list`),
      cm_update_s_erases);
  thm next_rooted = mp_rule(
      specl_rule(
          TERM_LIST(`p:cm_program`, `fid:int`, `stmt:cm_stmt`,
              `st:cm_src_state`, ann),
          cm_update_s_rooted),
      rooted);
  gnode reduced = CONV_WITH_ASMP_TAC(
      leaf, reduce_rewrite_conv,
      THM_LIST(ks_eq, conj_rule(next_erases, next_rooted),
          get_cm_step_def(), cm_annotation_step_def));
  if (IS_NULL(reduced->solved)) {
    ACCEPT_TAC(reduced, taut_rule(goal_ccl(reduced->g)));
  }
  return gnode_prove(root);
}
PROOF thm cm_s_step_preserves = mk_cm_s_step_preserves();

PROOF thm mk_cm_annotation_step_preserves(void) {
  gnode root = gnode_new_with_ccl(
      `!task pc temp breakpc continuepc cursors spills saved calls.
         cm_annotation_rooted
           (CMAnnotation (pc:int) (temp:int)
             (breakpc:int) (continuepc:int)
             (cursors:(cm_acursor)list)
             (spills:(cm_spill)list)
             (saved:(cm_spill_frame)list)
             (calls:(cm_call_sim_frame)list)) &&
         cm_annotation_erases
           (task:cm_task)
           (CMAnnotation pc temp breakpc continuepc
             cursors spills saved calls) ==>
         cm_annotation_erases
           (cm_step task)
           (cm_update_annotation
             (cm_annotation_step task
               (CMAnnotation pc temp breakpc continuepc
                 cursors spills saved calls))) &&
         cm_annotation_rooted
           (cm_update_annotation
             (cm_annotation_step task
               (CMAnnotation pc temp breakpc continuepc
                 cursors spills saved calls)))`);
  gnode_list premises = AUTO_ASMP_DESTRUCT_TAC(
      AUTO_INTROS_TAC(root));
  gnode introduced = premises[0];
  term ann =
      `CMAnnotation (pc:int) (temp:int)
         (breakpc:int) (continuepc:int)
         (cursors:(cm_acursor)list)
         (spills:(cm_spill)list)
         (saved:(cm_spill_frame)list)
         (calls:(cm_call_sim_frame)list)`;
  thm rooted = assume_rule(
      `cm_annotation_rooted
         (CMAnnotation (pc:int) (temp:int)
           (breakpc:int) (continuepc:int)
           (cursors:(cm_acursor)list)
           (spills:(cm_spill)list)
           (saved:(cm_spill_frame)list)
           (calls:(cm_call_sim_frame)list))`);
  thm erases = assume_rule(
      `cm_annotation_erases (task:cm_task)
         (CMAnnotation (pc:int) (temp:int)
           (breakpc:int) (continuepc:int)
           (cursors:(cm_acursor)list)
           (spills:(cm_spill)list)
           (saved:(cm_spill_frame)list)
           (calls:(cm_call_sim_frame)list))`);
  gnode_list cases =
      CASES_TAC(introduced, `task:cm_task`, "Htask");
  thm task_cases[7] = {
      assume_rule(
          `(task:cm_task) ==
           CMStartTask (a0:cm_program) (a1:(int)list)`),
      assume_rule(
          `(task:cm_task) ==
           CMRTask (a0:cm_program) (a1:int) (a2:cm_expr)
             (a3:cm_src_state) (a4:(cm_frame)list)`),
      assume_rule(
          `(task:cm_task) ==
           CMLTask (a0:cm_program) (a1:int) (a2:cm_expr)
             (a3:cm_src_state) (a4:(cm_frame)list)`),
      assume_rule(
          `(task:cm_task) ==
           CMSTask (a0:cm_program) (a1:int) (a2:cm_stmt)
             (a3:cm_src_state) (a4:(cm_frame)list)`),
      assume_rule(
          `(task:cm_task) ==
           CMVTask (a0:cm_program) (a1:int) (a2:cm_value)
             (a3:cm_src_state) (a4:(cm_frame)list)`),
      assume_rule(
          `(task:cm_task) ==
           CMCTask (a0:cm_program) (a1:int) (a2:cm_control)
             (a3:cm_src_state) (a4:(cm_frame)list)`),
      assume_rule(
          `(task:cm_task) ==
           CMDoneTask (a0:cm_src_state) (a1:cm_control)
             (a2:int)`)
  };
  thm branch_erases[7];
  for (size_t i = 0; i < 7; ++i) {
    branch_erases[i] = conv_rule(
        rewrite_conv(THM_LIST(task_cases[i])), erases);
  }
  thm results[7];
  results[0] = specl_rule(
      TERM_LIST(`a0:cm_program`, `a1:(int)list`, ann),
      cm_start_step_preserves);
  results[1] = match_mp_rule(
      cm_r_step_preserves,
      conj_rule(rooted, branch_erases[1]));
  results[2] = match_mp_rule(
      cm_l_step_preserves,
      conj_rule(rooted, branch_erases[2]));
  results[3] = match_mp_rule(
      cm_s_step_preserves,
      conj_rule(rooted, branch_erases[3]));
  results[4] = match_mp_rule(
      cm_v_step_preserves,
      conj_rule(rooted, branch_erases[4]));
  results[5] = match_mp_rule(
      cm_c_step_preserves,
      conj_rule(rooted, branch_erases[5]));
  results[6] = conj_rule(branch_erases[6], rooted);
  for (size_t i = 0; i < 6; ++i) {
    gnode reduced = CONV_WITH_ASMP_TAC(
        cases[i], reduce_rewrite_conv,
        THM_LIST(task_cases[i], results[i]));
    if (IS_NULL(reduced->solved)) {
      ACCEPT_TAC(reduced, taut_rule(goal_ccl(reduced->g)));
    }
  }
  gnode done_reduced = CONV_WITH_ASMP_TAC(
      cases[6], reduce_rewrite_conv,
      THM_LIST(task_cases[6], results[6],
          get_cm_step_def(), cm_annotation_step_def,
          cm_update_annotation_def));
  if (IS_NULL(done_reduced->solved)) {
    ACCEPT_TAC(
        done_reduced, taut_rule(goal_ccl(done_reduced->g)));
  }
  return gnode_prove(root);
}
PROOF thm cm_annotation_step_preserves =
    mk_cm_annotation_step_preserves();

PROOF thm mk_cm_annotation_step_sound(void) {
  gnode root = gnode_new_with_ccl(
      `!task ann.
         cm_annotation_rooted (ann:cm_annotation) &&
         cm_annotation_erases (task:cm_task) ann ==>
         cm_annotation_erases
           (cm_step task)
           (cm_update_annotation
             (cm_annotation_step task ann)) &&
         cm_annotation_rooted
           (cm_update_annotation
             (cm_annotation_step task ann))`);
  gnode_list premises = AUTO_ASMP_DESTRUCT_TAC(
      AUTO_INTROS_TAC(root));
  gnode introduced = premises[0];
  thm rooted =
      assume_rule(`cm_annotation_rooted (ann:cm_annotation)`);
  thm erases = assume_rule(
      `cm_annotation_erases (task:cm_task)
         (ann:cm_annotation)`);
  gnode_list cases =
      CASES_TAC(introduced, `ann:cm_annotation`, "Hann");
  thm ann_case = assume_rule(
      `(ann:cm_annotation) ==
       CMAnnotation (a0:int) (a1:int) (a2:int) (a3:int)
         (a4:(cm_acursor)list) (a5:(cm_spill)list)
         (a6:(cm_spill_frame)list)
         (a7:(cm_call_sim_frame)list)`);
  thm case_rooted = conv_rule(
      rewrite_conv(THM_LIST(ann_case)), rooted);
  thm case_erases = conv_rule(
      rewrite_conv(THM_LIST(ann_case)), erases);
  thm preserved = match_mp_rule(
      cm_annotation_step_preserves,
      conj_rule(case_rooted, case_erases));
  gnode reduced = CONV_WITH_ASMP_TAC(
      cases[0], reduce_rewrite_conv,
      THM_LIST(ann_case, preserved));
  if (IS_NULL(reduced->solved)) {
    ACCEPT_TAC(reduced, taut_rule(goal_ccl(reduced->g)));
  }
  return gnode_prove(root);
}
PROOF thm cm_annotation_step_sound =
    mk_cm_annotation_step_sound();
PROOF thm mk_cm_annotated_step_target(void) {
  gnode root = gnode_new_with_ccl(
      `!(ast:cm_astate).
         cm_astate_target (cm_annotated_step ast) ==
         tvm_iter
           (cm_update_steps
             (cm_annotation_step (cm_astate_task ast)
               (cm_astate_annotation ast)))
           (cm_astate_target ast)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
      cm_annotated_step_def, cm_astate_task_def,
      cm_astate_target_def, cm_astate_annotation_def)));
  return gnode_prove(root);
}
PROOF thm cm_annotated_step_target =
    mk_cm_annotated_step_target();

PROOF thm mk_cm_annotated_step_task(void) {
  gnode root = gnode_new_with_ccl(
      `!(ast:cm_astate).
         cm_astate_task (cm_annotated_step ast) ==
         cm_step (cm_astate_task ast)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
      cm_annotated_step_def, cm_astate_task_def,
      cm_astate_annotation_def)));
  return gnode_prove(root);
}
PROOF thm cm_annotated_step_task =
    mk_cm_annotated_step_task();


PROOF thm mk_cm_annotated_step_erasure(void) {
  gnode root = gnode_new_with_ccl(
      `!ast.
         cm_annotation_rooted
           (cm_astate_annotation (ast:cm_astate)) &&
         cm_annotation_erases
           (cm_astate_task ast)
           (cm_astate_annotation ast) ==>
         cm_annotation_erases
           (cm_astate_task (cm_annotated_step ast))
           (cm_astate_annotation (cm_annotated_step ast)) &&
         cm_annotation_rooted
           (cm_astate_annotation (cm_annotated_step ast))`);
  gnode_list premises = AUTO_ASMP_DESTRUCT_TAC(
      AUTO_INTROS_TAC(root));
  gnode leaf = premises[0];
  thm rooted = assume_rule(
      `cm_annotation_rooted
         (cm_astate_annotation (ast:cm_astate))`);
  thm erases = assume_rule(
      `cm_annotation_erases
         (cm_astate_task (ast:cm_astate))
         (cm_astate_annotation ast)`);
  thm preserved = match_mp_rule(
      cm_annotation_step_sound,
      conj_rule(rooted, erases));
  gnode reduced = CONV_WITH_ASMP_TAC(
      leaf, reduce_rewrite_conv,
      THM_LIST(preserved, cm_annotated_step_def,
          cm_astate_task_def, cm_astate_annotation_def));
  if (IS_NULL(reduced->solved)) {
    ACCEPT_TAC(reduced, taut_rule(goal_ccl(reduced->g)));
  }
  return gnode_prove(root);
}
PROOF thm cm_annotated_step_erasure =
    mk_cm_annotated_step_erasure();

PROOF thm mk_cm_annotated_start_rooted(void) {
  gnode root = gnode_new_with_ccl(
      `!p input.
         cm_annotation_rooted
           (cm_astate_annotation
             (cm_annotated_start
               (p:cm_program) (input:(int)list)))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
      cm_annotated_start_def, cm_initial_annotation_def,
      cm_astate_annotation_def, cm_annotation_rooted_def,
      cm_ann_cursors_def, cm_cursors_rooted_def)));
  return gnode_prove(root);
}
PROOF thm cm_annotated_start_rooted =
    mk_cm_annotated_start_rooted();
PROOF thm mk_cm_annotated_start_erases(void) {
  gnode root = gnode_new_with_ccl(
      `!p input.
         cm_annotation_erases
           (cm_astate_task
             (cm_annotated_start (p:cm_program) (input:(int)list)))
           (cm_astate_annotation
             (cm_annotated_start p input))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
      cm_annotated_start_def, cm_initial_annotation_def,
      cm_astate_task_def, cm_astate_annotation_def,
      cm_annotation_erases_def, cm_ann_cursors_def)));
  return gnode_prove(root);
}
PROOF thm cm_annotated_start_erases =
    mk_cm_annotated_start_erases();

PROOF thm mk_cm_annotated_iter_invariant(void) {
  gnode root = gnode_new_with_ccl(
      `!(n:num). !(ast:cm_astate).
         cm_annotation_erases
           (cm_astate_task ast)
           (cm_astate_annotation ast) &&
         cm_annotation_rooted
           (cm_astate_annotation ast) ==>
         cm_annotation_erases
           (cm_astate_task (cm_annotated_iter n ast))
           (cm_astate_annotation (cm_annotated_iter n ast)) &&
         cm_annotation_rooted
           (cm_astate_annotation (cm_annotated_iter n ast))`);
  gnode_list cases = INDUCT_TAC(root, `n:num`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_WITH_ASMP_TAC(leaf, reduce_rewrite_conv, THM_LIST(
        cm_annotated_iter_def));
  }
  {
    gnode_list premises = AUTO_ASMP_DESTRUCT_TAC(
        AUTO_INTROS_TAC(cases[1]));
    gnode leaf = premises[0];
    thm erases = assume_rule(
        `cm_annotation_erases
           (cm_astate_task (ast:cm_astate))
           (cm_astate_annotation ast)`);
    thm rooted = assume_rule(
        `cm_annotation_rooted
           (cm_astate_annotation (ast:cm_astate))`);
    thm stepped = mp_rule(
        spec_rule(`ast:cm_astate`, cm_annotated_step_erasure),
        conj_rule(rooted, erases));
    thm ih = assume_rule(
        `!(ast:cm_astate).
           cm_annotation_erases
             (cm_astate_task ast)
             (cm_astate_annotation ast) &&
           cm_annotation_rooted
             (cm_astate_annotation ast) ==>
           cm_annotation_erases
             (cm_astate_task (cm_annotated_iter (n:num) ast))
             (cm_astate_annotation (cm_annotated_iter n ast)) &&
           cm_annotation_rooted
             (cm_astate_annotation (cm_annotated_iter n ast))`);
    thm iterated = mp_rule(
        spec_rule(`cm_annotated_step (ast:cm_astate)`, ih),
        stepped);
    gnode reduced = CONV_TAC(
        leaf, reduce_rewrite_conv(THM_LIST(
            cm_annotated_iter_def)));
    if (IS_NULL(reduced->solved)) {
      ACCEPT_TAC(reduced, iterated);
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_annotated_iter_invariant =
    mk_cm_annotated_iter_invariant();

PROOF thm mk_cm_annotated_iter_task(void) {
  gnode root = gnode_new_with_ccl(
      `!(n:num). !(ast:cm_astate).
         cm_astate_task (cm_annotated_iter n ast) ==
         cm_iter n (cm_astate_task ast)`);
  gnode_list cases = INDUCT_TAC(root, `n:num`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        cm_annotated_iter_def, get_cm_iter_def())));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm ih = assume_rule(
        `!(ast:cm_astate).
           cm_astate_task (cm_annotated_iter (n:num) ast) ==
           cm_iter n (cm_astate_task ast)`);
    thm iterated = conv_rule(
        reduce_rewrite_conv(THM_LIST(cm_annotated_step_task)),
        spec_rule(`cm_annotated_step (ast:cm_astate)`, ih));
    gnode reduced = CONV_TAC(
        leaf, reduce_rewrite_conv(THM_LIST(
            cm_annotated_iter_def, get_cm_iter_def(),
            cm_annotated_step_task)));
    if (IS_NULL(reduced->solved)) {
      ACCEPT_TAC(reduced, iterated);
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_annotated_iter_task =
    mk_cm_annotated_iter_task();

PROOF thm mk_cm_annotated_iter_sound(void) {
  gnode root = gnode_new_with_ccl(
      `!(n:num). !(ast:cm_astate).
         cm_annotation_erases
           (cm_astate_task ast)
           (cm_astate_annotation ast) &&
         cm_annotation_rooted
           (cm_astate_annotation ast) ==>
         cm_annotation_erases
           (cm_astate_task (cm_annotated_iter n ast))
           (cm_astate_annotation (cm_annotated_iter n ast)) &&
         cm_annotation_rooted
           (cm_astate_annotation (cm_annotated_iter n ast)) &&
         cm_astate_task (cm_annotated_iter n ast) ==
           cm_iter n (cm_astate_task ast)`);
  gnode_list premises = AUTO_ASMP_DESTRUCT_TAC(
      AUTO_INTROS_TAC(root));
  gnode leaf = premises[0];
  thm erases = assume_rule(
      `cm_annotation_erases
         (cm_astate_task (ast:cm_astate))
         (cm_astate_annotation ast)`);
  thm rooted = assume_rule(
      `cm_annotation_rooted
         (cm_astate_annotation (ast:cm_astate))`);
  thm invariant = mp_rule(
      specl_rule(TERM_LIST(`n:num`, `ast:cm_astate`),
          cm_annotated_iter_invariant),
      conj_rule(erases, rooted));
  thm task = specl_rule(
      TERM_LIST(`n:num`, `ast:cm_astate`),
      cm_annotated_iter_task);
  ACCEPT_TAC(leaf, conj_rule(
      conjunct1_rule(invariant),
      conj_rule(conjunct2_rule(invariant), task)));
  return gnode_prove(root);
}
PROOF thm cm_annotated_iter_sound =
    mk_cm_annotated_iter_sound();

PROOF thm mk_cm_annotated_iter_erasure(void) {
  gnode root = gnode_new_with_ccl(
      `!p input n.
         cm_annotation_erases
           (cm_astate_task
             (cm_annotated_iter n
               (cm_annotated_start
                 (p:cm_program) (input:(int)list))))
           (cm_astate_annotation
             (cm_annotated_iter n
               (cm_annotated_start p input))) &&
         cm_annotation_rooted
           (cm_astate_annotation
             (cm_annotated_iter n
               (cm_annotated_start p input))) &&
         cm_astate_task
           (cm_annotated_iter n
             (cm_annotated_start p input)) ==
           cm_iter n (CMStartTask p input)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm erases = specl_rule(
      TERM_LIST(`p:cm_program`, `input:(int)list`),
      cm_annotated_start_erases);
  thm rooted = specl_rule(
      TERM_LIST(`p:cm_program`, `input:(int)list`),
      cm_annotated_start_rooted);
  thm result = mp_rule(
      specl_rule(TERM_LIST(
          `n:num`,
          `cm_annotated_start
             (p:cm_program) (input:(int)list)`),
          cm_annotated_iter_sound),
      conj_rule(erases, rooted));
  thm start_task = apply_conversion(
      reduce_rewrite_conv(THM_LIST(
          cm_annotated_start_def, cm_astate_task_def)),
      `cm_astate_task
         (cm_annotated_start
           (p:cm_program) (input:(int)list))`);
  thm normalized = conv_rule(
      rewrite_conv(THM_LIST(start_task)), result);
  ACCEPT_TAC(leaf, normalized);
  return gnode_prove(root);
}
PROOF thm cm_annotated_iter_erasure =
    mk_cm_annotated_iter_erasure();

PROOF thm get_cm_annotation_erasure(void) {
  return cm_annotation_erases_def;
}
PROOF thm get_cm_annotated_step_target(void) {
  return cm_annotated_step_target;
}
PROOF thm get_cm_annotated_step_erasure(void) {
  return cm_annotated_step_erasure;
}
PROOF thm get_cm_annotated_iter_erasure(void) {
  return cm_annotated_iter_erasure;
}
