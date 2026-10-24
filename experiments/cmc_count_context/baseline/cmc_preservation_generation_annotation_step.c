#include "proof/proof.h"
#include "userlib/proof.h"
#include "cmc_annotate_model.h"
#include "cmc_preservation_generation_annotation.h"
#include "cmc_preservation_generation_annotation_step.h"
#include "cmc_preservation_spill_semantic.h"

#require "cmc_preservation_generation_annotation.c"

PROOF static size_t _cmc_preservation_generation_annotation_step_axioms_before =
    vector_size(get_all_axioms());
PROOF static thm cm_gap_update_annotation_cond = ispecl_rule(
    TERM_LIST(`condition:bool`, `cm_update_annotation`,
      `yes_update:cm_aupdate`, `no_update:cm_aupdate`),
    get_theorem_by_name("COND_RAND"));
PROOF static thm cm_gap_ann_spills_cond = ispecl_rule(
    TERM_LIST(`condition:bool`, `cm_ann_spills`,
      `yes_annotation:cm_annotation`, `no_annotation:cm_annotation`),
    get_theorem_by_name("COND_RAND"));
PROOF static thm cm_gap_ann_saved_cond = ispecl_rule(
    TERM_LIST(`condition:bool`, `cm_ann_saved`,
      `yes_annotation:cm_annotation`, `no_annotation:cm_annotation`),
    get_theorem_by_name("COND_RAND"));
PROOF static thm cm_gap_spills_generation_cond = beta_norm(ispecl_rule(
    TERM_LIST(`condition:bool`,
      `\spills:(cm_spill)list.
         cm_spills_generation_below (limit:int) spills`,
      `yes_spills:(cm_spill)list`, `no_spills:(cm_spill)list`),
    get_theorem_by_name("COND_RAND")));
PROOF static thm cm_gap_frames_generation_cond = beta_norm(ispecl_rule(
    TERM_LIST(`condition:bool`,
      `\frames:(cm_spill_frame)list.
         cm_spill_frames_generation_below (limit:int) frames`,
      `yes_frames:(cm_spill_frame)list`,
      `no_frames:(cm_spill_frame)list`),
    get_theorem_by_name("COND_RAND")));

PROOF static thm_list cm_gap_payload_rules(void) {
  return THM_LIST(
      cm_update_annotation_def,
      cm_annotation_payload_generation_below_def,
      cm_ann_plain_def, cm_ann_linear_def, cm_ann_push_def,
      cm_ann_replace_def, cm_ann_pop_def, cm_ann_put_spill_def,
      cm_ann_spills_set_def, cm_ann_enter_call_def,
      cm_ann_leave_call_def, cm_ann_spills_def, cm_ann_saved_def,
      cm_spill_put_def, cm_spill_value_def,
      cm_spills_generation_remove,
      cm_spills_generation_below_def,
      cm_spill_frames_generation_below_def,
      cm_spill_frame_spills_def,
      cm_gap_update_annotation_cond,
      cm_gap_ann_spills_cond, cm_gap_ann_saved_cond,
      cm_gap_spills_generation_cond, cm_gap_frames_generation_cond,
      get_theorem_by_name("COND_ID"));
}

PROOF static thm cm_prove_update_r_payload_generation(void) {
  gnode root = gnode_new_with_ccl(
      `!(limit:int) (p:cm_program) (fid:int) (st:cm_src_state)
         (ann:cm_annotation) (expr:cm_expr).
         cm_annotation_payload_generation_below limit ann ==>
         cm_annotation_payload_generation_below limit
           (cm_update_annotation (cm_update_r p fid st ann expr))`);
  gnode introduced = AUTO_INTROS_TAC(root);
  thm old_payload = assume_rule(
      `cm_annotation_payload_generation_below (limit:int)
        (ann:cm_annotation)`);
  thm old_open = conv_rule(rewrite_conv(THM_LIST(
      cm_annotation_payload_generation_below_def)), old_payload);
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
    thm_list rules = cm_gap_payload_rules();
    vector_add(&rules, shape);
    vector_add(&rules, cm_update_r_def);
    vector_add(&rules, old_payload);
    vector_add(&rules, conjunct1_rule(old_open));
    vector_add(&rules, conjunct2_rule(old_open));
    thm result = eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(rules), goal_ccl(branch->g)));
    ACCEPT_TAC(branch, result);
  }
  return gnode_prove(root);
}
PROOF thm cm_update_r_payload_generation =
    cm_prove_update_r_payload_generation();

PROOF static thm cm_prove_update_l_payload_generation(void) {
  gnode root = gnode_new_with_ccl(
      `!(limit:int) (p:cm_program) (fid:int) (st:cm_src_state)
         (ann:cm_annotation) (expr:cm_expr).
         cm_annotation_payload_generation_below limit ann ==>
         cm_annotation_payload_generation_below limit
           (cm_update_annotation (cm_update_l p fid st ann expr))`);
  gnode introduced = AUTO_INTROS_TAC(root);
  thm old_payload = assume_rule(
      `cm_annotation_payload_generation_below (limit:int)
        (ann:cm_annotation)`);
  thm old_open = conv_rule(rewrite_conv(THM_LIST(
      cm_annotation_payload_generation_below_def)), old_payload);
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
    thm_list rules = cm_gap_payload_rules();
    vector_add(&rules, shape);
    vector_add(&rules, cm_update_l_def);
    vector_add(&rules, old_payload);
    vector_add(&rules, conjunct1_rule(old_open));
    vector_add(&rules, conjunct2_rule(old_open));
    thm result = eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(rules), goal_ccl(branch->g)));
    ACCEPT_TAC(branch, result);
  }
  return gnode_prove(root);
}
PROOF thm cm_update_l_payload_generation =
    cm_prove_update_l_payload_generation();

PROOF static thm cm_prove_update_s_payload_generation(void) {
  gnode root = gnode_new_with_ccl(
      `!(limit:int) (p:cm_program) (fid:int) (st:cm_src_state)
         (ann:cm_annotation) (stmt:cm_stmt).
         cm_annotation_payload_generation_below limit ann ==>
         cm_annotation_payload_generation_below limit
           (cm_update_annotation (cm_update_s p fid st ann stmt))`);
  gnode introduced = AUTO_INTROS_TAC(root);
  thm old_payload = assume_rule(
      `cm_annotation_payload_generation_below (limit:int)
        (ann:cm_annotation)`);
  thm old_open = conv_rule(rewrite_conv(THM_LIST(
      cm_annotation_payload_generation_below_def)), old_payload);
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
    thm_list rules = cm_gap_payload_rules();
    vector_add(&rules, shape);
    vector_add(&rules, cm_update_s_def);
    vector_add(&rules, old_payload);
    vector_add(&rules, conjunct1_rule(old_open));
    vector_add(&rules, conjunct2_rule(old_open));
    thm result = eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(rules), goal_ccl(branch->g)));
    ACCEPT_TAC(branch, result);
  }
  return gnode_prove(root);
}
PROOF thm cm_update_s_payload_generation =
    cm_prove_update_s_payload_generation();

PROOF static thm cm_prove_update_v_payload_generation(void) {
  gnode root = gnode_new_with_ccl(
      `!(limit:int) (p:cm_program) (fid:int) (v:cm_value)
         (st:cm_src_state) (ann:cm_annotation) (phase:cm_aphase).
         cm_value_generation_below limit v ==>
         cm_annotation_payload_generation_below limit ann ==>
         cm_annotation_payload_generation_below limit
           (cm_update_annotation
             (cm_update_v p fid v st ann phase))`);
  gnode introduced = AUTO_INTROS_TAC(root);
  thm value_below = assume_rule(
      `cm_value_generation_below (limit:int) (v:cm_value)`);
  thm old_payload = assume_rule(
      `cm_annotation_payload_generation_below (limit:int)
        (ann:cm_annotation)`);
  thm old_open = conv_rule(rewrite_conv(THM_LIST(
      cm_annotation_payload_generation_below_def)), old_payload);
  thm old_spills = conjunct1_rule(old_open);
  term arbitrary_slot = `arbitrary_slot:int`;
  thm removed_any = gen_rule(arbitrary_slot,
      match_mp_rule(specl_rule(TERM_LIST(
        `cm_ann_spills (ann:cm_annotation)`, `limit:int`,
        arbitrary_slot), cm_spills_generation_remove), old_spills));
  thm put_any = gen_rule(arbitrary_slot,
      match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
        `cm_ann_spills (ann:cm_annotation)`, `limit:int`,
        arbitrary_slot, `v:cm_value`), cm_spills_generation_put),
        value_below), old_spills));
  gnode_list cases = DISJ_CASES_TAC(introduced,
      ispec_rule(`phase:cm_aphase`,
        get_datatype_cases("cm_aphase")), "Hphase");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode branch = cases[i];
    while (true) {
      labeled_term_list assumptions = goal_lasmps(branch->g);
      int index = labeled_term_list_index(assumptions, "Hphase");
      if (!is_exists(assumptions[index].tm)) break;
      branch = ASMP_EXISTS_TAC(branch, "Hphase", NULL);
    }
    thm shape = assume_rule(
        goal_lasmps(branch->g)[labeled_term_list_index(
          goal_lasmps(branch->g), "Hphase")].tm);
    thm_list rules = cm_gap_payload_rules();
    vector_add(&rules, shape);
    vector_add(&rules, cm_update_v_def);
    vector_add(&rules, value_below);
    vector_add(&rules, old_payload);
    vector_add(&rules, conjunct1_rule(old_open));
    vector_add(&rules, conjunct2_rule(old_open));
    vector_add(&rules, removed_any);
    vector_add(&rules, put_any);
    thm result = eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(rules), goal_ccl(branch->g)));
    ACCEPT_TAC(branch, result);
  }
  return gnode_prove(root);
}
PROOF thm cm_update_v_payload_generation =
    cm_prove_update_v_payload_generation();

PROOF static thm cm_prove_update_c_payload_generation(void) {
  gnode root = gnode_new_with_ccl(
      `!(limit:int) (p:cm_program) (fid:int) (ctl:cm_control)
         (st:cm_src_state) (phase:cm_aphase)
         (pc:int) (temp:int) (breakpc:int) (continuepc:int)
         (owner:int) (owner_break:int) (owner_continue:int)
         (cursor_rest:(cm_acursor)list) (spills:(cm_spill)list)
         (saved:(cm_spill_frame)list)
         (calls:(cm_call_sim_frame)list).
         (cm_phase_is_call phase ==> ~(saved == [])) ==>
         cm_annotation_payload_generation_below limit
           (CMAnnotation pc temp breakpc continuepc
             (CMACursor phase owner owner_break owner_continue ::
               cursor_rest)
             spills saved calls) ==>
         cm_annotation_payload_generation_below limit
           (cm_update_annotation
             (cm_update_c p fid ctl st
               (CMAnnotation pc temp breakpc continuepc
                 (CMACursor phase owner owner_break owner_continue ::
                   cursor_rest)
                 spills saved calls)
               phase))`);
  gnode introduced = AUTO_INTROS_TAC(root);
  thm call_saved = assume_rule(
      `cm_phase_is_call (phase:cm_aphase) ==>
       ~((saved:(cm_spill_frame)list) == [])`);
  thm old_payload = assume_rule(
      `cm_annotation_payload_generation_below (limit:int)
        (CMAnnotation (pc:int) (temp:int) (breakpc:int)
          (continuepc:int)
          (CMACursor (phase:cm_aphase) (owner:int)
            (owner_break:int) (owner_continue:int) ::
            (cursor_rest:(cm_acursor)list))
          (spills:(cm_spill)list)
          (saved:(cm_spill_frame)list)
          (calls:(cm_call_sim_frame)list))`);
  thm old_open = conv_rule(rewrite_conv(THM_LIST(
      cm_annotation_payload_generation_below_def,
      cm_ann_spills_def, cm_ann_saved_def)), old_payload);
  gnode_list cases = DISJ_CASES_TAC(introduced,
      ispec_rule(`phase:cm_aphase`,
        get_datatype_cases("cm_aphase")), "Hphase");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode branch = cases[i];
    while (true) {
      labeled_term_list assumptions = goal_lasmps(branch->g);
      int index = labeled_term_list_index(assumptions, "Hphase");
      if (!is_exists(assumptions[index].tm)) break;
      branch = ASMP_EXISTS_TAC(branch, "Hphase", NULL);
    }
    thm phase_shape = assume_rule(
        goal_lasmps(branch->g)[labeled_term_list_index(
          goal_lasmps(branch->g), "Hphase")].tm);
    if (i != 22) {
      thm_list rules = cm_gap_payload_rules();
      vector_add(&rules, phase_shape);
      vector_add(&rules, cm_update_c_def);
      vector_add(&rules, old_payload);
      vector_add(&rules, conjunct1_rule(old_open));
      vector_add(&rules, conjunct2_rule(old_open));
      thm result = eqt_elim_rule(apply_conversion(
          reduce_rewrite_conv(rules), goal_ccl(branch->g)));
      ACCEPT_TAC(branch, result);
      continue;
    }
    thm saved_nonempty = conv_rule(reduce_rewrite_conv(THM_LIST(
        phase_shape, cm_phase_is_call_def)), call_saved);
    gnode_list saved_cases = DISJ_CASES_TAC(branch,
        ispec_rule(`saved:(cm_spill_frame)list`,
          get_theorem_by_name("list_CASES")), "Hsaved");
    {
      thm saved_nil = assume_rule(
          goal_lasmps(saved_cases[0]->g)[labeled_term_list_index(
            goal_lasmps(saved_cases[0]->g), "Hsaved")].tm);
      CONTR_TAC(saved_cases[0], contra(saved_nonempty, saved_nil));
    }
    gnode cons = ASMP_EXISTS_TAC(saved_cases[1], "Hsaved", NULL);
    cons = ASMP_EXISTS_TAC(cons, "Hsaved", NULL);
    thm saved_shape = assume_rule(
        goal_lasmps(cons->g)[labeled_term_list_index(
          goal_lasmps(cons->g), "Hsaved")].tm);
    thm restored = conv_rule(reduce_rewrite_conv(THM_LIST(
        saved_shape, cm_spill_frames_generation_below_def,
        get_theorem_by_name("HD"), get_theorem_by_name("TL"))),
        conjunct2_rule(old_open));
    thm_list rules = cm_gap_payload_rules();
    vector_add(&rules, phase_shape);
    vector_add(&rules, saved_shape);
    vector_add(&rules, cm_update_c_def);
    vector_add(&rules, old_payload);
    vector_add(&rules, conjunct1_rule(old_open));
    vector_add(&rules, conjunct2_rule(old_open));
    vector_add(&rules, get_theorem_by_name("HD"));
    vector_add(&rules, get_theorem_by_name("TL"));
    thm target_view = apply_conversion(
        reduce_rewrite_conv(rules), goal_ccl(cons->g));
    ACCEPT_TAC(cons, eq_mp_rule(sym_rule(target_view), restored));
  }
  return gnode_prove(root);
}
PROOF thm cm_update_c_payload_generation =
    cm_prove_update_c_payload_generation();

PROOF static int cmc_preservation_generation_annotation_step_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_generation_annotation_step_axioms_before,
      "cmc_preservation_generation_annotation_step introduced an axiom");
  ENSURE_COND(vector_size(hyp(cm_update_r_payload_generation)) == 0,
      "rvalue annotation payload theorem is not closed");
  ENSURE_COND(vector_size(hyp(cm_update_l_payload_generation)) == 0,
      "lvalue annotation payload theorem is not closed");
  ENSURE_COND(vector_size(hyp(cm_update_s_payload_generation)) == 0,
      "statement annotation payload theorem is not closed");
  ENSURE_COND(vector_size(hyp(cm_update_v_payload_generation)) == 0,
      "value annotation payload theorem is not closed");
  ENSURE_COND(vector_size(hyp(cm_update_c_payload_generation)) == 0,
      "control annotation payload theorem is not closed");
  return 0;
err:
  return -1;
}

PROOF static int _cmc_preservation_generation_annotation_step_checks =
    cmc_preservation_generation_annotation_step_final_checks();
