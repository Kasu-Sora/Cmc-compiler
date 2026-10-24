#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_type_source_c_total.h"
#include "cmc_preservation_type_source_c_helpers.h"

#require "cmc_preservation_type_source_c_call.c"

PROOF static size_t _cmc_preservation_type_source_c_total_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_prove_c_phase_family_cases(void) {
  gnode root = gnode_new_with_ccl(
      `!(phase:cm_aphase).
         cm_c_phase_family phase == 0i ||
         cm_c_phase_family phase == 1i ||
         cm_c_phase_family phase == 2i ||
         cm_c_phase_family phase == 3i ||
         cm_c_phase_family phase == 4i`);
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list cases = DISJ_CASES_TAC(introduced,
      ispec_rule(`phase:cm_aphase`, get_datatype_cases("cm_aphase")),
      "Hphase");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    while (true) {
      labeled_term_list assumptions = goal_lasmps(cases[i]->g);
      int shape_index = labeled_term_list_index(assumptions, "Hphase");
      if (!is_exists(assumptions[shape_index].tm)) break;
      cases[i] = ASMP_EXISTS_TAC(cases[i], "Hphase", NULL);
    }
    thm shape = assume_rule(goal_lasmps(cases[i]->g)[
        labeled_term_list_index(goal_lasmps(cases[i]->g), "Hphase")].tm);
    CONV_TAC(cases[i], reduce_rewrite_conv(THM_LIST(
        shape, get_cm_c_phase_family_def())));
  }
  return gnode_prove(root);
}
PROOF thm cm_c_phase_family_cases =
    cm_prove_c_phase_family_cases();

PROOF static thm cm_prove_c_halt_type_ready_step(void) {
  term phase = `phase:cm_aphase`;
  term ann = cm_tvs_annotation(phase);
  term task = cm_tcs_task(phase);
  term body = imp_chain(TERM_LIST(
      `cm_task_type_ready (p:cm_program) ${task:cm_task}
        ${ann:cm_annotation}`,
      `cm_c_phase_family (phase:cm_aphase) == 4i`),
      `cm_task_type_ready (p:cm_program)
        (cm_step ${task:cm_task})
        (cm_update_annotation
          (cm_annotation_step ${task:cm_task}
            ${ann:cm_annotation}))`);
  gnode root = gnode_new_with_ccl(list_mk_forall(free_vars(body), body));
  gnode introduced = cm_tcs_nonexit_branch(AUTO_INTROS_TAC(root));
  thm family = assume_rule(
      `cm_c_phase_family (phase:cm_aphase) == 4i`);
  gnode_list cases = DISJ_CASES_TAC(introduced,
      ispec_rule(phase, get_datatype_cases("cm_aphase")), "Hphase");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    while (true) {
      labeled_term_list assumptions = goal_lasmps(cases[i]->g);
      int shape_index = labeled_term_list_index(assumptions, "Hphase");
      if (!is_exists(assumptions[shape_index].tm)) break;
      cases[i] = ASMP_EXISTS_TAC(cases[i], "Hphase", NULL);
    }
    thm shape = assume_rule(goal_lasmps(cases[i]->g)[
        labeled_term_list_index(goal_lasmps(cases[i]->g), "Hphase")].tm);
    if (i != 0) {
      thm impossible = conv_rule(reduce_rewrite_conv(THM_LIST(
          shape, get_cm_c_phase_family_def())), family);
      CONTR_TAC(cases[i], impossible);
      continue;
    }
    gnode_list control_cases = DISJ_CASES_TAC(cases[i],
        ispec_rule(`control:cm_control`,
          get_datatype_cases("cm_control")), "Hcontrol");
    for (size_t j = 0; j < vector_size(control_cases); ++j) {
      while (true) {
        labeled_term_list assumptions =
            goal_lasmps(control_cases[j]->g);
        int shape_index =
            labeled_term_list_index(assumptions, "Hcontrol");
        if (!is_exists(assumptions[shape_index].tm)) break;
        control_cases[j] = ASMP_EXISTS_TAC(
            control_cases[j], "Hcontrol", NULL);
      }
      thm control_shape = assume_rule(goal_lasmps(control_cases[j]->g)[
          labeled_term_list_index(
            goal_lasmps(control_cases[j]->g), "Hcontrol")].tm);
      thm_list rules = cm_tcs_rules(shape);
      vector_add(&rules, control_shape);
      thm target_first = apply_conversion(
          reduce_rewrite_conv(rules), goal_ccl(control_cases[j]->g));
      thm target_second = apply_conversion(
          reduce_rewrite_conv(rules), rhs_of(target_first));
      ACCEPT_TAC(control_cases[j],
          eqt_elim_rule(trans_rule(target_first, target_second)));
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_c_halt_type_ready_step =
    cm_prove_c_halt_type_ready_step();

PROOF static thm cm_prove_c_type_ready_step_at(void) {
  term phase = `phase:cm_aphase`;
  term ann = cm_tvs_annotation(phase);
  term task = cm_tcs_task(phase);
  term body = imp_chain(TERM_LIST(
      `cm_typed_program (p:cm_program)`,
      `cm_phase_is_halt (phase:cm_aphase) ||
       (0i <= (fid:int) &&
        fid < ilength (cm_program_functions p))`,
      `cm_task_type_ready p ${task:cm_task} ${ann:cm_annotation}`),
      `cm_task_type_ready (p:cm_program)
        (cm_step ${task:cm_task})
        (cm_update_annotation
          (cm_annotation_step ${task:cm_task}
            ${ann:cm_annotation}))`);
  gnode root = gnode_new_with_ccl(list_mk_forall(free_vars(body), body));
  gnode introduced = AUTO_INTROS_TAC(root);
  thm typed = assume_rule(`cm_typed_program (p:cm_program)`);
  thm bounds = assume_rule(
      `cm_phase_is_halt (phase:cm_aphase) ||
       (0i <= (fid:int) &&
        fid < ilength (cm_program_functions (p:cm_program)))`);
  thm ready = assume_rule(
      `cm_task_type_ready (p:cm_program) ${task:cm_task}
        ${ann:cm_annotation}`);
  gnode_list cases = DISJ_CASES_TAC(introduced,
      spec_rule(phase, cm_c_phase_family_cases), "Hfamily");
  term_list arguments = TERM_LIST(
      `p:cm_program`, `q:cm_program`, `fid:int`, `control:cm_control`,
      `st:cm_src_state`, `ks:(cm_frame)list`, `pc:int`, `temp:int`,
      `breakpc:int`, `continuepc:int`, phase, `parent_temp:int`,
      `parent_break:int`, `parent_continue:int`,
      `rest:(cm_acursor)list`, `spills:(cm_spill)list`,
      `saved:(cm_spill_frame)list`, `calls:(cm_call_sim_frame)list`);
  for (size_t i = 0; i < vector_size(cases); ++i) {
    labeled_term_list assumptions = goal_lasmps(cases[i]->g);
    thm family = assume_rule(assumptions[
        labeled_term_list_index(assumptions, "Hfamily")].tm);
    thm proved = specl_rule(arguments, cm_c_regular_type_ready_step);
    if (i == 0) {
      proved = mp_rule(proved, ready);
      proved = mp_rule(proved, family);
    } else if (i == 1 || i == 2) {
      term structural =
          `cm_c_phase_family (phase:cm_aphase) == 1i ||
           cm_c_phase_family phase == 2i`;
      thm structural_fact = mp_rule(taut_rule(
          mk_imp(concl(family), structural)), family);
      proved = specl_rule(arguments, cm_c_struct_type_ready_step);
      proved = mp_rule(proved, bounds);
      proved = mp_rule(proved, ready);
      proved = mp_rule(proved, structural_fact);
    } else if (i == 3) {
      proved = specl_rule(arguments, cm_c_call_type_ready_step);
      proved = mp_rule(proved, typed);
      proved = mp_rule(proved, ready);
      proved = mp_rule(proved, family);
    } else {
      proved = specl_rule(arguments, cm_c_halt_type_ready_step);
      proved = mp_rule(proved, ready);
      proved = mp_rule(proved, family);
    }
    ACCEPT_TAC(cases[i], proved);
  }
  return gnode_prove(root);
}
PROOF thm cm_c_type_ready_step_at =
    cm_prove_c_type_ready_step_at();

PROOF static int cmc_preservation_type_source_c_total_final_checks(void) {
  ENSURE_COND(vector_size(hyp(cm_c_phase_family_cases)) == 0 &&
      vector_size(hyp(cm_c_halt_type_ready_step)) == 0 &&
      vector_size(hyp(cm_c_type_ready_step_at)) == 0,
      "total control type theorem has assumptions");
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_type_source_c_total_axioms_before,
      "total control type proof introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_type_source_c_total_checks =
    cmc_preservation_type_source_c_total_final_checks();
