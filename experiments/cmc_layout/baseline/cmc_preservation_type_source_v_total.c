#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_type_source_v_total.h"
#include "cmc_preservation_type_source_v_helpers.h"

#require "cmc_preservation_type_source_v_call.c"

PROOF static size_t _cmc_preservation_type_source_v_total_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_prove_v_phase_family_cases(void) {
  gnode root = gnode_new_with_ccl(
      `!(phase:cm_aphase).
         cm_v_phase_family phase == 0i ||
         cm_v_phase_family phase == 1i ||
         cm_v_phase_family phase == 2i ||
         cm_v_phase_family phase == 3i ||
         cm_v_phase_family phase == 4i ||
         cm_v_phase_family phase == 5i`);
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
        shape, get_cm_v_phase_family_def())));
  }
  return gnode_prove(root);
}
PROOF thm cm_v_phase_family_cases =
    cm_prove_v_phase_family_cases();

PROOF static thm cm_prove_v_impossible_family_not_ready(void) {
  term phase = `phase:cm_aphase`;
  term ann = cm_tvs_annotation(phase);
  term task = cm_tvs_task(phase);
  term body = imp_chain(TERM_LIST(
      `cm_task_type_ready (p:cm_program) ${task:cm_task}
        ${ann:cm_annotation}`),
      `~(cm_v_phase_family (phase:cm_aphase) == 5i)`);
  gnode root = gnode_new_with_ccl(list_mk_forall(free_vars(body), body));
  gnode introduced = AUTO_INTROS_TAC(root);
  thm generic_ready = assume_rule(
      `cm_task_type_ready (p:cm_program) ${task:cm_task}
        ${ann:cm_annotation}`);
  thm family = assume_rule(
      `cm_v_phase_family (phase:cm_aphase) == 5i`);
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
    term concrete_phase = rhs_of(shape);
    if (i != 15 && i != 16 && i != 19 && i != 22) {
      thm impossible = conv_rule(reduce_rewrite_conv(THM_LIST(
          shape, get_cm_v_phase_family_def())), family);
      CONTR_TAC(cases[i], impossible);
      continue;
    }
    thm ready = conv_rule(rewrite_conv(THM_LIST(shape)), generic_ready);
    thm components = cm_tvs_components(concrete_phase, ready);
    thm value_ready = cm_tvs_pick_conjunct(components,
        `cm_phase_value_type_ready (p:cm_program) (fid:int)
          ${concrete_phase:cm_aphase} (incoming:cm_value)`);
    thm impossible = conv_rule(reduce_rewrite_conv(THM_LIST(
        get_cm_phase_value_type_ready_def())), value_ready);
    CONTR_TAC(cases[i], impossible);
  }
  return gnode_prove(root);
}
PROOF thm cm_v_impossible_family_not_ready =
    cm_prove_v_impossible_family_not_ready();

PROOF static thm cm_prove_v_type_ready_step_at(void) {
  term phase = `phase:cm_aphase`;
  term ann = cm_tvs_annotation(phase);
  term task = cm_tvs_task(phase);
  term body = imp_chain(TERM_LIST(
      `cm_typed_program (p:cm_program)`,
      `cm_phase_is_halt (phase:cm_aphase) ||
       (0i <= (fid:int) &&
        fid < ilength (cm_program_functions p))`,
      `cm_annotation_erases ${task:cm_task} ${ann:cm_annotation}`,
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
  thm erases = assume_rule(
      `cm_annotation_erases ${task:cm_task} ${ann:cm_annotation}`);
  thm ready = assume_rule(
      `cm_task_type_ready (p:cm_program) ${task:cm_task}
        ${ann:cm_annotation}`);
  thm families = spec_rule(phase, cm_v_phase_family_cases);
  gnode_list cases = DISJ_CASES_TAC(
      introduced, families, "Hfamily");
  thm_list family_theorems = THM_LIST(
      cm_v_scalar_type_ready_step,
      cm_v_binary_type_ready_step,
      cm_v_pointer_type_ready_step,
      cm_v_control_type_ready_step,
      cm_v_call_type_ready_step);
  term_list arguments = TERM_LIST(
      `p:cm_program`, `q:cm_program`, `fid:int`, `incoming:cm_value`,
      `st:cm_src_state`, `ks:(cm_frame)list`, `pc:int`, `temp:int`,
      `breakpc:int`, `continuepc:int`, phase, `parent_temp:int`,
      `parent_break:int`, `parent_continue:int`,
      `rest:(cm_acursor)list`, `spills:(cm_spill)list`,
      `saved:(cm_spill_frame)list`, `calls:(cm_call_sim_frame)list`);
  term_list impossible_arguments = TERM_LIST(
      `p:cm_program`, `q:cm_program`, `fid:int`, `incoming:cm_value`,
      `st:cm_src_state`, `ks:(cm_frame)list`, `pc:int`, `temp:int`,
      `breakpc:int`, `continuepc:int`, `parent_temp:int`,
      `parent_break:int`, `parent_continue:int`,
      `rest:(cm_acursor)list`, `spills:(cm_spill)list`,
      `saved:(cm_spill_frame)list`, `calls:(cm_call_sim_frame)list`,
      phase);
  for (size_t i = 0; i < vector_size(cases); ++i) {
    labeled_term_list assumptions = goal_lasmps(cases[i]->g);
    thm family = assume_rule(assumptions[
        labeled_term_list_index(assumptions, "Hfamily")].tm);
    if (i == 5) {
      thm possible = specl_rule(impossible_arguments,
          cm_v_impossible_family_not_ready);
      possible = mp_rule(possible, ready);
      CONTR_TAC(cases[i], contra(possible, family));
      continue;
    }
    thm proved = specl_rule(arguments, family_theorems[i]);
    if (i == 4) proved = mp_rule(proved, typed);
    proved = mp_rule(proved, bounds);
    if (i == 4) proved = mp_rule(proved, erases);
    proved = mp_rule(proved, ready);
    proved = mp_rule(proved, family);
    ACCEPT_TAC(cases[i], proved);
  }
  return gnode_prove(root);
}
PROOF thm cm_v_type_ready_step_at =
    cm_prove_v_type_ready_step_at();

PROOF static int cmc_preservation_type_source_v_total_final_checks(void) {
  ENSURE_COND(vector_size(hyp(cm_v_phase_family_cases)) == 0 &&
      vector_size(hyp(cm_v_impossible_family_not_ready)) == 0 &&
      vector_size(hyp(cm_v_type_ready_step_at)) == 0,
      "total value type theorem has assumptions");
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_type_source_v_total_axioms_before,
      "total value type proof introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_type_source_v_total_checks =
    cmc_preservation_type_source_v_total_final_checks();
