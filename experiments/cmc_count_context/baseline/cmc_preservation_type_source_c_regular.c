#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_type_source_c_regular.h"
#include "cmc_preservation_type_source_c_helpers.h"

#require "cmc_preservation_type_source_c_support.c"

PROOF static size_t _cmc_preservation_type_source_c_regular_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_prove_c_regular_type_ready_step(void) {
  term phase = `phase:cm_aphase`;
  term ann = cm_tvs_annotation(phase);
  term task = cm_tcs_task(phase);
  term body = imp_chain(TERM_LIST(
      `cm_task_type_ready (p:cm_program) ${task:cm_task}
        ${ann:cm_annotation}`,
      `cm_c_phase_family (phase:cm_aphase) == 0i`),
      `cm_task_type_ready (p:cm_program)
        (cm_step ${task:cm_task})
        (cm_update_annotation
          (cm_annotation_step ${task:cm_task}
            ${ann:cm_annotation}))`);
  gnode root = gnode_new_with_ccl(list_mk_forall(free_vars(body), body));
  gnode introduced = cm_tcs_nonexit_branch(AUTO_INTROS_TAC(root));
  thm generic_ready = assume_rule(
      `cm_task_type_ready (p:cm_program) ${task:cm_task}
        ${ann:cm_annotation}`);
  thm family = assume_rule(
      `cm_c_phase_family (phase:cm_aphase) == 0i`);
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
    if (i == 0 || i == 16 || i == 19 || i == 22) {
      thm impossible = conv_rule(reduce_rewrite_conv(THM_LIST(
          shape, get_cm_c_phase_family_def())), family);
      CONTR_TAC(cases[i], impossible);
      continue;
    }
    thm ready = conv_rule(rewrite_conv(THM_LIST(shape)), generic_ready);
    thm components = cm_tcs_components(concrete_phase, ready);
    thm same_program = cm_tvs_pick_conjunct(components,
        `(q:cm_program) == (p:cm_program)`);
    thm control_ready = cm_tvs_pick_conjunct(components,
        `cm_control_type_ready (p:cm_program) (fid:int)
          (control:cm_control)`);
    thm old_next = cm_tvs_trivial(
        `cm_phase_next_fid (fid:int) ${concrete_phase:cm_aphase} == fid`,
        THM_LIST(cm_phase_next_fid_def));
    thm next_view = beta_norm(ap_term_rule(
        `\next_fid:int.
           cm_control_type_ready (p:cm_program) next_fid
             (control:cm_control)`, old_next));
    thm next_control_ready = eq_mp_rule(sym_rule(next_view),
        control_ready);
    term next_st = `st:cm_src_state`;
    if (i == 15) {
      term env = cm_tvs_phase_arg(concrete_phase, 4, 0);
      term regions = cm_tvs_phase_arg(concrete_phase, 4, 1);
      next_st = `cm_restore_scope (st:cm_src_state)
        ${env:int->int->cm_value} ${regions:(cm_region)list}`;
    }
    thm proved = cm_tcs_pop_control(concrete_phase,
        `control:cm_control`, next_st, ready, next_control_ready,
        THM_LIST(same_program));
    cm_tcs_accept(cases[i], proved, shape, THM_LIST(same_program));
  }
  return gnode_prove(root);
}
PROOF thm cm_c_regular_type_ready_step =
    cm_prove_c_regular_type_ready_step();

PROOF static int cmc_preservation_type_source_c_regular_final_checks(void) {
  ENSURE_COND(vector_size(hyp(cm_c_regular_type_ready_step)) == 0,
      "regular control type theorem has assumptions");
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_type_source_c_regular_axioms_before,
      "regular control type proof introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_type_source_c_regular_checks =
    cmc_preservation_type_source_c_regular_final_checks();
