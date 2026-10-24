#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_lang.h"
#include "userlib/proof_patterns.h"
#include "cmc_preservation_total.h"
#include "cmc_preservation_budget_defs.h"
#include "cmc_annotate_preservation.h"
#include "cmc_preservation_ready_coordinate.h"
#include "cmc_preservation_ready_context.h"
#include "cmc_preservation_invariant_step.h"
#include "cmc_preservation_type_ready.h"
#include "cmc_preservation_fid.h"
#include "cmc_preservation_spill_semantic.h"
#include "cmc_preservation_generation.h"
#include "cmc_preservation_generation_task.h"
#include "cmc_preservation_static_bases.h"
#include "cmc_preservation_tagged_task.h"
#include "cmc_preservation_short_defs.h"
#include "cmc_preservation_code_task.h"
#include "cmc_preservation_code.h"
#include "cmc_preservation_state.h"

#require "userlib/proof_patterns.c"
#require "cmc_annotate_preservation.c"
#require "cmc_preservation_ready_coordinate.c"
#require "cmc_preservation_ready_context.c"
#require "cmc_preservation_invariant_step.c"
#require "cmc_preservation_type_ready.c"
#require "cmc_preservation_fid.c"
#require "cmc_preservation_spill_semantic.c"
#require "cmc_preservation_generation.c"
#require "cmc_preservation_generation_task.c"
#require "cmc_preservation_static_bases.c"
#require "cmc_preservation_tagged_task.c"
#require "cmc_preservation_budget_defs.c"
#require "cmc_preservation_short_defs.c"
#require "cmc_preservation_code.c"
#require "cmc_preservation_code_task.c"
#require "cmc_preservation_state.c"

PROOF static size_t _cmc_preservation_total_axioms_before =
    vector_size(get_all_axioms());

PROOF thm cm_preservation_invariant_def = new_fun_definition(
    `cm_preservation_invariant (p:cm_program) (ast:cm_astate) : bool =
       (cm_task_succeeds (cm_astate_task ast) &&
        cm_annotation_erases (cm_astate_task ast)
          (cm_astate_annotation ast) &&
        cm_annotation_rooted (cm_astate_annotation ast) &&
        cm_task_coordinate_ready p (cm_astate_task ast)
          (cm_astate_annotation ast) &&
        cm_task_layout_ready p (cm_astate_task ast)
          (cm_astate_annotation ast) &&
        cm_task_context_ready (cm_astate_task ast)
          (cm_astate_annotation ast) &&
        cm_task_runtime_invariant p (cm_astate_task ast)
          (cm_astate_annotation ast) &&
        cm_task_type_ready p (cm_astate_task ast)
          (cm_astate_annotation ast) &&
        cm_task_fid_ready p (cm_astate_task ast) &&
        cm_annotation_spill_consistent (cm_astate_annotation ast) &&
        cm_task_generation_safe p (cm_astate_task ast)
          (cm_astate_annotation ast) &&
        cm_task_static_valid (cm_astate_task ast) &&
        cm_task_static_bases p (cm_astate_task ast) &&
        cm_task_tagged_valid (cm_astate_task ast) &&
        cm_task_budget p (cm_astate_task ast)
          (cm_astate_annotation ast) &&
        cm_task_short_ready (cm_astate_task ast) &&
        cm_task_layout p (cm_astate_task ast)
          (cm_astate_annotation ast) &&
        cm_task_target_sim p (cm_astate_task ast)
          (cm_astate_target ast) (cm_astate_annotation ast))`);
PROOF static int _c_cm_preservation_invariant =
    cst_add_const_to_header(`cm_preservation_invariant`);

PROOF static thm cm_prove_succeeds_step_total(void) {
  gnode root = gnode_new_with_ccl(
      `!(task:cm_task).
         cm_task_succeeds task ==>
         cm_task_succeeds (cm_step task)`);
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list cases = BOOL_CASES_TAC(
      introduced, `cm_task_done (task:cm_task)`, "Hpt_done");
  {
    thm fixed = match_mp_rule(spec_rule(
        `task:cm_task`, get_cm_done_step()),
        assume_rule(`cm_task_done (task:cm_task)`));
    thm lifted = ap_term_rule(`cm_task_succeeds`, fixed);
    ACCEPT_TAC(cases[0], eq_mp_rule(sym_rule(lifted),
        assume_rule(`cm_task_succeeds (task:cm_task)`)));
  }
  ACCEPT_TAC(cases[1], match_mp_rule(match_mp_rule(
      spec_rule(`task:cm_task`, cm_task_succeeds_step),
      assume_rule(`~cm_task_done (task:cm_task)`)),
      assume_rule(`cm_task_succeeds (task:cm_task)`)));
  return gnode_prove(root);
}
PROOF static thm cm_succeeds_step_total =
    cm_prove_succeeds_step_total();
PROOF thm get_cm_succeeds_step_total(void) {
  return cm_succeeds_step_total;
}

PROOF static thm cm_prove_start_succeeds_call_ok(void) {
  term start = `CMStartTask (p:cm_program) (input:(int)list)`;
  term call_ok =
      `cm_call_ok (p:cm_program) (cm_program_main p)
        ([]:(cm_value)list) (cm_initial_state p (input:(int)list))`;
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (input:(int)list).
         cm_task_succeeds (CMStartTask p input) ==>
         cm_call_ok p (cm_program_main p) []
           (cm_initial_state p input)`);
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list cases = BOOL_CASES_TAC(
      introduced, call_ok, "Hpt_call_ok");
  ACCEPT_TAC(cases[0], assume_rule(call_ok));
  thm start_not_done = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(get_cm_task_done_def())),
      `~cm_task_done ${start:cm_task}`));
  thm next_succeeds = match_mp_rule(match_mp_rule(
      spec_rule(start, cm_task_succeeds_step), start_not_done),
      assume_rule(`cm_task_succeeds ${start:cm_task}`));
  thm next_not_error = match_mp_rule(specl_rule(TERM_LIST(
      `1i:int`, `cm_step ${start:cm_task}`),
      cm_task_succeeds_not_error), next_succeeds);
  thm impossible = conv_rule(reduce_rewrite_conv(THM_LIST(
      assume_rule(mk_not(call_ok)), get_cm_step_def(),
      get_cm_begin_call_def(), cm_error_task_def,
      get_datatype_injectivity("cm_control"))), next_not_error);
  CONTR_TAC(cases[1], impossible);
  return gnode_prove(root);
}
PROOF static thm cm_start_succeeds_call_ok =
    cm_prove_start_succeeds_call_ok();

PROOF static thm cm_prove_initial_astate_sim(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (input:(int)list).
         cm_astate_sim p (cm_annotated_start p input)`);
  CONV_TAC(root, reduce_rewrite_conv(THM_LIST(
      cm_astate_sim_def, cm_annotated_start_def,
      cm_astate_task_def, cm_astate_target_def,
      cm_astate_annotation_def, cm_task_target_sim_def)));
  return gnode_prove(root);
}
PROOF static thm cm_initial_astate_sim =
    cm_prove_initial_astate_sim();

PROOF static thm cm_pt_initial_fact(
    term proposition, thm_list rules) {
  return eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(rules), proposition));
}

PROOF static thm cm_prove_preservation_initial(void) {
  term start = `CMStartTask (p:cm_program) (input:(int)list)`;
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (input:(int)list).
         cm_wf_program p ==>
         cm_task_succeeds (CMStartTask p input) ==>
         cm_preservation_invariant p (cm_annotated_start p input)`);
  gnode introduced = AUTO_INTROS_TAC(root);
  thm succeeds = assume_rule(`cm_task_succeeds ${start:cm_task}`);
  thm call_ok = match_mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `input:(int)list`),
      cm_start_succeeds_call_ok), succeeds);
  thm erases_raw = specl_rule(TERM_LIST(
      `p:cm_program`, `input:(int)list`),
      cm_annotated_start_erases);
  thm erases = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_annotated_start_def, cm_astate_task_def,
      cm_astate_annotation_def)), erases_raw);
  thm rooted_raw = specl_rule(TERM_LIST(
      `p:cm_program`, `input:(int)list`),
      cm_annotated_start_rooted);
  thm rooted = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_annotated_start_def, cm_astate_annotation_def)), rooted_raw);
  thm coordinate = specl_rule(TERM_LIST(
      `p:cm_program`, `input:(int)list`),
      cm_task_coordinate_initial);
  thm ready = eq_mp_rule(sym_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(cm_task_layout_ready_def)),
      `cm_task_layout_ready (p:cm_program) ${start:cm_task}
        cm_initial_annotation`)), call_ok);
  thm context = specl_rule(TERM_LIST(
      `p:cm_program`, `input:(int)list`), cm_task_context_initial);
  thm runtime = specl_rule(TERM_LIST(
      `p:cm_program`, `input:(int)list`), cm_task_runtime_initial);
  thm type_ready = cm_pt_initial_fact(
      `cm_task_type_ready (p:cm_program) ${start:cm_task}
        cm_initial_annotation`,
      THM_LIST(get_cm_task_type_ready_def()));
  thm fid_ready = cm_pt_initial_fact(
      `cm_task_fid_ready (p:cm_program) ${start:cm_task}`,
      THM_LIST(cm_task_fid_ready_def));
  thm spill = cm_annotation_spill_consistent_initial;
  thm generation = cm_pt_initial_fact(
      `cm_task_generation_safe (p:cm_program) ${start:cm_task}
        cm_initial_annotation`,
      THM_LIST(cm_task_generation_safe_def,
        cm_task_generation_below_def,
        cm_annotation_generation_below_def,
        cm_initial_annotation_def, cm_ann_saved_def,
        cm_spill_frames_generation_below_def));
  thm static_valid = cm_pt_initial_fact(
      `cm_task_static_valid ${start:cm_task}`,
      THM_LIST(cm_task_static_valid_def));
  thm static_bases = specl_rule(TERM_LIST(
      `p:cm_program`, `input:(int)list`),
      cm_task_static_bases_initial);
  thm tagged = specl_rule(TERM_LIST(
      `p:cm_program`, `input:(int)list`), cm_task_tagged_initial);
  thm budget = cm_pt_initial_fact(
      `cm_task_budget (p:cm_program) ${start:cm_task}
        cm_initial_annotation`,
      THM_LIST(get_cm_task_budget_def(), get_cm_cursors_budget_def(),
        cm_initial_annotation_def, cm_ann_cursors_def));
  thm short_ready = specl_rule(TERM_LIST(
      `p:cm_program`, `input:(int)list`),
      cm_task_short_ready_initial);
  thm layout = specl_rule(TERM_LIST(
      `p:cm_program`, `input:(int)list`),
      get_cm_task_layout_initial());
  thm simulation_astate = specl_rule(TERM_LIST(
      `p:cm_program`, `input:(int)list`), cm_initial_astate_sim);
  thm simulation_open = conv_rule(rewrite_conv(THM_LIST(
      cm_astate_sim_def)), simulation_astate);
  thm simulation = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_annotated_start_def, cm_astate_task_def,
      cm_astate_target_def, cm_astate_annotation_def)),
      simulation_open);
  thm packed = list_conj_rule(THM_LIST(
      succeeds, erases, rooted, coordinate, ready, context,
      runtime, type_ready, fid_ready, spill, generation,
      static_valid, static_bases, tagged, budget, short_ready,
      layout, simulation));
  gnode unfolded = CONV_TAC(introduced,
      rewrite_conv(THM_LIST(cm_preservation_invariant_def)));
  gnode normalized = unfolded;
  for (size_t pass = 0; pass < 3; ++pass) {
    normalized = CONV_TAC(normalized,
        reduce_rewrite_conv(THM_LIST(
          cm_annotated_start_def, cm_astate_task_def,
          cm_astate_target_def, cm_astate_annotation_def)));
  }
  ACCEPT_TAC(normalized, packed);
  return gnode_prove(root);
}
PROOF thm cm_preservation_initial =
    cm_prove_preservation_initial();

PROOF thm get_cm_preservation_invariant_def(void) {
  return cm_preservation_invariant_def;
}
PROOF thm get_cm_preservation_initial(void) {
  return cm_preservation_initial;
}

PROOF static int cmc_preservation_total_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_total_axioms_before,
      "initial preservation invariant introduced an axiom");
  ENSURE_COND(!IS_NULL(get_cm_preservation_initial()) &&
      vector_size(hyp(get_cm_preservation_initial())) == 0 &&
      alpha_compare(concl(get_cm_preservation_initial()),
        `!(p:cm_program) (input:(int)list).
           cm_wf_program p ==>
           cm_task_succeeds (CMStartTask p input) ==>
           cm_preservation_invariant p (cm_annotated_start p input)`) == 0,
      "initial preservation theorem has the wrong contract");
  ENSURE_COND(!IS_NULL(get_cm_succeeds_step_total()) &&
      vector_size(hyp(get_cm_succeeds_step_total())) == 0 &&
      alpha_compare(concl(get_cm_succeeds_step_total()),
        `!(task:cm_task).
           cm_task_succeeds task ==>
           cm_task_succeeds (cm_step task)`) == 0,
      "successful task transition has the wrong contract");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_total_checks =
    cmc_preservation_total_final_checks();
