#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_target_value_total.h"
#include "cmc_preservation_target_value_scalar_total.h"
#include "cmc_preservation_target_value_binary_total.h"
#include "cmc_preservation_target_value_pointer_total.h"
#include "cmc_preservation_target_value_control_total.h"
#include "cmc_preservation_target_value_call_total.h"
#include "cmc_preservation_type_source_v_total.h"

#require "cmc_preservation_target_value_scalar_total.c"
#require "cmc_preservation_target_value_binary_total.c"
#require "cmc_preservation_target_value_pointer_total.c"
#require "cmc_preservation_target_value_control_total.c"
#require "cmc_preservation_target_value_call_total.c"
#require "cmc_preservation_type_source_v_total.c"

PROOF static size_t _cmc_preservation_target_value_total_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_value_total_apply(thm result, thm_list premises) {
  for (size_t i = 0; i < vector_size(premises); ++i) {
    result = match_mp_rule(result, premises[i]);
  }
  return result;
}

PROOF static thm cm_prove_target_v_step(void) {
  term phase = `phase:cm_aphase`;
  term cursors =
      `CMACursor ${phase:cm_aphase} (owner:int) (saved_break:int)
        (saved_continue:int) :: (rest:(cm_acursor)list)`;
  term frames =
      `cm_phase_frame ${phase:cm_aphase} ::
       cm_cursor_frames (rest:(cm_acursor)list)`;
  term task =
      `CMVTask (p:cm_program) (fid:int) (incoming:cm_value)
        (st:cm_src_state) ${frames:(cm_frame)list}`;
  term ann =
      `CMAnnotation (pc:int) (temp:int) (breakpc:int) (continuepc:int)
        ${cursors:(cm_acursor)list} (spills:(cm_spill)list)
        (saved:(cm_spill_frame)list) (calls:(cm_call_sim_frame)list)`;
  term update = `cm_annotation_step ${task:cm_task} ${ann:cm_annotation}`;
  term result_term =
      `cm_task_target_sim (p:cm_program) (cm_step ${task:cm_task})
        (tvm_iter (cm_update_steps ${update:cm_aupdate})
          (target:tvm_task))
        (cm_update_annotation ${update:cm_aupdate})`;
  term body = imp_chain(TERM_LIST(
      `cm_wf_program (p:cm_program)`,
      `cm_runtime_step_ready p ${task:cm_task} ${ann:cm_annotation}`,
      `cm_task_runtime_invariant p ${task:cm_task} ${ann:cm_annotation}`,
      `cm_task_type_ready p ${task:cm_task} ${ann:cm_annotation}`,
      `cm_task_fid_ready p ${task:cm_task}`,
      `cm_annotation_spill_consistent ${ann:cm_annotation}`,
      `cm_task_generation_safe p ${task:cm_task} ${ann:cm_annotation}`,
      `cm_task_tagged_valid ${task:cm_task}`,
      `cm_task_layout p ${task:cm_task} ${ann:cm_annotation}`,
      `cm_task_target_sim p ${task:cm_task} (target:tvm_task)
        ${ann:cm_annotation}`), result_term);
  gnode root = gnode_new_with_ccl(list_mk_forall(free_vars(body), body));
  gnode introduced = AUTO_INTROS_TAC(root);

  thm_list premises = THM_LIST(
      assume_rule(`cm_wf_program (p:cm_program)`),
      assume_rule(`cm_runtime_step_ready (p:cm_program) ${task:cm_task}
        ${ann:cm_annotation}`),
      assume_rule(`cm_task_runtime_invariant (p:cm_program)
        ${task:cm_task} ${ann:cm_annotation}`),
      assume_rule(`cm_task_type_ready (p:cm_program) ${task:cm_task}
        ${ann:cm_annotation}`),
      assume_rule(`cm_task_fid_ready (p:cm_program) ${task:cm_task}`),
      assume_rule(`cm_annotation_spill_consistent ${ann:cm_annotation}`),
      assume_rule(`cm_task_generation_safe (p:cm_program)
        ${task:cm_task} ${ann:cm_annotation}`),
      assume_rule(`cm_task_tagged_valid ${task:cm_task}`),
      assume_rule(`cm_task_layout (p:cm_program) ${task:cm_task}
        ${ann:cm_annotation}`),
      assume_rule(`cm_task_target_sim (p:cm_program) ${task:cm_task}
        (target:tvm_task) ${ann:cm_annotation}`));
  thm families = spec_rule(phase, cm_v_phase_family_cases);
  gnode_list cases = DISJ_CASES_TAC(
      introduced, families, "Hfamily");
  thm_list family_theorems = THM_LIST(
      get_cm_target_v_scalar_step(),
      get_cm_target_v_binary_step(),
      get_cm_target_v_pointer_step(),
      get_cm_target_v_control_step(),
      get_cm_target_v_call_step());
  term_list arguments = TERM_LIST(
      `target:tvm_task`, `p:cm_program`, `fid:int`,
      `incoming:cm_value`, `st:cm_src_state`, `pc:int`, `temp:int`,
      `breakpc:int`, `continuepc:int`, phase, `owner:int`,
      `saved_break:int`, `saved_continue:int`,
      `rest:(cm_acursor)list`, `spills:(cm_spill)list`,
      `saved:(cm_spill_frame)list`, `calls:(cm_call_sim_frame)list`);
  term_list impossible_arguments = TERM_LIST(
      `p:cm_program`, `p:cm_program`, `fid:int`,
      `incoming:cm_value`, `st:cm_src_state`,
      `cm_cursor_frames (rest:(cm_acursor)list)`,
      `pc:int`, `temp:int`, `breakpc:int`, `continuepc:int`,
      `owner:int`, `saved_break:int`, `saved_continue:int`,
      `rest:(cm_acursor)list`, `spills:(cm_spill)list`,
      `saved:(cm_spill_frame)list`, `calls:(cm_call_sim_frame)list`, phase);

  for (size_t i = 0; i < vector_size(cases); ++i) {
    labeled_term_list assumptions = goal_lasmps(cases[i]->g);
    thm family = assume_rule(assumptions[
        labeled_term_list_index(assumptions, "Hfamily")].tm);
    if (i == 5) {
      thm possible = specl_rule(impossible_arguments,
          cm_v_impossible_family_not_ready);
      possible = match_mp_rule(possible, premises[3]);
      CONTR_TAC(cases[i], not_elim_rule(possible, family));
      continue;
    }
    thm proved = specl_rule(arguments, family_theorems[i]);
    proved = cm_value_total_apply(proved, premises);
    proved = match_mp_rule(proved, family);
    ACCEPT_TAC(cases[i], proved);
  }
  return gnode_prove(root);
}

PROOF thm cm_target_v_step = cm_prove_target_v_step();

PROOF thm get_cm_target_v_step(void) {
  return cm_target_v_step;
}

PROOF static int cmc_preservation_target_value_total_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_target_value_total_axioms_before,
      "cmc_preservation_target_value_total introduced an axiom");
  ENSURE_COND(vector_size(hyp(cm_target_v_step)) == 0,
      "total value target theorem is not closed");
  return 0;
err:
  return 1;
}
PROOF static int _cmc_preservation_target_value_total_checks =
    cmc_preservation_target_value_total_final_checks();
