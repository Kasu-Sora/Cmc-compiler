#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_target_control_halt.h"
#include "cmc_preservation_invariant.h"
#include "cmc_preservation_invariant_transition.h"
#include "cmc_preservation_code_task.h"
#include "cmc_preservation_generation.h"

#require "cmc_preservation_target_machine.c"
#require "cmc_preservation_invariant_transition.c"
#require "cmc_preservation_code_task.c"
#require "cmc_preservation_generation.c"

PROOF static size_t _cmc_preservation_target_control_halt_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm_list cm_target_halt_annotation_rules(void) {
  return THM_LIST(
      cm_ann_pc_def, cm_ann_temp_def, cm_ann_break_def,
      cm_ann_continue_def, cm_ann_cursors_def, cm_ann_spills_def,
      cm_ann_saved_def, cm_ann_calls_def, cm_ann_done_def,
      get_theorem_by_name("HD"), get_theorem_by_name("TL"),
      get_theorem_by_name("NOT_CONS_NIL"));
}

PROOF static thm cm_target_halt_true(
    term proposition, thm_list rules) {
  return eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(rules), proposition));
}

PROOF static thm cm_prove_target_c_halt_step(void) {
  term annotation = `ann:cm_annotation`;
  term task =
      `CMCTask (p:cm_program) (fid:int) (ctl:cm_control)
        (st:cm_src_state) (ks:(cm_frame)list)`;
  term update =
      `cm_annotation_step ${task:cm_task} ${annotation:cm_annotation}`;
  term result_term =
      `cm_task_target_sim (p:cm_program) (cm_step ${task:cm_task})
        (tvm_iter (cm_update_steps ${update:cm_aupdate})
          (target:tvm_task))
        (cm_update_annotation ${update:cm_aupdate})`;
  term body = imp_chain(TERM_LIST(
      `cm_wf_program (p:cm_program)`,
      `cm_runtime_step_ready p ${task:cm_task} ${annotation:cm_annotation}`,
      `cm_task_runtime_invariant p ${task:cm_task}
        ${annotation:cm_annotation}`,
      `cm_task_generation_safe p ${task:cm_task}
        ${annotation:cm_annotation}`,
      `cm_task_layout p ${task:cm_task} ${annotation:cm_annotation}`,
      `cm_task_target_sim p ${task:cm_task} (target:tvm_task)
        ${annotation:cm_annotation}`,
      `cm_control_kind (ctl:cm_control) == 4i`), result_term);
  gnode root = gnode_new_with_ccl(list_mk_forall(free_vars(body), body));
  gnode leaf = AUTO_INTROS_TAC(root);
  thm sim = assume_rule(
      `cm_task_target_sim (p:cm_program) ${task:cm_task}
        (target:tvm_task) ${annotation:cm_annotation}`);
  thm exit_kind = assume_rule(
      `cm_control_kind (ctl:cm_control) == 4i`);
  term next_ann = `cm_update_annotation ${update:cm_aupdate}`;
  term steps = `cm_update_steps ${update:cm_aupdate}`;

  thm_list update_rules = THM_LIST(
      exit_kind, cm_annotation_step_def, cm_ann_done_def);
  thm next_stage = apply_conversion(
      reduce_rewrite_conv(update_rules), next_ann);
  thm next_finish = apply_conversion(
      reduce_rewrite_conv(THM_LIST(cm_update_annotation_def)),
      rhs_of(next_stage));
  thm next_equal = trans_rule(next_stage, next_finish);
  thm steps_stage = apply_conversion(
      reduce_rewrite_conv(update_rules), steps);
  thm steps_finish = apply_conversion(
      reduce_rewrite_conv(THM_LIST(cm_update_steps_def)),
      rhs_of(steps_stage));
  thm steps_equal = trans_rule(steps_stage, steps_finish);

  thm_list equality_rules = cm_target_halt_annotation_rules();
  vector_add(&equality_rules, next_equal);
  thm same_pc = cm_target_halt_true(
      `cm_ann_pc ${next_ann:cm_annotation} ==
       cm_ann_pc ${annotation:cm_annotation}`, equality_rules);
  thm same_calls = cm_target_halt_true(
      `cm_ann_calls ${next_ann:cm_annotation} ==
       cm_ann_calls ${annotation:cm_annotation}`, equality_rules);
  thm same_spills = cm_target_halt_true(
      `cm_ann_spills ${next_ann:cm_annotation} ==
       cm_ann_spills ${annotation:cm_annotation}`, equality_rules);
  thm same_saved = cm_target_halt_true(
      `cm_ann_saved ${next_ann:cm_annotation} ==
       cm_ann_saved ${annotation:cm_annotation}`, equality_rules);

  term status = `cm_control_status (ctl:cm_control)`;
  term old_halted_term =
      `cm_halted_target_sim (p:cm_program) (fid:int)
        (st:cm_src_state) ${status:int} T
        ${annotation:cm_annotation} (target:tvm_task)`;
  thm_list sim_rules = THM_LIST(
      exit_kind, cm_task_target_sim_def);
  thm old_halted_raw = conv_rule(
      reduce_rewrite_conv(sim_rules), sim);
  thm old_halted_view = apply_conversion(
      reduce_rewrite_conv(sim_rules), old_halted_term);
  thm old_halted = eq_mp_rule(
      sym_rule(old_halted_view), old_halted_raw);
  thm reannotated = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`, status,
      `T:bool`, annotation, next_ann, `target:tvm_task`),
      get_cm_target_halted_reannotate());
  reannotated = match_mp_rule(reannotated, same_pc);
  reannotated = match_mp_rule(reannotated, same_calls);
  reannotated = match_mp_rule(reannotated, same_spills);
  reannotated = match_mp_rule(reannotated, same_saved);
  reannotated = match_mp_rule(reannotated, old_halted);
  thm deactivated = match_mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`, status,
      next_ann, `target:tvm_task`),
      get_cm_target_halted_deactivate()), reannotated);

  thm_list finish_rules = THM_LIST(
      exit_kind, next_equal, steps_equal, get_cm_step_def(),
      cm_annotation_step_def, cm_update_steps_def,
      cm_update_annotation_def, cm_task_target_sim_def,
      get_tvm_iter_def());
  thm normalized = conv_rule(reduce_rewrite_conv(THM_LIST(
      next_equal, cm_halted_target_sim_def,
      cm_active_spill_frames_def)), deactivated);
  thm target_stage = apply_conversion(
      reduce_rewrite_conv(finish_rules), goal_ccl(leaf->g));
  thm target_finish = apply_conversion(reduce_rewrite_conv(THM_LIST(
      cm_task_target_sim_def, cm_halted_target_sim_def,
      cm_active_spill_frames_def)), rhs_of(target_stage));
  thm target_view = trans_rule(target_stage, target_finish);
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), normalized));
  return gnode_prove(root);
}
PROOF thm cm_target_c_halt_step = cm_prove_target_c_halt_step();

PROOF thm get_cm_target_c_halt_step(void) {
  return cm_target_c_halt_step;
}

PROOF static int cmc_preservation_target_control_halt_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_target_control_halt_axioms_before,
      "cmc_preservation_target_control_halt introduced an axiom");
  ENSURE_COND(vector_size(hyp(cm_target_c_halt_step)) == 0,
      "halt-control target theorem has hypotheses");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_target_control_halt_checks =
    cmc_preservation_target_control_halt_final_checks();
