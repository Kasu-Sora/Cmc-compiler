#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_target_control_total.h"
#include "cmc_preservation_target_control_halt.h"
#include "cmc_preservation_target_control_scope.h"
#include "cmc_preservation_target_control_regular.h"
#include "cmc_preservation_target_control_call.h"
#include "cmc_preservation_invariant_transition.h"
#include "cmc_preservation_code_control.h"
#include "cmc_preservation_code_task.h"

#require "cmc_preservation_target_control_halt.c"
#require "cmc_preservation_target_control_scope.c"
#require "cmc_preservation_target_control_regular.c"
#require "cmc_preservation_target_control_call.c"

PROOF static size_t _cmc_preservation_target_control_total_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_target_c_total_apply(
    thm rule, const thm_list premises) {
  for (size_t i = 0; i < vector_size(premises); ++i) {
    rule = match_mp_rule(rule, premises[i]);
  }
  return rule;
}

PROOF static void cm_target_c_total_accept(
    const gnode branch, const thm_list rules, const thm result) {
  thm normalized = conv_rule(reduce_rewrite_conv(rules), result);
  thm target_view = apply_conversion(
      reduce_rewrite_conv(rules), goal_ccl(branch->g));
  ACCEPT_TAC(branch, eq_mp_rule(sym_rule(target_view), normalized));
}

PROOF static thm cm_prove_target_c_step(void) {
  term phase = `phase:cm_aphase`;
  term cursors =
      `CMACursor ${phase:cm_aphase} (owner:int) (saved_break:int)
        (saved_continue:int) :: (rest:(cm_acursor)list)`;
  term frames =
      `cm_phase_frame ${phase:cm_aphase} ::
       cm_cursor_frames (rest:(cm_acursor)list)`;
  term annotation =
      `CMAnnotation (pc:int) (temp:int) (breakpc:int) (continuepc:int)
        ${cursors:(cm_acursor)list} (spills:(cm_spill)list)
        (saved:(cm_spill_frame)list) (calls:(cm_call_sim_frame)list)`;
  term task =
      `CMCTask (p:cm_program) (fid:int) (ctl:cm_control)
        (st:cm_src_state) ${frames:(cm_frame)list}`;
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
      `cm_task_type_ready p ${task:cm_task} ${annotation:cm_annotation}`,
      `cm_tagged_span_valid (st:cm_src_state)`,
      `cm_task_layout p ${task:cm_task} ${annotation:cm_annotation}`,
      `cm_task_target_sim p ${task:cm_task} (target:tvm_task)
        ${annotation:cm_annotation}`), result_term);
  gnode root = gnode_new_with_ccl(list_mk_forall(free_vars(body), body));
  gnode introduced = AUTO_INTROS_TAC(root);
  thm wf = assume_rule(`cm_wf_program (p:cm_program)`);
  thm readiness = assume_rule(
      `cm_runtime_step_ready (p:cm_program) ${task:cm_task}
        ${annotation:cm_annotation}`);
  thm runtime = assume_rule(
      `cm_task_runtime_invariant (p:cm_program) ${task:cm_task}
        ${annotation:cm_annotation}`);
  thm generation = assume_rule(
      `cm_task_generation_safe (p:cm_program) ${task:cm_task}
        ${annotation:cm_annotation}`);
  thm typed = assume_rule(
      `cm_task_type_ready (p:cm_program) ${task:cm_task}
        ${annotation:cm_annotation}`);
  thm tagged = assume_rule(`cm_tagged_span_valid (st:cm_src_state)`);
  thm layout = assume_rule(
      `cm_task_layout (p:cm_program) ${task:cm_task}
        ${annotation:cm_annotation}`);
  thm sim = assume_rule(
      `cm_task_target_sim (p:cm_program) ${task:cm_task}
        (target:tvm_task) ${annotation:cm_annotation}`);
  thm_list common = THM_LIST(wf, readiness, runtime, generation, layout, sim);

  gnode_list exit_cases = BOOL_CASES_TAC(
      introduced, `cm_control_kind (ctl:cm_control) == 4i`, "Hexit");
  thm exit_kind = assume_rule(
      `cm_control_kind (ctl:cm_control) == 4i`);
  thm halted = cm_target_c_total_apply(
      get_cm_target_c_halt_step(), common);
  halted = match_mp_rule(halted, exit_kind);
  ACCEPT_TAC(exit_cases[0], halted);

  gnode nonexit = exit_cases[1];
  thm not_exit = assume_rule(
      `~(cm_control_kind (ctl:cm_control) == 4i)`);
  gnode_list phase_cases = DISJ_CASES_TAC(nonexit,
      ispec_rule(phase, get_datatype_cases("cm_aphase")), "Hphase");
  for (size_t i = 0; i < vector_size(phase_cases); ++i) {
    gnode branch = phase_cases[i];
    while (is_exists(goal_lasmps(branch->g)[
        labeled_term_list_index(goal_lasmps(branch->g), "Hphase")].tm)) {
      branch = ASMP_EXISTS_TAC(branch, "Hphase", NULL);
    }
    thm phase_shape = assume_rule(goal_lasmps(branch->g)[
        labeled_term_list_index(goal_lasmps(branch->g), "Hphase")].tm);
    thm_list shape_rules = THM_LIST(phase_shape, cm_phase_frame_def);

    if (i == 0) {
      thm impossible = conv_rule(reduce_rewrite_conv(THM_LIST(
          phase_shape, not_exit, cm_runtime_step_ready_def,
          cm_task_layout_ready_def, cm_c_layout_ready_def,
          cm_c_phase_ready_def, cm_ann_cursors_def,
          cm_cursor_phase_def, get_theorem_by_name("HD"),
          get_theorem_by_name("TL"),
          get_theorem_by_name("NOT_CONS_NIL"))), readiness);
      CONTR_TAC(branch, impossible);
      continue;
    }

    if (i == 15 || i == 19) {
      thm scope_family = eqt_elim_rule(apply_conversion(
          reduce_rewrite_conv(THM_LIST(
            phase_shape, cm_phase_is_scope_def)),
          `cm_phase_is_scope ${phase:cm_aphase}`));
      thm scoped = cm_target_c_total_apply(
          get_cm_target_c_scope_step(), common);
      scoped = match_mp_rule(scoped, not_exit);
      scoped = match_mp_rule(scoped, scope_family);
      cm_target_c_total_accept(branch, shape_rules, scoped);
      continue;
    }

    if (i == 22) {
      thm shaped_runtime = conv_rule(
          rewrite_conv(shape_rules), runtime);
      thm shaped_generation = conv_rule(
          rewrite_conv(shape_rules), generation);
      thm shaped_typed = conv_rule(rewrite_conv(shape_rules), typed);
      thm shaped_layout = conv_rule(rewrite_conv(shape_rules), layout);
      thm shaped_sim = conv_rule(rewrite_conv(shape_rules), sim);
      thm allowed = conv_rule(reduce_rewrite_conv(THM_LIST(
          phase_shape, not_exit, cm_runtime_step_ready_def,
          cm_task_layout_ready_def, cm_c_layout_ready_def,
          cm_c_phase_ready_def, cm_ann_cursors_def,
          cm_cursor_phase_def, get_theorem_by_name("HD"),
          get_theorem_by_name("TL"),
          get_theorem_by_name("NOT_CONS_NIL"))), readiness);
      thm allowed_control = conjunct1_rule(allowed);
      thm called = cm_target_c_total_apply(
          get_cm_target_c_call_step(), THM_LIST(
            shaped_runtime, shaped_generation, shaped_typed, tagged,
            shaped_layout, shaped_sim, allowed_control));
      cm_target_c_total_accept(branch, shape_rules, called);
      continue;
    }

    thm not_halt = eqf_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(phase_shape, cm_phase_is_halt_def)),
        `cm_phase_is_halt ${phase:cm_aphase}`));
    thm not_scope = eqf_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(phase_shape, cm_phase_is_scope_def)),
        `cm_phase_is_scope ${phase:cm_aphase}`));
    thm not_call = eqf_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(phase_shape, cm_phase_is_call_def)),
        `cm_phase_is_call ${phase:cm_aphase}`));
    thm regular = cm_target_c_total_apply(
        get_cm_target_c_regular_step(), common);
    regular = match_mp_rule(regular, not_exit);
    regular = match_mp_rule(regular, not_halt);
    regular = match_mp_rule(regular, not_scope);
    regular = match_mp_rule(regular, not_call);
    cm_target_c_total_accept(branch, shape_rules, regular);
  }
  return gnode_prove(root);
}
PROOF thm cm_target_c_step = cm_prove_target_c_step();

PROOF thm get_cm_target_c_step(void) {
  return cm_target_c_step;
}

PROOF static int cmc_preservation_target_control_total_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_target_control_total_axioms_before,
      "cmc_preservation_target_control_total introduced an axiom");
  ENSURE_COND(vector_size(hyp(cm_target_c_step)) == 0,
      "total control target theorem has hypotheses");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_target_control_total_checks =
    cmc_preservation_target_control_total_final_checks();
