#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_target_control_regular.h"
#include "cmc_preservation_invariant.h"
#include "cmc_preservation_invariant_transition.h"
#include "cmc_preservation_generation.h"
#include "cmc_preservation_code_task.h"
#include "cmc_preservation_code_control.h"

#require "cmc_preservation_target_machine.c"
#require "cmc_preservation_invariant_transition.c"
#require "cmc_preservation_code_task.c"
#require "cmc_preservation_generation.c"
#require "cmc_preservation_code_control.c"

PROOF static size_t _cmc_preservation_target_control_regular_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm_list cm_target_regular_annotation_rules(void) {
  return THM_LIST(
      cm_ann_pc_def, cm_ann_temp_def, cm_ann_break_def,
      cm_ann_continue_def, cm_ann_cursors_def, cm_ann_spills_def,
      cm_ann_saved_def, cm_ann_calls_def,
      cm_cursor_phase_def, cm_cursor_temp_def,
      cm_cursor_break_def, cm_cursor_continue_def,
      cm_ann_pop_def, get_theorem_by_name("HD"),
      get_theorem_by_name("TL"),
      get_theorem_by_name("NOT_CONS_NIL"));
}

PROOF static thm cm_target_regular_true(
    term proposition, thm_list rules) {
  return eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(rules), proposition));
}

PROOF static thm cm_target_regular_running(
    thm sim, thm control_shape, term concrete_control,
    term annotation, size_t control_index) {
  term values = control_index == 3
      ? `[cm_control_value ${concrete_control:cm_control}]:(cm_value)list`
      : `[]:(cm_value)list`;
  term wanted =
      `cm_running_target_sim (p:cm_program) (fid:int)
        (st:cm_src_state) ${values:(cm_value)list}
        ${annotation:cm_annotation} (target:tvm_task)`;
  thm_list rules = THM_LIST(
      control_shape, cm_task_target_sim_def,
      get_cm_control_kind_def(), get_cm_control_value_def(),
      get_cm_control_status_def());
  thm normalized = conv_rule(reduce_rewrite_conv(rules), sim);
  thm wanted_view = apply_conversion(
      reduce_rewrite_conv(rules), wanted);
  return eq_mp_rule(sym_rule(wanted_view), normalized);
}

PROOF static thm cm_target_regular_halted(
    thm sim, thm control_shape, term concrete_control,
    term annotation) {
  term wanted =
      `cm_halted_target_sim (p:cm_program) (fid:int)
        (st:cm_src_state)
        (cm_control_status ${concrete_control:cm_control}) T
        ${annotation:cm_annotation} (target:tvm_task)`;
  thm_list rules = THM_LIST(
      control_shape, cm_task_target_sim_def,
      get_cm_control_kind_def(), get_cm_control_value_def(),
      get_cm_control_status_def());
  thm normalized = conv_rule(reduce_rewrite_conv(rules), sim);
  thm wanted_view = apply_conversion(
      reduce_rewrite_conv(rules), wanted);
  return eq_mp_rule(sym_rule(wanted_view), normalized);
}

PROOF static void cm_target_regular_accept(
    gnode branch, thm result, thm phase_shape, thm control_shape,
    thm next_ann_equality, thm steps_equality) {
  thm_list rules = cm_target_regular_annotation_rules();
  vector_add(&rules, phase_shape);
  vector_add(&rules, control_shape);
  vector_add(&rules, next_ann_equality);
  vector_add(&rules, steps_equality);
  vector_add(&rules, get_cm_step_def());
  vector_add(&rules, cm_phase_frame_def);
  vector_add(&rules, get_cm_capply_def());
  vector_add(&rules, get_cm_control_kind_def());
  vector_add(&rules, get_cm_control_value_def());
  vector_add(&rules, get_cm_control_status_def());
  vector_add(&rules, cm_annotation_step_def);
  vector_add(&rules, cm_update_c_def);
  vector_add(&rules, cm_update_steps_def);
  vector_add(&rules, cm_update_annotation_def);
  vector_add(&rules, cm_task_target_sim_def);
  vector_add(&rules, cm_cursor_frames_def);
  vector_add(&rules, get_tvm_iter_def());
  thm_list late_rules = cm_target_regular_annotation_rules();
  for (size_t i = 0; i < vector_size(late_rules); ++i) {
    vector_add(&rules, late_rules[i]);
  }
  thm normalized = conv_rule(reduce_rewrite_conv(rules), result);
  thm target_stage = apply_conversion(
      reduce_rewrite_conv(rules), goal_ccl(branch->g));
  thm target_finish = apply_conversion(reduce_rewrite_conv(THM_LIST(
      cm_task_target_sim_def, get_cm_control_kind_def(),
      get_cm_control_value_def(), get_cm_control_status_def())),
      rhs_of(target_stage));
  thm target_view = trans_rule(target_stage, target_finish);
  ACCEPT_TAC(branch, eq_mp_rule(sym_rule(target_view), normalized));
}

PROOF static void cm_target_regular_finish(
    gnode branch, thm phase_shape, thm control_shape,
    term concrete_control, term annotation, size_t control_index,
    thm sim) {
  term task =
      `CMCTask (p:cm_program) (fid:int) (ctl:cm_control)
        (st:cm_src_state)
        (cm_phase_frame (phase:cm_aphase) ::
         cm_cursor_frames (rest:(cm_acursor)list))`;
  term update =
      `cm_annotation_step ${task:cm_task} ${annotation:cm_annotation}`;
  term next_ann = `cm_update_annotation ${update:cm_aupdate}`;
  term steps = `cm_update_steps ${update:cm_aupdate}`;
  thm_list update_rules = cm_target_regular_annotation_rules();
  vector_add(&update_rules, phase_shape);
  vector_add(&update_rules, control_shape);
  vector_add(&update_rules, cm_annotation_step_def);
  vector_add(&update_rules, cm_update_c_def);
  vector_add(&update_rules, get_cm_control_kind_def());
  vector_add(&update_rules, get_cm_control_value_def());
  vector_add(&update_rules, get_cm_control_status_def());
  vector_add(&update_rules, cm_phase_frame_def);
  vector_add(&update_rules, cm_cursor_frames_def);

  thm next_stage = apply_conversion(
      reduce_rewrite_conv(update_rules), next_ann);
  thm_list selector_rules = cm_target_regular_annotation_rules();
  vector_add(&selector_rules, cm_update_annotation_def);
  thm next_finish = apply_conversion(
      reduce_rewrite_conv(selector_rules), rhs_of(next_stage));
  thm next_ann_equality = trans_rule(next_stage, next_finish);

  thm steps_stage = apply_conversion(
      reduce_rewrite_conv(update_rules), steps);
  thm steps_finish = apply_conversion(
      reduce_rewrite_conv(THM_LIST(cm_update_steps_def)),
      rhs_of(steps_stage));
  thm steps_equality = trans_rule(steps_stage, steps_finish);

  thm_list equality_rules = cm_target_regular_annotation_rules();
  vector_add(&equality_rules, next_ann_equality);
  thm same_pc = cm_target_regular_true(
      `cm_ann_pc ${next_ann:cm_annotation} ==
       cm_ann_pc ${annotation:cm_annotation}`, equality_rules);
  thm same_calls = cm_target_regular_true(
      `cm_ann_calls ${next_ann:cm_annotation} ==
       cm_ann_calls ${annotation:cm_annotation}`, equality_rules);
  thm same_spills = cm_target_regular_true(
      `cm_ann_spills ${next_ann:cm_annotation} ==
       cm_ann_spills ${annotation:cm_annotation}`, equality_rules);
  thm same_saved = cm_target_regular_true(
      `cm_ann_saved ${next_ann:cm_annotation} ==
       cm_ann_saved ${annotation:cm_annotation}`, equality_rules);

  thm result;
  if (control_index == 4) {
    thm old_halted = cm_target_regular_halted(
        sim, control_shape, concrete_control, annotation);
    result = specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `st:cm_src_state`,
        `cm_control_status ${concrete_control:cm_control}`, `T:bool`,
        annotation, next_ann, `target:tvm_task`),
        get_cm_target_halted_reannotate());
    result = match_mp_rule(result, same_pc);
    result = match_mp_rule(result, same_calls);
    result = match_mp_rule(result, same_spills);
    result = match_mp_rule(result, same_saved);
    result = match_mp_rule(result, old_halted);
  } else {
    term values = control_index == 3
        ? `[cm_control_value ${concrete_control:cm_control}]:(cm_value)list`
        : `[]:(cm_value)list`;
    thm old_running = cm_target_regular_running(
        sim, control_shape, concrete_control, annotation, control_index);
    result = specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `st:cm_src_state`, values,
        annotation, next_ann, `target:tvm_task`),
        get_cm_target_reannotate());
    result = match_mp_rule(result, same_pc);
    result = match_mp_rule(result, same_calls);
    result = match_mp_rule(result, same_spills);
    result = match_mp_rule(result, same_saved);
    result = match_mp_rule(result, old_running);
  }
  cm_target_regular_accept(branch, result, phase_shape, control_shape,
      next_ann_equality, steps_equality);
}

PROOF static thm cm_prove_target_c_regular_step(void) {
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
      `cm_task_layout p ${task:cm_task} ${annotation:cm_annotation}`,
      `cm_task_target_sim p ${task:cm_task} (target:tvm_task)
        ${annotation:cm_annotation}`,
      `~(cm_control_kind (ctl:cm_control) == 4i)`,
      `~cm_phase_is_halt ${phase:cm_aphase}`,
      `~cm_phase_is_scope ${phase:cm_aphase}`,
      `~cm_phase_is_call ${phase:cm_aphase}`), result_term);
  gnode root = gnode_new_with_ccl(list_mk_forall(free_vars(body), body));
  gnode introduced = AUTO_INTROS_TAC(root);
  thm sim = assume_rule(
      `cm_task_target_sim (p:cm_program) ${task:cm_task}
        (target:tvm_task) ${annotation:cm_annotation}`);
  thm not_exit = assume_rule(
      `~(cm_control_kind (ctl:cm_control) == 4i)`);
  thm not_halt = assume_rule(`~cm_phase_is_halt ${phase:cm_aphase}`);
  thm not_scope = assume_rule(`~cm_phase_is_scope ${phase:cm_aphase}`);
  thm not_call = assume_rule(`~cm_phase_is_call ${phase:cm_aphase}`);

  gnode_list phase_cases = DISJ_CASES_TAC(introduced,
      ispec_rule(phase, get_datatype_cases("cm_aphase")), "Hphase");
  for (size_t i = 0; i < vector_size(phase_cases); ++i) {
    gnode phase_branch = phase_cases[i];
    while (is_exists(goal_lasmps(phase_branch->g)[
        labeled_term_list_index(goal_lasmps(phase_branch->g),
          "Hphase")].tm)) {
      phase_branch = ASMP_EXISTS_TAC(phase_branch, "Hphase", NULL);
    }
    thm phase_shape = assume_rule(goal_lasmps(phase_branch->g)[
        labeled_term_list_index(goal_lasmps(phase_branch->g),
          "Hphase")].tm);
    if (i == 0 || i == 15 || i == 19 || i == 22) {
      thm negative = i == 0 ? not_halt : (i == 22 ? not_call : not_scope);
      thm impossible = conv_rule(reduce_rewrite_conv(THM_LIST(
          phase_shape, cm_phase_is_halt_def, cm_phase_is_scope_def,
          cm_phase_is_call_def)), negative);
      CONTR_TAC(phase_branch, impossible);
      continue;
    }
    gnode_list control_cases = DISJ_CASES_TAC(phase_branch,
        ispec_rule(`ctl:cm_control`, get_datatype_cases("cm_control")),
        "Hcontrol");
    for (size_t j = 0; j < vector_size(control_cases); ++j) {
      gnode control_branch = control_cases[j];
      while (is_exists(goal_lasmps(control_branch->g)[
          labeled_term_list_index(goal_lasmps(control_branch->g),
            "Hcontrol")].tm)) {
        control_branch = ASMP_EXISTS_TAC(
            control_branch, "Hcontrol", NULL);
      }
      thm control_shape = assume_rule(goal_lasmps(control_branch->g)[
          labeled_term_list_index(goal_lasmps(control_branch->g),
            "Hcontrol")].tm);
      if (j == 4) {
        thm impossible = conv_rule(reduce_rewrite_conv(THM_LIST(
            control_shape, get_cm_control_kind_def())), not_exit);
        CONTR_TAC(control_branch, impossible);
        continue;
      }
      cm_target_regular_finish(control_branch, phase_shape, control_shape,
          rhs_of(control_shape), annotation, j, sim);
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_target_c_regular_step = cm_prove_target_c_regular_step();

PROOF thm get_cm_target_c_regular_step(void) {
  return cm_target_c_regular_step;
}

PROOF static int cmc_preservation_target_control_regular_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_target_control_regular_axioms_before,
      "cmc_preservation_target_control_regular introduced an axiom");
  ENSURE_COND(vector_size(hyp(cm_target_c_regular_step)) == 0,
      "regular-control target theorem has hypotheses");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_target_control_regular_checks =
    cmc_preservation_target_control_regular_final_checks();
