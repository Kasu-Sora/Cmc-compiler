#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_target_control_scope.h"
#include "cmc_preservation_generation_step_apply.h"
#include "cmc_preservation_invariant.h"
#include "cmc_preservation_generation.h"
#include "cmc_preservation_call_value.h"
#include "cmc_preservation_invariant_transition.h"
#include "cmc_preservation_code_task.h"
#include "cmc_preservation_code_control.h"

#require "cmc_preservation_target_restore.c"
#require "cmc_preservation_target_jump_valid.c"
#require "cmc_preservation_generation_step_apply.c"
#require "cmc_preservation_code_control.c"
#require "cmc_preservation_generation.c"
#require "cmc_preservation_invariant_transition.c"
#require "cmc_preservation_code_task.c"

PROOF static size_t _cmc_preservation_target_control_scope_axioms_before =
    vector_size(get_all_axioms());

PROOF static term cm_target_scope_app_arg_from_right(
    term application, size_t offset) {
  for (size_t i = 0; i < offset; ++i) {
    application = dest_comb(application).tm1;
  }
  return dest_comb(application).tm2;
}

PROOF static term cm_target_scope_constructor_arg(
    term constructor, size_t arity, size_t index) {
  return cm_target_scope_app_arg_from_right(
      constructor, arity - index - 1);
}

PROOF static thm cm_target_scope_pick(thm fact, term wanted) {
  if (alpha_compare(concl(fact), wanted) == 0) return fact;
  if (!is_conj(concl(fact))) return empty_theorem;
  thm left = cm_target_scope_pick(conjunct1_rule(fact), wanted);
  if (!IS_NULL(left)) return left;
  return cm_target_scope_pick(conjunct2_rule(fact), wanted);
}

PROOF static thm_list cm_target_scope_annotation_rules(void) {
  return THM_LIST(
      cm_ann_plain_def, cm_ann_replace_def, cm_ann_pop_def,
      cm_ann_pc_def, cm_ann_temp_def, cm_ann_break_def,
      cm_ann_continue_def, cm_ann_cursors_def, cm_ann_spills_def,
      cm_ann_saved_def, cm_ann_calls_def,
      cm_cursor_phase_def, cm_cursor_temp_def,
      cm_cursor_break_def, cm_cursor_continue_def,
      get_theorem_by_name("HD"), get_theorem_by_name("TL"),
      get_theorem_by_name("NOT_CONS_NIL"));
}

PROOF static thm cm_target_scope_true(term proposition, thm_list rules) {
  return eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(rules), proposition));
}

PROOF static thm_list cm_target_scope_layout_rules(
    thm phase_shape, thm control_shape, thm extra_shape,
    thm jump_alignment) {
  thm_list rules = cm_target_scope_annotation_rules();
  vector_add(&rules, phase_shape);
  vector_add(&rules, control_shape);
  if (!IS_NULL(extra_shape)) vector_add(&rules, extra_shape);
  if (!IS_NULL(jump_alignment)) vector_add(&rules, jump_alignment);
  vector_add(&rules, cm_task_layout_def);
  vector_add(&rules, cm_task_code_def);
  vector_add(&rules, cm_control_phase_code_def);
  vector_add(&rules, cm_normal_cont_code_def);
  vector_add(&rules, cm_cursor_code_def);
  vector_add(&rules, cm_normal_phase_code_def);
  vector_add(&rules, get_cm_control_kind_def());
  vector_add(&rules, get_theorem_by_name("APPEND"));
  vector_add(&rules, get_theorem_by_name("APPEND_NIL"));
  return rules;
}

PROOF static thm cm_target_scope_values_below(
    thm control_below, thm control_shape, term concrete_control,
    size_t control_index) {
  term limit = `cm_state_nextgen (st:cm_src_state)`;
  if (control_index != 3) {
    return eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(cm_values_generation_below_def)),
        `cm_values_generation_below ${limit:int} ([]:(cm_value)list)`));
  }
  thm concrete_below = conv_rule(
      rewrite_conv(THM_LIST(control_shape)), control_below);
  thm value_below = match_mp_rule(specl_rule(TERM_LIST(
      concrete_control, limit), cm_control_value_generation_below),
      concrete_below);
  return eqt_elim_rule(apply_conversion(reduce_rewrite_conv(THM_LIST(
      cm_values_generation_below_def, value_below)),
      `cm_values_generation_below ${limit:int}
        [cm_control_value ${concrete_control:cm_control}]`));
}

PROOF static void cm_target_scope_accept(
    gnode branch, thm result, thm phase_shape,
    thm control_shape, thm extra_shape, thm next_ann_equality,
    thm steps_equality) {
  thm_list rules = cm_target_scope_annotation_rules();
  vector_add(&rules, phase_shape);
  vector_add(&rules, control_shape);
  if (!IS_NULL(extra_shape)) vector_add(&rules, extra_shape);
  vector_add(&rules, next_ann_equality);
  vector_add(&rules, steps_equality);
  vector_add(&rules, get_cm_step_def());
  vector_add(&rules, get_cm_capply_def());
  vector_add(&rules, get_cm_control_kind_def());
  vector_add(&rules, get_cm_control_value_def());
  vector_add(&rules, get_cm_control_status_def());
  vector_add(&rules, cm_annotation_step_def);
  vector_add(&rules, cm_update_c_def);
  vector_add(&rules, cm_update_steps_def);
  vector_add(&rules, cm_update_annotation_def);
  vector_add(&rules, cm_task_target_sim_def);
  vector_add(&rules, cm_phase_frame_def);
  vector_add(&rules, cm_cursor_frames_def);
  vector_add(&rules, get_tvm_iter_def());
  thm_list late_annotation_rules = cm_target_scope_annotation_rules();
  for (size_t i = 0; i < vector_size(late_annotation_rules); ++i) {
    vector_add(&rules, late_annotation_rules[i]);
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

PROOF static thm cm_target_scope_running_sim(
    thm sim, thm phase_shape, thm control_shape,
    term concrete_control, term annotation, size_t control_index) {
  term values = control_index == 3
      ? `[cm_control_value ${concrete_control:cm_control}]:(cm_value)list`
      : `[]:(cm_value)list`;
  term wanted =
      `cm_running_target_sim (p:cm_program) (fid:int)
        (st:cm_src_state) ${values:(cm_value)list}
        ${annotation:cm_annotation} (target:tvm_task)`;
  thm_list rules = THM_LIST(
      control_shape, cm_phase_frame_def, cm_task_target_sim_def,
      get_cm_control_kind_def(), get_cm_control_value_def(),
      get_cm_control_status_def());
  thm normalized = conv_rule(reduce_rewrite_conv(rules), sim);
  thm wanted_view = apply_conversion(
      reduce_rewrite_conv(rules), wanted);
  (void)phase_shape;
  return eq_mp_rule(sym_rule(wanted_view), normalized);
}

PROOF static thm cm_target_scope_halted_sim(
    thm sim, thm phase_shape, thm control_shape,
    term concrete_control, term annotation) {
  term wanted =
      `cm_halted_target_sim (p:cm_program) (fid:int)
        (st:cm_src_state) (cm_control_status ${concrete_control:cm_control})
        T ${annotation:cm_annotation} (target:tvm_task)`;
  thm_list rules = THM_LIST(
      control_shape, cm_phase_frame_def, cm_task_target_sim_def,
      get_cm_control_kind_def(), get_cm_control_value_def(),
      get_cm_control_status_def());
  thm normalized = conv_rule(reduce_rewrite_conv(rules), sim);
  thm wanted_view = apply_conversion(
      reduce_rewrite_conv(rules), wanted);
  (void)phase_shape;
  return eq_mp_rule(sym_rule(wanted_view), normalized);
}

PROOF static thm cm_target_scope_spill_for_annotation(
    thm spill_below, term transport_ann) {
  term wanted =
      `cm_spill_frames_generation_below (cm_state_nextgen (st:cm_src_state))
        (cm_active_spill_frames (fid:int) st
          ${transport_ann:cm_annotation})`;
  thm_list rules = cm_target_scope_annotation_rules();
  vector_add(&rules, cm_active_spill_frames_def);
  thm normalized = conv_rule(reduce_rewrite_conv(rules), spill_below);
  thm wanted_view = apply_conversion(reduce_rewrite_conv(rules), wanted);
  return eq_mp_rule(sym_rule(wanted_view), normalized);
}

PROOF static void cm_target_scope_finish(
    gnode branch, size_t phase_index, size_t control_index,
    term concrete_phase, term concrete_control, term annotation,
    thm phase_shape, thm control_shape, thm extra_shape,
    thm jump_alignment, bool jumps, term jump_pc,
    term oldenv, term oldregions,
    thm prefix, thm tag_below, thm spill_below,
    thm control_below, thm wf, thm layout, thm sim) {
  term task =
      `CMCTask (p:cm_program) (fid:int) (ctl:cm_control)
        (st:cm_src_state)
        (cm_phase_frame (phase:cm_aphase) ::
         cm_cursor_frames (rest:(cm_acursor)list))`;
  term update =
      `cm_annotation_step ${task:cm_task} ${annotation:cm_annotation}`;
  term next_ann = `cm_update_annotation ${update:cm_aupdate}`;
  thm_list update_rules = cm_target_scope_annotation_rules();
  vector_add(&update_rules, phase_shape);
  vector_add(&update_rules, control_shape);
  if (!IS_NULL(extra_shape)) vector_add(&update_rules, extra_shape);
  vector_add(&update_rules, cm_annotation_step_def);
  vector_add(&update_rules, cm_update_c_def);
  vector_add(&update_rules, cm_update_annotation_def);
  vector_add(&update_rules, cm_update_steps_def);
  vector_add(&update_rules, get_cm_control_kind_def());
  vector_add(&update_rules, get_cm_control_value_def());
  vector_add(&update_rules, get_cm_control_status_def());
  vector_add(&update_rules, cm_update_annotation_def);
  vector_add(&update_rules, cm_update_steps_def);
  thm_list late_update_rules = cm_target_scope_annotation_rules();
  for (size_t i = 0; i < vector_size(late_update_rules); ++i) {
    vector_add(&update_rules, late_update_rules[i]);
  }
  vector_add(&update_rules, cm_phase_frame_def);
  vector_add(&update_rules, cm_cursor_frames_def);
  vector_add(&update_rules, cm_update_annotation_def);
  vector_add(&update_rules, cm_update_steps_def);
  thm_list final_update_rules = cm_target_scope_annotation_rules();
  for (size_t i = 0; i < vector_size(final_update_rules); ++i) {
    vector_add(&update_rules, final_update_rules[i]);
  }
  thm next_ann_stage = apply_conversion(
      reduce_rewrite_conv(update_rules), next_ann);
  thm_list next_ann_finish_rules = cm_target_scope_annotation_rules();
  vector_add(&next_ann_finish_rules, cm_update_annotation_def);
  thm next_ann_finish = apply_conversion(
      reduce_rewrite_conv(next_ann_finish_rules), rhs_of(next_ann_stage));
  thm next_ann_equality = trans_rule(next_ann_stage, next_ann_finish);
  vector_add(&update_rules, next_ann_equality);
  term steps = `cm_update_steps ${update:cm_aupdate}`;
  thm steps_stage = apply_conversion(
      reduce_rewrite_conv(update_rules), steps);
  thm steps_finish = apply_conversion(
      reduce_rewrite_conv(THM_LIST(cm_update_steps_def)),
      rhs_of(steps_stage));
  thm steps_equality = trans_rule(steps_stage, steps_finish);
  vector_add(&update_rules, steps_equality);

  term values = control_index == 3
      ? `[cm_control_value ${concrete_control:cm_control}]:(cm_value)list`
      : `[]:(cm_value)list`;
  thm values_below = cm_target_scope_values_below(
      control_below, control_shape, concrete_control, control_index);
  term transport_ann = annotation;
  term transport_target = `target:tvm_task`;
  thm old_running = empty_theorem;

  if (control_index != 4) {
    old_running = cm_target_scope_running_sim(
        sim, phase_shape, control_shape, concrete_control, annotation,
        control_index);
  }

  if (jumps) {
    thm opened_layout = conv_rule(reduce_rewrite_conv(
        cm_target_scope_layout_rules(
          phase_shape, control_shape, extra_shape, jump_alignment)), layout);
    thm code_at = conjunct1_rule(opened_layout);
    thm target_valid = match_mp_rule(cm_model_jump_valid, wf);
    target_valid = match_mp_rule(target_valid, code_at);
    target_valid = match_mp_rule(target_valid,
        cm_target_scope_true(dest_imp(concl(target_valid)).tm1,
          THM_LIST(get_tvm_opcode_is_target_def())));
    term suffix = cm_target_scope_app_arg_from_right(concl(code_at), 0);
    term jump_rest = cm_target_scope_app_arg_from_right(suffix, 0);
    term code_at_ann_term =
        `cm_code_at (cm_model_code (p:cm_program))
          (cm_ann_pc ${annotation:cm_annotation})
          (TVMInst TVMJmpOp ${jump_pc:int} ::
           ${jump_rest:(tvm_inst)list})`;
    thm code_at_ann_view = apply_conversion(
        reduce_rewrite_conv(cm_target_scope_annotation_rules()),
        code_at_ann_term);
    thm code_at_ann = eq_mp_rule(sym_rule(code_at_ann_view), code_at);
    thm jumped = specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `st:cm_src_state`, values,
        annotation, `target:tvm_task`, jump_pc, jump_rest),
        cm_target_jump);
    jumped = match_mp_rule(jumped, code_at_ann);
    jumped = match_mp_rule(jumped, target_valid);
    jumped = match_mp_rule(jumped, old_running);
    transport_ann =
        `cm_ann_plain ${jump_pc:int}
          (cm_ann_temp ${annotation:cm_annotation})
          (cm_ann_break ${annotation:cm_annotation})
          (cm_ann_continue ${annotation:cm_annotation})
          ${annotation:cm_annotation}`;
    transport_target = `tvm_iter 1 (target:tvm_task)`;
    old_running = jumped;
  }

  thm transport_spills = cm_target_scope_spill_for_annotation(
      spill_below, transport_ann);
  thm pc_equal = cm_target_scope_true(
      `cm_ann_pc ${next_ann:cm_annotation} ==
       cm_ann_pc ${transport_ann:cm_annotation}`, update_rules);
  thm calls_equal = cm_target_scope_true(
      `cm_ann_calls ${next_ann:cm_annotation} ==
       cm_ann_calls ${transport_ann:cm_annotation}`, update_rules);
  thm spills_equal = cm_target_scope_true(
      `cm_ann_spills ${next_ann:cm_annotation} ==
       cm_ann_spills ${transport_ann:cm_annotation}`, update_rules);
  thm saved_equal = cm_target_scope_true(
      `cm_ann_saved ${next_ann:cm_annotation} ==
       cm_ann_saved ${transport_ann:cm_annotation}`, update_rules);

  thm result;
  if (control_index == 4) {
    thm old_halted = cm_target_scope_halted_sim(
        sim, phase_shape, control_shape, concrete_control, annotation);
    result = specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `st:cm_src_state`, oldenv, oldregions,
        transport_ann, next_ann, transport_target,
        `cm_control_status ${concrete_control:cm_control}`),
        cm_target_restore_scope_halted);
    result = match_mp_rule(result, prefix);
    result = match_mp_rule(result, tag_below);
    result = match_mp_rule(result, transport_spills);
    result = match_mp_rule(result, pc_equal);
    result = match_mp_rule(result, calls_equal);
    result = match_mp_rule(result, spills_equal);
    result = match_mp_rule(result, saved_equal);
    result = match_mp_rule(result, old_halted);
  } else {
    result = specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `st:cm_src_state`, oldenv, oldregions,
        transport_ann, next_ann, transport_target, values),
        cm_target_restore_scope);
    result = match_mp_rule(result, prefix);
    result = match_mp_rule(result, tag_below);
    result = match_mp_rule(result, transport_spills);
    result = match_mp_rule(result, values_below);
    result = match_mp_rule(result, pc_equal);
    result = match_mp_rule(result, calls_equal);
    result = match_mp_rule(result, spills_equal);
    result = match_mp_rule(result, saved_equal);
    result = match_mp_rule(result, old_running);
  }
  cm_target_scope_accept(
      branch, result, phase_shape, control_shape, extra_shape,
      next_ann_equality, steps_equality);
  (void)phase_index;
  (void)concrete_phase;
}

PROOF static thm cm_prove_target_c_scope_step(void) {
  term phase = `phase:cm_aphase`;
  term cursors =
      `CMACursor ${phase:cm_aphase} (owner:int) (saved_break:int)
        (saved_continue:int) :: (rest:(cm_acursor)list)`;
  term frames =
      `cm_phase_frame ${phase:cm_aphase} ::
       cm_cursor_frames (rest:(cm_acursor)list)`;
  term ann =
      `CMAnnotation (pc:int) (temp:int) (breakpc:int) (continuepc:int)
        ${cursors:(cm_acursor)list} (spills:(cm_spill)list)
        (saved:(cm_spill_frame)list) (calls:(cm_call_sim_frame)list)`;
  term task =
      `CMCTask (p:cm_program) (fid:int) (ctl:cm_control)
        (st:cm_src_state) ${frames:(cm_frame)list}`;
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
      `cm_task_generation_safe p ${task:cm_task} ${ann:cm_annotation}`,
      `cm_task_layout p ${task:cm_task} ${ann:cm_annotation}`,
      `cm_task_target_sim p ${task:cm_task} (target:tvm_task)
        ${ann:cm_annotation}`,
      `~(cm_control_kind (ctl:cm_control) == 4i)`,
      `cm_phase_is_scope ${phase:cm_aphase}`), result_term);
  gnode root = gnode_new_with_ccl(list_mk_forall(free_vars(body), body));
  gnode introduced = AUTO_INTROS_TAC(root);
  thm wf = assume_rule(`cm_wf_program (p:cm_program)`);
  thm readiness = assume_rule(
      `cm_runtime_step_ready (p:cm_program) ${task:cm_task}
        ${ann:cm_annotation}`);
  thm runtime = assume_rule(
      `cm_task_runtime_invariant (p:cm_program) ${task:cm_task}
        ${ann:cm_annotation}`);
  thm generation = assume_rule(
      `cm_task_generation_safe (p:cm_program) ${task:cm_task}
        ${ann:cm_annotation}`);
  thm layout = assume_rule(
      `cm_task_layout (p:cm_program) ${task:cm_task}
        ${ann:cm_annotation}`);
  thm sim = assume_rule(
      `cm_task_target_sim (p:cm_program) ${task:cm_task}
        (target:tvm_task) ${ann:cm_annotation}`);
  thm not_exit = assume_rule(
      `~(cm_control_kind (ctl:cm_control) == 4i)`);
  thm scope_family = assume_rule(`cm_phase_is_scope ${phase:cm_aphase}`);

  gnode_list phase_cases = DISJ_CASES_TAC(introduced,
      ispec_rule(phase, get_datatype_cases("cm_aphase")), "Hphase");
  for (size_t i = 0; i < vector_size(phase_cases); ++i) {
    gnode phase_branch = phase_cases[i];
    while (is_exists(goal_lasmps(phase_branch->g)[
        labeled_term_list_index(goal_lasmps(phase_branch->g), "Hphase")].tm)) {
      phase_branch = ASMP_EXISTS_TAC(phase_branch, "Hphase", NULL);
    }
    thm phase_shape = assume_rule(goal_lasmps(phase_branch->g)[
        labeled_term_list_index(goal_lasmps(phase_branch->g), "Hphase")].tm);
    if (i != 15 && i != 19) {
      thm impossible = conv_rule(reduce_rewrite_conv(THM_LIST(
          phase_shape, cm_phase_is_scope_def)), scope_family);
      CONTR_TAC(phase_branch, impossible);
      continue;
    }
    term concrete_phase = rhs_of(phase_shape);
    size_t arity = i == 15 ? 4 : 6;
    term oldenv = cm_target_scope_constructor_arg(concrete_phase, arity,
        i == 15 ? 0 : 2);
    term oldregions = cm_target_scope_constructor_arg(concrete_phase, arity,
        i == 15 ? 1 : 3);
    thm break_alignment = empty_theorem;
    thm continue_alignment = empty_theorem;
    if (i == 19) {
      thm ready_step = conv_rule(
          rewrite_conv(THM_LIST(cm_runtime_step_ready_def)), readiness);
      thm layout_step = conv_rule(reduce_rewrite_conv(THM_LIST(
          cm_task_layout_ready_def)), ready_step);
      thm ready_open = conv_rule(reduce_rewrite_conv(THM_LIST(
          cm_c_layout_ready_def, cm_ann_cursors_def,
          cm_cursor_phase_def, get_theorem_by_name("HD"),
          get_theorem_by_name("NOT_CONS_NIL"))), layout_step);
      thm code_ready = cm_target_scope_pick(ready_open,
          `cm_c_code_ready (p:cm_program) (fid:int)
            ${ann:cm_annotation} ${phase:cm_aphase}`);
      thm code_ready_open = conv_rule(
          rewrite_conv(THM_LIST(cm_c_code_ready_def)), code_ready);
      term guard = cm_target_scope_constructor_arg(concrete_phase, 6, 0);
      term loop_body = cm_target_scope_constructor_arg(
          concrete_phase, 6, 1);
      term loop_env = cm_target_scope_constructor_arg(
          concrete_phase, 6, 2);
      term loop_regions = cm_target_scope_constructor_arg(
          concrete_phase, 6, 3);
      term loop_start = cm_target_scope_constructor_arg(
          concrete_phase, 6, 4);
      term loop_end = cm_target_scope_constructor_arg(
          concrete_phase, 6, 5);
      thm alignments = specl_rule(TERM_LIST(
          guard, loop_body, loop_env, loop_regions, loop_start, loop_end),
          code_ready_open);
      alignments = match_mp_rule(alignments, phase_shape);
      alignments = conv_rule(reduce_rewrite_conv(THM_LIST(
          cm_ann_break_def, cm_ann_continue_def)), alignments);
      break_alignment = conjunct1_rule(alignments);
      continue_alignment = conjunct1_rule(conjunct2_rule(alignments));
    }

    thm runtime_open = conv_rule(reduce_rewrite_conv(THM_LIST(
        phase_shape, cm_task_runtime_invariant_def,
        cm_runtime_stack_def, cm_phase_is_call_def,
        cm_phase_is_scope_def, cm_phase_oldregions_def,
        cm_cursor_phase_def, cm_ann_cursors_def, cm_ann_spills_def,
        cm_ann_saved_def, cm_ann_calls_def,
        get_theorem_by_name("HD"), get_theorem_by_name("TL"),
        get_theorem_by_name("NOT_CONS_NIL"))), runtime);
    thm prefix = cm_target_scope_pick(runtime_open,
        `cm_region_prefix_safe (p:cm_program)
          (cm_state_regions (st:cm_src_state)) (fid:int) (cm_state_fp st)
          (cm_state_regions st) ${oldregions:(cm_region)list}`);

    thm generation_open = conv_rule(reduce_rewrite_conv(THM_LIST(
        cm_task_generation_safe_def, cm_task_generation_below_def,
        cm_annotation_generation_below_def,
        cm_phase_frame_def, cm_cursor_frames_def,
        cm_ann_spills_def, cm_ann_saved_def)), generation);
    thm state_generation = cm_target_scope_pick(generation_open,
        `cm_state_generation_below (p:cm_program) (fid:int)
          (st:cm_src_state)`);
    thm tag_below = cm_target_scope_pick(
        conv_rule(rewrite_conv(THM_LIST(
          cm_state_generation_below_def)), state_generation),
        `cm_tags_generation_below (cm_state_nextgen (st:cm_src_state))
          (cm_state_tags st)`);
    tag_below = match_mp_rule(specl_rule(TERM_LIST(
        `st:cm_src_state`, `cm_state_nextgen (st:cm_src_state)`),
        get_cm_state_tags_generation_from_all()), tag_below);
    thm spill_below = cm_target_scope_pick(generation_open,
        `cm_spill_frames_generation_below (cm_state_nextgen st)
          (cm_active_spill_frames (fid:int) st ${ann:cm_annotation})`);
    thm control_below = cm_target_scope_pick(generation_open,
        `cm_control_generation_below (cm_state_nextgen st)
          (ctl:cm_control)`);

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
      term concrete_control = rhs_of(control_shape);
      if (j == 4 || j == 5) {
        thm impossible;
        if (j == 4) {
          impossible = conv_rule(reduce_rewrite_conv(THM_LIST(
              control_shape, get_cm_control_kind_def())), not_exit);
        } else {
          impossible = conv_rule(reduce_rewrite_conv(THM_LIST(
              phase_shape, control_shape, cm_runtime_step_ready_def,
              cm_task_layout_ready_def, cm_c_layout_ready_def,
              cm_c_phase_ready_def, cm_c_regular_ready_def,
              cm_ann_cursors_def, cm_cursor_phase_def,
              get_cm_control_kind_def(), get_theorem_by_name("HD"),
              get_theorem_by_name("TL"),
              get_theorem_by_name("NOT_CONS_NIL"))), readiness);
        }
        CONTR_TAC(control_branch, impossible);
        continue;
      }

      if (i == 15 && j == 0) {
        term jump = cm_target_scope_constructor_arg(
            concrete_phase, 4, 2);
        term jump_pc = cm_target_scope_constructor_arg(
            concrete_phase, 4, 3);
        gnode_list jump_cases = BOOL_CASES_TAC(
            control_branch, jump, "Hblock_jump");
        for (size_t k = 0; k < vector_size(jump_cases); ++k) {
          thm jump_shape = assume_rule(goal_lasmps(jump_cases[k]->g)[
              labeled_term_list_index(goal_lasmps(jump_cases[k]->g),
                "Hblock_jump")].tm);
          cm_target_scope_finish(jump_cases[k], i, j,
              concrete_phase, concrete_control, ann,
              phase_shape, control_shape, jump_shape, empty_theorem,
              k == 0, jump_pc, oldenv, oldregions,
              prefix, tag_below, spill_below, control_below,
              wf, layout, sim);
        }
        continue;
      }

      bool jumps = i == 19 && j <= 2;
      term jump_pc = `pc:int`;
      if (jumps) {
        jump_pc = cm_target_scope_constructor_arg(
            concrete_phase, 6, j == 1 ? 5 : 4);
      }
      thm jump_alignment = empty_theorem;
      if (jumps) {
        jump_alignment = j == 1
            ? break_alignment : continue_alignment;
      }
      cm_target_scope_finish(control_branch, i, j,
          concrete_phase, concrete_control, ann,
          phase_shape, control_shape, empty_theorem, jump_alignment,
          jumps, jump_pc, oldenv, oldregions,
          prefix, tag_below, spill_below, control_below,
          wf, layout, sim);
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_target_c_scope_step = cm_prove_target_c_scope_step();

PROOF thm get_cm_target_c_scope_step(void) {
  return cm_target_c_scope_step;
}

PROOF static int cmc_preservation_target_control_scope_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_target_control_scope_axioms_before,
      "cmc_preservation_target_control_scope introduced an axiom");
  ENSURE_COND(vector_size(hyp(cm_target_c_scope_step)) == 0,
      "scope-control target theorem has hypotheses");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_target_control_scope_checks =
    cmc_preservation_target_control_scope_final_checks();
