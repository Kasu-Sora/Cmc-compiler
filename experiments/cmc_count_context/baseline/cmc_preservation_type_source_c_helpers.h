#pragma once

#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_type_source_c_support.h"
#include "cmc_preservation_type_source_v_helpers.h"

PROOF static term cm_tcs_task(term phase) {
  return `CMCTask (q:cm_program) (fid:int) (control:cm_control)
    (st:cm_src_state) (cm_phase_frame ${phase:cm_aphase} ::
      (ks:(cm_frame)list))`;
}

PROOF static term cm_tcs_next_annotation(term phase) {
  term task = cm_tcs_task(phase);
  term ann = cm_tvs_annotation(phase);
  return `cm_update_annotation
    (cm_annotation_step ${task:cm_task} ${ann:cm_annotation})`;
}

PROOF static gnode cm_tcs_nonexit_branch(gnode introduced) {
  gnode_list cases = BOOL_CASES_TAC(introduced,
      `cm_control_kind (control:cm_control) == 4i`, "Htype_control_exit");
  CONV_TAC(cases[0], reduce_rewrite_conv(THM_LIST(
      assume_rule(`cm_control_kind (control:cm_control) == 4i`),
      get_cm_step_def(), get_cm_task_type_ready_def())));
  return cases[1];
}

PROOF static thm_list cm_tcs_rules(thm shape) {
  return THM_LIST(
      assume_rule(`~(cm_control_kind (control:cm_control) == 4i)`),
      shape, get_cm_step_def(), get_cm_capply_def(),
      cm_annotation_step_def, cm_update_annotation_def,
      cm_update_c_def, cm_ann_pop_def, cm_ann_replace_def,
      cm_ann_leave_call_def, cm_ann_pc_def, cm_ann_temp_def,
      cm_ann_break_def, cm_ann_continue_def, cm_ann_cursors_def,
      cm_ann_spills_def, cm_ann_saved_def, cm_ann_calls_def,
      cm_cursor_phase_def, cm_cursor_temp_def, cm_cursor_break_def,
      cm_cursor_continue_def, cm_phase_frame_def,
      cm_phase_next_fid_def, get_cm_task_type_ready_def(),
      get_cm_control_kind_def(), get_cm_control_value_def(),
      get_theorem_by_name("HD"), get_theorem_by_name("TL"),
      get_theorem_by_name("NOT_CONS_NIL"),
      get_theorem_by_name("COND_CLAUSES"),
      cm_tvs_update_annotation_cond(), cm_tvs_ann_cursors_cond(),
      get_theorem_by_name("COND_ID"));
}

PROOF static thm cm_tcs_components(term phase, thm ready) {
  return mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `q:cm_program`, `fid:int`, `control:cm_control`,
      `st:cm_src_state`,
      `cm_phase_frame ${phase:cm_aphase} :: (ks:(cm_frame)list)`,
      phase, `pc:int`, `temp:int`, `breakpc:int`, `continuepc:int`,
      `parent_temp:int`, `parent_break:int`, `parent_continue:int`,
      `rest:(cm_acursor)list`, `spills:(cm_spill)list`,
      `saved:(cm_spill_frame)list`, `calls:(cm_call_sim_frame)list`),
      cm_c_cursor_type_components), ready);
}

PROOF static thm cm_tcs_cursor_fact(
    term phase, term expected, thm_list extra) {
  term next_ann = cm_tcs_next_annotation(phase);
  thm_list rules = cm_tcs_rules(refl_rule(phase));
  for (size_t i = 0; i < vector_size(extra); ++i) {
    vector_add(&rules, extra[i]);
  }
  term proposition =
      `cm_ann_cursors ${next_ann:cm_annotation} ==
        ${expected:(cm_acursor)list}`;
  thm first = apply_conversion(reduce_rewrite_conv(rules), proposition);
  thm second = apply_conversion(reduce_rewrite_conv(rules), rhs_of(first));
  return eqt_elim_rule(trans_rule(first, second));
}

PROOF static thm cm_tcs_pop_control(
    term phase, term next_control, term next_st, thm ready,
    thm control_ready, thm_list extra) {
  term next_ann = cm_tcs_next_annotation(phase);
  thm cursor_equal = cm_tcs_cursor_fact(
      phase, `rest:(cm_acursor)list`, extra);
  thm proved = specl_rule(TERM_LIST(
      `p:cm_program`, `q:cm_program`, `fid:int`, `control:cm_control`,
      next_control, `st:cm_src_state`, next_st,
      `cm_phase_frame ${phase:cm_aphase} :: (ks:(cm_frame)list)`,
      `ks:(cm_frame)list`, phase, `pc:int`, `temp:int`,
      `breakpc:int`, `continuepc:int`, `parent_temp:int`,
      `parent_break:int`, `parent_continue:int`,
      `rest:(cm_acursor)list`, `spills:(cm_spill)list`,
      `saved:(cm_spill_frame)list`, `calls:(cm_call_sim_frame)list`,
      next_ann), cm_c_pop_control_task_ready);
  proved = mp_rule(proved, ready);
  proved = mp_rule(proved, control_ready);
  return mp_rule(proved, cursor_equal);
}

PROOF static thm cm_tcs_pop_value(
    term phase, term result, term result_ty, term next_st,
    thm ready, thm compatible, thm_list extra) {
  term next_ann = cm_tcs_next_annotation(phase);
  thm phase_result = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(get_cm_phase_result_type_def())),
      `cm_phase_result_type (p:cm_program) (fid:int)
        ${phase:cm_aphase} ${result_ty:cm_type}`));
  thm cursor_equal = cm_tcs_cursor_fact(
      phase, `rest:(cm_acursor)list`, extra);
  thm proved = specl_rule(TERM_LIST(
      `p:cm_program`, `q:cm_program`, `fid:int`, `control:cm_control`,
      result, result_ty, `st:cm_src_state`, next_st,
      `cm_phase_frame ${phase:cm_aphase} :: (ks:(cm_frame)list)`,
      `ks:(cm_frame)list`, phase, `pc:int`, `temp:int`,
      `breakpc:int`, `continuepc:int`, `parent_temp:int`,
      `parent_break:int`, `parent_continue:int`,
      `rest:(cm_acursor)list`, `spills:(cm_spill)list`,
      `saved:(cm_spill_frame)list`, `calls:(cm_call_sim_frame)list`,
      next_ann), cm_c_pop_value_task_ready);
  proved = mp_rule(proved, ready);
  proved = mp_rule(proved, phase_result);
  proved = mp_rule(proved, compatible);
  return mp_rule(proved, cursor_equal);
}

PROOF static void cm_tcs_accept(
    gnode branch, thm proved, thm shape, thm_list extra) {
  thm_list rules = cm_tcs_rules(shape);
  for (size_t i = 0; i < vector_size(extra); ++i) {
    vector_add(&rules, extra[i]);
  }
  thm normalized = conv_rule(reduce_rewrite_conv(rules), proved);
  normalized = conv_rule(reduce_rewrite_conv(rules), normalized);
  thm target_first = apply_conversion(
      reduce_rewrite_conv(rules), goal_ccl(branch->g));
  thm target_second = apply_conversion(
      reduce_rewrite_conv(rules), rhs_of(target_first));
  thm target_view = trans_rule(target_first, target_second);
  ACCEPT_TAC(branch, eq_mp_rule(sym_rule(target_view), normalized));
}
