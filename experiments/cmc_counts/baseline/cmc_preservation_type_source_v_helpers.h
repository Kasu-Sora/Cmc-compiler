#pragma once

#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_type_source_v_support.h"
#include "cmc_preservation_ready_coordinate.h"
#include "cmc_preservation_type_value.h"

PROOF static term cm_tvs_app_arg(term application, size_t offset) {
  for (size_t i = 0; i < offset; ++i) {
    application = dest_comb(application).tm1;
  }
  return dest_comb(application).tm2;
}

PROOF static term cm_tvs_phase_arg(
    term phase, size_t arity, size_t index) {
  return cm_tvs_app_arg(phase, arity - index - 1);
}

PROOF static term cm_tvs_annotation(term phase) {
  return `CMAnnotation (pc:int) (temp:int) (breakpc:int)
    (continuepc:int)
    (CMACursor ${phase:cm_aphase} (parent_temp:int)
       (parent_break:int) (parent_continue:int) ::
     (rest:(cm_acursor)list))
    (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
    (calls:(cm_call_sim_frame)list)`;
}

PROOF static term cm_tvs_task(term phase) {
  return `CMVTask (q:cm_program) (fid:int) (incoming:cm_value)
    (st:cm_src_state) (cm_phase_frame ${phase:cm_aphase} ::
      (ks:(cm_frame)list))`;
}

PROOF static term cm_tvs_next_annotation(term phase) {
  term task = cm_tvs_task(phase);
  term ann = cm_tvs_annotation(phase);
  return `cm_update_annotation
    (cm_annotation_step ${task:cm_task} ${ann:cm_annotation})`;
}

PROOF static thm cm_tvs_update_annotation_cond(void) {
  return ispecl_rule(TERM_LIST(`condition:bool`, `cm_update_annotation`,
      `yes_update:cm_aupdate`, `no_update:cm_aupdate`),
      get_theorem_by_name("COND_RAND"));
}

PROOF static thm cm_tvs_ann_cursors_cond(void) {
  return ispecl_rule(TERM_LIST(`condition:bool`, `cm_ann_cursors`,
      `yes_annotation:cm_annotation`, `no_annotation:cm_annotation`),
      get_theorem_by_name("COND_RAND"));
}

PROOF static thm_list cm_tvs_rules(thm shape) {
  return THM_LIST(
      shape, get_cm_step_def(), get_cm_vapply_def(),
      cm_annotation_step_def, cm_update_annotation_def,
      cm_update_v_def, cm_ann_plain_def, cm_ann_linear_def,
      cm_ann_replace_def, cm_ann_pop_def, cm_ann_spills_set_def,
      cm_ann_put_spill_def, cm_ann_pc_def, cm_ann_temp_def,
      cm_ann_break_def, cm_ann_continue_def, cm_ann_cursors_def,
      cm_ann_spills_def, cm_ann_saved_def, cm_ann_calls_def,
      cm_cursor_phase_def, cm_cursor_temp_def, cm_cursor_break_def,
      cm_cursor_continue_def, cm_phase_frame_def,
      cm_phase_next_fid_def, get_cm_task_type_ready_def(),
      get_theorem_by_name("HD"), get_theorem_by_name("TL"),
      get_theorem_by_name("NOT_CONS_NIL"),
      get_theorem_by_name("COND_CLAUSES"),
      cm_tvs_update_annotation_cond(), cm_tvs_ann_cursors_cond(),
      get_theorem_by_name("COND_ID"));
}

PROOF static thm cm_tvs_pick_conjunct(thm fact, term wanted) {
  if (alpha_compare(concl(fact), wanted) == 0) return fact;
  if (!is_conj(concl(fact))) return empty_theorem;
  thm left = cm_tvs_pick_conjunct(conjunct1_rule(fact), wanted);
  if (!IS_NULL(left)) return left;
  return cm_tvs_pick_conjunct(conjunct2_rule(fact), wanted);
}

PROOF static thm cm_tvs_components(term phase, thm ready) {
  return mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `q:cm_program`, `fid:int`, `incoming:cm_value`,
      `st:cm_src_state`,
      `cm_phase_frame ${phase:cm_aphase} :: (ks:(cm_frame)list)`,
      phase, `pc:int`, `temp:int`, `breakpc:int`, `continuepc:int`,
      `parent_temp:int`, `parent_break:int`, `parent_continue:int`,
      `rest:(cm_acursor)list`, `spills:(cm_spill)list`,
      `saved:(cm_spill_frame)list`, `calls:(cm_call_sim_frame)list`),
      cm_v_cursor_type_components), ready);
}

PROOF static thm cm_tvs_cursor_fact(
    term phase, term expected, thm_list extra) {
  term next_ann = cm_tvs_next_annotation(phase);
  thm_list rules = THM_LIST();
  vector_add(&rules, get_cm_step_def());
  vector_add(&rules, get_cm_vapply_def());
  vector_add(&rules, cm_annotation_step_def);
  vector_add(&rules, cm_update_annotation_def);
  vector_add(&rules, cm_update_v_def);
  vector_add(&rules, cm_ann_plain_def);
  vector_add(&rules, cm_ann_linear_def);
  vector_add(&rules, cm_ann_replace_def);
  vector_add(&rules, cm_ann_pop_def);
  vector_add(&rules, cm_ann_spills_set_def);
  vector_add(&rules, cm_ann_put_spill_def);
  vector_add(&rules, cm_ann_pc_def);
  vector_add(&rules, cm_ann_temp_def);
  vector_add(&rules, cm_ann_break_def);
  vector_add(&rules, cm_ann_continue_def);
  vector_add(&rules, cm_ann_cursors_def);
  vector_add(&rules, cm_ann_spills_def);
  vector_add(&rules, cm_ann_saved_def);
  vector_add(&rules, cm_ann_calls_def);
  vector_add(&rules, cm_cursor_phase_def);
  vector_add(&rules, cm_cursor_temp_def);
  vector_add(&rules, cm_cursor_break_def);
  vector_add(&rules, cm_cursor_continue_def);
  vector_add(&rules, cm_phase_frame_def);
  vector_add(&rules, cm_phase_next_fid_def);
  vector_add(&rules, get_theorem_by_name("HD"));
  vector_add(&rules, get_theorem_by_name("TL"));
  vector_add(&rules, get_theorem_by_name("NOT_CONS_NIL"));
  vector_add(&rules, get_theorem_by_name("COND_CLAUSES"));
  vector_add(&rules, get_theorem_by_name("COND_ID"));
  vector_add(&rules, cm_tvs_update_annotation_cond());
  vector_add(&rules, cm_tvs_ann_cursors_cond());
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

PROOF static thm cm_tvs_pop_value(
    term phase, term result, term result_ty, term next_st,
    thm ready, thm compatible, thm_list extra) {
  term next_ann = cm_tvs_next_annotation(phase);
  thm phase_result = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_phase_result_type_def())),
      `cm_phase_result_type (p:cm_program) (fid:int)
        ${phase:cm_aphase} ${result_ty:cm_type}`));
  thm cursor_equal = cm_tvs_cursor_fact(
      phase, `rest:(cm_acursor)list`, extra);
  thm proved = specl_rule(TERM_LIST(
      `p:cm_program`, `q:cm_program`, `fid:int`, `incoming:cm_value`,
      result, result_ty, `st:cm_src_state`, next_st,
      `cm_phase_frame ${phase:cm_aphase} :: (ks:(cm_frame)list)`,
      `ks:(cm_frame)list`, phase, `pc:int`, `temp:int`,
      `breakpc:int`, `continuepc:int`, `parent_temp:int`,
      `parent_break:int`, `parent_continue:int`,
      `rest:(cm_acursor)list`, `spills:(cm_spill)list`,
      `saved:(cm_spill_frame)list`, `calls:(cm_call_sim_frame)list`,
      next_ann), cm_v_pop_value_task_ready);
  proved = mp_rule(proved, ready);
  proved = mp_rule(proved, phase_result);
  proved = mp_rule(proved, compatible);
  return mp_rule(proved, cursor_equal);
}

PROOF static thm cm_tvs_pop_control(
    term phase, term control, term next_st, thm ready,
    thm control_ready, thm_list extra) {
  term next_ann = cm_tvs_next_annotation(phase);
  thm cursor_equal = cm_tvs_cursor_fact(
      phase, `rest:(cm_acursor)list`, extra);
  thm proved = specl_rule(TERM_LIST(
      `p:cm_program`, `q:cm_program`, `fid:int`, `incoming:cm_value`,
      control, `st:cm_src_state`, next_st,
      `cm_phase_frame ${phase:cm_aphase} :: (ks:(cm_frame)list)`,
      `ks:(cm_frame)list`, phase, `pc:int`, `temp:int`,
      `breakpc:int`, `continuepc:int`, `parent_temp:int`,
      `parent_break:int`, `parent_continue:int`,
      `rest:(cm_acursor)list`, `spills:(cm_spill)list`,
      `saved:(cm_spill_frame)list`, `calls:(cm_call_sim_frame)list`,
      next_ann), cm_v_pop_control_task_ready);
  proved = mp_rule(proved, ready);
  proved = mp_rule(proved, control_ready);
  return mp_rule(proved, cursor_equal);
}

PROOF static void cm_tvs_accept(
    gnode branch, thm proved, thm shape, thm_list extra) {
  thm_list rules = cm_tvs_rules(shape);
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

PROOF static thm cm_tvs_trivial(term proposition, thm_list rules) {
  return eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(rules), proposition));
}
