#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_invariant_value.h"

#require "cmc_preservation_invariant_transition.c"

PROOF static size_t _cmc_preservation_invariant_value_axioms_before =
    vector_size(get_all_axioms());

PROOF static term cm_v_runtime_annotation(term phase) {
  return `CMAnnotation (pc:int) (temp:int) (breakpc:int)
    (continuepc:int)
    (CMACursor ${phase:cm_aphase} (owner:int)
       (saved_break:int) (saved_continue:int) ::
     (rest:(cm_acursor)list))
    (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
    (calls:(cm_call_sim_frame)list)`;
}

PROOF static term cm_v_app_arg_from_right(
    term application, size_t offset) {
  for (size_t i = 0; i < offset; ++i) {
    application = dest_comb(application).tm1;
  }
  return dest_comb(application).tm2;
}

PROOF static term cm_v_phase_arg(
    term phase, size_t arity, size_t index) {
  return cm_v_app_arg_from_right(phase, arity - index - 1);
}

PROOF static thm_list cm_v_annotation_rules(void) {
  return THM_LIST(
      cm_ann_plain_def, cm_ann_linear_def,
      cm_ann_push_def, cm_ann_replace_def, cm_ann_pop_def,
      cm_ann_spills_set_def, cm_ann_put_spill_def,
      cm_ann_enter_call_def, cm_ann_leave_call_def,
      cm_ann_pc_def, cm_ann_temp_def, cm_ann_break_def,
      cm_ann_continue_def, cm_ann_cursors_def,
      cm_ann_spills_def, cm_ann_saved_def, cm_ann_calls_def,
      cm_cursor_phase_def, cm_cursor_temp_def,
      cm_cursor_break_def, cm_cursor_continue_def,
      get_theorem_by_name("HD"), get_theorem_by_name("TL"));
}

PROOF static thm cm_v_cursor_eq(term ann, term phase) {
  return eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(cm_v_annotation_rules()),
      `cm_ann_cursors ${ann:cm_annotation} ==
       CMACursor ${phase:cm_aphase} (owner:int)
         (saved_break:int) (saved_continue:int) ::
       (rest:(cm_acursor)list)`));
}

PROOF static thm cm_v_pop(
    term phase, term ann, term st, term nextpc,
    thm core) {
  thm result = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, st, ann, phase,
      `owner:int`, `saved_break:int`, `saved_continue:int`,
      `rest:(cm_acursor)list`, nextpc),
      cm_runtime_core_pop_plain);
  result = match_mp_rule(result, cm_v_cursor_eq(ann, phase));
  thm_list phase_rules = THM_LIST(
      cm_phase_is_call_def, cm_phase_is_scope_def,
      cm_phase_is_halt_def);
  for (size_t i = 0; i < 3; ++i) {
    result = match_mp_rule(result, eqt_elim_rule(
        apply_conversion(reduce_rewrite_conv(phase_rules),
          dest_imp(concl(result)).tm1)));
  }
  return match_mp_rule(result, core);
}

PROOF static thm cm_v_replace(
    term oldphase, term newphase, term ann, term st,
    term nextpc, term nexttemp, term nextbreak,
    term nextcontinue, thm core) {
  thm result = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, st, ann,
      oldphase, newphase, `owner:int`, `saved_break:int`,
      `saved_continue:int`, `rest:(cm_acursor)list`,
      nextpc, nexttemp, nextbreak, nextcontinue),
      cm_runtime_core_replace_plain);
  result = match_mp_rule(result, cm_v_cursor_eq(ann, oldphase));
  thm_list phase_rules = THM_LIST(
      cm_phase_is_call_def, cm_phase_is_scope_def,
      cm_phase_is_halt_def);
  for (size_t i = 0; i < 6; ++i) {
    result = match_mp_rule(result, eqt_elim_rule(
        apply_conversion(reduce_rewrite_conv(phase_rules),
          dest_imp(concl(result)).tm1)));
  }
  return match_mp_rule(result, core);
}

PROOF static thm cm_v_replace_and_spill(
    term oldphase, term newphase, term ann, term st,
    term nextpc, term nexttemp, term nextbreak,
    term nextcontinue, term slot, term spill_value,
    thm slot_lower, thm slot_upper, thm core) {
  thm replaced = cm_v_replace(
      oldphase, newphase, ann, st, nextpc, nexttemp,
      nextbreak, nextcontinue, core);
  term replaced_ann =
      `cm_ann_replace ${newphase:cm_aphase} ${nextpc:int}
        ${nexttemp:int} ${nextbreak:int} ${nextcontinue:int}
        ${ann:cm_annotation}`;
  thm updated = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, st, replaced_ann,
      slot, spill_value), cm_runtime_core_spill_put);
  updated = match_mp_rule(updated,
      assume_rule(`0i <= (fid:int)`));
  updated = match_mp_rule(updated, slot_lower);
  updated = match_mp_rule(updated, slot_upper);
  return match_mp_rule(updated, replaced);
}

PROOF static thm cm_v_replace_scope(
    term oldphase, term newphase, term ann, term st,
    term nextpc, term nexttemp, term nextbreak,
    term nextcontinue, thm core) {
  thm result = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, st, ann,
      oldphase, newphase, `owner:int`, `saved_break:int`,
      `saved_continue:int`, `rest:(cm_acursor)list`,
      nextpc, nexttemp, nextbreak, nextcontinue),
      cm_runtime_core_replace_scope);
  result = match_mp_rule(result, cm_v_cursor_eq(ann, oldphase));
  result = match_mp_rule(result,
      assume_rule(`0i <= (fid:int)`));
  thm_list phase_rules = THM_LIST(
      cm_phase_is_call_def, cm_phase_is_scope_def,
      cm_phase_is_halt_def, cm_phase_oldregions_def);
  for (size_t i = 0; i < 6; ++i) {
    result = match_mp_rule(result, eqt_elim_rule(
        apply_conversion(reduce_rewrite_conv(phase_rules),
          dest_imp(concl(result)).tm1)));
  }
  return match_mp_rule(result, core);
}

PROOF static void cm_v_accept(
    gnode branch, thm result, thm phase_shape,
    thm frames_eq, thm_list extra) {
  thm_list rules = THM_LIST(
      phase_shape, sym_rule(frames_eq),
      get_cm_step_def(), get_cm_vapply_def(),
      get_cm_begin_call_def(), cm_annotation_step_def,
      cm_update_annotation_def, cm_update_v_def,
      cm_ann_plain_def, cm_ann_linear_def,
      cm_ann_push_def, cm_ann_replace_def, cm_ann_pop_def,
      cm_ann_spills_set_def, cm_ann_put_spill_def,
      cm_ann_enter_call_def, cm_ann_leave_call_def,
      cm_task_runtime_invariant_def, cm_runtime_core_def,
      cm_cursor_frames_def, cm_phase_frame_def,
      cm_v_phase_ready_def, cm_v_spill_ready_def,
      cm_ann_pc_def, cm_ann_temp_def, cm_ann_break_def,
      cm_ann_continue_def, cm_ann_cursors_def,
      cm_ann_spills_def, cm_ann_saved_def, cm_ann_calls_def,
      cm_cursor_phase_def, cm_cursor_temp_def,
      cm_cursor_break_def, cm_cursor_continue_def,
      get_theorem_by_name("HD"), get_theorem_by_name("TL"),
      get_theorem_by_name("NOT_CONS_NIL"));
  for (size_t i = 0; i < vector_size(extra); ++i) {
    vector_add(&rules, extra[i]);
  }
  thm expanded =
      conv_rule(reduce_rewrite_conv(rules), result);
  gnode reduced =
      CONV_WITH_ASMP_TAC(branch, reduce_rewrite_conv, rules);
  if (IS_NULL(reduced->solved)) {
    reduced =
        CONV_WITH_ASMP_TAC(reduced, reduce_rewrite_conv, rules);
  }
  if (IS_NULL(reduced->solved)) {
    ACCEPT_TAC(reduced, mp_rule(taut_rule(mk_imp(
        concl(expanded), goal_ccl(reduced->g))), expanded));
  }
}

PROOF static thm cm_prove_task_runtime_v_phase_step(void) {
  term phase = `phase:cm_aphase`;
  term ann = cm_v_runtime_annotation(phase);
  term task =
      `CMVTask (p:cm_program) (fid:int) (v:cm_value)
        (st:cm_src_state) (ks:(cm_frame)list)`;
  term body = imp_chain(TERM_LIST(
      `cm_typed_program (p:cm_program)`,
      `cm_phase_is_halt (phase:cm_aphase) || 0i <= (fid:int)`,
      `cm_annotation_erases ${task:cm_task} ${ann:cm_annotation}`,
      `cm_v_layout_ready (p:cm_program) (v:cm_value)
        (st:cm_src_state) ${ann:cm_annotation}`,
      `cm_v_spill_ready (p:cm_program) (fid:int)
        ${ann:cm_annotation} (phase:cm_aphase)`,
      `cm_v_source_ready (p:cm_program) (fid:int)
        (st:cm_src_state) (phase:cm_aphase)`,
      `cm_runtime_core (p:cm_program) (fid:int)
        (st:cm_src_state) ${ann:cm_annotation}`),
      `cm_task_runtime_invariant (p:cm_program)
        (cm_step ${task:cm_task})
        (cm_update_annotation
          (cm_annotation_step ${task:cm_task}
            ${ann:cm_annotation}))`);
  gnode root = gnode_new_with_ccl(
      list_mk_forall(free_vars(body), body));
  gnode introduced = AUTO_INTROS_TAC(root);
  thm erases = assume_rule(
      `cm_annotation_erases ${task:cm_task} ${ann:cm_annotation}`);
  thm frames_eq = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_annotation_erases_def, cm_ann_cursors_def,
      cm_cursor_frames_def, cm_cursor_phase_def)), erases);
  thm ready = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_v_layout_ready_def, cm_ann_cursors_def,
      cm_ann_temp_def, cm_cursor_temp_def,
      cm_cursor_phase_def, get_theorem_by_name("HD"),
      get_theorem_by_name("NOT_CONS_NIL"))),
      assume_rule(
        `cm_v_layout_ready (p:cm_program) (v:cm_value)
          (st:cm_src_state) ${ann:cm_annotation}`));
  thm phase_ready = conjunct2_rule(ready);
  thm spill_ready = assume_rule(
      `cm_v_spill_ready (p:cm_program) (fid:int)
        ${ann:cm_annotation} (phase:cm_aphase)`);
  thm source_ready = assume_rule(
      `cm_v_source_ready (p:cm_program) (fid:int)
        (st:cm_src_state) (phase:cm_aphase)`);
  thm core = assume_rule(
      `cm_runtime_core (p:cm_program) (fid:int)
        (st:cm_src_state) ${ann:cm_annotation}`);
  gnode_list cases = DISJ_CASES_TAC(
      introduced,
      ispec_rule(`phase:cm_aphase`,
        get_datatype_cases("cm_aphase")),
      "Hphase");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    while (true) {
      labeled_term_list assumptions = goal_lasmps(cases[i]->g);
      int index =
          labeled_term_list_index(assumptions, "Hphase");
      if (!is_exists(assumptions[index].tm)) break;
      cases[i] = ASMP_EXISTS_TAC(cases[i], "Hphase", NULL);
    }
    thm phase_shape = assume_rule(
        goal_lasmps(cases[i]->g)[
          labeled_term_list_index(
            goal_lasmps(cases[i]->g), "Hphase")].tm);
    term concrete_phase = rhs_of(phase_shape);
    if (i != 0) {
      thm fid_nonnegative = conv_rule(
          reduce_rewrite_conv(THM_LIST(
            phase_shape, cm_phase_is_halt_def)),
          assume_rule(
            `cm_phase_is_halt (phase:cm_aphase) ||
             0i <= (fid:int)`));
      cases[i] = ASSUME_TAC(
          cases[i], fid_nonnegative, "Hfid_nonnegative");
    }
    term concrete_ann = cm_v_runtime_annotation(concrete_phase);
    thm concrete_core = conv_rule(
        rewrite_conv(THM_LIST(phase_shape)), core);
    thm concrete_ready = conv_rule(
        rewrite_conv(THM_LIST(phase_shape)), phase_ready);
    thm concrete_spill = conv_rule(
        rewrite_conv(THM_LIST(phase_shape)), spill_ready);
    thm result = empty_theorem;
      thm tail_nil = conv_rule(reduce_rewrite_conv(THM_LIST(
          cm_v_phase_ready_def, cm_ann_cursors_def,
          cm_cursor_phase_def, get_theorem_by_name("HD"),
          get_theorem_by_name("TL"),
          get_theorem_by_name("NOT_CONS_NIL"))),
          concrete_ready);
    if (i == 0) {
      result = match_mp_rule(specl_rule(TERM_LIST(
          `p:cm_program`, `fid:int`, `st:cm_src_state`,
          concrete_ann, `owner:int`, `saved_break:int`,
          `saved_continue:int`, `rest:(cm_acursor)list`,
          `CMReturn (v:cm_value)`,
          `tower_status
            (cm_value_number (st:cm_src_state) (v:cm_value))`,
          `(pc:int) +
            ilength (cm_char_normalize_code CMCharTy)`),
          cm_runtime_halt_done),
          cm_v_cursor_eq(concrete_ann, concrete_phase));
      result = match_mp_rule(result, concrete_core);
      cm_v_accept(cases[i], result, phase_shape, frames_eq,
          THM_LIST(tail_nil));
    } else if (i == 1) {
      term ty = cm_v_phase_arg(concrete_phase, 1, 0);
      thm load_ok = conv_rule(reduce_rewrite_conv(
          THM_LIST(cm_v_phase_ready_def)), concrete_ready);
      result = cm_v_pop(concrete_phase, concrete_ann,
          `st:cm_src_state`,
          `(pc:int) + ilength (cm_load_code ${ty:cm_type})`,
          concrete_core);
      cm_v_accept(cases[i], result, phase_shape, frames_eq,
          THM_LIST(load_ok));
      continue;
    } else if (i == 2) {
      term ty = cm_v_phase_arg(concrete_phase, 2, 1);
      thm bounds = conv_rule(reduce_rewrite_conv(THM_LIST(
          cm_v_spill_ready_def, cm_ann_temp_def)),
          concrete_spill);
      result = cm_v_replace_and_spill(
          concrete_phase,
          `CAAssignRP (v:cm_value) ${ty:cm_type}`,
          concrete_ann, `st:cm_src_state`,
          `(pc:int) + ilength
            (cm_temp_store_code (p:cm_program) (fid:int)
              (temp:int))`,
          `(temp:int) + 1i`, `breakpc:int`, `continuepc:int`,
          `temp:int`, `v:cm_value`,
          conjunct1_rule(bounds), conjunct2_rule(bounds),
          concrete_core);
    } else if (i == 3) {
      term ptr = cm_v_phase_arg(concrete_phase, 2, 0);
      term ty = cm_v_phase_arg(concrete_phase, 2, 1);
      thm store_ok = conv_rule(reduce_rewrite_conv(
          THM_LIST(cm_v_phase_ready_def)), concrete_ready);
      thm stored = match_mp_rule(specl_rule(TERM_LIST(
          `p:cm_program`, `fid:int`, `st:cm_src_state`,
          concrete_ann, ty, ptr, `v:cm_value`),
          cm_runtime_core_store), concrete_core);
      result = cm_v_pop(concrete_phase, concrete_ann,
          `cm_state_store ${ty:cm_type} ${ptr:cm_value}
            (v:cm_value) (st:cm_src_state)`,
          `(pc:int) + ilength
            (cm_assign_tail_code (p:cm_program) (fid:int)
              ${ty:cm_type} (owner:int))`, stored);
      cm_v_accept(cases[i], result, phase_shape, frames_eq,
          THM_LIST(store_ok));
      continue;
    } else if (i == 4) {
      term op = cm_v_phase_arg(concrete_phase, 4, 0);
      term left = cm_v_phase_arg(concrete_phase, 4, 1);
      term right = cm_v_phase_arg(concrete_phase, 4, 2);
      term ty = cm_v_phase_arg(concrete_phase, 4, 3);
      gnode_list zero_cases = BOOL_CASES_TAC(
          cases[i], `${op:int} == 0i`, "Hop_zero");
      thm op_zero = assume_rule(`${op:int} == 0i`);
      gnode_list zero_truth = BOOL_CASES_TAC(
          zero_cases[0],
          `cm_truth (st:cm_src_state) (v:cm_value)`,
          "Htruth_zero");
      {
        thm popped = cm_v_pop(concrete_phase, concrete_ann,
            `st:cm_src_state`,
            `(pc:int) + cm_rvalue_code_count
              (p:cm_program) (fid:int) ${right:cm_expr} + 5i`,
            concrete_core);
        cm_v_accept(zero_truth[0], popped, phase_shape,
            frames_eq, THM_LIST(op_zero));
      }
      {
        thm replaced = cm_v_replace(
            concrete_phase,
            `CABinRP 0i ${left:cm_expr} ${right:cm_expr}
              (v:cm_value) ${ty:cm_type}`,
            concrete_ann, `st:cm_src_state`, `(pc:int) + 1i`,
            `temp:int`, `breakpc:int`, `continuepc:int`,
            concrete_core);
        cm_v_accept(zero_truth[1], replaced, phase_shape,
            frames_eq, THM_LIST(op_zero));
      }
      gnode_list one_cases = BOOL_CASES_TAC(
          zero_cases[1], `${op:int} == 1i`, "Hop_one");
      thm op_one = assume_rule(`${op:int} == 1i`);
      gnode_list one_truth = BOOL_CASES_TAC(
          one_cases[0],
          `cm_truth (st:cm_src_state) (v:cm_value)`,
          "Htruth_one");
      {
        thm replaced = cm_v_replace(
            concrete_phase,
            `CABinRP 1i ${left:cm_expr} ${right:cm_expr}
              (v:cm_value) ${ty:cm_type}`,
            concrete_ann, `st:cm_src_state`, `(pc:int) + 1i`,
            `temp:int`, `breakpc:int`, `continuepc:int`,
            concrete_core);
        cm_v_accept(one_truth[0], replaced, phase_shape,
            frames_eq, THM_LIST(op_one));
      }
      {
        thm popped = cm_v_pop(concrete_phase, concrete_ann,
            `st:cm_src_state`,
            `(pc:int) + cm_rvalue_code_count
              (p:cm_program) (fid:int) ${right:cm_expr} + 5i`,
            concrete_core);
        cm_v_accept(one_truth[1], popped, phase_shape,
            frames_eq, THM_LIST(op_one));
      }
      {
        thm bounds = conv_rule(reduce_rewrite_conv(THM_LIST(
            cm_v_spill_ready_def, cm_ann_temp_def,
            assume_rule(`~(${op:int} == 0i)`),
            assume_rule(`~(${op:int} == 1i)`))),
            concrete_spill);
        thm replaced = cm_v_replace_and_spill(
            concrete_phase,
            `CABinRP ${op:int} ${left:cm_expr} ${right:cm_expr}
              (v:cm_value) ${ty:cm_type}`,
            concrete_ann, `st:cm_src_state`,
            `(pc:int) + ilength
              (cm_temp_store_code (p:cm_program) (fid:int)
                (temp:int))`,
            `(temp:int) + 1i`, `breakpc:int`, `continuepc:int`,
            `temp:int`, `v:cm_value`,
            conjunct1_rule(bounds), conjunct2_rule(bounds),
            concrete_core);
        cm_v_accept(one_cases[1], replaced, phase_shape,
            frames_eq, THM_LIST());
      }
      continue;
    } else if (i == 5) {
      term op = cm_v_phase_arg(concrete_phase, 5, 0);
      term left = cm_v_phase_arg(concrete_phase, 5, 1);
      term right = cm_v_phase_arg(concrete_phase, 5, 2);
      thm binary_ok = conv_rule(reduce_rewrite_conv(
          THM_LIST(cm_v_phase_ready_def)), concrete_ready);
      gnode_list zero_cases = BOOL_CASES_TAC(
          cases[i], `${op:int} == 0i`, "Hop_zero_r");
      thm op_zero_r = assume_rule(`${op:int} == 0i`);
      thm binary_ok_zero = conv_rule(
          rewrite_conv(THM_LIST(op_zero_r)), binary_ok);
      {
        thm popped = cm_v_pop(concrete_phase, concrete_ann,
            `st:cm_src_state`, `(pc:int) + 4i`, concrete_core);
        cm_v_accept(zero_cases[0], popped, phase_shape,
            frames_eq, THM_LIST(binary_ok_zero, op_zero_r));
      }
      gnode_list one_cases = BOOL_CASES_TAC(
          zero_cases[1], `${op:int} == 1i`, "Hop_one_r");
      thm op_one_r = assume_rule(`${op:int} == 1i`);
      thm binary_ok_one = conv_rule(
          rewrite_conv(THM_LIST(op_one_r)), binary_ok);
      {
        thm popped = cm_v_pop(concrete_phase, concrete_ann,
            `st:cm_src_state`, `(pc:int) + 4i`, concrete_core);
        cm_v_accept(one_cases[0], popped, phase_shape,
            frames_eq, THM_LIST(binary_ok_one, op_one_r));
      }
      {
        thm popped = cm_v_pop(concrete_phase, concrete_ann,
            `st:cm_src_state`,
            `(pc:int) + ilength
              (cm_binary_finish_code (p:cm_program) (fid:int)
                ${op:int} ${left:cm_expr} ${right:cm_expr}
                (owner:int))`, concrete_core);
        cm_v_accept(one_cases[1], popped, phase_shape,
            frames_eq, THM_LIST(binary_ok));
      }
      continue;
    } else if (i == 6) {
      result = cm_v_pop(concrete_phase, concrete_ann,
          `st:cm_src_state`, `(pc:int) + 2i`, concrete_core);
    } else if (i == 7) {
      term ty = cm_v_phase_arg(concrete_phase, 2, 1);
      thm bounds = conv_rule(reduce_rewrite_conv(THM_LIST(
          cm_v_spill_ready_def, cm_ann_temp_def)), concrete_spill);
      result = cm_v_replace_and_spill(
          concrete_phase,
          `CAIndexRP (v:cm_value) ${ty:cm_type}`,
          concrete_ann, `st:cm_src_state`,
          `(pc:int) + ilength
            (cm_temp_store_code (p:cm_program) (fid:int)
              (temp:int))`,
          `(temp:int) + 1i`, `breakpc:int`, `continuepc:int`,
          `temp:int`, `v:cm_value`,
          conjunct1_rule(bounds), conjunct2_rule(bounds),
          concrete_core);
    } else if (i == 8) {
      term ty = cm_v_phase_arg(concrete_phase, 2, 1);
      thm shift_ok = conv_rule(reduce_rewrite_conv(
          THM_LIST(cm_v_phase_ready_def)), concrete_ready);
      result = cm_v_pop(concrete_phase, concrete_ann,
          `st:cm_src_state`,
          `(pc:int) + ilength
            (cm_index_tail_code (p:cm_program) (fid:int)
              ${ty:cm_type} (owner:int))`, concrete_core);
      cm_v_accept(cases[i], result, phase_shape, frames_eq,
          THM_LIST(shift_ok));
      continue;
    } else if (i == 9) {
      term mid = cm_v_phase_arg(concrete_phase, 2, 0);
      term base_ty = cm_v_phase_arg(concrete_phase, 2, 1);
      thm member_ok = conv_rule(reduce_rewrite_conv(
          THM_LIST(cm_v_phase_ready_def)), concrete_ready);
      result = cm_v_pop(concrete_phase, concrete_ann,
          `st:cm_src_state`,
          `(pc:int) + ilength
            (cm_member_tail_code (p:cm_program)
              ${base_ty:cm_type} ${mid:int})`, concrete_core);
      cm_v_accept(cases[i], result, phase_shape, frames_eq,
          THM_LIST(member_ok));
      continue;
    } else if (i == 10) {
      thm io_core = match_mp_rule(specl_rule(TERM_LIST(
          `p:cm_program`, `fid:int`, `st:cm_src_state`,
          concrete_ann, `cm_state_input (st:cm_src_state)`,
          `APPEND (cm_state_output (st:cm_src_state))
            [tower_u8
              (cm_value_number (st:cm_src_state) (v:cm_value))]`),
          cm_runtime_core_io), concrete_core);
      result = cm_v_pop(concrete_phase, concrete_ann,
          `cm_state_io (st:cm_src_state) (cm_state_input st)
            (APPEND (cm_state_output st)
              [tower_u8 (cm_value_number st (v:cm_value))])`,
          `(pc:int) + 2i`, io_core);
    } else if (i == 11) {
      thm io_core = match_mp_rule(specl_rule(TERM_LIST(
          `p:cm_program`, `fid:int`, `st:cm_src_state`,
          concrete_ann, `cm_state_input (st:cm_src_state)`,
          `APPEND (cm_state_output (st:cm_src_state))
            (tower_decimal
              (cm_value_number (st:cm_src_state) (v:cm_value)))`),
          cm_runtime_core_io), concrete_core);
      result = cm_v_pop(concrete_phase, concrete_ann,
          `cm_state_io (st:cm_src_state) (cm_state_input st)
            (APPEND (cm_state_output st)
              (tower_decimal
                (cm_value_number st (v:cm_value))))`,
          `(pc:int) + 2i`, io_core);
    } else if (i == 12) {
      result = cm_v_pop(concrete_phase, concrete_ann,
          `st:cm_src_state`,
          `(pc:int) + ilength (cm_char_normalize_code CMCharTy)`,
          concrete_core);
    } else if (i == 13) {
      result = cm_v_pop(concrete_phase, concrete_ann,
          `st:cm_src_state`, `(pc:int) + 1i`, concrete_core);
    } else if (i == 14) {
      term slot = cm_v_phase_arg(concrete_phase, 1, 0);
      thm concrete_source_ready = conv_rule(
          rewrite_conv(THM_LIST(phase_shape)), source_ready);
      thm init_ready = spec_rule(slot, conjunct1_rule(conv_rule(
          rewrite_conv(THM_LIST(cm_v_source_ready_def)),
          concrete_source_ready)));
      init_ready = match_mp_rule(
          init_ready, refl_rule(concrete_phase));
      thm init_address = conjunct1_rule(init_ready);
      thm init_store = conjunct2_rule(init_ready);
      gnode_list store_cases = BOOL_CASES_TAC(cases[i],
          `cm_store_ok
            (cm_slot_ty
              (inth ${slot:int} (cm_function_locals
                (inth (fid:int)
                  (cm_program_functions (p:cm_program))))))
            (cm_state_env (st:cm_src_state) 1i ${slot:int}) st`,
          "Hinit_store");
      {
        term init_ty =
            `cm_slot_ty
              (inth ${slot:int} (cm_function_locals
                (inth (fid:int)
                  (cm_program_functions (p:cm_program)))))`;
        term init_ptr =
            `cm_state_env (st:cm_src_state) 1i ${slot:int}`;
        thm stored = match_mp_rule(specl_rule(TERM_LIST(
            `p:cm_program`, `fid:int`, `st:cm_src_state`,
            concrete_ann, init_ty, init_ptr, `v:cm_value`),
            cm_runtime_core_store), concrete_core);
        thm popped = cm_v_pop(concrete_phase, concrete_ann,
            `cm_state_store ${init_ty:cm_type}
              ${init_ptr:cm_value} (v:cm_value)
              (st:cm_src_state)`,
            `(pc:int) + ilength
              (cm_init_tail_code (p:cm_program) (fid:int)
                ${slot:int})`, stored);
        cm_v_accept(store_cases[0], popped, phase_shape,
            frames_eq, THM_LIST(init_address));
      }
      {
        thm impossible = not_elim_rule(
            assume_rule(mk_not(concl(init_store))), init_store);
        CONTR_TAC(store_cases[1], impossible);
      }
      continue;
    } else if (i == 15 || i == 16 || i == 19 || i == 22) {
      thm impossible = conv_rule(reduce_rewrite_conv(
          THM_LIST(cm_v_phase_ready_def)), concrete_ready);
      CONTR_TAC(cases[i], impossible);
      continue;
    } else if (i == 17) {
      term yes = cm_v_phase_arg(concrete_phase, 2, 0);
      term no = cm_v_phase_arg(concrete_phase, 2, 1);
      gnode_list truth_cases = BOOL_CASES_TAC(cases[i],
          `cm_truth (st:cm_src_state) (v:cm_value)`, "Hif_truth");
      {
        thm replaced = cm_v_replace_scope(
            concrete_phase,
            `CABlockP (cm_state_env (st:cm_src_state))
              (cm_state_regions st) T
              ((pc:int) + 2i +
                cm_stmt_code_count (p:cm_program) (fid:int)
                  ${yes:cm_stmt} +
                cm_stmt_code_count p fid ${no:cm_stmt})`,
            concrete_ann, `st:cm_src_state`, `(pc:int) + 1i`,
            `owner:int`, `saved_break:int`, `saved_continue:int`,
            concrete_core);
        cm_v_accept(truth_cases[0], replaced, phase_shape,
            frames_eq, THM_LIST());
      }
      {
        thm replaced = cm_v_replace_scope(
            concrete_phase,
            `CABlockP (cm_state_env (st:cm_src_state))
              (cm_state_regions st) F
              ((pc:int) + 2i +
                cm_stmt_code_count (p:cm_program) (fid:int)
                  ${yes:cm_stmt} +
                cm_stmt_code_count p fid ${no:cm_stmt})`,
            concrete_ann, `st:cm_src_state`,
            `(pc:int) + 2i +
              cm_stmt_code_count (p:cm_program) (fid:int)
                ${yes:cm_stmt}`,
            `owner:int`, `saved_break:int`, `saved_continue:int`,
            concrete_core);
        cm_v_accept(truth_cases[1], replaced, phase_shape,
            frames_eq, THM_LIST());
      }
      continue;
    } else if (i == 18) {
      term guard = cm_v_phase_arg(concrete_phase, 4, 0);
      term loop_body = cm_v_phase_arg(concrete_phase, 4, 1);
      term loop_start = cm_v_phase_arg(concrete_phase, 4, 2);
      term loop_end = cm_v_phase_arg(concrete_phase, 4, 3);
      gnode_list truth_cases = BOOL_CASES_TAC(cases[i],
          `cm_truth (st:cm_src_state) (v:cm_value)`,
          "Hwhile_truth");
      {
        thm replaced = cm_v_replace_scope(
            concrete_phase,
            `CAWhileBodyP ${guard:cm_expr} ${loop_body:cm_stmt}
              (cm_state_env (st:cm_src_state))
              (cm_state_regions st) ${loop_start:int} ${loop_end:int}`,
            concrete_ann, `st:cm_src_state`, `(pc:int) + 1i`,
            `owner:int`, loop_end, loop_start, concrete_core);
        cm_v_accept(truth_cases[0], replaced, phase_shape,
            frames_eq, THM_LIST());
      }
      {
        thm popped = cm_v_pop(concrete_phase, concrete_ann,
            `st:cm_src_state`, loop_end, concrete_core);
        cm_v_accept(truth_cases[1], popped, phase_shape,
            frames_eq, THM_LIST());
      }
      continue;
    } else if (i == 20) {
      result = cm_v_pop(concrete_phase, concrete_ann,
          `st:cm_src_state`, `pc:int`, concrete_core);
    } else if (i == 21) {
      term callee = cm_v_phase_arg(concrete_phase, 8, 0);
      term rest_args = cm_v_phase_arg(concrete_phase, 8, 1);
      term values = cm_v_phase_arg(concrete_phase, 8, 2);
      term ret = cm_v_phase_arg(concrete_phase, 8, 3);
      term all_args = cm_v_phase_arg(concrete_phase, 8, 4);
      term base_slot = cm_v_phase_arg(concrete_phase, 8, 5);
      term current_slot = cm_v_phase_arg(concrete_phase, 8, 6);
      term scratch = cm_v_phase_arg(concrete_phase, 8, 7);
      thm bounds = conv_rule(reduce_rewrite_conv(THM_LIST(
          cm_v_spill_ready_def)), concrete_spill);
      gnode_list rest_cases = BOOL_CASES_TAC(cases[i],
          `${rest_args:(cm_expr)list} == []`, "Harg_rest");
      {
        thm rest_nil = assume_rule(
            `${rest_args:(cm_expr)list} == []`);
        thm ready_nil = conv_rule(reduce_rewrite_conv(THM_LIST(
            cm_v_phase_ready_def, rest_nil,
            cm_ann_cursors_def, cm_cursor_frames_def,
            get_theorem_by_name("TL"))), concrete_ready);
        thm call_ok = conjunct1_rule(ready_nil);
        thm depth = conjunct2_rule(ready_nil);
        thm spilled = specl_rule(TERM_LIST(
            `p:cm_program`, `fid:int`, `st:cm_src_state`,
            concrete_ann, current_slot, `v:cm_value`),
            cm_runtime_core_spill_put);
        spilled = match_mp_rule(spilled,
            assume_rule(`0i <= (fid:int)`));
        spilled = match_mp_rule(spilled,
            conjunct1_rule(conjunct2_rule(bounds)));
        spilled = match_mp_rule(spilled,
            conjunct2_rule(conjunct2_rule(bounds)));
        spilled = match_mp_rule(spilled, concrete_core);
        term spilled_ann =
            `cm_ann_put_spill ${current_slot:int} (v:cm_value)
              ${concrete_ann:cm_annotation}`;
        thm popped = cm_v_pop(concrete_phase, spilled_ann,
            `st:cm_src_state`, `pc:int`, spilled);
        thm normalized_parent = conv_rule(
            reduce_rewrite_conv(cm_v_annotation_rules()), popped);
        term parent_ann =
            `CMAnnotation (pc:int) (owner:int) (saved_break:int)
              (saved_continue:int) (rest:(cm_acursor)list)
              (cm_spill_put ${current_slot:int} (v:cm_value)
                (spills:(cm_spill)list))
              (saved:(cm_spill_frame)list)
              (calls:(cm_call_sim_frame)list)`;
        thm entered = specl_rule(TERM_LIST(
            `p:cm_program`, `fid:int`, callee,
            `REVERSE ((v:cm_value) :: ${values:(cm_value)list})`,
            `st:cm_src_state`, ret,
            `(pc:int) + ilength
              (cm_temp_store_code (p:cm_program) (fid:int)
                ${current_slot:int}) +
              ilength
                (cm_emit_args_reload p fid ${base_slot:int}
                  ${all_args:(cm_expr)list}) + 1i`,
            `owner:int`, `saved_break:int`, `saved_continue:int`,
            parent_ann), cm_runtime_core_enter_call);
        entered = match_mp_rule(entered,
            assume_rule(`cm_typed_program (p:cm_program)`));
        entered = match_mp_rule(entered, call_ok);
        entered = match_mp_rule(entered, normalized_parent);
        entered = conv_rule(reduce_rewrite_conv(
            cm_v_annotation_rules()), entered);
        cm_v_accept(rest_cases[0], entered, phase_shape,
            frames_eq, THM_LIST(rest_nil, call_ok, depth));
      }
      {
        thm replaced = cm_v_replace_and_spill(
            concrete_phase,
            `CAArgP ${callee:int} (TL ${rest_args:(cm_expr)list})
              ((v:cm_value) :: ${values:(cm_value)list})
              ${ret:cm_type} ${all_args:(cm_expr)list}
              ${base_slot:int} (${current_slot:int} + 1i)
              ${scratch:int}`,
            concrete_ann, `st:cm_src_state`,
            `(pc:int) + ilength
              (cm_temp_store_code (p:cm_program) (fid:int)
                ${current_slot:int})`,
            scratch, `breakpc:int`, `continuepc:int`,
            current_slot, `v:cm_value`,
            conjunct1_rule(conjunct2_rule(bounds)),
            conjunct2_rule(conjunct2_rule(bounds)),
            concrete_core);
        cm_v_accept(rest_cases[1], replaced, phase_shape,
            frames_eq, THM_LIST());
      }
      continue;
    }
    cm_v_accept(cases[i], result, phase_shape, frames_eq,
        THM_LIST());
  }
  return gnode_prove(root);
}
PROOF thm cm_task_runtime_v_phase_step =
    cm_prove_task_runtime_v_phase_step();

PROOF static thm cm_prove_task_runtime_v_step(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (v:cm_value)
         (st:cm_src_state) (ks:(cm_frame)list)
         (ann:cm_annotation).
         cm_typed_program p ==>
         (~(cm_ann_cursors ann == []) ==>
          (cm_phase_is_halt
             (cm_cursor_phase (HD (cm_ann_cursors ann))) ||
           0i <= fid)) ==>
         cm_annotation_erases (CMVTask p fid v st ks) ann ==>
         cm_v_layout_ready p v st ann ==>
         (~(cm_ann_cursors ann == []) ==>
          cm_v_spill_ready p fid ann
            (cm_cursor_phase (HD (cm_ann_cursors ann)))) ==>
         (~(cm_ann_cursors ann == []) ==>
          cm_v_source_ready p fid st
            (cm_cursor_phase (HD (cm_ann_cursors ann)))) ==>
         cm_runtime_core p fid st ann ==>
         cm_task_runtime_invariant p
           (cm_step (CMVTask p fid v st ks))
           (cm_update_annotation
             (cm_annotation_step
               (CMVTask p fid v st ks) ann))`);
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list ann_cases = DISJ_CASES_TAC(
      introduced,
      ispec_rule(`ann:cm_annotation`,
        get_datatype_cases("cm_annotation")),
      "Hann");
  gnode branch = ann_cases[0];
  while (true) {
    labeled_term_list assumptions = goal_lasmps(branch->g);
    int index = labeled_term_list_index(assumptions, "Hann");
    if (!is_exists(assumptions[index].tm)) break;
    branch = ASMP_EXISTS_TAC(branch, "Hann", NULL);
  }
  thm ann_shape = assume_rule(
      goal_lasmps(branch->g)[labeled_term_list_index(
        goal_lasmps(branch->g), "Hann")].tm);
  term cursors = cm_v_app_arg_from_right(
      rhs_of(ann_shape), 3);
  gnode_list cursor_cases = DISJ_CASES_TAC(branch,
      ispec_rule(cursors, get_theorem_by_name("list_CASES")),
      "Hcursors");
  {
    thm cursors_nil = assume_rule(
        goal_lasmps(cursor_cases[0]->g)[
          labeled_term_list_index(
            goal_lasmps(cursor_cases[0]->g), "Hcursors")].tm);
    thm shaped_core = conv_rule(rewrite_conv(THM_LIST(
        ann_shape, cursors_nil)), assume_rule(
          `cm_runtime_core (p:cm_program) (fid:int)
            (st:cm_src_state) (ann:cm_annotation)`));
    thm impossible = conv_rule(reduce_rewrite_conv(THM_LIST(
        cm_runtime_core_def, cm_runtime_stack_def,
        cm_ann_cursors_def)), shaped_core);
    CONTR_TAC(cursor_cases[0], impossible);
  }
  gnode cons = ASMP_EXISTS_TAC(
      cursor_cases[1], "Hcursors", NULL);
  cons = ASMP_EXISTS_TAC(cons, "Hcursors", NULL);
  thm cursors_cons = assume_rule(
      goal_lasmps(cons->g)[labeled_term_list_index(
        goal_lasmps(cons->g), "Hcursors")].tm);
  term cursor = cm_v_app_arg_from_right(
      rhs_of(cursors_cons), 1);
  gnode_list cursor_shapes = DISJ_CASES_TAC(cons,
      ispec_rule(cursor, get_datatype_cases("cm_acursor")),
      "Hcursor");
  gnode cursor_branch = cursor_shapes[0];
  while (true) {
    labeled_term_list assumptions = goal_lasmps(cursor_branch->g);
    int index = labeled_term_list_index(assumptions, "Hcursor");
    if (!is_exists(assumptions[index].tm)) break;
    cursor_branch = ASMP_EXISTS_TAC(
        cursor_branch, "Hcursor", NULL);
  }
  thm cursor_shape = assume_rule(
      goal_lasmps(cursor_branch->g)[labeled_term_list_index(
        goal_lasmps(cursor_branch->g), "Hcursor")].tm);
  thm full_shape = conv_rule(rewrite_conv(THM_LIST(
      cursors_cons, cursor_shape)), ann_shape);
  term shaped_ann = rhs_of(full_shape);
  term pc_value = cm_v_phase_arg(shaped_ann, 8, 0);
  term temp_value = cm_v_phase_arg(shaped_ann, 8, 1);
  term break_value = cm_v_phase_arg(shaped_ann, 8, 2);
  term continue_value = cm_v_phase_arg(shaped_ann, 8, 3);
  term spills_value = cm_v_phase_arg(shaped_ann, 8, 5);
  term saved_value = cm_v_phase_arg(shaped_ann, 8, 6);
  term calls_value = cm_v_phase_arg(shaped_ann, 8, 7);
  term shaped_cursor = rhs_of(cursor_shape);
  term phase_value = cm_v_phase_arg(shaped_cursor, 4, 0);
  term owner_value = cm_v_phase_arg(shaped_cursor, 4, 1);
  term owner_break_value = cm_v_phase_arg(shaped_cursor, 4, 2);
  term owner_continue_value = cm_v_phase_arg(shaped_cursor, 4, 3);
  term rest_value = cm_v_app_arg_from_right(
      rhs_of(cursors_cons), 0);
  thm nonempty = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        cm_ann_cursors_def, get_theorem_by_name("NOT_CONS_NIL"))),
      `~(cm_ann_cursors ${shaped_ann:cm_annotation} == [])`));
  thm original_nonempty = conv_rule(
      rewrite_conv(THM_LIST(sym_rule(full_shape))), nonempty);
  thm fid_ready = match_mp_rule(assume_rule(
      `~(cm_ann_cursors (ann:cm_annotation) == []) ==>
       (cm_phase_is_halt
          (cm_cursor_phase (HD (cm_ann_cursors ann))) ||
        0i <= (fid:int))`), original_nonempty);
  fid_ready = conv_rule(reduce_rewrite_conv(THM_LIST(
      full_shape, cm_ann_cursors_def, cm_cursor_phase_def,
      get_theorem_by_name("HD"))), fid_ready);
  thm result = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `v:cm_value`,
      `st:cm_src_state`, `ks:(cm_frame)list`,
      pc_value, temp_value, break_value, continue_value,
      phase_value, owner_value, owner_break_value,
      owner_continue_value, rest_value, spills_value,
      saved_value, calls_value),
      cm_task_runtime_v_phase_step);
  thm_list premises = THM_LIST(
      assume_rule(`cm_typed_program (p:cm_program)`),
      fid_ready,
      conv_rule(rewrite_conv(THM_LIST(full_shape)),
        assume_rule(
          `cm_annotation_erases
            (CMVTask (p:cm_program) (fid:int) (v:cm_value)
              (st:cm_src_state) (ks:(cm_frame)list))
            (ann:cm_annotation)`)),
      conv_rule(rewrite_conv(THM_LIST(full_shape)),
        assume_rule(
          `cm_v_layout_ready (p:cm_program) (v:cm_value)
            (st:cm_src_state) (ann:cm_annotation)`)));
  for (size_t i = 0; i < vector_size(premises); ++i) {
    result = match_mp_rule(result, premises[i]);
  }
  thm spill = match_mp_rule(assume_rule(
      `~(cm_ann_cursors (ann:cm_annotation) == []) ==>
       cm_v_spill_ready (p:cm_program) (fid:int) ann
         (cm_cursor_phase (HD (cm_ann_cursors ann)))`),
      original_nonempty);
  spill = conv_rule(reduce_rewrite_conv(THM_LIST(
      full_shape, cm_ann_cursors_def, cm_cursor_phase_def,
      get_theorem_by_name("HD"))), spill);
  result = match_mp_rule(result, spill);
  thm source = match_mp_rule(assume_rule(
      `~(cm_ann_cursors (ann:cm_annotation) == []) ==>
       cm_v_source_ready (p:cm_program) (fid:int)
         (st:cm_src_state)
         (cm_cursor_phase (HD (cm_ann_cursors ann)))`),
      original_nonempty);
  source = conv_rule(reduce_rewrite_conv(THM_LIST(
      full_shape, cm_ann_cursors_def, cm_cursor_phase_def,
      get_theorem_by_name("HD"))), source);
  result = match_mp_rule(result, source);
  result = match_mp_rule(result,
      conv_rule(rewrite_conv(THM_LIST(full_shape)),
        assume_rule(
          `cm_runtime_core (p:cm_program) (fid:int)
            (st:cm_src_state) (ann:cm_annotation)`)));
  gnode reduced = CONV_TAC(cursor_branch,
      rewrite_conv(THM_LIST(full_shape)));
  ACCEPT_TAC(reduced, result);
  return gnode_prove(root);
}
PROOF thm cm_task_runtime_v_step =
    cm_prove_task_runtime_v_step();

PROOF static int cmc_preservation_invariant_value_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_invariant_value_axioms_before,
      "cmc_preservation_invariant_value introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_invariant_value_checks =
    cmc_preservation_invariant_value_final_checks();
