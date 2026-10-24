#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_invariant_control.h"

#require "cmc_preservation_invariant_value.c"

PROOF static size_t _cmc_preservation_invariant_control_axioms_before =
    vector_size(get_all_axioms());

PROOF static term cm_ci_app_arg_from_right(
    term application, size_t offset) {
  for (size_t i = 0; i < offset; ++i) {
    application = dest_comb(application).tm1;
  }
  return dest_comb(application).tm2;
}

PROOF static term cm_ci_constructor_arg(
    term constructor, size_t arity, size_t index) {
  return cm_ci_app_arg_from_right(
      constructor, arity - index - 1);
}

PROOF static term cm_ci_runtime_annotation(term phase) {
  return `CMAnnotation (pc:int) (temp:int) (breakpc:int)
    (continuepc:int)
    (CMACursor ${phase:cm_aphase} (owner:int)
       (saved_break:int) (saved_continue:int) ::
     (rest:(cm_acursor)list))
    (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
    (calls:(cm_call_sim_frame)list)`;
}

PROOF static thm_list cm_ci_annotation_rules(void) {
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
      cm_call_sim_base_def, cm_call_sim_saved_def,
      cm_call_sim_return_def,
      cm_spill_frame_fid_def, cm_spill_frame_fp_def,
      cm_spill_frame_spills_def,
      get_theorem_by_name("HD"), get_theorem_by_name("TL"));
}

PROOF static thm cm_ci_cursor_eq(term ann, term phase) {
  return eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(cm_ci_annotation_rules()),
      `cm_ann_cursors ${ann:cm_annotation} ==
       CMACursor ${phase:cm_aphase} (owner:int)
         (saved_break:int) (saved_continue:int) ::
       (rest:(cm_acursor)list)`));
}

PROOF static thm cm_ci_consequence(thm source, term consequence) {
  return mp_rule(taut_rule(mk_imp(concl(source), consequence)), source);
}

PROOF static thm cm_ci_pop_plain(
    term phase, term ann, term st, term nextpc, thm core) {
  thm result = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, st, ann, phase,
      `owner:int`, `saved_break:int`, `saved_continue:int`,
      `rest:(cm_acursor)list`, nextpc),
      cm_runtime_core_pop_plain);
  result = match_mp_rule(result, cm_ci_cursor_eq(ann, phase));
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

PROOF static thm cm_ci_leave_scope(
    term phase, term ann, term st, term oldenv,
    term oldregions, term nextpc, thm core) {
  thm result = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, st, ann, phase,
      oldenv, oldregions, `owner:int`, `saved_break:int`,
      `saved_continue:int`, `rest:(cm_acursor)list`, nextpc),
      cm_runtime_core_leave_scope);
  result = match_mp_rule(result, cm_ci_cursor_eq(ann, phase));
  thm_list phase_rules = THM_LIST(
      cm_phase_is_scope_def, cm_phase_is_call_def,
      cm_phase_oldregions_def);
  for (size_t i = 0; i < 3; ++i) {
    result = match_mp_rule(result, eqt_elim_rule(
        apply_conversion(reduce_rewrite_conv(phase_rules),
          dest_imp(concl(result)).tm1)));
  }
  return match_mp_rule(result, core);
}

PROOF static thm cm_ci_leave_scope_replace_plain(
    term oldphase, term newphase, term ann, term st,
    term oldenv, term oldregions, term newpc, term newtemp,
    term newbreak, term newcontinue, thm core) {
  thm left = cm_ci_leave_scope(
      oldphase, ann, st, oldenv, oldregions, newpc, core);
  term restored =
      `cm_restore_scope ${st:cm_src_state}
        ${oldenv:int->int->cm_value}
        ${oldregions:(cm_region)list}`;
  term popped = `cm_ann_pop ${newpc:int} ${ann:cm_annotation}`;
  thm result = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, restored, popped, newphase,
      newpc, newtemp, newbreak, newcontinue),
      cm_runtime_core_push_plain);
  thm_list phase_rules = THM_LIST(
      cm_phase_is_call_def, cm_phase_is_scope_def,
      cm_phase_is_halt_def);
  for (size_t i = 0; i < 3; ++i) {
    result = match_mp_rule(result, eqt_elim_rule(
        apply_conversion(reduce_rewrite_conv(phase_rules),
          dest_imp(concl(result)).tm1)));
  }
  return match_mp_rule(result, left);
}

PROOF static thm cm_prove_ci_spill_frame_reconstruct(void) {
  gnode root = gnode_new_with_ccl(
      `!(frame:cm_spill_frame).
         CMSpillFrame (cm_spill_frame_fid frame)
           (cm_spill_frame_fp frame)
           (cm_spill_frame_spills frame) == frame`);
  gnode_list cases = INDUCT_TAC(root, `frame:cm_spill_frame`);
  CONV_TAC(cases[0], reduce_rewrite_conv(THM_LIST(
      cm_spill_frame_fid_def, cm_spill_frame_fp_def,
      cm_spill_frame_spills_def)));
  return gnode_prove(root);
}
PROOF static thm cm_ci_spill_frame_reconstruct =
    cm_prove_ci_spill_frame_reconstruct();

PROOF static thm cm_prove_ci_call_frame_reconstruct(void) {
  gnode root = gnode_new_with_ccl(
      `!(frame:cm_call_sim_frame).
         CMCallSimFrame (cm_call_sim_base frame)
           (cm_call_sim_saved frame)
           (cm_call_sim_return frame) == frame`);
  gnode_list cases = INDUCT_TAC(root, `frame:cm_call_sim_frame`);
  CONV_TAC(cases[0], reduce_rewrite_conv(THM_LIST(
      cm_call_sim_base_def, cm_call_sim_saved_def,
      cm_call_sim_return_def)));
  return gnode_prove(root);
}
PROOF static thm cm_ci_call_frame_reconstruct =
    cm_prove_ci_call_frame_reconstruct();

PROOF static thm cm_ci_cons_reconstruct(
    term list_value, term cons_constant, term tail_value,
    thm head_reconstruct, thm nonempty) {
  thm list_shape = mp_rule(
      ispec_rule(list_value, get_theorem_by_name("CONS_HD_TL")),
      nonempty);
  thm rebuilt = mk_comb_rule(mk_comb_rule(
      refl_rule(cons_constant), head_reconstruct),
      refl_rule(tail_value));
  return sym_rule(trans_rule(rebuilt, sym_rule(list_shape)));
}

PROOF static thm cm_ci_leave_call(
    term phase, term ann, term st, term caller, term oldenv,
    term oldfp, term oldregions, term ret, term targetpc,
    thm core) {
  thm opened_core = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_runtime_core_def, cm_ann_cursors_def,
      cm_ann_spills_def, cm_ann_saved_def, cm_ann_calls_def)), core);
  thm stack = conjunct2_rule(opened_core);
  thm opened_stack = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_runtime_stack_def, cm_cursor_phase_def,
      cm_phase_is_call_def, cm_phase_oldregions_def,
      cm_phase_oldfp_def, cm_phase_caller_def)), stack);
  term saved_list = cm_ci_constructor_arg(ann, 8, 6);
  term calls_list = cm_ci_constructor_arg(ann, 8, 7);
  thm saved_nonempty = cm_ci_consequence(opened_stack,
      `~(${saved_list:(cm_spill_frame)list} == [])`);
  thm calls_nonempty = cm_ci_consequence(opened_stack,
      `~(${calls_list:(cm_call_sim_frame)list} == [])`);
  thm saved_fid = cm_ci_consequence(opened_stack,
      `cm_spill_frame_fid
         (HD ${saved_list:(cm_spill_frame)list}) == ${caller:int}`);
  thm saved_fp = cm_ci_consequence(opened_stack,
      `cm_spill_frame_fp
         (HD ${saved_list:(cm_spill_frame)list}) == ${oldfp:int}`);
  thm call_base = cm_ci_consequence(opened_stack,
      `cm_call_sim_base
         (HD ${calls_list:(cm_call_sim_frame)list}) ==
       cm_state_fp ${st:cm_src_state}`);
  thm call_saved = cm_ci_consequence(opened_stack,
      `cm_call_sim_saved
         (HD ${calls_list:(cm_call_sim_frame)list}) == ${oldfp:int}`);
  thm saved_head = spec_rule(
      `HD ${saved_list:(cm_spill_frame)list}`,
      cm_ci_spill_frame_reconstruct);
  saved_head = conv_rule(
      rewrite_conv(THM_LIST(saved_fid, saved_fp)), saved_head);
  thm saved_shape = cm_ci_cons_reconstruct(
      saved_list,
      `CONS:cm_spill_frame->(cm_spill_frame)list->
        (cm_spill_frame)list`,
      `TL ${saved_list:(cm_spill_frame)list}`,
      saved_head, saved_nonempty);
  thm call_head = spec_rule(
      `HD ${calls_list:(cm_call_sim_frame)list}`,
      cm_ci_call_frame_reconstruct);
  call_head = conv_rule(
      rewrite_conv(THM_LIST(call_base, call_saved)), call_head);
  thm calls_shape = cm_ci_cons_reconstruct(
      calls_list,
      `CONS:cm_call_sim_frame->(cm_call_sim_frame)list->
        (cm_call_sim_frame)list`,
      `TL ${calls_list:(cm_call_sim_frame)list}`,
      call_head, calls_nonempty);
  thm result = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, caller, st, ann,
      oldenv, oldfp, oldregions, ret,
      `owner:int`, `saved_break:int`, `saved_continue:int`,
      `rest:(cm_acursor)list`,
      `cm_spill_frame_spills
        (HD ${saved_list:(cm_spill_frame)list})`,
      `TL ${saved_list:(cm_spill_frame)list}`,
      `cm_call_sim_return
        (HD ${calls_list:(cm_call_sim_frame)list})`,
      `TL ${calls_list:(cm_call_sim_frame)list}`, targetpc),
      cm_runtime_core_leave_call);
  result = match_mp_rule(result, cm_ci_cursor_eq(ann, phase));
  result = conv_rule(rewrite_conv(THM_LIST(
      cm_ann_saved_def, cm_ann_calls_def)), result);
  result = match_mp_rule(result, saved_shape);
  result = match_mp_rule(result, calls_shape);
  return match_mp_rule(result, core);
}

PROOF static void cm_ci_accept(
    gnode branch, thm result, thm phase_shape,
    thm control_shape, thm frames_eq, thm_list extra) {
  thm_list rules = THM_LIST(
      phase_shape, control_shape, sym_rule(frames_eq),
      get_cm_step_def(), get_cm_capply_def(),
      get_cm_control_kind_def(), get_cm_control_value_def(),
      get_cm_control_status_def(), cm_annotation_step_def,
      cm_update_annotation_def, cm_update_c_def,
      cm_ann_plain_def, cm_ann_linear_def, cm_ann_done_def,
      cm_ann_push_def, cm_ann_replace_def, cm_ann_pop_def,
      cm_ann_spills_set_def, cm_ann_put_spill_def,
      cm_ann_enter_call_def, cm_ann_leave_call_def,
      cm_task_runtime_invariant_def, cm_runtime_core_def,
      cm_cursor_frames_def, cm_phase_frame_def,
      cm_ann_pc_def, cm_ann_temp_def, cm_ann_break_def,
      cm_ann_continue_def, cm_ann_cursors_def,
      cm_ann_spills_def, cm_ann_saved_def, cm_ann_calls_def,
      cm_cursor_phase_def, cm_cursor_temp_def,
      cm_cursor_break_def, cm_cursor_continue_def,
      cm_call_sim_return_def,
      get_theorem_by_name("HD"), get_theorem_by_name("TL"),
      get_theorem_by_name("NOT_CONS_NIL"));
  for (size_t i = 0; i < vector_size(extra); ++i) {
    vector_add(&rules, extra[i]);
  }
  thm expanded = conv_rule(reduce_rewrite_conv(rules), result);
  gnode reduced =
      CONV_WITH_ASMP_TAC(branch, reduce_rewrite_conv, rules);
  if (IS_NULL(reduced->solved)) {
    reduced = CONV_WITH_ASMP_TAC(
        reduced, reduce_rewrite_conv, rules);
  }
  if (IS_NULL(reduced->solved)) {
    ACCEPT_TAC(reduced, mp_rule(taut_rule(mk_imp(
        concl(expanded), goal_ccl(reduced->g))), expanded));
  }
}

PROOF static thm cm_prove_task_runtime_c_phase_step(void) {
  term phase = `phase:cm_aphase`;
  term ann = cm_ci_runtime_annotation(phase);
  term task =
      `CMCTask (p:cm_program) (fid:int) (ctl:cm_control)
        (st:cm_src_state) (ks:(cm_frame)list)`;
  term body = imp_chain(TERM_LIST(
      `cm_annotation_erases ${task:cm_task} ${ann:cm_annotation}`,
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
  thm core = assume_rule(
      `cm_runtime_core (p:cm_program) (fid:int)
        (st:cm_src_state) ${ann:cm_annotation}`);
  gnode_list phase_cases = DISJ_CASES_TAC(
      introduced,
      ispec_rule(phase, get_datatype_cases("cm_aphase")),
      "Hphase");
  for (size_t i = 0; i < vector_size(phase_cases); ++i) {
    gnode phase_branch = phase_cases[i];
    while (true) {
      labeled_term_list assumptions = goal_lasmps(phase_branch->g);
      int index = labeled_term_list_index(assumptions, "Hphase");
      if (!is_exists(assumptions[index].tm)) break;
      phase_branch = ASMP_EXISTS_TAC(
          phase_branch, "Hphase", NULL);
    }
    thm phase_shape = assume_rule(
        goal_lasmps(phase_branch->g)[labeled_term_list_index(
          goal_lasmps(phase_branch->g), "Hphase")].tm);
    term concrete_phase = rhs_of(phase_shape);
    term concrete_ann = cm_ci_runtime_annotation(concrete_phase);
    thm concrete_core = conv_rule(
        rewrite_conv(THM_LIST(phase_shape)), core);
    gnode_list control_cases = DISJ_CASES_TAC(
        phase_branch,
        ispec_rule(`ctl:cm_control`,
          get_datatype_cases("cm_control")),
        "Hcontrol");
    for (size_t j = 0; j < vector_size(control_cases); ++j) {
      gnode control_branch = control_cases[j];
      while (true) {
        labeled_term_list assumptions =
            goal_lasmps(control_branch->g);
        int index = labeled_term_list_index(
            assumptions, "Hcontrol");
        if (!is_exists(assumptions[index].tm)) break;
        control_branch = ASMP_EXISTS_TAC(
            control_branch, "Hcontrol", NULL);
      }
      thm control_shape = assume_rule(
          goal_lasmps(control_branch->g)[labeled_term_list_index(
            goal_lasmps(control_branch->g), "Hcontrol")].tm);
      term concrete_control = rhs_of(control_shape);
      thm result = empty_theorem;
      if (j == 4) {
        term status = cm_ci_constructor_arg(concrete_control, 1, 0);
        result = specl_rule(TERM_LIST(
            `p:cm_program`, `fid:int`, `st:cm_src_state`,
            concrete_ann, concrete_control, status,
            `cm_ann_done ${concrete_ann:cm_annotation}`),
            cm_runtime_core_done);
        result = match_mp_rule(result, concrete_core);
      } else if (i == 0) {
        term status = `2i`;
        if (j == 0) {
          status = `0i`;
        } else if (j == 3) {
          term value = cm_ci_constructor_arg(
              concrete_control, 1, 0);
          status = `tower_status
            (cm_value_number (st:cm_src_state) ${value:cm_value})`;
        }
        result = match_mp_rule(specl_rule(TERM_LIST(
            `p:cm_program`, `fid:int`, `st:cm_src_state`,
            concrete_ann, `owner:int`, `saved_break:int`,
            `saved_continue:int`, `rest:(cm_acursor)list`,
            concrete_control, status, `pc:int`),
            cm_runtime_halt_done),
            cm_ci_cursor_eq(concrete_ann, concrete_phase));
        result = match_mp_rule(result, concrete_core);
      } else if (i == 15) {
        term oldenv = cm_ci_constructor_arg(
            concrete_phase, 4, 0);
        term oldregions = cm_ci_constructor_arg(
            concrete_phase, 4, 1);
        term jump = cm_ci_constructor_arg(
            concrete_phase, 4, 2);
        term target = cm_ci_constructor_arg(
            concrete_phase, 4, 3);
        term nextpc =
            `if cm_control_kind ${concrete_control:cm_control} == 0i &&
                ${jump:bool}
             then ${target:int}
             else (pc:int)`;
        result = cm_ci_leave_scope(
            concrete_phase, concrete_ann, `st:cm_src_state`,
            oldenv, oldregions, nextpc, concrete_core);
        gnode_list jump_cases = BOOL_CASES_TAC(
            control_branch, jump, "Hjump");
        for (size_t k = 0; k < vector_size(jump_cases); ++k) {
          thm jump_shape = assume_rule(
              goal_lasmps(jump_cases[k]->g)[labeled_term_list_index(
                goal_lasmps(jump_cases[k]->g), "Hjump")].tm);
          cm_ci_accept(jump_cases[k], result, phase_shape,
              control_shape, frames_eq, THM_LIST(jump_shape));
        }
        continue;
      } else if (i == 19) {
        term guard = cm_ci_constructor_arg(
            concrete_phase, 6, 0);
        term loop_body = cm_ci_constructor_arg(
            concrete_phase, 6, 1);
        term oldenv = cm_ci_constructor_arg(
            concrete_phase, 6, 2);
        term oldregions = cm_ci_constructor_arg(
            concrete_phase, 6, 3);
        term loop_start = cm_ci_constructor_arg(
            concrete_phase, 6, 4);
        term loop_end = cm_ci_constructor_arg(
            concrete_phase, 6, 5);
        if (j == 0 || j == 2) {
          term nextphase =
              `CAWhileGuardP ${guard:cm_expr} ${loop_body:cm_stmt}
                ${loop_start:int} ${loop_end:int}`;
          result = cm_ci_leave_scope_replace_plain(
              concrete_phase, nextphase, concrete_ann,
              `st:cm_src_state`, oldenv, oldregions,
              loop_start, `owner:int`, loop_end, loop_start,
              concrete_core);
        } else if (j == 1) {
          result = cm_ci_leave_scope(
              concrete_phase, concrete_ann, `st:cm_src_state`,
              oldenv, oldregions, loop_end, concrete_core);
        } else {
          result = cm_ci_leave_scope(
              concrete_phase, concrete_ann, `st:cm_src_state`,
              oldenv, oldregions, `pc:int`, concrete_core);
        }
      } else if (i == 22) {
        term caller = cm_ci_constructor_arg(
            concrete_phase, 5, 0);
        term oldenv = cm_ci_constructor_arg(
            concrete_phase, 5, 1);
        term oldfp = cm_ci_constructor_arg(
            concrete_phase, 5, 2);
        term oldregions = cm_ci_constructor_arg(
            concrete_phase, 5, 3);
        term ret = cm_ci_constructor_arg(
            concrete_phase, 5, 4);
        term targetpc = `pc:int`;
        if (j == 0 || j == 3) {
          targetpc =
              `cm_call_sim_return
                (HD (cm_ann_calls ${concrete_ann:cm_annotation}))`;
        }
        result = cm_ci_leave_call(
            concrete_phase, concrete_ann, `st:cm_src_state`,
            caller, oldenv, oldfp, oldregions, ret, targetpc,
            concrete_core);
      } else {
        result = cm_ci_pop_plain(
            concrete_phase, concrete_ann, `st:cm_src_state`,
            `pc:int`, concrete_core);
      }
      cm_ci_accept(control_branch, result, phase_shape,
          control_shape, frames_eq, THM_LIST());
    }
  }
  return gnode_prove(root);
}
PROOF static thm cm_task_runtime_c_phase_step =
    cm_prove_task_runtime_c_phase_step();

PROOF static thm cm_prove_task_runtime_c_step(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (ctl:cm_control)
         (st:cm_src_state) (ks:(cm_frame)list)
         (ann:cm_annotation).
         cm_annotation_erases (CMCTask p fid ctl st ks) ann ==>
         cm_runtime_core p fid st ann ==>
         cm_task_runtime_invariant p
           (cm_step (CMCTask p fid ctl st ks))
           (cm_update_annotation
             (cm_annotation_step
               (CMCTask p fid ctl st ks) ann))`);
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
  term cursors = cm_ci_app_arg_from_right(
      rhs_of(ann_shape), 3);
  gnode_list cursor_cases = DISJ_CASES_TAC(
      branch,
      ispec_rule(cursors, get_theorem_by_name("list_CASES")),
      "Hcursors");
  {
    thm cursors_nil = assume_rule(
        goal_lasmps(cursor_cases[0]->g)[labeled_term_list_index(
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
  term cursor = cm_ci_app_arg_from_right(
      rhs_of(cursors_cons), 1);
  gnode_list cursor_shapes = DISJ_CASES_TAC(
      cons,
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
  term pc_value = cm_ci_constructor_arg(shaped_ann, 8, 0);
  term temp_value = cm_ci_constructor_arg(shaped_ann, 8, 1);
  term break_value = cm_ci_constructor_arg(shaped_ann, 8, 2);
  term continue_value = cm_ci_constructor_arg(shaped_ann, 8, 3);
  term spills_value = cm_ci_constructor_arg(shaped_ann, 8, 5);
  term saved_value = cm_ci_constructor_arg(shaped_ann, 8, 6);
  term calls_value = cm_ci_constructor_arg(shaped_ann, 8, 7);
  term shaped_cursor = rhs_of(cursor_shape);
  term phase_value = cm_ci_constructor_arg(shaped_cursor, 4, 0);
  term owner_value = cm_ci_constructor_arg(shaped_cursor, 4, 1);
  term owner_break_value = cm_ci_constructor_arg(shaped_cursor, 4, 2);
  term owner_continue_value = cm_ci_constructor_arg(shaped_cursor, 4, 3);
  term rest_value = cm_ci_app_arg_from_right(
      rhs_of(cursors_cons), 0);
  thm result = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `ctl:cm_control`,
      `st:cm_src_state`, `ks:(cm_frame)list`,
      pc_value, temp_value, break_value, continue_value,
      phase_value, owner_value, owner_break_value,
      owner_continue_value, rest_value, spills_value,
      saved_value, calls_value),
      cm_task_runtime_c_phase_step);
  result = match_mp_rule(result,
      conv_rule(rewrite_conv(THM_LIST(full_shape)),
        assume_rule(
          `cm_annotation_erases
            (CMCTask (p:cm_program) (fid:int) (ctl:cm_control)
              (st:cm_src_state) (ks:(cm_frame)list))
            (ann:cm_annotation)`)));
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
PROOF thm cm_task_runtime_c_step =
    cm_prove_task_runtime_c_step();

PROOF static int cmc_preservation_invariant_control_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_invariant_control_axioms_before,
      "cmc_preservation_invariant_control introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_invariant_control_checks =
    cmc_preservation_invariant_control_final_checks();
