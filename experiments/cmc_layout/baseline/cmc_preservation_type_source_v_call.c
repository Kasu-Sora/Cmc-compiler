#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_type_source_v_call.h"
#include "cmc_preservation_type_source_v_helpers.h"
#include "cmc_preservation_type_args.h"
#include "cmc_preservation_type_facts.h"
#include "cmc_preservation_type_cursor.h"

#require "cmc_preservation_type_source_v_control.c"
#require "cmc_preservation_type_args.c"

PROOF static size_t _cmc_preservation_type_source_v_call_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_tvcall_tail_frames(term phase, thm erases) {
  thm cons_equal = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_annotation_erases_def, cm_ann_cursors_def,
      cm_cursor_frames_def, cm_cursor_phase_def)), erases);
  term head = `cm_phase_frame ${phase:cm_aphase}`;
  thm injective = ispecl_rule(TERM_LIST(
      head, head, `cm_cursor_frames (rest:(cm_acursor)list)`,
      `ks:(cm_frame)list`), get_theorem_by_name("CONS_11"));
  return conjunct2_rule(eq_mp_rule(injective, cons_equal));
}

PROOF static thm cm_tvcall_nonfinal(
    term old_phase, term callee, term pending, term values,
    term ret, term all_args, term base_slot, term current_slot,
    term scratch, thm ready, thm components, thm bounds,
    thm pending_nonempty, thm_list extra) {
  term function =
      `inth (fid:int) (cm_program_functions (p:cm_program))`;
  term params =
      `cm_function_params
        (inth ${callee:int} (cm_program_functions (p:cm_program)))`;
  term child = `HD ${pending:(cm_expr)list}`;
  term new_phase =
      `CAArgP ${callee:int} (TL ${pending:(cm_expr)list})
        ((incoming:cm_value) :: ${values:(cm_value)list})
        ${ret:cm_type} ${all_args:(cm_expr)list} ${base_slot:int}
        (${current_slot:int} + 1i) ${scratch:int}`;
  thm old_static = cm_tvs_pick_conjunct(components,
      `cm_phase_static_type_ready (p:cm_program) (fid:int)
        ${old_phase:cm_aphase}`);
  thm static_open = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_phase_static_type_ready_def())), old_static);
  thm callee_low = cm_tvs_pick_conjunct(static_open,
      `0i <= ${callee:int}`);
  thm callee_high = cm_tvs_pick_conjunct(static_open,
      `${callee:int} < ilength
        (cm_program_functions (p:cm_program))`);
  thm exprs_ready = cm_tvs_pick_conjunct(static_open,
      `cm_exprs_type_ready (p:cm_program) ${function:cm_function_d}
        ${pending:(cm_expr)list}`);
  thm args_wf = cm_tvs_pick_conjunct(static_open,
      `cm_args_wf (p:cm_program) ${function:cm_function_d}
        ${all_args:(cm_expr)list} ${params:(cm_slot_d)list}`);
  thm progress = cm_tvs_pick_conjunct(static_open,
      `cm_arg_progress_type_ready ${all_args:(cm_expr)list}
        ${params:(cm_slot_d)list}
        (REVERSE ${values:(cm_value)list})
        ${pending:(cm_expr)list}`);
  thm ret_equal = cm_tvs_pick_conjunct(static_open,
      `${ret:cm_type} == cm_function_ret
        (inth ${callee:int} (cm_program_functions (p:cm_program)))`);
  thm incoming_ready = cm_tvs_pick_conjunct(components,
      `cm_phase_value_type_ready (p:cm_program) (fid:int)
        ${old_phase:cm_aphase} (incoming:cm_value)`);
  incoming_ready = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_phase_value_type_ready_def())), incoming_ready);

  thm pending_shape = mp_rule(ispec_rule(pending,
      get_theorem_by_name("CONS_HD_TL")), pending_nonempty);
  thm exprs_view = beta_norm(ap_term_rule(
      `\xs:(cm_expr)list.
         cm_exprs_type_ready (p:cm_program) ${function:cm_function_d} xs`,
      pending_shape));
  thm exprs_shaped = eq_mp_rule(exprs_view, exprs_ready);
  thm exprs_open = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_exprs_type_ready_def, get_theorem_by_name("HD"),
      get_theorem_by_name("TL"))), exprs_shaped);
  thm child_wf = cm_tvs_pick_conjunct(exprs_open,
      `cm_expr_wf (p:cm_program) ${function:cm_function_d}
        ${child:cm_expr}`);
  thm child_scalar = cm_tvs_pick_conjunct(exprs_open,
      `cm_scalar_expr_type (cm_expr_type ${child:cm_expr})`);
  thm tail_ready = cm_tvs_pick_conjunct(exprs_open,
      `cm_exprs_type_ready (p:cm_program) ${function:cm_function_d}
        (TL ${pending:(cm_expr)list})`);

  thm new_progress = specl_rule(TERM_LIST(
      `REVERSE ${values:(cm_value)list}`, `p:cm_program`, function,
      all_args, params, pending, `incoming:cm_value`),
      cm_arg_progress_extend);
  new_progress = mp_rule(new_progress, args_wf);
  new_progress = mp_rule(new_progress, progress);
  new_progress = mp_rule(new_progress, pending_nonempty);
  new_progress = mp_rule(new_progress, incoming_ready);

  thm next_expr = specl_rule(TERM_LIST(
      `REVERSE ${values:(cm_value)list}`, `p:cm_program`, function,
      all_args, params, pending, `incoming:cm_value`),
      cm_arg_progress_next_expr);
  next_expr = mp_rule(next_expr, args_wf);
  next_expr = mp_rule(next_expr, progress);
  next_expr = mp_rule(next_expr, pending_nonempty);
  next_expr = mp_rule(next_expr, incoming_ready);

  thm new_static = cm_tvs_trivial(
      `cm_phase_static_type_ready (p:cm_program) (fid:int)
        ${new_phase:cm_aphase}`,
      THM_LIST(get_cm_phase_static_type_ready_def(), callee_low,
        callee_high, tail_ready, args_wf, new_progress, ret_equal,
        get_theorem_by_name("REVERSE")));
  thm old_parent = cm_tvs_pick_conjunct(components,
      `cm_phase_parent_type_ready (p:cm_program) (fid:int)
        ${old_phase:cm_aphase} (rest:(cm_acursor)list)`);
  thm parent_open = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_phase_parent_type_ready_def())), old_parent);
  thm parent_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
      get_cm_phase_parent_type_ready_def())),
      `cm_phase_parent_type_ready (p:cm_program) (fid:int)
        ${new_phase:cm_aphase} (rest:(cm_acursor)list)`);
  thm new_parent = eq_mp_rule(sym_rule(parent_view), parent_open);
  thm old_result = cm_tvs_pick_conjunct(components,
      `cm_phase_result_type_ready (p:cm_program) (fid:int)
        ${old_phase:cm_aphase} (rest:(cm_acursor)list)`);
  thm result_open = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_phase_result_type_ready_def(),
      get_cm_phase_result_type_def(), cm_phase_next_fid_def)),
      old_result);
  thm result_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
      get_cm_phase_result_type_ready_def(),
      get_cm_phase_result_type_def(), cm_phase_next_fid_def)),
      `cm_phase_result_type_ready (p:cm_program) (fid:int)
        ${new_phase:cm_aphase} (rest:(cm_acursor)list)`);
  thm new_result = eq_mp_rule(sym_rule(result_view), result_open);
  thm old_next = cm_tvs_trivial(
      `cm_phase_next_fid (fid:int) ${old_phase:cm_aphase} == fid`,
      THM_LIST(cm_phase_next_fid_def));
  thm new_next = cm_tvs_trivial(
      `cm_phase_next_fid (fid:int) ${new_phase:cm_aphase} == fid`,
      THM_LIST(cm_phase_next_fid_def));
  thm new_input = cm_tvs_trivial(
      `cm_phase_input_type_ready (p:cm_program) (fid:int)
        ${new_phase:cm_aphase} (cm_expr_type ${child:cm_expr})`,
      THM_LIST(get_cm_phase_input_type_ready_def()));
  thm new_expr = cm_tvs_trivial(
      `cm_phase_expr_type_ready (p:cm_program) (fid:int)
        ${new_phase:cm_aphase} ${child:cm_expr}`,
      THM_LIST(get_cm_phase_expr_type_ready_def(), next_expr,
        get_theorem_by_name("REVERSE")));
  term next_ann = cm_tvs_next_annotation(old_phase);
  thm cursor_equal = cm_tvs_cursor_fact(old_phase,
      `CMACursor ${new_phase:cm_aphase} (parent_temp:int)
         (parent_break:int) (parent_continue:int) ::
       (rest:(cm_acursor)list)`, extra);
  thm proved = specl_rule(TERM_LIST(
      `p:cm_program`, `q:cm_program`, `fid:int`, `incoming:cm_value`,
      `st:cm_src_state`, `st:cm_src_state`,
      `cm_phase_frame ${old_phase:cm_aphase} :: (ks:(cm_frame)list)`,
      `CMArgK ${callee:int} (TL ${pending:(cm_expr)list})
         ((incoming:cm_value) :: ${values:(cm_value)list})
         ${ret:cm_type} :: (ks:(cm_frame)list)`,
      old_phase, new_phase, child, `pc:int`, `temp:int`,
      `breakpc:int`, `continuepc:int`, `parent_temp:int`,
      `parent_break:int`, `parent_continue:int`,
      `rest:(cm_acursor)list`, `spills:(cm_spill)list`,
      `saved:(cm_spill_frame)list`, `calls:(cm_call_sim_frame)list`,
      next_ann), cm_v_replace_r_task_ready);
  thm_list premises = THM_LIST(ready, conjunct1_rule(bounds),
      conjunct2_rule(bounds), old_next, child_wf, child_scalar,
      new_static, new_parent, new_result, new_next, new_input,
      new_expr, cursor_equal);
  for (size_t i = 0; i < vector_size(premises); ++i) {
    proved = mp_rule(proved, premises[i]);
  }
  return proved;
}

PROOF static thm cm_tvcall_enter(
    term old_phase, term callee, term values, term ret,
    thm ready, thm components, thm typed, thm bounds,
    thm pending_empty, thm frame_equal, thm call_ready,
    thm same_program) {
  term callee_function =
      `inth ${callee:int} (cm_program_functions (p:cm_program))`;
  term new_phase =
      `CACallP (fid:int) (cm_state_env (st:cm_src_state))
        (cm_state_fp st) (cm_state_regions st) ${ret:cm_type}`;
  thm old_static = cm_tvs_pick_conjunct(components,
      `cm_phase_static_type_ready (p:cm_program) (fid:int)
        ${old_phase:cm_aphase}`);
  thm static_open = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_phase_static_type_ready_def())), old_static);
  thm callee_low = cm_tvs_pick_conjunct(static_open,
      `0i <= ${callee:int}`);
  thm callee_high = cm_tvs_pick_conjunct(static_open,
      `${callee:int} < ilength
        (cm_program_functions (p:cm_program))`);
  thm ret_equal = cm_tvs_pick_conjunct(static_open,
      `${ret:cm_type} == cm_function_ret ${callee_function:cm_function_d}`);
  thm function_wf = mp_rule(mp_rule(mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, callee), cm_typed_function_at), typed),
      callee_low), callee_high);
  thm function_open = conv_rule(rewrite_conv(THM_LIST(
      get_cm_function_wf_def())), function_wf);
  thm body_wf_false = cm_tvs_pick_conjunct(function_open,
      `cm_stmt_wf (p:cm_program) ${callee_function:cm_function_d} F
        (cm_function_body ${callee_function:cm_function_d})`);
  thm body_wf = mp_rule(specl_rule(TERM_LIST(
      `cm_function_body ${callee_function:cm_function_d}`,
      `p:cm_program`, callee_function, `F`),
      cm_stmt_wf_loop_mono), body_wf_false);
  thm caller_ready = taut_rule(imp_chain(TERM_LIST(
      concl(conjunct1_rule(bounds)), concl(conjunct2_rule(bounds))),
      `(fid:int) == --1i ||
       (0i <= fid &&
        fid < ilength (cm_program_functions (p:cm_program)))`));
  caller_ready = mp_rule(caller_ready, conjunct1_rule(bounds));
  caller_ready = mp_rule(caller_ready, conjunct2_rule(bounds));
  thm new_static = cm_tvs_trivial(
      `cm_phase_static_type_ready (p:cm_program) ${callee:int}
        ${new_phase:cm_aphase}`,
      THM_LIST(get_cm_phase_static_type_ready_def(), callee_low,
        callee_high, caller_ready, ret_equal));

  thm old_parent = cm_tvs_pick_conjunct(components,
      `cm_phase_parent_type_ready (p:cm_program) (fid:int)
        ${old_phase:cm_aphase} (rest:(cm_acursor)list)`);
  thm parent_open = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_phase_parent_type_ready_def())), old_parent);
  thm parent_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
      get_cm_phase_parent_type_ready_def())),
      `cm_phase_parent_type_ready (p:cm_program) ${callee:int}
        ${new_phase:cm_aphase} (rest:(cm_acursor)list)`);
  thm new_parent = eq_mp_rule(sym_rule(parent_view), parent_open);
  thm old_result = cm_tvs_pick_conjunct(components,
      `cm_phase_result_type_ready (p:cm_program) (fid:int)
        ${old_phase:cm_aphase} (rest:(cm_acursor)list)`);
  thm result_open = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_phase_result_type_ready_def(),
      get_cm_phase_result_type_def(), cm_phase_next_fid_def)),
      old_result);
  thm result_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
      get_cm_phase_result_type_ready_def(),
      get_cm_phase_result_type_def(), cm_phase_next_fid_def)),
      `cm_phase_result_type_ready (p:cm_program) ${callee:int}
        ${new_phase:cm_aphase} (rest:(cm_acursor)list)`);
  thm new_result = eq_mp_rule(sym_rule(result_view), result_open);
  thm old_rest = cm_tvs_pick_conjunct(components,
      `cm_cursors_type_ready (p:cm_program)
        (cm_phase_next_fid (fid:int) ${old_phase:cm_aphase})
        (rest:(cm_acursor)list)`);
  thm old_next = cm_tvs_trivial(
      `cm_phase_next_fid (fid:int) ${old_phase:cm_aphase} == fid`,
      THM_LIST(cm_phase_next_fid_def));
  thm rest_ready = conv_rule(rewrite_conv(THM_LIST(old_next)), old_rest);
  thm new_next = cm_tvs_trivial(
      `cm_phase_next_fid ${callee:int} ${new_phase:cm_aphase} == fid`,
      THM_LIST(cm_phase_next_fid_def));
  thm next_rest_view = apply_conversion(rewrite_conv(THM_LIST(new_next)),
      `cm_cursors_type_ready (p:cm_program)
        (cm_phase_next_fid ${callee:int} ${new_phase:cm_aphase})
        (rest:(cm_acursor)list)`);
  thm next_rest = eq_mp_rule(sym_rule(next_rest_view), rest_ready);
  thm new_cursors = specl_rule(TERM_LIST(
      `p:cm_program`, callee, new_phase, `parent_temp:int`,
      `parent_break:int`, `parent_continue:int`,
      `rest:(cm_acursor)list`), cm_cursor_push_type_ready);
  new_cursors = mp_rule(new_cursors, new_static);
  new_cursors = mp_rule(new_cursors, new_parent);
  new_cursors = mp_rule(new_cursors, new_result);
  new_cursors = mp_rule(new_cursors, next_rest);

  term next_ann = cm_tvs_next_annotation(old_phase);
  thm cursor_equal = cm_tvs_cursor_fact(old_phase,
      `CMACursor ${new_phase:cm_aphase} (parent_temp:int)
         (parent_break:int) (parent_continue:int) ::
       (rest:(cm_acursor)list)`,
      THM_LIST(same_program, pending_empty, call_ready, frame_equal,
        cm_ann_enter_call_def));
  thm next_cursors = conv_rule(rewrite_conv(THM_LIST(
      sym_rule(cursor_equal))), new_cursors);
  term next_task =
      `CMSTask (q:cm_program) ${callee:int}
        (cm_function_body
          (inth ${callee:int} (cm_program_functions q)))
        (cm_enter_call q ${callee:int}
          (REVERSE ((incoming:cm_value) :: ${values:(cm_value)list}))
          (st:cm_src_state))
        (CMCallK (fid:int) (cm_state_env st) (cm_state_fp st)
           (cm_state_regions st) ${ret:cm_type} ::
         (ks:(cm_frame)list))`;
  thm target_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
      get_cm_task_type_ready_def(), same_program, callee_low,
      callee_high, body_wf, next_cursors)),
      `cm_task_type_ready (p:cm_program) ${next_task:cm_task}
        ${next_ann:cm_annotation}`);
  return eqt_elim_rule(target_view);
}

PROOF static thm cm_prove_v_call_type_ready_step(void) {
  term phase = `phase:cm_aphase`;
  term ann = cm_tvs_annotation(phase);
  term task = cm_tvs_task(phase);
  term body = imp_chain(TERM_LIST(
      `cm_typed_program (p:cm_program)`,
      `cm_phase_is_halt (phase:cm_aphase) ||
       (0i <= (fid:int) &&
        fid < ilength (cm_program_functions p))`,
      `cm_annotation_erases ${task:cm_task} ${ann:cm_annotation}`,
      `cm_task_type_ready p ${task:cm_task} ${ann:cm_annotation}`,
      `cm_v_phase_family (phase:cm_aphase) == 4i`),
      `cm_task_type_ready (p:cm_program)
        (cm_step ${task:cm_task})
        (cm_update_annotation
          (cm_annotation_step ${task:cm_task}
            ${ann:cm_annotation}))`);
  gnode root = gnode_new_with_ccl(list_mk_forall(free_vars(body), body));
  gnode introduced = AUTO_INTROS_TAC(root);
  thm typed = assume_rule(`cm_typed_program (p:cm_program)`);
  thm generic_erases = assume_rule(
      `cm_annotation_erases ${task:cm_task} ${ann:cm_annotation}`);
  thm generic_ready = assume_rule(
      `cm_task_type_ready (p:cm_program) ${task:cm_task}
        ${ann:cm_annotation}`);
  thm family = assume_rule(
      `cm_v_phase_family (phase:cm_aphase) == 4i`);
  gnode_list cases = DISJ_CASES_TAC(introduced,
      ispec_rule(phase, get_datatype_cases("cm_aphase")), "Hphase");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    while (true) {
      labeled_term_list assumptions = goal_lasmps(cases[i]->g);
      int shape_index = labeled_term_list_index(assumptions, "Hphase");
      if (!is_exists(assumptions[shape_index].tm)) break;
      cases[i] = ASMP_EXISTS_TAC(cases[i], "Hphase", NULL);
    }
    thm shape = assume_rule(goal_lasmps(cases[i]->g)[
        labeled_term_list_index(goal_lasmps(cases[i]->g), "Hphase")].tm);
    term concrete_phase = rhs_of(shape);
    thm ready = conv_rule(rewrite_conv(THM_LIST(shape)), generic_ready);
    thm components = cm_tvs_components(concrete_phase, ready);
    thm same_program = cm_tvs_pick_conjunct(components,
        `(q:cm_program) == (p:cm_program)`);
    if (i != 21) {
      thm impossible = conv_rule(reduce_rewrite_conv(THM_LIST(
          shape, get_cm_v_phase_family_def())), family);
      CONTR_TAC(cases[i], impossible);
      continue;
    }
    term callee = cm_tvs_phase_arg(concrete_phase, 8, 0);
    term pending = cm_tvs_phase_arg(concrete_phase, 8, 1);
    term values = cm_tvs_phase_arg(concrete_phase, 8, 2);
    term ret = cm_tvs_phase_arg(concrete_phase, 8, 3);
    term all_args = cm_tvs_phase_arg(concrete_phase, 8, 4);
    term base_slot = cm_tvs_phase_arg(concrete_phase, 8, 5);
    term current_slot = cm_tvs_phase_arg(concrete_phase, 8, 6);
    term scratch = cm_tvs_phase_arg(concrete_phase, 8, 7);
    thm bounds = conv_rule(reduce_rewrite_conv(THM_LIST(
        shape, cm_phase_is_halt_def)), assume_rule(
        `cm_phase_is_halt (phase:cm_aphase) ||
         (0i <= (fid:int) &&
          fid < ilength (cm_program_functions (p:cm_program)))`));
    term pending_empty = `${pending:(cm_expr)list} == []`;
    gnode_list pending_cases = BOOL_CASES_TAC(
        cases[i], pending_empty, "Hpending");
    {
      thm empty = assume_rule(pending_empty);
      thm erases = conv_rule(rewrite_conv(THM_LIST(shape)),
          generic_erases);
      thm frame_equal = cm_tvcall_tail_frames(concrete_phase, erases);
      term condition =
          `cm_call_ok (p:cm_program) ${callee:int}
             (REVERSE ((incoming:cm_value) :: ${values:(cm_value)list}))
             (st:cm_src_state) &&
           cm_call_depth (ks:(cm_frame)list) < 65536i`;
      gnode_list condition_cases = BOOL_CASES_TAC(
          pending_cases[0], condition, "Hcall");
      {
        thm call_ready = assume_rule(condition);
        thm proved = cm_tvcall_enter(concrete_phase, callee, values,
            ret, ready, components, typed, bounds, empty, frame_equal,
            call_ready, same_program);
        cm_tvs_accept(condition_cases[0], proved, shape,
            THM_LIST(same_program, empty, call_ready, frame_equal,
              get_cm_begin_call_def(), cm_ann_enter_call_def));
      }
      {
        thm call_bad = assume_rule(mk_not(condition));
        thm control_ready = cm_tvs_trivial(
            `cm_control_type_ready (p:cm_program)
              (cm_phase_next_fid (fid:int) ${concrete_phase:cm_aphase})
              (CMError 1i)`,
            THM_LIST(get_cm_control_type_ready_def(),
              cm_phase_next_fid_def));
        thm proved = cm_tvs_pop_control(concrete_phase, `CMError 1i`,
            `st:cm_src_state`, ready, control_ready,
            THM_LIST(same_program, empty, call_bad, frame_equal));
        cm_tvs_accept(condition_cases[1], proved, shape,
            THM_LIST(same_program, empty, call_bad, frame_equal,
              get_cm_begin_call_def()));
      }
    }
    {
      thm nonempty = assume_rule(mk_not(pending_empty));
      thm proved = cm_tvcall_nonfinal(concrete_phase, callee,
          pending, values, ret, all_args, base_slot, current_slot,
          scratch, ready, components, bounds, nonempty,
          THM_LIST(same_program, nonempty));
      cm_tvs_accept(pending_cases[1], proved, shape,
          THM_LIST(same_program, nonempty));
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_v_call_type_ready_step =
    cm_prove_v_call_type_ready_step();

PROOF static int cmc_preservation_type_source_v_call_final_checks(void) {
  ENSURE_COND(vector_size(hyp(cm_v_call_type_ready_step)) == 0,
      "call value type theorem has assumptions");
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_type_source_v_call_axioms_before,
      "call value type proof introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_type_source_v_call_checks =
    cmc_preservation_type_source_v_call_final_checks();
