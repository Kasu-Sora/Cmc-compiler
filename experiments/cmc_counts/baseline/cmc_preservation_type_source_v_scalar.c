#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_type_source_v_scalar.h"
#include "cmc_preservation_type_source_v_helpers.h"

#require "cmc_preservation_type_source_v_support.c"

PROOF static size_t _cmc_preservation_type_source_v_scalar_axioms_before =
    vector_size(get_all_axioms());


PROOF static thm cm_prove_v_scalar_type_ready_step(void) {
  term phase = `phase:cm_aphase`;
  term ann = cm_tvs_annotation(phase);
  term task = cm_tvs_task(phase);
  term body = imp_chain(TERM_LIST(
      `cm_phase_is_halt (phase:cm_aphase) ||
       (0i <= (fid:int) &&
        fid < ilength (cm_program_functions (p:cm_program)))`,
      `cm_task_type_ready (p:cm_program) ${task:cm_task}
        ${ann:cm_annotation}`,
      `cm_v_phase_family (phase:cm_aphase) == 0i`),
      `cm_task_type_ready (p:cm_program)
        (cm_step ${task:cm_task})
        (cm_update_annotation
          (cm_annotation_step ${task:cm_task}
            ${ann:cm_annotation}))`);
  gnode root = gnode_new_with_ccl(list_mk_forall(free_vars(body), body));
  gnode introduced = AUTO_INTROS_TAC(root);
  thm generic_ready = assume_rule(
      `cm_task_type_ready (p:cm_program) ${task:cm_task}
        ${ann:cm_annotation}`);
  thm family = assume_rule(
      `cm_v_phase_family (phase:cm_aphase) == 0i`);
  gnode_list cases = DISJ_CASES_TAC(introduced,
      ispec_rule(phase, get_datatype_cases("cm_aphase")), "Hphase");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    while (true) {
      labeled_term_list assumptions = goal_lasmps(cases[i]->g);
      int index = labeled_term_list_index(assumptions, "Hphase");
      if (!is_exists(assumptions[index].tm)) break;
      cases[i] = ASMP_EXISTS_TAC(cases[i], "Hphase", NULL);
    }
    thm shape = assume_rule(goal_lasmps(cases[i]->g)[
        labeled_term_list_index(goal_lasmps(cases[i]->g), "Hphase")].tm);
    term concrete_phase = rhs_of(shape);
    thm ready = conv_rule(rewrite_conv(THM_LIST(shape)), generic_ready);
    thm components = cm_tvs_components(concrete_phase, ready);
    if (i == 4 || i == 5 || (7 <= i && i <= 9) ||
        (15 <= i && i <= 19) || i == 21 || i == 22) {
      thm impossible = conv_rule(reduce_rewrite_conv(THM_LIST(
          shape, get_cm_v_phase_family_def())), family);
      CONTR_TAC(cases[i], impossible);
      continue;
    }
    thm_list no_extra = THM_LIST();
    if (i == 0) {
      thm view = apply_conversion(reduce_rewrite_conv(cm_tvs_rules(shape)),
          goal_ccl(cases[i]->g));
      ACCEPT_TAC(cases[i], eqt_elim_rule(view));
    } else if (i == 1) {
      term ty = cm_tvs_phase_arg(concrete_phase, 1, 0);
      term condition = `cm_load_ok ${ty:cm_type}
        (incoming:cm_value) (st:cm_src_state)`;
      gnode_list condition_cases = BOOL_CASES_TAC(
          cases[i], condition, "Hload");
      thm static_ready = cm_tvs_pick_conjunct(components,
          `cm_phase_static_type_ready (p:cm_program) (fid:int)
            ${concrete_phase:cm_aphase}`);
      static_ready = conv_rule(reduce_rewrite_conv(THM_LIST(
          get_cm_phase_static_type_ready_def())), static_ready);
      {
        thm load_ok = assume_rule(condition);
        thm compatible = mp_rule(mp_rule(specl_rule(TERM_LIST(
            `st:cm_src_state`, `incoming:cm_value`, ty),
            cm_load_value_type_ready), static_ready), load_ok);
        thm proved = cm_tvs_pop_value(concrete_phase,
            `cm_load_value ${ty:cm_type} (incoming:cm_value)
              (st:cm_src_state)`, ty, `st:cm_src_state`, ready,
            compatible, THM_LIST(load_ok));
        cm_tvs_accept(condition_cases[0], proved, shape,
            THM_LIST(load_ok));
      }
      {
        thm load_bad = assume_rule(mk_not(condition));
        thm control_ready = cm_tvs_trivial(
            `cm_control_type_ready (p:cm_program)
              (cm_phase_next_fid (fid:int) ${concrete_phase:cm_aphase})
              (CMError 1i)`,
            THM_LIST(get_cm_control_type_ready_def(),
              cm_phase_next_fid_def));
        thm proved = cm_tvs_pop_control(concrete_phase, `CMError 1i`,
            `st:cm_src_state`, ready, control_ready,
            THM_LIST(load_bad));
        cm_tvs_accept(condition_cases[1], proved, shape,
            THM_LIST(load_bad));
      }
    } else if (i == 2) {
      term src = cm_tvs_phase_arg(concrete_phase, 2, 0);
      term ty = cm_tvs_phase_arg(concrete_phase, 2, 1);
      term new_phase = `CAAssignRP (incoming:cm_value) ${ty:cm_type}`;
      thm bounds = conv_rule(reduce_rewrite_conv(THM_LIST(
          shape, cm_phase_is_halt_def)), assume_rule(
          `cm_phase_is_halt (phase:cm_aphase) ||
           (0i <= (fid:int) &&
            fid < ilength (cm_program_functions (p:cm_program)))`));
      thm old_static = cm_tvs_pick_conjunct(components,
          `cm_phase_static_type_ready (p:cm_program) (fid:int)
            ${concrete_phase:cm_aphase}`);
      thm static_open = conv_rule(reduce_rewrite_conv(THM_LIST(
          get_cm_phase_static_type_ready_def())), old_static);
      thm child_wf = cm_tvs_pick_conjunct(static_open,
          `cm_expr_wf (p:cm_program)
            (inth (fid:int) (cm_program_functions p)) ${src:cm_expr}`);
      thm convertible = cm_tvs_pick_conjunct(static_open,
          `cm_expr_convertible ${src:cm_expr} ${ty:cm_type}`);
      thm scalar_ty = cm_tvs_pick_conjunct(static_open,
          `cm_scalar_expr_type ${ty:cm_type}`);
      thm child_scalar = mp_rule(specl_rule(TERM_LIST(src, ty),
          cm_expr_convertible_source_scalar), convertible);
      thm incoming_ready = cm_tvs_pick_conjunct(components,
          `cm_phase_value_type_ready (p:cm_program) (fid:int)
            ${concrete_phase:cm_aphase} (incoming:cm_value)`);
      incoming_ready = conv_rule(reduce_rewrite_conv(THM_LIST(
          get_cm_phase_value_type_ready_def())), incoming_ready);
      thm new_static = cm_tvs_trivial(
          `cm_phase_static_type_ready (p:cm_program) (fid:int)
            ${new_phase:cm_aphase}`,
          THM_LIST(get_cm_phase_static_type_ready_def(),
            incoming_ready, scalar_ty));
      thm old_parent = cm_tvs_pick_conjunct(components,
          `cm_phase_parent_type_ready (p:cm_program) (fid:int)
            ${concrete_phase:cm_aphase} (rest:(cm_acursor)list)`);
      thm parent_open = conv_rule(reduce_rewrite_conv(THM_LIST(
          get_cm_phase_parent_type_ready_def())), old_parent);
      thm parent_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
          get_cm_phase_parent_type_ready_def())),
          `cm_phase_parent_type_ready (p:cm_program) (fid:int)
            ${new_phase:cm_aphase} (rest:(cm_acursor)list)`);
      thm new_parent = eq_mp_rule(sym_rule(parent_view), parent_open);
      thm old_result = cm_tvs_pick_conjunct(components,
          `cm_phase_result_type_ready (p:cm_program) (fid:int)
            ${concrete_phase:cm_aphase} (rest:(cm_acursor)list)`);
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
          `cm_phase_next_fid (fid:int) ${concrete_phase:cm_aphase} == fid`,
          THM_LIST(cm_phase_next_fid_def));
      thm new_next = cm_tvs_trivial(
          `cm_phase_next_fid (fid:int) ${new_phase:cm_aphase} == fid`,
          THM_LIST(cm_phase_next_fid_def));
      thm new_input = cm_tvs_trivial(
          `cm_phase_input_type_ready (p:cm_program) (fid:int)
            ${new_phase:cm_aphase} (cm_expr_type ${src:cm_expr})`,
          THM_LIST(get_cm_phase_input_type_ready_def()));
      thm new_expr = cm_tvs_trivial(
          `cm_phase_expr_type_ready (p:cm_program) (fid:int)
            ${new_phase:cm_aphase} ${src:cm_expr}`,
          THM_LIST(get_cm_phase_expr_type_ready_def(), convertible));
      term next_ann = cm_tvs_next_annotation(concrete_phase);
      thm cursor_equal = cm_tvs_cursor_fact(concrete_phase,
          `CMACursor ${new_phase:cm_aphase} (parent_temp:int)
             (parent_break:int) (parent_continue:int) ::
           (rest:(cm_acursor)list)`, no_extra);
      thm proved = specl_rule(TERM_LIST(
          `p:cm_program`, `q:cm_program`, `fid:int`,
          `incoming:cm_value`, `st:cm_src_state`, `st:cm_src_state`,
          `cm_phase_frame ${concrete_phase:cm_aphase} ::
            (ks:(cm_frame)list)`,
          `CMAssignRK (incoming:cm_value) ${ty:cm_type} ::
            (ks:(cm_frame)list)`,
          concrete_phase, new_phase, src, `pc:int`, `temp:int`,
          `breakpc:int`, `continuepc:int`, `parent_temp:int`,
          `parent_break:int`, `parent_continue:int`,
          `rest:(cm_acursor)list`, `spills:(cm_spill)list`,
          `saved:(cm_spill_frame)list`, `calls:(cm_call_sim_frame)list`,
          next_ann), cm_v_replace_r_task_ready);
      thm_list premises = THM_LIST(ready, conjunct1_rule(bounds),
          conjunct2_rule(bounds), old_next, child_wf, child_scalar,
          new_static, new_parent, new_result, new_next, new_input,
          new_expr, cursor_equal);
      for (size_t j = 0; j < vector_size(premises); ++j) {
        proved = mp_rule(proved, premises[j]);
      }
      cm_tvs_accept(cases[i], proved, shape, no_extra);
    } else if (i == 3) {
      term ptr = cm_tvs_phase_arg(concrete_phase, 2, 0);
      term ty = cm_tvs_phase_arg(concrete_phase, 2, 1);
      term condition = `cm_store_ok ${ty:cm_type} ${ptr:cm_value}
        (st:cm_src_state)`;
      gnode_list condition_cases = BOOL_CASES_TAC(
          cases[i], condition, "Hstore");
      thm incoming_ready = cm_tvs_pick_conjunct(components,
          `cm_phase_value_type_ready (p:cm_program) (fid:int)
            ${concrete_phase:cm_aphase} (incoming:cm_value)`);
      incoming_ready = conv_rule(reduce_rewrite_conv(THM_LIST(
          get_cm_phase_value_type_ready_def())), incoming_ready);
      {
        thm store_ok = assume_rule(condition);
        thm compatible = mp_rule(specl_rule(TERM_LIST(
            `st:cm_src_state`, `incoming:cm_value`, ty),
            cm_convert_value_type_ready), incoming_ready);
        thm proved = cm_tvs_pop_value(concrete_phase,
            `cm_convert_value (st:cm_src_state) ${ty:cm_type}
              (incoming:cm_value)`, ty,
            `cm_state_store ${ty:cm_type} ${ptr:cm_value}
              (incoming:cm_value) (st:cm_src_state)`,
            ready, compatible, THM_LIST(store_ok));
        cm_tvs_accept(condition_cases[0], proved, shape,
            THM_LIST(store_ok));
      }
      {
        thm store_bad = assume_rule(mk_not(condition));
        thm control_ready = cm_tvs_trivial(
            `cm_control_type_ready (p:cm_program)
              (cm_phase_next_fid (fid:int) ${concrete_phase:cm_aphase})
              (CMError 1i)`,
            THM_LIST(get_cm_control_type_ready_def(),
              cm_phase_next_fid_def));
        thm proved = cm_tvs_pop_control(concrete_phase, `CMError 1i`,
            `st:cm_src_state`, ready, control_ready,
            THM_LIST(store_bad));
        cm_tvs_accept(condition_cases[1], proved, shape,
            THM_LIST(store_bad));
      }
    } else if (i == 6) {
      term op = cm_tvs_phase_arg(concrete_phase, 1, 0);
      thm compatible = specl_rule(TERM_LIST(op, `incoming:cm_value`,
          `st:cm_src_state`), cm_unary_value_type_ready);
      thm proved = cm_tvs_pop_value(concrete_phase,
          `cm_unary_value ${op:int} (incoming:cm_value)
            (st:cm_src_state)`, `CMIntTy`, `st:cm_src_state`, ready,
          compatible, no_extra);
      cm_tvs_accept(cases[i], proved, shape, no_extra);
    } else if (i == 10 || i == 11) {
      thm compatible = cm_tvs_trivial(
          `cm_value_type_compatible
            (CMIntV (cm_value_number (st:cm_src_state)
              (incoming:cm_value))) CMIntTy`,
          THM_LIST(get_cm_value_type_compatible_def(),
            get_cm_value_type_def(),
            get_datatype_distinctness("cm_value"),
            get_datatype_distinctness("cm_type")));
      term next_st = i == 10
          ? `cm_state_io (st:cm_src_state) (cm_state_input st)
              (APPEND (cm_state_output st)
                [tower_u8 (cm_value_number st (incoming:cm_value))])`
          : `cm_state_io (st:cm_src_state) (cm_state_input st)
              (APPEND (cm_state_output st)
                (tower_decimal (cm_value_number st
                  (incoming:cm_value))))`;
      thm proved = cm_tvs_pop_value(concrete_phase,
          `CMIntV (cm_value_number (st:cm_src_state)
            (incoming:cm_value))`, `CMIntTy`, next_st, ready,
          compatible, no_extra);
      cm_tvs_accept(cases[i], proved, shape, no_extra);
    } else if (i == 12) {
      thm control_ready = cm_tvs_trivial(
          `cm_control_type_ready (p:cm_program)
            (cm_phase_next_fid (fid:int) ${concrete_phase:cm_aphase})
            (CMExit (tower_status
              (cm_value_number (st:cm_src_state) (incoming:cm_value))))`,
          THM_LIST(get_cm_control_type_ready_def(),
            cm_phase_next_fid_def));
      thm proved = cm_tvs_pop_control(concrete_phase,
          `CMExit (tower_status
            (cm_value_number (st:cm_src_state) (incoming:cm_value)))`,
          `st:cm_src_state`, ready, control_ready, no_extra);
      cm_tvs_accept(cases[i], proved, shape, no_extra);
    } else if (i == 13) {
      thm control_ready = cm_tvs_trivial(
          `cm_control_type_ready (p:cm_program)
            (cm_phase_next_fid (fid:int) ${concrete_phase:cm_aphase})
            CMNormal`,
          THM_LIST(get_cm_control_type_ready_def(),
            cm_phase_next_fid_def));
      thm proved = cm_tvs_pop_control(concrete_phase, `CMNormal`,
          `st:cm_src_state`, ready, control_ready, no_extra);
      cm_tvs_accept(cases[i], proved, shape, no_extra);
    } else if (i == 14) {
      term slot = cm_tvs_phase_arg(concrete_phase, 1, 0);
      term condition =
          `cm_binding_address_ok (q:cm_program) (fid:int) 1i ${slot:int}
             (st:cm_src_state) &&
           cm_store_ok
             (cm_slot_ty (inth ${slot:int} (cm_function_locals
               (inth fid (cm_program_functions q)))))
             (cm_state_env st 1i ${slot:int}) st`;
      gnode_list condition_cases = BOOL_CASES_TAC(
          cases[i], condition, "Hinit");
      for (size_t j = 0; j < vector_size(condition_cases); ++j) {
        thm condition_fact = j == 0
            ? assume_rule(condition) : assume_rule(mk_not(condition));
        term control = j == 0 ? `CMNormal` : `CMError 1i`;
        thm control_ready = cm_tvs_trivial(
            `cm_control_type_ready (p:cm_program)
              (cm_phase_next_fid (fid:int) ${concrete_phase:cm_aphase})
              ${control:cm_control}`,
            THM_LIST(get_cm_control_type_ready_def(),
              cm_phase_next_fid_def));
        term next_st = j == 0
            ? `cm_state_store
                (cm_slot_ty (inth ${slot:int} (cm_function_locals
                  (inth (fid:int) (cm_program_functions (q:cm_program))))))
                (cm_state_env (st:cm_src_state) 1i ${slot:int})
                (incoming:cm_value) st`
            : `st:cm_src_state`;
        thm proved = cm_tvs_pop_control(concrete_phase, control,
            next_st, ready, control_ready, THM_LIST(condition_fact));
        cm_tvs_accept(condition_cases[j], proved, shape,
            THM_LIST(condition_fact));
      }
    } else {
      thm incoming_ready = cm_tvs_pick_conjunct(components,
          `cm_phase_value_type_ready (p:cm_program) (fid:int)
            ${concrete_phase:cm_aphase} (incoming:cm_value)`);
      incoming_ready = conv_rule(reduce_rewrite_conv(THM_LIST(
          get_cm_phase_value_type_ready_def())), incoming_ready);
      thm control_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
          get_cm_control_type_ready_def(), cm_phase_next_fid_def)),
          `cm_control_type_ready (p:cm_program)
            (cm_phase_next_fid (fid:int) ${concrete_phase:cm_aphase})
            (CMReturn (incoming:cm_value))`);
      thm control_ready = eq_mp_rule(sym_rule(control_view), incoming_ready);
      thm proved = cm_tvs_pop_control(concrete_phase,
          `CMReturn (incoming:cm_value)`, `st:cm_src_state`, ready,
          control_ready, no_extra);
      cm_tvs_accept(cases[i], proved, shape, no_extra);
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_v_scalar_type_ready_step =
    cm_prove_v_scalar_type_ready_step();

PROOF static int cmc_preservation_type_source_v_scalar_final_checks(void) {
  ENSURE_COND(vector_size(hyp(cm_v_scalar_type_ready_step)) == 0,
      "scalar value type theorem has assumptions");
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_type_source_v_scalar_axioms_before,
      "scalar value type proof introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_type_source_v_scalar_checks =
    cmc_preservation_type_source_v_scalar_final_checks();
