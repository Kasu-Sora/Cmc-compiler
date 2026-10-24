#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_type_source_c_call.h"
#include "cmc_preservation_type_source_c_helpers.h"
#include "cmc_preservation_type_facts.h"

#require "cmc_preservation_type_source_c_struct.c"

PROOF static size_t _cmc_preservation_type_source_c_call_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_prove_zero_value_convertible_scalar(void) {
  gnode root = gnode_new_with_ccl(
      `!(structs:(cm_struct_d)list) (ty:cm_type).
         cm_scalar_type structs ty ==>
         cm_value_convertible_to (CMIntV 0i) ty`);
  gnode_list cases = INDUCT_TAC(root, `ty:cm_type`);
  for (size_t i = 0; i < vector_size(cases); ++i) {
    thm view = apply_conversion(reduce_rewrite_conv(THM_LIST(
        get_cm_scalar_type_def(), get_cm_value_convertible_to_def(),
        get_cm_value_type_def(), get_cm_convertible_def(),
        get_cm_is_pointer_def(), get_cm_is_struct_def(),
        get_cm_type_code_wf_def(), get_cm_type_refs_def(),
        get_datatype_distinctness("cm_type"),
        get_datatype_injectivity("cm_type"),
        get_datatype_distinctness("cm_value"))),
        goal_ccl(cases[i]->g));
    ACCEPT_TAC(cases[i], eqt_elim_rule(view));
  }
  return gnode_prove(root);
}
PROOF static thm cm_zero_value_convertible_scalar =
    cm_prove_zero_value_convertible_scalar();

PROOF static thm cm_tccall_ret_scalar(
    term old_phase, term ret, thm typed, thm components) {
  term function =
      `inth (fid:int) (cm_program_functions (p:cm_program))`;
  thm old_static = cm_tvs_pick_conjunct(components,
      `cm_phase_static_type_ready (p:cm_program) (fid:int)
        ${old_phase:cm_aphase}`);
  thm static_open = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_phase_static_type_ready_def())), old_static);
  thm fid_low = cm_tvs_pick_conjunct(static_open, `0i <= (fid:int)`);
  thm fid_high = cm_tvs_pick_conjunct(static_open,
      `(fid:int) < ilength (cm_program_functions (p:cm_program))`);
  thm ret_equal = cm_tvs_pick_conjunct(static_open,
      `${ret:cm_type} == cm_function_ret ${function:cm_function_d}`);
  thm function_wf = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`), cm_typed_function_at);
  function_wf = mp_rule(function_wf, typed);
  function_wf = mp_rule(function_wf, fid_low);
  function_wf = mp_rule(function_wf, fid_high);
  thm function_open = conv_rule(rewrite_conv(THM_LIST(
      get_cm_function_wf_def())), function_wf);
  thm stored_scalar = cm_tvs_pick_conjunct(function_open,
      `cm_scalar_type (cm_program_structs (p:cm_program))
        (cm_function_ret ${function:cm_function_d})`);
  thm scalar_view = beta_norm(ap_term_rule(
      `\result_ty:cm_type.
         cm_scalar_type (cm_program_structs (p:cm_program)) result_ty`,
      ret_equal));
  return eq_mp_rule(sym_rule(scalar_view), stored_scalar);
}

PROOF static thm cm_tccall_result_ready(
    term old_phase, term ret, term incoming, term restored,
    thm ready, thm components, thm convertible, thm_list extra) {
  thm compatible = specl_rule(TERM_LIST(
      restored, incoming, ret), cm_convert_value_type_ready);
  compatible = mp_rule(compatible, convertible);
  return cm_tcs_pop_value(old_phase,
      `cm_convert_value ${restored:cm_src_state}
        ${ret:cm_type} ${incoming:cm_value}`,
      ret, restored, ready, compatible, extra);
}

PROOF static thm cm_prove_c_call_type_ready_step(void) {
  term phase = `phase:cm_aphase`;
  term ann = cm_tvs_annotation(phase);
  term task = cm_tcs_task(phase);
  term body = imp_chain(TERM_LIST(
      `cm_typed_program (p:cm_program)`,
      `cm_task_type_ready p ${task:cm_task} ${ann:cm_annotation}`,
      `cm_c_phase_family (phase:cm_aphase) == 3i`),
      `cm_task_type_ready (p:cm_program)
        (cm_step ${task:cm_task})
        (cm_update_annotation
          (cm_annotation_step ${task:cm_task}
            ${ann:cm_annotation}))`);
  gnode root = gnode_new_with_ccl(list_mk_forall(free_vars(body), body));
  gnode introduced = cm_tcs_nonexit_branch(AUTO_INTROS_TAC(root));
  thm typed = assume_rule(`cm_typed_program (p:cm_program)`);
  thm generic_ready = assume_rule(
      `cm_task_type_ready (p:cm_program) ${task:cm_task}
        ${ann:cm_annotation}`);
  thm family = assume_rule(
      `cm_c_phase_family (phase:cm_aphase) == 3i`);
  gnode_list phase_cases = DISJ_CASES_TAC(introduced,
      ispec_rule(phase, get_datatype_cases("cm_aphase")), "Hphase");
  for (size_t i = 0; i < vector_size(phase_cases); ++i) {
    while (true) {
      labeled_term_list assumptions = goal_lasmps(phase_cases[i]->g);
      int shape_index = labeled_term_list_index(assumptions, "Hphase");
      if (!is_exists(assumptions[shape_index].tm)) break;
      phase_cases[i] = ASMP_EXISTS_TAC(
          phase_cases[i], "Hphase", NULL);
    }
    thm phase_shape = assume_rule(goal_lasmps(phase_cases[i]->g)[
        labeled_term_list_index(
          goal_lasmps(phase_cases[i]->g), "Hphase")].tm);
    term concrete_phase = rhs_of(phase_shape);
    if (i != 22) {
      thm impossible = conv_rule(reduce_rewrite_conv(THM_LIST(
          phase_shape, get_cm_c_phase_family_def())), family);
      CONTR_TAC(phase_cases[i], impossible);
      continue;
    }
    term caller = cm_tvs_phase_arg(concrete_phase, 5, 0);
    term oldenv = cm_tvs_phase_arg(concrete_phase, 5, 1);
    term oldfp = cm_tvs_phase_arg(concrete_phase, 5, 2);
    term oldregions = cm_tvs_phase_arg(concrete_phase, 5, 3);
    term ret = cm_tvs_phase_arg(concrete_phase, 5, 4);
    term restored =
        `cm_restore_call (st:cm_src_state)
          ${oldenv:int->int->cm_value} ${oldfp:int}
          ${oldregions:(cm_region)list}`;
    thm ready = conv_rule(rewrite_conv(THM_LIST(phase_shape)),
        generic_ready);
    thm components = cm_tcs_components(concrete_phase, ready);
    thm same_program = cm_tvs_pick_conjunct(components,
        `(q:cm_program) == (p:cm_program)`);
    thm old_control = cm_tvs_pick_conjunct(components,
        `cm_control_type_ready (p:cm_program) (fid:int)
          (control:cm_control)`);
    thm ret_scalar = cm_tccall_ret_scalar(
        concrete_phase, ret, typed, components);
    gnode_list control_cases = DISJ_CASES_TAC(phase_cases[i],
        ispec_rule(`control:cm_control`,
          get_datatype_cases("cm_control")), "Hcontrol");
    for (size_t j = 0; j < vector_size(control_cases); ++j) {
      while (true) {
        labeled_term_list assumptions = goal_lasmps(control_cases[j]->g);
        int shape_index = labeled_term_list_index(
            assumptions, "Hcontrol");
        if (!is_exists(assumptions[shape_index].tm)) break;
        control_cases[j] = ASMP_EXISTS_TAC(
            control_cases[j], "Hcontrol", NULL);
      }
      thm control_shape = assume_rule(goal_lasmps(control_cases[j]->g)[
          labeled_term_list_index(
            goal_lasmps(control_cases[j]->g), "Hcontrol")].tm);
      term concrete_control = rhs_of(control_shape);
      if (j == 0) {
        thm convertible = specl_rule(TERM_LIST(
            `cm_program_structs (p:cm_program)`, ret),
            cm_zero_value_convertible_scalar);
        convertible = mp_rule(convertible, ret_scalar);
        thm proved = cm_tccall_result_ready(concrete_phase, ret,
            `CMIntV 0i`, restored, ready, components, convertible,
            THM_LIST(same_program, control_shape));
        cm_tcs_accept(control_cases[j], proved, phase_shape,
            THM_LIST(same_program, control_shape));
        continue;
      }
      if (j == 3) {
        term returned = cm_tvs_phase_arg(concrete_control, 1, 0);
        thm concrete_ready = conv_rule(reduce_rewrite_conv(THM_LIST(
            control_shape, get_cm_control_type_ready_def())), old_control);
        thm old_static = cm_tvs_pick_conjunct(components,
            `cm_phase_static_type_ready (p:cm_program) (fid:int)
              ${concrete_phase:cm_aphase}`);
        thm static_open = conv_rule(reduce_rewrite_conv(THM_LIST(
            get_cm_phase_static_type_ready_def())), old_static);
        thm ret_equal = cm_tvs_pick_conjunct(static_open,
            `${ret:cm_type} == cm_function_ret
              (inth (fid:int)
                (cm_program_functions (p:cm_program)))`);
        thm convertible_view = beta_norm(ap_term_rule(
            `\result_ty:cm_type.
               cm_value_convertible_to ${returned:cm_value} result_ty`,
            ret_equal));
        thm convertible = eq_mp_rule(
            sym_rule(convertible_view), concrete_ready);
        thm proved = cm_tccall_result_ready(concrete_phase, ret,
            returned, restored, ready, components, convertible,
            THM_LIST(same_program, control_shape));
        cm_tcs_accept(control_cases[j], proved, phase_shape,
            THM_LIST(same_program, control_shape));
        continue;
      }
      thm next_control = cm_tvs_trivial(
          `cm_control_type_ready (p:cm_program)
            (cm_phase_next_fid (fid:int) ${concrete_phase:cm_aphase})
            ${concrete_control:cm_control}`,
          THM_LIST(get_cm_control_type_ready_def(),
            cm_phase_next_fid_def));
      thm proved = cm_tcs_pop_control(concrete_phase,
          concrete_control, restored, ready, next_control,
          THM_LIST(same_program, control_shape));
      cm_tcs_accept(control_cases[j], proved, phase_shape,
          THM_LIST(same_program, control_shape));
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_c_call_type_ready_step =
    cm_prove_c_call_type_ready_step();

PROOF static int cmc_preservation_type_source_c_call_final_checks(void) {
  ENSURE_COND(vector_size(hyp(cm_zero_value_convertible_scalar)) == 0,
      "scalar zero conversion theorem has assumptions");
  ENSURE_COND(vector_size(hyp(cm_c_call_type_ready_step)) == 0,
      "call control type theorem has assumptions");
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_type_source_c_call_axioms_before,
      "call control type proof introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_type_source_c_call_checks =
    cmc_preservation_type_source_c_call_final_checks();
