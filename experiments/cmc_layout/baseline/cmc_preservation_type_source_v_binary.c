#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_type_source_v_binary.h"
#include "cmc_preservation_type_source_v_helpers.h"

#require "cmc_preservation_type_source_v_scalar.c"
#require "cmc_preservation_type_source_r_struct.c"

PROOF static size_t _cmc_preservation_type_source_v_binary_axioms_before =
    vector_size(get_all_axioms());


PROOF static thm cm_tvbin_result_compatible(
    term ty, term number, thm binary_types, thm op_equal) {
  thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_binary_types_def(), op_equal)), binary_types);
  thm result_is_int = cm_tvs_pick_conjunct(opened,
      `${ty:cm_type} == CMIntTy`);
  thm base = cm_tvs_trivial(
      `cm_value_type_compatible (CMIntV ${number:int}) CMIntTy`,
      THM_LIST(get_cm_value_type_compatible_def(),
        get_cm_value_type_def(), get_datatype_distinctness("cm_value"),
        get_datatype_distinctness("cm_type")));
  thm target_view = apply_conversion(rewrite_conv(THM_LIST(result_is_int)),
      `cm_value_type_compatible (CMIntV ${number:int}) ${ty:cm_type}`);
  return eq_mp_rule(sym_rule(target_view), base);
}

PROOF static thm cm_tvbin_replace_right(
    term old_phase, term op, term left, term right, term ty,
    thm ready, thm components, thm bounds, thm_list extra) {
  term new_phase = `CABinRP ${op:int} ${left:cm_expr} ${right:cm_expr}
    (incoming:cm_value) ${ty:cm_type}`;
  thm old_static = cm_tvs_pick_conjunct(components,
      `cm_phase_static_type_ready (p:cm_program) (fid:int)
        ${old_phase:cm_aphase}`);
  thm expression_wf = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_phase_static_type_ready_def())), old_static);
  thm wf_open = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_expr_wf_def())), expression_wf);
  thm right_wf = cm_tvs_pick_conjunct(wf_open,
      `cm_expr_wf (p:cm_program)
        (inth (fid:int) (cm_program_functions p)) ${right:cm_expr}`);
  thm binary_types = cm_tvs_pick_conjunct(wf_open,
      `cm_binary_types ${op:int} (cm_expr_type ${left:cm_expr})
        (cm_expr_type ${right:cm_expr}) ${ty:cm_type}`);
  thm scalar_pair = mp_rule(specl_rule(TERM_LIST(
      op, `cm_expr_type ${left:cm_expr}`,
      `cm_expr_type ${right:cm_expr}`, ty),
      cm_binary_operand_scalars), binary_types);
  thm right_scalar = conjunct2_rule(scalar_pair);
  thm incoming_ready = cm_tvs_pick_conjunct(components,
      `cm_phase_value_type_ready (p:cm_program) (fid:int)
        ${old_phase:cm_aphase} (incoming:cm_value)`);
  incoming_ready = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_phase_value_type_ready_def())), incoming_ready);
  thm new_static = cm_tvs_trivial(
      `cm_phase_static_type_ready (p:cm_program) (fid:int)
        ${new_phase:cm_aphase}`,
      THM_LIST(get_cm_phase_static_type_ready_def(), expression_wf,
        incoming_ready));
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
      get_cm_phase_result_type_def(), cm_phase_next_fid_def)), old_result);
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
        ${new_phase:cm_aphase} (cm_expr_type ${right:cm_expr})`,
      THM_LIST(get_cm_phase_input_type_ready_def()));
  thm new_expr = cm_tvs_trivial(
      `cm_phase_expr_type_ready (p:cm_program) (fid:int)
        ${new_phase:cm_aphase} ${right:cm_expr}`,
      THM_LIST(get_cm_phase_expr_type_ready_def()));
  term next_ann = cm_tvs_next_annotation(old_phase);
  thm cursor_equal = cm_tvs_cursor_fact(old_phase,
      `CMACursor ${new_phase:cm_aphase} (parent_temp:int)
         (parent_break:int) (parent_continue:int) ::
       (rest:(cm_acursor)list)`, extra);
  thm proved = specl_rule(TERM_LIST(
      `p:cm_program`, `q:cm_program`, `fid:int`,
      `incoming:cm_value`, `st:cm_src_state`, `st:cm_src_state`,
      `cm_phase_frame ${old_phase:cm_aphase} :: (ks:(cm_frame)list)`,
      `CMBinRK ${op:int} (incoming:cm_value) ${ty:cm_type} ::
        (ks:(cm_frame)list)`,
      old_phase, new_phase, right, `pc:int`, `temp:int`,
      `breakpc:int`, `continuepc:int`, `parent_temp:int`,
      `parent_break:int`, `parent_continue:int`,
      `rest:(cm_acursor)list`, `spills:(cm_spill)list`,
      `saved:(cm_spill_frame)list`, `calls:(cm_call_sim_frame)list`,
      next_ann), cm_v_replace_r_task_ready);
  thm_list premises = THM_LIST(ready, conjunct1_rule(bounds),
      conjunct2_rule(bounds), old_next, right_wf, right_scalar,
      new_static, new_parent, new_result, new_next, new_input,
      new_expr, cursor_equal);
  for (size_t i = 0; i < vector_size(premises); ++i) {
    proved = mp_rule(proved, premises[i]);
  }
  return proved;
}

PROOF static thm cm_prove_v_binary_type_ready_step(void) {
  term phase = `phase:cm_aphase`;
  term ann = cm_tvs_annotation(phase);
  term task = cm_tvs_task(phase);
  term body = imp_chain(TERM_LIST(
      `cm_phase_is_halt (phase:cm_aphase) ||
       (0i <= (fid:int) &&
        fid < ilength (cm_program_functions (p:cm_program)))`,
      `cm_task_type_ready (p:cm_program) ${task:cm_task}
        ${ann:cm_annotation}`,
      `cm_v_phase_family (phase:cm_aphase) == 1i`),
      `cm_task_type_ready (p:cm_program)
        (cm_step ${task:cm_task})
        (cm_update_annotation
          (cm_annotation_step ${task:cm_task} ${ann:cm_annotation}))`);
  gnode root = gnode_new_with_ccl(list_mk_forall(free_vars(body), body));
  gnode introduced = AUTO_INTROS_TAC(root);
  thm generic_ready = assume_rule(
      `cm_task_type_ready (p:cm_program) ${task:cm_task}
        ${ann:cm_annotation}`);
  thm family = assume_rule(
      `cm_v_phase_family (phase:cm_aphase) == 1i`);
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
    thm same_program = cm_tvs_pick_conjunct(components,
        `(q:cm_program) == (p:cm_program)`);
    if (i != 4 && i != 5) {
      thm impossible = conv_rule(reduce_rewrite_conv(THM_LIST(
          shape, get_cm_v_phase_family_def())), family);
      CONTR_TAC(cases[i], impossible);
      continue;
    }
    if (i == 4) {
      term op = cm_tvs_phase_arg(concrete_phase, 4, 0);
      term left = cm_tvs_phase_arg(concrete_phase, 4, 1);
      term right = cm_tvs_phase_arg(concrete_phase, 4, 2);
      term ty = cm_tvs_phase_arg(concrete_phase, 4, 3);
      thm old_static = cm_tvs_pick_conjunct(components,
          `cm_phase_static_type_ready (p:cm_program) (fid:int)
            ${concrete_phase:cm_aphase}`);
      thm expression_wf = conv_rule(reduce_rewrite_conv(THM_LIST(
          get_cm_phase_static_type_ready_def())), old_static);
      thm wf_open = conv_rule(reduce_rewrite_conv(THM_LIST(
          get_cm_expr_wf_def())), expression_wf);
      thm binary_types = cm_tvs_pick_conjunct(wf_open,
          `cm_binary_types ${op:int} (cm_expr_type ${left:cm_expr})
            (cm_expr_type ${right:cm_expr}) ${ty:cm_type}`);
      thm bounds = conv_rule(reduce_rewrite_conv(THM_LIST(
          shape, cm_phase_is_halt_def)), assume_rule(
          `cm_phase_is_halt (phase:cm_aphase) ||
           (0i <= (fid:int) &&
            fid < ilength (cm_program_functions (p:cm_program)))`));
      gnode_list zero_cases = BOOL_CASES_TAC(
          cases[i], `${op:int} == 0i`, "Hop_zero");
      thm op_zero = assume_rule(`${op:int} == 0i`);
      gnode_list zero_truth = BOOL_CASES_TAC(zero_cases[0],
          `cm_truth (st:cm_src_state) (incoming:cm_value)`,
          "Htruth_zero");
      {
        thm truth = assume_rule(
            `cm_truth (st:cm_src_state) (incoming:cm_value)`);
        thm compatible = cm_tvbin_result_compatible(
            ty, `1i`, binary_types, op_zero);
        thm proved = cm_tvs_pop_value(concrete_phase, `CMIntV 1i`, ty,
            `st:cm_src_state`, ready, compatible,
            THM_LIST(same_program, op_zero, truth));
        cm_tvs_accept(zero_truth[0], proved, shape,
            THM_LIST(same_program, op_zero, truth));
      }
      {
        thm not_truth = assume_rule(mk_not(
            `cm_truth (st:cm_src_state) (incoming:cm_value)`));
        thm proved = cm_tvbin_replace_right(concrete_phase, op, left,
            right, ty, ready, components, bounds,
            THM_LIST(same_program, op_zero, not_truth));
        cm_tvs_accept(zero_truth[1], proved, shape,
            THM_LIST(same_program, op_zero, not_truth));
      }
      gnode_list one_cases = BOOL_CASES_TAC(
          zero_cases[1], `${op:int} == 1i`, "Hop_one");
      thm not_zero = assume_rule(mk_not(`${op:int} == 0i`));
      thm op_one = assume_rule(`${op:int} == 1i`);
      gnode_list one_truth = BOOL_CASES_TAC(one_cases[0],
          `cm_truth (st:cm_src_state) (incoming:cm_value)`,
          "Htruth_one");
      {
        thm truth = assume_rule(
            `cm_truth (st:cm_src_state) (incoming:cm_value)`);
        thm proved = cm_tvbin_replace_right(concrete_phase, op, left,
            right, ty, ready, components, bounds,
            THM_LIST(same_program, not_zero, op_one, truth));
        cm_tvs_accept(one_truth[0], proved, shape,
            THM_LIST(same_program, not_zero, op_one, truth));
      }
      {
        thm not_truth = assume_rule(mk_not(
            `cm_truth (st:cm_src_state) (incoming:cm_value)`));
        thm compatible = cm_tvbin_result_compatible(
            ty, `0i`, binary_types, op_one);
        thm proved = cm_tvs_pop_value(concrete_phase, `CMIntV 0i`, ty,
            `st:cm_src_state`, ready, compatible,
            THM_LIST(same_program, not_zero, op_one, not_truth));
        cm_tvs_accept(one_truth[1], proved, shape,
            THM_LIST(same_program, not_zero, op_one, not_truth));
      }
      {
        thm not_one = assume_rule(mk_not(`${op:int} == 1i`));
        thm proved = cm_tvbin_replace_right(concrete_phase, op, left,
            right, ty, ready, components, bounds,
            THM_LIST(same_program, not_zero, not_one));
        cm_tvs_accept(one_cases[1], proved, shape,
            THM_LIST(same_program, not_zero, not_one));
      }
    } else {
      term op = cm_tvs_phase_arg(concrete_phase, 5, 0);
      term left = cm_tvs_phase_arg(concrete_phase, 5, 1);
      term right = cm_tvs_phase_arg(concrete_phase, 5, 2);
      term saved_value = cm_tvs_phase_arg(concrete_phase, 5, 3);
      term ty = cm_tvs_phase_arg(concrete_phase, 5, 4);
      thm old_static = cm_tvs_pick_conjunct(components,
          `cm_phase_static_type_ready (p:cm_program) (fid:int)
            ${concrete_phase:cm_aphase}`);
      thm static_open = conv_rule(reduce_rewrite_conv(THM_LIST(
          get_cm_phase_static_type_ready_def())), old_static);
      thm expression_wf = cm_tvs_pick_conjunct(static_open,
          `cm_expr_wf (p:cm_program)
            (inth (fid:int) (cm_program_functions p))
            (CMBinaryE ${op:int} ${left:cm_expr} ${right:cm_expr}
              ${ty:cm_type})`);
      thm left_ready = cm_tvs_pick_conjunct(static_open,
          `cm_value_type_compatible ${saved_value:cm_value}
            (cm_expr_type ${left:cm_expr})`);
      thm wf_open = conv_rule(reduce_rewrite_conv(THM_LIST(
          get_cm_expr_wf_def())), expression_wf);
      thm binary_types = cm_tvs_pick_conjunct(wf_open,
          `cm_binary_types ${op:int} (cm_expr_type ${left:cm_expr})
            (cm_expr_type ${right:cm_expr}) ${ty:cm_type}`);
      thm right_ready = cm_tvs_pick_conjunct(components,
          `cm_phase_value_type_ready (p:cm_program) (fid:int)
            ${concrete_phase:cm_aphase} (incoming:cm_value)`);
      right_ready = conv_rule(reduce_rewrite_conv(THM_LIST(
          get_cm_phase_value_type_ready_def())), right_ready);
      term condition = `cm_binary_ok (p:cm_program) ${op:int}
        ${saved_value:cm_value} (incoming:cm_value) (st:cm_src_state)`;
      gnode_list condition_cases = BOOL_CASES_TAC(
          cases[i], condition, "Hbinary");
      {
        thm binary_ok = assume_rule(condition);
        thm compatible = specl_rule(TERM_LIST(
            `p:cm_program`, op, saved_value, `incoming:cm_value`,
            `cm_expr_type ${left:cm_expr}`,
            `cm_expr_type ${right:cm_expr}`, ty, `st:cm_src_state`),
            cm_binary_value_type_ready);
        thm_list premises = THM_LIST(binary_types, left_ready,
            right_ready, binary_ok);
        for (size_t j = 0; j < vector_size(premises); ++j) {
          compatible = mp_rule(compatible, premises[j]);
        }
        thm proved = cm_tvs_pop_value(concrete_phase,
            `cm_binary_value (p:cm_program) ${op:int}
              ${saved_value:cm_value} (incoming:cm_value)
              ${ty:cm_type} (st:cm_src_state)`,
            ty, `st:cm_src_state`, ready, compatible,
            THM_LIST(same_program, binary_ok));
        cm_tvs_accept(condition_cases[0], proved, shape,
            THM_LIST(same_program, binary_ok));
      }
      {
        thm binary_bad = assume_rule(mk_not(condition));
        thm control_ready = cm_tvs_trivial(
            `cm_control_type_ready (p:cm_program)
              (cm_phase_next_fid (fid:int) ${concrete_phase:cm_aphase})
              (CMError 1i)`,
            THM_LIST(get_cm_control_type_ready_def(),
              cm_phase_next_fid_def));
        thm proved = cm_tvs_pop_control(concrete_phase, `CMError 1i`,
            `st:cm_src_state`, ready, control_ready,
            THM_LIST(same_program, binary_bad));
        cm_tvs_accept(condition_cases[1], proved, shape,
            THM_LIST(same_program, binary_bad));
      }
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_v_binary_type_ready_step =
    cm_prove_v_binary_type_ready_step();

PROOF static int cmc_preservation_type_source_v_binary_final_checks(void) {
  ENSURE_COND(vector_size(hyp(cm_v_binary_type_ready_step)) == 0,
      "binary value type theorem has assumptions");
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_type_source_v_binary_axioms_before,
      "binary value type proof introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_type_source_v_binary_checks =
    cmc_preservation_type_source_v_binary_final_checks();
