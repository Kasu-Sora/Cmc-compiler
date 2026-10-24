#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_type_source_v_pointer.h"
#include "cmc_preservation_type_source_v_helpers.h"

#require "cmc_preservation_type_source_v_binary.c"
#require "cmc_preservation_type_lvalue.c"

PROOF static size_t _cmc_preservation_type_source_v_pointer_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_tvptr_replace_index(
    term old_phase, term index, term ty, thm ready,
    thm components, thm bounds, thm_list extra) {
  term new_phase = `CAIndexRP (incoming:cm_value) ${ty:cm_type}`;
  thm old_static = cm_tvs_pick_conjunct(components,
      `cm_phase_static_type_ready (p:cm_program) (fid:int)
        ${old_phase:cm_aphase}`);
  thm static_open = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_phase_static_type_ready_def())), old_static);
  thm index_wf = cm_tvs_pick_conjunct(static_open,
      `cm_expr_wf (p:cm_program)
        (inth (fid:int) (cm_program_functions p)) ${index:cm_expr}`);
  thm index_integer = cm_tvs_pick_conjunct(static_open,
      `cm_integer_type (cm_expr_type ${index:cm_expr})`);
  thm index_scalar = mp_rule(spec_rule(
      `cm_expr_type ${index:cm_expr}`, cm_integer_expr_type),
      index_integer);
  thm type_refs = cm_tvs_pick_conjunct(static_open,
      `cm_type_refs (cm_program_structs (p:cm_program)) ${ty:cm_type}`);
  thm incoming_ready = cm_tvs_pick_conjunct(components,
      `cm_phase_value_type_ready (p:cm_program) (fid:int)
        ${old_phase:cm_aphase} (incoming:cm_value)`);
  incoming_ready = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_phase_value_type_ready_def())), incoming_ready);
  thm new_static = cm_tvs_trivial(
      `cm_phase_static_type_ready (p:cm_program) (fid:int)
        ${new_phase:cm_aphase}`,
      THM_LIST(get_cm_phase_static_type_ready_def(), incoming_ready,
        type_refs));
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
        ${new_phase:cm_aphase} (cm_expr_type ${index:cm_expr})`,
      THM_LIST(get_cm_phase_input_type_ready_def(), index_integer));
  thm new_expr = cm_tvs_trivial(
      `cm_phase_expr_type_ready (p:cm_program) (fid:int)
        ${new_phase:cm_aphase} ${index:cm_expr}`,
      THM_LIST(get_cm_phase_expr_type_ready_def(), index_integer));
  term next_ann = cm_tvs_next_annotation(old_phase);
  thm cursor_equal = cm_tvs_cursor_fact(old_phase,
      `CMACursor ${new_phase:cm_aphase} (parent_temp:int)
         (parent_break:int) (parent_continue:int) ::
       (rest:(cm_acursor)list)`, extra);
  thm proved = specl_rule(TERM_LIST(
      `p:cm_program`, `q:cm_program`, `fid:int`,
      `incoming:cm_value`, `st:cm_src_state`, `st:cm_src_state`,
      `cm_phase_frame ${old_phase:cm_aphase} :: (ks:(cm_frame)list)`,
      `CMIndexRK (incoming:cm_value) ${ty:cm_type} ::
        (ks:(cm_frame)list)`,
      old_phase, new_phase, index, `pc:int`, `temp:int`,
      `breakpc:int`, `continuepc:int`, `parent_temp:int`,
      `parent_break:int`, `parent_continue:int`,
      `rest:(cm_acursor)list`, `spills:(cm_spill)list`,
      `saved:(cm_spill_frame)list`, `calls:(cm_call_sim_frame)list`,
      next_ann), cm_v_replace_r_task_ready);
  thm_list premises = THM_LIST(ready, conjunct1_rule(bounds),
      conjunct2_rule(bounds), old_next, index_wf, index_scalar,
      new_static, new_parent, new_result, new_next, new_input,
      new_expr, cursor_equal);
  for (size_t i = 0; i < vector_size(premises); ++i) {
    proved = mp_rule(proved, premises[i]);
  }
  return proved;
}

PROOF static thm cm_tvptr_index_result(
    term base, term ty, term offset, thm static_ready, thm shift_ok) {
  thm static_open = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_phase_static_type_ready_def())), static_ready);
  thm base_ready = cm_tvs_pick_conjunct(static_open,
      `cm_value_type_compatible ${base:cm_value} (CMPtrTy ${ty:cm_type})`);
  thm shift_open = conv_rule(rewrite_conv(THM_LIST(
      get_cm_ptr_shift_ok_def())), shift_ok);
  thm base_live = conjunct1_rule(shift_open);
  thm proved = specl_rule(TERM_LIST(
      `cm_program_structs (p:cm_program)`, `st:cm_src_state`,
      base, ty, offset), cm_ptr_add_type_ready);
  proved = mp_rule(proved, base_ready);
  return mp_rule(proved, base_live);
}

PROOF static thm cm_tvptr_member_result(
    term mid, term base_ty, thm static_ready,
    thm incoming_ready, thm member_ok) {
  thm member_valid = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_phase_static_type_ready_def())), static_ready);
  thm valid_open = conv_rule(rewrite_conv(THM_LIST(
      get_cm_member_valid_def())), member_valid);
  thm base_pointer = cm_tvs_pick_conjunct(valid_open,
      `cm_is_pointer ${base_ty:cm_type}`);
  thm base_ready = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_phase_value_type_ready_def())), incoming_ready);
  thm member_open = conv_rule(rewrite_conv(THM_LIST(
      get_cm_ptr_member_ok_def())), member_ok);
  thm base_live = conjunct1_rule(member_open);
  thm base_view = specl_rule(TERM_LIST(
      `st:cm_src_state`, `incoming:cm_value`, base_ty),
      cm_pointer_view_type);
  base_view = mp_rule(base_view, base_ready);
  base_view = mp_rule(base_view, base_pointer);
  base_view = mp_rule(base_view, base_live);
  thm slot_equal = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(get_cm_member_slot_def(), base_view)),
      `cm_member_slot (p:cm_program) (incoming:cm_value) ${mid:int} ==
       inth ${mid:int}
         (cm_struct_members
           (inth (cm_struct_id (cm_pointee ${base_ty:cm_type}))
             (cm_program_structs p)))`));
  thm proved = specl_rule(TERM_LIST(
      `p:cm_program`, `incoming:cm_value`, mid),
      cm_ptr_member_type_ready);
  thm member_type_equal = beta_norm(ap_term_rule(
      `\slot:cm_slot_d. CMPtrTy (cm_slot_ty slot)`, slot_equal));
  thm static_view = beta_norm(ap_term_rule(
      `\target:cm_type.
         cm_value_type_compatible
           (cm_ptr_member (p:cm_program) (incoming:cm_value) ${mid:int})
           target`, member_type_equal));
  thm static_result = eq_mp_rule(static_view, proved);
  thm target_view = apply_conversion(rewrite_conv(THM_LIST(
      get_cm_member_lvalue_type_def())),
      `cm_value_type_compatible
        (cm_ptr_member (p:cm_program) (incoming:cm_value) ${mid:int})
        (cm_member_lvalue_type p ${base_ty:cm_type} ${mid:int})`);
  return eq_mp_rule(sym_rule(target_view), static_result);
}

PROOF static thm cm_prove_v_pointer_type_ready_step(void) {
  term phase = `phase:cm_aphase`;
  term ann = cm_tvs_annotation(phase);
  term task = cm_tvs_task(phase);
  term body = imp_chain(TERM_LIST(
      `cm_phase_is_halt (phase:cm_aphase) ||
       (0i <= (fid:int) &&
        fid < ilength (cm_program_functions (p:cm_program)))`,
      `cm_task_type_ready (p:cm_program) ${task:cm_task}
        ${ann:cm_annotation}`,
      `cm_v_phase_family (phase:cm_aphase) == 2i`),
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
      `cm_v_phase_family (phase:cm_aphase) == 2i`);
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
    if (i != 7 && i != 8 && i != 9) {
      thm impossible = conv_rule(reduce_rewrite_conv(THM_LIST(
          shape, get_cm_v_phase_family_def())), family);
      CONTR_TAC(cases[i], impossible);
      continue;
    }
    if (i == 7) {
      term index = cm_tvs_phase_arg(concrete_phase, 2, 0);
      term ty = cm_tvs_phase_arg(concrete_phase, 2, 1);
      thm bounds = conv_rule(reduce_rewrite_conv(THM_LIST(
          shape, cm_phase_is_halt_def)), assume_rule(
          `cm_phase_is_halt (phase:cm_aphase) ||
           (0i <= (fid:int) &&
            fid < ilength (cm_program_functions (p:cm_program)))`));
      thm proved = cm_tvptr_replace_index(concrete_phase, index, ty,
          ready, components, bounds, THM_LIST(same_program));
      cm_tvs_accept(cases[i], proved, shape, THM_LIST(same_program));
      continue;
    }
    thm static_ready = cm_tvs_pick_conjunct(components,
        `cm_phase_static_type_ready (p:cm_program) (fid:int)
          ${concrete_phase:cm_aphase}`);
    if (i == 8) {
      term base = cm_tvs_phase_arg(concrete_phase, 2, 0);
      term ty = cm_tvs_phase_arg(concrete_phase, 2, 1);
      term condition =
          `cm_ptr_shift_ok (cm_program_structs (p:cm_program))
            ${base:cm_value} (cm_value_number (st:cm_src_state)
              (incoming:cm_value)) st`;
      gnode_list condition_cases = BOOL_CASES_TAC(
          cases[i], condition, "Hshift");
      {
        thm shift_ok = assume_rule(condition);
        thm compatible = cm_tvptr_index_result(base, ty,
            `cm_value_number (st:cm_src_state) (incoming:cm_value)`,
            static_ready, shift_ok);
        thm proved = cm_tvs_pop_value(concrete_phase,
            `cm_ptr_add (cm_program_structs (p:cm_program))
              ${base:cm_value}
              (cm_value_number (st:cm_src_state) (incoming:cm_value))`,
            `CMPtrTy ${ty:cm_type}`, `st:cm_src_state`, ready,
            compatible, THM_LIST(same_program, shift_ok));
        cm_tvs_accept(condition_cases[0], proved, shape,
            THM_LIST(same_program, shift_ok));
      }
      {
        thm shift_bad = assume_rule(mk_not(condition));
        thm control_ready = cm_tvs_trivial(
            `cm_control_type_ready (p:cm_program)
              (cm_phase_next_fid (fid:int) ${concrete_phase:cm_aphase})
              (CMError 1i)`,
            THM_LIST(get_cm_control_type_ready_def(), cm_phase_next_fid_def));
        thm proved = cm_tvs_pop_control(concrete_phase, `CMError 1i`,
            `st:cm_src_state`, ready, control_ready,
            THM_LIST(same_program, shift_bad));
        cm_tvs_accept(condition_cases[1], proved, shape,
            THM_LIST(same_program, shift_bad));
      }
      continue;
    }
    term mid = cm_tvs_phase_arg(concrete_phase, 2, 0);
    term base_ty = cm_tvs_phase_arg(concrete_phase, 2, 1);
    thm incoming_ready = cm_tvs_pick_conjunct(components,
        `cm_phase_value_type_ready (p:cm_program) (fid:int)
          ${concrete_phase:cm_aphase} (incoming:cm_value)`);
    term condition =
        `cm_ptr_member_ok (p:cm_program) (incoming:cm_value)
          ${mid:int} (st:cm_src_state)`;
    gnode_list condition_cases = BOOL_CASES_TAC(
        cases[i], condition, "Hmember");
    {
      thm member_ok = assume_rule(condition);
      thm compatible = cm_tvptr_member_result(mid, base_ty,
          static_ready, incoming_ready, member_ok);
      thm proved = cm_tvs_pop_value(concrete_phase,
          `cm_ptr_member (p:cm_program) (incoming:cm_value) ${mid:int}`,
          `cm_member_lvalue_type (p:cm_program) ${base_ty:cm_type}
            ${mid:int}`,
          `st:cm_src_state`, ready, compatible,
          THM_LIST(same_program, member_ok));
      cm_tvs_accept(condition_cases[0], proved, shape,
          THM_LIST(same_program, member_ok));
    }
    {
      thm member_bad = assume_rule(mk_not(condition));
      thm control_ready = cm_tvs_trivial(
          `cm_control_type_ready (p:cm_program)
            (cm_phase_next_fid (fid:int) ${concrete_phase:cm_aphase})
            (CMError 1i)`,
          THM_LIST(get_cm_control_type_ready_def(), cm_phase_next_fid_def));
      thm proved = cm_tvs_pop_control(concrete_phase, `CMError 1i`,
          `st:cm_src_state`, ready, control_ready,
          THM_LIST(same_program, member_bad));
      cm_tvs_accept(condition_cases[1], proved, shape,
          THM_LIST(same_program, member_bad));
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_v_pointer_type_ready_step =
    cm_prove_v_pointer_type_ready_step();

PROOF static int cmc_preservation_type_source_v_pointer_final_checks(void) {
  ENSURE_COND(vector_size(hyp(cm_v_pointer_type_ready_step)) == 0,
      "pointer value type theorem has assumptions");
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_type_source_v_pointer_axioms_before,
      "pointer value type proof introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_type_source_v_pointer_checks =
    cmc_preservation_type_source_v_pointer_final_checks();
