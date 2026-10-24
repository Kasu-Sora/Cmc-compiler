#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_target_value_pointer_total.h"
#include "cmc_concrete_defs.h"
#include "cmc_preservation_target_value_context.h"
#include "cmc_preservation_target_value_index.h"
#include "cmc_preservation_target_value_member.h"
#include "cmc_preservation_spill_safety.h"
#include "cmc_preservation_spill_holds_safety.h"
#include "cmc_preservation_type_facts.h"
#include "cmc_preservation_type_value.h"
#include "cmc_preservation_invariant_frame.h"

#require "cmc_concrete_defs.c"
#require "cmc_preservation_target_value_context.c"
#require "cmc_preservation_target_value_index.c"
#require "cmc_preservation_target_value_member.c"
#require "cmc_preservation_spill_safety.c"
#require "cmc_preservation_spill_holds_safety.c"
#require "cmc_preservation_type_facts.c"
#require "cmc_preservation_type_value.c"
#require "cmc_preservation_invariant_frame.c"

PROOF static size_t _cmc_preservation_target_value_pointer_total_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_pointer_total_pick(thm fact, term wanted) {
  if (alpha_compare(concl(fact), wanted) == 0) return fact;
  if (!is_conj(concl(fact))) return empty_theorem;
  thm left = cm_pointer_total_pick(conjunct1_rule(fact), wanted);
  if (!IS_NULL(left)) return left;
  return cm_pointer_total_pick(conjunct2_rule(fact), wanted);
}

PROOF static thm cm_pointer_total_apply(thm result, thm_list premises) {
  for (size_t i = 0; i < vector_size(premises); ++i) {
    result = match_mp_rule(result, premises[i]);
  }
  return result;
}
PROOF static thm cm_pointer_total_conjoin(thm_list facts) {
  thm result = facts[vector_size(facts) - 1];
  for (size_t i = vector_size(facts) - 1; i > 0; --i) {
    result = conj_rule(facts[i - 1], result);
  }
  return result;
}


PROOF static void cm_pointer_total_accept(
    const gnode branch, const thm shape, const thm result) {
  thm_list rules = THM_LIST(shape, cm_phase_frame_def);
  thm normalized = conv_rule(reduce_rewrite_conv(rules), result);
  thm target_view = apply_conversion(
      reduce_rewrite_conv(rules), goal_ccl(branch->g));
  ACCEPT_TAC(branch, eq_mp_rule(sym_rule(target_view), normalized));
}

PROOF static thm cm_prove_member_offset_signed(void) {
  term structs = `cm_program_structs (p:cm_program)`;
  term sid = `cm_struct_id (cm_pointee (base_ty:cm_type))`;
  term slots = `cm_struct_members
      (inth ${sid:int} ${structs:(cm_struct_d)list})`;
  term offset = `cm_member_offset ${structs:(cm_struct_d)list}
      ${sid:int} (mid:int)`;
  term member_offset = `cm_member_offset_slots
      ${slots:(cm_slot_d)list} (mid:int)`;
  term prefix = `cm_slots_prefix ${structs:(cm_struct_d)list}
      ${slots:(cm_slot_d)list} (mid:int)`;
  term cell_size = `cm_slot_size ${structs:(cm_struct_d)list}
      (inth (mid:int) ${slots:(cm_slot_d)list})`;
  term slots_size = `cm_slots_size ${structs:(cm_struct_d)list}
      ${slots:(cm_slot_d)list}`;
  term struct_size = `cm_struct_slots_size ${slots:(cm_slot_d)list}`;
  term typed_term = `cm_typed_program (p:cm_program)`;
  term valid_term =
      `cm_member_valid (p:cm_program) (base_ty:cm_type) (mid:int)`;
  term theorem_body = imp_chain(TERM_LIST(typed_term, valid_term),
      `tower_signed64 ${offset:int}`);
  gnode root = gnode_new_with_ccl(
      list_mk_forall(free_vars(theorem_body), theorem_body));
  gnode leaf = AUTO_INTROS_TAC(root);
  thm typed = assume_rule(typed_term);
  thm valid = assume_rule(valid_term);
  thm valid_open = conv_rule(rewrite_conv(THM_LIST(
      get_cm_member_valid_def())), valid);
  thm sid_low = cm_pointer_total_pick(valid_open, `0i <= ${sid:int}`);
  thm sid_high = cm_pointer_total_pick(valid_open,
      `${sid:int} < ilength ${structs:(cm_struct_d)list}`);
  thm mid_low = cm_pointer_total_pick(valid_open, `0i <= (mid:int)`);
  thm mid_high = cm_pointer_total_pick(valid_open,
      `(mid:int) < ilength ${slots:(cm_slot_d)list}`);
  thm typed_open = conv_rule(rewrite_conv(THM_LIST(
      get_cm_typed_program_def())), typed);
  thm struct_wf = cm_pointer_total_apply(
      spec_rule(sid, conjunct1_rule(typed_open)),
      THM_LIST(sid_low, sid_high));
  thm struct_open = conv_rule(rewrite_conv(THM_LIST(
      get_cm_struct_wf_def())), struct_wf);
  thm slots_wf = cm_pointer_total_pick(struct_open,
      `cm_slots_wf ${structs:(cm_struct_d)list}
        ${slots:(cm_slot_d)list}`);
  thm struct_upper = cm_pointer_total_pick(struct_open,
      `${struct_size:int} <= 1048576i`);
  thm positive = match_mp_rule(specl_rule(TERM_LIST(
      structs, slots), cm_slots_wf_sizes_positive), slots_wf);
  thm prefix_bounds = specl_rule(TERM_LIST(
      structs, slots), cm_slots_prefix_cell_bounds);
  prefix_bounds = match_mp_rule(prefix_bounds, positive);
  prefix_bounds = spec_rule(`mid:int`, prefix_bounds);
  prefix_bounds = cm_pointer_total_apply(
      prefix_bounds, THM_LIST(mid_low, mid_high));
  thm all_slots = conv_rule(rewrite_conv(THM_LIST(
      get_cm_slots_wf_def())), slots_wf);
  thm selected_wf = cm_pointer_total_apply(spec_rule(`mid:int`, all_slots),
      THM_LIST(mid_low, mid_high));
  thm selected_open = conv_rule(rewrite_conv(THM_LIST(
      get_cm_slot_wf_def())), selected_wf);
  thm cell_positive = cm_pointer_total_pick(selected_open,
      `0i < ${cell_size:int}`);
  thm rep_to_prefix = match_mp_rule(specl_rule(TERM_LIST(
      structs, slots, `mid:int`), cm_rep_member_prefix_matches), slots_wf);
  thm rep_to_member = match_mp_rule(specl_rule(TERM_LIST(
      structs, slots, `mid:int`),
      cm_rep_struct_member_prefix_slots_matches), slots_wf);
  thm member_to_prefix = trans_rule(sym_rule(rep_to_member), rep_to_prefix);
  thm offset_open = apply_conversion(reduce_rewrite_conv(THM_LIST(
      get_cm_member_offset_def(), sid_low, sid_high)), offset);
  thm offset_to_prefix = trans_rule(offset_open, member_to_prefix);
  thm rep_to_slots_size = match_mp_rule(specl_rule(TERM_LIST(
      structs, slots), cm_rep_members_size_matches), slots_wf);
  thm rep_to_struct_size = match_mp_rule(specl_rule(TERM_LIST(
      structs, slots), cm_rep_struct_members_size_matches), slots_wf);
  thm slots_to_struct_size = trans_rule(
      sym_rule(rep_to_slots_size), rep_to_struct_size);
  thm inputs = cm_pointer_total_conjoin(THM_LIST(
      conjunct1_rule(prefix_bounds), conjunct2_rule(prefix_bounds),
      cell_positive, struct_upper, offset_to_prefix, slots_to_struct_size));
  thm raw_bounds = mp_rule(int_arith_rule(mk_imp(concl(inputs),
      `--9223372036854775808i <= ${offset:int} &&
       ${offset:int} <= 9223372036854775807i`)), inputs);
  thm view = apply_conversion(rewrite_conv(THM_LIST(
      get_tower_signed64_def())), `tower_signed64 ${offset:int}`);
  thm result = eq_mp_rule(sym_rule(view), raw_bounds);
  ACCEPT_TAC(leaf, result);
  return gnode_prove(root);
}
PROOF static thm cm_member_offset_signed =
    cm_prove_member_offset_signed();

PROOF static thm cm_prove_target_v_pointer_step(void) {
  term phase = `phase:cm_aphase`;
  term cursors =
      `CMACursor ${phase:cm_aphase} (owner:int) (saved_break:int)
        (saved_continue:int) :: (rest:(cm_acursor)list)`;
  term frames =
      `cm_phase_frame ${phase:cm_aphase} ::
       cm_cursor_frames (rest:(cm_acursor)list)`;
  term task =
      `CMVTask (p:cm_program) (fid:int) (incoming:cm_value)
        (st:cm_src_state) ${frames:(cm_frame)list}`;
  term ann =
      `CMAnnotation (pc:int) (temp:int) (breakpc:int) (continuepc:int)
        ${cursors:(cm_acursor)list} (spills:(cm_spill)list)
        (saved:(cm_spill_frame)list) (calls:(cm_call_sim_frame)list)`;
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
      `cm_task_type_ready p ${task:cm_task} ${ann:cm_annotation}`,
      `cm_task_fid_ready p ${task:cm_task}`,
      `cm_annotation_spill_consistent ${ann:cm_annotation}`,
      `cm_task_generation_safe p ${task:cm_task} ${ann:cm_annotation}`,
      `cm_task_tagged_valid ${task:cm_task}`,
      `cm_task_layout p ${task:cm_task} ${ann:cm_annotation}`,
      `cm_task_target_sim p ${task:cm_task} (target:tvm_task)
        ${ann:cm_annotation}`,
      `cm_v_phase_family ${phase:cm_aphase} == 2i`), result_term);
  gnode root = gnode_new_with_ccl(list_mk_forall(free_vars(body), body));
  gnode introduced = AUTO_INTROS_TAC(root);

  thm context = get_cm_target_v_context();
  context = cm_pointer_total_apply(context, THM_LIST(
      assume_rule(`cm_wf_program (p:cm_program)`),
      assume_rule(`cm_runtime_step_ready (p:cm_program) ${task:cm_task}
        ${ann:cm_annotation}`),
      assume_rule(`cm_task_runtime_invariant (p:cm_program)
        ${task:cm_task} ${ann:cm_annotation}`),
      assume_rule(`cm_task_type_ready (p:cm_program) ${task:cm_task}
        ${ann:cm_annotation}`),
      assume_rule(`cm_task_fid_ready (p:cm_program) ${task:cm_task}`),
      assume_rule(`cm_annotation_spill_consistent ${ann:cm_annotation}`),
      assume_rule(`cm_task_generation_safe (p:cm_program)
        ${task:cm_task} ${ann:cm_annotation}`),
      assume_rule(`cm_task_tagged_valid ${task:cm_task}`)));
  thm layout = assume_rule(
      `cm_task_layout (p:cm_program) ${task:cm_task} ${ann:cm_annotation}`);
  thm sim = assume_rule(
      `cm_task_target_sim (p:cm_program) ${task:cm_task}
        (target:tvm_task) ${ann:cm_annotation}`);
  thm family = assume_rule(`cm_v_phase_family ${phase:cm_aphase} == 2i`);

  gnode_list cases = DISJ_CASES_TAC(introduced,
      ispec_rule(phase, get_datatype_cases("cm_aphase")), "Hphase");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode branch = cases[i];
    while (true) {
      labeled_term_list assumptions = goal_lasmps(branch->g);
      int index = labeled_term_list_index(assumptions, "Hphase");
      if (!is_exists(assumptions[index].tm)) break;
      branch = ASMP_EXISTS_TAC(branch, "Hphase", NULL);
    }
    thm shape = assume_rule(goal_lasmps(branch->g)[
        labeled_term_list_index(goal_lasmps(branch->g), "Hphase")].tm);
    if (i != 7 && i != 8 && i != 9) {
      thm impossible = conv_rule(reduce_rewrite_conv(THM_LIST(
          shape, get_cm_v_phase_family_def())), family);
      CONTR_TAC(branch, impossible);
      continue;
    }

    term concrete_phase = rhs_of(shape);
    term concrete_cursors =
        `CMACursor ${concrete_phase:cm_aphase} (owner:int)
          (saved_break:int) (saved_continue:int) ::
         (rest:(cm_acursor)list)`;
    term concrete_frames =
        `cm_phase_frame ${concrete_phase:cm_aphase} ::
         cm_cursor_frames (rest:(cm_acursor)list)`;
    term concrete_task =
        `CMVTask (p:cm_program) (fid:int) (incoming:cm_value)
          (st:cm_src_state) ${concrete_frames:(cm_frame)list}`;
    term concrete_ann =
        `CMAnnotation (pc:int) (temp:int) (breakpc:int) (continuepc:int)
          ${concrete_cursors:(cm_acursor)list} (spills:(cm_spill)list)
          (saved:(cm_spill_frame)list) (calls:(cm_call_sim_frame)list)`;
    thm_list shape_rules = THM_LIST(shape, cm_phase_frame_def);
    thm shaped_context = conv_rule(rewrite_conv(THM_LIST(shape)), context);
    thm shaped_layout = conv_rule(reduce_rewrite_conv(shape_rules), layout);
    thm shaped_sim = conv_rule(reduce_rewrite_conv(shape_rules), sim);
    thm runtime_stack = cm_pointer_total_pick(shaped_context,
        `cm_runtime_stack (p:cm_program)
          (cm_state_regions (st:cm_src_state)) (fid:int)
          (cm_state_fp st) (cm_state_regions st)
          ${concrete_cursors:(cm_acursor)list} (spills:(cm_spill)list)
          (saved:(cm_spill_frame)list) (calls:(cm_call_sim_frame)list)`);
    thm typed = cm_pointer_total_pick(shaped_context,
        `cm_typed_program (p:cm_program)`);

    if (i == 7) {
      term index_expr = `a0:cm_expr`;
      term ty = `a1:cm_type`;
      thm bounds_disjunction = cm_pointer_total_pick(shaped_context,
          `cm_phase_is_halt ${concrete_phase:cm_aphase} ||
           (0i <= (fid:int) &&
            fid < ilength (cm_program_functions (p:cm_program)))`);
      thm bounds = conv_rule(reduce_rewrite_conv(THM_LIST(
          cm_phase_is_halt_def)), bounds_disjunction);
      thm temp_ready = cm_pointer_total_pick(shaped_context,
          `cm_v_temp_ready ${concrete_ann:cm_annotation}
            ${concrete_phase:cm_aphase}`);
      thm temp_equal = conv_rule(reduce_rewrite_conv(THM_LIST(
          cm_v_temp_ready_def, cm_phase_child_temp_def,
          cm_ann_temp_def, cm_ann_cursors_def, cm_cursor_temp_def,
          get_theorem_by_name("HD"))), temp_ready);
      thm spill_ready = cm_pointer_total_pick(shaped_context,
          `cm_v_spill_ready (p:cm_program) (fid:int)
            ${concrete_ann:cm_annotation} ${concrete_phase:cm_aphase}`);
      thm spill_bounds = conv_rule(reduce_rewrite_conv(THM_LIST(
          cm_v_spill_ready_def, cm_ann_temp_def, temp_equal,
          get_cm_temp_slots_def())), spill_ready);
      thm runtime_put = specl_rule(TERM_LIST(
          `p:cm_program`, `cm_state_regions (st:cm_src_state)`,
          `fid:int`, `cm_state_fp (st:cm_src_state)`, concrete_cursors,
          `cm_state_regions (st:cm_src_state)`, `owner:int`,
          `incoming:cm_value`, `spills:(cm_spill)list`,
          `saved:(cm_spill_frame)list`, `calls:(cm_call_sim_frame)list`),
          cm_runtime_stack_spill_put);
      runtime_put = cm_pointer_total_apply(runtime_put, THM_LIST(
          conjunct1_rule(bounds), conjunct1_rule(spill_bounds),
          conjunct2_rule(spill_bounds), runtime_stack));
      term address =
          `cm_state_fp (st:cm_src_state) +
           cm_temp_offset (p:cm_program) (fid:int) (owner:int)`;
      thm address_facts = specl_rule(TERM_LIST(
          `p:cm_program`, `cm_state_regions (st:cm_src_state)`,
          concrete_cursors, `fid:int`, `cm_state_fp (st:cm_src_state)`,
          `cm_state_regions (st:cm_src_state)`, `spills:(cm_spill)list`,
          `saved:(cm_spill_frame)list`, `calls:(cm_call_sim_frame)list`,
          `owner:int`, `incoming:cm_value`, address),
          get_cm_runtime_spill_address_safe());
      address_facts = cm_pointer_total_apply(address_facts,
          THM_LIST(runtime_put, conjunct1_rule(bounds), refl_rule(address)));
      thm tagged = cm_pointer_total_pick(shaped_context,
          `cm_tagged_span_valid (st:cm_src_state)`);
      thm proved = cm_pointer_total_apply(
          get_cm_target_v_index_left_step(), THM_LIST(
            shaped_layout, shaped_sim, runtime_put, conjunct1_rule(bounds),
            temp_equal, tagged,
            cm_pointer_total_pick(address_facts,
              `tower_signed64 (cm_state_fp (st:cm_src_state))`),
            cm_pointer_total_pick(address_facts,
              `tower_signed64
                (cm_temp_offset (p:cm_program) (fid:int) (owner:int))`),
            refl_rule(address),
            cm_pointer_total_pick(address_facts,
              `tower_signed64 ${address:int}`),
            cm_pointer_total_pick(address_facts,
              `tower_word_valid ${address:int}`)));
      cm_pointer_total_accept(branch, shape, proved);
      (void)index_expr;
      (void)ty;
      continue;
    }

    if (i == 8) {
      term base = `a0:cm_value`;
      term ty = `a1:cm_type`;
      thm bounds_disjunction = cm_pointer_total_pick(shaped_context,
          `cm_phase_is_halt ${concrete_phase:cm_aphase} ||
           (0i <= (fid:int) &&
            fid < ilength (cm_program_functions (p:cm_program)))`);
      thm bounds = conv_rule(reduce_rewrite_conv(THM_LIST(
          cm_phase_is_halt_def)), bounds_disjunction);
      thm phase_ready = cm_pointer_total_pick(shaped_context,
          `cm_v_phase_ready (p:cm_program) (incoming:cm_value)
            (st:cm_src_state) ${concrete_ann:cm_annotation}
            ${concrete_phase:cm_aphase}`);
      thm shift_ok = conv_rule(reduce_rewrite_conv(THM_LIST(
          cm_v_phase_ready_def)), phase_ready);
      thm shift_open = conv_rule(rewrite_conv(THM_LIST(
          get_cm_ptr_shift_ok_def())), shift_ok);
      thm base_live = conjunct1_rule(shift_open);
      thm static_type = cm_pointer_total_pick(shaped_context,
          `cm_phase_static_type_ready (p:cm_program) (fid:int)
            ${concrete_phase:cm_aphase}`);
      thm static_open = conv_rule(reduce_rewrite_conv(THM_LIST(
          cm_phase_static_type_ready_def)), static_type);
      thm compatible = cm_pointer_total_pick(static_open,
          `cm_value_type_compatible ${base:cm_value} (CMPtrTy ${ty:cm_type})`);
      thm type_refs = cm_pointer_total_pick(static_open,
          `cm_type_refs (cm_program_structs (p:cm_program)) ${ty:cm_type}`);
      thm base_view = cm_pointer_total_apply(specl_rule(TERM_LIST(
          base, ty, `st:cm_src_state`), cm_pointer_value_view),
          THM_LIST(compatible, base_live));
      thm spill_fact = cm_pointer_total_pick(shaped_context,
          `cm_phase_spill_consistent (temp:int) (owner:int)
            ${concrete_phase:cm_aphase} (spills:(cm_spill)list)`);
      thm held = conjunct2_rule(conv_rule(reduce_rewrite_conv(THM_LIST(
          cm_phase_spill_consistent_def)), spill_fact));
      thm scale_is_signed = cm_pointer_total_apply(specl_rule(TERM_LIST(
          `p:cm_program`, ty), get_cm_referenced_type_size_signed()),
          THM_LIST(typed, type_refs));
      term address =
          `cm_state_fp (st:cm_src_state) +
           cm_temp_offset (p:cm_program) (fid:int) (owner:int)`;
      thm address_facts = specl_rule(TERM_LIST(
          `p:cm_program`, `cm_state_regions (st:cm_src_state)`,
          concrete_cursors, `fid:int`, `cm_state_fp (st:cm_src_state)`,
          `cm_state_regions (st:cm_src_state)`, `spills:(cm_spill)list`,
          `saved:(cm_spill_frame)list`, `calls:(cm_call_sim_frame)list`,
          `owner:int`, base, address),
          get_cm_runtime_spill_holds_address_safe());
      address_facts = cm_pointer_total_apply(address_facts,
          THM_LIST(runtime_stack, held, conjunct1_rule(bounds),
            refl_rule(address)));
      thm proved = cm_pointer_total_apply(
          get_cm_target_v_index_right_step(), THM_LIST(
            shaped_layout, shaped_sim, shift_ok, base_live, base_view, held,
            scale_is_signed,
            cm_pointer_total_pick(address_facts,
              `tower_signed64 (cm_state_fp (st:cm_src_state))`),
            cm_pointer_total_pick(address_facts,
              `tower_signed64
                (cm_temp_offset (p:cm_program) (fid:int) (owner:int))`),
            refl_rule(address),
            cm_pointer_total_pick(address_facts,
              `tower_signed64 ${address:int}`),
            cm_pointer_total_pick(address_facts,
              `tower_word_valid ${address:int}`)));
      cm_pointer_total_accept(branch, shape, proved);
      continue;
    }

    {
      term mid = `a0:int`;
      term base_ty = `a1:cm_type`;
      thm phase_ready = cm_pointer_total_pick(shaped_context,
          `cm_v_phase_ready (p:cm_program) (incoming:cm_value)
            (st:cm_src_state) ${concrete_ann:cm_annotation}
            ${concrete_phase:cm_aphase}`);
      thm member_ok = conv_rule(reduce_rewrite_conv(THM_LIST(
          cm_v_phase_ready_def)), phase_ready);
      thm member_open = conv_rule(rewrite_conv(THM_LIST(
          get_cm_ptr_member_ok_def())), member_ok);
      thm pointer_live = conjunct1_rule(member_open);
      thm static_type = cm_pointer_total_pick(shaped_context,
          `cm_phase_static_type_ready (p:cm_program) (fid:int)
            ${concrete_phase:cm_aphase}`);
      thm member_valid = conv_rule(reduce_rewrite_conv(THM_LIST(
          cm_phase_static_type_ready_def)), static_type);
      thm valid_open = conv_rule(rewrite_conv(THM_LIST(
          get_cm_member_valid_def())), member_valid);
      thm base_pointer = cm_pointer_total_pick(valid_open,
          `cm_is_pointer ${base_ty:cm_type}`);
      thm value_type = cm_pointer_total_pick(shaped_context,
          `cm_phase_value_type_ready (p:cm_program) (fid:int)
            ${concrete_phase:cm_aphase} (incoming:cm_value)`);
      thm compatible = conv_rule(reduce_rewrite_conv(THM_LIST(
          cm_phase_value_type_ready_def)), value_type);
      thm pointer_view = cm_pointer_total_apply(specl_rule(TERM_LIST(
          `st:cm_src_state`, `incoming:cm_value`, base_ty),
          cm_pointer_view_type),
          THM_LIST(compatible, base_pointer, pointer_live));
      thm offset_is_signed = cm_pointer_total_apply(specl_rule(TERM_LIST(
          `p:cm_program`, base_ty, mid), cm_member_offset_signed),
          THM_LIST(typed, member_valid));
      thm proved = cm_pointer_total_apply(
          get_cm_target_v_member_step(), THM_LIST(
            shaped_layout, shaped_sim, member_ok, pointer_live,
            pointer_view, offset_is_signed));
      cm_pointer_total_accept(branch, shape, proved);
    }
  }
  return gnode_prove(root);
}

PROOF thm cm_target_v_pointer_step =
    cm_prove_target_v_pointer_step();

PROOF thm get_cm_target_v_pointer_step(void) {
  return cm_target_v_pointer_step;
}

PROOF static int cmc_preservation_target_value_pointer_total_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_target_value_pointer_total_axioms_before,
      "cmc_preservation_target_value_pointer_total introduced an axiom");
  ENSURE_COND(vector_size(hyp(cm_member_offset_signed)) == 0 &&
      vector_size(hyp(cm_target_v_pointer_step)) == 0,
      "pointer value target theorem is not closed");
  return 0;
err:
  return 1;
}
