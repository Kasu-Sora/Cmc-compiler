#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_target_value_scalar_total.h"
#include "cmc_preservation_target_value_context.h"
#include "cmc_preservation_target_value_init.h"
#include "cmc_preservation_target_value.h"
#include "cmc_preservation_target_value_unary.h"
#include "cmc_preservation_target_value_io.h"
#include "cmc_preservation_target_value_control.h"
#include "cmc_preservation_target_value_return.h"
#include "cmc_preservation_target_access.h"
#include "cmc_preservation_spill_safety.h"
#include "cmc_preservation_spill_holds_safety.h"
#include "cmc_preservation_binding_numeric.h"
#include "cmc_preservation_type_facts.h"
#include "cmc_sim.h"

#require "cmc_preservation_target_value_context.c"
#require "cmc_preservation_target_value_init.c"
#require "cmc_preservation_target_value.c"
#require "cmc_preservation_target_value_unary.c"
#require "cmc_preservation_target_value_io.c"
#require "cmc_preservation_target_value_control.c"
#require "cmc_preservation_target_value_return.c"
#require "cmc_preservation_target_access.c"
#require "cmc_preservation_spill_safety.c"
#require "cmc_preservation_spill_holds_safety.c"
#require "cmc_preservation_binding_numeric.c"
#require "cmc_preservation_type_facts.c"
#require "cmc_sim.c"

PROOF static size_t _cmc_preservation_target_value_scalar_total_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_scalar_total_pick(thm fact, term wanted) {
  if (alpha_compare(concl(fact), wanted) == 0) return fact;
  if (!is_conj(concl(fact))) return empty_theorem;
  thm left = cm_scalar_total_pick(conjunct1_rule(fact), wanted);
  if (!IS_NULL(left)) return left;
  return cm_scalar_total_pick(conjunct2_rule(fact), wanted);
}

PROOF static thm cm_scalar_total_scalar_kind(
    const thm scalar_expr, const term ty) {
  thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_scalar_expr_type_def(), get_cm_integer_type_def())),
      scalar_expr);
  term wanted =
      `${ty:cm_type} == CMCharTy ||
       ${ty:cm_type} == CMIntTy ||
       cm_is_pointer ${ty:cm_type}`;
  return mp_rule(taut_rule(mk_imp(concl(opened), wanted)), opened);
}

PROOF static thm cm_scalar_total_consequence(
    const thm premise, const term conclusion) {
  return mp_rule(taut_rule(mk_imp(concl(premise), conclusion)), premise);
}

PROOF static thm cm_scalar_total_apply(thm result, thm_list premises) {
  for (size_t i = 0; i < vector_size(premises); ++i) {
    result = match_mp_rule(result, premises[i]);
  }
  return result;
}

PROOF static void cm_scalar_total_accept(
    const gnode branch, const thm shape, const thm result) {
  thm_list rules = THM_LIST(shape, cm_phase_frame_def);
  thm normalized = conv_rule(reduce_rewrite_conv(rules), result);
  thm target_view = apply_conversion(
      reduce_rewrite_conv(rules), goal_ccl(branch->g));
  ACCEPT_TAC(branch, eq_mp_rule(sym_rule(target_view), normalized));
}

PROOF static thm cm_scalar_total_live_span(
    const thm memory_layout, const thm access_ok,
    const term p, const term st, const term calls,
    const term spill_frames, const term ptr, const term ty,
    const bool writable) {
  thm_list access_rules = THM_LIST(
      writable ? get_cm_store_ok_def() : get_cm_load_ok_def());
  if (writable) vector_add(&access_rules, get_cm_pointer_writable_def());
  thm opened = conv_rule(rewrite_conv(access_rules), access_ok);
  thm pointer_live = cm_scalar_total_pick(opened,
      `cm_pointer_live ${st:cm_src_state} ${ptr:cm_value}`);
  thm lower = cm_scalar_total_pick(opened,
      `cm_ptr_lo ${ptr:cm_value} <= cm_ptr_offset ${ptr:cm_value}`);
  thm upper = cm_scalar_total_pick(opened,
      `cm_ptr_offset ${ptr:cm_value} + cm_store_width ${ty:cm_type} <=
       cm_ptr_hi ${ptr:cm_value}`);
  thm result = specl_rule(TERM_LIST(
      p, st, calls, spill_frames, ptr, `cm_store_width ${ty:cm_type}`),
      get_cm_runtime_pointer_live_span());
  result = match_mp_rule(result, memory_layout);
  result = match_mp_rule(result, pointer_live);
  result = match_mp_rule(result, lower);
  result = match_mp_rule(result, upper);
  return match_mp_rule(result, spec_rule(ty, get_cm_store_width_positive()));
}

PROOF static thm cm_scalar_total_fp_signed(const thm runtime_stack) {
  thm fp_bounds = match_mp_rule(cm_runtime_stack_fp_bounds, runtime_stack);
  thm raw = mp_rule(int_arith_rule(mk_imp(
      concl(fp_bounds),
      `--9223372036854775808i <= cm_state_fp (st:cm_src_state) &&
       cm_state_fp st <= 9223372036854775807i`)), fp_bounds);
  thm view = apply_conversion(rewrite_conv(THM_LIST(
      get_tower_signed64_def())),
      `tower_signed64 (cm_state_fp (st:cm_src_state))`);
  return eq_mp_rule(sym_rule(view), raw);
}

PROOF static thm cm_prove_target_v_scalar_step(void) {
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
      `cm_v_phase_family ${phase:cm_aphase} == 0i`), result_term);
  gnode root = gnode_new_with_ccl(list_mk_forall(free_vars(body), body));
  gnode introduced = AUTO_INTROS_TAC(root);

  thm context = get_cm_target_v_context();
  thm_list context_premises = THM_LIST(
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
      assume_rule(`cm_task_tagged_valid ${task:cm_task}`));
  context = cm_scalar_total_apply(context, context_premises);
  thm layout = assume_rule(
      `cm_task_layout (p:cm_program) ${task:cm_task} ${ann:cm_annotation}`);
  thm sim = assume_rule(
      `cm_task_target_sim (p:cm_program) ${task:cm_task}
        (target:tvm_task) ${ann:cm_annotation}`);
  thm family = assume_rule(`cm_v_phase_family ${phase:cm_aphase} == 0i`);

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
    if (i != 0 && i != 1 && i != 2 && i != 3 && i != 6 &&
        i != 10 && i != 11 && i != 12 && i != 13 && i != 14 &&
        i != 20) {
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
    thm runtime_stack = cm_scalar_total_pick(shaped_context,
        `cm_runtime_stack (p:cm_program)
          (cm_state_regions (st:cm_src_state)) (fid:int)
          (cm_state_fp st) (cm_state_regions st)
          ${concrete_cursors:(cm_acursor)list} (spills:(cm_spill)list)
          (saved:(cm_spill_frame)list) (calls:(cm_call_sim_frame)list)`);
    thm memory_layout = cm_scalar_total_pick(shaped_context,
        `cm_runtime_memory_layout (p:cm_program) (st:cm_src_state)
          (calls:(cm_call_sim_frame)list)
          (CMSpillFrame (fid:int) (cm_state_fp st)
            (spills:(cm_spill)list) ::
           (saved:(cm_spill_frame)list))`);
    thm value_number_signed = specl_rule(TERM_LIST(
        `st:cm_src_state`, `incoming:cm_value`),
        get_cm_value_number_signed_bridge());

    if (i == 0) {
      thm proved = cm_scalar_total_apply(get_cm_target_v_halt_step(),
          THM_LIST(shaped_layout, shaped_sim, value_number_signed));
      cm_scalar_total_accept(branch, shape, proved);
      continue;
    }
    if (i == 1) {
      term ty = `a:cm_type`;
      thm phase_ready = cm_scalar_total_pick(shaped_context,
          `cm_v_phase_ready (p:cm_program) (incoming:cm_value)
            (st:cm_src_state) ${concrete_ann:cm_annotation}
            ${concrete_phase:cm_aphase}`);
      thm load_ok = conv_rule(reduce_rewrite_conv(THM_LIST(
          cm_v_phase_ready_def)), phase_ready);
      thm static_type = cm_scalar_total_pick(shaped_context,
          `cm_phase_static_type_ready (p:cm_program) (fid:int)
            ${concrete_phase:cm_aphase}`);
      thm scalar_expr = conv_rule(reduce_rewrite_conv(THM_LIST(
          cm_phase_static_type_ready_def)), static_type);
      thm scalar_kind =
          cm_scalar_total_scalar_kind(scalar_expr, ty);
      term spill_frames =
          `CMSpillFrame (fid:int) (cm_state_fp (st:cm_src_state))
            (spills:(cm_spill)list) :: (saved:(cm_spill_frame)list)`;
      thm live_span = cm_scalar_total_live_span(memory_layout, load_ok,
          `p:cm_program`, `st:cm_src_state`,
          `calls:(cm_call_sim_frame)list`, spill_frames,
          `incoming:cm_value`, ty, false);
      thm proved = cm_scalar_total_apply(get_cm_target_v_load_step(),
          THM_LIST(shaped_layout, shaped_sim, memory_layout, load_ok,
            scalar_kind, live_span));
      cm_scalar_total_accept(branch, shape, proved);
      continue;
    }
    if (i == 2) {
      thm bounds_disjunction = cm_scalar_total_pick(shaped_context,
          `cm_phase_is_halt ${concrete_phase:cm_aphase} ||
           (0i <= (fid:int) &&
            fid < ilength (cm_program_functions (p:cm_program)))`);
      thm bounds = conv_rule(reduce_rewrite_conv(THM_LIST(
          cm_phase_is_halt_def)), bounds_disjunction);
      thm temp_ready = cm_scalar_total_pick(shaped_context,
          `cm_v_temp_ready ${concrete_ann:cm_annotation}
            ${concrete_phase:cm_aphase}`);
      thm temp_equal = conv_rule(reduce_rewrite_conv(THM_LIST(
          cm_v_temp_ready_def, cm_phase_child_temp_def,
          cm_ann_temp_def, cm_ann_cursors_def, cm_cursor_temp_def,
          get_theorem_by_name("HD"))), temp_ready);
      thm spill_ready = cm_scalar_total_pick(shaped_context,
          `cm_v_spill_ready (p:cm_program) (fid:int)
            ${concrete_ann:cm_annotation} ${concrete_phase:cm_aphase}`);
      thm spill_bounds = conv_rule(reduce_rewrite_conv(THM_LIST(
          cm_v_spill_ready_def, cm_ann_temp_def, temp_equal,
          get_cm_temp_slots_def())), spill_ready);
      thm runtime_put = cm_runtime_stack_spill_put;
      runtime_put = specl_rule(TERM_LIST(
          `p:cm_program`, `cm_state_regions (st:cm_src_state)`,
          `fid:int`, `cm_state_fp (st:cm_src_state)`, concrete_cursors,
          `cm_state_regions (st:cm_src_state)`, `owner:int`,
          `incoming:cm_value`, `spills:(cm_spill)list`,
          `saved:(cm_spill_frame)list`, `calls:(cm_call_sim_frame)list`),
          runtime_put);
      runtime_put = cm_scalar_total_apply(runtime_put, THM_LIST(
          conjunct1_rule(bounds), conjunct1_rule(spill_bounds),
          conjunct2_rule(spill_bounds), runtime_stack));
      term address =
          `cm_state_fp (st:cm_src_state) +
           cm_temp_offset (p:cm_program) (fid:int) (owner:int)`;
      thm address_facts = specl_rule(TERM_LIST(
          `p:cm_program`, `cm_state_regions (st:cm_src_state)`,
          concrete_cursors, `fid:int`, `cm_state_fp (st:cm_src_state)`,
          `cm_state_regions (st:cm_src_state)`,
          `spills:(cm_spill)list`,
          `saved:(cm_spill_frame)list`, `calls:(cm_call_sim_frame)list`,
          `owner:int`, `incoming:cm_value`, address),
          get_cm_runtime_spill_address_safe());
      address_facts = cm_scalar_total_apply(address_facts,
          THM_LIST(runtime_put, conjunct1_rule(bounds), refl_rule(address)));
      thm tagged = cm_scalar_total_pick(shaped_context,
          `cm_tagged_span_valid (st:cm_src_state)`);
      thm proved = cm_scalar_total_apply(get_cm_target_v_assign_left_step(),
          THM_LIST(shaped_layout, shaped_sim, runtime_put,
            conjunct1_rule(bounds), temp_equal, tagged,
            cm_scalar_total_pick(address_facts,
              `tower_signed64 (cm_state_fp (st:cm_src_state))`),
            cm_scalar_total_pick(address_facts,
              `tower_signed64
                (cm_temp_offset (p:cm_program) (fid:int) (owner:int))`),
            refl_rule(address),
            cm_scalar_total_pick(address_facts,
              `tower_signed64 ${address:int}`),
            cm_scalar_total_pick(address_facts,
              `tower_word_valid ${address:int}`)));
      cm_scalar_total_accept(branch, shape, proved);
      continue;
    }
    if (i == 3) {
      term ptr = `a0:cm_value`;
      term ty = `a1:cm_type`;
      thm bounds_disjunction = cm_scalar_total_pick(shaped_context,
          `cm_phase_is_halt ${concrete_phase:cm_aphase} ||
           (0i <= (fid:int) &&
            fid < ilength (cm_program_functions (p:cm_program)))`);
      thm bounds = conv_rule(reduce_rewrite_conv(THM_LIST(
          cm_phase_is_halt_def)), bounds_disjunction);
      thm phase_ready = cm_scalar_total_pick(shaped_context,
          `cm_v_phase_ready (p:cm_program) (incoming:cm_value)
            (st:cm_src_state) ${concrete_ann:cm_annotation}
            ${concrete_phase:cm_aphase}`);
      thm store_ok = conv_rule(reduce_rewrite_conv(THM_LIST(
          cm_v_phase_ready_def)), phase_ready);
      thm static_type = cm_scalar_total_pick(shaped_context,
          `cm_phase_static_type_ready (p:cm_program) (fid:int)
            ${concrete_phase:cm_aphase}`);
      thm static_open = conv_rule(reduce_rewrite_conv(THM_LIST(
          cm_phase_static_type_ready_def)), static_type);
      thm scalar_expr = conjunct2_rule(static_open);
      thm scalar_kind =
          cm_scalar_total_scalar_kind(scalar_expr, ty);
      thm value_type = cm_scalar_total_pick(shaped_context,
          `cm_phase_value_type_ready (p:cm_program) (fid:int)
            ${concrete_phase:cm_aphase} (incoming:cm_value)`);
      thm convertible = conv_rule(reduce_rewrite_conv(THM_LIST(
          cm_phase_value_type_ready_def)), value_type);
      thm spill_fact = cm_scalar_total_pick(shaped_context,
          `cm_phase_spill_consistent (temp:int) (owner:int)
            ${concrete_phase:cm_aphase} (spills:(cm_spill)list)`);
      thm held = conjunct2_rule(conv_rule(reduce_rewrite_conv(THM_LIST(
          cm_phase_spill_consistent_def)), spill_fact));
      term address =
          `cm_state_fp (st:cm_src_state) +
           cm_temp_offset (p:cm_program) (fid:int) (owner:int)`;
      thm address_facts = specl_rule(TERM_LIST(
          `p:cm_program`, `cm_state_regions (st:cm_src_state)`,
          concrete_cursors, `fid:int`, `cm_state_fp (st:cm_src_state)`,
          `cm_state_regions (st:cm_src_state)`, `spills:(cm_spill)list`,
          `saved:(cm_spill_frame)list`, `calls:(cm_call_sim_frame)list`,
          `owner:int`, ptr, address),
          get_cm_runtime_spill_holds_address_safe());
      address_facts = cm_scalar_total_apply(address_facts,
          THM_LIST(runtime_stack, held, conjunct1_rule(bounds),
            refl_rule(address)));
      term spill_frames =
          `CMSpillFrame (fid:int) (cm_state_fp (st:cm_src_state))
            (spills:(cm_spill)list) :: (saved:(cm_spill_frame)list)`;
      thm live_span = cm_scalar_total_live_span(memory_layout, store_ok,
          `p:cm_program`, `st:cm_src_state`,
          `calls:(cm_call_sim_frame)list`, spill_frames, ptr, ty, true);
      thm proved = cm_scalar_total_apply(get_cm_target_v_assign_right_step(),
          THM_LIST(shaped_layout, shaped_sim, memory_layout, held,
            store_ok, scalar_kind, scalar_expr, convertible, live_span,
            cm_scalar_total_pick(address_facts,
              `tower_signed64 (cm_state_fp (st:cm_src_state))`),
            cm_scalar_total_pick(address_facts,
              `tower_signed64
                (cm_temp_offset (p:cm_program) (fid:int) (owner:int))`),
            refl_rule(address),
            cm_scalar_total_pick(address_facts,
              `tower_signed64 ${address:int}`),
            cm_scalar_total_pick(address_facts,
              `tower_word_valid ${address:int}`)));
      cm_scalar_total_accept(branch, shape, proved);
      continue;
    }
    if (i == 6) {
      gnode_list op_cases = BOOL_CASES_TAC(
          branch, `(a:int) == 0i`, "Hunary_zero");
      thm zero_result = cm_scalar_total_apply(
          get_cm_target_v_unary_zero_step(),
          THM_LIST(conv_rule(rewrite_conv(THM_LIST(shape,
              assume_rule(`(a:int) == 0i`), cm_phase_frame_def)), layout),
            conv_rule(rewrite_conv(THM_LIST(shape,
              assume_rule(`(a:int) == 0i`), cm_phase_frame_def)), sim)));
      thm_list zero_rules = THM_LIST(
          shape, assume_rule(`(a:int) == 0i`), cm_phase_frame_def);
      thm zero_normalized =
          conv_rule(reduce_rewrite_conv(zero_rules), zero_result);
      thm zero_view = apply_conversion(
          reduce_rewrite_conv(zero_rules), goal_ccl(op_cases[0]->g));
      ACCEPT_TAC(op_cases[0],
          eq_mp_rule(sym_rule(zero_view), zero_normalized));
      thm other_result = cm_scalar_total_apply(
          get_cm_target_v_unary_other_step(),
          THM_LIST(shaped_layout, shaped_sim,
            assume_rule(`~((a:int) == 0i)`)));
      cm_scalar_total_accept(op_cases[1], shape, other_result);
      continue;
    }
    if (i == 10 || i == 11) {
      thm local = i == 10
          ? get_cm_target_v_putc_step() : get_cm_target_v_puti_step();
      thm proved = cm_scalar_total_apply(local,
          THM_LIST(shaped_layout, shaped_sim));
      cm_scalar_total_accept(branch, shape, proved);
      continue;
    }
    if (i == 12 || i == 0) {
      thm local = i == 12
          ? get_cm_target_v_exit_step() : get_cm_target_v_halt_step();
      thm proved = cm_scalar_total_apply(local,
          THM_LIST(shaped_layout, shaped_sim, value_number_signed));
      cm_scalar_total_accept(branch, shape, proved);
      continue;
    }
    if (i == 13) {
      thm proved = cm_scalar_total_apply(get_cm_target_v_expr_stmt_step(),
          THM_LIST(shaped_layout, shaped_sim));
      cm_scalar_total_accept(branch, shape, proved);
      continue;
    }
    if (i == 14) {
      term slot = `a:int`;
      term ty =
          `cm_slot_ty
            (inth ${slot:int}
              (cm_function_locals
                (inth (fid:int) (cm_program_functions (p:cm_program)))))`;
      term ptr = `cm_state_env (st:cm_src_state) 1i ${slot:int}`;
      term offset = `cm_local_offset (p:cm_program) (fid:int) ${slot:int}`;
      term address =
          `cm_local_base (p:cm_program) (fid:int) ${slot:int}
            (cm_state_fp (st:cm_src_state))`;
      thm bounds_disjunction = cm_scalar_total_pick(shaped_context,
          `cm_phase_is_halt ${concrete_phase:cm_aphase} ||
           (0i <= (fid:int) &&
            fid < ilength (cm_program_functions (p:cm_program)))`);
      thm bounds = conv_rule(reduce_rewrite_conv(THM_LIST(
          cm_phase_is_halt_def)), bounds_disjunction);
      thm source_ready = cm_scalar_total_pick(shaped_context,
          `cm_v_source_ready (p:cm_program) (fid:int)
            (st:cm_src_state) ${concrete_phase:cm_aphase}`);
      thm source_open = conv_rule(rewrite_conv(THM_LIST(
          cm_v_source_ready_def)), source_ready);
      thm init_ready = spec_rule(slot, conjunct1_rule(source_open));
      init_ready = match_mp_rule(init_ready, refl_rule(concrete_phase));
      thm address_ok = conjunct1_rule(init_ready);
      thm store_ok = conjunct2_rule(init_ready);
      thm static_type = cm_scalar_total_pick(shaped_context,
          `cm_phase_static_type_ready (p:cm_program) (fid:int)
            ${concrete_phase:cm_aphase}`);
      thm static_open = conv_rule(reduce_rewrite_conv(THM_LIST(
          cm_phase_static_type_ready_def)), static_type);
      thm slot_nonnegative = conjunct1_rule(static_open);
      thm slot_upper = conjunct1_rule(conjunct2_rule(static_open));
      thm scalar_type = conjunct2_rule(conjunct2_rule(
          conjunct2_rule(static_open)));
      thm scalar_expr = match_mp_rule(
          specl_rule(TERM_LIST(ty, `cm_program_structs (p:cm_program)`),
            cm_scalar_type_is_expr_type), scalar_type);
      thm scalar_kind =
          cm_scalar_total_scalar_kind(scalar_expr, ty);
      term spill_frames =
          `CMSpillFrame (fid:int) (cm_state_fp (st:cm_src_state))
            (spills:(cm_spill)list) :: (saved:(cm_spill_frame)list)`;
      thm live_span = cm_scalar_total_live_span(memory_layout, store_ok,
          `p:cm_program`, `st:cm_src_state`,
          `calls:(cm_call_sim_frame)list`, spill_frames, ptr, ty, true);
      thm typed = cm_scalar_total_pick(shaped_context,
          `cm_typed_program (p:cm_program)`);
      thm typed_open = conv_rule(rewrite_conv(THM_LIST(
          get_cm_typed_program_def())), typed);
      thm function_rule = spec_rule(`fid:int`,
          cm_scalar_total_consequence(typed_open,
            `!(i:int). 0i <= i ==>
              i < ilength (cm_program_functions (p:cm_program)) ==>
              cm_function_wf p (inth i (cm_program_functions p))`));
      thm function_wf = cm_scalar_total_apply(function_rule,
          THM_LIST(conjunct1_rule(bounds), conjunct2_rule(bounds)));
      thm fp_is_signed = cm_scalar_total_fp_signed(runtime_stack);
      thm offset_is_signed = cm_scalar_total_apply(
          specl_rule(TERM_LIST(`p:cm_program`, `fid:int`, slot),
            get_cm_local_offset_signed()),
          THM_LIST(function_wf, slot_nonnegative, slot_upper));
      thm address_open = conv_rule(reduce_rewrite_conv(THM_LIST(
          get_cm_binding_address_ok_def())), address_ok);
      thm address_equal = eqt_elim_rule(apply_conversion(
          reduce_rewrite_conv(THM_LIST(
            get_cm_local_base_def(), get_cm_local_offset_def())),
          `${address:int} ==
           cm_state_fp (st:cm_src_state) + ${offset:int}`));
      thm address_is_signed = cm_scalar_total_pick(address_open,
          `tower_signed64 ${address:int}`);
      thm wrap_equal = cm_scalar_total_pick(address_open,
          `tower_wrap64 ${address:int} ==
           cm_value_number (st:cm_src_state) ${ptr:cm_value}`);
      thm proved = get_cm_target_v_init_step();
      proved = match_mp_rule(proved, shaped_layout);
      proved = match_mp_rule(proved, shaped_sim);
      proved = match_mp_rule(proved, address_ok);
      proved = match_mp_rule(proved, refl_rule(ty));
      proved = match_mp_rule(proved, refl_rule(ptr));
      proved = match_mp_rule(proved, memory_layout);
      proved = match_mp_rule(proved, store_ok);
      proved = match_mp_rule(proved, scalar_kind);
      proved = match_mp_rule(proved, live_span);
      proved = match_mp_rule(proved, value_number_signed);
      proved = match_mp_rule(proved, fp_is_signed);
      proved = match_mp_rule(proved, offset_is_signed);
      proved = match_mp_rule(proved, address_equal);
      proved = match_mp_rule(proved, address_is_signed);
      proved = match_mp_rule(proved, wrap_equal);
      cm_scalar_total_accept(branch, shape, proved);
      continue;
    }
    if (i == 20) {
      thm proved = match_mp_rule(
          get_cm_target_v_return_step(), shaped_sim);
      cm_scalar_total_accept(branch, shape, proved);
      continue;
    }
  }
  return gnode_prove(root);
}

PROOF thm cm_target_v_scalar_step =
    cm_prove_target_v_scalar_step();

PROOF thm get_cm_target_v_scalar_step(void) {
  return cm_target_v_scalar_step;
}

PROOF static int cmc_preservation_target_value_scalar_total_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_target_value_scalar_total_axioms_before,
      "cmc_preservation_target_value_scalar_total introduced an axiom");
  ENSURE_COND(vector_size(hyp(cm_target_v_scalar_step)) == 0,
      "scalar target theorem has assumptions");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_target_value_scalar_total_checked =
    cmc_preservation_target_value_scalar_total_final_checks();
