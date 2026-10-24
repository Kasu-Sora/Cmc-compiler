#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "userlib/proof_patterns.h"
#include "cmc_preservation_target_value_call_total.h"
#include "cmc_preservation_target_value_arg.h"
#include "cmc_preservation_target_value_call.h"
#include "cmc_preservation_target_value_context.h"
#include "cmc_preservation_target_ready.h"
#include "cmc_preservation_generation.h"
#include "cmc_preservation_generation_annotation.h"
#include "cmc_preservation_spill_semantic.h"
#include "cmc_preservation_invariant.h"

#require "cmc_preservation_target_value_arg.c"
#require "cmc_preservation_target_value_call.c"
#require "cmc_preservation_target_value_context.c"
#require "cmc_preservation_target_ready.c"
#require "userlib/proof_patterns.c"
#require "cmc_preservation_generation_annotation.c"

PROOF static size_t _cmc_preservation_target_value_call_total_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_call_total_pick(thm fact, term wanted) {
  if (alpha_compare(concl(fact), wanted) == 0) return fact;
  if (!is_conj(concl(fact))) return empty_theorem;
  thm left = cm_call_total_pick(conjunct1_rule(fact), wanted);
  if (!IS_NULL(left)) return left;
  return cm_call_total_pick(conjunct2_rule(fact), wanted);
}

PROOF static thm cm_call_total_apply(thm result, thm_list premises) {
  for (size_t i = 0; i < vector_size(premises); ++i) {
    result = match_mp_rule(result, premises[i]);
  }
  return result;
}

PROOF static thm cm_call_total_shape_fact(
    const term wanted, const thm fact, const thm_list rules) {
  thm wanted_view = apply_conversion(
      reduce_rewrite_conv(rules), wanted);
  thm fact_normal = conv_rule(reduce_rewrite_conv(rules), fact);
  return eq_mp_rule(sym_rule(wanted_view), fact_normal);
}

PROOF static thm cm_call_total_match(
    thm result, const thm fact, const thm_list rules) {
  term wanted = dest_imp(concl(result)).tm1;
  return match_mp_rule(result,
      cm_call_total_shape_fact(wanted, fact, rules));
}

PROOF static void cm_call_total_accept(
    const gnode branch, const thm_list rules, const thm result) {
  thm normalized = conv_rule(reduce_rewrite_conv(rules), result);
  thm target_view = apply_conversion(
      reduce_rewrite_conv(rules), goal_ccl(branch->g));
  ACCEPT_TAC(branch, eq_mp_rule(sym_rule(target_view), normalized));
}

PROOF static thm_list cm_call_total_annotation_rules(void) {
  return THM_LIST(
      cm_ann_linear_def, cm_ann_plain_def,
      cm_ann_put_spill_def, cm_ann_spills_set_def,
      cm_ann_pc_def, cm_ann_temp_def, cm_ann_break_def,
      cm_ann_continue_def, cm_ann_cursors_def,
      cm_ann_spills_def, cm_ann_saved_def, cm_ann_calls_def,
      cm_active_spill_frames_def,
      get_theorem_by_name("ILENGTH_DEF"),
      int_ring_rule(`8i + 8i == 16i`));
}

PROOF static thm cm_prove_target_v_call_step(void) {
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
      `cm_v_phase_family ${phase:cm_aphase} == 4i`), result_term);
  gnode root = gnode_new_with_ccl(list_mk_forall(free_vars(body), body));
  gnode introduced = AUTO_INTROS_TAC(root);

  thm wf = assume_rule(`cm_wf_program (p:cm_program)`);
  thm generation_safe = assume_rule(
      `cm_task_generation_safe (p:cm_program) ${task:cm_task}
        ${ann:cm_annotation}`);
  thm context = get_cm_target_v_context();
  context = cm_call_total_apply(context, THM_LIST(
      wf,
      assume_rule(`cm_runtime_step_ready (p:cm_program) ${task:cm_task}
        ${ann:cm_annotation}`),
      assume_rule(`cm_task_runtime_invariant (p:cm_program)
        ${task:cm_task} ${ann:cm_annotation}`),
      assume_rule(`cm_task_type_ready (p:cm_program) ${task:cm_task}
        ${ann:cm_annotation}`),
      assume_rule(`cm_task_fid_ready (p:cm_program) ${task:cm_task}`),
      assume_rule(`cm_annotation_spill_consistent ${ann:cm_annotation}`),
      generation_safe,
      assume_rule(`cm_task_tagged_valid ${task:cm_task}`)));
  thm layout = assume_rule(
      `cm_task_layout (p:cm_program) ${task:cm_task} ${ann:cm_annotation}`);
  thm sim = assume_rule(
      `cm_task_target_sim (p:cm_program) ${task:cm_task}
        (target:tvm_task) ${ann:cm_annotation}`);
  thm family = assume_rule(`cm_v_phase_family ${phase:cm_aphase} == 4i`);

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
    if (i != 21) {
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
    term callee = `a0:int`;
    term rest_args = `a1:(cm_expr)list`;
    term values = `a2:(cm_value)list`;
    term ret = `a3:cm_type`;
    term all_args = `a4:(cm_expr)list`;
    term base_slot = `a5:int`;
    term current_slot = `a6:int`;
    term scratch = `a7:int`;

    thm shaped_context = conv_rule(rewrite_conv(THM_LIST(shape)), context);
    thm_list phase_rules = THM_LIST(shape, cm_phase_frame_def);
    thm shaped_layout = conv_rule(reduce_rewrite_conv(phase_rules), layout);
    thm shaped_sim = conv_rule(reduce_rewrite_conv(phase_rules), sim);
    thm bounds_disjunction = cm_call_total_pick(shaped_context,
        `cm_phase_is_halt ${concrete_phase:cm_aphase} ||
         (0i <= (fid:int) &&
          fid < ilength (cm_program_functions (p:cm_program)))`);
    thm fid_bounds = conv_rule(reduce_rewrite_conv(THM_LIST(
        cm_phase_is_halt_def)), bounds_disjunction);
    thm fid_lower = conjunct1_rule(fid_bounds);
    thm phase_ready = cm_call_total_pick(shaped_context,
        `cm_v_phase_ready (p:cm_program) (incoming:cm_value)
          (st:cm_src_state) ${concrete_ann:cm_annotation}
          ${concrete_phase:cm_aphase}`);
    thm spill_ready = cm_call_total_pick(shaped_context,
        `cm_v_spill_ready (p:cm_program) (fid:int)
          ${concrete_ann:cm_annotation} ${concrete_phase:cm_aphase}`);
    thm spill_bounds = conv_rule(reduce_rewrite_conv(THM_LIST(
        cm_v_spill_ready_def)), spill_ready);
    thm current_nonnegative = conjunct1_rule(conjunct2_rule(spill_bounds));
    thm current_upper_raw =
        conjunct2_rule(conjunct2_rule(spill_bounds));
    thm current_upper = conv_rule(rewrite_conv(THM_LIST(
        get_cm_temp_slots_def())), current_upper_raw);
    thm phase_spill = cm_call_total_pick(shaped_context,
        `cm_phase_spill_consistent (temp:int) (owner:int)
          ${concrete_phase:cm_aphase} (spills:(cm_spill)list)`);
    thm regions_before = cm_call_total_pick(shaped_context,
        `cm_regions_before (cm_state_regions (st:cm_src_state))
          (cm_state_nextgen st)`);
    thm runtime_stack = cm_call_total_pick(shaped_context,
        `cm_runtime_stack (p:cm_program)
          (cm_state_regions (st:cm_src_state)) (fid:int)
          (cm_state_fp st) (cm_state_regions st)
          ${concrete_cursors:(cm_acursor)list} (spills:(cm_spill)list)
          (saved:(cm_spill_frame)list) (calls:(cm_call_sim_frame)list)`);
    thm typed = cm_call_total_pick(shaped_context,
        `cm_typed_program (p:cm_program)`);
    thm state_generation = cm_call_total_pick(shaped_context,
        `cm_state_generation_below (p:cm_program) (fid:int)
          (st:cm_src_state)`);
    thm annotation_generation = cm_call_total_pick(shaped_context,
        `cm_annotation_generation_below ${concrete_task:cm_task}
          ${concrete_ann:cm_annotation}`);
    thm tagged = cm_call_total_pick(shaped_context,
        `cm_tagged_span_valid (st:cm_src_state)`);

    term stored_spills =
        `cm_spill_put ${current_slot:int} (incoming:cm_value)
          (spills:(cm_spill)list)`;
    thm runtime_put = specl_rule(TERM_LIST(
        `p:cm_program`, `cm_state_regions (st:cm_src_state)`,
        `fid:int`, `cm_state_fp (st:cm_src_state)`, concrete_cursors,
        `cm_state_regions (st:cm_src_state)`, current_slot,
        `incoming:cm_value`, `spills:(cm_spill)list`,
        `saved:(cm_spill_frame)list`, `calls:(cm_call_sim_frame)list`),
        cm_runtime_stack_spill_put);
    runtime_put = cm_call_total_apply(runtime_put, THM_LIST(
        fid_lower, current_nonnegative, current_upper, runtime_stack));

    term address =
        `cm_state_fp (st:cm_src_state) +
         cm_temp_offset (p:cm_program) (fid:int) ${current_slot:int}`;
    thm address_facts = specl_rule(TERM_LIST(
        `p:cm_program`, `cm_state_regions (st:cm_src_state)`,
        concrete_cursors, `fid:int`, `cm_state_fp (st:cm_src_state)`,
        `cm_state_regions (st:cm_src_state)`, `spills:(cm_spill)list`,
        `saved:(cm_spill_frame)list`, `calls:(cm_call_sim_frame)list`,
        current_slot, `incoming:cm_value`, address),
        get_cm_runtime_spill_address_safe());
    address_facts = cm_call_total_apply(address_facts,
        THM_LIST(runtime_put, fid_lower, refl_rule(address)));

    gnode_list rest_cases = DISJ_CASES_TAC(branch,
        ispec_rule(rest_args, get_theorem_by_name("list_CASES")),
        "Hrest_args");
    {
      thm rest_nil = assume_rule(goal_lasmps(rest_cases[0]->g)[
          labeled_term_list_index(goal_lasmps(rest_cases[0]->g),
            "Hrest_args")].tm);
      thm_list nil_rules = THM_LIST(
          shape, rest_nil, cm_phase_frame_def);
      thm nil_layout = conv_rule(reduce_rewrite_conv(nil_rules), layout);
      thm nil_sim = conv_rule(reduce_rewrite_conv(nil_rules), sim);
      thm nil_phase_ready = conv_rule(reduce_rewrite_conv(THM_LIST(
          rest_nil, cm_v_phase_ready_def, cm_ann_cursors_def,
          get_theorem_by_name("TL"))), phase_ready);
      thm call_ok = conjunct1_rule(nil_phase_ready);
      thm call_depth = conjunct2_rule(nil_phase_ready);
      term call_values =
          `REVERSE ((incoming:cm_value) :: ${values:(cm_value)list})`;
      term store_code =
          `cm_temp_store_code (p:cm_program) (fid:int)
            ${current_slot:int}`;
      term reload_code =
          `cm_emit_args_reload (p:cm_program) (fid:int)
            ${base_slot:int} ${all_args:(cm_expr)list}`;
      term stored_ann =
          `cm_ann_put_spill ${current_slot:int} (incoming:cm_value)
            (cm_ann_linear ${store_code:(tvm_inst)list}
              ${concrete_ann:cm_annotation})`;
      term reload_ann =
          `cm_ann_linear ${reload_code:(tvm_inst)list}
            ${stored_ann:cm_annotation}`;
      term return_pc =
          `(pc:int) + ilength ${store_code:(tvm_inst)list} +
            ilength ${reload_code:(tvm_inst)list} + 1i`;
      term entered =
          `cm_ann_enter_call (p:cm_program) (fid:int) ${callee:int}
            (st:cm_src_state) ${ret:cm_type} ${return_pc:int}
            (owner:int) (saved_break:int) (saved_continue:int)
            (rest:(cm_acursor)list) ${stored_spills:(cm_spill)list}
            (saved:(cm_spill_frame)list)
            (calls:(cm_call_sim_frame)list)`;
      term frame_bytes =
          `cm_frame_size (cm_program_structs (p:cm_program))
            (inth ${callee:int} (cm_program_functions p))`;
      term frame_base =
          `cm_state_fp (st:cm_src_state) - ${frame_bytes:int}`;
      term active =
          `cm_active_spill_frames (fid:int) (st:cm_src_state)
            ${reload_ann:cm_annotation}`;
      term pending =
          `cm_call_pending_base (p:cm_program) ${callee:int}
            (st:cm_src_state)`;

      thm opened_phase_spill = conv_rule(rewrite_conv(THM_LIST(
          cm_phase_spill_consistent_def)), phase_spill);
      thm owner_old_upper = conjunct1_rule(opened_phase_spill);
      thm after_owner = conjunct2_rule(opened_phase_spill);
      thm base_equal = conjunct1_rule(after_owner);
      thm after_base = conjunct2_rule(after_owner);
      thm current_equal = conjunct1_rule(after_base);
      thm after_current = conjunct2_rule(after_base);
      thm scratch_equal = conjunct1_rule(after_current);
      thm after_scratch = conjunct2_rule(after_current);
      thm length_equal = conjunct1_rule(after_scratch);
      thm after_length = conjunct2_rule(after_scratch);
      thm current_old_upper = conjunct1_rule(after_length);
      thm staged = conjunct2_rule(after_length);
      thm values_length_nonnegative = ispec_rule(
          values, get_theorem_by_name("ILENGTH_NONNEG"));
      thm owner_current = cm_call_total_apply(int_arith_rule(
          imp_chain(TERM_LIST(concl(base_equal), concl(current_equal),
            concl(values_length_nonnegative)),
            `(owner:int) <= ${current_slot:int}`)),
          THM_LIST(base_equal, current_equal, values_length_nonnegative));
      thm owner_slots = cm_call_total_apply(int_arith_rule(
          imp_chain(TERM_LIST(concl(owner_current),
            concl(current_upper_raw)),
            `(owner:int) <=
             cm_temp_slots
               (inth (fid:int) (cm_program_functions (p:cm_program)))`)),
          THM_LIST(owner_current, current_upper_raw));
      thm current_slots = mp_rule(int_arith_rule(mk_imp(
          concl(current_upper_raw),
          `${current_slot:int} <=
           cm_temp_slots
             (inth (fid:int) (cm_program_functions (p:cm_program)))`)),
          current_upper_raw);
      term full_phase_spill_term =
          `cm_phase_spill_consistent
            (cm_temp_slots
              (inth (fid:int) (cm_program_functions (p:cm_program))))
            (owner:int) ${concrete_phase:cm_aphase}
            (spills:(cm_spill)list)`;
      thm full_phase_view = apply_conversion(rewrite_conv(THM_LIST(
          cm_phase_spill_consistent_def)), full_phase_spill_term);
      thm full_phase_spill = eq_mp_rule(sym_rule(full_phase_view),
          list_conj_rule(THM_LIST(owner_slots, base_equal, current_equal,
            scratch_equal, length_equal, current_slots, staged)));
      (void)owner_old_upper;
      (void)current_old_upper;

      thm popped_stack = conv_rule(reduce_rewrite_conv(THM_LIST(
          rest_nil, cm_runtime_stack_def, cm_cursor_phase_def,
          cm_phase_is_call_def, cm_phase_is_scope_def,
          cm_phase_is_halt_def)), runtime_put);
      thm call_ready = get_cm_target_call_ready();
      call_ready = cm_call_total_apply(call_ready, THM_LIST(
          wf, state_generation, call_ok, call_depth,
          regions_before, popped_stack));
      call_ready = spec_rule(ret, call_ready);
      call_ready = spec_rule(return_pc, call_ready);
      call_ready = spec_rule(`owner:int`, call_ready);
      call_ready = spec_rule(`saved_break:int`, call_ready);
      call_ready = spec_rule(`saved_continue:int`, call_ready);
      thm call_ready_opened = conv_rule(rewrite_conv(THM_LIST(
          cm_call_target_ready_def)), call_ready);

      thm state_opened = conv_rule(rewrite_conv(THM_LIST(
          cm_state_generation_below_def)), state_generation);
      thm all_tags = cm_call_total_pick(state_opened,
          `cm_tags_generation_below
            (cm_state_nextgen (st:cm_src_state))
            (cm_state_tags st)`);
      thm state_tags = match_mp_rule(specl_rule(TERM_LIST(
          `st:cm_src_state`, `cm_state_nextgen (st:cm_src_state)`),
          cm_state_tags_generation_from_all), all_tags);

      thm task_generation_opened = conv_rule(reduce_rewrite_conv(THM_LIST(
          shape, rest_nil, cm_task_generation_safe_def,
          cm_task_generation_below_def, cm_phase_frame_def,
          cm_frames_generation_below_def, cm_frame_generation_below_def)),
          generation_safe);
      thm incoming_generation = cm_call_total_pick(task_generation_opened,
          `cm_value_generation_below
            (cm_state_nextgen (st:cm_src_state)) (incoming:cm_value)`);
      thm prior_values_generation = cm_call_total_pick(
          task_generation_opened,
          `cm_values_generation_below
            (cm_state_nextgen (st:cm_src_state))
            ${values:(cm_value)list}`);
      term accumulated_term =
          `cm_values_generation_below
            (cm_state_nextgen (st:cm_src_state))
            ((incoming:cm_value) :: ${values:(cm_value)list})`;
      thm accumulated_view = apply_conversion(rewrite_conv(THM_LIST(
          cm_values_generation_below_def)), accumulated_term);
      thm accumulated_generation = eq_mp_rule(sym_rule(accumulated_view),
          conj_rule(incoming_generation, prior_values_generation));
      term reversed_call_values_term =
          `cm_values_generation_below
            (cm_state_nextgen (st:cm_src_state))
            (REVERSE ${call_values:(cm_value)list})`;
      thm reversed_call_values_view = apply_conversion(
          reduce_rewrite_conv(THM_LIST(
            get_theorem_by_name("REVERSE_REVERSE"))),
          reversed_call_values_term);
      thm call_values_generation = eq_mp_rule(
          sym_rule(reversed_call_values_view), accumulated_generation);

      thm annotation_generation_opened = conv_rule(
          reduce_rewrite_conv(THM_LIST(
            cm_annotation_generation_below_def,
            cm_active_spill_frames_def,
            cm_spill_frames_generation_below_def,
            cm_spill_frame_spills_def,
            cm_ann_spills_def, cm_ann_saved_def)),
          annotation_generation);
      thm old_spills_generation = cm_call_total_pick(
          annotation_generation_opened,
          `cm_spills_generation_below
            (cm_state_nextgen (st:cm_src_state))
            (spills:(cm_spill)list)`);
      thm saved_generation = cm_call_total_pick(
          annotation_generation_opened,
          `cm_spill_frames_generation_below
            (cm_state_nextgen (st:cm_src_state))
            (saved:(cm_spill_frame)list)`);
      thm stored_spills_generation = specl_rule(TERM_LIST(
          `spills:(cm_spill)list`,
          `cm_state_nextgen (st:cm_src_state)`, current_slot,
          `incoming:cm_value`), cm_spills_generation_put);
      stored_spills_generation = cm_call_total_apply(
          stored_spills_generation,
          THM_LIST(incoming_generation, old_spills_generation));
      term raw_active_term =
          `cm_spill_frames_generation_below
            (cm_state_nextgen (st:cm_src_state))
            (CMSpillFrame (fid:int) (cm_state_fp st)
              ${stored_spills:(cm_spill)list} ::
             (saved:(cm_spill_frame)list))`;
      thm raw_active_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
          cm_spill_frames_generation_below_def,
          cm_spill_frame_spills_def)), raw_active_term);
      thm raw_active_generation = eq_mp_rule(sym_rule(raw_active_view),
          conj_rule(stored_spills_generation, saved_generation));
      thm_list ann_rules = cm_call_total_annotation_rules();
      vector_add(&ann_rules, shape);
      vector_add(&ann_rules, rest_nil);
      vector_add(&ann_rules, cm_phase_frame_def);
      thm active_generation = cm_call_total_shape_fact(
          `cm_spill_frames_generation_below
            (cm_state_nextgen (st:cm_src_state))
            ${active:(cm_spill_frame)list}`,
          raw_active_generation, ann_rules);

      term raw_active =
          `CMSpillFrame (fid:int) (cm_state_fp (st:cm_src_state))
            ${stored_spills:(cm_spill)list} ::
           (saved:(cm_spill_frame)list)`;
      thm target_valid = cm_call_total_pick(call_ready_opened,
          `tvm_target_valid (cm_model_code (p:cm_program))
            (cm_function_pc p ${callee:int})`);
      thm nextgen_nonnegative = cm_call_total_pick(call_ready_opened,
          `0i <= cm_state_nextgen (st:cm_src_state)`);
      thm calls_capacity = cm_call_total_pick(call_ready_opened,
          `ilength (calls:(cm_call_sim_frame)list) < 65536i`);
      thm values_capacity = cm_call_total_pick(call_ready_opened,
          `ilength ${call_values:(cm_value)list} < 65534i`);
      thm outside_frame = cm_call_total_pick(call_ready_opened,
          `!addr. cm_live_address (st:cm_src_state) addr ==>
            ~(${frame_base:int} <= addr && addr < ${frame_base:int} + 8i)`);
      thm outside_scratch = cm_call_total_pick(call_ready_opened,
          `!addr. cm_live_address (st:cm_src_state) addr ==>
            ~(8i <= addr && addr < 16i)`);
      thm left_disjoint = cm_call_total_pick(call_ready_opened,
          `cm_range_disjoint ${frame_base:int} 8i 8i 8i`);
      thm right_disjoint = cm_call_total_pick(call_ready_opened,
          `cm_range_disjoint 8i 8i ${frame_base:int} 8i`);
      thm calls_frame_safe = cm_call_total_pick(call_ready_opened,
          `cm_call_frames_store_safe CMIntTy ${frame_base:int}
            (calls:(cm_call_sim_frame)list)`);
      thm spills_frame_safe = cm_call_total_pick(call_ready_opened,
          `cm_spill_frames_store_safe (p:cm_program) CMIntTy
            ${frame_base:int} ${raw_active:(cm_spill_frame)list}`);
      thm calls_scratch_safe = cm_call_total_pick(call_ready_opened,
          `cm_call_frames_store_safe CMIntTy 8i
            (calls:(cm_call_sim_frame)list)`);
      thm spills_scratch_safe = cm_call_total_pick(call_ready_opened,
          `cm_spill_frames_store_safe (p:cm_program) CMIntTy 8i
            ${raw_active:(cm_spill_frame)list}`);
      thm frame_bytes_fit = cm_call_total_pick(call_ready_opened,
          `tower_signed64 ${frame_bytes:int}`);
      thm frame_base_fit = cm_call_total_pick(call_ready_opened,
          `tower_signed64 ${frame_base:int}`);
      thm frame_base_word = cm_call_total_pick(call_ready_opened,
          `tower_word_valid ${frame_base:int}`);
      thm pending_layout = cm_call_total_pick(call_ready_opened,
          `cm_runtime_memory_layout (p:cm_program)
            ${pending:cm_src_state}
            (cm_ann_calls ${entered:cm_annotation})
            (cm_active_spill_frames ${callee:int}
              ${pending:cm_src_state} ${entered:cm_annotation})`);

      thm proved = specl_rule(TERM_LIST(
          `target:tvm_task`, `p:cm_program`, `fid:int`,
          `incoming:cm_value`, `st:cm_src_state`,
          `pc:int`, `temp:int`, `breakpc:int`, `continuepc:int`,
          callee, values, ret, all_args, base_slot, current_slot,
          scratch, `owner:int`, `saved_break:int`, `saved_continue:int`,
          `rest:(cm_acursor)list`, `spills:(cm_spill)list`,
          `saved:(cm_spill_frame)list`,
          `calls:(cm_call_sim_frame)list`),
          get_cm_target_v_arg_nil_step());
      thm_list direct_premises = THM_LIST(
          nil_layout, nil_sim, runtime_put, full_phase_spill,
          spill_ready, fid_lower, typed,
          call_ok, call_depth, target_valid, regions_before,
          nextgen_nonnegative, calls_capacity, values_capacity,
          state_tags, call_values_generation, active_generation,
          tagged, outside_frame, outside_scratch, left_disjoint,
          right_disjoint, calls_frame_safe, spills_frame_safe,
          calls_scratch_safe, spills_scratch_safe, frame_bytes_fit,
          frame_base_fit, frame_base_word, pending_layout);
      for (size_t premise_index = 0;
           premise_index < vector_size(direct_premises);
           ++premise_index) {
        proved = cm_call_total_match(
            proved, direct_premises[premise_index], ann_rules);
      }
      cm_call_total_accept(rest_cases[0], nil_rules, proved);
    }
    {
      gnode cons_branch = ASMP_EXISTS_TAC(
          rest_cases[1], "Hrest_args", NULL);
      cons_branch = ASMP_EXISTS_TAC(cons_branch, "Hrest_args", NULL);
      thm rest_cons = assume_rule(goal_lasmps(cons_branch->g)[
          labeled_term_list_index(goal_lasmps(cons_branch->g),
            "Hrest_args")].tm);
      thm_list cons_rules = THM_LIST(
          shape, rest_cons, cm_phase_frame_def);
      thm cons_layout = conv_rule(reduce_rewrite_conv(cons_rules), layout);
      thm cons_sim = conv_rule(reduce_rewrite_conv(cons_rules), sim);
      thm cons_runtime_put = conv_rule(
          rewrite_conv(THM_LIST(rest_cons)), runtime_put);
      thm proved = get_cm_target_v_arg_cons_step();
      proved = cm_call_total_apply(proved, THM_LIST(
          cons_layout, cons_sim, cons_runtime_put, fid_lower, tagged,
          cm_call_total_pick(address_facts,
            `tower_signed64 (cm_state_fp (st:cm_src_state))`),
          cm_call_total_pick(address_facts,
            `tower_signed64
              (cm_temp_offset (p:cm_program) (fid:int)
                ${current_slot:int})`),
          refl_rule(address),
          cm_call_total_pick(address_facts,
            `tower_signed64 ${address:int}`),
          cm_call_total_pick(address_facts,
            `tower_word_valid ${address:int}`)));
      cm_call_total_accept(cons_branch, cons_rules, proved);
    }
  }
  return gnode_prove(root);
}

PROOF thm cm_target_v_call_step =
    cm_prove_target_v_call_step();

PROOF thm get_cm_target_v_call_step(void) {
  return cm_target_v_call_step;
}

PROOF static int cmc_preservation_target_value_call_total_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_target_value_call_total_axioms_before,
      "cmc_preservation_target_value_call_total introduced an axiom");
  ENSURE_COND(vector_size(hyp(cm_target_v_call_step)) == 0,
      "call value target theorem is not closed");
  return 0;
err:
  return 1;
}
PROOF static int _cmc_preservation_target_value_call_total_checks =
    cmc_preservation_target_value_call_total_final_checks();
