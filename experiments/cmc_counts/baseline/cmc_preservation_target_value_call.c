#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_target_value_call.h"
#include "cmc_preservation_spill_semantic.h"
#include "cmc_preservation_spill_safety.h"
#include "cmc_preservation_invariant_frame.h"
#include "cmc_preservation_invariant_transition.h"
#include "cmc_preservation_target_spill_runtime.h"
#include "cmc_preservation_layout.h"
#include "cmc_preservation_code_expr.h"
#include "cmc_preservation_code_stmt.h"

#require "cmc_preservation_target_call_complete.c"
#require "cmc_preservation_target_value_args.c"
#require "cmc_preservation_code_value_call.c"
#require "cmc_preservation_invariant_transition.c"

PROOF static size_t _cmc_preservation_target_value_call_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_value_call_pc_offset(
    const term current_ann, const term prefix,
    const term next_ann, const thm_list rules) {
  term pc_equation =
      `cm_ann_pc ${next_ann:cm_annotation} ==
       cm_ann_pc ${current_ann:cm_annotation} +
         ilength ${prefix:(tvm_inst)list}`;
  thm pc_view = apply_conversion(
      reduce_rewrite_conv(rules), pc_equation);
  dest_iff_results pc_parts = dest_iff(concl(pc_view));
  thm pc_normal = int_ring_rule(pc_parts.tm2);
  return eq_mp_rule(sym_rule(pc_view), pc_normal);
}

PROOF static thm cm_value_call_code_suffix(
    const thm current_code, const term code,
    const term current_ann, const term prefix,
    const term suffix, const term next_ann,
    const thm_list rules) {
  thm suffix_rule = ispecl_rule(TERM_LIST(
      code, `cm_ann_pc ${current_ann:cm_annotation}`,
      prefix, suffix), get_cm_code_at_append_right());
  thm suffix_raw = mp_rule(suffix_rule, current_code);
  thm pc_equal = cm_value_call_pc_offset(
      current_ann, prefix, next_ann, rules);
  thm code_equal = beta_norm(ap_term_rule(
      `\next_pc:int.
         cm_code_at ${code:(tvm_inst)list} next_pc
           ${suffix:(tvm_inst)list}`,
      pc_equal));
  return eq_mp_rule(sym_rule(code_equal), suffix_raw);
}

PROOF static thm cm_value_call_shape_fact(
    const term wanted, const thm fact, const thm_list rules) {
  thm wanted_view = apply_conversion(
      reduce_rewrite_conv(rules), wanted);
  thm fact_normal = conv_rule(
      reduce_rewrite_conv(rules), fact);
  return eq_mp_rule(sym_rule(wanted_view), fact_normal);
}

PROOF static thm cm_prove_value_call_reverse_length(void) {
  gnode root = gnode_new_with_ccl(
      `!(values:(cm_value)list).
         ilength (REVERSE values) == ilength values`);
  gnode_list cases = INDUCT_TAC(root, `values:(cm_value)list`);
  {
    CONV_TAC(cases[0], reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("REVERSE"),
        get_theorem_by_name("ILENGTH_DEF"))));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm ih = assume_rule(goal_lasmps(leaf->g)[0].tm);
    gnode reduced = CONV_WITH_ASMP_TAC(
        leaf, reduce_rewrite_conv, THM_LIST(
          get_theorem_by_name("REVERSE"),
          get_theorem_by_name("ILENGTH_APPEND"),
          get_theorem_by_name("ILENGTH_DEF"), ih));
    if (IS_NULL(reduced->solved)) {
      ACCEPT_TAC(reduced, int_ring_rule(goal_ccl(reduced->g)));
    }
  }
  return gnode_prove(root);
}
PROOF static thm cm_value_call_reverse_length =
    cm_prove_value_call_reverse_length();

PROOF static thm cm_prove_value_call_code_steps_append(void) {
  gnode root = gnode_new_with_ccl(
      `!(left:(tvm_inst)list) (right:(tvm_inst)list).
         cm_code_steps (left ++ right) ==
         cm_code_steps left + cm_code_steps right`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm left_nonnegative = ispec_rule(
      `left:(tvm_inst)list`, get_theorem_by_name("ILENGTH_NONNEG"));
  thm right_nonnegative = ispec_rule(
      `right:(tvm_inst)list`, get_theorem_by_name("ILENGTH_NONNEG"));
  thm count_add = mp_rule(
      specl_rule(TERM_LIST(`ilength (left:(tvm_inst)list)`,
          `ilength (right:(tvm_inst)list)`),
          get_theorem_by_name("NUM_OF_INT_ADD")),
      conj_rule(left_nonnegative, right_nonnegative));
  CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
      cm_code_steps_def, get_theorem_by_name("ILENGTH_APPEND"),
      count_add)));
  return gnode_prove(root);
}
PROOF static thm cm_value_call_code_steps_append =
    cm_prove_value_call_code_steps_append();

PROOF static thm cm_prove_value_call_final_steps(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (caller:int) (callee:int)
         (all_args:(cm_expr)list) (base_slot:int)
         (current_slot:int).
         cm_code_steps
           (cm_arg_final_code p caller callee all_args
             base_slot current_slot) ==
         5 +
           (cm_code_steps
              (cm_emit_args_reload p caller base_slot all_args) +
            (1 + (6 + (6 + (2 +
              cm_code_steps
                (cm_emit_param_stores p callee 0i
                  (cm_function_params
                    (inth callee (cm_program_functions p)))))))))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm num_of_int_one = spec_rule(
      `1:num`, get_theorem_by_name("NUM_OF_INT_OF_NUM"));
  thm num_of_int_five = spec_rule(
      `5:num`, get_theorem_by_name("NUM_OF_INT_OF_NUM"));
  thm num_of_int_fourteen = spec_rule(
      `14:num`, get_theorem_by_name("NUM_OF_INT_OF_NUM"));
  gnode reduced = CONV_TAC(leaf, rewrite_conv(THM_LIST(
      cm_arg_final_code_def, cm_value_call_code_steps_append)));
  if (IS_NULL(reduced->solved)) {
    reduced = CONV_TAC(reduced, rewrite_conv(THM_LIST(
        get_cm_emit_prologue_def(), cm_value_call_code_steps_append)));
  }
  if (IS_NULL(reduced->solved)) {
    reduced = CONV_TAC(reduced, reduce_rewrite_conv(THM_LIST(
        cm_code_steps_def, get_cm_layout_temp_store_length(),
        get_theorem_by_name("APPEND"),
        get_theorem_by_name("ILENGTH_DEF"),
        num_of_int_one, num_of_int_five, num_of_int_fourteen)));
  }
  if (IS_NULL(reduced->solved)) {
    reduced = CONV_TAC(reduced, rewrite_conv(THM_LIST(
        num_of_int_one, num_of_int_five, num_of_int_fourteen)));
  }
  if (IS_NULL(reduced->solved)) {
    struct dest_eq_results sides = dest_eq(goal_ccl(reduced->g));
    thm left_normal = apply_conversion(
        get_conversion_by_name("NUM_NORMALIZE_CONV"), sides.tm1);
    thm right_normal = apply_conversion(
        get_conversion_by_name("NUM_NORMALIZE_CONV"), sides.tm2);
    ACCEPT_TAC(reduced, trans_rule(left_normal, sym_rule(right_normal)));
  }
  return gnode_prove(root);
}
PROOF static thm cm_value_call_final_steps =
    cm_prove_value_call_final_steps();

PROOF static thm cm_function_wf_for_value_call(
    const thm typed, const thm callee_bounds) {
  thm typed_open = conv_rule(rewrite_conv(THM_LIST(
      get_cm_typed_program_def())), typed);
  thm all_functions = mp_rule(taut_rule(mk_imp(
      concl(typed_open),
      `!index.
         0i <= index ==>
         index < ilength (cm_program_functions (p:cm_program)) ==>
         cm_function_wf p
           (inth index (cm_program_functions p))`)), typed_open);
  return match_mp_rule(match_mp_rule(
      spec_rule(`callee:int`, all_functions),
      conjunct1_rule(callee_bounds)),
      conjunct2_rule(callee_bounds));
}

PROOF static thm cm_prove_target_v_arg_nil_step(void) {
  term phase =
      `CAArgP (callee:int) [] (values:(cm_value)list) (ret:cm_type)
        (all_args:(cm_expr)list) (base_slot:int)
        (current_slot:int) (scratch:int)`;
  term task =
      `CMVTask (p:cm_program) (fid:int) (v:cm_value)
        (st:cm_src_state)
        (CMArgK (callee:int) [] (values:(cm_value)list)
          (ret:cm_type) ::
         cm_cursor_frames (rest:(cm_acursor)list))`;
  term ann =
      `CMAnnotation (pc:int) (temp:int) (breakpc:int) (continuepc:int)
        (CMACursor ${phase:cm_aphase} (owner:int)
          (saved_break:int) (saved_continue:int) ::
         (rest:(cm_acursor)list))
        (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
        (calls:(cm_call_sim_frame)list)`;
  term store_code =
      `cm_temp_store_code (p:cm_program) (fid:int) (current_slot:int)`;
  term reload_code =
      `cm_emit_args_reload (p:cm_program) (fid:int)
        (base_slot:int) (all_args:(cm_expr)list)`;
  term call_values =
      `REVERSE ((v:cm_value) :: (values:(cm_value)list))`;
  term stored_spills =
      `cm_spill_put (current_slot:int) (v:cm_value)
        (spills:(cm_spill)list)`;
  term stored_ann =
      `cm_ann_put_spill (current_slot:int) (v:cm_value)
        (cm_ann_linear ${store_code:(tvm_inst)list}
          ${ann:cm_annotation})`;
  term reload_ann =
      `cm_ann_linear ${reload_code:(tvm_inst)list}
        ${stored_ann:cm_annotation}`;
  term return_pc =
      `(pc:int) + ilength ${store_code:(tvm_inst)list} +
        ilength ${reload_code:(tvm_inst)list} + 1i`;
  term entered =
      `cm_ann_enter_call (p:cm_program) (fid:int) (callee:int)
        (st:cm_src_state) (ret:cm_type) ${return_pc:int}
        (owner:int) (saved_break:int) (saved_continue:int)
        (rest:(cm_acursor)list) ${stored_spills:(cm_spill)list}
        (saved:(cm_spill_frame)list)
        (calls:(cm_call_sim_frame)list)`;
  term frame_bytes =
      `cm_frame_size (cm_program_structs (p:cm_program))
        (inth (callee:int) (cm_program_functions p))`;
  term frame_base =
      `cm_state_fp (st:cm_src_state) - ${frame_bytes:int}`;
  term active =
      `cm_active_spill_frames (fid:int) (st:cm_src_state)
        ${reload_ann:cm_annotation}`;
  term pending =
      `cm_call_pending_base (p:cm_program) (callee:int)
        (st:cm_src_state)`;
  term body = imp_chain(TERM_LIST(
      `cm_task_layout (p:cm_program) ${task:cm_task}
        ${ann:cm_annotation}`,
      `cm_task_target_sim (p:cm_program) ${task:cm_task}
        (target:tvm_task) ${ann:cm_annotation}`,
      `cm_runtime_stack (p:cm_program)
        (cm_state_regions (st:cm_src_state)) (fid:int)
        (cm_state_fp st) (cm_state_regions st)
        (CMACursor ${phase:cm_aphase} (owner:int)
          (saved_break:int) (saved_continue:int) ::
         (rest:(cm_acursor)list))
        ${stored_spills:(cm_spill)list}
        (saved:(cm_spill_frame)list)
        (calls:(cm_call_sim_frame)list)`,
      `cm_phase_spill_consistent
        (cm_temp_slots
          (inth (fid:int) (cm_program_functions (p:cm_program))))
        (owner:int) ${phase:cm_aphase} (spills:(cm_spill)list)`,
      `cm_v_spill_ready (p:cm_program) (fid:int)
        ${ann:cm_annotation} ${phase:cm_aphase}`,
      `0i <= (fid:int)`,
      `cm_typed_program (p:cm_program)`,
      `cm_call_ok (p:cm_program) (callee:int)
        ${call_values:(cm_value)list} (st:cm_src_state)`,
      `cm_call_depth
        (cm_cursor_frames (rest:(cm_acursor)list)) < 65536i`,
      `tvm_target_valid (cm_model_code (p:cm_program))
        (cm_function_pc p (callee:int))`,
      `cm_regions_before (cm_state_regions (st:cm_src_state))
        (cm_state_nextgen st)`,
      `0i <= cm_state_nextgen (st:cm_src_state)`,
      `ilength (calls:(cm_call_sim_frame)list) < 65536i`,
      `ilength ${call_values:(cm_value)list} < 65534i`,
      `cm_state_tags_generation_below (st:cm_src_state)
        (cm_state_nextgen st)`,
      `cm_values_generation_below (cm_state_nextgen st)
        (REVERSE ${call_values:(cm_value)list})`,
      `cm_spill_frames_generation_below (cm_state_nextgen st)
        ${active:(cm_spill_frame)list}`,
      `cm_tagged_span_valid (st:cm_src_state)`,
      `!addr. cm_live_address (st:cm_src_state) addr ==>
        ~(${frame_base:int} <= addr && addr < ${frame_base:int} + 8i)`,
      `!addr. cm_live_address (st:cm_src_state) addr ==>
        ~(8i <= addr && addr < 8i + 8i)`,
      `cm_range_disjoint ${frame_base:int} 8i 8i 8i`,
      `cm_range_disjoint 8i 8i ${frame_base:int} 8i`,
      `cm_call_frames_store_safe CMIntTy ${frame_base:int}
        (cm_ann_calls ${reload_ann:cm_annotation})`,
      `cm_spill_frames_store_safe (p:cm_program) CMIntTy
        ${frame_base:int} ${active:(cm_spill_frame)list}`,
      `cm_call_frames_store_safe CMIntTy 8i
        (cm_ann_calls ${reload_ann:cm_annotation})`,
      `cm_spill_frames_store_safe (p:cm_program) CMIntTy 8i
        ${active:(cm_spill_frame)list}`,
      `tower_signed64 ${frame_bytes:int}`,
      `tower_signed64 ${frame_base:int}`,
      `tower_word_valid ${frame_base:int}`,
      `cm_runtime_memory_layout (p:cm_program)
        ${pending:cm_src_state}
        (cm_ann_calls ${entered:cm_annotation})
        (cm_active_spill_frames (callee:int) ${pending:cm_src_state}
          ${entered:cm_annotation})`),
      `cm_task_target_sim (p:cm_program)
        (cm_step ${task:cm_task})
        (tvm_iter
          (cm_update_steps
            (cm_annotation_step ${task:cm_task} ${ann:cm_annotation}))
          (target:tvm_task))
        (cm_update_annotation
          (cm_annotation_step ${task:cm_task} ${ann:cm_annotation}))`);
  gnode root = gnode_new_with_ccl(
      list_mk_forall(free_vars(body), body));
  gnode leaf = AUTO_INTROS_TAC(root);

  term phase_code =
      `cm_value_phase_code (p:cm_program) (fid:int) (pc:int)
        (temp:int) (owner:int) (breakpc:int) (continuepc:int)
        ${phase:cm_aphase}`;
  term continuation =
      `cm_cont_code (p:cm_program) (fid:int)
        ((pc:int) + ilength ${phase_code:(tvm_inst)list})
        (owner:int) (rest:(cm_acursor)list)`;
  term call_tail =
      `TVMInst TVMCallOp (cm_function_pc (p:cm_program) (callee:int)) ::
       ${continuation:(tvm_inst)list}`;
  term code_rest =
      `${reload_code:(tvm_inst)list} ++ ${call_tail:(tvm_inst)list}`;

  thm layout = assume_rule(
      `cm_task_layout (p:cm_program) ${task:cm_task}
        ${ann:cm_annotation}`);
  thm old_code = conjunct1_rule(conv_rule(
      rewrite_conv(THM_LIST(cm_task_layout_def)), layout));
  thm running = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_task_target_sim_def)), assume_rule(
        `cm_task_target_sim (p:cm_program) ${task:cm_task}
          (target:tvm_task) ${ann:cm_annotation}`));

  thm_list layout_rules = cm_v_layout_rules();
  thm_list ann_rules = THM_LIST(
      cm_ann_linear_def, cm_ann_plain_def,
      cm_ann_put_spill_def, cm_ann_spills_set_def,
      cm_ann_pc_def, cm_ann_temp_def, cm_ann_break_def,
      cm_ann_continue_def, cm_ann_cursors_def,
      cm_ann_spills_def, cm_ann_saved_def, cm_ann_calls_def,
      get_theorem_by_name("ILENGTH_DEF"));

  term address =
      `cm_state_fp (st:cm_src_state) +
        cm_temp_offset (p:cm_program) (fid:int) (current_slot:int)`;
  thm runtime_stack = assume_rule(
      `cm_runtime_stack (p:cm_program)
        (cm_state_regions (st:cm_src_state)) (fid:int)
        (cm_state_fp st) (cm_state_regions st)
        (CMACursor ${phase:cm_aphase} (owner:int)
          (saved_break:int) (saved_continue:int) ::
         (rest:(cm_acursor)list))
        ${stored_spills:(cm_spill)list}
        (saved:(cm_spill_frame)list)
        (calls:(cm_call_sim_frame)list)`);
  thm address_facts = specl_rule(TERM_LIST(
      `p:cm_program`, `cm_state_regions (st:cm_src_state)`,
      `CMACursor ${phase:cm_aphase} (owner:int)
        (saved_break:int) (saved_continue:int) ::
       (rest:(cm_acursor)list)`,
      `fid:int`, `cm_state_fp (st:cm_src_state)`,
      `cm_state_regions (st:cm_src_state)`,
      `spills:(cm_spill)list`, `saved:(cm_spill_frame)list`,
      `calls:(cm_call_sim_frame)list`, `current_slot:int`,
      `v:cm_value`, address), get_cm_runtime_spill_address_safe());
  address_facts = match_mp_rule(address_facts, runtime_stack);
  address_facts = match_mp_rule(address_facts,
      assume_rule(`0i <= (fid:int)`));
  address_facts = match_mp_rule(address_facts,
      refl_rule(address));
  thm fp_signed = conjunct1_rule(address_facts);
  thm offset_signed = conjunct1_rule(conjunct2_rule(address_facts));
  thm address_signed = conjunct1_rule(
      conjunct2_rule(conjunct2_rule(address_facts)));
  thm address_valid = conjunct2_rule(
      conjunct2_rule(conjunct2_rule(address_facts)));

  thm stored_result = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`,
      `current_slot:int`, `v:cm_value`, `[]:(cm_value)list`,
      ann, `target:tvm_task`, code_rest, address),
      get_cm_target_temp_store_runtime());
  term wanted_store_code = dest_imp(concl(stored_result)).tm1;
  thm wanted_store_view = apply_conversion(
      reduce_rewrite_conv(layout_rules), wanted_store_code);
  thm old_code_normal = conv_rule(
      reduce_rewrite_conv(layout_rules), old_code);
  thm store_code_at = eq_mp_rule(
      sym_rule(wanted_store_view), old_code_normal);
  stored_result = match_mp_rule(stored_result, store_code_at);
  stored_result = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_ann_cursors_def, cm_ann_spills_def,
      cm_ann_saved_def, cm_ann_calls_def)), stored_result);
  stored_result = match_mp_rule(stored_result, running);
  stored_result = match_mp_rule(stored_result, runtime_stack);
  stored_result = match_mp_rule(stored_result,
      assume_rule(`0i <= (fid:int)`));
  stored_result = match_mp_rule(stored_result,
      eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          get_theorem_by_name("ILENGTH_DEF"))),
        `ilength ([]:(cm_value)list) < 65534i`)));
  stored_result = match_mp_rule(stored_result,
      assume_rule(`cm_tagged_span_valid (st:cm_src_state)`));
  stored_result = match_mp_rule(stored_result, fp_signed);
  stored_result = match_mp_rule(stored_result, offset_signed);
  stored_result = match_mp_rule(stored_result, address_signed);
  stored_result = match_mp_rule(stored_result, address_valid);

  thm consistency = conv_rule(rewrite_conv(THM_LIST(
      cm_phase_spill_consistent_def)), assume_rule(
        `cm_phase_spill_consistent
          (cm_temp_slots
            (inth (fid:int) (cm_program_functions (p:cm_program))))
          (owner:int) ${phase:cm_aphase} (spills:(cm_spill)list)`));
  thm consistency_tail = conjunct2_rule(consistency);
  thm base_equal = conjunct1_rule(consistency_tail);
  thm after_base = conjunct2_rule(consistency_tail);
  thm current_equal = conjunct1_rule(after_base);
  thm after_current = conjunct2_rule(after_base);
  thm after_scratch = conjunct2_rule(after_current);
  thm length_equal = conjunct1_rule(after_scratch);
  thm after_length = conjunct2_rule(after_scratch);
  thm staged = conjunct2_rule(after_length);

  thm spill_ready = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_v_spill_ready_def)), assume_rule(
        `cm_v_spill_ready (p:cm_program) (fid:int)
          ${ann:cm_annotation} ${phase:cm_aphase}`));
  thm base_nonnegative = conjunct1_rule(spill_ready);
  thm current_nonnegative =
      conjunct1_rule(conjunct2_rule(spill_ready));
  thm current_upper_raw =
      conjunct2_rule(conjunct2_rule(spill_ready));
  thm current_upper = conv_rule(rewrite_conv(THM_LIST(
      get_cm_temp_slots_def())), current_upper_raw);

  thm old_staged_after = match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(`base_slot:int`, `values:(cm_value)list`,
        `spills:(cm_spill)list`, `current_slot:int`, `v:cm_value`),
        cm_staged_spills_put_above), staged),
      mp_rule(int_arith_rule(
        `(current_slot:int) == (base_slot:int) +
             ilength (values:(cm_value)list) ==>
         base_slot + ilength values <= current_slot`), current_equal));
  thm new_spill_holds = specl_rule(TERM_LIST(
      `current_slot:int`, `v:cm_value`, `spills:(cm_spill)list`),
      cm_spill_holds_put_same);
  thm held_slot_equal = beta_norm(ap_term_rule(
      `\slot:int.
        cm_spill_holds slot (v:cm_value) ${stored_spills:(cm_spill)list}`,
      current_equal));
  new_spill_holds = eq_mp_rule(held_slot_equal, new_spill_holds);
  term staged_with_value_term =
      `cm_staged_spills (base_slot:int)
        ((v:cm_value) :: (values:(cm_value)list))
        ${stored_spills:(cm_spill)list}`;
  thm staged_with_value_view = apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        cm_staged_spills_def, get_theorem_by_name("ILENGTH_DEF"))),
      staged_with_value_term);
  thm staged_with_value = eq_mp_rule(sym_rule(staged_with_value_view),
      conj_rule(new_spill_holds, old_staged_after));
  thm forward_view = specl_rule(TERM_LIST(
      call_values, `base_slot:int`, stored_spills),
      get_cm_staged_reverse_spills());
  forward_view = conv_rule(rewrite_conv(THM_LIST(
      get_theorem_by_name("REVERSE_REVERSE"))), forward_view);
  thm forward_spills = eq_mp_rule(forward_view, staged_with_value);

  thm reverse_length = spec_rule(
      `(v:cm_value) :: (values:(cm_value)list)`,
      cm_value_call_reverse_length);
  thm call_length = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_theorem_by_name("ILENGTH_DEF"))), reverse_length);
  thm args_call_length = mp_rule(mp_rule(int_arith_rule(
      `ilength (all_args:(cm_expr)list) ==
           ilength (values:(cm_value)list) + 1i ==>
       ilength ${call_values:(cm_value)list} ==
           1i + ilength values ==>
       ilength all_args == ilength ${call_values:(cm_value)list}`),
      conv_rule(reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF"))), length_equal)),
      call_length);
  thm reload_bound = mp_rule(mp_rule(mp_rule(int_arith_rule(
      `(current_slot:int) == (base_slot:int) +
           ilength (values:(cm_value)list) ==>
       current_slot < cm_stemps
         (cm_function_body
           (inth (fid:int) (cm_program_functions (p:cm_program)))) ==>
       ilength ${call_values:(cm_value)list} ==
           1i + ilength values ==>
       base_slot + ilength ${call_values:(cm_value)list} <=
         cm_stemps (cm_function_body
           (inth fid (cm_program_functions p)))`),
      current_equal), current_upper), call_length);
  thm reload_capacity = mp_rule(int_arith_rule(
      `ilength ${call_values:(cm_value)list} < 65534i ==>
       ilength ${call_values:(cm_value)list} + 0i < 65536i`),
      assume_rule(
        `ilength ${call_values:(cm_value)list} < 65534i`));

  thm stored_code_at = cm_value_call_code_suffix(
      store_code_at, `cm_model_code (p:cm_program)`, ann,
      store_code, code_rest, stored_ann, ann_rules);
  thm reload_result = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`,
      `all_args:(cm_expr)list`, call_values,
      `[]:(cm_value)list`, `base_slot:int`, stored_ann,
      `tvm_iter 5 (target:tvm_task)`, call_tail),
      get_cm_target_args_reload());
  reload_result = match_mp_rule(reload_result, stored_code_at);
  reload_result = match_mp_rule(reload_result, stored_result);
  reload_result = match_mp_rule(reload_result,
      cm_value_call_shape_fact(dest_imp(concl(reload_result)).tm1,
        forward_spills, ann_rules));
  reload_result = match_mp_rule(reload_result, args_call_length);
  reload_result = match_mp_rule(reload_result,
      cm_value_call_shape_fact(dest_imp(concl(reload_result)).tm1,
        runtime_stack, ann_rules));
  reload_result = match_mp_rule(reload_result,
      assume_rule(`0i <= (fid:int)`));
  reload_result = match_mp_rule(reload_result, base_nonnegative);
  reload_result = match_mp_rule(reload_result, reload_bound);
  reload_result = match_mp_rule(reload_result,
      cm_value_call_shape_fact(dest_imp(concl(reload_result)).tm1,
        reload_capacity, ann_rules));
  reload_result = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_theorem_by_name("APPEND_NIL"))), reload_result);

  thm call_code_at = cm_value_call_code_suffix(
      stored_code_at, `cm_model_code (p:cm_program)`, stored_ann,
      reload_code, call_tail, reload_ann, ann_rules);
  thm call_ok_open = conv_rule(rewrite_conv(THM_LIST(
      get_cm_call_ok_def())), assume_rule(
        `cm_call_ok (p:cm_program) (callee:int)
          ${call_values:(cm_value)list} (st:cm_src_state)`));
  thm callee_bounds = conj_rule(conjunct1_rule(call_ok_open),
      conjunct1_rule(conjunct2_rule(call_ok_open)));
  thm function_wf = cm_function_wf_for_value_call(
      assume_rule(`cm_typed_program (p:cm_program)`), callee_bounds);
  thm frame_segment = match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(`p:cm_program`, `callee:int`,
        call_values, `st:cm_src_state`), cm_call_frame_segment),
      assume_rule(`cm_typed_program (p:cm_program)`)),
      assume_rule(
        `cm_call_ok (p:cm_program) (callee:int)
          ${call_values:(cm_value)list} (st:cm_src_state)`));
  thm call_arity = mp_rule(taut_rule(mk_imp(concl(call_ok_open),
      `ilength ${call_values:(cm_value)list} ==
       ilength (cm_function_params
         (inth (callee:int) (cm_program_functions (p:cm_program))))`)),
      call_ok_open);

  thm stored_pc = cm_value_call_pc_offset(
      ann, store_code, stored_ann, ann_rules);
  thm reload_pc = cm_value_call_pc_offset(
      stored_ann, reload_code, reload_ann, ann_rules);
  thm initial_pc = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(ann_rules),
      `cm_ann_pc ${ann:cm_annotation} == (pc:int)`));
  thm reload_return_pc = int_arith_rule(imp_chain(TERM_LIST(
      concl(stored_pc), concl(reload_pc), concl(initial_pc)),
      `cm_ann_pc ${reload_ann:cm_annotation} + 1i == ${return_pc:int}`));
  reload_return_pc = match_mp_rule(match_mp_rule(
      match_mp_rule(reload_return_pc, stored_pc), reload_pc), initial_pc);
  thm entered_pc = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        cm_ann_enter_call_def, cm_ann_pc_def)),
      `cm_ann_pc ${entered:cm_annotation} ==
       cm_call_body_pc (p:cm_program) (callee:int)`));
  thm entered_calls = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        cm_ann_enter_call_def, cm_ann_calls_def,
        cm_ann_linear_def, cm_ann_plain_def,
        cm_ann_put_spill_def, cm_ann_spills_set_def,
        reload_return_pc)),
      `cm_ann_calls ${entered:cm_annotation} ==
       CMCallSimFrame ${frame_base:int}
         (cm_state_fp (st:cm_src_state))
         (cm_ann_pc ${reload_ann:cm_annotation} + 1i) ::
       cm_ann_calls ${reload_ann:cm_annotation}`));
  thm pending_structure = specl_rule(TERM_LIST(
      `p:cm_program`, `callee:int`, `st:cm_src_state`),
      get_cm_call_pending_structure());
  thm pending_fp = conjunct1_rule(pending_structure);
  thm entered_active = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        cm_active_spill_frames_def, cm_ann_enter_call_def,
        cm_ann_spills_def, cm_ann_saved_def,
        cm_ann_linear_def, cm_ann_plain_def,
        cm_ann_put_spill_def, cm_ann_spills_set_def,
        pending_fp)),
      `cm_active_spill_frames (callee:int) ${pending:cm_src_state}
          ${entered:cm_annotation} ==
       CMSpillFrame (callee:int) ${frame_base:int} [] ::
         ${active:(cm_spill_frame)list}`));

  thm call_result = specl_rule(TERM_LIST(
      continuation, `fid:int`, reload_ann, call_values,
      `st:cm_src_state`, entered, `callee:int`, `p:cm_program`,
      `tvm_iter
        (cm_code_steps ${reload_code:(tvm_inst)list})
        (tvm_iter 5 (target:tvm_task))`),
      get_cm_target_call_complete());
  call_result = match_mp_rule(call_result, call_code_at);
  call_result = match_mp_rule(call_result, reload_result);
  call_result = match_mp_rule(call_result, callee_bounds);
  call_result = match_mp_rule(call_result, assume_rule(
      `tvm_target_valid (cm_model_code (p:cm_program))
        (cm_function_pc p (callee:int))`));
  call_result = match_mp_rule(call_result, function_wf);
  call_result = match_mp_rule(call_result, frame_segment);
  call_result = match_mp_rule(call_result, assume_rule(
      `cm_regions_before (cm_state_regions (st:cm_src_state))
        (cm_state_nextgen st)`));
  call_result = match_mp_rule(call_result, assume_rule(
      `0i <= cm_state_nextgen (st:cm_src_state)`));
  call_result = match_mp_rule(call_result,
      cm_value_call_shape_fact(dest_imp(concl(call_result)).tm1,
        assume_rule(`ilength (calls:(cm_call_sim_frame)list) < 65536i`),
        ann_rules));
  call_result = match_mp_rule(call_result, assume_rule(
      `ilength ${call_values:(cm_value)list} < 65534i`));
  call_result = match_mp_rule(call_result, assume_rule(
      `cm_state_tags_generation_below (st:cm_src_state)
        (cm_state_nextgen st)`));
  call_result = match_mp_rule(call_result, assume_rule(
      `cm_values_generation_below (cm_state_nextgen st)
        (REVERSE ${call_values:(cm_value)list})`));
  call_result = match_mp_rule(call_result, assume_rule(
      `cm_spill_frames_generation_below (cm_state_nextgen st)
        ${active:(cm_spill_frame)list}`));
  call_result = match_mp_rule(call_result, assume_rule(
      `cm_tagged_span_valid (st:cm_src_state)`));
  call_result = match_mp_rule(call_result, assume_rule(
      `!addr. cm_live_address (st:cm_src_state) addr ==>
        ~(${frame_base:int} <= addr && addr < ${frame_base:int} + 8i)`));
  call_result = match_mp_rule(call_result, assume_rule(
      `!addr. cm_live_address (st:cm_src_state) addr ==>
        ~(8i <= addr && addr < 8i + 8i)`));
  call_result = match_mp_rule(call_result, assume_rule(
      `cm_range_disjoint ${frame_base:int} 8i 8i 8i`));
  call_result = match_mp_rule(call_result, assume_rule(
      `cm_range_disjoint 8i 8i ${frame_base:int} 8i`));
  call_result = match_mp_rule(call_result, assume_rule(
      `cm_call_frames_store_safe CMIntTy ${frame_base:int}
        (cm_ann_calls ${reload_ann:cm_annotation})`));
  call_result = match_mp_rule(call_result, assume_rule(
      `cm_spill_frames_store_safe (p:cm_program) CMIntTy
        ${frame_base:int} ${active:(cm_spill_frame)list}`));
  call_result = match_mp_rule(call_result, assume_rule(
      `cm_call_frames_store_safe CMIntTy 8i
        (cm_ann_calls ${reload_ann:cm_annotation})`));
  call_result = match_mp_rule(call_result, assume_rule(
      `cm_spill_frames_store_safe (p:cm_program) CMIntTy 8i
        ${active:(cm_spill_frame)list}`));
  call_result = match_mp_rule(call_result, fp_signed);
  call_result = match_mp_rule(call_result,
      assume_rule(`tower_signed64 ${frame_bytes:int}`));
  call_result = match_mp_rule(call_result,
      assume_rule(`tower_signed64 ${frame_base:int}`));
  call_result = match_mp_rule(call_result,
      assume_rule(`tower_word_valid ${frame_base:int}`));
  call_result = match_mp_rule(call_result, assume_rule(
      `cm_runtime_memory_layout (p:cm_program)
        ${pending:cm_src_state}
        (cm_ann_calls ${entered:cm_annotation})
        (cm_active_spill_frames (callee:int) ${pending:cm_src_state}
          ${entered:cm_annotation})`));
  call_result = match_mp_rule(call_result, entered_pc);
  call_result = match_mp_rule(call_result, entered_calls);
  call_result = match_mp_rule(call_result, entered_active);
  call_result = match_mp_rule(call_result, call_arity);

  thm final_steps = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `callee:int`,
      `all_args:(cm_expr)list`, `base_slot:int`, `current_slot:int`),
      cm_value_call_final_steps);
  thm_list iteration_rules = THM_LIST(
      gsym_rule(get_cm_tvm_iter_add()),
      get_theorem_by_name("ADD_ASSOC"),
      gsym_rule(final_steps));
  call_result = conv_rule(reduce_rewrite_conv(iteration_rules),
      call_result);

  thm_list finish_rules = cm_v_layout_rules();
  vector_add(&finish_rules, cm_task_target_sim_def);
  vector_add(&finish_rules, cm_running_target_sim_def);
  vector_add(&finish_rules, cm_active_spill_frames_def);
  vector_add(&finish_rules, get_cm_begin_call_def());
  vector_add(&finish_rules, cm_update_steps_def);
  vector_add(&finish_rules, cm_update_annotation_def);
  vector_add(&finish_rules, cm_ann_enter_call_def);
  vector_add(&finish_rules, cm_arg_final_code_def);
  vector_add(&finish_rules, get_theorem_by_name("REVERSE_REVERSE"));
  vector_add(&finish_rules, get_theorem_by_name("ILENGTH_DEF"));
  vector_add(&finish_rules, assume_rule(
      `cm_call_ok (p:cm_program) (callee:int)
        ${call_values:(cm_value)list} (st:cm_src_state)`));
  vector_add(&finish_rules, assume_rule(
      `cm_call_depth
        (cm_cursor_frames (rest:(cm_acursor)list)) < 65536i`));
  gnode reduced = CONV_TAC(leaf, reduce_rewrite_conv(finish_rules));
  reduced = CONV_TAC(reduced, reduce_rewrite_conv(finish_rules));
  thm normalized = conv_rule(
      reduce_rewrite_conv(finish_rules), call_result);
  normalized = conv_rule(
      reduce_rewrite_conv(finish_rules), normalized);
  ACCEPT_TAC(reduced, normalized);
  return gnode_prove(root);
}

PROOF thm cm_target_v_arg_nil_step =
    cm_prove_target_v_arg_nil_step();

PROOF thm get_cm_target_v_arg_nil_step(void) {
  return cm_target_v_arg_nil_step;
}

PROOF static int cmc_preservation_target_value_call_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_target_value_call_axioms_before,
      "cmc_preservation_target_value_call introduced an axiom");
  ENSURE_COND(vector_size(hyp(cm_target_v_arg_nil_step)) == 0,
      "cm_target_v_arg_nil_step has hypotheses");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_target_value_call_checks =
    cmc_preservation_target_value_call_final_checks();
