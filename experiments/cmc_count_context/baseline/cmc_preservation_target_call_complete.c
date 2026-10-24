#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_target_call_complete.h"
#include "cmc_preservation_layout.h"

#require "cmc_preservation_call_params_complete.c"
#require "cmc_preservation_target_call_pending.c"
#require "cmc_preservation_target_call_params.c"

PROOF extern thm cm_call_env_def;
PROOF extern thm cm_param_stores_length;
PROOF extern thm cm_state_make_def;
PROOF extern thm cm_state_env_def;

PROOF static size_t _cmc_preservation_target_call_complete_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_call_complete_pc_offset(
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

PROOF static thm cm_call_complete_code_suffix(
    const thm current_code, const term code,
    const term current_ann, const term prefix,
    const term suffix, const term next_ann,
    const thm_list rules) {
  thm tail_rule = ispecl_rule(TERM_LIST(
      code, `cm_ann_pc ${current_ann:cm_annotation}`,
      prefix, suffix), get_cm_code_at_append_right());
  thm tail_raw = mp_rule(tail_rule, current_code);
  thm pc_equal = cm_call_complete_pc_offset(
      current_ann, prefix, next_ann, rules);
  thm code_equal = beta_norm(ap_term_rule(
      `\next_pc:int.
         cm_code_at ${code:(tvm_inst)list} next_pc
           ${suffix:(tvm_inst)list}`,
      pc_equal));
  return eq_mp_rule(sym_rule(code_equal), tail_raw);
}

PROOF static thm cm_call_complete_shape_fact(
    const term wanted, const thm fact, const thm_list rules) {
  thm wanted_view =
      apply_conversion(reduce_rewrite_conv(rules), wanted);
  thm fact_normal =
      conv_rule(reduce_rewrite_conv(rules), fact);
  return eq_mp_rule(sym_rule(wanted_view), fact_normal);
}

PROOF static thm cm_prove_call_complete_reverse_length(void) {
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
PROOF static thm cm_call_complete_reverse_length =
    cm_prove_call_complete_reverse_length();


PROOF static thm cm_prove_target_call_complete(void) {
  term frame_bytes =
      `cm_frame_size (cm_program_structs (p:cm_program))
        (inth (callee:int) (cm_program_functions p))`;
  term frame_base =
      `cm_state_fp (st:cm_src_state) - ${frame_bytes:int}`;
  term params =
      `cm_function_params
        (inth (callee:int) (cm_program_functions (p:cm_program)))`;
  term call_pc = `cm_function_pc (p:cm_program) (callee:int)`;
  term return_pc = `(cm_ann_pc (ann:cm_annotation)) + 1i`;
  term active =
      `cm_active_spill_frames (caller:int) (st:cm_src_state)
        (ann:cm_annotation)`;
  term pending =
      `cm_call_pending_base (p:cm_program) (callee:int)
        (st:cm_src_state)`;
  term entered = `entered:cm_annotation`;
  term body = imp_chain(TERM_LIST(
      `cm_code_at (cm_model_code (p:cm_program))
        (cm_ann_pc (ann:cm_annotation))
        (TVMInst TVMCallOp ${call_pc:int} ::
          (call_rest:(tvm_inst)list))`,
      `cm_running_target_sim (p:cm_program) (caller:int)
        (st:cm_src_state) (REVERSE (values:(cm_value)list))
        (ann:cm_annotation) (target:tvm_task)`,
      `0i <= (callee:int) &&
       callee < ilength (cm_program_functions (p:cm_program))`,
      `tvm_target_valid (cm_model_code (p:cm_program))
        ${call_pc:int}`,
      `cm_function_wf (p:cm_program)
        (inth (callee:int) (cm_program_functions p))`,
      `cm_frame_segment (p:cm_program) (callee:int)
        ${frame_base:int} (cm_state_fp (st:cm_src_state))`,
      `cm_regions_before (cm_state_regions (st:cm_src_state))
        (cm_state_nextgen st)`,
      `0i <= cm_state_nextgen (st:cm_src_state)`,
      `ilength (cm_ann_calls (ann:cm_annotation)) < 65536i`,
      `ilength (values:(cm_value)list) < 65534i`,
      `cm_state_tags_generation_below (st:cm_src_state)
        (cm_state_nextgen st)`,
      `cm_values_generation_below (cm_state_nextgen st)
        (REVERSE (values:(cm_value)list))`,
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
        (cm_ann_calls (ann:cm_annotation))`,
      `cm_spill_frames_store_safe (p:cm_program) CMIntTy
        ${frame_base:int} ${active:(cm_spill_frame)list}`,
      `cm_call_frames_store_safe CMIntTy 8i
        (cm_ann_calls (ann:cm_annotation))`,
      `cm_spill_frames_store_safe (p:cm_program) CMIntTy 8i
        ${active:(cm_spill_frame)list}`,
      `tower_signed64 (cm_state_fp (st:cm_src_state))`,
      `tower_signed64 ${frame_bytes:int}`,
      `tower_signed64 ${frame_base:int}`,
      `tower_word_valid ${frame_base:int}`,
      `cm_runtime_memory_layout (p:cm_program) ${pending:cm_src_state}
        (cm_ann_calls ${entered:cm_annotation})
        (cm_active_spill_frames (callee:int) ${pending:cm_src_state}
          ${entered:cm_annotation})`,
      `cm_ann_pc ${entered:cm_annotation} ==
        cm_call_body_pc (p:cm_program) (callee:int)`,
      `cm_ann_calls ${entered:cm_annotation} ==
        CMCallSimFrame ${frame_base:int}
          (cm_state_fp (st:cm_src_state)) ${return_pc:int} ::
          cm_ann_calls (ann:cm_annotation)`,
      `cm_active_spill_frames (callee:int) ${pending:cm_src_state}
          ${entered:cm_annotation} ==
        CMSpillFrame (callee:int) ${frame_base:int} [] ::
          ${active:(cm_spill_frame)list}`,
      `ilength (values:(cm_value)list) == ilength ${params:(cm_slot_d)list}`),
      `cm_running_target_sim (p:cm_program) (callee:int)
        (cm_enter_call p callee (values:(cm_value)list)
          (st:cm_src_state)) [] ${entered:cm_annotation}
        (tvm_iter (cm_code_steps
          (cm_emit_param_stores p callee 0i ${params:(cm_slot_d)list}))
          (tvm_iter 2 (tvm_iter 6 (tvm_iter 6
            (tvm_iter 1 (target:tvm_task))))))`);
  gnode root = gnode_new_with_ccl(
      list_mk_forall(free_vars(body), body));
  gnode leaf = AUTO_INTROS_TAC(root);

  term frame_code = `cm_call_frame_save_code ${frame_bytes:int}`;
  term fp_code = `cm_call_fp_prepare_code ${frame_bytes:int}`;
  term pending_code =
      `[TVMInst TVMStoreOp 0i; TVMInst TVMPopOp 0i]:(tvm_inst)list`;
  term param_code =
      `cm_emit_param_stores (p:cm_program) (callee:int) 0i
        ${params:(cm_slot_d)list}`;
  term function_tail =
      `cm_emit_stmt (p:cm_program) (callee:int)
         (cm_function_pc p callee +
          cm_function_prologue_count
            (inth callee (cm_program_functions p)))
         0i 0i 0i
         (cm_function_body
           (inth callee (cm_program_functions p))) ++
       [TVMInst TVMPushOp 0i] ++ cm_return_epilogue`;
  term after_frame =
      `${fp_code:(tvm_inst)list} ++
       ${pending_code:(tvm_inst)list} ++
       ${param_code:(tvm_inst)list} ++
       ${function_tail:(tvm_inst)list}`;
  term after_fp =
      `${pending_code:(tvm_inst)list} ++
       ${param_code:(tvm_inst)list} ++
       ${function_tail:(tvm_inst)list}`;
  term after_pending =
      `${param_code:(tvm_inst)list} ++
       ${function_tail:(tvm_inst)list}`;

  term ann1 =
      `cm_ann_call_jump ${call_pc:int}
        (cm_state_fp (st:cm_src_state)) ${return_pc:int}
        (ann:cm_annotation)`;
  term ann2 =
      `cm_ann_after_call_frame_save ${frame_bytes:int}
        ${frame_base:int} ${ann1:cm_annotation}`;
  term ann3 =
      `cm_ann_after_call_fp_prepare ${frame_bytes:int}
        ${ann2:cm_annotation}`;
  term param_ann =
      `cm_ann_plain
        (cm_ann_pc ${ann3:cm_annotation} + 2i)
        0i 0i 0i ${entered:cm_annotation}`;
  term target1 = `tvm_iter 1 (target:tvm_task)`;
  term target2 = `tvm_iter 6 ${target1:tvm_task}`;
  term target3 = `tvm_iter 6 ${target2:tvm_task}`;
  term target4 = `tvm_iter 2 ${target3:tvm_task}`;

  thm bounds = assume_rule(
      `0i <= (callee:int) &&
       callee < ilength (cm_program_functions (p:cm_program))`);
  thm function_at = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `callee:int`), cm_model_function_at), bounds);
  thm_list code_rules = THM_LIST(
      get_cm_emit_function_def(), get_cm_emit_prologue_def(),
      cm_call_frame_save_code_def, cm_call_fp_prepare_code_def,
      get_cm_push_code_def(), get_theorem_by_name("APPEND"),
      get_theorem_by_name("APPEND_ASSOC"),
      get_theorem_by_name("ILENGTH_DEF"),
      cm_ann_call_jump_def, cm_ann_after_call_frame_save_def,
      cm_ann_after_call_fp_prepare_def, cm_ann_call_rebase_def,
      cm_rebase_call_frames_def, cm_ann_linear_def,
      cm_ann_plain_def, cm_ann_pc_def, cm_ann_temp_def,
      cm_ann_break_def, cm_ann_continue_def, cm_ann_cursors_def,
      cm_ann_spills_def, cm_ann_saved_def, cm_ann_calls_def,
      cm_active_spill_frames_def, cm_spill_frame_fp_def);
  thm_list frame_pc_rules = THM_LIST(
      cm_call_frame_save_code_def,
      cm_ann_after_call_frame_save_def, cm_ann_call_rebase_def,
      cm_ann_linear_def, cm_ann_plain_def, cm_ann_pc_def,
      get_cm_push_code_def(), get_theorem_by_name("ILENGTH_DEF"));
  thm_list fp_pc_rules = THM_LIST(
      cm_call_fp_prepare_code_def,
      cm_ann_after_call_fp_prepare_def, cm_ann_linear_def,
      cm_ann_plain_def, cm_ann_pc_def, get_cm_push_code_def(),
      get_theorem_by_name("ILENGTH_DEF"));
  thm_list pending_pc_rules = THM_LIST(
      cm_ann_linear_def, cm_ann_plain_def, cm_ann_pc_def,
      get_theorem_by_name("ILENGTH_DEF"));


  thm function_normal =
      conv_rule(reduce_rewrite_conv(code_rules), function_at);
  term wanted_function =
      `cm_code_at (cm_model_code (p:cm_program)) ${call_pc:int}
        (${frame_code:(tvm_inst)list} ++
         ${after_frame:(tvm_inst)list})`;
  thm function_view =
      apply_conversion(reduce_rewrite_conv(code_rules), wanted_function);
  thm frame_code_at =
      eq_mp_rule(sym_rule(function_view), function_normal);
  thm ann1_code_view = apply_conversion(
      reduce_rewrite_conv(code_rules),
      `cm_code_at (cm_model_code (p:cm_program))
        (cm_ann_pc ${ann1:cm_annotation})
        (${frame_code:(tvm_inst)list} ++
         ${after_frame:(tvm_inst)list})`);
  frame_code_at = eq_mp_rule(sym_rule(ann1_code_view),
      conv_rule(reduce_rewrite_conv(code_rules), frame_code_at));

  thm jump_result = specl_rule(TERM_LIST(
      `p:cm_program`, `caller:int`, `st:cm_src_state`,
      `REVERSE (values:(cm_value)list)`, `ann:cm_annotation`,
      `target:tvm_task`, call_pc,
      `call_rest:(tvm_inst)list`), cm_target_call_jump);
  jump_result = match_mp_rule(jump_result, assume_rule(
      `cm_code_at (cm_model_code (p:cm_program))
        (cm_ann_pc (ann:cm_annotation))
        (TVMInst TVMCallOp ${call_pc:int} ::
          (call_rest:(tvm_inst)list))`));
  jump_result = match_mp_rule(jump_result, assume_rule(
      `tvm_target_valid (cm_model_code (p:cm_program))
        ${call_pc:int}`));
  jump_result = match_mp_rule(jump_result, assume_rule(
      `ilength (cm_ann_calls (ann:cm_annotation)) < 65536i`));
  jump_result = match_mp_rule(jump_result, assume_rule(
      `cm_running_target_sim (p:cm_program) (caller:int)
        (st:cm_src_state) (REVERSE (values:(cm_value)list))
        (ann:cm_annotation) (target:tvm_task)`));

  thm frame_result = specl_rule(TERM_LIST(
      `p:cm_program`, `caller:int`, `st:cm_src_state`,
      frame_bytes, frame_base,
      `REVERSE (values:(cm_value)list)`, ann1, target1,
      after_frame), cm_target_call_frame_save);
  frame_result = match_mp_rule(frame_result, frame_code_at);
  frame_result = match_mp_rule(frame_result, jump_result);
  thm reverse_length = spec_rule(
      `values:(cm_value)list`, cm_call_complete_reverse_length);
  thm capacity_view = beta_norm(ap_term_rule(
      `\n:int. n < 65534i`, reverse_length));
  thm value_capacity = eq_mp_rule(sym_rule(capacity_view),
      assume_rule(`ilength (values:(cm_value)list) < 65534i`));
  frame_result = match_mp_rule(frame_result, value_capacity);
  thm_list frame_rules = (thm_list)vector_copy(code_rules);
  vector_add(&frame_rules, get_theorem_by_name("NOT_CONS_NIL"));
  vector_add(&frame_rules, get_theorem_by_name("HD"));
  vector_add(&frame_rules, get_theorem_by_name("TL"));
  vector_add(&frame_rules, cm_call_sim_base_def);
  vector_add(&frame_rules, cm_call_sim_saved_def);
  for (size_t premise = 0; premise < 3; ++premise) {
    frame_result = match_mp_rule(frame_result,
        eqt_elim_rule(apply_conversion(
          reduce_rewrite_conv(frame_rules),
          dest_imp(concl(frame_result)).tm1)));
  }
  frame_result = match_mp_rule(frame_result,
      assume_rule(`cm_tagged_span_valid (st:cm_src_state)`));
  frame_result = match_mp_rule(frame_result, assume_rule(
      `!addr. cm_live_address (st:cm_src_state) addr ==>
        ~(${frame_base:int} <= addr && addr < ${frame_base:int} + 8i)`));
  frame_result = match_mp_rule(frame_result, assume_rule(
      `cm_range_disjoint ${frame_base:int} 8i 8i 8i`));
  frame_result = match_mp_rule(frame_result,
      cm_call_complete_shape_fact(
        dest_imp(concl(frame_result)).tm1,
        assume_rule(
          `cm_call_frames_store_safe CMIntTy ${frame_base:int}
            (cm_ann_calls (ann:cm_annotation))`),
        frame_rules));
  frame_result = match_mp_rule(frame_result,
      cm_call_complete_shape_fact(
        dest_imp(concl(frame_result)).tm1,
        assume_rule(
          `cm_spill_frames_store_safe (p:cm_program) CMIntTy
            ${frame_base:int} ${active:(cm_spill_frame)list}`),
        frame_rules));
  frame_result = match_mp_rule(frame_result, assume_rule(
      `tower_signed64 (cm_state_fp (st:cm_src_state))`));
  frame_result = match_mp_rule(frame_result, assume_rule(
      `tower_signed64 ${frame_bytes:int}`));
  frame_result = match_mp_rule(frame_result, refl_rule(frame_base));
  frame_result = match_mp_rule(frame_result,
      assume_rule(`tower_signed64 ${frame_base:int}`));
  frame_result = match_mp_rule(frame_result,
      assume_rule(`tower_word_valid ${frame_base:int}`));

  thm fp_code_at = cm_call_complete_code_suffix(
      frame_code_at, `cm_model_code (p:cm_program)`, ann1,
      frame_code, after_frame, ann2, frame_pc_rules);
  thm fp_result = specl_rule(TERM_LIST(
      `p:cm_program`, `caller:int`, `st:cm_src_state`,
      frame_bytes, frame_base,
      `REVERSE (values:(cm_value)list)`, ann2, target2,
      after_fp), cm_target_call_fp_prepare);
  fp_result = match_mp_rule(fp_result, fp_code_at);
  fp_result = match_mp_rule(fp_result, frame_result);
  fp_result = match_mp_rule(fp_result, value_capacity);
  fp_result = match_mp_rule(fp_result, assume_rule(
      `tower_signed64 (cm_state_fp (st:cm_src_state))`));
  fp_result = match_mp_rule(fp_result,
      assume_rule(`tower_signed64 ${frame_bytes:int}`));
  fp_result = match_mp_rule(fp_result, refl_rule(frame_base));
  fp_result = match_mp_rule(fp_result,
      assume_rule(`tower_signed64 ${frame_base:int}`));

  thm pending_code_at = cm_call_complete_code_suffix(
      fp_code_at, `cm_model_code (p:cm_program)`, ann2,
      fp_code, after_fp, ann3, fp_pc_rules);
  thm params_code_at = cm_call_complete_code_suffix(
      pending_code_at, `cm_model_code (p:cm_program)`, ann3,
      pending_code, after_pending, param_ann, pending_pc_rules);

  thm calls_3_2 = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        cm_ann_after_call_fp_prepare_def, cm_ann_linear_def,
        cm_ann_plain_def, cm_ann_calls_def)),
      `cm_ann_calls ${ann3:cm_annotation} ==
        cm_ann_calls ${ann2:cm_annotation}`));
  thm calls_2_rebased = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        cm_ann_after_call_frame_save_def, cm_ann_call_rebase_def,
        cm_ann_linear_def, cm_ann_plain_def, cm_ann_calls_def)),
      `cm_ann_calls ${ann2:cm_annotation} ==
        cm_rebase_call_frames ${frame_base:int}
          (cm_ann_calls ${ann1:cm_annotation})`));
  thm calls_1_0 = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        cm_ann_call_jump_def, cm_ann_calls_def)),
      `cm_ann_calls ${ann1:cm_annotation} ==
        CMCallSimFrame 8i (cm_state_fp (st:cm_src_state))
          ${return_pc:int} ::
          cm_ann_calls (ann:cm_annotation)`));
  thm rebased_calls_1 = beta_norm(ap_term_rule(
      `\frames:(cm_call_sim_frame)list.
         cm_rebase_call_frames ${frame_base:int} frames`,
      calls_1_0));
  thm rebase_cons = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        cm_rebase_call_frames_def,
        cm_call_sim_saved_def, cm_call_sim_return_def)),
      `cm_rebase_call_frames ${frame_base:int}
          (CMCallSimFrame 8i (cm_state_fp (st:cm_src_state))
             ${return_pc:int} ::
           cm_ann_calls (ann:cm_annotation)) ==
        CMCallSimFrame ${frame_base:int}
          (cm_state_fp (st:cm_src_state)) ${return_pc:int} ::
          cm_ann_calls (ann:cm_annotation)`));
  thm calls_equal = trans_rule(calls_3_2,
      trans_rule(calls_2_rebased,
        trans_rule(rebased_calls_1, rebase_cons)));
  term call_safe_term =
      `cm_call_frames_store_safe CMIntTy 8i
        (cm_ann_calls ${ann3:cm_annotation})`;
  thm call_safe_view = apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        calls_equal, cm_call_frames_store_safe_def,
        cm_call_sim_base_def, get_cm_store_width_def(),
        get_cm_type_int_char_distinct())),
      call_safe_term);
  thm call_safe_8 = eq_mp_rule(sym_rule(call_safe_view),
      conj_rule(assume_rule(
        `cm_range_disjoint 8i 8i ${frame_base:int} 8i`),
        assume_rule(
          `cm_call_frames_store_safe CMIntTy 8i
            (cm_ann_calls (ann:cm_annotation))`)));
  thm spills_3_2 = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        cm_ann_after_call_fp_prepare_def, cm_ann_linear_def,
        cm_ann_plain_def, cm_ann_spills_def)),
      `cm_ann_spills ${ann3:cm_annotation} ==
        cm_ann_spills ${ann2:cm_annotation}`));
  thm spills_2_1 = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        cm_ann_after_call_frame_save_def, cm_ann_call_rebase_def,
        cm_ann_linear_def, cm_ann_plain_def, cm_ann_spills_def)),
      `cm_ann_spills ${ann2:cm_annotation} ==
        cm_ann_spills ${ann1:cm_annotation}`));
  thm spills_1_0 = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        cm_ann_call_jump_def, cm_ann_spills_def)),
      `cm_ann_spills ${ann1:cm_annotation} ==
        cm_ann_spills (ann:cm_annotation)`));
  thm spills_equal =
      trans_rule(spills_3_2, trans_rule(spills_2_1, spills_1_0));
  thm saved_3_2 = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        cm_ann_after_call_fp_prepare_def, cm_ann_linear_def,
        cm_ann_plain_def, cm_ann_saved_def)),
      `cm_ann_saved ${ann3:cm_annotation} ==
        cm_ann_saved ${ann2:cm_annotation}`));
  thm saved_2_1 = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        cm_ann_after_call_frame_save_def, cm_ann_call_rebase_def,
        cm_ann_linear_def, cm_ann_plain_def, cm_ann_saved_def)),
      `cm_ann_saved ${ann2:cm_annotation} ==
        cm_ann_saved ${ann1:cm_annotation}`));
  thm saved_1_0 = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        cm_ann_call_jump_def, cm_ann_saved_def)),
      `cm_ann_saved ${ann1:cm_annotation} ==
        cm_ann_saved (ann:cm_annotation)`));
  thm saved_equal =
      trans_rule(saved_3_2, trans_rule(saved_2_1, saved_1_0));
  thm active_equal = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        cm_active_spill_frames_def, spills_equal, saved_equal)),
      `cm_active_spill_frames (caller:int) (st:cm_src_state)
          ${ann3:cm_annotation} ==
        ${active:(cm_spill_frame)list}`));

  thm pending_result = specl_rule(TERM_LIST(
      `p:cm_program`, `caller:int`, `callee:int`,
      `st:cm_src_state`, `REVERSE (values:(cm_value)list)`,
      ann3, param_ann, target3, after_pending, frame_base),
      cm_target_call_pending);
  term pending_cons =
      `TVMInst TVMStoreOp 0i :: TVMInst TVMPopOp 0i ::
        ${after_pending:(tvm_inst)list}`;
  term pending_shape_term =
      `(${pending_code:(tvm_inst)list} ++
          ${after_pending:(tvm_inst)list}) ==
        ${pending_cons:(tvm_inst)list}`;
  thm pending_shape = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(get_theorem_by_name("APPEND"))),
      pending_shape_term));
  thm pending_code_shape = beta_norm(ap_term_rule(
      `\suffix:(tvm_inst)list.
         cm_code_at (cm_model_code (p:cm_program))
           (cm_ann_pc ${ann3:cm_annotation}) suffix`,
      pending_shape));
  thm pending_code_ready =
      eq_mp_rule(pending_code_shape, pending_code_at);
  pending_result = match_mp_rule(pending_result, pending_code_ready);
  pending_result = match_mp_rule(pending_result, fp_result);
  pending_result = match_mp_rule(pending_result, assume_rule(
      `cm_function_wf (p:cm_program)
        (inth (callee:int) (cm_program_functions p))`));
  pending_result = match_mp_rule(pending_result, assume_rule(
      `cm_regions_before (cm_state_regions (st:cm_src_state))
        (cm_state_nextgen st)`));
  pending_result = match_mp_rule(pending_result, assume_rule(
      `cm_state_tags_generation_below (st:cm_src_state)
        (cm_state_nextgen st)`));
  pending_result = match_mp_rule(pending_result, assume_rule(
      `cm_values_generation_below (cm_state_nextgen st)
        (REVERSE (values:(cm_value)list))`));
  thm generation_shape = beta_norm(ap_term_rule(
      `\frames:(cm_spill_frame)list.
         cm_spill_frames_generation_below
           (cm_state_nextgen (st:cm_src_state)) frames`,
      active_equal));
  pending_result = match_mp_rule(pending_result,
      eq_mp_rule(sym_rule(generation_shape), assume_rule(
        `cm_spill_frames_generation_below
          (cm_state_nextgen (st:cm_src_state))
          ${active:(cm_spill_frame)list}`)));
  pending_result = match_mp_rule(pending_result,
      assume_rule(`cm_tagged_span_valid (st:cm_src_state)`));
  pending_result = match_mp_rule(pending_result, assume_rule(
      `!addr. cm_live_address (st:cm_src_state) addr ==>
        ~(${frame_base:int} <= addr && addr < ${frame_base:int} + 8i)`));
  pending_result = match_mp_rule(pending_result, assume_rule(
      `!addr. cm_live_address (st:cm_src_state) addr ==>
        ~(8i <= addr && addr < 8i + 8i)`));
  pending_result = match_mp_rule(pending_result, call_safe_8);
  thm store_shape = beta_norm(ap_term_rule(
      `\frames:(cm_spill_frame)list.
         cm_spill_frames_store_safe
           (p:cm_program) CMIntTy 8i frames`,
      active_equal));
  pending_result = match_mp_rule(pending_result,
      eq_mp_rule(sym_rule(store_shape), assume_rule(
        `cm_spill_frames_store_safe
          (p:cm_program) CMIntTy 8i
          ${active:(cm_spill_frame)list}`)));
  pending_result = match_mp_rule(pending_result, refl_rule(frame_base));
  pending_result = match_mp_rule(pending_result, assume_rule(
      `tower_signed64 (cm_state_fp (st:cm_src_state))`));
  pending_result = match_mp_rule(pending_result,
      assume_rule(`tower_signed64 ${frame_base:int}`));
  thm param_pc = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        cm_ann_plain_def, cm_ann_pc_def)),
      `cm_ann_pc ${param_ann:cm_annotation} ==
        cm_ann_pc ${ann3:cm_annotation} + 2i`));
  pending_result = match_mp_rule(pending_result, param_pc);
  thm param_calls_entered = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        cm_ann_plain_def, cm_ann_calls_def)),
      `cm_ann_calls ${param_ann:cm_annotation} ==
        cm_ann_calls ${entered:cm_annotation}`));
  thm entered_calls = assume_rule(
      `cm_ann_calls ${entered:cm_annotation} ==
        CMCallSimFrame ${frame_base:int}
          (cm_state_fp (st:cm_src_state)) ${return_pc:int} ::
          cm_ann_calls (ann:cm_annotation)`);
  thm param_calls_equal = trans_rule(param_calls_entered,
      trans_rule(entered_calls, sym_rule(calls_equal)));
  pending_result =
      match_mp_rule(pending_result, param_calls_equal);
  thm param_active_entered = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        cm_active_spill_frames_def, cm_ann_plain_def,
        cm_ann_spills_def, cm_ann_saved_def)),
      `cm_active_spill_frames (callee:int)
          ${pending:cm_src_state} ${param_ann:cm_annotation} ==
        cm_active_spill_frames callee
          ${pending:cm_src_state} ${entered:cm_annotation}`));
  thm entered_active = assume_rule(
      `cm_active_spill_frames (callee:int)
          ${pending:cm_src_state} ${entered:cm_annotation} ==
        CMSpillFrame (callee:int) ${frame_base:int} [] ::
          ${active:(cm_spill_frame)list}`);
  thm active_tail = beta_norm(ap_term_rule(
      `\frames:(cm_spill_frame)list.
         CMSpillFrame (callee:int) ${frame_base:int} [] :: frames`,
      active_equal));
  thm param_active_equal = trans_rule(param_active_entered,
      trans_rule(entered_active, sym_rule(active_tail)));
  pending_result =
      match_mp_rule(pending_result, param_active_equal);

  thm pending_structure = specl_rule(TERM_LIST(
      `p:cm_program`, `callee:int`, `st:cm_src_state`),
      cm_call_pending_structure);
  thm pending_fp = conjunct1_rule(pending_structure);
  thm pending_regions = conjunct1_rule(
      conjunct2_rule(conjunct2_rule(pending_structure)));
  term pending_env_function_term =
      `cm_state_env ${pending:cm_src_state} ==
        cm_call_env (p:cm_program) (callee:int)
          (cm_state_env (st:cm_src_state)) ${frame_base:int}
          (cm_state_nextgen st)`;
  thm pending_env_function = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_call_pending_base_def(),
        cm_state_make_def, cm_state_env_def)),
      pending_env_function_term));
  term env_index = `j:int`;
  thm pending_env_at = beta_norm(ap_term_rule(
      `\env:int->int->cm_value. env 2i ${env_index:int}`,
      pending_env_function));
  pending_env_at = conv_rule(reduce_rewrite_conv(
      THM_LIST(cm_call_env_def)), pending_env_at);
  term env_lower = `0i <= ${env_index:int}`;
  term env_upper =
      `${env_index:int} < ilength ${params:(cm_slot_d)list}`;
  thm pending_env = gen_rule(env_index,
      disch_rule(env_lower, disch_rule(env_upper, pending_env_at)));
  thm pending_layout = assume_rule(
      `cm_runtime_memory_layout (p:cm_program)
        ${pending:cm_src_state}
        (cm_ann_calls ${entered:cm_annotation})
        (cm_active_spill_frames (callee:int)
          ${pending:cm_src_state} ${entered:cm_annotation})`);
  thm calls_layout = beta_norm(ap_term_rule(
      `\calls:(cm_call_sim_frame)list.
         cm_runtime_memory_layout (p:cm_program)
           ${pending:cm_src_state} calls
           (cm_active_spill_frames (callee:int)
             ${pending:cm_src_state} ${entered:cm_annotation})`,
      param_calls_entered));
  pending_layout =
      eq_mp_rule(sym_rule(calls_layout), pending_layout);
  thm active_layout = beta_norm(ap_term_rule(
      `\frames:(cm_spill_frame)list.
         cm_runtime_memory_layout (p:cm_program)
           ${pending:cm_src_state}
           (cm_ann_calls ${param_ann:cm_annotation}) frames`,
      param_active_entered));
  pending_layout =
      eq_mp_rule(sym_rule(active_layout), pending_layout);

  thm params_result = specl_rule(TERM_LIST(
      params, `values:(cm_value)list`, `p:cm_program`,
      `callee:int`, pending, `cm_state_regions (st:cm_src_state)`,
      `cm_state_nextgen (st:cm_src_state)`, frame_base,
      `cm_state_fp (st:cm_src_state)`, `0i:int`,
      `[]:(cm_value)list`, param_ann, target4, function_tail),
      cm_target_call_params);
  params_result = match_mp_rule(params_result, sym_rule(assume_rule(
      `ilength (values:(cm_value)list) ==
        ilength ${params:(cm_slot_d)list}`)));
  params_result = match_mp_rule(params_result,
      spec_rule(params, cm_param_indices_refl));
  params_result = match_mp_rule(params_result, assume_rule(
      `cm_function_wf (p:cm_program)
        (inth (callee:int) (cm_program_functions p))`));
  params_result = match_mp_rule(params_result, assume_rule(
      `cm_frame_segment (p:cm_program) (callee:int)
        ${frame_base:int} (cm_state_fp (st:cm_src_state))`));
  params_result = match_mp_rule(params_result, assume_rule(
      `cm_regions_before (cm_state_regions (st:cm_src_state))
        (cm_state_nextgen st)`));
  params_result = match_mp_rule(params_result,
      assume_rule(`0i <= cm_state_nextgen (st:cm_src_state)`));
  params_result = match_mp_rule(params_result, pending_fp);
  params_result = match_mp_rule(params_result, pending_regions);
  params_result = match_mp_rule(params_result, pending_env);
  params_result = match_mp_rule(params_result, pending_layout);
  params_result = match_mp_rule(params_result, params_code_at);
  thm reverse_nil = ispec_rule(
      `REVERSE (values:(cm_value)list)`,
      get_theorem_by_name("APPEND_NIL"));
  thm pending_stack_shape = beta_norm(ap_term_rule(
      `\stack_values:(cm_value)list.
         cm_running_target_sim (p:cm_program) (callee:int)
           ${pending:cm_src_state} stack_values
           ${param_ann:cm_annotation} ${target4:tvm_task}`,
      reverse_nil));
  params_result = match_mp_rule(params_result,
      eq_mp_rule(sym_rule(pending_stack_shape), pending_result));
  thm params_capacity_view = apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF"))),
      dest_imp(concl(params_result)).tm1);
  thm normalized_capacity = mp_rule(int_arith_rule(
      `ilength (values:(cm_value)list) < 65534i ==>
       ilength values + 0i < 65534i`),
      assume_rule(`ilength (values:(cm_value)list) < 65534i`));
  thm params_capacity = eq_mp_rule(
      sym_rule(params_capacity_view), normalized_capacity);
  params_result = match_mp_rule(params_result, params_capacity);

  thm entered_state = specl_rule(TERM_LIST(
      `p:cm_program`, `callee:int`, `values:(cm_value)list`,
      `st:cm_src_state`), cm_pending_params_enter_call);
  entered_state = match_mp_rule(entered_state, assume_rule(
      `cm_function_wf (p:cm_program)
        (inth (callee:int) (cm_program_functions p))`));
  entered_state = match_mp_rule(entered_state, assume_rule(
      `cm_frame_segment (p:cm_program) (callee:int)
        ${frame_base:int} (cm_state_fp (st:cm_src_state))`));
  entered_state = match_mp_rule(entered_state, assume_rule(
      `cm_regions_before (cm_state_regions (st:cm_src_state))
        (cm_state_nextgen st)`));
  entered_state = match_mp_rule(entered_state, assume_rule(
      `ilength (values:(cm_value)list) ==
       ilength ${params:(cm_slot_d)list}`));
  params_result = conv_rule(rewrite_conv(THM_LIST(entered_state)),
      params_result);

  term final_ann =
      `cm_ann_linear ${param_code:(tvm_inst)list}
        ${param_ann:cm_annotation}`;
  thm reannotated = specl_rule(TERM_LIST(
      `p:cm_program`, `callee:int`,
      `cm_enter_call (p:cm_program) (callee:int)
        (values:(cm_value)list) (st:cm_src_state)`,
      `[]:(cm_value)list`, final_ann,
      entered, `tvm_iter (cm_code_steps ${param_code:(tvm_inst)list})
        ${target4:tvm_task}`), cm_target_reannotate);
  thm ann1_pc = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        cm_ann_call_jump_def, cm_ann_pc_def)),
      `cm_ann_pc ${ann1:cm_annotation} == ${call_pc:int}`));
  thm ann2_pc = cm_call_complete_pc_offset(
      ann1, frame_code, ann2, frame_pc_rules);
  thm ann3_pc = cm_call_complete_pc_offset(
      ann2, fp_code, ann3, fp_pc_rules);
  thm_list final_pc_rules = THM_LIST(
      cm_ann_linear_def, cm_ann_plain_def, cm_ann_pc_def,
      cm_param_stores_length);
  thm final_pc_offset = cm_call_complete_pc_offset(
      param_ann, param_code, final_ann, final_pc_rules);
  thm ann2_pc_numeric = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_call_frame_save_code_def,
      get_theorem_by_name("ILENGTH_DEF"))), ann2_pc);
  thm ann3_pc_numeric = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_call_fp_prepare_code_def,
      get_theorem_by_name("ILENGTH_DEF"))), ann3_pc);
  thm final_pc_numeric = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_param_stores_length)), final_pc_offset);
  thm entered_pc_absolute = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_call_body_pc_def, get_cm_function_prologue_count_def())),
      assume_rule(
        `cm_ann_pc ${entered:cm_annotation} ==
          cm_call_body_pc (p:cm_program) (callee:int)`));
  term pc_target =
      `cm_ann_pc ${entered:cm_annotation} ==
        cm_ann_pc ${final_ann:cm_annotation}`;
  thm pc_alignment = int_arith_rule(imp_chain(TERM_LIST(
      concl(ann1_pc), concl(ann2_pc_numeric),
      concl(ann3_pc_numeric), concl(param_pc),
      concl(final_pc_numeric), concl(entered_pc_absolute)), pc_target));
  pc_alignment = match_mp_rule(pc_alignment, ann1_pc);
  pc_alignment =
      match_mp_rule(pc_alignment, ann2_pc_numeric);
  pc_alignment =
      match_mp_rule(pc_alignment, ann3_pc_numeric);
  pc_alignment = match_mp_rule(pc_alignment, param_pc);
  pc_alignment =
      match_mp_rule(pc_alignment, final_pc_numeric);
  pc_alignment =
      match_mp_rule(pc_alignment, entered_pc_absolute);
  reannotated = match_mp_rule(reannotated, pc_alignment);
  thm calls_alignment = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        cm_ann_linear_def, cm_ann_plain_def, cm_ann_calls_def)),
      `cm_ann_calls ${entered:cm_annotation} ==
        cm_ann_calls ${final_ann:cm_annotation}`));
  reannotated = match_mp_rule(reannotated, calls_alignment);
  thm spills_alignment = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        cm_ann_linear_def, cm_ann_plain_def, cm_ann_spills_def)),
      `cm_ann_spills ${entered:cm_annotation} ==
        cm_ann_spills ${final_ann:cm_annotation}`));
  reannotated = match_mp_rule(reannotated, spills_alignment);
  thm saved_alignment = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        cm_ann_linear_def, cm_ann_plain_def, cm_ann_saved_def)),
      `cm_ann_saved ${entered:cm_annotation} ==
        cm_ann_saved ${final_ann:cm_annotation}`));
  reannotated = match_mp_rule(reannotated, saved_alignment);
  reannotated = match_mp_rule(reannotated, params_result);
  ACCEPT_TAC(leaf, reannotated);
  return gnode_prove(root);
}

PROOF thm cm_target_call_complete =
    cm_prove_target_call_complete();

PROOF thm get_cm_target_call_complete(void) {
  return cm_target_call_complete;
}

PROOF static int cmc_preservation_target_call_complete_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_target_call_complete_axioms_before,
      "cmc_preservation_target_call_complete introduced an axiom");
  ENSURE_COND(vector_size(hyp(cm_target_call_complete)) == 0,
      "cm_target_call_complete has hypotheses");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_target_call_complete_checks =
    cmc_preservation_target_call_complete_final_checks();
