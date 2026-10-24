#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_target_control_call.h"
#include "cmc_preservation_target_convert.h"
#include "cmc_preservation_target_ready.h"
#include "cmc_preservation_invariant.h"
#include "cmc_preservation_invariant_transition.h"
#include "cmc_preservation_generation.h"
#include "cmc_preservation_generation_step_apply.h"
#include "cmc_preservation_tagged_restore.h"
#include "cmc_preservation_type_ready.h"
#include "cmc_preservation_code_task.h"
#include "cmc_preservation_code_control.h"

#require "cmc_preservation_target_return_machine.c"
#require "cmc_preservation_target_convert.c"
#require "cmc_preservation_target_ready.c"
#require "cmc_preservation_invariant_transition.c"
#require "cmc_preservation_generation.c"
#require "cmc_preservation_generation_step_apply.c"
#require "cmc_preservation_tagged_restore.c"
#require "cmc_preservation_type_ready.c"
#require "cmc_preservation_code_task.c"
#require "cmc_preservation_code_control.c"

PROOF static size_t _cmc_preservation_target_control_call_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_target_call_pick(thm fact, term wanted) {
  if (alpha_compare(concl(fact), wanted) == 0) return fact;
  if (!is_conj(concl(fact))) return empty_theorem;
  thm left = cm_target_call_pick(conjunct1_rule(fact), wanted);
  if (!IS_NULL(left)) return left;
  return cm_target_call_pick(conjunct2_rule(fact), wanted);
}

PROOF static thm_list cm_target_call_annotation_rules(void) {
  return THM_LIST(
      cm_ann_plain_def, cm_ann_linear_def, cm_ann_leave_call_def,
      cm_ann_pc_def, cm_ann_temp_def, cm_ann_break_def,
      cm_ann_continue_def, cm_ann_cursors_def, cm_ann_spills_def,
      cm_ann_saved_def, cm_ann_calls_def,
      cm_cursor_phase_def, cm_cursor_temp_def,
      cm_cursor_break_def, cm_cursor_continue_def,
      get_cm_push_code_def(), get_theorem_by_name("ILENGTH_DEF"),
      get_theorem_by_name("HD"), get_theorem_by_name("TL"),
      get_theorem_by_name("NOT_CONS_NIL"));
}

PROOF static thm cm_target_call_true(term proposition, thm_list rules) {
  return eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(rules), proposition));
}

PROOF static thm cm_target_call_code_suffix(
    thm current_code, term current_ann, term prefix,
    term suffix, term next_ann) {
  thm_list rules = cm_target_call_annotation_rules();
  vector_add(&rules, get_cm_return_epilogue_def());
  vector_add(&rules, get_theorem_by_name("APPEND"));
  vector_add(&rules, get_theorem_by_name("APPEND_NIL"));
  thm current_normal =
      conv_rule(reduce_rewrite_conv(rules), current_code);
  thm tail_rule = ispecl_rule(TERM_LIST(
      `cm_model_code (p:cm_program)`,
      `cm_ann_pc ${current_ann:cm_annotation}`,
      prefix, suffix), get_cm_code_at_append_right());
  thm tail_raw = mp_rule(
      conv_rule(reduce_rewrite_conv(rules), tail_rule),
      current_normal);
  thm tail_normal =
      conv_rule(reduce_rewrite_conv(rules), tail_raw);
  thm tail_view = apply_conversion(
      reduce_rewrite_conv(rules),
      `cm_code_at (cm_model_code (p:cm_program))
        (cm_ann_pc ${next_ann:cm_annotation})
        ${suffix:(tvm_inst)list}`);
  return eq_mp_rule(sym_rule(tail_view), tail_normal);
}

PROOF static thm cm_prove_convert_restore_number(void) {
  term restored =
      `cm_restore_call (st:cm_src_state)
        (oldenv:int->int->cm_value) (oldfp:int)
        (oldregions:(cm_region)list)`;
  term body = imp_chain(TERM_LIST(
      `cm_region_prefix_safe (p:cm_program)
        (cm_state_regions (st:cm_src_state)) (fid:int)
        (cm_state_fp st) (cm_state_regions st)
        (oldregions:(cm_region)list)`,
      `cm_value_generation_below (cm_state_nextgen st)
        (v:cm_value)`),
      `cm_value_number ${restored:cm_src_state}
          (cm_convert_value st (ty:cm_type) v) ==
       cm_value_number ${restored:cm_src_state}
          (cm_convert_value ${restored:cm_src_state} ty v)`);
  gnode root = gnode_new_with_ccl(list_mk_forall(free_vars(body), body));
  gnode leaf = AUTO_INTROS_TAC(root);
  thm prefix = assume_rule(
      `cm_region_prefix_safe (p:cm_program)
        (cm_state_regions (st:cm_src_state)) (fid:int)
        (cm_state_fp st) (cm_state_regions st)
        (oldregions:(cm_region)list)`);
  thm value_below = assume_rule(
      `cm_value_generation_below (cm_state_nextgen (st:cm_src_state))
        (v:cm_value)`);
  thm bases = match_mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `oldenv:int->int->cm_value`,
      `oldfp:int`, `oldregions:(cm_region)list`, `st:cm_src_state`),
      get_cm_restore_call_bases_below()), prefix);
  thm raw_number = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
      `v:cm_value`, `st:cm_src_state`, restored,
      `cm_state_nextgen (st:cm_src_state)`),
      cm_value_number_bases), bases), value_below);
  thm converted_below = match_mp_rule(specl_rule(TERM_LIST(
      `st:cm_src_state`, `ty:cm_type`, `v:cm_value`,
      `cm_state_nextgen (st:cm_src_state)`),
      get_cm_convert_generation_below()), value_below);
  thm converted_number = match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(
        `cm_convert_value (st:cm_src_state) (ty:cm_type) (v:cm_value)`,
        `st:cm_src_state`, restored,
        `cm_state_nextgen (st:cm_src_state)`),
        cm_value_number_bases), bases), converted_below);
  thm old_bridge = specl_rule(TERM_LIST(
      `st:cm_src_state`, `ty:cm_type`, `v:cm_value`),
      get_cm_convert_value_number_bridge());
  thm new_bridge = specl_rule(TERM_LIST(
      restored, `ty:cm_type`, `v:cm_value`),
      get_cm_convert_value_number_bridge());
  term operation =
      `\(number:int). if (ty:cm_type) == CMCharTy
                       then tower_u8 number else number`;
  thm operation_equal = beta_norm(
      ap_term_rule(operation, sym_rule(raw_number)));
  thm result = trans_rule(converted_number,
      trans_rule(old_bridge,
        trans_rule(operation_equal, sym_rule(new_bridge))));
  ACCEPT_TAC(leaf, result);
  return gnode_prove(root);
}
PROOF static thm cm_convert_restore_number =
    cm_prove_convert_restore_number();

PROOF static thm cm_prove_target_call_epilogue(void) {
  term restored =
      `cm_restore_call (st:cm_src_state)
        (oldenv:int->int->cm_value) (oldfp:int)
        (oldregions:(cm_region)list)`;
  term caller_saved =
      `CMSpillFrame (caller:int) (oldfp:int)
         (caller_spills:(cm_spill)list) ::
       (saved:(cm_spill_frame)list)`;
  term body = imp_chain(TERM_LIST(
      `cm_code_at (cm_model_code (p:cm_program))
        (cm_ann_pc (ann:cm_annotation)) cm_return_epilogue`,
      `cm_ann_calls ann ==
        CMCallSimFrame (cm_state_fp (st:cm_src_state))
          (oldfp:int) (returnpc:int) ::
        (calls:(cm_call_sim_frame)list)`,
      `cm_ann_saved ann == ${caller_saved:(cm_spill_frame)list}`,
      `cm_region_prefix_safe p (cm_state_regions st) (fid:int)
        (cm_state_fp st) (cm_state_regions st)
        (oldregions:(cm_region)list)`,
      `cm_state_tags_generation_below st (cm_state_nextgen st)`,
      `cm_spill_frames_generation_below (cm_state_nextgen st)
        ${caller_saved:(cm_spill_frame)list}`,
      `cm_value_generation_below (cm_state_nextgen st)
        (retv:cm_value)`,
      `cm_tagged_span_valid ${restored:cm_src_state}`,
      `!addr. cm_live_address ${restored:cm_src_state} addr ==>
        ~(8i <= addr && addr < 16i)`,
      `cm_call_frames_store_safe CMIntTy 8i
        (calls:(cm_call_sim_frame)list)`,
      `cm_spill_frames_store_safe p CMIntTy 8i
        ${caller_saved:(cm_spill_frame)list}`,
      `tower_signed64 (cm_state_fp st)`,
      `tower_word_valid (cm_state_fp st)`,
      `tower_signed64 (oldfp:int)`,
      `cm_running_target_sim p (fid:int) st [(retv:cm_value)]
        ann (target:tvm_task)`),
      `cm_running_target_sim p (caller:int) ${restored:cm_src_state}
        [(retv:cm_value)] (cm_ann_leave_call (returnpc:int) ann)
        (tvm_iter 6 target)`);
  gnode root = gnode_new_with_ccl(list_mk_forall(free_vars(body), body));
  gnode leaf = AUTO_INTROS_TAC(root);
  thm code0 = assume_rule(
      `cm_code_at (cm_model_code (p:cm_program))
        (cm_ann_pc (ann:cm_annotation)) cm_return_epilogue`);
  thm calls_shape = assume_rule(
      `cm_ann_calls (ann:cm_annotation) ==
       CMCallSimFrame (cm_state_fp (st:cm_src_state))
         (oldfp:int) (returnpc:int) ::
       (calls:(cm_call_sim_frame)list)`);
  thm saved_shape = assume_rule(
      `cm_ann_saved (ann:cm_annotation) ==
       ${caller_saved:(cm_spill_frame)list}`);
  thm running0 = assume_rule(
      `cm_running_target_sim (p:cm_program) (fid:int)
        (st:cm_src_state) [(retv:cm_value)]
        (ann:cm_annotation) (target:tvm_task)`);
  term suffix1 =
      `[TVMInst TVMLoadOp 0i; TVMInst TVMLoadOp 0i;
        TVMInst TVMPushOp 8i; TVMInst TVMStoreOp 0i;
        TVMInst TVMRetOp 0i]:(tvm_inst)list`;
  term suffix2 =
      `[TVMInst TVMLoadOp 0i; TVMInst TVMPushOp 8i;
        TVMInst TVMStoreOp 0i; TVMInst TVMRetOp 0i]:(tvm_inst)list`;
  term suffix3 =
      `[TVMInst TVMPushOp 8i; TVMInst TVMStoreOp 0i;
        TVMInst TVMRetOp 0i]:(tvm_inst)list`;
  term suffix4 =
      `[TVMInst TVMStoreOp 0i; TVMInst TVMRetOp 0i]:(tvm_inst)list`;
  term ann1 = `cm_ann_linear (cm_push_code 8i) (ann:cm_annotation)`;
  term ann2 =
      `cm_ann_linear [TVMInst TVMLoadOp 0i] ${ann1:cm_annotation}`;
  term ann3 =
      `cm_ann_linear [TVMInst TVMLoadOp 0i] ${ann2:cm_annotation}`;
  term ann4 = `cm_ann_linear (cm_push_code 8i) ${ann3:cm_annotation}`;
  term target1 = `tvm_iter 1 (target:tvm_task)`;
  term target2 = `tvm_iter 1 ${target1:tvm_task}`;
  term target3 = `tvm_iter 1 ${target2:tvm_task}`;
  term target4 = `tvm_iter 1 ${target3:tvm_task}`;
  thm push_bridge = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_value_number_def(), get_tower_wrap64_def())),
      `tower_wrap64 8i ==
       cm_value_number (st:cm_src_state) (CMIntV 8i)`));
  thm capacity1 = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(get_theorem_by_name("ILENGTH_DEF"))),
      `ilength ([(retv:cm_value)]:(cm_value)list) < 65536i`));
  thm pushed1 = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`,
      `[(retv:cm_value)]:(cm_value)list`, `ann:cm_annotation`,
      `target:tvm_task`, `CMIntV 8i`, `8i:int`, suffix1),
      get_cm_target_push());
  pushed1 = match_mp_rule(pushed1,
      conv_rule(reduce_rewrite_conv(THM_LIST(
        get_cm_return_epilogue_def(), get_cm_push_code_def(),
        get_theorem_by_name("APPEND"))), code0));
  pushed1 = match_mp_rule(pushed1, running0);
  pushed1 = match_mp_rule(pushed1, capacity1);
  pushed1 = match_mp_rule(pushed1, push_bridge);

  thm code1 = cm_target_call_code_suffix(code0,
      `ann:cm_annotation`, `cm_push_code 8i`, suffix1, ann1);
  thm loaded_fp = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`,
      `[(retv:cm_value)]:(cm_value)list`, ann1, target1, suffix2),
      get_cm_target_load_fp());
  loaded_fp = match_mp_rule(loaded_fp, code1);
  loaded_fp = match_mp_rule(loaded_fp, pushed1);
  loaded_fp = match_mp_rule(loaded_fp, assume_rule(
      `tower_signed64 (cm_state_fp (st:cm_src_state))`));

  thm code2 = cm_target_call_code_suffix(code1, ann1,
      `[TVMInst TVMLoadOp 0i]:(tvm_inst)list`, suffix2, ann2);
  thm_list calls2_rules = cm_target_call_annotation_rules();
  vector_add(&calls2_rules, calls_shape);
  thm calls2 = cm_target_call_true(
      `cm_ann_calls ${ann2:cm_annotation} ==
       CMCallSimFrame (cm_state_fp (st:cm_src_state))
         (oldfp:int) (returnpc:int) ::
       (calls:(cm_call_sim_frame)list)`,
      calls2_rules);
  thm loaded_saved = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`, `oldfp:int`,
      `returnpc:int`, `calls:(cm_call_sim_frame)list`,
      `[(retv:cm_value)]:(cm_value)list`, ann2, target2, suffix3),
      get_cm_target_load_saved_fp());
  loaded_saved = match_mp_rule(loaded_saved, code2);
  loaded_saved = match_mp_rule(loaded_saved, calls2);
  loaded_saved = match_mp_rule(loaded_saved, assume_rule(
      `tower_signed64 (cm_state_fp (st:cm_src_state))`));
  loaded_saved = match_mp_rule(loaded_saved, assume_rule(
      `tower_word_valid (cm_state_fp (st:cm_src_state))`));
  loaded_saved = match_mp_rule(loaded_saved,
      assume_rule(`tower_signed64 (oldfp:int)`));
  loaded_saved = match_mp_rule(loaded_saved, loaded_fp);

  thm code3 = cm_target_call_code_suffix(code2, ann2,
      `[TVMInst TVMLoadOp 0i]:(tvm_inst)list`, suffix3, ann3);
  thm capacity2 = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(get_theorem_by_name("ILENGTH_DEF"))),
      `ilength ([CMIntV (oldfp:int); (retv:cm_value)]:
         (cm_value)list) < 65536i`));
  thm pushed2 = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`,
      `[CMIntV (oldfp:int); (retv:cm_value)]:(cm_value)list`,
      ann3, target3, `CMIntV 8i`, `8i:int`, suffix4),
      get_cm_target_push());
  pushed2 = match_mp_rule(pushed2, code3);
  pushed2 = match_mp_rule(pushed2, loaded_saved);
  pushed2 = match_mp_rule(pushed2, capacity2);
  pushed2 = match_mp_rule(pushed2, push_bridge);

  thm code4 = cm_target_call_code_suffix(code3, ann3,
      `cm_push_code 8i`, suffix4, ann4);
  thm_list calls4_rules = cm_target_call_annotation_rules();
  vector_add(&calls4_rules, calls_shape);
  thm calls4 = cm_target_call_true(
      `cm_ann_calls ${ann4:cm_annotation} ==
       CMCallSimFrame (cm_state_fp (st:cm_src_state))
         (oldfp:int) (returnpc:int) ::
       (calls:(cm_call_sim_frame)list)`,
      calls4_rules);
  thm_list saved4_rules = cm_target_call_annotation_rules();
  vector_add(&saved4_rules, saved_shape);
  thm saved4 = cm_target_call_true(
      `cm_ann_saved ${ann4:cm_annotation} ==
       ${caller_saved:(cm_spill_frame)list}`,
      saved4_rules);
  thm result = specl_rule(TERM_LIST(
      `[]:(tvm_inst)list`, `calls:(cm_call_sim_frame)list`,
      `caller_spills:(cm_spill)list`, `saved:(cm_spill_frame)list`,
      `fid:int`, `p:cm_program`, `caller:int`, `st:cm_src_state`,
      `oldenv:int->int->cm_value`, `oldfp:int`,
      `oldregions:(cm_region)list`, `retv:cm_value`, `returnpc:int`,
      ann4, target4), get_cm_target_return_epilogue());
  result = match_mp_rule(result, code4);
  result = match_mp_rule(result, calls4);
  result = match_mp_rule(result, saved4);
  result = match_mp_rule(result, assume_rule(
      `cm_region_prefix_safe (p:cm_program)
        (cm_state_regions (st:cm_src_state)) (fid:int)
        (cm_state_fp st) (cm_state_regions st)
        (oldregions:(cm_region)list)`));
  result = match_mp_rule(result, assume_rule(
      `cm_state_tags_generation_below (st:cm_src_state)
        (cm_state_nextgen st)`));
  result = match_mp_rule(result, assume_rule(
      `cm_spill_frames_generation_below (cm_state_nextgen st)
        ${caller_saved:(cm_spill_frame)list}`));
  result = match_mp_rule(result, assume_rule(
      `cm_value_generation_below (cm_state_nextgen st)
        (retv:cm_value)`));
  result = match_mp_rule(result, assume_rule(
      `cm_tagged_span_valid ${restored:cm_src_state}`));
  result = match_mp_rule(result, assume_rule(
      `!addr. cm_live_address ${restored:cm_src_state} addr ==>
        ~(8i <= addr && addr < 16i)`));
  result = match_mp_rule(result, assume_rule(
      `cm_call_frames_store_safe CMIntTy 8i
        (calls:(cm_call_sim_frame)list)`));
  result = match_mp_rule(result, assume_rule(
      `cm_spill_frames_store_safe (p:cm_program) CMIntTy 8i
        ${caller_saved:(cm_spill_frame)list}`));
  result = match_mp_rule(result,
      assume_rule(`tower_signed64 (oldfp:int)`));
  result = match_mp_rule(result, pushed2);

  thm_list finish_rules = cm_target_call_annotation_rules();
  vector_add(&finish_rules, gsym_rule(get_cm_tvm_iter_add()));
  vector_add(&finish_rules, get_theorem_by_name("ADD_ASSOC"));
  vector_add(&finish_rules, get_cm_return_epilogue_def());
  vector_add(&finish_rules, get_theorem_by_name("APPEND"));
  vector_add(&finish_rules, get_theorem_by_name("APPEND_NIL"));
  vector_add(&finish_rules, apply_conversion(
      get_conversion_by_name("NUM_REDUCE_CONV"),
      `((((1:num) + 1) + 1) + 1) + 2`));
  thm normalized = conv_rule(reduce_rewrite_conv(finish_rules), result);
  thm target_view = apply_conversion(
      reduce_rewrite_conv(finish_rules), goal_ccl(leaf->g));
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), normalized));
  return gnode_prove(root);
}
PROOF static thm cm_target_call_epilogue =
    cm_prove_target_call_epilogue();

PROOF static thm cm_prove_call_spill_frame_reconstruct(void) {
  gnode root = gnode_new_with_ccl(
      `!(frame:cm_spill_frame).
         CMSpillFrame (cm_spill_frame_fid frame)
           (cm_spill_frame_fp frame)
           (cm_spill_frame_spills frame) == frame`);
  gnode_list cases = INDUCT_TAC(root, `frame:cm_spill_frame`);
  CONV_TAC(cases[0], reduce_rewrite_conv(THM_LIST(
      cm_spill_frame_fid_def, cm_spill_frame_fp_def,
      cm_spill_frame_spills_def)));
  return gnode_prove(root);
}
PROOF static thm cm_call_spill_frame_reconstruct =
    cm_prove_call_spill_frame_reconstruct();

PROOF static thm cm_prove_call_sim_frame_reconstruct(void) {
  gnode root = gnode_new_with_ccl(
      `!(frame:cm_call_sim_frame).
         CMCallSimFrame (cm_call_sim_base frame)
           (cm_call_sim_saved frame)
           (cm_call_sim_return frame) == frame`);
  gnode_list cases = INDUCT_TAC(root, `frame:cm_call_sim_frame`);
  CONV_TAC(cases[0], reduce_rewrite_conv(THM_LIST(
      cm_call_sim_base_def, cm_call_sim_saved_def,
      cm_call_sim_return_def)));
  return gnode_prove(root);
}
PROOF static thm cm_call_sim_frame_reconstruct =
    cm_prove_call_sim_frame_reconstruct();

PROOF static thm cm_target_call_cons_reconstruct(
    term list_value, term cons_constant, term tail_value,
    thm head_reconstruct, thm nonempty) {
  thm list_shape = mp_rule(
      ispec_rule(list_value, get_theorem_by_name("CONS_HD_TL")),
      nonempty);
  thm rebuilt = mk_comb_rule(mk_comb_rule(
      refl_rule(cons_constant), head_reconstruct),
      refl_rule(tail_value));
  return sym_rule(trans_rule(rebuilt, sym_rule(list_shape)));
}

PROOF static thm cm_prove_call_return_steps(void) {
  term char_code =
      `cm_char_normalize_code
        (cm_function_ret
          (inth (fid:int) (cm_program_functions (p:cm_program))))`;
  term body =
      `cm_code_steps (cm_return_tail_code (p:cm_program) (fid:int)) ==
       cm_code_steps ${char_code:(tvm_inst)list} + 6`;
  gnode root = gnode_new_with_ccl(list_mk_forall(free_vars(body), body));
  gnode leaf = AUTO_INTROS_TAC(root);
  thm nonnegative = ispec_rule(
      char_code, get_theorem_by_name("ILENGTH_NONNEG"));
  thm count_add = mp_rule(specl_rule(TERM_LIST(
      `ilength ${char_code:(tvm_inst)list}`, `6i:int`),
      get_theorem_by_name("NUM_OF_INT_ADD")),
      conj_rule(nonnegative, int_arith_rule(`0i <= 6i`)));
  count_add = conv_rule(rewrite_conv(THM_LIST(
      spec_rule(`6:num`, get_theorem_by_name("NUM_OF_INT_OF_NUM")))),
      count_add);
  thm_list rules = THM_LIST(
      cm_return_tail_code_def, get_cm_return_epilogue_def(),
      cm_code_steps_def, get_theorem_by_name("ILENGTH_APPEND"),
      get_theorem_by_name("ILENGTH_DEF"), sym_rule(count_add),
      spec_rule(`6:num`, get_theorem_by_name("NUM_OF_INT_OF_NUM")));
  thm solved = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(rules), goal_ccl(leaf->g)));
  ACCEPT_TAC(leaf, solved);
  return gnode_prove(root);
}
PROOF static thm cm_call_return_steps =
    cm_prove_call_return_steps();

PROOF static thm cm_prove_call_fallthrough_steps(void) {
  gnode root = gnode_new_with_ccl(
      `cm_code_steps cm_fallthrough_tail_code == 7`);
  gnode leaf = AUTO_INTROS_TAC(root);
  conv normalize = then_conv(
      reduce_rewrite_conv(THM_LIST(
        cm_fallthrough_tail_code_def, get_cm_return_epilogue_def(),
        cm_code_steps_def, get_theorem_by_name("ILENGTH_APPEND"),
        get_theorem_by_name("ILENGTH_DEF"))),
      rewrite_conv(THM_LIST(
        spec_rule(`7:num`, get_theorem_by_name("NUM_OF_INT_OF_NUM")))));
  thm solved = eqt_elim_rule(apply_conversion(
      normalize, goal_ccl(leaf->g)));
  ACCEPT_TAC(leaf, solved);
  return gnode_prove(root);
}
PROOF static thm cm_call_fallthrough_steps =
    cm_prove_call_fallthrough_steps();

PROOF static thm_list cm_target_call_layout_rules(
    thm control_shape) {
  thm_list rules = cm_target_call_annotation_rules();
  vector_add(&rules, control_shape);
  vector_add(&rules, cm_task_layout_def);
  vector_add(&rules, cm_task_code_def);
  vector_add(&rules, cm_control_phase_code_def);
  vector_add(&rules, cm_normal_cont_code_def);
  vector_add(&rules, cm_cursor_code_def);
  vector_add(&rules, cm_normal_phase_code_def);
  vector_add(&rules, cm_normal_phase_stops_def);
  vector_add(&rules, get_cm_control_kind_def());
  vector_add(&rules, get_cm_control_value_def());
  vector_add(&rules, get_cm_control_status_def());
  vector_add(&rules, cm_fallthrough_tail_code_def);
  vector_add(&rules, cm_return_tail_code_def);
  vector_add(&rules, get_cm_return_epilogue_def());
  vector_add(&rules, get_theorem_by_name("APPEND"));
  vector_add(&rules, get_theorem_by_name("APPEND_NIL"));
  return rules;
}

PROOF static thm cm_target_call_layout_code(
    thm layout, thm control_shape, term concrete_control,
    size_t control_index, term annotation) {
  term wanted_code = control_index == 3
      ? `cm_char_normalize_code
          (cm_function_ret
            (inth (fid:int) (cm_program_functions (p:cm_program)))) ++
         cm_return_epilogue`
      : `[TVMInst TVMPushOp 0i] ++ cm_return_epilogue`;
  term wanted =
      `cm_code_at (cm_model_code (p:cm_program))
        (cm_ann_pc ${annotation:cm_annotation})
        ${wanted_code:(tvm_inst)list}`;
  thm_list rules = cm_target_call_layout_rules(control_shape);
  thm opened = conv_rule(reduce_rewrite_conv(rules), layout);
  thm code = conjunct1_rule(opened);
  thm normalized = conv_rule(reduce_rewrite_conv(rules), code);
  thm wanted_view = apply_conversion(
      reduce_rewrite_conv(rules), wanted);
  (void)concrete_control;
  return eq_mp_rule(sym_rule(wanted_view), normalized);
}

PROOF static thm cm_target_call_running(
    thm sim, thm control_shape, term concrete_control,
    term annotation, size_t control_index) {
  term values = control_index == 3
      ? `[cm_control_value ${concrete_control:cm_control}]:
           (cm_value)list`
      : `[]:(cm_value)list`;
  term wanted =
      `cm_running_target_sim (p:cm_program) (fid:int)
        (st:cm_src_state) ${values:(cm_value)list}
        ${annotation:cm_annotation} (target:tvm_task)`;
  thm_list rules = THM_LIST(
      control_shape, cm_task_target_sim_def,
      get_cm_control_kind_def(), get_cm_control_value_def(),
      get_cm_control_status_def());
  thm normalized = conv_rule(reduce_rewrite_conv(rules), sim);
  thm wanted_view = apply_conversion(
      reduce_rewrite_conv(rules), wanted);
  return eq_mp_rule(sym_rule(wanted_view), normalized);
}

PROOF static thm cm_target_call_apply_epilogue(
    term epilogue_ann, term epilogue_target, term retv,
    thm epilogue_code, thm calls_shape, thm saved_shape,
    thm prefix, thm tag_below, thm spill_below,
    thm value_below, thm span_valid, thm outside,
    thm calls_safe, thm spills_safe, thm fp_signed,
    thm fp_word, thm oldfp_signed, thm running) {
  term caller_saved =
      `CMSpillFrame (caller:int) (oldfp:int)
         (cm_spill_frame_spills
           (HD (saved0:(cm_spill_frame)list))) ::
       TL saved0`;
  thm calls_selector = cm_target_call_true(
      `cm_ann_calls ${epilogue_ann:cm_annotation} ==
       (calls0:(cm_call_sim_frame)list)`,
      cm_target_call_annotation_rules());
  thm shaped_calls = trans_rule(calls_selector, calls_shape);
  thm saved_selector = cm_target_call_true(
      `cm_ann_saved ${epilogue_ann:cm_annotation} ==
       (saved0:(cm_spill_frame)list)`,
      cm_target_call_annotation_rules());
  thm shaped_saved = trans_rule(saved_selector, saved_shape);
  thm result = specl_rule(TERM_LIST(
      `TL (calls0:(cm_call_sim_frame)list)`,
      `cm_spill_frame_spills
        (HD (saved0:(cm_spill_frame)list))`,
      `TL (saved0:(cm_spill_frame)list)`,
      `fid:int`, `p:cm_program`, `caller:int`, `st:cm_src_state`,
      `oldenv:int->int->cm_value`, `oldfp:int`,
      `oldregions:(cm_region)list`, retv,
      `cm_call_sim_return
        (HD (calls0:(cm_call_sim_frame)list))`,
      epilogue_ann, epilogue_target), cm_target_call_epilogue);
  result = match_mp_rule(result, epilogue_code);
  result = match_mp_rule(result, shaped_calls);
  result = match_mp_rule(result, shaped_saved);
  result = match_mp_rule(result, prefix);
  result = match_mp_rule(result, tag_below);
  result = match_mp_rule(result, spill_below);
  result = match_mp_rule(result, value_below);
  result = match_mp_rule(result, span_valid);
  result = match_mp_rule(result, outside);
  result = match_mp_rule(result, calls_safe);
  result = match_mp_rule(result, spills_safe);
  result = match_mp_rule(result, fp_signed);
  result = match_mp_rule(result, fp_word);
  result = match_mp_rule(result, oldfp_signed);
  return match_mp_rule(result, running);
}

PROOF static void cm_target_call_accept(
    gnode branch, thm result, thm control_shape,
    thm ret_equal) {
  thm_list rules = cm_target_call_annotation_rules();
  vector_add(&rules, control_shape);
  vector_add(&rules, ret_equal);
  vector_add(&rules, get_cm_step_def());
  vector_add(&rules, get_cm_capply_def());
  vector_add(&rules, get_cm_control_kind_def());
  vector_add(&rules, get_cm_control_value_def());
  vector_add(&rules, get_cm_control_status_def());
  vector_add(&rules, cm_annotation_step_def);
  vector_add(&rules, cm_update_c_def);
  vector_add(&rules, cm_update_steps_def);
  vector_add(&rules, cm_update_annotation_def);
  vector_add(&rules, cm_task_target_sim_def);
  vector_add(&rules, cm_phase_frame_def);
  vector_add(&rules, cm_cursor_frames_def);
  vector_add(&rules, cm_call_return_steps);
  vector_add(&rules, cm_call_fallthrough_steps);
  vector_add(&rules, cm_return_tail_code_def);
  vector_add(&rules, cm_fallthrough_tail_code_def);
  vector_add(&rules, gsym_rule(get_cm_tvm_iter_add()));
  vector_add(&rules, get_theorem_by_name("ADD_ASSOC"));
  vector_add(&rules, apply_conversion(
      get_conversion_by_name("NUM_REDUCE_CONV"), `(1:num) + 6`));
  thm normalized = conv_rule(reduce_rewrite_conv(rules), result);
  normalized = conv_rule(reduce_rewrite_conv(rules), normalized);
  thm target_stage = apply_conversion(
      reduce_rewrite_conv(rules), goal_ccl(branch->g));
  thm target_finish = apply_conversion(
      reduce_rewrite_conv(rules), rhs_of(target_stage));
  thm target_view = trans_rule(target_stage, target_finish);
  ACCEPT_TAC(branch, eq_mp_rule(sym_rule(target_view), normalized));
}

PROOF static thm cm_prove_target_c_call_step(void) {
  term phase =
      `CACallP (caller:int) (oldenv:int->int->cm_value)
        (oldfp:int) (oldregions:(cm_region)list) (ret:cm_type)`;
  term cursors =
      `CMACursor ${phase:cm_aphase} (owner:int)
        (saved_break:int) (saved_continue:int) ::
       (rest:(cm_acursor)list)`;
  term frames =
      `CMCallK (caller:int) (oldenv:int->int->cm_value)
        (oldfp:int) (oldregions:(cm_region)list) (ret:cm_type) ::
       cm_cursor_frames (rest:(cm_acursor)list)`;
  term annotation =
      `CMAnnotation (pc:int) (temp:int) (breakpc:int) (continuepc:int)
        ${cursors:(cm_acursor)list} (spills:(cm_spill)list)
        (saved0:(cm_spill_frame)list)
        (calls0:(cm_call_sim_frame)list)`;
  term task =
      `CMCTask (p:cm_program) (fid:int) (ctl:cm_control)
        (st:cm_src_state) ${frames:(cm_frame)list}`;
  term update =
      `cm_annotation_step ${task:cm_task} ${annotation:cm_annotation}`;
  term body = imp_chain(TERM_LIST(
      `cm_task_runtime_invariant (p:cm_program) ${task:cm_task}
        ${annotation:cm_annotation}`,
      `cm_task_generation_safe p ${task:cm_task}
        ${annotation:cm_annotation}`,
      `cm_task_type_ready p ${task:cm_task}
        ${annotation:cm_annotation}`,
      `cm_tagged_span_valid (st:cm_src_state)`,
      `cm_task_layout p ${task:cm_task} ${annotation:cm_annotation}`,
      `cm_task_target_sim p ${task:cm_task} (target:tvm_task)
        ${annotation:cm_annotation}`,
      `cm_control_kind (ctl:cm_control) == 0i ||
       cm_control_kind ctl == 3i`),
      `cm_task_target_sim p (cm_step ${task:cm_task})
        (tvm_iter (cm_update_steps ${update:cm_aupdate})
          (target:tvm_task))
        (cm_update_annotation ${update:cm_aupdate})`);
  gnode root = gnode_new_with_ccl(list_mk_forall(free_vars(body), body));
  gnode introduced = AUTO_INTROS_TAC(root);
  thm runtime = assume_rule(
      `cm_task_runtime_invariant (p:cm_program) ${task:cm_task}
        ${annotation:cm_annotation}`);
  thm generation = assume_rule(
      `cm_task_generation_safe (p:cm_program) ${task:cm_task}
        ${annotation:cm_annotation}`);
  thm typed = assume_rule(
      `cm_task_type_ready (p:cm_program) ${task:cm_task}
        ${annotation:cm_annotation}`);
  thm tagged = assume_rule(
      `cm_tagged_span_valid (st:cm_src_state)`);
  thm layout = assume_rule(
      `cm_task_layout (p:cm_program) ${task:cm_task}
        ${annotation:cm_annotation}`);
  thm sim = assume_rule(
      `cm_task_target_sim (p:cm_program) ${task:cm_task}
        (target:tvm_task) ${annotation:cm_annotation}`);
  thm allowed = assume_rule(
      `cm_control_kind (ctl:cm_control) == 0i ||
       cm_control_kind ctl == 3i`);

  thm_list ann_rules = cm_target_call_annotation_rules();
  thm runtime_opened = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_task_runtime_invariant_def, cm_ann_cursors_def,
      cm_ann_spills_def, cm_ann_saved_def, cm_ann_calls_def)), runtime);
  thm regions_before = cm_target_call_pick(runtime_opened,
      `cm_regions_before (cm_state_regions (st:cm_src_state))
        (cm_state_nextgen st)`);
  thm stack = cm_target_call_pick(runtime_opened,
      `cm_runtime_stack (p:cm_program)
        (cm_state_regions (st:cm_src_state)) (fid:int)
        (cm_state_fp st) (cm_state_regions st)
        ${cursors:(cm_acursor)list} (spills:(cm_spill)list)
        (saved0:(cm_spill_frame)list)
        (calls0:(cm_call_sim_frame)list)`);
  thm stack_opened = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_runtime_stack_def, cm_cursor_phase_def,
      cm_phase_is_call_def, cm_phase_oldregions_def,
      cm_phase_oldfp_def, cm_phase_caller_def)), stack);
  thm prefix = cm_target_call_pick(stack_opened,
      `cm_region_prefix_safe (p:cm_program)
        (cm_state_regions (st:cm_src_state)) (fid:int)
        (cm_state_fp st) (cm_state_regions st)
        (oldregions:(cm_region)list)`);
  thm frame_segment = cm_target_call_pick(stack_opened,
      `cm_frame_segment (p:cm_program) (fid:int)
        (cm_state_fp (st:cm_src_state)) (oldfp:int)`);
  thm saved_nonempty = cm_target_call_pick(stack_opened,
      `~((saved0:(cm_spill_frame)list) == [])`);
  thm calls_nonempty = cm_target_call_pick(stack_opened,
      `~((calls0:(cm_call_sim_frame)list) == [])`);
  thm saved_fid = cm_target_call_pick(stack_opened,
      `cm_spill_frame_fid
        (HD (saved0:(cm_spill_frame)list)) == (caller:int)`);
  thm saved_fp = cm_target_call_pick(stack_opened,
      `cm_spill_frame_fp
        (HD (saved0:(cm_spill_frame)list)) == (oldfp:int)`);
  thm call_base = cm_target_call_pick(stack_opened,
      `cm_call_sim_base
        (HD (calls0:(cm_call_sim_frame)list)) ==
       cm_state_fp (st:cm_src_state)`);
  thm call_saved = cm_target_call_pick(stack_opened,
      `cm_call_sim_saved
        (HD (calls0:(cm_call_sim_frame)list)) == (oldfp:int)`);

  thm saved_head = spec_rule(
      `HD (saved0:(cm_spill_frame)list)`,
      cm_call_spill_frame_reconstruct);
  saved_head = conv_rule(rewrite_conv(THM_LIST(
      saved_fid, saved_fp)), saved_head);
  thm saved_shape = cm_target_call_cons_reconstruct(
      `saved0:(cm_spill_frame)list`,
      `CONS:cm_spill_frame->(cm_spill_frame)list->
        (cm_spill_frame)list`,
      `TL (saved0:(cm_spill_frame)list)`,
      saved_head, saved_nonempty);
  thm call_head = spec_rule(
      `HD (calls0:(cm_call_sim_frame)list)`,
      cm_call_sim_frame_reconstruct);
  call_head = conv_rule(rewrite_conv(THM_LIST(
      call_base, call_saved)), call_head);
  thm calls_shape = cm_target_call_cons_reconstruct(
      `calls0:(cm_call_sim_frame)list`,
      `CONS:cm_call_sim_frame->(cm_call_sim_frame)list->
        (cm_call_sim_frame)list`,
      `TL (calls0:(cm_call_sim_frame)list)`,
      call_head, calls_nonempty);

  thm core_body = conj_rule(regions_before, stack);
  thm core_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
      cm_runtime_core_def, cm_ann_cursors_def, cm_ann_spills_def,
      cm_ann_saved_def, cm_ann_calls_def)),
      `cm_runtime_core (p:cm_program) (fid:int)
        (st:cm_src_state) ${annotation:cm_annotation}`);
  thm core = eq_mp_rule(sym_rule(core_view), core_body);
  thm cursor_shape = cm_target_call_true(
      `cm_ann_cursors ${annotation:cm_annotation} ==
       ${cursors:(cm_acursor)list}`, ann_rules);
  thm saved_selector = cm_target_call_true(
      `cm_ann_saved ${annotation:cm_annotation} ==
       (saved0:(cm_spill_frame)list)`,
      cm_target_call_annotation_rules());
  thm saved_ann_shape = trans_rule(saved_selector, saved_shape);
  thm calls_selector = cm_target_call_true(
      `cm_ann_calls ${annotation:cm_annotation} ==
       (calls0:(cm_call_sim_frame)list)`,
      cm_target_call_annotation_rules());
  thm calls_ann_shape = trans_rule(calls_selector, calls_shape);
  thm leave_core = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `caller:int`, `st:cm_src_state`,
      annotation, `oldenv:int->int->cm_value`, `oldfp:int`,
      `oldregions:(cm_region)list`, `ret:cm_type`, `owner:int`,
      `saved_break:int`, `saved_continue:int`,
      `rest:(cm_acursor)list`,
      `cm_spill_frame_spills
        (HD (saved0:(cm_spill_frame)list))`,
      `TL (saved0:(cm_spill_frame)list)`,
      `cm_call_sim_return
        (HD (calls0:(cm_call_sim_frame)list))`,
      `TL (calls0:(cm_call_sim_frame)list)`,
      `cm_call_sim_return
        (HD (calls0:(cm_call_sim_frame)list))`),
      cm_runtime_core_leave_call);
  leave_core = match_mp_rule(leave_core, cursor_shape);
  leave_core = match_mp_rule(leave_core, saved_ann_shape);
  leave_core = match_mp_rule(leave_core, calls_ann_shape);
  leave_core = match_mp_rule(leave_core, core);
  thm leave_opened = conv_rule(rewrite_conv(
      THM_LIST(cm_runtime_core_def)), leave_core);
  thm restored_stack = conjunct2_rule(leave_opened);
  thm outside = match_mp_rule(
      get_cm_scratch_outside_live(), restored_stack);

  thm generation_opened = conv_rule(rewrite_conv(
      THM_LIST(cm_task_generation_safe_def)), generation);
  thm task_generation = conjunct1_rule(generation_opened);
  thm annotation_generation = conjunct2_rule(generation_opened);
  thm task_generation_opened = conv_rule(
      reduce_rewrite_conv(THM_LIST(cm_task_generation_below_def)),
      task_generation);
  thm state_generation = cm_target_call_pick(task_generation_opened,
      `cm_state_generation_below (p:cm_program) (fid:int)
        (st:cm_src_state)`);
  thm control_below = cm_target_call_pick(task_generation_opened,
      `cm_control_generation_below
        (cm_state_nextgen (st:cm_src_state)) (ctl:cm_control)`);
  thm state_generation_opened = conv_rule(rewrite_conv(
      THM_LIST(cm_state_generation_below_def)), state_generation);
  thm all_tags_below = cm_target_call_pick(state_generation_opened,
      `cm_tags_generation_below (cm_state_nextgen (st:cm_src_state))
        (cm_state_tags st)`);
  thm tag_below = match_mp_rule(specl_rule(TERM_LIST(
      `st:cm_src_state`, `cm_state_nextgen (st:cm_src_state)`),
      get_cm_state_tags_generation_from_all()), all_tags_below);
  thm annotation_generation_opened = conv_rule(
      reduce_rewrite_conv(THM_LIST(
        cm_annotation_generation_below_def,
        cm_active_spill_frames_def, cm_ann_spills_def,
        cm_ann_saved_def, cm_spill_frames_generation_below_def)),
      annotation_generation);
  thm saved_below = cm_target_call_pick(annotation_generation_opened,
      `cm_spill_frames_generation_below
        (cm_state_nextgen (st:cm_src_state))
        (saved0:(cm_spill_frame)list)`);
  thm saved_below_view = beta_norm(ap_term_rule(
      `\(frames:(cm_spill_frame)list).
         cm_spill_frames_generation_below
           (cm_state_nextgen (st:cm_src_state)) frames`,
      saved_shape));
  thm saved_below_shaped =
      eq_mp_rule(saved_below_view, saved_below);

  thm typed_opened = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_task_type_ready_def, cm_ann_cursors_def)), typed);
  thm cursors_typed = cm_target_call_pick(typed_opened,
      `cm_cursors_type_ready (p:cm_program) (fid:int)
        ${cursors:(cm_acursor)list}`);
  thm cursors_typed_opened = conv_rule(rewrite_conv(THM_LIST(
      cm_cursors_type_ready_def, cm_cursor_phase_def)), cursors_typed);
  thm static_typed = conjunct1_rule(cursors_typed_opened);
  thm static_typed_opened = conv_rule(rewrite_conv(
      THM_LIST(cm_phase_static_type_ready_def)), static_typed);
  thm ret_equal = cm_target_call_pick(static_typed_opened,
      `(ret:cm_type) ==
       cm_function_ret
         (inth (fid:int) (cm_program_functions (p:cm_program)))`);

  thm fp_bounds = match_mp_rule(cm_runtime_stack_fp_bounds, stack);
  thm frame_opened = conv_rule(rewrite_conv(
      THM_LIST(cm_frame_segment_def)), frame_segment);
  thm fp_signed_raw = mp_rule(int_arith_rule(mk_imp(
      concl(fp_bounds),
      `--9223372036854775808i <=
         cm_state_fp (st:cm_src_state) &&
       cm_state_fp st <= 9223372036854775807i`)), fp_bounds);
  thm fp_signed = eq_mp_rule(sym_rule(apply_conversion(
      rewrite_conv(THM_LIST(get_tower_signed64_def())),
      `tower_signed64 (cm_state_fp (st:cm_src_state))`)),
      fp_signed_raw);
  thm oldfp_signed_raw = mp_rule(int_arith_rule(mk_imp(
      concl(frame_opened),
      `--9223372036854775808i <= (oldfp:int) &&
       oldfp <= 9223372036854775807i`)), frame_opened);
  thm oldfp_signed = eq_mp_rule(sym_rule(apply_conversion(
      rewrite_conv(THM_LIST(get_tower_signed64_def())),
      `tower_signed64 (oldfp:int)`)), oldfp_signed_raw);
  thm fp_word_raw = mp_rule(int_arith_rule(mk_imp(
      concl(frame_opened),
      `0i <= cm_state_fp (st:cm_src_state) &&
       cm_state_fp st + 7i < 1048576i`)), frame_opened);
  thm fp_word = eq_mp_rule(sym_rule(apply_conversion(
      rewrite_conv(THM_LIST(get_tower_word_valid_def())),
      `tower_word_valid (cm_state_fp (st:cm_src_state))`)),
      fp_word_raw);

  thm lower = match_mp_rule(cm_runtime_stack_lower, stack);
  thm calls_lower = conjunct1_rule(lower);
  thm saved_lower = conjunct2_rule(conjunct2_rule(lower));
  thm calls_lower_view = beta_norm(ap_term_rule(
      `\(frames:(cm_call_sim_frame)list).
         cm_call_frames_lower
           (cm_state_fp (st:cm_src_state)) frames`,
      calls_shape));
  thm calls_lower_shaped =
      eq_mp_rule(calls_lower_view, calls_lower);
  thm calls_lower_opened = conv_rule(rewrite_conv(
      THM_LIST(cm_call_frames_lower_def)), calls_lower_shaped);
  thm tail_calls_lower = conjunct2_rule(calls_lower_opened);
  thm scratch_below = mp_rule(int_arith_rule(mk_imp(
      concl(fp_bounds),
      `8i + 8i <= cm_state_fp (st:cm_src_state)`)), fp_bounds);
  thm call_range_safe = match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(
        `8i:int`, `8i:int`, `cm_state_fp (st:cm_src_state)`,
        `TL (calls0:(cm_call_sim_frame)list)`),
        cm_call_lower_range_safe),
      scratch_below), tail_calls_lower);
  thm spill_range_safe = match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(
        `p:cm_program`, `8i:int`, `8i:int`,
        `cm_state_fp (st:cm_src_state)`,
        `saved0:(cm_spill_frame)list`),
        cm_spill_frames_lower_range_safe),
      scratch_below), saved_lower);
  thm store_upper = cm_target_call_true(
      `8i + cm_store_width CMIntTy <= 8i + 8i`,
      THM_LIST(get_cm_store_width_def(),
        get_cm_type_int_char_distinct()));
  thm calls_safe = match_mp_rule(match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(
        `8i:int`, `8i:int`, `8i:int`, `CMIntTy:cm_type`,
        `TL (calls0:(cm_call_sim_frame)list)`),
        cm_call_frames_range_subrange),
      int_arith_rule(`8i <= 8i`)), store_upper), call_range_safe);
  thm spills_safe = match_mp_rule(match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(
        `p:cm_program`, `8i:int`, `8i:int`, `8i:int`,
        `CMIntTy:cm_type`, `saved0:(cm_spill_frame)list`),
        cm_spill_frames_range_subrange),
      int_arith_rule(`8i <= 8i`)), store_upper), spill_range_safe);
  thm spills_safe_view = beta_norm(ap_term_rule(
      `\(frames:(cm_spill_frame)list).
         cm_spill_frames_store_safe
           (p:cm_program) CMIntTy 8i frames`,
      saved_shape));
  thm spills_safe_shaped =
      eq_mp_rule(spills_safe_view, spills_safe);

  thm span_valid = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`,
      `cm_state_fp (st:cm_src_state)`, `st:cm_src_state`,
      `oldenv:int->int->cm_value`, `oldfp:int`,
      `oldregions:(cm_region)list`),
      cm_tagged_span_restore_call), prefix), tagged);

  gnode_list control_cases = DISJ_CASES_TAC(introduced,
      ispec_rule(`ctl:cm_control`, get_datatype_cases("cm_control")),
      "Hcontrol");
  for (size_t i = 0; i < vector_size(control_cases); ++i) {
    gnode branch = control_cases[i];
    while (is_exists(goal_lasmps(branch->g)[
        labeled_term_list_index(goal_lasmps(branch->g),
          "Hcontrol")].tm)) {
      branch = ASMP_EXISTS_TAC(branch, "Hcontrol", NULL);
    }
    thm control_shape = assume_rule(goal_lasmps(branch->g)[
        labeled_term_list_index(goal_lasmps(branch->g),
          "Hcontrol")].tm);
    term concrete_control = rhs_of(control_shape);
    if (i != 0 && i != 3) {
      thm impossible = conv_rule(reduce_rewrite_conv(THM_LIST(
          control_shape, get_cm_control_kind_def())), allowed);
      CONTR_TAC(branch, impossible);
      continue;
    }

    thm code0 = cm_target_call_layout_code(
        layout, control_shape, concrete_control, i, annotation);
    thm running0 = cm_target_call_running(
        sim, control_shape, concrete_control, annotation, i);
    term raw_value = i == 3
        ? `cm_control_value ${concrete_control:cm_control}`
        : `CMIntV 0i`;
    thm raw_below;
    if (i == 3) {
      thm concrete_below = conv_rule(
          rewrite_conv(THM_LIST(control_shape)), control_below);
      raw_below = match_mp_rule(specl_rule(TERM_LIST(
          concrete_control,
          `cm_state_nextgen (st:cm_src_state)`),
          cm_control_value_generation_below), concrete_below);
    } else {
      raw_below = eqt_elim_rule(apply_conversion(
          reduce_rewrite_conv(THM_LIST(
            cm_value_generation_below_def)),
          `cm_value_generation_below
            (cm_state_nextgen (st:cm_src_state)) (CMIntV 0i)`));
    }

    term old_value =
        `cm_convert_value (st:cm_src_state)
          (cm_function_ret
            (inth (fid:int) (cm_program_functions (p:cm_program))))
          ${raw_value:cm_value}`;
    term restored =
        `cm_restore_call (st:cm_src_state)
          (oldenv:int->int->cm_value) (oldfp:int)
          (oldregions:(cm_region)list)`;
    term new_value =
        `cm_convert_value ${restored:cm_src_state}
          (cm_function_ret
            (inth (fid:int) (cm_program_functions (p:cm_program))))
          ${raw_value:cm_value}`;
    thm old_value_below = match_mp_rule(specl_rule(TERM_LIST(
        `st:cm_src_state`,
        `cm_function_ret
          (inth (fid:int) (cm_program_functions (p:cm_program)))`,
        raw_value, `cm_state_nextgen (st:cm_src_state)`),
        get_cm_convert_generation_below()), raw_below);
    term epilogue_ann;
    term epilogue_target;
    thm epilogue_code;
    thm running_value;

    if (i == 0) {
      term pushed_ann =
          `cm_ann_linear (cm_push_code 0i)
            ${annotation:cm_annotation}`;
      term pushed_target = `tvm_iter 1 (target:tvm_task)`;
      thm push_bridge = eqt_elim_rule(apply_conversion(
          reduce_rewrite_conv(THM_LIST(
            get_cm_value_number_def(), get_tower_wrap64_def())),
          `tower_wrap64 0i ==
           cm_value_number (st:cm_src_state) (CMIntV 0i)`));
      thm capacity = eqt_elim_rule(apply_conversion(
          reduce_rewrite_conv(THM_LIST(
            get_theorem_by_name("ILENGTH_DEF"))),
          `ilength ([]:(cm_value)list) < 65536i`));
      thm pushed = specl_rule(TERM_LIST(
          `p:cm_program`, `fid:int`, `st:cm_src_state`,
          `[]:(cm_value)list`, annotation, `target:tvm_task`,
          `CMIntV 0i`, `0i:int`, `cm_return_epilogue`),
          get_cm_target_push());
      pushed = match_mp_rule(pushed,
          conv_rule(reduce_rewrite_conv(THM_LIST(
            get_cm_push_code_def(), get_theorem_by_name("APPEND"))),
            code0));
      pushed = match_mp_rule(pushed, running0);
      pushed = match_mp_rule(pushed, capacity);
      pushed = match_mp_rule(pushed, push_bridge);
      thm zero_bridge = specl_rule(TERM_LIST(
          `st:cm_src_state`,
          `cm_function_ret
            (inth (fid:int) (cm_program_functions (p:cm_program)))`,
          `CMIntV 0i`), get_cm_convert_value_number_bridge());
      thm_list zero_rules = THM_LIST(
          get_cm_value_number_def(), get_tower_wrap64_def(),
          get_tower_u8_def(), get_theorem_by_name("COND_ID"));
      thm normalized_zero_bridge =
          conv_rule(reduce_rewrite_conv(zero_rules), zero_bridge);
      normalized_zero_bridge =
          conv_rule(reduce_rewrite_conv(zero_rules),
            normalized_zero_bridge);
      thm zero_number = cm_target_call_true(
          `cm_value_number (st:cm_src_state) (CMIntV 0i) == 0i`,
          zero_rules);
      thm zero_equal =
          trans_rule(zero_number, sym_rule(normalized_zero_bridge));
      thm revalued = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
          `p:cm_program`, `fid:int`, `st:cm_src_state`,
          `CMIntV 0i`, old_value, `[]:(cm_value)list`,
          pushed_ann, pushed_target), get_cm_target_revalue()),
          zero_equal), pushed);
      epilogue_ann = pushed_ann;
      epilogue_target = pushed_target;
      epilogue_code = cm_target_call_code_suffix(code0,
          annotation, `cm_push_code 0i`, `cm_return_epilogue`,
          pushed_ann);
      running_value = revalued;
    } else {
      term char_code =
          `cm_char_normalize_code
            (cm_function_ret
              (inth (fid:int) (cm_program_functions (p:cm_program))))`;
      term char_ann =
          `cm_ann_linear ${char_code:(tvm_inst)list}
            ${annotation:cm_annotation}`;
      term char_target =
          `tvm_iter (cm_code_steps ${char_code:(tvm_inst)list})
            (target:tvm_task)`;
      thm capacity = eqt_elim_rule(apply_conversion(
          reduce_rewrite_conv(THM_LIST(
            get_theorem_by_name("ILENGTH_DEF"))),
          `ilength ([]:(cm_value)list) < 65535i`));
      thm normalized_value = specl_rule(TERM_LIST(
          `p:cm_program`, `fid:int`, `st:cm_src_state`,
          `cm_function_ret
            (inth (fid:int) (cm_program_functions (p:cm_program)))`,
          raw_value, `[]:(cm_value)list`, annotation,
          `target:tvm_task`, `cm_return_epilogue`),
          get_cm_target_char_normalize());
      normalized_value = match_mp_rule(normalized_value, code0);
      normalized_value = match_mp_rule(normalized_value, running0);
      normalized_value = match_mp_rule(normalized_value, capacity);
      normalized_value = match_mp_rule(normalized_value,
          specl_rule(TERM_LIST(`st:cm_src_state`, raw_value),
            get_cm_value_number_signed_bridge()));
      epilogue_ann = char_ann;
      epilogue_target = char_target;
      epilogue_code = cm_target_call_code_suffix(code0,
          annotation, char_code, `cm_return_epilogue`, char_ann);
      running_value = normalized_value;
    }

    thm returned = cm_target_call_apply_epilogue(
        epilogue_ann, epilogue_target, old_value,
        epilogue_code, calls_shape, saved_shape, prefix,
        tag_below, saved_below_shaped, old_value_below,
        span_valid, outside, calls_safe, spills_safe_shaped,
        fp_signed, fp_word, oldfp_signed, running_value);
    term final_ann =
        `cm_ann_leave_call
          (cm_call_sim_return
            (HD (calls0:(cm_call_sim_frame)list)))
          ${annotation:cm_annotation}`;
    term final_target =
        `tvm_iter 6 ${epilogue_target:tvm_task}`;
    thm returned_normal = conv_rule(
        reduce_rewrite_conv(cm_target_call_annotation_rules()),
        returned);
    thm returned_view = apply_conversion(
        reduce_rewrite_conv(cm_target_call_annotation_rules()),
        `cm_running_target_sim (p:cm_program) (caller:int)
          ${restored:cm_src_state} [${old_value:cm_value}]
          ${final_ann:cm_annotation} ${final_target:tvm_task}`);
    returned =
        eq_mp_rule(sym_rule(returned_view), returned_normal);
    thm number_transport = match_mp_rule(match_mp_rule(
        specl_rule(TERM_LIST(
          `p:cm_program`, `fid:int`, `st:cm_src_state`,
          `oldenv:int->int->cm_value`, `oldfp:int`,
          `oldregions:(cm_region)list`,
          `cm_function_ret
            (inth (fid:int) (cm_program_functions (p:cm_program)))`,
          raw_value), cm_convert_restore_number),
        prefix), raw_below);
    thm final_result = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
        `p:cm_program`, `caller:int`, restored, old_value, new_value,
        `[]:(cm_value)list`, final_ann, final_target),
        get_cm_target_revalue()), number_transport), returned);
    cm_target_call_accept(branch, final_result,
        control_shape, ret_equal);
  }
  return gnode_prove(root);
}
PROOF thm cm_target_c_call_step =
    cm_prove_target_c_call_step();

PROOF thm get_cm_target_c_call_step(void) {
  return cm_target_c_call_step;
}

PROOF static int cmc_preservation_target_control_call_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_target_control_call_axioms_before,
      "cmc_preservation_target_control_call introduced an axiom");
  ENSURE_COND(vector_size(hyp(cm_target_c_call_step)) == 0,
      "call-control target theorem has hypotheses");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_target_control_call_checks =
    cmc_preservation_target_control_call_final_checks();
