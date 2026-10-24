#include "proof/proof.h"
#include "userlib/proof.h"
#include "cmc_preservation_target_value_binary_pointer.h"
#include "cmc_preservation_target_value_binary.h"
#include "cmc_preservation_target_machine.h"
#include "cmc_preservation_target_spill.h"
#include "cmc_preservation_code_value.h"
#include "cmc_preservation_code_expr.h"

#require "cmc_preservation_target_value_binary.c"

PROOF static size_t
    _cmc_preservation_target_value_binary_pointer_axioms_before =
        vector_size(get_all_axioms());

PROOF static thm cm_target_pointer_code_suffix(
    const thm current_code, const term code,
    const term current_ann, const term prefix,
    const term suffix, const term next_ann,
    const thm_list rules) {
  thm current_normal =
      conv_rule(reduce_rewrite_conv(rules), current_code);
  thm tail_rule = ispecl_rule(TERM_LIST(
      code, `cm_ann_pc ${current_ann:cm_annotation}`,
      prefix, suffix), get_cm_code_at_append_right());
  thm tail_raw = mp_rule(
      conv_rule(reduce_rewrite_conv(rules), tail_rule),
      current_normal);
  thm tail_normal =
      conv_rule(reduce_rewrite_conv(rules), tail_raw);
  thm tail_view = apply_conversion(
      reduce_rewrite_conv(rules),
      `cm_code_at ${code:(tvm_inst)list}
        (cm_ann_pc ${next_ann:cm_annotation})
        ${suffix:(tvm_inst)list}`);
  return eq_mp_rule(sym_rule(tail_view), tail_normal);
}

PROOF static thm cm_target_pointer_push_step(
    const thm original_code, const term code,
    const term base_ann, const term prefix, const term suffix,
    const term current_ann, const term current_target,
    const thm current_sim, const term values, const term value,
    const term immediate, const term rest, const thm capacity,
    const thm number_equal, const thm_list rules) {
  thm code_at = cm_target_pointer_code_suffix(
      original_code, code, base_ann, prefix, suffix,
      current_ann, rules);
  code_at = conv_rule(reduce_rewrite_conv(rules), code_at);
  thm result = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`, values,
      current_ann, current_target, value, immediate, rest),
      get_cm_target_push());
  result = conv_rule(reduce_rewrite_conv(rules), result);
  result = match_mp_rule(result, code_at);
  result = match_mp_rule(result,
      conv_rule(reduce_rewrite_conv(rules), current_sim));
  return match_mp_rule(result, number_equal);
}

PROOF static thm cm_target_pointer_swap_step(
    const thm original_code, const term code,
    const term base_ann, const term prefix, const term suffix,
    const term current_ann, const term current_target,
    const thm current_sim, const term first, const term second,
    const term values, const term rest, const thm_list rules) {
  thm code_at = cm_target_pointer_code_suffix(
      original_code, code, base_ann, prefix, suffix,
      current_ann, rules);
  code_at = conv_rule(reduce_rewrite_conv(rules), code_at);
  thm result = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`, first, second,
      values, current_ann, current_target, rest),
      get_cm_target_swap());
  result = conv_rule(reduce_rewrite_conv(rules), result);
  result = match_mp_rule(result, code_at);
  return match_mp_rule(result,
      conv_rule(reduce_rewrite_conv(rules), current_sim));
}

PROOF static thm cm_target_pointer_binary_step(
    const bool nonzero, const thm original_code, const term code,
    const term base_ann, const term prefix, const term suffix,
    const term current_ann, const term current_target,
    const thm current_sim, const term right, const term left,
    const term values, const term opcode, const term operation,
    const term result_value, const term rest, const thm transition,
    const thm number_equal, const thm nonzero_fact,
    const thm_list rules) {
  thm code_at = cm_target_pointer_code_suffix(
      original_code, code, base_ann, prefix, suffix,
      current_ann, rules);
  code_at = conv_rule(reduce_rewrite_conv(rules), code_at);
  thm result = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`, right, left,
      values, current_ann, current_target, opcode, operation,
      result_value, rest),
      nonzero ? get_cm_target_binary_nonzero()
              : get_cm_target_binary_total());
  result = match_mp_rule(result, transition);
  result = conv_rule(reduce_rewrite_conv(rules), result);
  result = match_mp_rule(result, code_at);
  result = match_mp_rule(result,
      conv_rule(reduce_rewrite_conv(rules), current_sim));
  if (nonzero) {
    result = match_mp_rule(result, nonzero_fact);
  }
  return match_mp_rule(result, number_equal);
}

PROOF static thm cm_prove_target_v_bin_r_pointer(const int mode) {
  bool add_case = mode < 2;
  term op_value = add_case ? `8i:int` : `9i:int`;
  term task =
      `CMVTask (p:cm_program) (fid:int) (v:cm_value)
        (st:cm_src_state)
        (CMBinRK ${op_value:int} (left_value:cm_value) (ty:cm_type) ::
         cm_cursor_frames (rest:(cm_acursor)list))`;
  term ann =
      `CMAnnotation (pc:int) (temp:int) (breakpc:int) (continuepc:int)
        (CMACursor
          (CABinRP ${op_value:int} (left:cm_expr) (right:cm_expr)
            (left_value:cm_value) (ty:cm_type))
          (owner:int) (saved_break:int) (saved_continue:int) ::
         (rest:(cm_acursor)list))
        (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
        (calls:(cm_call_sim_frame)list)`;
  term finish_code =
      `cm_binary_finish_code (p:cm_program) (fid:int) ${op_value:int}
        (left:cm_expr) (right:cm_expr) (owner:int)`;
  term semantic_result =
      `cm_binary_value (p:cm_program) ${op_value:int}
        (left_value:cm_value) (v:cm_value) (ty:cm_type)
        (st:cm_src_state)`;
  term scale = mode == 0
      ? `cm_pointer_scale (p:cm_program) (right:cm_expr)`
      : `cm_pointer_scale (p:cm_program) (left:cm_expr)`;
  term scale_value = `CMIntV ${scale:int}`;
  term left_number =
      `cm_value_number (st:cm_src_state) (left_value:cm_value)`;
  term right_number =
      `cm_value_number (st:cm_src_state) (v:cm_value)`;
  term intermediate = mode == 2
      ? `CMIntV
          (tower_sub ${left_number:int} ${right_number:int})`
      : (mode == 0
          ? `CMIntV
              (tower_mul ${left_number:int} ${scale:int})`
          : `CMIntV
              (tower_mul ${right_number:int} ${scale:int})`);
  term inst0 = mode == 0
      ? `TVMInst TVMPushOp ${scale:int}`
      : `TVMInst TVMSwapOp 0i`;
  term inst1 = mode == 0
      ? `TVMInst TVMMulOp 0i`
      : (mode == 2
          ? `TVMInst TVMSubOp 0i`
          : `TVMInst TVMPushOp ${scale:int}`);
  term inst2 = mode == 0
      ? `TVMInst TVMSwapOp 0i`
      : (mode == 2
          ? `TVMInst TVMPushOp ${scale:int}`
          : `TVMInst TVMMulOp 0i`);
  term inst3 = mode < 2
      ? `TVMInst TVMAddOp 0i`
      : (mode == 2
          ? `TVMInst TVMDivOp 0i`
          : `TVMInst TVMSubOp 0i`);
  term instructions =
      `${inst0:tvm_inst} :: ${inst1:tvm_inst} ::
       ${inst2:tvm_inst} :: ${inst3:tvm_inst} :: []`;
  term final_equal;
  if (mode == 0) {
    final_equal =
        `tower_add
           (cm_value_number (st:cm_src_state)
             ${intermediate:cm_value})
           ${right_number:int} ==
         cm_value_number st ${semantic_result:cm_value}`;
  } else if (mode == 1) {
    final_equal =
        `tower_add ${left_number:int}
           (cm_value_number (st:cm_src_state)
             ${intermediate:cm_value}) ==
         cm_value_number st ${semantic_result:cm_value}`;
  } else if (mode == 2) {
    final_equal =
        `tower_div
           (cm_value_number (st:cm_src_state)
             ${intermediate:cm_value})
           (cm_value_number st ${scale_value:cm_value}) ==
         cm_value_number st ${semantic_result:cm_value}`;
  } else {
    final_equal =
        `tower_sub ${left_number:int}
           (cm_value_number (st:cm_src_state)
             ${intermediate:cm_value}) ==
         cm_value_number st ${semantic_result:cm_value}`;
  }
  term shape_term =
      `${finish_code:(tvm_inst)list} ==
       cm_temp_load_code (p:cm_program) (fid:int) (owner:int) ++
       ${instructions:(tvm_inst)list}`;
  term_list premises = TERM_LIST(
      `cm_task_layout (p:cm_program) ${task:cm_task}
        ${ann:cm_annotation}`,
      `cm_task_target_sim (p:cm_program) ${task:cm_task}
        (target:tvm_task) ${ann:cm_annotation}`,
      `cm_binary_ok (p:cm_program) ${op_value:int}
        (left_value:cm_value) (v:cm_value) (st:cm_src_state)`,
      `cm_spill_holds (owner:int) (left_value:cm_value)
        (spills:(cm_spill)list)`,
      `(temp:int) == (owner:int) + 1i`,
      shape_term,
      `tower_wrap64 ${scale:int} == ${scale:int}`,
      final_equal,
      `tower_signed64 (cm_state_fp (st:cm_src_state))`,
      `tower_signed64
        (cm_temp_offset (p:cm_program) (fid:int) (owner:int))`,
      `(address:int) == cm_state_fp st + cm_temp_offset p fid owner`,
      `tower_signed64 (address:int)`,
      `tower_word_valid (address:int)`);
  if (mode == 2) {
    vector_add(&premises, `~(${scale:int} == 0i)`);
  }
  term body = imp_chain(premises,
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
  thm layout = assume_rule(
      `cm_task_layout (p:cm_program) ${task:cm_task}
        ${ann:cm_annotation}`);
  thm code_at = conjunct1_rule(conv_rule(
      reduce_rewrite_conv(cm_v_layout_rules()), layout));
  thm running = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_task_target_sim_def)), assume_rule(
        `cm_task_target_sim (p:cm_program) ${task:cm_task}
          (target:tvm_task) ${ann:cm_annotation}`));
  thm shape = assume_rule(shape_term);
  thm scale_fixed = assume_rule(
      `tower_wrap64 ${scale:int} == ${scale:int}`);
  term continuation =
      `cm_cursor_code (p:cm_program) (fid:int)
        ((pc:int) + ilength ${finish_code:(tvm_inst)list})
        (owner:int) F (rest:(cm_acursor)list)`;
  term suffix0 =
      `${inst0:tvm_inst} :: ${inst1:tvm_inst} ::
       ${inst2:tvm_inst} :: ${inst3:tvm_inst} ::
       ${continuation:(tvm_inst)list}`;
  thm loaded = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`, `owner:int`,
      `left_value:cm_value`, `[v:cm_value]`, ann,
      `target:tvm_task`, suffix0, `address:int`),
      get_cm_target_temp_load());
  thm_list rules = cm_v_layout_rules();
  vector_add(&rules, shape);
  vector_add(&rules, cm_active_spill_frames_def);
  vector_add(&rules, cm_ann_linear_def);
  vector_add(&rules, cm_ann_plain_def);
  vector_add(&rules, cm_ann_pc_def);
  vector_add(&rules, cm_ann_temp_def);
  vector_add(&rules, cm_ann_break_def);
  vector_add(&rules, cm_ann_continue_def);
  vector_add(&rules, cm_ann_cursors_def);
  vector_add(&rules, cm_ann_spills_def);
  vector_add(&rules, cm_ann_saved_def);
  vector_add(&rules, cm_ann_calls_def);
  vector_add(&rules, get_cm_layout_temp_load_length());
  vector_add(&rules, get_theorem_by_name("ILENGTH_APPEND"));
  vector_add(&rules, get_theorem_by_name("ILENGTH_DEF"));
  vector_add(&rules, get_theorem_by_name("APPEND"));
  vector_add(&rules, get_theorem_by_name("APPEND_NIL"));
  code_at = conv_rule(reduce_rewrite_conv(rules), code_at);
  loaded = conv_rule(reduce_rewrite_conv(rules), loaded);
  loaded = match_mp_rule(loaded, code_at);
  loaded = match_mp_rule(loaded, running);
  vector_add(&rules, get_cm_push_code_def());
  vector_add(&rules, get_theorem_by_name("ILENGTH_DEF"));
  loaded = match_mp_rule(loaded, assume_rule(
      `cm_spill_holds (owner:int) (left_value:cm_value)
        (spills:(cm_spill)list)`));
  loaded = match_mp_rule(loaded, assume_rule(
      `tower_signed64 (cm_state_fp (st:cm_src_state))`));
  loaded = match_mp_rule(loaded, assume_rule(
      `tower_signed64
        (cm_temp_offset (p:cm_program) (fid:int) (owner:int))`));
  loaded = match_mp_rule(loaded, assume_rule(
      `(address:int) == cm_state_fp (st:cm_src_state) +
        cm_temp_offset (p:cm_program) (fid:int) (owner:int)`));
  loaded = match_mp_rule(loaded,
      assume_rule(`tower_signed64 (address:int)`));
  loaded = match_mp_rule(loaded,
      assume_rule(`tower_word_valid (address:int)`));

  term load_code =
      `cm_temp_load_code (p:cm_program) (fid:int) (owner:int)`;
  term ann0 = `cm_ann_linear ${load_code:(tvm_inst)list}
      ${ann:cm_annotation}`;
  term ann1 = `cm_ann_linear [${inst0:tvm_inst}]
      ${ann0:cm_annotation}`;
  term ann2 = `cm_ann_linear [${inst1:tvm_inst}]
      ${ann1:cm_annotation}`;
  term ann3 = `cm_ann_linear [${inst2:tvm_inst}]
      ${ann2:cm_annotation}`;
  term ann4 = `cm_ann_linear [${inst3:tvm_inst}]
      ${ann3:cm_annotation}`;
  term prefix0 = load_code;
  term prefix1 =
      `${load_code:(tvm_inst)list} ++ [${inst0:tvm_inst}]`;
  term prefix2 =
      `${load_code:(tvm_inst)list} ++
       [${inst0:tvm_inst}; ${inst1:tvm_inst}]`;
  term prefix3 =
      `${load_code:(tvm_inst)list} ++
       [${inst0:tvm_inst}; ${inst1:tvm_inst}; ${inst2:tvm_inst}]`;
  term suffix1 =
      `${inst1:tvm_inst} :: ${inst2:tvm_inst} ::
       ${inst3:tvm_inst} :: ${continuation:(tvm_inst)list}`;
  term suffix2 =
      `${inst2:tvm_inst} :: ${inst3:tvm_inst} ::
       ${continuation:(tvm_inst)list}`;
  term suffix3 =
      `${inst3:tvm_inst} :: ${continuation:(tvm_inst)list}`;
  term target0 = `tvm_iter 5 (target:tvm_task)`;
  term target1 = `tvm_iter 1 ${target0:tvm_task}`;
  term target2 = `tvm_iter 1 ${target1:tvm_task}`;
  term target3 = `tvm_iter 1 ${target2:tvm_task}`;
  thm capacity_one = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(get_theorem_by_name("ILENGTH_DEF"))),
      `ilength [${intermediate:cm_value}] < 65536i`));
  thm capacity_two = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(get_theorem_by_name("ILENGTH_DEF"))),
      `ilength
        [left_value:cm_value; v:cm_value] < 65536i`));
  thm capacity_swapped = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(get_theorem_by_name("ILENGTH_DEF"))),
      `ilength
        [v:cm_value; left_value:cm_value] < 65536i`));
  thm scale_number = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(get_cm_value_number_def())),
      `tower_wrap64 ${scale:int} ==
       cm_value_number (st:cm_src_state) ${scale_value:cm_value}`));
  thm intermediate_equal;
  if (mode == 0) {
    intermediate_equal = eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          get_cm_value_number_def(),
          get_tower_mul_def(),
          get_tower_wrap64_idempotent(), scale_fixed)),
        `tower_mul ${left_number:int}
            (cm_value_number (st:cm_src_state)
              ${scale_value:cm_value}) ==
         cm_value_number st ${intermediate:cm_value}`));
  } else if (mode == 2) {
    intermediate_equal = eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          get_cm_value_number_def(),
          get_tower_sub_def(),
          get_tower_wrap64_idempotent())),
        `tower_sub ${left_number:int} ${right_number:int} ==
         cm_value_number (st:cm_src_state)
           ${intermediate:cm_value}`));
  } else {
    intermediate_equal = eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          get_cm_value_number_def(),
          get_tower_mul_def(),
          get_tower_wrap64_idempotent(), scale_fixed)),
        `tower_mul ${right_number:int}
            (cm_value_number (st:cm_src_state)
              ${scale_value:cm_value}) ==
         cm_value_number st ${intermediate:cm_value}`));
  }
  thm final_number = assume_rule(final_equal);
  thm scale_nonzero = empty_theorem;
  if (mode == 2) {
    thm raw_nonzero = assume_rule(`~(${scale:int} == 0i)`);
    term target_nonzero =
        `~(cm_value_number (st:cm_src_state)
             ${scale_value:cm_value} == 0i)`;
    thm nonzero_view = apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          get_cm_value_number_def(), scale_fixed)),
        target_nonzero);
    scale_nonzero =
        eq_mp_rule(sym_rule(nonzero_view), raw_nonzero);
  }

  thm sim1;
  thm sim2;
  thm sim3;
  thm sim4;
  if (mode == 0) {
    sim1 = cm_target_pointer_push_step(
        code_at, `cm_model_code (p:cm_program)`, ann,
        prefix0, suffix0, ann0, target0, loaded,
        `[left_value:cm_value; v:cm_value]`,
        scale_value, scale, suffix1, capacity_two, scale_number, rules);
    sim2 = cm_target_pointer_binary_step(
        false, code_at, `cm_model_code (p:cm_program)`, ann,
        prefix1, suffix1, ann1, target1, sim1,
        scale_value, `left_value:cm_value`, `[v:cm_value]`,
        `TVMMulOp:tvm_opcode`, `tower_mul:int->int->int`,
        intermediate, suffix2, get_tvm_mul_transition(),
        intermediate_equal, empty_theorem, rules);
    sim3 = cm_target_pointer_swap_step(
        code_at, `cm_model_code (p:cm_program)`, ann,
        prefix2, suffix2, ann2, target2, sim2,
        intermediate, `v:cm_value`, `[]:(cm_value)list`,
        suffix3, rules);
    sim4 = cm_target_pointer_binary_step(
        false, code_at, `cm_model_code (p:cm_program)`, ann,
        prefix3, suffix3, ann3, target3, sim3,
        `v:cm_value`, intermediate, `[]:(cm_value)list`,
        `TVMAddOp:tvm_opcode`, `tower_add:int->int->int`,
        semantic_result, continuation, get_tvm_add_transition(),
        final_number, empty_theorem, rules);
  } else if (mode == 1) {
    sim1 = cm_target_pointer_swap_step(
        code_at, `cm_model_code (p:cm_program)`, ann,
        prefix0, suffix0, ann0, target0, loaded,
        `left_value:cm_value`, `v:cm_value`, `[]:(cm_value)list`,
        suffix1, rules);
    sim2 = cm_target_pointer_push_step(
        code_at, `cm_model_code (p:cm_program)`, ann,
        prefix1, suffix1, ann1, target1, sim1,
        `[v:cm_value; left_value:cm_value]`,
        scale_value, scale, suffix2, capacity_swapped,
        scale_number, rules);
    sim3 = cm_target_pointer_binary_step(
        false, code_at, `cm_model_code (p:cm_program)`, ann,
        prefix2, suffix2, ann2, target2, sim2,
        scale_value, `v:cm_value`, `[left_value:cm_value]`,
        `TVMMulOp:tvm_opcode`, `tower_mul:int->int->int`,
        intermediate, suffix3, get_tvm_mul_transition(),
        intermediate_equal, empty_theorem, rules);
    sim4 = cm_target_pointer_binary_step(
        false, code_at, `cm_model_code (p:cm_program)`, ann,
        prefix3, suffix3, ann3, target3, sim3,
        intermediate, `left_value:cm_value`, `[]:(cm_value)list`,
        `TVMAddOp:tvm_opcode`, `tower_add:int->int->int`,
        semantic_result, continuation, get_tvm_add_transition(),
        final_number, empty_theorem, rules);
  } else if (mode == 2) {
    sim1 = cm_target_pointer_swap_step(
        code_at, `cm_model_code (p:cm_program)`, ann,
        prefix0, suffix0, ann0, target0, loaded,
        `left_value:cm_value`, `v:cm_value`, `[]:(cm_value)list`,
        suffix1, rules);
    sim2 = cm_target_pointer_binary_step(
        false, code_at, `cm_model_code (p:cm_program)`, ann,
        prefix1, suffix1, ann1, target1, sim1,
        `v:cm_value`, `left_value:cm_value`, `[]:(cm_value)list`,
        `TVMSubOp:tvm_opcode`, `tower_sub:int->int->int`,
        intermediate, suffix2, get_tvm_sub_transition(),
        intermediate_equal, empty_theorem, rules);
    sim3 = cm_target_pointer_push_step(
        code_at, `cm_model_code (p:cm_program)`, ann,
        prefix2, suffix2, ann2, target2, sim2,
        `[${intermediate:cm_value}]:(cm_value)list`,
        scale_value, scale, suffix3, capacity_one, scale_number, rules);
    sim4 = cm_target_pointer_binary_step(
        true, code_at, `cm_model_code (p:cm_program)`, ann,
        prefix3, suffix3, ann3, target3, sim3,
        scale_value, intermediate, `[]:(cm_value)list`,
        `TVMDivOp:tvm_opcode`, `tower_div:int->int->int`,
        semantic_result, continuation, get_tvm_div_transition(),
        final_number, scale_nonzero, rules);
  } else {
    sim1 = cm_target_pointer_swap_step(
        code_at, `cm_model_code (p:cm_program)`, ann,
        prefix0, suffix0, ann0, target0, loaded,
        `left_value:cm_value`, `v:cm_value`, `[]:(cm_value)list`,
        suffix1, rules);
    sim2 = cm_target_pointer_push_step(
        code_at, `cm_model_code (p:cm_program)`, ann,
        prefix1, suffix1, ann1, target1, sim1,
        `[v:cm_value; left_value:cm_value]`,
        scale_value, scale, suffix2, capacity_swapped,
        scale_number, rules);
    sim3 = cm_target_pointer_binary_step(
        false, code_at, `cm_model_code (p:cm_program)`, ann,
        prefix2, suffix2, ann2, target2, sim2,
        scale_value, `v:cm_value`, `[left_value:cm_value]`,
        `TVMMulOp:tvm_opcode`, `tower_mul:int->int->int`,
        intermediate, suffix3, get_tvm_mul_transition(),
        intermediate_equal, empty_theorem, rules);
    sim4 = cm_target_pointer_binary_step(
        false, code_at, `cm_model_code (p:cm_program)`, ann,
        prefix3, suffix3, ann3, target3, sim3,
        intermediate, `left_value:cm_value`, `[]:(cm_value)list`,
        `TVMSubOp:tvm_opcode`, `tower_sub:int->int->int`,
        semantic_result, continuation, get_tvm_sub_transition(),
        final_number, empty_theorem, rules);
  }

  thm iter_six = specl_rule(TERM_LIST(
      `5:num`, `1:num`, `target:tvm_task`), get_cm_tvm_iter_add());
  sim4 = conv_rule(rewrite_conv(THM_LIST(
      sym_rule(iter_six),
      apply_conversion(get_conversion_by_name("NUM_REDUCE_CONV"),
        `(5:num) + 1`))), sim4);
  thm iter_seven = specl_rule(TERM_LIST(
      `6:num`, `1:num`, `target:tvm_task`), get_cm_tvm_iter_add());
  sim4 = conv_rule(rewrite_conv(THM_LIST(
      sym_rule(iter_seven),
      apply_conversion(get_conversion_by_name("NUM_REDUCE_CONV"),
        `(6:num) + 1`))), sim4);
  thm iter_eight = specl_rule(TERM_LIST(
      `7:num`, `1:num`, `target:tvm_task`), get_cm_tvm_iter_add());
  sim4 = conv_rule(rewrite_conv(THM_LIST(
      sym_rule(iter_eight),
      apply_conversion(get_conversion_by_name("NUM_REDUCE_CONV"),
        `(7:num) + 1`))), sim4);
  thm iter_nine = specl_rule(TERM_LIST(
      `8:num`, `1:num`, `target:tvm_task`), get_cm_tvm_iter_add());
  sim4 = conv_rule(rewrite_conv(THM_LIST(
      sym_rule(iter_nine),
      apply_conversion(get_conversion_by_name("NUM_REDUCE_CONV"),
        `(8:num) + 1`))), sim4);
  term next_ann =
      `cm_ann_pop
        ((pc:int) + ilength ${finish_code:(tvm_inst)list})
        ${ann:cm_annotation}`;
  thm reannotated = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`,
      `[${semantic_result:cm_value}]:(cm_value)list`,
      ann4, next_ann, `tvm_iter 9 (target:tvm_task)`),
      get_cm_target_reannotate());
  thm_list ann_rules = THM_LIST(
      shape, cm_ann_linear_def, cm_ann_plain_def, cm_ann_pop_def,
      cm_ann_pc_def, cm_ann_temp_def, cm_ann_break_def,
      cm_ann_continue_def, cm_ann_cursors_def,
      cm_ann_calls_def, cm_ann_spills_def, cm_ann_saved_def,
      get_cm_layout_temp_load_length(),
      get_theorem_by_name("ILENGTH_APPEND"),
      get_theorem_by_name("ILENGTH_DEF"),
      get_theorem_by_name("APPEND"),
      assume_rule(`(temp:int) == (owner:int) + 1i`));
  for (size_t index = 0; index < 4; ++index) {
    term premise = dest_imp(concl(reannotated)).tm1;
    if (index == 0) {
      thm premise_view = apply_conversion(
          reduce_rewrite_conv(ann_rules), premise);
      thm arithmetic = int_ring_rule(
          `(pc:int) + 9i ==
           (((((pc:int) + 5i) + 1i) + 1i) + 1i) + 1i`);
      reannotated = match_mp_rule(reannotated,
          eq_mp_rule(sym_rule(premise_view), arithmetic));
    } else {
      reannotated = match_mp_rule(reannotated,
          eqt_elim_rule(apply_conversion(
            reduce_rewrite_conv(ann_rules), premise)));
    }
  }
  reannotated = conv_rule(
      reduce_rewrite_conv(ann_rules), reannotated);
  reannotated = conv_rule(
      reduce_rewrite_conv(ann_rules), reannotated);
  sim4 = conv_rule(reduce_rewrite_conv(ann_rules), sim4);
  sim4 = conv_rule(reduce_rewrite_conv(ann_rules), sim4);
  thm pc_normal = int_ring_rule(
      `(((((pc:int) + 5i) + 1i) + 1i) + 1i) + 1i ==
       (pc:int) + 9i`);
  reannotated = conv_rule(
      rewrite_conv(THM_LIST(pc_normal)), reannotated);
  sim4 = conv_rule(rewrite_conv(THM_LIST(pc_normal)), sim4);
  thm result = match_mp_rule(reannotated, sim4);

  thm_list finish_rules = cm_v_layout_rules();
  vector_add(&finish_rules, shape);
  vector_add(&finish_rules, cm_update_steps_def);
  vector_add(&finish_rules, cm_task_target_sim_def);
  vector_add(&finish_rules, cm_active_spill_frames_def);
  vector_add(&finish_rules, cm_ann_linear_def);
  vector_add(&finish_rules, cm_ann_plain_def);
  vector_add(&finish_rules, cm_ann_pop_def);
  vector_add(&finish_rules, cm_code_steps_def);
  vector_add(&finish_rules, get_cm_layout_temp_load_length());
  vector_add(&finish_rules, get_theorem_by_name("ILENGTH_APPEND"));
  vector_add(&finish_rules, get_theorem_by_name("ILENGTH_DEF"));
  vector_add(&finish_rules, get_theorem_by_name("APPEND"));
  vector_add(&finish_rules, assume_rule(
      `cm_binary_ok (p:cm_program) ${op_value:int}
        (left_value:cm_value) (v:cm_value) (st:cm_src_state)`));
  gnode reduced = CONV_TAC(
      leaf, reduce_rewrite_conv(finish_rules));
  reduced = CONV_TAC(reduced, rewrite_conv(THM_LIST(
      spec_rule(`9:num`, get_theorem_by_name("NUM_OF_INT_OF_NUM")))));
  reduced = CONV_TAC(
      reduced, reduce_rewrite_conv(finish_rules));
  thm normalized = conv_rule(
      reduce_rewrite_conv(finish_rules), result);
  normalized = conv_rule(
      reduce_rewrite_conv(finish_rules), normalized);
  ACCEPT_TAC(reduced, normalized);
  return gnode_prove(root);
}

PROOF thm cm_target_v_bin_r_add_right_pointer_step =
    cm_prove_target_v_bin_r_pointer(0);
PROOF thm cm_target_v_bin_r_add_left_pointer_step =
    cm_prove_target_v_bin_r_pointer(1);
PROOF thm cm_target_v_bin_r_subtract_pointers_step =
    cm_prove_target_v_bin_r_pointer(2);
PROOF thm cm_target_v_bin_r_subtract_pointer_number_step =
    cm_prove_target_v_bin_r_pointer(3);

PROOF thm get_cm_target_v_bin_r_add_right_pointer_step(void) {
  return cm_target_v_bin_r_add_right_pointer_step;
}
PROOF thm get_cm_target_v_bin_r_add_left_pointer_step(void) {
  return cm_target_v_bin_r_add_left_pointer_step;
}
PROOF thm get_cm_target_v_bin_r_subtract_pointers_step(void) {
  return cm_target_v_bin_r_subtract_pointers_step;
}
PROOF thm get_cm_target_v_bin_r_subtract_pointer_number_step(void) {
  return cm_target_v_bin_r_subtract_pointer_number_step;
}

PROOF static int
cmc_preservation_target_value_binary_pointer_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_target_value_binary_pointer_axioms_before,
      "cmc_preservation_target_value_binary_pointer introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_target_value_binary_pointer_checks =
    cmc_preservation_target_value_binary_pointer_final_checks();
