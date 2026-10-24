#include "proof/proof.h"
#include "userlib/proof.h"
#include "cmc_preservation_target_value_unary.h"
#include "cmc_preservation_target_value_binary.h"
#include "cmc_preservation_target_machine.h"
#include "cmc_preservation_code_value.h"

#require "cmc_preservation_target_value_binary.c"

PROOF static size_t _cmc_preservation_target_value_unary_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_target_unary_code_suffix(
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

PROOF static thm cm_prove_unary_mul_neg(void) {
  gnode root = gnode_new_with_ccl(
      `!(x:int). tower_mul x (--1i) == tower_neg x`);
  gnode leaf = AUTO_INTROS_TAC(root);
  CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
      get_tower_mul_def(), get_tower_neg_def(),
      int_ring_rule(`!(x:int). x * --1i == --x`))));
  return gnode_prove(root);
}
PROOF static thm cm_unary_mul_neg = cm_prove_unary_mul_neg();

PROOF static thm cm_prove_target_v_unary(const bool zero) {
  term op_value = zero ? `0i:int` : `op:int`;
  term immediate = zero ? `--1i:int` : `0i:int`;
  term opcode = zero ? `TVMMulOp:tvm_opcode` : `TVMEqOp:tvm_opcode`;
  term operation = zero
      ? `tower_mul:int->int->int`
      : `\(x:int) (y:int). tower_bool (x == y)`;
  term task =
      `CMVTask (p:cm_program) (fid:int) (v:cm_value)
        (st:cm_src_state)
        (CMUnaryK ${op_value:int} ::
         cm_cursor_frames (rest:(cm_acursor)list))`;
  term ann =
      `CMAnnotation (pc:int) (temp:int) (breakpc:int) (continuepc:int)
        (CMACursor (CAUnaryP ${op_value:int}) (owner:int)
          (saved_break:int) (saved_continue:int) ::
         (rest:(cm_acursor)list))
        (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
        (calls:(cm_call_sim_frame)list)`;
  term semantic_result =
      `cm_unary_value ${op_value:int} (v:cm_value) (st:cm_src_state)`;
  term_list premises = TERM_LIST(
      `cm_task_layout (p:cm_program) ${task:cm_task}
        ${ann:cm_annotation}`,
      `cm_task_target_sim (p:cm_program) ${task:cm_task}
        (target:tvm_task) ${ann:cm_annotation}`);
  if (!zero) {
    vector_add(&premises, `~((op:int) == 0i)`);
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
  term continuation =
      `cm_cursor_code (p:cm_program) (fid:int) ((pc:int) + 2i)
        (owner:int) F (rest:(cm_acursor)list)`;
  term after_push =
      `TVMInst ${opcode:tvm_opcode} 0i ::
       ${continuation:(tvm_inst)list}`;
  thm pushed = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`,
      `[v:cm_value]`, ann, `target:tvm_task`,
      `CMIntV ${immediate:int}`, immediate, after_push),
      get_cm_target_push());
  thm_list rules = cm_v_layout_rules();
  if (!zero) {
    vector_add(&rules, assume_rule(`~((op:int) == 0i)`));
  }
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
  vector_add(&rules, get_cm_push_code_def());
  vector_add(&rules, get_theorem_by_name("ILENGTH_DEF"));
  vector_add(&rules, get_theorem_by_name("APPEND"));
  vector_add(&rules, get_theorem_by_name("APPEND_NIL"));
  code_at = conv_rule(reduce_rewrite_conv(rules), code_at);
  pushed = conv_rule(reduce_rewrite_conv(rules), pushed);
  pushed = match_mp_rule(pushed, code_at);
  pushed = match_mp_rule(pushed, running);
  thm immediate_number = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(get_cm_value_number_def())),
      `tower_wrap64 ${immediate:int} ==
       cm_value_number (st:cm_src_state) (CMIntV ${immediate:int})`));
  pushed = match_mp_rule(pushed, immediate_number);

  term push_ann =
      `cm_ann_linear [TVMInst TVMPushOp ${immediate:int}]
        ${ann:cm_annotation}`;
  thm operation_code = cm_target_unary_code_suffix(
      code_at, `cm_model_code (p:cm_program)`, ann,
      `[TVMInst TVMPushOp ${immediate:int}]:(tvm_inst)list`,
      `TVMInst ${opcode:tvm_opcode} 0i ::
       ${continuation:(tvm_inst)list}`,
      push_ann, rules);
  operation_code = conv_rule(
      reduce_rewrite_conv(rules), operation_code);
  thm operation_step = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`,
      `CMIntV ${immediate:int}`, `v:cm_value`,
      `[]:(cm_value)list`, push_ann,
      `tvm_iter 1 (target:tvm_task)`, opcode, operation,
      semantic_result, continuation), get_cm_target_binary_total());
  operation_step = conv_rule(
      reduce_rewrite_conv(THM_LIST()), operation_step);
  operation_step = match_mp_rule(operation_step,
      zero ? get_tvm_mul_transition() : get_tvm_eq_transition());
  operation_step = conv_rule(
      reduce_rewrite_conv(rules), operation_step);
  operation_step = match_mp_rule(operation_step, operation_code);
  pushed = conv_rule(reduce_rewrite_conv(rules), pushed);
  operation_step = match_mp_rule(operation_step, pushed);

  thm bridge = specl_rule(TERM_LIST(
      op_value, `v:cm_value`, `st:cm_src_state`),
      get_cm_unary_value_number_bridge());
  thm fixed = mp_rule(
      spec_rule(immediate, get_tower_wrap64_fixed()),
      eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(get_tower_signed64_def())),
        zero ? `tower_signed64 (--1i)` : `tower_signed64 0i`)));
  thm number_equal;
  if (zero) {
    number_equal = eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          bridge, get_cm_value_number_def(), fixed,
          cm_unary_mul_neg)),
        `tower_mul
            (cm_value_number (st:cm_src_state) (v:cm_value))
            (cm_value_number st (CMIntV (--1i))) ==
         cm_value_number st ${semantic_result:cm_value}`));
  } else {
    number_equal = eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          bridge, get_cm_value_number_def(), fixed,
          get_cm_truth_number_bridge(),
          assume_rule(`~((op:int) == 0i)`))),
        `tower_bool
            (cm_value_number (st:cm_src_state) (v:cm_value) ==
             cm_value_number st (CMIntV 0i)) ==
         cm_value_number st ${semantic_result:cm_value}`));
  }
  operation_step = match_mp_rule(operation_step, number_equal);
  thm iter_two = specl_rule(TERM_LIST(
      `1:num`, `1:num`, `target:tvm_task`), get_cm_tvm_iter_add());
  operation_step = conv_rule(rewrite_conv(THM_LIST(
      sym_rule(iter_two),
      apply_conversion(get_conversion_by_name("NUM_REDUCE_CONV"),
        `(1:num) + 1`))), operation_step);

  term operation_ann =
      `cm_ann_linear [TVMInst ${opcode:tvm_opcode} 0i]
        ${push_ann:cm_annotation}`;
  term next_ann = `cm_ann_pop ((pc:int) + 2i) ${ann:cm_annotation}`;
  thm reannotated = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`,
      `[${semantic_result:cm_value}]:(cm_value)list`,
      operation_ann, next_ann, `tvm_iter 2 (target:tvm_task)`),
      get_cm_target_reannotate());
  thm_list ann_rules = THM_LIST(
      cm_ann_linear_def, cm_ann_plain_def, cm_ann_pop_def,
      cm_ann_pc_def, cm_ann_temp_def, cm_ann_break_def,
      cm_ann_continue_def, cm_ann_cursors_def,
      cm_ann_calls_def, cm_ann_spills_def, cm_ann_saved_def,
      get_theorem_by_name("ILENGTH_DEF"),
      int_ring_rule(`!(a:int). a + 2i == (a + 1i) + 1i`));
  for (size_t index = 0; index < 4; ++index) {
    reannotated = match_mp_rule(reannotated,
        eqt_elim_rule(apply_conversion(
          reduce_rewrite_conv(ann_rules),
          dest_imp(concl(reannotated)).tm1)));
  }
  reannotated = conv_rule(
      reduce_rewrite_conv(ann_rules), reannotated);
  operation_step = conv_rule(
      reduce_rewrite_conv(ann_rules), operation_step);
  thm result = match_mp_rule(reannotated, operation_step);

  thm_list finish_rules = cm_v_layout_rules();
  vector_add(&finish_rules, cm_update_steps_def);
  vector_add(&finish_rules, cm_task_target_sim_def);
  vector_add(&finish_rules, cm_active_spill_frames_def);
  vector_add(&finish_rules, cm_ann_linear_def);
  vector_add(&finish_rules, cm_ann_plain_def);
  vector_add(&finish_rules, cm_ann_pop_def);
  vector_add(&finish_rules, cm_code_steps_def);
  if (!zero) {
    vector_add(&finish_rules, assume_rule(`~((op:int) == 0i)`));
  }
  gnode reduced = CONV_TAC(
      leaf, reduce_rewrite_conv(finish_rules));
  reduced = CONV_TAC(reduced, rewrite_conv(THM_LIST(
      spec_rule(`2:num`, get_theorem_by_name("NUM_OF_INT_OF_NUM")))));
  reduced = CONV_TAC(
      reduced, reduce_rewrite_conv(finish_rules));
  thm normalized = conv_rule(
      reduce_rewrite_conv(finish_rules), result);
  normalized = conv_rule(
      reduce_rewrite_conv(finish_rules), normalized);
  ACCEPT_TAC(reduced, normalized);
  return gnode_prove(root);
}

PROOF thm cm_target_v_unary_zero_step =
    cm_prove_target_v_unary(true);
PROOF thm cm_target_v_unary_other_step =
    cm_prove_target_v_unary(false);

PROOF thm get_cm_target_v_unary_zero_step(void) {
  return cm_target_v_unary_zero_step;
}
PROOF thm get_cm_target_v_unary_other_step(void) {
  return cm_target_v_unary_other_step;
}

PROOF static int cmc_preservation_target_value_unary_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_target_value_unary_axioms_before,
      "cmc_preservation_target_value_unary introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_target_value_unary_checks =
    cmc_preservation_target_value_unary_final_checks();
