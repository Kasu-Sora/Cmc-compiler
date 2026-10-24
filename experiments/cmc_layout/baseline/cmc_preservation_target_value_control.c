#include "proof/proof.h"
#include "userlib/proof.h"
#include "cmc_preservation_target_value_control.h"
#include "cmc_preservation_target_value_io.h"
#include "cmc_preservation_target_machine.h"
#include "cmc_preservation_target_convert.h"
#include "cmc_preservation_code_value.h"
#include "cmc_preservation_code_expr.h"

#require "cmc_preservation_target_value_io.c"

PROOF static size_t _cmc_preservation_target_value_control_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_target_control_code_suffix(
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

PROOF static thm cm_prove_target_v_expr_stmt_step(void) {
  term task =
      `CMVTask (p:cm_program) (fid:int) (v:cm_value)
        (st:cm_src_state)
        (CMExprStmtK :: cm_cursor_frames (rest:(cm_acursor)list))`;
  term ann =
      `CMAnnotation (pc:int) (temp:int) (breakpc:int) (continuepc:int)
        (CMACursor CAExprStmtP (owner:int)
          (saved_break:int) (saved_continue:int) ::
         (rest:(cm_acursor)list))
        (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
        (calls:(cm_call_sim_frame)list)`;
  term body = imp_chain(TERM_LIST(
      `cm_task_layout (p:cm_program) ${task:cm_task} ${ann:cm_annotation}`,
      `cm_task_target_sim (p:cm_program) ${task:cm_task}
        (target:tvm_task) ${ann:cm_annotation}`),
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
      `cm_cursor_code (p:cm_program) (fid:int) ((pc:int) + 1i)
        (owner:int) T (rest:(cm_acursor)list)`;
  thm_list rules = cm_v_layout_rules();
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
  vector_add(&rules, get_theorem_by_name("APPEND"));
  vector_add(&rules, get_theorem_by_name("APPEND_NIL"));
  vector_add(&rules, get_theorem_by_name("ILENGTH_DEF"));
  code_at = conv_rule(reduce_rewrite_conv(rules), code_at);
  thm popped = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`, `v:cm_value`,
      `[]:(cm_value)list`, ann, `target:tvm_task`, continuation),
      get_cm_target_pop());
  popped = conv_rule(reduce_rewrite_conv(rules), popped);
  popped = match_mp_rule(popped, code_at);
  popped = match_mp_rule(popped, running);
  term pop_ann =
      `cm_ann_linear [TVMInst TVMPopOp 0i] ${ann:cm_annotation}`;
  term next_ann = `cm_ann_pop ((pc:int) + 1i) ${ann:cm_annotation}`;
  thm reannotated = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`,
      `[]:(cm_value)list`, pop_ann, next_ann,
      `tvm_iter 1 (target:tvm_task)`), get_cm_target_reannotate());
  thm_list ann_rules = THM_LIST(
      cm_ann_linear_def, cm_ann_plain_def, cm_ann_pop_def,
      cm_ann_pc_def, cm_ann_temp_def, cm_ann_break_def,
      cm_ann_continue_def, cm_ann_cursors_def,
      cm_ann_calls_def, cm_ann_spills_def, cm_ann_saved_def,
      get_theorem_by_name("ILENGTH_DEF"));
  for (size_t index = 0; index < 4; ++index) {
    reannotated = match_mp_rule(reannotated,
        eqt_elim_rule(apply_conversion(
          reduce_rewrite_conv(ann_rules),
          dest_imp(concl(reannotated)).tm1)));
  }
  reannotated = conv_rule(
      reduce_rewrite_conv(ann_rules), reannotated);
  popped = conv_rule(reduce_rewrite_conv(ann_rules), popped);
  thm result = match_mp_rule(reannotated, popped);
  thm_list finish_rules = cm_v_layout_rules();
  vector_add(&finish_rules, cm_update_steps_def);
  vector_add(&finish_rules, cm_task_target_sim_def);
  vector_add(&finish_rules, cm_active_spill_frames_def);
  vector_add(&finish_rules, cm_ann_linear_def);
  vector_add(&finish_rules, cm_ann_plain_def);
  vector_add(&finish_rules, cm_ann_pop_def);
  vector_add(&finish_rules, cm_code_steps_def);
  gnode reduced = CONV_TAC(
      leaf, reduce_rewrite_conv(finish_rules));
  reduced = CONV_TAC(reduced, rewrite_conv(THM_LIST(
      spec_rule(`1:num`, get_theorem_by_name("NUM_OF_INT_OF_NUM")))));
  reduced = CONV_TAC(
      reduced, reduce_rewrite_conv(finish_rules));
  thm normalized = conv_rule(
      reduce_rewrite_conv(finish_rules), result);
  normalized = conv_rule(
      reduce_rewrite_conv(finish_rules), normalized);
  ACCEPT_TAC(reduced, normalized);
  return gnode_prove(root);
}

PROOF thm cm_target_v_expr_stmt_step =
    cm_prove_target_v_expr_stmt_step();

PROOF thm get_cm_target_v_expr_stmt_step(void) {
  return cm_target_v_expr_stmt_step;
}

PROOF static thm cm_prove_target_v_status_step(const bool done) {
  term frame = done ? `CMHaltK:cm_frame` : `CMExitK:cm_frame`;
  term phase = done ? `CAHaltP:cm_aphase` : `CAExitP:cm_aphase`;
  term number =
      `cm_value_number (st:cm_src_state) (v:cm_value)`;
  term converted =
      `cm_convert_value (st:cm_src_state) CMCharTy (v:cm_value)`;
  term status = `tower_status ${number:int}`;
  term task =
      `CMVTask (p:cm_program) (fid:int) (v:cm_value)
        (st:cm_src_state)
        (${frame:cm_frame} ::
         cm_cursor_frames (rest:(cm_acursor)list))`;
  term ann =
      `CMAnnotation (pc:int) (temp:int) (breakpc:int) (continuepc:int)
        (CMACursor ${phase:cm_aphase} (owner:int)
          (saved_break:int) (saved_continue:int) ::
         (rest:(cm_acursor)list))
        (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
        (calls:(cm_call_sim_frame)list)`;
  term body = imp_chain(TERM_LIST(
      `cm_task_layout (p:cm_program) ${task:cm_task} ${ann:cm_annotation}`,
      `cm_task_target_sim (p:cm_program) ${task:cm_task}
        (target:tvm_task) ${ann:cm_annotation}`,
      `tower_signed64 ${number:int}`),
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
  thm_list rules = cm_v_layout_rules();
  vector_add(&rules, cm_status_tail_code_def);
  vector_add(&rules, get_cm_char_normalize_code_def());
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
  vector_add(&rules, cm_code_steps_def);
  vector_add(&rules, get_cm_layout_char_normalize_length());
  vector_add(&rules, get_theorem_by_name("APPEND"));
  vector_add(&rules, get_theorem_by_name("APPEND_NIL"));
  vector_add(&rules, get_theorem_by_name("ILENGTH_APPEND"));
  vector_add(&rules, get_theorem_by_name("ILENGTH_DEF"));
  vector_add(&rules, spec_rule(
      `6:num`, get_theorem_by_name("NUM_OF_INT_OF_NUM")));
  code_at = conv_rule(reduce_rewrite_conv(rules), code_at);
  thm normalized = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`,
      `CMCharTy:cm_type`, `v:cm_value`, `[]:(cm_value)list`,
      ann, `target:tvm_task`,
      `[TVMInst TVMHaltOp 0i]:(tvm_inst)list`),
      get_cm_target_char_normalize());
  normalized = conv_rule(reduce_rewrite_conv(rules), normalized);
  normalized = match_mp_rule(normalized, code_at);
  normalized = match_mp_rule(normalized, running);
  normalized = match_mp_rule(normalized,
      assume_rule(`tower_signed64 ${number:int}`));
  normalized = conv_rule(reduce_rewrite_conv(rules), normalized);

  term char_ann =
      `cm_ann_linear (cm_char_normalize_code CMCharTy)
        ${ann:cm_annotation}`;
  thm halt_code = cm_target_control_code_suffix(
      code_at, `cm_model_code (p:cm_program)`, ann,
      `cm_char_normalize_code CMCharTy`,
      `[TVMInst TVMHaltOp 0i]:(tvm_inst)list`, char_ann, rules);
  halt_code = conv_rule(reduce_rewrite_conv(rules), halt_code);
  thm halted = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`, converted,
      char_ann, `tvm_iter 6 (target:tvm_task)`,
      `[]:(tvm_inst)list`), get_cm_target_halt());
  halted = conv_rule(reduce_rewrite_conv(rules), halted);
  halted = match_mp_rule(halted, halt_code);
  normalized = conv_rule(reduce_rewrite_conv(rules), normalized);
  halted = match_mp_rule(halted, normalized);
  thm converted_number = conv_rule(
      reduce_rewrite_conv(THM_LIST()),
      specl_rule(TERM_LIST(
        `st:cm_src_state`, `CMCharTy:cm_type`, `v:cm_value`),
        get_cm_convert_value_number_bridge()));
  thm status_view = apply_conversion(
      rewrite_conv(THM_LIST(get_tower_status_def())),
      `tower_status ${number:int}`);
  thm status_equal =
      trans_rule(converted_number, sym_rule(status_view));
  thm byte_value = conv_rule(rewrite_conv(THM_LIST(
      sym_rule(converted_number))),
      spec_rule(number, get_tower_u8_range()));
  halted = match_mp_rule(halted, byte_value);
  halted = conv_rule(rewrite_conv(THM_LIST(status_equal)), halted);
  thm iter_seven = specl_rule(TERM_LIST(
      `6:num`, `1:num`, `target:tvm_task`), get_cm_tvm_iter_add());
  halted = conv_rule(rewrite_conv(THM_LIST(
      sym_rule(iter_seven),
      apply_conversion(get_conversion_by_name("NUM_REDUCE_CONV"),
        `(6:num) + 1`))), halted);

  term next_ann =
      `cm_ann_pop
        ((pc:int) + ilength (cm_char_normalize_code CMCharTy))
        ${ann:cm_annotation}`;
  thm reannotated = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`, status,
      `T:bool`, char_ann, next_ann,
      `tvm_iter 7 (target:tvm_task)`),
      get_cm_target_halted_reannotate());
  thm_list ann_rules = THM_LIST(
      cm_ann_linear_def, cm_ann_plain_def, cm_ann_pop_def,
      cm_ann_pc_def, cm_ann_temp_def, cm_ann_break_def,
      cm_ann_continue_def, cm_ann_cursors_def,
      cm_ann_calls_def, cm_ann_spills_def, cm_ann_saved_def,
      get_cm_layout_char_normalize_length(),
      get_cm_char_normalize_count_def());
  for (size_t index = 0; index < 4; ++index) {
    reannotated = match_mp_rule(reannotated,
        eqt_elim_rule(apply_conversion(
          reduce_rewrite_conv(ann_rules),
          dest_imp(concl(reannotated)).tm1)));
  }
  reannotated = conv_rule(
      reduce_rewrite_conv(ann_rules), reannotated);
  halted = conv_rule(reduce_rewrite_conv(ann_rules), halted);
  thm result = match_mp_rule(reannotated, halted);
  if (done) {
    thm deactivate = specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `st:cm_src_state`, status,
        next_ann, `tvm_iter 7 (target:tvm_task)`),
        get_cm_target_halted_deactivate());
    deactivate = conv_rule(reduce_rewrite_conv(ann_rules), deactivate);
    result = match_mp_rule(deactivate, result);
  }

  thm_list finish_rules = cm_v_layout_rules();
  vector_add(&finish_rules, cm_update_steps_def);
  vector_add(&finish_rules, cm_task_target_sim_def);
  vector_add(&finish_rules, get_cm_control_status_def());
  vector_add(&finish_rules, cm_halted_target_sim_def);
  vector_add(&finish_rules, cm_active_spill_frames_def);
  vector_add(&finish_rules, cm_ann_linear_def);
  vector_add(&finish_rules, cm_ann_plain_def);
  vector_add(&finish_rules, cm_ann_pop_def);
  vector_add(&finish_rules, cm_code_steps_def);
  vector_add(&finish_rules, cm_status_tail_code_def);
  vector_add(&finish_rules, get_cm_layout_char_normalize_length());
  vector_add(&finish_rules, get_theorem_by_name("ILENGTH_APPEND"));
  vector_add(&finish_rules, get_theorem_by_name("ILENGTH_DEF"));
  gnode reduced = CONV_TAC(
      leaf, reduce_rewrite_conv(finish_rules));
  reduced = CONV_TAC(reduced, rewrite_conv(THM_LIST(
      spec_rule(`7:num`, get_theorem_by_name("NUM_OF_INT_OF_NUM")))));
  reduced = CONV_TAC(
      reduced, reduce_rewrite_conv(finish_rules));
  result = conv_rule(reduce_rewrite_conv(finish_rules), result);
  result = conv_rule(reduce_rewrite_conv(finish_rules), result);
  ACCEPT_TAC(reduced, result);
  return gnode_prove(root);
}

PROOF thm cm_target_v_exit_step =
    cm_prove_target_v_status_step(false);
PROOF thm cm_target_v_halt_step =
    cm_prove_target_v_status_step(true);

PROOF thm get_cm_target_v_exit_step(void) {
  return cm_target_v_exit_step;
}
PROOF thm get_cm_target_v_halt_step(void) {
  return cm_target_v_halt_step;
}

PROOF static int cmc_preservation_target_value_control_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_target_value_control_axioms_before,
      "cmc_preservation_target_value_control introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_target_value_control_checks =
    cmc_preservation_target_value_control_final_checks();
