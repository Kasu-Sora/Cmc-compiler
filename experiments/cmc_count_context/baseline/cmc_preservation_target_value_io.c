#include "proof/proof.h"
#include "userlib/proof.h"
#include "cmc_preservation_target_value_io.h"
#include "cmc_preservation_target_value_member.h"
#include "cmc_preservation_target_machine.h"
#include "cmc_preservation_code_value.h"

#require "cmc_preservation_target_value_member.c"

PROOF static size_t _cmc_preservation_target_value_io_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_target_io_code_suffix(
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

PROOF static thm cm_prove_target_v_output_step(const bool character) {
  term frame = character ? `CMPutcK:cm_frame` : `CMPutiK:cm_frame`;
  term phase = character ? `CAPutcP:cm_aphase` : `CAPutiP:cm_aphase`;
  term opcode = character ? `TVMPutcOp:tvm_opcode` : `TVMPutiOp:tvm_opcode`;
  term next_state = character
      ? `cm_state_io (st:cm_src_state) (cm_state_input st)
          (cm_state_output st ++
           [tower_u8 (cm_value_number st (v:cm_value))])`
      : `cm_state_io (st:cm_src_state) (cm_state_input st)
          (cm_state_output st ++
           tower_decimal (cm_value_number st (v:cm_value)))`;
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
      `cm_cursor_code (p:cm_program) (fid:int) ((pc:int) + 2i)
        (owner:int) F (rest:(cm_acursor)list)`;
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
  thm duplicated = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`, `v:cm_value`,
      `[]:(cm_value)list`, ann, `target:tvm_task`,
      `TVMInst ${opcode:tvm_opcode} 0i ::
       ${continuation:(tvm_inst)list}`), get_cm_target_dup());
  duplicated = conv_rule(reduce_rewrite_conv(rules), duplicated);
  duplicated = match_mp_rule(duplicated, code_at);
  duplicated = match_mp_rule(duplicated, running);

  term dup_ann =
      `cm_ann_linear [TVMInst TVMDupOp 0i] ${ann:cm_annotation}`;
  thm output_code = cm_target_io_code_suffix(
      code_at, `cm_model_code (p:cm_program)`, ann,
      `[TVMInst TVMDupOp 0i]:(tvm_inst)list`,
      `TVMInst ${opcode:tvm_opcode} 0i ::
       ${continuation:(tvm_inst)list}`,
      dup_ann, rules);
  output_code = conv_rule(reduce_rewrite_conv(rules), output_code);
  thm output = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`, `v:cm_value`,
      `[]:(cm_value)list`, dup_ann,
      `tvm_iter 1 (target:tvm_task)`, continuation),
      character ? get_cm_target_putc() : get_cm_target_puti());
  output = conv_rule(reduce_rewrite_conv(rules), output);
  output = match_mp_rule(output, output_code);
  duplicated = conv_rule(reduce_rewrite_conv(rules), duplicated);
  output = match_mp_rule(output, duplicated);
  thm iter_two = specl_rule(TERM_LIST(
      `1:num`, `1:num`, `target:tvm_task`), get_cm_tvm_iter_add());
  output = conv_rule(rewrite_conv(THM_LIST(
      sym_rule(iter_two),
      apply_conversion(get_conversion_by_name("NUM_REDUCE_CONV"),
        `(1:num) + 1`))), output);

  term output_ann =
      `cm_ann_linear [TVMInst ${opcode:tvm_opcode} 0i]
        ${dup_ann:cm_annotation}`;
  term next_ann = `cm_ann_pop ((pc:int) + 2i) ${ann:cm_annotation}`;
  thm reannotated = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, next_state,
      `[CMIntV
          (cm_value_number (st:cm_src_state)
            (v:cm_value))]:(cm_value)list`,
      output_ann, next_ann, `tvm_iter 2 (target:tvm_task)`),
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
  output = conv_rule(reduce_rewrite_conv(ann_rules), output);
  thm result = match_mp_rule(reannotated, output);

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

PROOF thm cm_target_v_putc_step =
    cm_prove_target_v_output_step(true);
PROOF thm cm_target_v_puti_step =
    cm_prove_target_v_output_step(false);

PROOF thm get_cm_target_v_putc_step(void) {
  return cm_target_v_putc_step;
}
PROOF thm get_cm_target_v_puti_step(void) {
  return cm_target_v_puti_step;
}

PROOF static int cmc_preservation_target_value_io_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_target_value_io_axioms_before,
      "cmc_preservation_target_value_io introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_target_value_io_checks =
    cmc_preservation_target_value_io_final_checks();
