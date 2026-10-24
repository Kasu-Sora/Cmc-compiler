#include "proof/proof.h"
#include "userlib/proof.h"
#include "cmc_preservation_target_value_binary_finish.h"
#include "cmc_preservation_target_value_binary.h"
#include "cmc_preservation_code_expr.h"
#include "cmc_preservation_code_value.h"
#include "cmc_preservation_target_machine.h"
#include "cmc_preservation_target_spill.h"

#require "cmc_preservation_target_value_binary.c"

PROOF static size_t
    _cmc_preservation_target_value_binary_finish_axioms_before =
        vector_size(get_all_axioms());

PROOF static thm cm_target_binary_finish_code_suffix(
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

PROOF static thm cm_prove_target_v_bin_r_ordinary(const bool nonzero) {
  term task =
      `CMVTask (p:cm_program) (fid:int) (v:cm_value)
        (st:cm_src_state)
        (CMBinRK (op:int) (left_value:cm_value) (ty:cm_type) ::
         cm_cursor_frames (rest:(cm_acursor)list))`;
  term ann =
      `CMAnnotation (pc:int) (temp:int) (breakpc:int) (continuepc:int)
        (CMACursor
          (CABinRP (op:int) (left:cm_expr) (right:cm_expr)
            (left_value:cm_value) (ty:cm_type))
          (owner:int) (saved_break:int) (saved_continue:int) ::
         (rest:(cm_acursor)list))
        (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
        (calls:(cm_call_sim_frame)list)`;
  term finish_code =
      `cm_binary_finish_code (p:cm_program) (fid:int) (op:int)
        (left:cm_expr) (right:cm_expr) (owner:int)`;
  term semantic_result =
      `cm_binary_value (p:cm_program) (op:int)
        (left_value:cm_value) (v:cm_value) (ty:cm_type)
        (st:cm_src_state)`;
  term transition = nonzero
      ? `!code imm vm.
           tvm_inst_step (code:(tvm_inst)list) (opcode:tvm_opcode)
             (imm:int) (vm:tvm_state) =
           (if 2i <= ilength (tvm_stack vm) &&
               ~(HD (tvm_stack vm) == 0i)
            then TVMStepState
              (tvm_next_state vm
                ((operation:int->int->int)
                   (HD (TL (tvm_stack vm))) (HD (tvm_stack vm)) ::
                 TL (TL (tvm_stack vm)))
                (tvm_calls vm) (tvm_mem vm)
                (tvm_input vm) (tvm_output vm))
            else TVMStepError vm)`
      : `!code imm vm.
           tvm_inst_step (code:(tvm_inst)list) (opcode:tvm_opcode)
             (imm:int) (vm:tvm_state) =
           (if 2i <= ilength (tvm_stack vm)
            then TVMStepState
              (tvm_next_state vm
                ((operation:int->int->int)
                   (HD (TL (tvm_stack vm))) (HD (tvm_stack vm)) ::
                 TL (TL (tvm_stack vm)))
                (tvm_calls vm) (tvm_mem vm)
                (tvm_input vm) (tvm_output vm))
            else TVMStepError vm)`;
  term_list premises = TERM_LIST(
      `cm_task_layout (p:cm_program) ${task:cm_task}
        ${ann:cm_annotation}`,
      `cm_task_target_sim (p:cm_program) ${task:cm_task}
        (target:tvm_task) ${ann:cm_annotation}`,
      `cm_binary_ok (p:cm_program) (op:int)
        (left_value:cm_value) (v:cm_value) (st:cm_src_state)`,
      `~((op:int) == 0i)`, `~((op:int) == 1i)`,
      `cm_spill_holds (owner:int) (left_value:cm_value)
        (spills:(cm_spill)list)`,
      `(temp:int) == (owner:int) + 1i`,
      `${finish_code:(tvm_inst)list} ==
        cm_temp_load_code (p:cm_program) (fid:int) (owner:int) ++
        [TVMInst TVMSwapOp 0i;
         TVMInst (opcode:tvm_opcode) 0i]`,
      transition,
      `(operation:int->int->int)
         (cm_value_number (st:cm_src_state) (left_value:cm_value))
         (cm_value_number st (v:cm_value)) ==
       cm_value_number st ${semantic_result:cm_value}`,
      `tower_signed64 (cm_state_fp (st:cm_src_state))`,
      `tower_signed64
        (cm_temp_offset (p:cm_program) (fid:int) (owner:int))`,
      `(address:int) == cm_state_fp st + cm_temp_offset p fid owner`,
      `tower_signed64 (address:int)`,
      `tower_word_valid (address:int)`);
  if (nonzero) {
    vector_insert(&premises, 10,
        `~(cm_value_number (st:cm_src_state) (v:cm_value) == 0i)`);
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
  thm shape = assume_rule(
      `${finish_code:(tvm_inst)list} ==
        cm_temp_load_code (p:cm_program) (fid:int) (owner:int) ++
        [TVMInst TVMSwapOp 0i;
         TVMInst (opcode:tvm_opcode) 0i]`);
  term continuation =
      `cm_cursor_code (p:cm_program) (fid:int)
        ((pc:int) + ilength ${finish_code:(tvm_inst)list})
        (owner:int) F (rest:(cm_acursor)list)`;
  term after_load =
      `[TVMInst TVMSwapOp 0i; TVMInst (opcode:tvm_opcode) 0i] ++
       ${continuation:(tvm_inst)list}`;
  thm loaded = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`, `owner:int`,
      `left_value:cm_value`, `[v:cm_value]`, ann,
      `target:tvm_task`, after_load, `address:int`),
      get_cm_target_temp_load());
  thm_list target_rules = cm_v_layout_rules();
  vector_add(&target_rules, assume_rule(`~((op:int) == 0i)`));
  vector_add(&target_rules, assume_rule(`~((op:int) == 1i)`));
  vector_add(&target_rules, shape);
  vector_add(&target_rules, cm_active_spill_frames_def);
  vector_add(&target_rules, cm_ann_linear_def);
  vector_add(&target_rules, cm_ann_plain_def);
  vector_add(&target_rules, cm_ann_pc_def);
  vector_add(&target_rules, cm_ann_temp_def);
  vector_add(&target_rules, cm_ann_break_def);
  vector_add(&target_rules, cm_ann_continue_def);
  vector_add(&target_rules, cm_ann_cursors_def);
  vector_add(&target_rules, cm_ann_spills_def);
  vector_add(&target_rules, cm_ann_saved_def);
  vector_add(&target_rules, cm_ann_calls_def);
  vector_add(&target_rules, get_cm_layout_temp_load_length());
  vector_add(&target_rules, get_theorem_by_name("ILENGTH_DEF"));
  vector_add(&target_rules, get_theorem_by_name("APPEND"));
  vector_add(&target_rules, get_theorem_by_name("APPEND_NIL"));
  code_at = conv_rule(reduce_rewrite_conv(target_rules), code_at);
  loaded = conv_rule(reduce_rewrite_conv(target_rules), loaded);
  loaded = match_mp_rule(loaded, code_at);
  loaded = match_mp_rule(loaded, running);
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

  term load_ann =
      `cm_ann_linear
        (cm_temp_load_code (p:cm_program) (fid:int) (owner:int))
        ${ann:cm_annotation}`;
  term swap_suffix =
      `[TVMInst TVMSwapOp 0i; TVMInst (opcode:tvm_opcode) 0i] ++
       ${continuation:(tvm_inst)list}`;
  thm swap_code = cm_target_binary_finish_code_suffix(
      code_at, `cm_model_code (p:cm_program)`, ann,
      `cm_temp_load_code (p:cm_program) (fid:int) (owner:int)`,
      swap_suffix, load_ann, target_rules);
  swap_code = conv_rule(reduce_rewrite_conv(target_rules), swap_code);
  thm swapped = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`,
      `left_value:cm_value`, `v:cm_value`, `[]:(cm_value)list`,
      load_ann, `tvm_iter 5 (target:tvm_task)`,
      `TVMInst (opcode:tvm_opcode) 0i ::
       ${continuation:(tvm_inst)list}`), get_cm_target_swap());
  swapped = conv_rule(reduce_rewrite_conv(target_rules), swapped);
  swapped = match_mp_rule(swapped, swap_code);
  loaded = conv_rule(reduce_rewrite_conv(target_rules), loaded);
  swapped = match_mp_rule(swapped, loaded);

  term swap_ann =
      `cm_ann_linear [TVMInst TVMSwapOp 0i]
        ${load_ann:cm_annotation}`;
  thm operation_code = cm_target_binary_finish_code_suffix(
      code_at, `cm_model_code (p:cm_program)`, ann,
      `cm_temp_load_code (p:cm_program) (fid:int) (owner:int) ++
       [TVMInst TVMSwapOp 0i]`,
      `TVMInst (opcode:tvm_opcode) 0i ::
       ${continuation:(tvm_inst)list}`,
      swap_ann, target_rules);
  operation_code = conv_rule(
      reduce_rewrite_conv(target_rules), operation_code);
  thm operation_step = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`,
      `v:cm_value`, `left_value:cm_value`, `[]:(cm_value)list`,
      swap_ann, `tvm_iter 1 (tvm_iter 5 (target:tvm_task))`,
      `opcode:tvm_opcode`, `operation:int->int->int`,
      semantic_result, continuation),
      nonzero ? get_cm_target_binary_nonzero()
              : get_cm_target_binary_total());
  operation_step = match_mp_rule(operation_step,
      assume_rule(transition));
  operation_step = conv_rule(
      reduce_rewrite_conv(target_rules), operation_step);
  operation_step = match_mp_rule(operation_step, operation_code);
  swapped = conv_rule(reduce_rewrite_conv(target_rules), swapped);
  operation_step = match_mp_rule(operation_step, swapped);
  if (nonzero) {
    operation_step = match_mp_rule(operation_step, assume_rule(
        `~(cm_value_number (st:cm_src_state) (v:cm_value) == 0i)`));
  }
  operation_step = match_mp_rule(operation_step, assume_rule(
      `(operation:int->int->int)
         (cm_value_number (st:cm_src_state) (left_value:cm_value))
         (cm_value_number st (v:cm_value)) ==
       cm_value_number st ${semantic_result:cm_value}`));

  thm iter_six = specl_rule(TERM_LIST(
      `5:num`, `1:num`, `target:tvm_task`), get_cm_tvm_iter_add());
  thm iter_seven = specl_rule(TERM_LIST(
      `6:num`, `1:num`, `target:tvm_task`), get_cm_tvm_iter_add());
  operation_step = conv_rule(rewrite_conv(THM_LIST(
      sym_rule(iter_six), sym_rule(iter_seven),
      apply_conversion(get_conversion_by_name("NUM_REDUCE_CONV"),
        `(5:num) + 1`),
      apply_conversion(get_conversion_by_name("NUM_REDUCE_CONV"),
        `(6:num) + 1`))), operation_step);

  term operation_ann =
      `cm_ann_linear [TVMInst (opcode:tvm_opcode) 0i]
        ${swap_ann:cm_annotation}`;
  term next_ann =
      `cm_ann_pop
        ((pc:int) + ilength ${finish_code:(tvm_inst)list})
        ${ann:cm_annotation}`;
  thm reannotated = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`,
      `[${semantic_result:cm_value}]:(cm_value)list`,
      operation_ann, next_ann, `tvm_iter 7 (target:tvm_task)`),
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
      assume_rule(`(temp:int) == (owner:int) + 1i`),
      int_ring_rule(`!(a:int). a + 7i == ((a + 5i) + 1i) + 1i`));
  for (size_t index = 0; index < 4; ++index) {
    term premise = dest_imp(concl(reannotated)).tm1;
    if (index == 0) {
      thm premise_view = apply_conversion(
          reduce_rewrite_conv(ann_rules), premise);
      thm arithmetic = int_ring_rule(
          `(pc:int) + 7i == (((pc:int) + 5i) + 1i) + 1i`);
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
  operation_step = conv_rule(
      reduce_rewrite_conv(ann_rules), operation_step);
  operation_step = conv_rule(
      reduce_rewrite_conv(ann_rules), operation_step);
  thm result = match_mp_rule(reannotated, operation_step);

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
  vector_add(&finish_rules, assume_rule(`~((op:int) == 0i)`));
  vector_add(&finish_rules, assume_rule(`~((op:int) == 1i)`));
  vector_add(&finish_rules, assume_rule(
      `cm_binary_ok (p:cm_program) (op:int)
        (left_value:cm_value) (v:cm_value) (st:cm_src_state)`));
  gnode reduced = CONV_TAC(
      leaf, reduce_rewrite_conv(finish_rules));
  reduced = CONV_TAC(reduced, rewrite_conv(THM_LIST(
      spec_rule(`7:num`, get_theorem_by_name("NUM_OF_INT_OF_NUM")))));
  reduced = CONV_TAC(
      reduced, reduce_rewrite_conv(finish_rules));
  thm normalized = conv_rule(
      reduce_rewrite_conv(finish_rules), result);
  normalized = conv_rule(
      reduce_rewrite_conv(finish_rules), normalized);
  ACCEPT_TAC(reduced, normalized);
  return gnode_prove(root);
}

PROOF thm cm_target_v_bin_r_ordinary_total_step =
    cm_prove_target_v_bin_r_ordinary(false);
PROOF thm cm_target_v_bin_r_ordinary_nonzero_step =
    cm_prove_target_v_bin_r_ordinary(true);

PROOF thm get_cm_target_v_bin_r_ordinary_total_step(void) {
  return cm_target_v_bin_r_ordinary_total_step;
}
PROOF thm get_cm_target_v_bin_r_ordinary_nonzero_step(void) {
  return cm_target_v_bin_r_ordinary_nonzero_step;
}

PROOF static int
cmc_preservation_target_value_binary_finish_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_target_value_binary_finish_axioms_before,
      "cmc_preservation_target_value_binary_finish introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_target_value_binary_finish_checks =
    cmc_preservation_target_value_binary_finish_final_checks();
