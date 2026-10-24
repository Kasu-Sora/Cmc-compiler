#include "proof/proof.h"
#include "userlib/proof.h"
#include "cmc_preservation_target_value_binary.h"
#include "cmc_preservation_target_value.h"
#include "cmc_preservation_target_spill_runtime.h"
#include "cmc_preservation_code_value.h"
#include "cmc_preservation_code_expr.h"

#require "cmc_preservation_target_value.c"
#require "cmc_preservation_code_value_flow.c"

PROOF static size_t _cmc_preservation_target_value_binary_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_target_binary_value_code_suffix(
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

PROOF static thm cm_prove_target_v_bin_l_eval(const bool zero) {
  term op_value = zero ? `0i:int` : `1i:int`;
  term opcode = zero ? `TVMJnzOp:tvm_opcode` : `TVMJzOp:tvm_opcode`;
  term short_value = zero ? `1i:int` : `0i:int`;
  term truth_condition = zero
      ? `~cm_truth (st:cm_src_state) (v:cm_value)`
      : `cm_truth (st:cm_src_state) (v:cm_value)`;
  term task =
      `CMVTask (p:cm_program) (fid:int) (v:cm_value)
        (st:cm_src_state)
        (CMBinLK ${op_value:int} (right:cm_expr) (ty:cm_type) ::
         cm_cursor_frames (rest:(cm_acursor)list))`;
  term ann =
      `CMAnnotation (pc:int) (temp:int) (breakpc:int) (continuepc:int)
        (CMACursor
          (CABinLP ${op_value:int} (left:cm_expr) (right:cm_expr)
            (ty:cm_type))
          (owner:int) (saved_break:int) (saved_continue:int) ::
         (rest:(cm_acursor)list))
        (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
        (calls:(cm_call_sim_frame)list)`;
  term jump_pc =
      `(pc:int) + cm_rvalue_code_count (p:cm_program) (fid:int)
        (right:cm_expr) + 4i`;
  term body = imp_chain(TERM_LIST(
      `cm_task_layout (p:cm_program) ${task:cm_task}
        ${ann:cm_annotation}`,
      `cm_task_target_sim (p:cm_program) ${task:cm_task}
        (target:tvm_task) ${ann:cm_annotation}`,
      `tvm_target_valid (cm_model_code (p:cm_program)) ${jump_pc:int}`,
      truth_condition,
      `(temp:int) == (owner:int)`),
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
  term code_rest =
      `cm_emit_rvalue (p:cm_program) (fid:int) ((pc:int) + 1i)
         (owner:int) (right:cm_expr) ++
       [TVMInst TVMPushOp 0i; TVMInst TVMNeOp 0i;
        TVMInst TVMJmpOp ((pc:int) +
          cm_rvalue_code_count p fid right + 5i);
        TVMInst TVMPushOp ${short_value:int}] ++
       cm_cursor_code p fid
         ((pc:int) + cm_rvalue_code_count p fid right + 5i)
         (owner:int) F (rest:(cm_acursor)list)`;
  thm result = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`, `v:cm_value`,
      `[]:(cm_value)list`, ann, `target:tvm_task`, jump_pc,
      code_rest), zero ? get_cm_target_jnz() : get_cm_target_jz());
  thm_list target_rules = cm_v_layout_rules();
  vector_add(&target_rules, cm_active_spill_frames_def);
  vector_add(&target_rules, get_theorem_by_name("APPEND"));
  vector_add(&target_rules, get_theorem_by_name("APPEND_NIL"));
  vector_add(&target_rules, int_ring_rule(
      `!(a:int) (b:int). a + 1i + b + 4i == a + b + 5i`));
  code_at = conv_rule(reduce_rewrite_conv(target_rules), code_at);
  result = conv_rule(reduce_rewrite_conv(target_rules), result);
  result = match_mp_rule(result, code_at);
  result = match_mp_rule(result, conv_rule(
      reduce_rewrite_conv(target_rules), assume_rule(
        `tvm_target_valid (cm_model_code (p:cm_program))
          ${jump_pc:int}`)));
  result = match_mp_rule(result, running);
  result = conv_rule(reduce_rewrite_conv(THM_LIST(
      assume_rule(truth_condition),
      cm_ann_linear_def, cm_ann_plain_def)), result);

  term branch_ann =
      `cm_ann_linear [TVMInst ${opcode:tvm_opcode} ${jump_pc:int}]
        ${ann:cm_annotation}`;
  term next_ann =
      `cm_ann_replace
        (CABinRP ${op_value:int} (left:cm_expr) (right:cm_expr)
          (v:cm_value) (ty:cm_type))
        ((pc:int) + 1i) (owner:int) (breakpc:int) (continuepc:int)
        ${ann:cm_annotation}`;
  thm reannotated = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`,
      `[]:(cm_value)list`, branch_ann, next_ann,
      `tvm_iter 1 (target:tvm_task)`), get_cm_target_reannotate());
  thm_list ann_rules = THM_LIST(
      cm_ann_linear_def, cm_ann_plain_def, cm_ann_replace_def,
      cm_ann_pc_def, cm_ann_temp_def, cm_ann_break_def,
      cm_ann_continue_def, cm_ann_cursors_def,
      cm_ann_calls_def, cm_ann_spills_def, cm_ann_saved_def,
      get_cm_rvalue_code_count_def(),
      get_theorem_by_name("ILENGTH_DEF"),
      assume_rule(`(temp:int) == (owner:int)`));
  for (size_t index = 0; index < 4; ++index) {
    reannotated = match_mp_rule(reannotated,
        eqt_elim_rule(apply_conversion(
          reduce_rewrite_conv(ann_rules),
          dest_imp(concl(reannotated)).tm1)));
  }
  reannotated = conv_rule(
      reduce_rewrite_conv(ann_rules), reannotated);
  result = conv_rule(reduce_rewrite_conv(ann_rules), result);
  result = match_mp_rule(reannotated, result);

  thm_list finish_rules = THM_LIST(
      get_cm_step_def(), get_cm_vapply_def(),
      cm_annotation_step_def, cm_update_v_def,
      cm_update_steps_def, cm_update_annotation_def,
      cm_task_target_sim_def, cm_active_spill_frames_def,
      cm_ann_linear_def, cm_ann_plain_def, cm_ann_replace_def,
      cm_ann_pc_def, cm_ann_temp_def, cm_ann_break_def,
      cm_ann_continue_def, cm_ann_cursors_def,
      cm_ann_calls_def, cm_ann_spills_def, cm_ann_saved_def,
      cm_cursor_phase_def, cm_cursor_temp_def,
      cm_cursor_break_def, cm_cursor_continue_def,
      get_theorem_by_name("HD"), get_theorem_by_name("TL"),
      get_theorem_by_name("NOT_CONS_NIL"), cm_code_steps_def,
      get_theorem_by_name("ILENGTH_DEF"),
      assume_rule(truth_condition),
      assume_rule(`(temp:int) == (owner:int)`));
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

PROOF thm cm_target_v_bin_l_eval_zero_step =
    cm_prove_target_v_bin_l_eval(true);
PROOF thm cm_target_v_bin_l_eval_one_step =
    cm_prove_target_v_bin_l_eval(false);

PROOF static thm cm_prove_target_v_bin_l_short(const bool zero) {
  term op_value = zero ? `0i:int` : `1i:int`;
  term opcode = zero ? `TVMJnzOp:tvm_opcode` : `TVMJzOp:tvm_opcode`;
  term short_value = zero ? `1i:int` : `0i:int`;
  term truth_condition = zero
      ? `cm_truth (st:cm_src_state) (v:cm_value)`
      : `~cm_truth (st:cm_src_state) (v:cm_value)`;
  term task =
      `CMVTask (p:cm_program) (fid:int) (v:cm_value)
        (st:cm_src_state)
        (CMBinLK ${op_value:int} (right:cm_expr) (ty:cm_type) ::
         cm_cursor_frames (rest:(cm_acursor)list))`;
  term ann =
      `CMAnnotation (pc:int) (temp:int) (breakpc:int) (continuepc:int)
        (CMACursor
          (CABinLP ${op_value:int} (left:cm_expr) (right:cm_expr)
            (ty:cm_type))
          (owner:int) (saved_break:int) (saved_continue:int) ::
         (rest:(cm_acursor)list))
        (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
        (calls:(cm_call_sim_frame)list)`;
  term jump_pc =
      `(pc:int) + cm_rvalue_code_count (p:cm_program) (fid:int)
        (right:cm_expr) + 4i`;
  term end_pc =
      `(pc:int) + cm_rvalue_code_count (p:cm_program) (fid:int)
        (right:cm_expr) + 5i`;
  term body = imp_chain(TERM_LIST(
      `cm_task_layout (p:cm_program) ${task:cm_task}
        ${ann:cm_annotation}`,
      `cm_task_target_sim (p:cm_program) ${task:cm_task}
        (target:tvm_task) ${ann:cm_annotation}`,
      `tvm_target_valid (cm_model_code (p:cm_program)) ${jump_pc:int}`,
      truth_condition,
      `(temp:int) == (owner:int)`),
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
      `cm_cursor_code (p:cm_program) (fid:int) ${end_pc:int}
        (owner:int) F (rest:(cm_acursor)list)`;
  term full_rest =
      `cm_emit_rvalue (p:cm_program) (fid:int) ((pc:int) + 1i)
         (owner:int) (right:cm_expr) ++
       [TVMInst TVMPushOp 0i; TVMInst TVMNeOp 0i;
        TVMInst TVMJmpOp ${end_pc:int};
        TVMInst TVMPushOp ${short_value:int}] ++
       ${continuation:(tvm_inst)list}`;
  thm branch = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`, `v:cm_value`,
      `[]:(cm_value)list`, ann, `target:tvm_task`, jump_pc,
      full_rest), zero ? get_cm_target_jnz() : get_cm_target_jz());
  thm_list target_rules = cm_v_layout_rules();
  vector_add(&target_rules, cm_active_spill_frames_def);
  vector_add(&target_rules, get_theorem_by_name("APPEND"));
  vector_add(&target_rules, cm_ann_plain_def);
  vector_add(&target_rules, cm_ann_pc_def);
  vector_add(&target_rules, cm_ann_temp_def);
  vector_add(&target_rules, cm_ann_break_def);
  vector_add(&target_rules, cm_ann_continue_def);
  vector_add(&target_rules, cm_ann_cursors_def);
  vector_add(&target_rules, cm_ann_spills_def);
  vector_add(&target_rules, cm_ann_saved_def);
  vector_add(&target_rules, cm_ann_calls_def);
  vector_add(&target_rules, get_theorem_by_name("APPEND_NIL"));
  vector_add(&target_rules, int_ring_rule(
      `!(a:int) (b:int). a + 1i + b + 4i == a + b + 5i`));
  code_at = conv_rule(reduce_rewrite_conv(target_rules), code_at);
  branch = conv_rule(reduce_rewrite_conv(target_rules), branch);
  branch = match_mp_rule(branch, code_at);
  branch = match_mp_rule(branch, conv_rule(
      reduce_rewrite_conv(target_rules), assume_rule(
        `tvm_target_valid (cm_model_code (p:cm_program))
          ${jump_pc:int}`)));
  branch = match_mp_rule(branch, running);
  branch = conv_rule(reduce_rewrite_conv(THM_LIST(
      assume_rule(truth_condition),
      cm_ann_linear_def, cm_ann_plain_def)), branch);

  term branch_ann =
      `cm_ann_plain ${jump_pc:int} (temp:int) (breakpc:int)
        (continuepc:int) ${ann:cm_annotation}`;
  term prefix =
      `[TVMInst ${opcode:tvm_opcode} ${jump_pc:int}] ++
       cm_emit_rvalue (p:cm_program) (fid:int) ((pc:int) + 1i)
         (owner:int) (right:cm_expr) ++
       [TVMInst TVMPushOp 0i; TVMInst TVMNeOp 0i;
        TVMInst TVMJmpOp ${end_pc:int}]`;
  term suffix =
      `[TVMInst TVMPushOp ${short_value:int}] ++
       ${continuation:(tvm_inst)list}`;
  thm_list suffix_rules = cm_v_layout_rules();
  vector_add(&suffix_rules, cm_ann_plain_def);
  vector_add(&suffix_rules, cm_ann_pc_def);
  vector_add(&suffix_rules, get_theorem_by_name("APPEND"));
  vector_add(&suffix_rules, get_theorem_by_name("APPEND_NIL"));
  vector_add(&suffix_rules, int_ring_rule(
      `!(a:int) (b:int). a + 1i + b + 3i == a + b + 4i`));
  thm push_code = cm_target_binary_value_code_suffix(
      code_at, `cm_model_code (p:cm_program)`, ann, prefix,
      suffix, branch_ann, suffix_rules);
  push_code = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_theorem_by_name("APPEND"))), push_code);
  thm pushed = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`,
      `[]:(cm_value)list`, branch_ann,
      `tvm_iter 1 (target:tvm_task)`,
      `CMIntV ${short_value:int}`, short_value, continuation),
      get_cm_target_push());
  pushed = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_push_code_def(), get_theorem_by_name("APPEND"))), pushed);
  pushed = match_mp_rule(pushed, push_code);
  pushed = conv_rule(
      reduce_rewrite_conv(target_rules), pushed);
  pushed = match_mp_rule(pushed, branch);
  pushed = match_mp_rule(pushed,
      eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          get_cm_value_number_def(), get_tower_wrap64_idempotent())),
        `tower_wrap64 ${short_value:int} ==
         cm_value_number (st:cm_src_state)
           (CMIntV ${short_value:int})`)));
  thm iter_two = specl_rule(TERM_LIST(
      `1:num`, `1:num`, `target:tvm_task`),
      get_cm_tvm_iter_add());
  pushed = conv_rule(reduce_rewrite_conv(THM_LIST(
      sym_rule(iter_two), get_theorem_by_name("ADD_CLAUSES"))),
      pushed);
  pushed = conv_rule(rewrite_conv(THM_LIST(
      apply_conversion(get_conversion_by_name("NUM_REDUCE_CONV"),
        `(1:num) + 1`))), pushed);

  term pushed_ann =
      `cm_ann_linear [TVMInst TVMPushOp ${short_value:int}]
        ${branch_ann:cm_annotation}`;
  term next_ann =
      `cm_ann_pop ${end_pc:int} ${ann:cm_annotation}`;
  thm reannotated = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`,
      `[CMIntV ${short_value:int}]:(cm_value)list`,
      pushed_ann, next_ann, `tvm_iter 2 (target:tvm_task)`),
      get_cm_target_reannotate());
  thm_list ann_rules = THM_LIST(
      cm_ann_linear_def, cm_ann_plain_def, cm_ann_pop_def,
      cm_ann_pc_def, cm_ann_temp_def, cm_ann_break_def,
      cm_ann_continue_def, cm_ann_cursors_def,
      cm_ann_calls_def, cm_ann_spills_def, cm_ann_saved_def,
      get_cm_rvalue_code_count_def(),
      get_theorem_by_name("ILENGTH_DEF"),
      int_ring_rule(
        `!(a:int) (b:int). a + b + 5i == (a + b + 4i) + 1i`),
      assume_rule(`(temp:int) == (owner:int)`));
  for (size_t index = 0; index < 4; ++index) {
    reannotated = match_mp_rule(reannotated,
        eqt_elim_rule(apply_conversion(
          reduce_rewrite_conv(ann_rules),
          dest_imp(concl(reannotated)).tm1)));
  }
  reannotated = conv_rule(
      reduce_rewrite_conv(ann_rules), reannotated);
  pushed = conv_rule(reduce_rewrite_conv(ann_rules), pushed);
  thm result = match_mp_rule(reannotated, pushed);
  thm_list finish_rules = THM_LIST(
      get_cm_step_def(), get_cm_vapply_def(),
      cm_annotation_step_def, cm_update_v_def,
      cm_update_steps_def, cm_update_annotation_def,
      cm_task_target_sim_def, cm_active_spill_frames_def,
      cm_ann_linear_def, cm_ann_plain_def, cm_ann_pop_def,
      cm_ann_pc_def, cm_ann_temp_def, cm_ann_break_def,
      cm_ann_continue_def, cm_ann_cursors_def,
      cm_ann_calls_def, cm_ann_spills_def, cm_ann_saved_def,
      cm_cursor_phase_def, cm_cursor_temp_def,
      cm_cursor_break_def, cm_cursor_continue_def,
      get_theorem_by_name("HD"), get_theorem_by_name("TL"),
      get_theorem_by_name("NOT_CONS_NIL"), cm_code_steps_def,
      get_cm_rvalue_code_count_def(),
      get_theorem_by_name("ILENGTH_DEF"),
      int_ring_rule(
        `!(a:int) (b:int). a + b + 5i == (a + b + 4i) + 1i`),
      assume_rule(truth_condition),
      assume_rule(`(temp:int) == (owner:int)`));
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

PROOF thm cm_target_v_bin_l_short_zero_step =
    cm_prove_target_v_bin_l_short(true);
PROOF thm cm_target_v_bin_l_short_one_step =
    cm_prove_target_v_bin_l_short(false);

PROOF static thm cm_prove_target_v_bin_l_other_step(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (v:cm_value) (st:cm_src_state)
         (op:int) (left:cm_expr) (right:cm_expr) (ty:cm_type)
         (pc:int) (temp:int) (breakpc:int) (continuepc:int)
         (owner:int) (saved_break:int) (saved_continue:int)
         (rest:(cm_acursor)list) (spills:(cm_spill)list)
         (saved:(cm_spill_frame)list)
         (calls:(cm_call_sim_frame)list) (target:tvm_task)
         (address:int).
         cm_task_layout p
           (CMVTask p fid v st
             (CMBinLK op right ty :: cm_cursor_frames rest))
           (CMAnnotation pc temp breakpc continuepc
             (CMACursor (CABinLP op left right ty) owner saved_break
               saved_continue :: rest) spills saved calls) ==>
         cm_task_target_sim p
           (CMVTask p fid v st
             (CMBinLK op right ty :: cm_cursor_frames rest))
           target
           (CMAnnotation pc temp breakpc continuepc
             (CMACursor (CABinLP op left right ty) owner saved_break
               saved_continue :: rest) spills saved calls) ==>
         cm_runtime_stack p (cm_state_regions st) fid
           (cm_state_fp st) (cm_state_regions st)
           (CMACursor (CABinLP op left right ty) owner saved_break
             saved_continue :: rest)
           (cm_spill_put owner v spills) saved calls ==>
         0i <= fid ==>
         temp == owner ==>
         ~(op == 0i) ==>
         ~(op == 1i) ==>
         cm_tagged_span_valid st ==>
         tower_signed64 (cm_state_fp st) ==>
         tower_signed64 (cm_temp_offset p fid owner) ==>
         address == cm_state_fp st + cm_temp_offset p fid owner ==>
         tower_signed64 address ==>
         tower_word_valid address ==>
         cm_task_target_sim p
           (cm_step
             (CMVTask p fid v st
               (CMBinLK op right ty :: cm_cursor_frames rest)))
           (tvm_iter
             (cm_update_steps
               (cm_annotation_step
                 (CMVTask p fid v st
                   (CMBinLK op right ty :: cm_cursor_frames rest))
                 (CMAnnotation pc temp breakpc continuepc
                   (CMACursor (CABinLP op left right ty) owner
                     saved_break saved_continue :: rest)
                   spills saved calls)))
             target)
           (cm_update_annotation
             (cm_annotation_step
               (CMVTask p fid v st
                 (CMBinLK op right ty :: cm_cursor_frames rest))
               (CMAnnotation pc temp breakpc continuepc
                 (CMACursor (CABinLP op left right ty) owner
                   saved_break saved_continue :: rest)
                 spills saved calls)))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  term ann =
      `CMAnnotation (pc:int) (temp:int) (breakpc:int) (continuepc:int)
        (CMACursor
          (CABinLP (op:int) (left:cm_expr) (right:cm_expr)
            (ty:cm_type))
          (owner:int) (saved_break:int) (saved_continue:int) ::
         (rest:(cm_acursor)list))
        (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
        (calls:(cm_call_sim_frame)list)`;
  term task =
      `CMVTask (p:cm_program) (fid:int) (v:cm_value)
        (st:cm_src_state)
        (CMBinLK (op:int) (right:cm_expr) (ty:cm_type) ::
         cm_cursor_frames (rest:(cm_acursor)list))`;
  thm layout = assume_rule(
      `cm_task_layout (p:cm_program) ${task:cm_task}
        ${ann:cm_annotation}`);
  thm code_at = conjunct1_rule(conv_rule(
      reduce_rewrite_conv(cm_v_layout_rules()), layout));
  thm running = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_task_target_sim_def)), assume_rule(
        `cm_task_target_sim (p:cm_program) ${task:cm_task}
          (target:tvm_task) ${ann:cm_annotation}`));
  term code_rest =
      `cm_emit_rvalue (p:cm_program) (fid:int)
         ((pc:int) + 5i) ((owner:int) + 1i) (right:cm_expr) ++
       cm_binary_finish_code p fid (op:int) (left:cm_expr) right owner ++
       cm_cursor_code p fid
         ((pc:int) + 5i +
          cm_rvalue_code_count p fid right +
          ilength
            (cm_binary_finish_code p fid op left right owner))
         (owner:int) F (rest:(cm_acursor)list)`;
  thm result = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`,
      `owner:int`, `v:cm_value`, `[]:(cm_value)list`,
      ann, `target:tvm_task`, code_rest, `address:int`),
      get_cm_target_temp_store_runtime());
  thm_list target_rules = cm_v_layout_rules();
  vector_add(&target_rules, cm_active_spill_frames_def);
  vector_add(&target_rules, get_theorem_by_name("APPEND"));
  vector_add(&target_rules, get_theorem_by_name("APPEND_NIL"));
  vector_add(&target_rules, assume_rule(`~((op:int) == 0i)`));
  vector_add(&target_rules, assume_rule(`~((op:int) == 1i)`));
  vector_add(&target_rules, int_ring_rule(
      `!(a:int) (b:int) (c:int).
         a + 5i + b + c == a + (5i + b + c)`));
  code_at = conv_rule(reduce_rewrite_conv(target_rules), code_at);
  result = conv_rule(reduce_rewrite_conv(target_rules), result);
  result = match_mp_rule(result, code_at);
  result = match_mp_rule(result, running);
  result = match_mp_rule(result, conv_rule(
      reduce_rewrite_conv(target_rules), assume_rule(
        `cm_runtime_stack (p:cm_program)
          (cm_state_regions (st:cm_src_state)) (fid:int)
          (cm_state_fp st) (cm_state_regions st)
          (CMACursor
            (CABinLP (op:int) (left:cm_expr) (right:cm_expr)
              (ty:cm_type))
            (owner:int) (saved_break:int) (saved_continue:int) ::
           (rest:(cm_acursor)list))
          (cm_spill_put owner (v:cm_value) (spills:(cm_spill)list))
          (saved:(cm_spill_frame)list)
          (calls:(cm_call_sim_frame)list)`)));
  result = match_mp_rule(result, assume_rule(`0i <= (fid:int)`));
  result = match_mp_rule(result,
      assume_rule(`cm_tagged_span_valid (st:cm_src_state)`));
  result = match_mp_rule(result, assume_rule(
      `tower_signed64 (cm_state_fp (st:cm_src_state))`));
  result = match_mp_rule(result, assume_rule(
      `tower_signed64
        (cm_temp_offset (p:cm_program) (fid:int) (owner:int))`));
  result = match_mp_rule(result, assume_rule(
      `(address:int) == cm_state_fp (st:cm_src_state) +
        cm_temp_offset (p:cm_program) (fid:int) (owner:int)`));
  result = match_mp_rule(result,
      assume_rule(`tower_signed64 (address:int)`));
  result = match_mp_rule(result,
      assume_rule(`tower_word_valid (address:int)`));
  term stored_ann =
      `cm_ann_put_spill (owner:int) (v:cm_value)
        (cm_ann_linear
          (cm_temp_store_code (p:cm_program) (fid:int) owner)
          ${ann:cm_annotation})`;
  term next_ann =
      `cm_ann_put_spill (owner:int) (v:cm_value)
        (cm_ann_replace
          (CABinRP (op:int) (left:cm_expr) (right:cm_expr)
            (v:cm_value) (ty:cm_type))
          ((pc:int) +
           ilength (cm_temp_store_code (p:cm_program) (fid:int) owner))
          ((owner:int) + 1i) (breakpc:int) (continuepc:int)
          ${ann:cm_annotation})`;
  thm reannotated = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`,
      `[]:(cm_value)list`, stored_ann, next_ann,
      `tvm_iter 5 (target:tvm_task)`), get_cm_target_reannotate());
  thm_list ann_rules = THM_LIST(
      cm_ann_linear_def, cm_ann_plain_def, cm_ann_replace_def,
      cm_ann_put_spill_def, cm_ann_spills_set_def,
      cm_spill_put_def,
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
  reannotated = conv_rule(
      reduce_rewrite_conv(ann_rules), reannotated);
  result = conv_rule(reduce_rewrite_conv(ann_rules), result);
  result = conv_rule(reduce_rewrite_conv(ann_rules), result);
  result = match_mp_rule(reannotated, result);
  thm_list finish_rules = cm_v_layout_rules();
  vector_add(&finish_rules, cm_update_steps_def);
  vector_add(&finish_rules, cm_task_target_sim_def);
  vector_add(&finish_rules, cm_active_spill_frames_def);
  vector_add(&finish_rules, cm_ann_linear_def);
  vector_add(&finish_rules, cm_ann_plain_def);
  vector_add(&finish_rules, cm_ann_replace_def);
  vector_add(&finish_rules, cm_ann_put_spill_def);
  vector_add(&finish_rules, cm_ann_spills_set_def);
  vector_add(&finish_rules, cm_code_steps_def);
  vector_add(&finish_rules, get_cm_layout_temp_store_length());
  vector_add(&finish_rules, assume_rule(`(temp:int) == (owner:int)`));
  vector_add(&finish_rules, assume_rule(`~((op:int) == 0i)`));
  vector_add(&finish_rules, assume_rule(`~((op:int) == 1i)`));
  gnode reduced = CONV_TAC(
      leaf, reduce_rewrite_conv(finish_rules));
  reduced = CONV_TAC(reduced, rewrite_conv(THM_LIST(
      spec_rule(`5:num`, get_theorem_by_name("NUM_OF_INT_OF_NUM")))));
  reduced = CONV_TAC(
      reduced, reduce_rewrite_conv(finish_rules));
  thm normalized = conv_rule(
      reduce_rewrite_conv(finish_rules), result);
  normalized = conv_rule(
      reduce_rewrite_conv(finish_rules), normalized);
  ACCEPT_TAC(reduced, normalized);
  return gnode_prove(root);
}
PROOF thm cm_target_v_bin_l_other_step =
    cm_prove_target_v_bin_l_other_step();

PROOF static thm cm_prove_target_v_bin_r_logical(const bool zero) {
  term op_value = zero ? `0i:int` : `1i:int`;
  term short_value = zero ? `1i:int` : `0i:int`;
  term left_condition = zero
      ? `~cm_truth (st:cm_src_state) (left_value:cm_value)`
      : `cm_truth (st:cm_src_state) (left_value:cm_value)`;
  term semantic_result =
      `cm_binary_value (p:cm_program) ${op_value:int}
        (left_value:cm_value) (v:cm_value) (ty:cm_type)
        (st:cm_src_state)`;
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
  term end_pc = `(pc:int) + 4i`;
  term body = imp_chain(TERM_LIST(
      `cm_task_layout (p:cm_program) ${task:cm_task}
        ${ann:cm_annotation}`,
      `cm_task_target_sim (p:cm_program) ${task:cm_task}
        (target:tvm_task) ${ann:cm_annotation}`,
      `cm_binary_ok (p:cm_program) ${op_value:int}
        (left_value:cm_value) (v:cm_value) (st:cm_src_state)`,
      left_condition,
      `tvm_target_valid (cm_model_code (p:cm_program)) ${end_pc:int}`),
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
      `cm_cursor_code (p:cm_program) (fid:int) ${end_pc:int}
        (owner:int) F (rest:(cm_acursor)list)`;
  term after_push =
      `[TVMInst TVMNeOp 0i; TVMInst TVMJmpOp ${end_pc:int};
        TVMInst TVMPushOp ${short_value:int}] ++
       ${continuation:(tvm_inst)list}`;
  thm pushed = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`,
      `[v:cm_value]`, ann, `target:tvm_task`, `CMIntV 0i`,
      `0i:int`, after_push), get_cm_target_push());
  thm_list target_rules = cm_v_layout_rules();
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
  vector_add(&target_rules, get_theorem_by_name("APPEND"));
  vector_add(&target_rules, get_cm_push_code_def());
  vector_add(&target_rules, get_theorem_by_name("ILENGTH_DEF"));
  vector_add(&target_rules, get_theorem_by_name("APPEND_NIL"));
  code_at = conv_rule(reduce_rewrite_conv(target_rules), code_at);
  pushed = conv_rule(reduce_rewrite_conv(target_rules), pushed);
  pushed = match_mp_rule(pushed, code_at);
  pushed = match_mp_rule(pushed, running);
  pushed = match_mp_rule(pushed,
      eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          get_cm_value_number_def(), get_tower_wrap64_idempotent())),
        `tower_wrap64 0i ==
         cm_value_number (st:cm_src_state) (CMIntV 0i)`)));

  term push_ann =
      `cm_ann_linear [TVMInst TVMPushOp 0i] ${ann:cm_annotation}`;
  term binary_suffix =
      `[TVMInst TVMNeOp 0i; TVMInst TVMJmpOp ${end_pc:int};
        TVMInst TVMPushOp ${short_value:int}] ++
       ${continuation:(tvm_inst)list}`;
  thm binary_code = cm_target_binary_value_code_suffix(
      code_at, `cm_model_code (p:cm_program)`, ann,
      `[TVMInst TVMPushOp 0i]:(tvm_inst)list`,
      binary_suffix, push_ann, target_rules);
  binary_code = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_theorem_by_name("APPEND"))), binary_code);
  binary_code = conv_rule(
      reduce_rewrite_conv(target_rules), binary_code);
  thm binary = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`,
      `CMIntV 0i`, `v:cm_value`, `[]:(cm_value)list`,
      push_ann, `tvm_iter 1 (target:tvm_task)`,
      `TVMNeOp:tvm_opcode`,
      `\(x:int) (y:int). tower_bool (~(x == y))`, semantic_result,
      `[TVMInst TVMJmpOp ${end_pc:int};
        TVMInst TVMPushOp ${short_value:int}] ++
       ${continuation:(tvm_inst)list}`),
      get_cm_target_binary_total());
  binary = conv_rule(reduce_rewrite_conv(THM_LIST()), binary);
  binary = match_mp_rule(binary, get_tvm_ne_transition());
  binary = conv_rule(reduce_rewrite_conv(target_rules), binary);
  binary = match_mp_rule(binary, binary_code);
  pushed = conv_rule(reduce_rewrite_conv(target_rules), pushed);
  binary = match_mp_rule(binary, pushed);

  thm bridge = specl_rule(TERM_LIST(
      `p:cm_program`, op_value, `left_value:cm_value`,
      `v:cm_value`, `ty:cm_type`, `st:cm_src_state`),
      get_cm_binary_value_number_bridge());
  bridge = match_mp_rule(bridge, assume_rule(
      `cm_binary_ok (p:cm_program) ${op_value:int}
        (left_value:cm_value) (v:cm_value) (st:cm_src_state)`));
  bridge = match_mp_rule(bridge,
      eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST()),
        `~(${op_value:int} == 8i &&
           cm_is_pointer
             (cm_value_type (left_value:cm_value)) &&
           cm_is_pointer (cm_value_type (v:cm_value)))`)));
  thm zero_fixed = mp_rule(
      spec_rule(`0i:int`, get_tower_wrap64_fixed()),
      eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(get_tower_signed64_def())),
        `tower_signed64 0i`)));
  thm operation_equal = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        bridge, get_cm_binary_machine_number_def(),
        get_cm_value_number_def(), get_cm_truth_number_bridge(),
        zero_fixed, assume_rule(left_condition))),
      `tower_bool
          (~(cm_value_number (st:cm_src_state) (v:cm_value) ==
             cm_value_number st (CMIntV 0i))) ==
       cm_value_number st ${semantic_result:cm_value}`));
  binary = match_mp_rule(binary, operation_equal);

  term binary_ann =
      `cm_ann_linear [TVMInst TVMNeOp 0i] ${push_ann:cm_annotation}`;
  term jump_suffix =
      `[TVMInst TVMJmpOp ${end_pc:int};
        TVMInst TVMPushOp ${short_value:int}] ++
       ${continuation:(tvm_inst)list}`;
  thm jump_code = cm_target_binary_value_code_suffix(
      code_at, `cm_model_code (p:cm_program)`, ann,
      `[TVMInst TVMPushOp 0i; TVMInst TVMNeOp 0i]:(tvm_inst)list`,
      jump_suffix, binary_ann, target_rules);
  jump_code = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_theorem_by_name("APPEND"))), jump_code);
  jump_code = conv_rule(
      reduce_rewrite_conv(target_rules), jump_code);
  thm jumped = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`,
      `[${semantic_result:cm_value}]:(cm_value)list`,
      binary_ann, `tvm_iter 1 (tvm_iter 1 (target:tvm_task))`,
      end_pc,
      `[TVMInst TVMPushOp ${short_value:int}] ++
       ${continuation:(tvm_inst)list}`),
      get_cm_target_jump());
  jumped = conv_rule(reduce_rewrite_conv(target_rules), jumped);
  jumped = match_mp_rule(jumped, jump_code);
  jumped = match_mp_rule(jumped, conv_rule(
      reduce_rewrite_conv(target_rules), assume_rule(
        `tvm_target_valid (cm_model_code (p:cm_program))
          ${end_pc:int}`)));
  binary = conv_rule(reduce_rewrite_conv(target_rules), binary);
  jumped = match_mp_rule(jumped, binary);

  thm iter_two = specl_rule(TERM_LIST(
      `1:num`, `1:num`, `target:tvm_task`),
      get_cm_tvm_iter_add());
  thm iter_three = specl_rule(TERM_LIST(
      `1:num`, `2:num`, `target:tvm_task`),
      get_cm_tvm_iter_add());
  jumped = conv_rule(rewrite_conv(THM_LIST(
      sym_rule(iter_two), sym_rule(iter_three),
      apply_conversion(get_conversion_by_name("NUM_REDUCE_CONV"),
        `(1:num) + 1`),
      apply_conversion(get_conversion_by_name("NUM_REDUCE_CONV"),
        `(1:num) + 2`))), jumped);

  term jump_ann =
      `cm_ann_plain ${end_pc:int}
        (cm_ann_temp ${binary_ann:cm_annotation})
        (cm_ann_break ${binary_ann:cm_annotation})
        (cm_ann_continue ${binary_ann:cm_annotation})
        ${binary_ann:cm_annotation}`;
  term next_ann = `cm_ann_pop ${end_pc:int} ${ann:cm_annotation}`;
  thm reannotated = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`,
      `[${semantic_result:cm_value}]:(cm_value)list`,
      jump_ann, next_ann, `tvm_iter 3 (target:tvm_task)`),
      get_cm_target_reannotate());
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
  reannotated = conv_rule(
      reduce_rewrite_conv(ann_rules), reannotated);
  jumped = conv_rule(reduce_rewrite_conv(ann_rules), jumped);
  jumped = conv_rule(reduce_rewrite_conv(ann_rules), jumped);
  thm result = match_mp_rule(reannotated, jumped);

  thm_list finish_rules = cm_v_layout_rules();
  vector_add(&finish_rules, cm_update_steps_def);
  vector_add(&finish_rules, cm_task_target_sim_def);
  vector_add(&finish_rules, cm_active_spill_frames_def);
  vector_add(&finish_rules, cm_ann_linear_def);
  vector_add(&finish_rules, cm_ann_plain_def);
  vector_add(&finish_rules, cm_ann_pop_def);
  vector_add(&finish_rules, cm_code_steps_def);
  vector_add(&finish_rules, assume_rule(left_condition));
  vector_add(&finish_rules, assume_rule(
      `cm_binary_ok (p:cm_program) ${op_value:int}
        (left_value:cm_value) (v:cm_value) (st:cm_src_state)`));
  gnode reduced = CONV_TAC(
      leaf, reduce_rewrite_conv(finish_rules));
  reduced = CONV_TAC(reduced, rewrite_conv(THM_LIST(
      spec_rule(`3:num`, get_theorem_by_name("NUM_OF_INT_OF_NUM")))));
  reduced = CONV_TAC(
      reduced, reduce_rewrite_conv(finish_rules));
  thm normalized = conv_rule(
      reduce_rewrite_conv(finish_rules), result);
  normalized = conv_rule(
      reduce_rewrite_conv(finish_rules), normalized);
  ACCEPT_TAC(reduced, normalized);
  return gnode_prove(root);
}

PROOF thm cm_target_v_bin_r_zero_step =
    cm_prove_target_v_bin_r_logical(true);
PROOF thm cm_target_v_bin_r_one_step =
    cm_prove_target_v_bin_r_logical(false);

PROOF thm get_cm_target_v_bin_l_eval_zero_step(void) {
  return cm_target_v_bin_l_eval_zero_step;
}
PROOF thm get_cm_target_v_bin_l_eval_one_step(void) {
  return cm_target_v_bin_l_eval_one_step;
}
PROOF thm get_cm_target_v_bin_l_short_zero_step(void) {
  return cm_target_v_bin_l_short_zero_step;
}
PROOF thm get_cm_target_v_bin_l_short_one_step(void) {
  return cm_target_v_bin_l_short_one_step;
}
PROOF thm get_cm_target_v_bin_l_other_step(void) {
  return cm_target_v_bin_l_other_step;
}
PROOF thm get_cm_target_v_bin_r_zero_step(void) {
  return cm_target_v_bin_r_zero_step;
}
PROOF thm get_cm_target_v_bin_r_one_step(void) {
  return cm_target_v_bin_r_one_step;
}

PROOF static int cmc_preservation_target_value_binary_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_target_value_binary_axioms_before,
      "cmc_preservation_target_value_binary introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_target_value_binary_checks =
    cmc_preservation_target_value_binary_final_checks();
