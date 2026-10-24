#include "proof/proof.h"
#include "userlib/proof.h"
#include "cmc_preservation_target_value_member.h"
#include "cmc_preservation_target_value_index.h"
#include "cmc_preservation_target_machine.h"
#include "cmc_preservation_code_value.h"
#include "cmc_preservation_code_expr.h"

#require "cmc_preservation_target_value_index.c"

PROOF static size_t _cmc_preservation_target_value_member_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_target_member_code_suffix(
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

PROOF static thm cm_prove_target_v_member_step(void) {
  term offset =
      `cm_member_offset (cm_program_structs (p:cm_program))
        (cm_struct_id (cm_pointee (base_ty:cm_type))) (mid:int)`;
  term result_value =
      `cm_ptr_member (p:cm_program) (v:cm_value) (mid:int)`;
  term task =
      `CMVTask (p:cm_program) (fid:int) (v:cm_value)
        (st:cm_src_state)
        (CMMemberK (mid:int) ::
         cm_cursor_frames (rest:(cm_acursor)list))`;
  term ann =
      `CMAnnotation (pc:int) (temp:int) (breakpc:int) (continuepc:int)
        (CMACursor (CAMemberP (mid:int) (base_ty:cm_type))
          (owner:int) (saved_break:int) (saved_continue:int) ::
         (rest:(cm_acursor)list))
        (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
        (calls:(cm_call_sim_frame)list)`;
  term body = imp_chain(TERM_LIST(
      `cm_task_layout (p:cm_program) ${task:cm_task} ${ann:cm_annotation}`,
      `cm_task_target_sim (p:cm_program) ${task:cm_task}
        (target:tvm_task) ${ann:cm_annotation}`,
      `cm_ptr_member_ok (p:cm_program) (v:cm_value) (mid:int)
        (st:cm_src_state)`,
      `cm_pointer_live (st:cm_src_state) (v:cm_value)`,
      `(cm_ptr_view (v:cm_value)) == cm_pointee (base_ty:cm_type)`,
      `tower_signed64 ${offset:int}`),
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
  vector_add(&rules, cm_member_tail_code_def);
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
  vector_add(&rules, get_theorem_by_name("APPEND"));
  vector_add(&rules, get_theorem_by_name("APPEND_NIL"));
  vector_add(&rules, get_theorem_by_name("ILENGTH_DEF"));
  code_at = conv_rule(reduce_rewrite_conv(rules), code_at);
  thm pushed = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`,
      `[v:cm_value]:(cm_value)list`, ann, `target:tvm_task`,
      `CMIntV ${offset:int}`, offset,
      `TVMInst TVMAddOp 0i :: ${continuation:(tvm_inst)list}`),
      get_cm_target_push());
  pushed = conv_rule(reduce_rewrite_conv(rules), pushed);
  pushed = match_mp_rule(pushed, code_at);
  pushed = match_mp_rule(pushed, running);
  thm offset_fixed = mp_rule(
      spec_rule(offset, get_tower_wrap64_fixed()),
      assume_rule(`tower_signed64 ${offset:int}`));
  pushed = match_mp_rule(pushed, eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_value_number_def(), offset_fixed)),
      `tower_wrap64 ${offset:int} ==
       cm_value_number (st:cm_src_state) (CMIntV ${offset:int})`)));

  term push_ann =
      `cm_ann_linear [TVMInst TVMPushOp ${offset:int}]
        ${ann:cm_annotation}`;
  thm add_code = cm_target_member_code_suffix(
      code_at, `cm_model_code (p:cm_program)`, ann,
      `[TVMInst TVMPushOp ${offset:int}]:(tvm_inst)list`,
      `TVMInst TVMAddOp 0i :: ${continuation:(tvm_inst)list}`,
      push_ann, rules);
  add_code = conv_rule(reduce_rewrite_conv(rules), add_code);
  thm added = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`,
      `CMIntV ${offset:int}`, `v:cm_value`,
      `[]:(cm_value)list`, push_ann,
      `tvm_iter 1 (target:tvm_task)`, `TVMAddOp:tvm_opcode`,
      `tower_add:int->int->int`, result_value, continuation),
      get_cm_target_binary_total());
  added = match_mp_rule(added, get_tvm_add_transition());
  added = conv_rule(reduce_rewrite_conv(rules), added);
  added = match_mp_rule(added, add_code);
  pushed = conv_rule(reduce_rewrite_conv(rules), pushed);
  added = match_mp_rule(added, pushed);
  thm ptr_bridge = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `v:cm_value`, `mid:int`, `st:cm_src_state`),
      get_cm_ptr_member_number_bridge()), assume_rule(
        `cm_pointer_live (st:cm_src_state) (v:cm_value)`));
  added = match_mp_rule(added,
      eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          ptr_bridge, get_cm_value_number_def(), offset_fixed,
          assume_rule(
            `(cm_ptr_view (v:cm_value)) ==
             cm_pointee (base_ty:cm_type)`))),
        `tower_add
            (cm_value_number (st:cm_src_state) (v:cm_value))
            (cm_value_number st (CMIntV ${offset:int})) ==
         cm_value_number st ${result_value:cm_value}`)));
  thm iter_two = specl_rule(TERM_LIST(
      `1:num`, `1:num`, `target:tvm_task`), get_cm_tvm_iter_add());
  added = conv_rule(rewrite_conv(THM_LIST(
      sym_rule(iter_two),
      apply_conversion(get_conversion_by_name("NUM_REDUCE_CONV"),
        `(1:num) + 1`))), added);

  term add_ann =
      `cm_ann_linear [TVMInst TVMAddOp 0i] ${push_ann:cm_annotation}`;
  term next_ann = `cm_ann_pop ((pc:int) + 2i) ${ann:cm_annotation}`;
  thm reannotated = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`,
      `[${result_value:cm_value}]:(cm_value)list`,
      add_ann, next_ann, `tvm_iter 2 (target:tvm_task)`),
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
  added = conv_rule(reduce_rewrite_conv(ann_rules), added);
  thm result = match_mp_rule(reannotated, added);

  thm_list finish_rules = cm_v_layout_rules();
  vector_add(&finish_rules, cm_update_steps_def);
  vector_add(&finish_rules, cm_task_target_sim_def);
  vector_add(&finish_rules, cm_active_spill_frames_def);
  vector_add(&finish_rules, cm_ann_linear_def);
  vector_add(&finish_rules, cm_ann_plain_def);
  vector_add(&finish_rules, cm_ann_pop_def);
  vector_add(&finish_rules, cm_code_steps_def);
  vector_add(&finish_rules, cm_member_tail_code_def);
  vector_add(&finish_rules, get_cm_layout_member_tail_length());
  vector_add(&finish_rules, assume_rule(
      `cm_ptr_member_ok (p:cm_program) (v:cm_value) (mid:int)
        (st:cm_src_state)`));
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

PROOF thm cm_target_v_member_step =
    cm_prove_target_v_member_step();

PROOF thm get_cm_target_v_member_step(void) {
  return cm_target_v_member_step;
}

PROOF static int cmc_preservation_target_value_member_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_target_value_member_axioms_before,
      "cmc_preservation_target_value_member introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_target_value_member_checks =
    cmc_preservation_target_value_member_final_checks();
