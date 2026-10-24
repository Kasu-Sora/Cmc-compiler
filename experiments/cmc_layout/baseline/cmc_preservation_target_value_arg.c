#include "proof/proof.h"
#include "userlib/proof.h"
#include "cmc_preservation_target_value_arg.h"
#include "cmc_preservation_code_value.h"
#include "cmc_preservation_target_spill_runtime.h"
#include "cmc_preservation_layout.h"
#include "cmc_preservation_code_expr.h"
#include "cmc_preservation_code_stmt.h"

#require "cmc_preservation_target_value_init.c"

PROOF static size_t _cmc_preservation_target_value_arg_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_prove_target_v_arg_cons_step(void) {
  term phase =
      `CAArgP (callee:int) ((arg:cm_expr) :: (more:(cm_expr)list))
        (values:(cm_value)list) (ret:cm_type)
        (all_args:(cm_expr)list) (base_slot:int)
        (current_slot:int) (scratch:int)`;
  term task =
      `CMVTask (p:cm_program) (fid:int) (v:cm_value)
        (st:cm_src_state)
        (CMArgK (callee:int) ((arg:cm_expr) :: (more:(cm_expr)list))
          (values:(cm_value)list) (ret:cm_type) ::
         cm_cursor_frames (rest:(cm_acursor)list))`;
  term ann =
      `CMAnnotation (pc:int) (temp:int) (breakpc:int) (continuepc:int)
        (CMACursor ${phase:cm_aphase} (owner:int)
          (saved_break:int) (saved_continue:int) ::
         (rest:(cm_acursor)list))
        (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
        (calls:(cm_call_sim_frame)list)`;
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
        (cm_spill_put (current_slot:int) (v:cm_value)
          (spills:(cm_spill)list))
        (saved:(cm_spill_frame)list)
        (calls:(cm_call_sim_frame)list)`,
      `0i <= (fid:int)`,
      `cm_tagged_span_valid (st:cm_src_state)`,
      `tower_signed64 (cm_state_fp (st:cm_src_state))`,
      `tower_signed64
        (cm_temp_offset (p:cm_program) (fid:int) (current_slot:int))`,
      `(address:int) == cm_state_fp st +
        cm_temp_offset p fid current_slot`,
      `tower_signed64 (address:int)`,
      `tower_word_valid (address:int)`),
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
  term code_rest =
      `cm_emit_args_store (p:cm_program) (fid:int)
          ((pc:int) + ilength
            (cm_temp_store_code p fid (current_slot:int)))
          ((current_slot:int) + 1i) (scratch:int)
          ((arg:cm_expr) :: (more:(cm_expr)list)) ++
       cm_emit_args_reload p fid (base_slot:int)
         (all_args:(cm_expr)list) ++
       [TVMInst TVMCallOp (cm_function_pc p (callee:int))] ++
       cm_cont_code p fid
         ((pc:int) + ilength ${phase_code:(tvm_inst)list})
         (owner:int) (rest:(cm_acursor)list)`;
  thm layout = assume_rule(
      `cm_task_layout (p:cm_program) ${task:cm_task}
        ${ann:cm_annotation}`);
  thm old_code = conjunct1_rule(conv_rule(
      rewrite_conv(THM_LIST(cm_task_layout_def)), layout));
  thm running = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_task_target_sim_def)), assume_rule(
        `cm_task_target_sim (p:cm_program) ${task:cm_task}
          (target:tvm_task) ${ann:cm_annotation}`));

  thm result = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`,
      `current_slot:int`, `v:cm_value`, `[]:(cm_value)list`,
      ann, `target:tvm_task`, code_rest, `address:int`),
      get_cm_target_temp_store_runtime());
  thm_list target_rules = cm_v_layout_rules();
  term wanted_code = dest_imp(concl(result)).tm1;
  thm wanted_view = apply_conversion(
      reduce_rewrite_conv(target_rules), wanted_code);
  thm old_normal = conv_rule(
      reduce_rewrite_conv(target_rules), old_code);
  thm code_at = eq_mp_rule(sym_rule(wanted_view), old_normal);
  result = match_mp_rule(result, code_at);
  result = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_ann_cursors_def, cm_ann_spills_def,
      cm_ann_saved_def, cm_ann_calls_def)), result);
  result = match_mp_rule(result, running);
  result = match_mp_rule(result, assume_rule(
      `cm_runtime_stack (p:cm_program)
        (cm_state_regions (st:cm_src_state)) (fid:int)
        (cm_state_fp st) (cm_state_regions st)
        (CMACursor ${phase:cm_aphase} (owner:int)
          (saved_break:int) (saved_continue:int) ::
         (rest:(cm_acursor)list))
        (cm_spill_put (current_slot:int) (v:cm_value)
          (spills:(cm_spill)list))
        (saved:(cm_spill_frame)list)
        (calls:(cm_call_sim_frame)list)`));
  result = match_mp_rule(result, assume_rule(`0i <= (fid:int)`));
  result = match_mp_rule(result, eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(get_theorem_by_name("ILENGTH_DEF"))),
      `ilength ([]:(cm_value)list) < 65534i`)));
  result = match_mp_rule(result, assume_rule(
      `cm_tagged_span_valid (st:cm_src_state)`));
  result = match_mp_rule(result, assume_rule(
      `tower_signed64 (cm_state_fp (st:cm_src_state))`));
  result = match_mp_rule(result, assume_rule(
      `tower_signed64
        (cm_temp_offset (p:cm_program) (fid:int) (current_slot:int))`));
  result = match_mp_rule(result, assume_rule(
      `(address:int) == cm_state_fp (st:cm_src_state) +
        cm_temp_offset (p:cm_program) (fid:int) (current_slot:int)`));
  result = match_mp_rule(result,
      assume_rule(`tower_signed64 (address:int)`));
  result = match_mp_rule(result,
      assume_rule(`tower_word_valid (address:int)`));

  term stored_ann =
      `cm_ann_put_spill (current_slot:int) (v:cm_value)
        (cm_ann_linear
          (cm_temp_store_code (p:cm_program) (fid:int) current_slot)
          ${ann:cm_annotation})`;
  term next_ann =
      `cm_ann_put_spill (current_slot:int) (v:cm_value)
        (cm_ann_replace
          (CAArgP (callee:int) (more:(cm_expr)list)
            ((v:cm_value) :: (values:(cm_value)list)) (ret:cm_type)
            (all_args:(cm_expr)list) (base_slot:int)
            ((current_slot:int) + 1i) (scratch:int))
          ((pc:int) + ilength
            (cm_temp_store_code (p:cm_program) (fid:int) current_slot))
          (scratch:int) (breakpc:int) (continuepc:int)
          ${ann:cm_annotation})`;
  thm reannotated = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`,
      `[]:(cm_value)list`, stored_ann, next_ann,
      `tvm_iter 5 (target:tvm_task)`), get_cm_target_reannotate());
  thm_list ann_rules = THM_LIST(
      cm_ann_linear_def, cm_ann_plain_def, cm_ann_replace_def,
      cm_ann_put_spill_def, cm_ann_spills_set_def,
      cm_ann_pc_def, cm_ann_temp_def, cm_ann_break_def,
      cm_ann_continue_def, cm_ann_cursors_def,
      cm_ann_calls_def, cm_ann_spills_def, cm_ann_saved_def,
      get_theorem_by_name("ILENGTH_DEF"));
  for (size_t premise = 0; premise < 4; ++premise) {
    reannotated = match_mp_rule(reannotated,
        eqt_elim_rule(apply_conversion(
          reduce_rewrite_conv(ann_rules),
          dest_imp(concl(reannotated)).tm1)));
  }
  result = match_mp_rule(reannotated, result);

  thm_list finish_rules = cm_v_layout_rules();
  vector_add(&finish_rules, cm_task_target_sim_def);
  vector_add(&finish_rules, cm_running_target_sim_def);
  vector_add(&finish_rules, cm_active_spill_frames_def);
  vector_add(&finish_rules, cm_update_steps_def);
  vector_add(&finish_rules, cm_code_steps_def);
  vector_add(&finish_rules, cm_ann_linear_def);
  vector_add(&finish_rules, cm_ann_plain_def);
  vector_add(&finish_rules, cm_ann_replace_def);
  vector_add(&finish_rules, cm_ann_put_spill_def);
  vector_add(&finish_rules, cm_ann_spills_set_def);
  vector_add(&finish_rules, get_theorem_by_name("APPEND"));
  vector_add(&finish_rules, get_theorem_by_name("APPEND_NIL"));
  vector_add(&finish_rules, get_theorem_by_name("ILENGTH_DEF"));
  thm num_of_int_five = spec_rule(
      `5:num`, get_theorem_by_name("NUM_OF_INT_OF_NUM"));
  gnode reduced = CONV_TAC(
      leaf, reduce_rewrite_conv(finish_rules));
  reduced = CONV_TAC(
      reduced, rewrite_conv(THM_LIST(num_of_int_five)));
  thm normalized = conv_rule(
      reduce_rewrite_conv(finish_rules), result);
  ACCEPT_TAC(reduced, normalized);
  return gnode_prove(root);
}

PROOF thm cm_target_v_arg_cons_step =
    cm_prove_target_v_arg_cons_step();

PROOF thm get_cm_target_v_arg_cons_step(void) {
  return cm_target_v_arg_cons_step;
}

PROOF static int cmc_preservation_target_value_arg_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_target_value_arg_axioms_before,
      "cmc_preservation_target_value_arg introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_target_value_arg_checks =
    cmc_preservation_target_value_arg_final_checks();
