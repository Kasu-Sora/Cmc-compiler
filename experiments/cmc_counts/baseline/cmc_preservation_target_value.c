#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_code.h"
#include "cmc_preservation_code_expr.h"
#include "cmc_preservation_code_value.h"
#include "cmc_preservation_target_value.h"
#include "cmc_preservation_target_spill_runtime.h"
#include "cmc_preservation_target_convert.h"
#include "cmc_preservation_target_spill.h"
#include "cmc_preservation_target_store.h"
#include "cmc_preservation_store_semantic.h"

#require "cmc_preservation_code_value.c"
#require "cmc_preservation_target_machine.c"
#require "cmc_preservation_target_spill_runtime.c"
#require "cmc_preservation_target_convert.c"
#require "cmc_preservation_target_spill.c"
#require "cmc_preservation_target_store.c"
#require "cmc_preservation_store_semantic.c"

PROOF static size_t _cmc_preservation_target_value_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_target_value_code_suffix(
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

PROOF static thm cm_prove_target_v_load_step(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (v:cm_value) (st:cm_src_state)
         (ty:cm_type) (pc:int) (temp:int) (breakpc:int)
         (continuepc:int) (owner:int) (saved_break:int)
         (saved_continue:int) (rest:(cm_acursor)list)
         (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
         (calls:(cm_call_sim_frame)list) (target:tvm_task).
         cm_task_layout p
           (CMVTask p fid v st
             (CMLoadK ty :: cm_cursor_frames rest))
           (CMAnnotation pc temp breakpc continuepc
             (CMACursor (CALoadP ty) owner saved_break saved_continue ::
              rest) spills saved calls) ==>
         cm_task_target_sim p
           (CMVTask p fid v st
             (CMLoadK ty :: cm_cursor_frames rest)) target
           (CMAnnotation pc temp breakpc continuepc
             (CMACursor (CALoadP ty) owner saved_break saved_continue ::
              rest) spills saved calls) ==>
         cm_runtime_memory_layout p st calls
           (CMSpillFrame fid (cm_state_fp st) spills :: saved) ==>
         cm_load_ok ty v st ==>
         (ty == CMCharTy || ty == CMIntTy || cm_is_pointer ty) ==>
         cm_live_span st (cm_value_number st v) (cm_store_width ty) ==>
         cm_task_target_sim p
           (cm_step
             (CMVTask p fid v st
               (CMLoadK ty :: cm_cursor_frames rest)))
           (tvm_iter
             (cm_update_steps
               (cm_annotation_step
                 (CMVTask p fid v st
                   (CMLoadK ty :: cm_cursor_frames rest))
                 (CMAnnotation pc temp breakpc continuepc
                   (CMACursor (CALoadP ty) owner saved_break
                     saved_continue :: rest) spills saved calls)))
             target)
           (cm_update_annotation
             (cm_annotation_step
               (CMVTask p fid v st
                 (CMLoadK ty :: cm_cursor_frames rest))
               (CMAnnotation pc temp breakpc continuepc
                 (CMACursor (CALoadP ty) owner saved_break
                   saved_continue :: rest) spills saved calls)))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  term ann =
      `CMAnnotation (pc:int) (temp:int) (breakpc:int) (continuepc:int)
        (CMACursor (CALoadP (ty:cm_type)) (owner:int)
          (saved_break:int) (saved_continue:int) ::
         (rest:(cm_acursor)list))
        (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
        (calls:(cm_call_sim_frame)list)`;
  term task =
      `CMVTask (p:cm_program) (fid:int) (v:cm_value)
        (st:cm_src_state)
        (CMLoadK (ty:cm_type) ::
         cm_cursor_frames (rest:(cm_acursor)list))`;
  thm layout = assume_rule(
      `cm_task_layout (p:cm_program) ${task:cm_task}
        ${ann:cm_annotation}`);
  thm_list code_rules = cm_v_layout_rules();
  thm opened = conv_rule(
      reduce_rewrite_conv(code_rules), layout);
  thm old_code = conjunct1_rule(opened);
  term code_rest =
      `cm_cont_code (p:cm_program) (fid:int)
        ((pc:int) + ilength (cm_load_code (ty:cm_type)))
        (owner:int) (rest:(cm_acursor)list)`;
  thm code_at = old_code;
  thm running = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_task_target_sim_def)), assume_rule(
        `cm_task_target_sim (p:cm_program) ${task:cm_task}
          (target:tvm_task) ${ann:cm_annotation}`));
  thm result = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`, `v:cm_value`,
      `[]:(cm_value)list`, ann, `target:tvm_task`, `ty:cm_type`,
      code_rest), get_cm_target_load());
  thm_list target_rules = THM_LIST(
      cm_ann_pc_def, cm_ann_calls_def, cm_ann_spills_def,
      cm_ann_saved_def, cm_active_spill_frames_def,
      get_cm_load_code_def(), cm_cont_code_def,
      cm_normal_cont_code_def, get_theorem_by_name("APPEND"),
      get_theorem_by_name("ILENGTH_DEF"));
  code_at = conv_rule(
      reduce_rewrite_conv(target_rules), code_at);
  result = conv_rule(
      reduce_rewrite_conv(target_rules), result);
  result = match_mp_rule(result, code_at);
  result = match_mp_rule(result, running);
  result = match_mp_rule(result, assume_rule(
      `cm_runtime_memory_layout (p:cm_program) (st:cm_src_state)
        (calls:(cm_call_sim_frame)list)
        (CMSpillFrame (fid:int) (cm_state_fp st)
          (spills:(cm_spill)list) ::
         (saved:(cm_spill_frame)list))`));
  result = match_mp_rule(result, assume_rule(
      `cm_load_ok (ty:cm_type) (v:cm_value) (st:cm_src_state)`));
  result = match_mp_rule(result, assume_rule(
      `(ty:cm_type) == CMCharTy || ty == CMIntTy ||
       cm_is_pointer ty`));
  result = match_mp_rule(result, assume_rule(
      `cm_live_span (st:cm_src_state)
        (cm_value_number st (v:cm_value))
        (cm_store_width (ty:cm_type))`));
  term load_code =
      `[TVMInst
          (if (ty:cm_type) == CMCharTy
           then TVMLoadBOp else TVMLoadOp) 0i]:(tvm_inst)list`;
  term linear_ann =
      `cm_ann_linear ${load_code:(tvm_inst)list}
        ${ann:cm_annotation}`;
  term popped_ann =
      `cm_ann_pop
        ((pc:int) + ilength ${load_code:(tvm_inst)list})
        ${ann:cm_annotation}`;
  thm reannotated = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`,
      `[cm_load_value (ty:cm_type) (v:cm_value)
          (st:cm_src_state)]:(cm_value)list`,
      linear_ann, popped_ann, `tvm_iter 1 (target:tvm_task)`),
      get_cm_target_reannotate());
  thm_list reannotation_rules = THM_LIST(
      cm_ann_linear_def, cm_ann_plain_def, cm_ann_pop_def,
      cm_ann_pc_def, cm_ann_temp_def, cm_ann_break_def,
      cm_ann_continue_def, cm_ann_cursors_def,
      cm_ann_calls_def, cm_ann_spills_def, cm_ann_saved_def);
  for (size_t i = 0; i < 4; ++i) {
    reannotated = match_mp_rule(reannotated,
        eqt_elim_rule(apply_conversion(
          reduce_rewrite_conv(reannotation_rules),
          dest_imp(concl(reannotated)).tm1)));
  }
  result = match_mp_rule(reannotated, result);
  thm_list goal_rules = THM_LIST(
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
      get_cm_load_code_def(), get_theorem_by_name("ILENGTH_DEF"),
      assume_rule(
        `cm_load_ok (ty:cm_type) (v:cm_value) (st:cm_src_state)`));
  thm num_of_int_one = spec_rule(
      `1:num`, get_theorem_by_name("NUM_OF_INT_OF_NUM"));
  gnode reduced = CONV_TAC(
      leaf, reduce_rewrite_conv(goal_rules));
  reduced = CONV_TAC(
      reduced, rewrite_conv(THM_LIST(num_of_int_one)));
  thm normalized = conv_rule(
      reduce_rewrite_conv(goal_rules), result);
  ACCEPT_TAC(reduced, normalized);
  return gnode_prove(root);
}
PROOF thm cm_target_v_load_step =
    cm_prove_target_v_load_step();

PROOF static thm cm_prove_target_v_assign_left_step(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (v:cm_value) (st:cm_src_state)
         (src:cm_expr) (ty:cm_type) (pc:int) (temp:int)
         (breakpc:int) (continuepc:int) (owner:int)
         (saved_break:int) (saved_continue:int)
         (rest:(cm_acursor)list) (spills:(cm_spill)list)
         (saved:(cm_spill_frame)list)
         (calls:(cm_call_sim_frame)list) (target:tvm_task)
         (address:int).
         cm_task_layout p
           (CMVTask p fid v st
             (CMAssignLK src ty :: cm_cursor_frames rest))
           (CMAnnotation pc temp breakpc continuepc
             (CMACursor (CAAssignLP src ty) owner saved_break
               saved_continue :: rest) spills saved calls) ==>
         cm_task_target_sim p
           (CMVTask p fid v st
             (CMAssignLK src ty :: cm_cursor_frames rest)) target
           (CMAnnotation pc temp breakpc continuepc
             (CMACursor (CAAssignLP src ty) owner saved_break
               saved_continue :: rest) spills saved calls) ==>
         cm_runtime_stack p (cm_state_regions st) fid
           (cm_state_fp st) (cm_state_regions st)
           (CMACursor (CAAssignLP src ty) owner saved_break
             saved_continue :: rest)
           (cm_spill_put owner v spills) saved calls ==>
         0i <= fid ==>
         temp == owner ==>
         cm_tagged_span_valid st ==>
         tower_signed64 (cm_state_fp st) ==>
         tower_signed64 (cm_temp_offset p fid owner) ==>
         address == cm_state_fp st + cm_temp_offset p fid owner ==>
         tower_signed64 address ==>
         tower_word_valid address ==>
         cm_task_target_sim p
           (cm_step
             (CMVTask p fid v st
               (CMAssignLK src ty :: cm_cursor_frames rest)))
           (tvm_iter
             (cm_update_steps
               (cm_annotation_step
                 (CMVTask p fid v st
                   (CMAssignLK src ty :: cm_cursor_frames rest))
                 (CMAnnotation pc temp breakpc continuepc
                   (CMACursor (CAAssignLP src ty) owner saved_break
                     saved_continue :: rest) spills saved calls)))
             target)
           (cm_update_annotation
             (cm_annotation_step
               (CMVTask p fid v st
                 (CMAssignLK src ty :: cm_cursor_frames rest))
               (CMAnnotation pc temp breakpc continuepc
                 (CMACursor (CAAssignLP src ty) owner saved_break
                   saved_continue :: rest) spills saved calls)))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  term ann =
      `CMAnnotation (pc:int) (temp:int) (breakpc:int) (continuepc:int)
        (CMACursor
          (CAAssignLP (src:cm_expr) (ty:cm_type)) (owner:int)
          (saved_break:int) (saved_continue:int) ::
         (rest:(cm_acursor)list))
        (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
        (calls:(cm_call_sim_frame)list)`;
  term task =
      `CMVTask (p:cm_program) (fid:int) (v:cm_value)
        (st:cm_src_state)
        (CMAssignLK (src:cm_expr) (ty:cm_type) ::
         cm_cursor_frames (rest:(cm_acursor)list))`;
  thm layout = assume_rule(
      `cm_task_layout (p:cm_program) ${task:cm_task}
        ${ann:cm_annotation}`);
  thm opened = conv_rule(
      reduce_rewrite_conv(cm_v_layout_rules()), layout);
  thm code_at = conjunct1_rule(opened);
  thm running = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_task_target_sim_def)), assume_rule(
        `cm_task_target_sim (p:cm_program) ${task:cm_task}
          (target:tvm_task) ${ann:cm_annotation}`));
  term code_rest =
      `cm_rcode_of
          (cm_emit_expr_pair (p:cm_program) (fid:int)
            ((pc:int) + 5i) ((owner:int) + 1i) (src:cm_expr)) ++
       cm_char_normalize_code (ty:cm_type) ++
       cm_temp_load_code p fid (owner:int) ++
       cm_store_code ty ++
       cm_temp_load_code p fid owner ++
       cm_load_code ty ++
       cm_cursor_code p fid
         ((pc:int) + 5i +
          cm_rcount_of (cm_expr_code_counts p fid src) +
          (if ty == CMCharTy then 6i else 0i) + 12i)
         (owner:int) F (rest:(cm_acursor)list)`;
  thm result = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`,
      `owner:int`, `v:cm_value`, `[]:(cm_value)list`,
      ann, `target:tvm_task`, code_rest, `address:int`),
      get_cm_target_temp_store_runtime());
  thm_list target_rules = THM_LIST(
      cm_ann_pc_def, cm_ann_temp_def, cm_ann_break_def,
      cm_ann_continue_def, cm_ann_cursors_def,
      cm_ann_calls_def, cm_ann_spills_def, cm_ann_saved_def,
      cm_active_spill_frames_def, cm_value_phase_code_def,
      cm_cursor_code_def, cm_cont_code_def,
      cm_normal_cont_code_def, cm_phase_stops_def,
      cm_phase_yields_normal_def,
      get_theorem_by_name("APPEND"),
      get_theorem_by_name("APPEND_NIL"));
  code_at = conv_rule(reduce_rewrite_conv(target_rules), code_at);
  result = conv_rule(reduce_rewrite_conv(target_rules), result);
  result = match_mp_rule(result, code_at);
  result = match_mp_rule(result, running);
  result = match_mp_rule(result, assume_rule(
      `cm_runtime_stack (p:cm_program)
        (cm_state_regions (st:cm_src_state)) (fid:int)
        (cm_state_fp st) (cm_state_regions st)
        (CMACursor
          (CAAssignLP (src:cm_expr) (ty:cm_type)) (owner:int)
          (saved_break:int) (saved_continue:int) ::
         (rest:(cm_acursor)list))
        (cm_spill_put owner v (spills:(cm_spill)list))
        (saved:(cm_spill_frame)list)
        (calls:(cm_call_sim_frame)list)`));
  result = match_mp_rule(result, assume_rule(`0i <= (fid:int)`));
  result = match_mp_rule(result,
      eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          get_theorem_by_name("ILENGTH_DEF"))),
        `ilength ([]:(cm_value)list) < 65534i`)));
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
          (CAAssignRP (v:cm_value) (ty:cm_type))
          ((pc:int) +
           ilength (cm_temp_store_code (p:cm_program) (fid:int) owner))
          ((owner:int) + 1i) (breakpc:int) (continuepc:int)
          ${ann:cm_annotation})`;
  thm reannotated = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`,
      `[]:(cm_value)list`, stored_ann, next_ann,
      `tvm_iter 5 (target:tvm_task)`), get_cm_target_reannotate());
  thm_list reannotation_rules = THM_LIST(
      cm_ann_linear_def, cm_ann_plain_def, cm_ann_replace_def,
      cm_ann_put_spill_def, cm_ann_spills_set_def,
      cm_ann_pc_def, cm_ann_temp_def, cm_ann_break_def,
      cm_ann_continue_def, cm_ann_cursors_def,
      cm_ann_calls_def, cm_ann_spills_def, cm_ann_saved_def,
      get_theorem_by_name("ILENGTH_DEF"));
  for (size_t i = 0; i < 4; ++i) {
    reannotated = match_mp_rule(reannotated,
        eqt_elim_rule(apply_conversion(
          reduce_rewrite_conv(reannotation_rules),
          dest_imp(concl(reannotated)).tm1)));
  }
  result = match_mp_rule(reannotated, result);
  thm_list goal_rules = THM_LIST(
      get_cm_step_def(), get_cm_vapply_def(),
      cm_annotation_step_def, cm_update_v_def,
      cm_update_steps_def, cm_update_annotation_def,
      cm_task_target_sim_def, cm_active_spill_frames_def,
      cm_ann_linear_def, cm_ann_plain_def, cm_ann_replace_def,
      cm_ann_put_spill_def, cm_ann_spills_set_def,
      cm_ann_pc_def, cm_ann_temp_def, cm_ann_break_def,
      cm_ann_continue_def, cm_ann_cursors_def,
      cm_ann_calls_def, cm_ann_spills_def, cm_ann_saved_def,
      cm_cursor_phase_def, cm_cursor_temp_def,
      cm_cursor_break_def, cm_cursor_continue_def,
      get_theorem_by_name("HD"), get_theorem_by_name("TL"),
      get_theorem_by_name("NOT_CONS_NIL"), cm_code_steps_def,
      get_cm_layout_temp_store_length(),
      assume_rule(`(temp:int) == (owner:int)`),
      get_theorem_by_name("ILENGTH_DEF"));
  gnode reduced = CONV_TAC(
      leaf, reduce_rewrite_conv(goal_rules));
  thm num_of_int_five = spec_rule(
      `5:num`, get_theorem_by_name("NUM_OF_INT_OF_NUM"));
  reduced = CONV_TAC(
      reduced, rewrite_conv(THM_LIST(num_of_int_five)));
  thm normalized = conv_rule(
      reduce_rewrite_conv(goal_rules), result);
  ACCEPT_TAC(reduced, normalized);
  return gnode_prove(root);
}
PROOF thm cm_target_v_assign_left_step =
    cm_prove_target_v_assign_left_step();

PROOF static thm cm_prove_target_v_assign_right_step(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (v:cm_value) (ptr:cm_value)
         (st:cm_src_state) (ty:cm_type)
         (pc:int) (temp:int) (breakpc:int) (continuepc:int)
         (owner:int) (saved_break:int) (saved_continue:int)
         (rest:(cm_acursor)list) (spills:(cm_spill)list)
         (saved:(cm_spill_frame)list)
         (calls:(cm_call_sim_frame)list) (target:tvm_task)
         (address:int).
         cm_task_layout p
           (CMVTask p fid v st
             (CMAssignRK ptr ty :: cm_cursor_frames rest))
           (CMAnnotation pc temp breakpc continuepc
             (CMACursor (CAAssignRP ptr ty) owner saved_break
               saved_continue :: rest) spills saved calls) ==>
         cm_task_target_sim p
           (CMVTask p fid v st
             (CMAssignRK ptr ty :: cm_cursor_frames rest))
           target
           (CMAnnotation pc temp breakpc continuepc
             (CMACursor (CAAssignRP ptr ty) owner saved_break
               saved_continue :: rest) spills saved calls) ==>
         cm_runtime_memory_layout p st calls
           (CMSpillFrame fid (cm_state_fp st) spills :: saved) ==>
         cm_spill_holds owner ptr spills ==>
         cm_store_ok ty ptr st ==>
         (ty == CMCharTy || ty == CMIntTy || cm_is_pointer ty) ==>
         cm_scalar_expr_type ty ==>
         cm_value_convertible_to v ty ==>
         cm_live_span st (cm_value_number st ptr)
           (cm_store_width ty) ==>
         tower_signed64 (cm_state_fp st) ==>
         tower_signed64 (cm_temp_offset p fid owner) ==>
         address == cm_state_fp st + cm_temp_offset p fid owner ==>
         tower_signed64 address ==>
         tower_word_valid address ==>
         cm_task_target_sim p
           (cm_step
             (CMVTask p fid v st
               (CMAssignRK ptr ty :: cm_cursor_frames rest)))
           (tvm_iter
             (cm_update_steps
               (cm_annotation_step
                 (CMVTask p fid v st
                   (CMAssignRK ptr ty :: cm_cursor_frames rest))
                 (CMAnnotation pc temp breakpc continuepc
                   (CMACursor (CAAssignRP ptr ty) owner saved_break
                     saved_continue :: rest) spills saved calls)))
             target)
           (cm_update_annotation
             (cm_annotation_step
               (CMVTask p fid v st
                 (CMAssignRK ptr ty :: cm_cursor_frames rest))
               (CMAnnotation pc temp breakpc continuepc
                 (CMACursor (CAAssignRP ptr ty) owner saved_break
                   saved_continue :: rest) spills saved calls)))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  term ann =
      `CMAnnotation (pc:int) (temp:int) (breakpc:int) (continuepc:int)
        (CMACursor
          (CAAssignRP (ptr:cm_value) (ty:cm_type)) (owner:int)
          (saved_break:int) (saved_continue:int) ::
         (rest:(cm_acursor)list))
        (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
        (calls:(cm_call_sim_frame)list)`;
  term task =
      `CMVTask (p:cm_program) (fid:int) (v:cm_value)
        (st:cm_src_state)
        (CMAssignRK (ptr:cm_value) (ty:cm_type) ::
         cm_cursor_frames (rest:(cm_acursor)list))`;
  term converted =
      `cm_convert_value (st:cm_src_state) (ty:cm_type) (v:cm_value)`;
  term new_state =
      `cm_state_store (ty:cm_type) (ptr:cm_value) (v:cm_value)
        (st:cm_src_state)`;
  term code = `cm_model_code (p:cm_program)`;
  term normalize_code =
      `cm_char_normalize_code (ty:cm_type)`;
  term temp_load =
      `cm_temp_load_code (p:cm_program) (fid:int) (owner:int)`;
  term store_code = `cm_store_code (ty:cm_type)`;
  term load_code = `cm_load_code (ty:cm_type)`;
  term code_rest =
      `cm_cont_code (p:cm_program) (fid:int)
        ((pc:int) +
         ilength
           (cm_assign_tail_code p fid (ty:cm_type) (owner:int)))
        (owner:int) (rest:(cm_acursor)list)`;
  term suffix1 =
      `${temp_load:(tvm_inst)list} ++
       ${store_code:(tvm_inst)list} ++
       ${temp_load:(tvm_inst)list} ++
       ${load_code:(tvm_inst)list} ++
       ${code_rest:(tvm_inst)list}`;
  term suffix2 =
      `${store_code:(tvm_inst)list} ++
       ${temp_load:(tvm_inst)list} ++
       ${load_code:(tvm_inst)list} ++
       ${code_rest:(tvm_inst)list}`;
  term suffix3 =
      `${temp_load:(tvm_inst)list} ++
       ${load_code:(tvm_inst)list} ++
       ${code_rest:(tvm_inst)list}`;
  term suffix4 =
      `${load_code:(tvm_inst)list} ++
       ${code_rest:(tvm_inst)list}`;
  term ann1 =
      `cm_ann_linear ${normalize_code:(tvm_inst)list}
        ${ann:cm_annotation}`;
  term ann2 =
      `cm_ann_linear ${temp_load:(tvm_inst)list}
        ${ann1:cm_annotation}`;
  term ann3 =
      `cm_ann_linear ${store_code:(tvm_inst)list}
        ${ann2:cm_annotation}`;
  term ann4 =
      `cm_ann_linear ${temp_load:(tvm_inst)list}
        ${ann3:cm_annotation}`;
  term ann5 =
      `cm_ann_linear ${load_code:(tvm_inst)list}
        ${ann4:cm_annotation}`;
  term target1 =
      `tvm_iter
        (cm_code_steps ${normalize_code:(tvm_inst)list})
        (target:tvm_task)`;
  term target2 = `tvm_iter 5 ${target1:tvm_task}`;
  term target3 = `tvm_iter 1 ${target2:tvm_task}`;
  term target4 = `tvm_iter 5 ${target3:tvm_task}`;
  term target5 = `tvm_iter 1 ${target4:tvm_task}`;

  thm layout = assume_rule(
      `cm_task_layout (p:cm_program) ${task:cm_task}
        ${ann:cm_annotation}`);
  thm opened = conv_rule(
      reduce_rewrite_conv(cm_v_layout_rules()), layout);
  thm old_code = conjunct1_rule(opened);
  thm_list code_rules = cm_v_layout_rules();
  vector_add(&code_rules, get_cm_char_normalize_code_def());
  vector_add(&code_rules, get_cm_temp_load_code_def());
  vector_add(&code_rules, get_cm_store_code_def());
  vector_add(&code_rules, get_cm_load_code_def());
  vector_add(&code_rules, get_cm_push_code_def());
  vector_add(&code_rules, cm_ann_linear_def);
  vector_add(&code_rules, cm_ann_plain_def);
  vector_add(&code_rules, cm_ann_pc_def);
  vector_add(&code_rules, cm_ann_temp_def);
  vector_add(&code_rules, cm_ann_break_def);
  vector_add(&code_rules, cm_ann_continue_def);
  vector_add(&code_rules, cm_ann_cursors_def);
  vector_add(&code_rules, cm_ann_calls_def);
  vector_add(&code_rules, cm_ann_spills_def);
  vector_add(&code_rules, cm_ann_saved_def);
  vector_add(&code_rules, cm_active_spill_frames_def);
  vector_add(&code_rules, get_theorem_by_name("APPEND"));
  vector_add(&code_rules, get_theorem_by_name("APPEND_NIL"));
  vector_add(&code_rules, get_theorem_by_name("ILENGTH_DEF"));
  old_code = conv_rule(
      reduce_rewrite_conv(code_rules), old_code);
  thm code1 = cm_target_value_code_suffix(
      old_code, code, ann, normalize_code, suffix1, ann1,
      code_rules);
  thm code2 = cm_target_value_code_suffix(
      code1, code, ann1, temp_load, suffix2, ann2,
      code_rules);
  thm code3 = cm_target_value_code_suffix(
      code2, code, ann2, store_code, suffix3, ann3,
      code_rules);
  thm code4 = cm_target_value_code_suffix(
      code3, code, ann3, temp_load, suffix4, ann4,
      code_rules);

  thm running = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_task_target_sim_def)), assume_rule(
        `cm_task_target_sim (p:cm_program) ${task:cm_task}
          (target:tvm_task) ${ann:cm_annotation}`));
  thm capacity_nil = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF"))),
      `ilength ([]:(cm_value)list) < 65535i`));
  thm signed_value = specl_rule(TERM_LIST(
      `st:cm_src_state`, `v:cm_value`),
      get_cm_value_number_signed_bridge());
  thm normalized_sim = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`,
      `ty:cm_type`, `v:cm_value`, `[]:(cm_value)list`,
      ann, `target:tvm_task`, suffix1),
      get_cm_target_char_normalize());
  normalized_sim = conv_rule(
      reduce_rewrite_conv(code_rules), normalized_sim);
  normalized_sim = match_mp_rule(normalized_sim, old_code);
  normalized_sim = match_mp_rule(normalized_sim, running);
  normalized_sim = match_mp_rule(normalized_sim, signed_value);

  thm spill = assume_rule(
      `cm_spill_holds (owner:int) (ptr:cm_value)
        (spills:(cm_spill)list)`);
  thm spill1 = conv_rule(
      reduce_rewrite_conv(code_rules), spill);
  thm capacity_one = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF"))),
      `ilength
        ([${converted:cm_value}]:(cm_value)list) < 65535i`));
  thm loaded_ptr1 = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`,
      `owner:int`, `ptr:cm_value`,
      `[${converted:cm_value}]:(cm_value)list`,
      ann1, target1, suffix2, `address:int`),
      get_cm_target_temp_load());
  loaded_ptr1 = conv_rule(
      reduce_rewrite_conv(code_rules), loaded_ptr1);
  loaded_ptr1 = match_mp_rule(loaded_ptr1,
      conv_rule(reduce_rewrite_conv(code_rules), code1));
  loaded_ptr1 = match_mp_rule(loaded_ptr1, normalized_sim);
  loaded_ptr1 = match_mp_rule(loaded_ptr1, spill1);
  loaded_ptr1 = match_mp_rule(loaded_ptr1, assume_rule(
      `tower_signed64 (cm_state_fp (st:cm_src_state))`));
  loaded_ptr1 = match_mp_rule(loaded_ptr1, assume_rule(
      `tower_signed64
        (cm_temp_offset (p:cm_program) (fid:int) (owner:int))`));
  loaded_ptr1 = match_mp_rule(loaded_ptr1, assume_rule(
      `(address:int) == cm_state_fp (st:cm_src_state) +
        cm_temp_offset (p:cm_program) (fid:int) (owner:int)`));
  loaded_ptr1 = match_mp_rule(loaded_ptr1,
      assume_rule(`tower_signed64 (address:int)`));
  loaded_ptr1 = match_mp_rule(loaded_ptr1,
      assume_rule(`tower_word_valid (address:int)`));

  thm runtime = assume_rule(
      `cm_runtime_memory_layout (p:cm_program) (st:cm_src_state)
        (calls:(cm_call_sim_frame)list)
        (CMSpillFrame (fid:int) (cm_state_fp st)
          (spills:(cm_spill)list) ::
         (saved:(cm_spill_frame)list))`);
  thm runtime2 = conv_rule(
      reduce_rewrite_conv(code_rules), runtime);
  thm store_ok = assume_rule(
      `cm_store_ok (ty:cm_type) (ptr:cm_value) (st:cm_src_state)`);
  thm kinds = assume_rule(
      `(ty:cm_type) == CMCharTy || ty == CMIntTy ||
       cm_is_pointer ty`);
  thm scalar = assume_rule(`cm_scalar_expr_type (ty:cm_type)`);
  thm convertible = assume_rule(
      `cm_value_convertible_to (v:cm_value) (ty:cm_type)`);
  thm live = assume_rule(
      `cm_live_span (st:cm_src_state)
        (cm_value_number st (ptr:cm_value))
        (cm_store_width (ty:cm_type))`);
  thm stored = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`,
      `ptr:cm_value`, converted, `[]:(cm_value)list`,
      ann2, target2, `ty:cm_type`, suffix3),
      get_cm_target_store());
  stored = conv_rule(
      reduce_rewrite_conv(code_rules), stored);
  stored = match_mp_rule(stored,
      conv_rule(reduce_rewrite_conv(code_rules), code2));
  stored = match_mp_rule(stored, loaded_ptr1);
  stored = match_mp_rule(stored, runtime2);
  stored = match_mp_rule(stored, store_ok);
  stored = match_mp_rule(stored, kinds);
  stored = match_mp_rule(stored, live);
  thm store_equality = specl_rule(TERM_LIST(
      `ty:cm_type`, `ptr:cm_value`, `v:cm_value`,
      `st:cm_src_state`), get_cm_state_store_converted());
  stored = conv_rule(
      rewrite_conv(THM_LIST(store_equality)), stored);

  thm runtime_new = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `ty:cm_type`, `ptr:cm_value`,
      `v:cm_value`, `st:cm_src_state`,
      `calls:(cm_call_sim_frame)list`,
      `CMSpillFrame (fid:int) (cm_state_fp st)
         (spills:(cm_spill)list) ::
       (saved:(cm_spill_frame)list)`),
      get_cm_store_runtime_layout()), runtime);
  thm live_new = mp_rule(specl_rule(TERM_LIST(
      `ty:cm_type`, `ptr:cm_value`, `v:cm_value`,
      `st:cm_src_state`,
      `cm_value_number (st:cm_src_state) (ptr:cm_value)`,
      `cm_store_width (ty:cm_type)`),
      get_cm_store_live_span()), live);
  thm load_ok_new = get_cm_store_load_ok();
  load_ok_new = match_mp_rule(load_ok_new, store_ok);
  load_ok_new = match_mp_rule(load_ok_new, kinds);
  load_ok_new = match_mp_rule(load_ok_new, scalar);
  load_ok_new = match_mp_rule(load_ok_new, convertible);
  thm_list state_rules = get_cm_state_core_defs();
  vector_add(&state_rules, get_cm_state_store_def());
  thm_list load2_rules = (thm_list)vector_copy(code_rules);
  vector_add(&load2_rules, get_cm_value_number_state_store());
  for (size_t i = 0; i < vector_size(state_rules); ++i) {
    vector_add(&load2_rules, state_rules[i]);
  }
  thm spill3 = conv_rule(
      reduce_rewrite_conv(code_rules), spill);
  thm loaded_ptr2 = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, new_state,
      `owner:int`, `ptr:cm_value`, `[]:(cm_value)list`,
      ann3, target3, suffix4, `address:int`),
      get_cm_target_temp_load());
  loaded_ptr2 = conv_rule(
      reduce_rewrite_conv(load2_rules), loaded_ptr2);
  loaded_ptr2 = match_mp_rule(loaded_ptr2,
      conv_rule(reduce_rewrite_conv(load2_rules), code3));
  loaded_ptr2 = match_mp_rule(loaded_ptr2,
      conv_rule(reduce_rewrite_conv(load2_rules), stored));
  loaded_ptr2 = match_mp_rule(loaded_ptr2, spill3);
  loaded_ptr2 = match_mp_rule(loaded_ptr2,
      conv_rule(reduce_rewrite_conv(state_rules), assume_rule(
        `tower_signed64 (cm_state_fp (st:cm_src_state))`)));
  loaded_ptr2 = match_mp_rule(loaded_ptr2, assume_rule(
      `tower_signed64
        (cm_temp_offset (p:cm_program) (fid:int) (owner:int))`));
  loaded_ptr2 = match_mp_rule(loaded_ptr2,
      conv_rule(reduce_rewrite_conv(state_rules), assume_rule(
        `(address:int) == cm_state_fp (st:cm_src_state) +
          cm_temp_offset (p:cm_program) (fid:int) (owner:int)`)));
  loaded_ptr2 = match_mp_rule(loaded_ptr2,
      assume_rule(`tower_signed64 (address:int)`));
  loaded_ptr2 = match_mp_rule(loaded_ptr2,
      assume_rule(`tower_word_valid (address:int)`));

  thm loaded_value = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, new_state, `ptr:cm_value`,
      `[]:(cm_value)list`, ann4, target4,
      `ty:cm_type`, code_rest), get_cm_target_load());
  loaded_value = conv_rule(
      reduce_rewrite_conv(load2_rules), loaded_value);
  loaded_value = match_mp_rule(loaded_value,
      conv_rule(reduce_rewrite_conv(load2_rules), code4));
  loaded_value = match_mp_rule(loaded_value, loaded_ptr2);
  loaded_value = match_mp_rule(loaded_value,
      conv_rule(reduce_rewrite_conv(load2_rules), runtime_new));
  loaded_value = match_mp_rule(loaded_value,
      conv_rule(reduce_rewrite_conv(load2_rules), load_ok_new));
  loaded_value = match_mp_rule(loaded_value, kinds);
  loaded_value = match_mp_rule(loaded_value,
      conv_rule(reduce_rewrite_conv(load2_rules), live_new));

  thm number_equal = mp_rule(specl_rule(TERM_LIST(
      `ty:cm_type`, `ptr:cm_value`, `v:cm_value`,
      `st:cm_src_state`), get_cm_store_load_number()), kinds);
  thm revalue_rule = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, new_state,
      `cm_load_value (ty:cm_type) (ptr:cm_value)
        ${new_state:cm_src_state}`,
      converted, `[]:(cm_value)list`, ann5, target5),
      get_cm_target_revalue());
  revalue_rule = conv_rule(
      reduce_rewrite_conv(load2_rules), revalue_rule);
  thm revalued = match_mp_rule(match_mp_rule(
      revalue_rule,
      conv_rule(reduce_rewrite_conv(load2_rules), number_equal)),
      loaded_value);

  term final_ann =
      `cm_ann_pop
        ((pc:int) +
         ilength
           (cm_assign_tail_code (p:cm_program) (fid:int)
             (ty:cm_type) (owner:int)))
        ${ann:cm_annotation}`;
  thm reannotated = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, new_state,
      `[${converted:cm_value}]:(cm_value)list`,
      ann5, final_ann, target5),
      get_cm_target_reannotate());
  thm_list ann_rules = (thm_list)vector_copy(code_rules);
  vector_add(&ann_rules, cm_ann_pop_def);
  for (size_t i = 0; i < 4; ++i) {
    term premise = dest_imp(concl(reannotated)).tm1;
    thm premise_view = apply_conversion(
        reduce_rewrite_conv(ann_rules), premise);
    thm premise_normal = eqt_elim_rule(
        apply_conversion(reduce_rewrite_conv(ann_rules),
          rhs_of(premise_view)));
    reannotated = match_mp_rule(reannotated,
        eq_mp_rule(sym_rule(premise_view), premise_normal));
  }
  reannotated = conv_rule(
      reduce_rewrite_conv(load2_rules), reannotated);
  reannotated = match_mp_rule(reannotated, revalued);

  thm_list goal_rules = cm_v_layout_rules();
  vector_add(&goal_rules, get_cm_state_store_converted());
  vector_add(&goal_rules, cm_update_steps_def);
  vector_add(&goal_rules, get_cm_state_store_def());
  vector_add(&goal_rules, get_cm_state_make_def());
  vector_add(&goal_rules, cm_task_target_sim_def);
  vector_add(&goal_rules, cm_active_spill_frames_def);
  vector_add(&goal_rules, cm_code_steps_def);
  vector_add(&goal_rules, get_cm_char_normalize_code_def());
  vector_add(&goal_rules, get_cm_temp_load_code_def());
  vector_add(&goal_rules, get_cm_store_code_def());
  vector_add(&goal_rules, get_cm_load_code_def());
  vector_add(&goal_rules, get_cm_push_code_def());
  vector_add(&goal_rules, cm_ann_linear_def);
  vector_add(&goal_rules, cm_ann_plain_def);
  vector_add(&goal_rules, cm_ann_pop_def);
  vector_add(&goal_rules, cm_ann_pc_def);
  vector_add(&goal_rules, cm_ann_temp_def);
  vector_add(&goal_rules, cm_ann_break_def);
  vector_add(&goal_rules, cm_ann_continue_def);
  vector_add(&goal_rules, cm_ann_cursors_def);
  vector_add(&goal_rules, cm_ann_calls_def);
  vector_add(&goal_rules, cm_ann_spills_def);
  vector_add(&goal_rules, cm_ann_saved_def);
  vector_add(&goal_rules, get_theorem_by_name("APPEND"));
  vector_add(&goal_rules, get_theorem_by_name("APPEND_NIL"));
  vector_add(&goal_rules, get_theorem_by_name("ILENGTH_APPEND"));
  vector_add(&goal_rules, get_theorem_by_name("ILENGTH_DEF"));
  vector_add(&goal_rules, store_ok);
  vector_add(&goal_rules, get_theorem_by_name("HD"));
  vector_add(&goal_rules, get_theorem_by_name("TL"));
  vector_add(&goal_rules, get_theorem_by_name("NOT_CONS_NIL"));
  thm_list numeral_rules = THM_LIST();
  term_list numerals = TERM_LIST(`0:num`, `1:num`, `5:num`, `6:num`,
      `12:num`, `18:num`);
  for (size_t i = 0; i < vector_size(numerals); ++i) {
    vector_add(&numeral_rules, spec_rule(
        numerals[i], get_theorem_by_name("NUM_OF_INT_OF_NUM")));
  }
  vector_add(&goal_rules, conjunct1_rule(get_tvm_iter_def()));
  term iter_index = `0`;
  for (size_t i = 0; i < 18; ++i) {
    thm successor = apply_conversion(
        get_conversion_by_name("NUM_SUC_CONV"),
        mk_comb(`SUC`, iter_index));
    vector_add(&goal_rules, conv_rule(
        rewrite_conv(THM_LIST(successor)),
        spec_rule(iter_index, conjunct2_rule(get_tvm_iter_def()))));
    iter_index = rhs_of(successor);
  }
  gnode_list char_cases = BOOL_CASES_TAC(
      leaf, `(ty:cm_type) == CMCharTy`, "Hchar");
  for (size_t i = 0; i < vector_size(char_cases); ++i) {
    thm type_case = assume_rule(i == 0
        ? `(ty:cm_type) == CMCharTy`
        : `~((ty:cm_type) == CMCharTy)`);
    thm_list branch_rules = (thm_list)vector_copy(goal_rules);
    vector_add(&branch_rules, type_case);
    vector_add(&branch_rules, conv_rule(
        reduce_rewrite_conv(THM_LIST(type_case)), store_ok));
    conv normalize = then_conv(
        then_conv(reduce_rewrite_conv(branch_rules),
          rewrite_conv(numeral_rules)),
        reduce_rewrite_conv(branch_rules));
    thm normalized = conv_rule(normalize, reannotated);
    thm target_view =
        apply_conversion(normalize, goal_ccl(char_cases[i]->g));
    ACCEPT_TAC(char_cases[i],
        eq_mp_rule(sym_rule(target_view), normalized));
  }
  return gnode_prove(root);
}

PROOF thm cm_target_v_assign_right_step =
    cm_prove_target_v_assign_right_step();

PROOF thm get_cm_target_v_load_step(void) {
  return cm_target_v_load_step;
}
PROOF thm get_cm_target_v_assign_left_step(void) {
  return cm_target_v_assign_left_step;
}
PROOF thm get_cm_target_v_assign_right_step(void) {
  return cm_target_v_assign_right_step;
}

PROOF static int cmc_preservation_target_value_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_target_value_axioms_before,
      "cmc_preservation_target_value introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_target_value_checks =
    cmc_preservation_target_value_final_checks();
