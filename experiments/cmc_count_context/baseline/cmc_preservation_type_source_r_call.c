#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_type_source_r_call.h"
#include "cmc_preservation_source_conditions.h"
#include "cmc_preservation_type_cursor.h"
#include "cmc_preservation_ready_coordinate.h"

#require "cmc_preservation_type_source_r_struct.c"
#require "cmc_preservation_source_conditions.c"

PROOF static size_t _cmc_preservation_type_source_r_call_axioms_before =
    vector_size(get_all_axioms());

PROOF static bool cm_tsrc_has_conjunct(term whole, term wanted) {
  if (alpha_compare(whole, wanted) == 0) return true;
  if (!is_conj(whole)) return false;
  struct dest_conj_results parts = dest_conj(whole);
  return cm_tsrc_has_conjunct(parts.tm1, wanted) ||
      cm_tsrc_has_conjunct(parts.tm2, wanted);
}

PROOF static thm cm_tsrc_pick_conjunct(thm fact, term wanted) {
  if (alpha_compare(concl(fact), wanted) == 0) return fact;
  struct dest_conj_results parts = dest_conj(concl(fact));
  return cm_tsrc_has_conjunct(parts.tm1, wanted)
      ? cm_tsrc_pick_conjunct(conjunct1_rule(fact), wanted)
      : cm_tsrc_pick_conjunct(conjunct2_rule(fact), wanted);
}

PROOF static thm cm_prove_r_call_cons_type_ready_step(void) {
  term expression =
      `CMCallE (callee:int)
        ((arg:cm_expr) :: (args:(cm_expr)list)) (ty:cm_type)`;
  term task =
      `CMRTask (q:cm_program) (fid:int) ${expression:cm_expr}
        (st:cm_src_state) (ks:(cm_frame)list)`;
  term function =
      `inth (fid:int) (cm_program_functions (p:cm_program))`;
  term params =
      `cm_function_params
        (inth (callee:int) (cm_program_functions (p:cm_program)))`;
  term old_cursors = `cm_ann_cursors (ann:cm_annotation)`;
  term phase =
      `CAArgP (callee:int) (args:(cm_expr)list) [] (ty:cm_type)
        ((arg:cm_expr) :: args)
        (cm_ann_temp (ann:cm_annotation)) (cm_ann_temp ann)
        (cm_ann_temp ann + ilength (arg :: args))`;
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (q:cm_program) (fid:int) (callee:int)
         (arg:cm_expr) (args:(cm_expr)list) (ty:cm_type)
         (st:cm_src_state) (ks:(cm_frame)list)
         (ann:cm_annotation).
         cm_typed_program p ==>
         cm_task_succeeds
           (CMRTask q fid (CMCallE callee (arg :: args) ty) st ks) ==>
         cm_annotation_erases
           (CMRTask q fid (CMCallE callee (arg :: args) ty) st ks) ann ==>
         cm_task_type_ready p
           (CMRTask q fid (CMCallE callee (arg :: args) ty) st ks) ann ==>
         cm_task_type_ready p
           (cm_step
             (CMRTask q fid (CMCallE callee (arg :: args) ty) st ks))
           (cm_update_annotation
             (cm_annotation_step
               (CMRTask q fid (CMCallE callee (arg :: args) ty) st ks)
               ann))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm task_ready = assume_rule(
      `cm_task_type_ready (p:cm_program) ${task:cm_task}
        (ann:cm_annotation)`);
  thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_task_type_ready_def())), task_ready);
  thm same_program = cm_tsrc_pick_conjunct(
      opened, `(q:cm_program) == (p:cm_program)`);
  thm expression_wf = cm_tsrc_pick_conjunct(opened,
      `cm_expr_wf (p:cm_program) ${function:cm_function_d}
        ${expression:cm_expr}`);
  thm parent_input = cm_tsrc_pick_conjunct(opened,
      `cm_cursor_head_input_type_ready (p:cm_program) (fid:int)
        (cm_expr_type ${expression:cm_expr})
        ${old_cursors:(cm_acursor)list}`);
  thm wf_open = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_expr_wf_def())), expression_wf);
  thm callee_low = cm_tsrc_pick_conjunct(
      wf_open, `0i <= (callee:int)`);
  thm callee_high = cm_tsrc_pick_conjunct(wf_open,
      `(callee:int) < ilength
        (cm_program_functions (p:cm_program))`);
  thm ret_equal = cm_tsrc_pick_conjunct(wf_open,
      `(ty:cm_type) == cm_function_ret
        (inth (callee:int) (cm_program_functions (p:cm_program)))`);
  thm slots_nonempty = cm_tsrc_pick_conjunct(wf_open,
      `~(${params:(cm_slot_d)list} == [])`);
  thm arg_wf = cm_tsrc_pick_conjunct(wf_open,
      `cm_expr_wf (p:cm_program) ${function:cm_function_d}
        (arg:cm_expr)`);
  thm arg_convertible = cm_tsrc_pick_conjunct(wf_open,
      `cm_expr_convertible (arg:cm_expr)
        (cm_slot_ty (HD ${params:(cm_slot_d)list}))`);
  thm tail_wf = cm_tsrc_pick_conjunct(wf_open,
      `cm_args_wf (p:cm_program) ${function:cm_function_d}
        (args:(cm_expr)list) (TL ${params:(cm_slot_d)list})`);
  term args_ready_term =
      `cm_args_wf (p:cm_program) ${function:cm_function_d}
        ((arg:cm_expr) :: (args:(cm_expr)list))
        ${params:(cm_slot_d)list}`;
  thm args_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
      get_cm_args_wf_def())), args_ready_term);
  thm args_ready = taut_rule(imp_chain(TERM_LIST(
      concl(slots_nonempty), concl(arg_wf), concl(arg_convertible),
      concl(tail_wf)), rhs_of(args_view)));
  args_ready = mp_rule(args_ready, slots_nonempty);
  args_ready = mp_rule(args_ready, arg_wf);
  args_ready = mp_rule(args_ready, arg_convertible);
  args_ready = mp_rule(args_ready, tail_wf);
  thm args_wf = eq_mp_rule(sym_rule(args_view), args_ready);
  thm arg_scalar = match_mp_rule(
      specl_rule(TERM_LIST(`arg:cm_expr`,
        `cm_slot_ty (HD ${params:(cm_slot_d)list})`),
        cm_expr_convertible_source_scalar), arg_convertible);
  thm tail_ready = match_mp_rule(specl_rule(TERM_LIST(
      `args:(cm_expr)list`, `p:cm_program`, function,
      `TL ${params:(cm_slot_d)list}`), cm_args_wf_exprs), tail_wf);
  thm progress = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_arg_progress_type_ready_def(), slots_nonempty,
        get_theorem_by_name("NOT_CONS_NIL"),
        get_theorem_by_name("HD"), get_theorem_by_name("TL"))),
      `cm_arg_progress_type_ready
        ((arg:cm_expr) :: (args:(cm_expr)list))
        ${params:(cm_slot_d)list} [] args`));
  thm parent_ready = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_expr_type_def())), parent_input);
  thm phase_static = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_phase_static_type_ready_def(), callee_low, callee_high,
        tail_ready, args_wf, progress, ret_equal,
        get_theorem_by_name("REVERSE"))),
      `cm_phase_static_type_ready (p:cm_program) (fid:int)
        ${phase:cm_aphase}`));
  thm phase_parent = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_phase_parent_type_ready_def(), parent_ready)),
      `cm_phase_parent_type_ready (p:cm_program) (fid:int)
        ${phase:cm_aphase} ${old_cursors:(cm_acursor)list}`));
  thm next_fid = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(cm_phase_next_fid_def)),
      `cm_phase_next_fid (fid:int) ${phase:cm_aphase} == fid`));
  thm phase_input = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_phase_input_type_ready_def())),
      `cm_phase_input_type_ready (p:cm_program) (fid:int)
        ${phase:cm_aphase} (cm_expr_type (arg:cm_expr))`));
  thm phase_expr = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_phase_expr_type_ready_def(), get_cm_arg_next_type_def(),
        arg_convertible, get_theorem_by_name("REVERSE"))),
      `cm_phase_expr_type_ready (p:cm_program) (fid:int)
        ${phase:cm_aphase} (arg:cm_expr)`));
  thm parent_nonzero = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_zero_literal_def(),
        get_datatype_distinctness("cm_expr"))),
      `~cm_zero_literal ${expression:cm_expr}`));
  thm phase_results = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_phase_result_type_def(), get_cm_expr_type_def())),
      `!(result_ty:cm_type).
         cm_phase_result_type (p:cm_program) (fid:int)
           ${phase:cm_aphase} result_ty ==>
         result_ty == cm_expr_type ${expression:cm_expr}`));
  thm result = specl_rule(TERM_LIST(
      `p:cm_program`, `q:cm_program`, `fid:int`, expression,
      `arg:cm_expr`, `st:cm_src_state`, `ks:(cm_frame)list`,
      `CMArgK (callee:int) (args:(cm_expr)list) [] (ty:cm_type)`,
      `ann:cm_annotation`, phase, `cm_ann_pc (ann:cm_annotation)`,
      `cm_ann_temp (ann:cm_annotation) +
        ilength ((arg:cm_expr) :: (args:(cm_expr)list))`,
      `cm_ann_break (ann:cm_annotation)`,
      `cm_ann_continue (ann:cm_annotation)`),
      cm_r_push_task_ready_at);
  thm_list premises = THM_LIST(task_ready, parent_nonzero,
      phase_results, arg_wf, arg_scalar, phase_static,
      phase_parent, next_fid, phase_input, phase_expr);
  for (size_t i = 0; i < vector_size(premises); ++i) {
    result = mp_rule(result, premises[i]);
  }
  thm target_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
      same_program, get_cm_step_def(), get_cm_rstart_def(),
      get_cm_args_start_def(), cm_annotation_step_def, cm_update_r_def,
      cm_update_annotation_def, get_theorem_by_name("NOT_CONS_NIL"),
      get_theorem_by_name("HD"), get_theorem_by_name("TL"))),
      goal_ccl(leaf->g));
  result = conv_rule(rewrite_conv(THM_LIST(same_program)), result);
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), result));
  return gnode_prove(root);
}
PROOF thm cm_r_call_cons_type_ready_step =
    cm_prove_r_call_cons_type_ready_step();

PROOF static thm cm_prove_r_call_nil_type_ready_step(void) {
  term expression =
      `CMCallE (callee:int) [] (ty:cm_type)`;
  term task =
      `CMRTask (q:cm_program) (fid:int) ${expression:cm_expr}
        (st:cm_src_state) (ks:(cm_frame)list)`;
  term old_cursors = `cm_ann_cursors (ann:cm_annotation)`;
  term callee_function =
      `inth (callee:int) (cm_program_functions (p:cm_program))`;
  term phase =
      `CACallP (fid:int) (cm_state_env (st:cm_src_state))
        (cm_state_fp st) (cm_state_regions st) (ty:cm_type)`;
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (q:cm_program) (fid:int) (callee:int)
         (ty:cm_type) (st:cm_src_state) (ks:(cm_frame)list)
         (ann:cm_annotation).
         cm_typed_program p ==>
         cm_task_succeeds
           (CMRTask q fid (CMCallE callee [] ty) st ks) ==>
         cm_annotation_erases
           (CMRTask q fid (CMCallE callee [] ty) st ks) ann ==>
         cm_task_type_ready p
           (CMRTask q fid (CMCallE callee [] ty) st ks) ann ==>
         cm_task_type_ready p
           (cm_step (CMRTask q fid (CMCallE callee [] ty) st ks))
           (cm_update_annotation
             (cm_annotation_step
               (CMRTask q fid (CMCallE callee [] ty) st ks) ann))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm typed = assume_rule(`cm_typed_program (p:cm_program)`);
  thm succeeds = assume_rule(
      `cm_task_succeeds (CMRTask (q:cm_program) (fid:int)
        ${expression:cm_expr} (st:cm_src_state) (ks:(cm_frame)list))`);
  thm erases = assume_rule(
      `cm_annotation_erases (CMRTask (q:cm_program) (fid:int)
        ${expression:cm_expr} (st:cm_src_state) (ks:(cm_frame)list))
        (ann:cm_annotation)`);
  thm task_ready = assume_rule(
      `cm_task_type_ready (p:cm_program) ${task:cm_task}
        (ann:cm_annotation)`);
  thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_task_type_ready_def())), task_ready);
  thm same_program = cm_tsrc_pick_conjunct(
      opened, `(q:cm_program) == (p:cm_program)`);
  thm fid_low = cm_tsrc_pick_conjunct(
      opened, `0i <= (fid:int)`);
  thm fid_high = cm_tsrc_pick_conjunct(opened,
      `(fid:int) < ilength
        (cm_program_functions (p:cm_program))`);
  thm expression_wf = cm_tsrc_pick_conjunct(opened,
      `cm_expr_wf (p:cm_program)
        (inth (fid:int) (cm_program_functions p))
        ${expression:cm_expr}`);
  thm cursors_ready = cm_tsrc_pick_conjunct(opened,
      `cm_cursors_type_ready (p:cm_program) (fid:int)
        ${old_cursors:(cm_acursor)list}`);
  thm parent_values = cm_tsrc_pick_conjunct(opened,
      `cm_cursor_expr_values_type_ready (p:cm_program) (fid:int)
        ${expression:cm_expr} ${old_cursors:(cm_acursor)list}`);
  thm parent_input = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_expr_type_def())), cm_tsrc_pick_conjunct(opened,
        `cm_cursor_head_input_type_ready (p:cm_program) (fid:int)
          (cm_expr_type ${expression:cm_expr})
          ${old_cursors:(cm_acursor)list}`));
  thm wf_open = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_expr_wf_def())), expression_wf);
  thm callee_low = cm_tsrc_pick_conjunct(
      wf_open, `0i <= (callee:int)`);
  thm callee_high = cm_tsrc_pick_conjunct(wf_open,
      `(callee:int) < ilength
        (cm_program_functions (p:cm_program))`);
  thm params_empty = cm_tsrc_pick_conjunct(wf_open,
      `cm_function_params ${callee_function:cm_function_d} == []`);
  thm ret_equal = cm_tsrc_pick_conjunct(wf_open,
      `(ty:cm_type) == cm_function_ret
        ${callee_function:cm_function_d}`);
  thm function_wf = mp_rule(mp_rule(mp_rule(
      specl_rule(TERM_LIST(`p:cm_program`, `callee:int`),
        cm_typed_function_at), typed), callee_low), callee_high);
  thm function_open = conv_rule(rewrite_conv(THM_LIST(
      get_cm_function_wf_def())), function_wf);
  thm body_wf_false = cm_tsrc_pick_conjunct(function_open,
      `cm_stmt_wf (p:cm_program) ${callee_function:cm_function_d}
        F (cm_function_body ${callee_function:cm_function_d})`);
  thm body_wf = mp_rule(specl_rule(TERM_LIST(
      `cm_function_body ${callee_function:cm_function_d}`,
      `p:cm_program`, callee_function, `F`),
      cm_stmt_wf_loop_mono), body_wf_false);
  thm call_ready = specl_rule(TERM_LIST(
      `q:cm_program`, `fid:int`, expression, `st:cm_src_state`,
      `ks:(cm_frame)list`), cm_rtask_succeeds_call_ready);
  call_ready = mp_rule(call_ready, succeeds);
  call_ready = specl_rule(TERM_LIST(
      `callee:int`, `ty:cm_type`), call_ready);
  call_ready = mp_rule(call_ready, refl_rule(expression));
  call_ready = conv_rule(rewrite_conv(THM_LIST(same_program)),
      call_ready);
  thm frame_equal = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_annotation_erases_def)), erases);
  thm annotation_call_ready = conv_rule(rewrite_conv(THM_LIST(
      sym_rule(frame_equal))), call_ready);
  term caller_ready_term =
      `(fid:int) == --1i ||
       (0i <= fid &&
        fid < ilength (cm_program_functions (p:cm_program)))`;
  thm caller_ready = taut_rule(imp_chain(TERM_LIST(
      concl(fid_low), concl(fid_high)), caller_ready_term));
  caller_ready = mp_rule(mp_rule(caller_ready, fid_low), fid_high);
  thm phase_static = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_phase_static_type_ready_def(), callee_low, callee_high,
        caller_ready, ret_equal)),
      `cm_phase_static_type_ready (p:cm_program) (callee:int)
        ${phase:cm_aphase}`));
  thm phase_parent = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_phase_parent_type_ready_def(), parent_input)),
      `cm_phase_parent_type_ready (p:cm_program) (callee:int)
        ${phase:cm_aphase} ${old_cursors:(cm_acursor)list}`));
  thm next_fid = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(cm_phase_next_fid_def)),
      `cm_phase_next_fid (callee:int) ${phase:cm_aphase} == fid`));
  thm next_rest_view = apply_conversion(rewrite_conv(THM_LIST(
      next_fid)),
      `cm_cursors_type_ready (p:cm_program)
        (cm_phase_next_fid (callee:int) ${phase:cm_aphase})
        ${old_cursors:(cm_acursor)list}`);
  thm next_rest = eq_mp_rule(
      sym_rule(next_rest_view), cursors_ready);
  thm parent_nonzero = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_zero_literal_def(),
        get_datatype_distinctness("cm_expr"))),
      `~cm_zero_literal ${expression:cm_expr}`));
  thm all_results = mp_rule(mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, expression, old_cursors),
      cm_cursor_expr_result_ready), parent_values), parent_nonzero);
  all_results = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_expr_type_def())), all_results);
  term result_equal_term =
      `(result_ty:cm_type) == (ty:cm_type)`;
  term compatible_term =
      `cm_value_type_compatible (v:cm_value) (result_ty:cm_type)`;
  thm compatible = conv_rule(rewrite_conv(THM_LIST(
      assume_rule(result_equal_term))), assume_rule(compatible_term));
  thm accepted = mp_rule(spec_rule(`v:cm_value`, all_results), compatible);
  thm phase_result = disch_rule(compatible_term, accepted);
  phase_result = disch_rule(result_equal_term, phase_result);
  phase_result = gen_rule(`v:cm_value`, phase_result);
  phase_result = gen_rule(`result_ty:cm_type`, phase_result);
  thm phase_result_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
      get_cm_phase_result_type_ready_def(),
      get_cm_phase_result_type_def(), cm_phase_next_fid_def)),
      `cm_phase_result_type_ready (p:cm_program) (callee:int)
        ${phase:cm_aphase} ${old_cursors:(cm_acursor)list}`);
  phase_result =
      eq_mp_rule(sym_rule(phase_result_view), phase_result);
  thm new_cursors = mp_rule(mp_rule(mp_rule(mp_rule(
      specl_rule(TERM_LIST(
        `p:cm_program`, `callee:int`, phase,
        `cm_ann_temp (ann:cm_annotation)`,
        `cm_ann_break (ann:cm_annotation)`,
        `cm_ann_continue (ann:cm_annotation)`, old_cursors),
        cm_cursor_push_type_ready), phase_static), phase_parent),
      phase_result), next_rest);
  thm target_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
      same_program, call_ready, annotation_call_ready,
      get_cm_step_def(), get_cm_rstart_def(), get_cm_args_start_def(),
      get_cm_begin_call_def(), cm_annotation_step_def, cm_update_r_def,
      cm_update_annotation_def, get_cm_task_type_ready_def(),
      cm_ann_enter_call_def, cm_ann_cursors_def, callee_low,
      callee_high, body_wf, new_cursors,
      get_theorem_by_name("REVERSE"))), goal_ccl(leaf->g));
  ACCEPT_TAC(leaf, eqt_elim_rule(target_view));
  return gnode_prove(root);
}
PROOF thm cm_r_call_nil_type_ready_step =
    cm_prove_r_call_nil_type_ready_step();

PROOF static thm cm_prove_r_call_type_ready_step(void) {
  gnode root = gnode_new_with_ccl(
      `!(args:(cm_expr)list). !(p:cm_program) (q:cm_program)
         (fid:int) (callee:int) (ty:cm_type)
         (st:cm_src_state) (ks:(cm_frame)list)
         (ann:cm_annotation).
         cm_typed_program p ==>
         cm_task_succeeds
           (CMRTask q fid (CMCallE callee args ty) st ks) ==>
         cm_annotation_erases
           (CMRTask q fid (CMCallE callee args ty) st ks) ann ==>
         cm_task_type_ready p
           (CMRTask q fid (CMCallE callee args ty) st ks) ann ==>
         cm_task_type_ready p
           (cm_step (CMRTask q fid (CMCallE callee args ty) st ks))
           (cm_update_annotation
             (cm_annotation_step
               (CMRTask q fid (CMCallE callee args ty) st ks) ann))`);
  gnode_list cases = INDUCT_TAC(root, `args:(cm_expr)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm result = specl_rule(TERM_LIST(
        `p:cm_program`, `q:cm_program`, `fid:int`, `callee:int`,
        `ty:cm_type`, `st:cm_src_state`, `ks:(cm_frame)list`,
        `ann:cm_annotation`), cm_r_call_nil_type_ready_step);
    term_list premises = TERM_LIST(
        `cm_typed_program (p:cm_program)`,
        `cm_task_succeeds
          (CMRTask (q:cm_program) (fid:int)
            (CMCallE (callee:int) [] (ty:cm_type))
            (st:cm_src_state) (ks:(cm_frame)list))`,
        `cm_annotation_erases
          (CMRTask (q:cm_program) (fid:int)
            (CMCallE (callee:int) [] (ty:cm_type))
            (st:cm_src_state) (ks:(cm_frame)list))
          (ann:cm_annotation)`,
        `cm_task_type_ready (p:cm_program)
          (CMRTask (q:cm_program) (fid:int)
            (CMCallE (callee:int) [] (ty:cm_type))
            (st:cm_src_state) (ks:(cm_frame)list))
          (ann:cm_annotation)`);
    for (size_t i = 0; i < vector_size(premises); ++i) {
      result = mp_rule(result, assume_rule(premises[i]));
    }
    ACCEPT_TAC(leaf, result);
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm result = specl_rule(TERM_LIST(
        `p:cm_program`, `q:cm_program`, `fid:int`, `callee:int`,
        `a0:cm_expr`, `a1:(cm_expr)list`, `ty:cm_type`,
        `st:cm_src_state`, `ks:(cm_frame)list`,
        `ann:cm_annotation`), cm_r_call_cons_type_ready_step);
    term_list premises = TERM_LIST(
        `cm_typed_program (p:cm_program)`,
        `cm_task_succeeds
          (CMRTask (q:cm_program) (fid:int)
            (CMCallE (callee:int)
              ((a0:cm_expr) :: (a1:(cm_expr)list)) (ty:cm_type))
            (st:cm_src_state) (ks:(cm_frame)list))`,
        `cm_annotation_erases
          (CMRTask (q:cm_program) (fid:int)
            (CMCallE (callee:int)
              ((a0:cm_expr) :: (a1:(cm_expr)list)) (ty:cm_type))
            (st:cm_src_state) (ks:(cm_frame)list))
          (ann:cm_annotation)`,
        `cm_task_type_ready (p:cm_program)
          (CMRTask (q:cm_program) (fid:int)
            (CMCallE (callee:int)
              ((a0:cm_expr) :: (a1:(cm_expr)list)) (ty:cm_type))
            (st:cm_src_state) (ks:(cm_frame)list))
          (ann:cm_annotation)`);
    for (size_t i = 0; i < vector_size(premises); ++i) {
      result = mp_rule(result, assume_rule(premises[i]));
    }
    ACCEPT_TAC(leaf, result);
  }
  return gnode_prove(root);
}
PROOF thm cm_r_call_type_ready_step =
    cm_prove_r_call_type_ready_step();

PROOF static int cmc_preservation_type_source_r_call_final_checks(void) {
  ENSURE_COND(vector_size(hyp(cm_r_call_cons_type_ready_step)) == 0 &&
      vector_size(hyp(cm_r_call_nil_type_ready_step)) == 0 &&
      vector_size(hyp(cm_r_call_type_ready_step)) == 0,
      "call rvalue type theorem has assumptions");
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_type_source_r_call_axioms_before,
      "cmc_preservation_type_source_r_call introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_type_source_r_call_checks =
    cmc_preservation_type_source_r_call_final_checks();
