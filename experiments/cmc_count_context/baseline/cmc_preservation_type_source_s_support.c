#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_type_source_s_support.h"
#include "cmc_preservation_ready_coordinate.h"

#require "cmc_preservation_type_source_r_total.c"

PROOF static size_t _cmc_preservation_type_source_s_support_axioms_before =
    vector_size(get_all_axioms());

PROOF static bool cm_tsss_has_conjunct(term whole, term wanted) {
  if (alpha_compare(whole, wanted) == 0) return true;
  if (!is_conj(whole)) return false;
  struct dest_conj_results parts = dest_conj(whole);
  return cm_tsss_has_conjunct(parts.tm1, wanted) ||
      cm_tsss_has_conjunct(parts.tm2, wanted);
}

PROOF static thm cm_tsss_pick_conjunct(thm fact, term wanted) {
  if (alpha_compare(concl(fact), wanted) == 0) return fact;
  struct dest_conj_results parts = dest_conj(concl(fact));
  return cm_tsss_has_conjunct(parts.tm1, wanted)
      ? cm_tsss_pick_conjunct(conjunct1_rule(fact), wanted)
      : cm_tsss_pick_conjunct(conjunct2_rule(fact), wanted);
}

PROOF static thm cm_prove_s_r_push_task_ready(void) {
  term old_cursors = `cm_ann_cursors (ann:cm_annotation)`;
  term child_type = `cm_expr_type (child:cm_expr)`;
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (q:cm_program) (fid:int)
         (parent:cm_stmt) (child:cm_expr)
         (old_st:cm_src_state) (next_st:cm_src_state)
         (ks:(cm_frame)list) (frame:cm_frame)
         (ann:cm_annotation) (phase:cm_aphase)
         (pc:int) (temp:int) (breakpc:int) (continuepc:int).
         cm_task_type_ready p (CMSTask q fid parent old_st ks) ann ==>
         cm_expr_wf p (inth fid (cm_program_functions p)) child ==>
         cm_scalar_expr_type (cm_expr_type child) ==>
         cm_phase_static_type_ready p fid phase ==>
         cm_phase_parent_type_ready p fid phase
           (cm_ann_cursors ann) ==>
         cm_phase_result_type_ready p fid phase
           (cm_ann_cursors ann) ==>
         cm_phase_next_fid fid phase == fid ==>
         cm_phase_input_type_ready p fid phase
           (cm_expr_type child) ==>
         cm_phase_expr_type_ready p fid phase child ==>
         cm_task_type_ready p
           (CMRTask q fid child next_st (frame :: ks))
           (cm_ann_push phase pc temp breakpc continuepc ann)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm parent_ready = assume_rule(
      `cm_task_type_ready (p:cm_program)
        (CMSTask (q:cm_program) (fid:int) (parent:cm_stmt)
          (old_st:cm_src_state) (ks:(cm_frame)list))
        (ann:cm_annotation)`);
  thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_task_type_ready_def())), parent_ready);
  thm same_program = cm_tsss_pick_conjunct(
      opened, `(q:cm_program) == (p:cm_program)`);
  thm fid_low = cm_tsss_pick_conjunct(opened, `0i <= (fid:int)`);
  thm fid_high = cm_tsss_pick_conjunct(opened,
      `(fid:int) < ilength (cm_program_functions (p:cm_program))`);
  thm cursors_ready = cm_tsss_pick_conjunct(opened,
      `cm_cursors_type_ready (p:cm_program) (fid:int)
        ${old_cursors:(cm_acursor)list}`);
  thm next_fid = assume_rule(
      `cm_phase_next_fid (fid:int) (phase:cm_aphase) == fid`);
  thm next_rest_view = apply_conversion(rewrite_conv(THM_LIST(
      next_fid)),
      `cm_cursors_type_ready (p:cm_program)
        (cm_phase_next_fid (fid:int) (phase:cm_aphase))
        ${old_cursors:(cm_acursor)list}`);
  thm next_rest = eq_mp_rule(sym_rule(next_rest_view), cursors_ready);
  thm new_cursors = mp_rule(mp_rule(mp_rule(mp_rule(
      specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `phase:cm_aphase`,
        `cm_ann_temp (ann:cm_annotation)`, `cm_ann_break ann`,
        `cm_ann_continue ann`, old_cursors), cm_cursor_push_type_ready),
      assume_rule(`cm_phase_static_type_ready (p:cm_program)
        (fid:int) (phase:cm_aphase)`)),
      assume_rule(`cm_phase_parent_type_ready (p:cm_program)
        (fid:int) (phase:cm_aphase)
        ${old_cursors:(cm_acursor)list}`)),
      assume_rule(`cm_phase_result_type_ready (p:cm_program)
        (fid:int) (phase:cm_aphase)
        ${old_cursors:(cm_acursor)list}`)), next_rest);
  thm new_input = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `phase:cm_aphase`, child_type,
      `cm_ann_temp (ann:cm_annotation)`, `cm_ann_break ann`,
      `cm_ann_continue ann`, old_cursors), cm_cursor_push_input_ready),
      assume_rule(`cm_phase_input_type_ready (p:cm_program)
        (fid:int) (phase:cm_aphase) ${child_type:cm_type}`));
  thm new_values = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `phase:cm_aphase`,
      `child:cm_expr`, `cm_ann_temp (ann:cm_annotation)`,
      `cm_ann_break ann`, `cm_ann_continue ann`, old_cursors),
      cm_cursor_push_expr_values_ready), assume_rule(
        `cm_phase_expr_type_ready (p:cm_program) (fid:int)
          (phase:cm_aphase) (child:cm_expr)`));
  thm target_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
      same_program, fid_low, fid_high,
      assume_rule(`cm_expr_wf (p:cm_program)
        (inth (fid:int) (cm_program_functions p)) (child:cm_expr)`),
      assume_rule(`cm_scalar_expr_type
        (cm_expr_type (child:cm_expr))`),
      new_cursors, new_input, new_values,
      get_cm_task_type_ready_def(), cm_ann_push_def,
      cm_ann_cursors_def)), goal_ccl(leaf->g));
  ACCEPT_TAC(leaf, eqt_elim_rule(target_view));
  return gnode_prove(root);
}
PROOF thm cm_s_r_push_task_ready = cm_prove_s_r_push_task_ready();

PROOF static thm cm_prove_s_s_push_task_ready(void) {
  term old_cursors = `cm_ann_cursors (ann:cm_annotation)`;
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (q:cm_program) (fid:int)
         (parent:cm_stmt) (child:cm_stmt)
         (old_st:cm_src_state) (next_st:cm_src_state)
         (ks:(cm_frame)list) (frame:cm_frame)
         (ann:cm_annotation) (phase:cm_aphase)
         (pc:int) (temp:int) (breakpc:int) (continuepc:int).
         cm_task_type_ready p (CMSTask q fid parent old_st ks) ann ==>
         cm_stmt_wf p (inth fid (cm_program_functions p)) T child ==>
         cm_phase_static_type_ready p fid phase ==>
         cm_phase_parent_type_ready p fid phase
           (cm_ann_cursors ann) ==>
         cm_phase_result_type_ready p fid phase
           (cm_ann_cursors ann) ==>
         cm_phase_next_fid fid phase == fid ==>
         cm_task_type_ready p
           (CMSTask q fid child next_st (frame :: ks))
           (cm_ann_push phase pc temp breakpc continuepc ann)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm parent_ready = assume_rule(
      `cm_task_type_ready (p:cm_program)
        (CMSTask (q:cm_program) (fid:int) (parent:cm_stmt)
          (old_st:cm_src_state) (ks:(cm_frame)list))
        (ann:cm_annotation)`);
  thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_task_type_ready_def())), parent_ready);
  thm same_program = cm_tsss_pick_conjunct(
      opened, `(q:cm_program) == (p:cm_program)`);
  thm fid_low = cm_tsss_pick_conjunct(opened, `0i <= (fid:int)`);
  thm fid_high = cm_tsss_pick_conjunct(opened,
      `(fid:int) < ilength (cm_program_functions (p:cm_program))`);
  thm cursors_ready = cm_tsss_pick_conjunct(opened,
      `cm_cursors_type_ready (p:cm_program) (fid:int)
        ${old_cursors:(cm_acursor)list}`);
  thm next_fid = assume_rule(
      `cm_phase_next_fid (fid:int) (phase:cm_aphase) == fid`);
  thm next_rest_view = apply_conversion(rewrite_conv(THM_LIST(
      next_fid)),
      `cm_cursors_type_ready (p:cm_program)
        (cm_phase_next_fid (fid:int) (phase:cm_aphase))
        ${old_cursors:(cm_acursor)list}`);
  thm next_rest = eq_mp_rule(sym_rule(next_rest_view), cursors_ready);
  thm new_cursors = mp_rule(mp_rule(mp_rule(mp_rule(
      specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `phase:cm_aphase`,
        `cm_ann_temp (ann:cm_annotation)`, `cm_ann_break ann`,
        `cm_ann_continue ann`, old_cursors), cm_cursor_push_type_ready),
      assume_rule(`cm_phase_static_type_ready (p:cm_program)
        (fid:int) (phase:cm_aphase)`)),
      assume_rule(`cm_phase_parent_type_ready (p:cm_program)
        (fid:int) (phase:cm_aphase)
        ${old_cursors:(cm_acursor)list}`)),
      assume_rule(`cm_phase_result_type_ready (p:cm_program)
        (fid:int) (phase:cm_aphase)
        ${old_cursors:(cm_acursor)list}`)), next_rest);
  thm target_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
      same_program, fid_low, fid_high,
      assume_rule(`cm_stmt_wf (p:cm_program)
        (inth (fid:int) (cm_program_functions p)) T
        (child:cm_stmt)`), new_cursors,
      get_cm_task_type_ready_def(), cm_ann_push_def,
      cm_ann_cursors_def)), goal_ccl(leaf->g));
  ACCEPT_TAC(leaf, eqt_elim_rule(target_view));
  return gnode_prove(root);
}
PROOF thm cm_s_s_push_task_ready = cm_prove_s_s_push_task_ready();

PROOF static thm cm_prove_s_control_task_ready(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (q:cm_program) (fid:int)
         (parent:cm_stmt) (control:cm_control)
         (old_st:cm_src_state) (next_st:cm_src_state)
         (ks:(cm_frame)list) (ann:cm_annotation)
         (next_ann:cm_annotation).
         cm_task_type_ready p (CMSTask q fid parent old_st ks) ann ==>
         cm_control_type_ready p fid control ==>
         cm_ann_cursors next_ann == cm_ann_cursors ann ==>
         cm_task_type_ready p
           (CMCTask q fid control next_st ks) next_ann`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_task_type_ready_def())), assume_rule(
        `cm_task_type_ready (p:cm_program)
          (CMSTask (q:cm_program) (fid:int) (parent:cm_stmt)
            (old_st:cm_src_state) (ks:(cm_frame)list))
          (ann:cm_annotation)`));
  thm same_program = cm_tsss_pick_conjunct(
      opened, `(q:cm_program) == (p:cm_program)`);
  thm cursors_ready = cm_tsss_pick_conjunct(opened,
      `cm_cursors_type_ready (p:cm_program) (fid:int)
        (cm_ann_cursors (ann:cm_annotation))`);
  thm cursor_equal = assume_rule(
      `cm_ann_cursors (next_ann:cm_annotation) ==
       cm_ann_cursors (ann:cm_annotation)`);
  thm next_cursors = conv_rule(rewrite_conv(THM_LIST(
      sym_rule(cursor_equal))), cursors_ready);
  thm target_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
      same_program, assume_rule(
        `cm_control_type_ready (p:cm_program) (fid:int)
          (control:cm_control)`), next_cursors,
      get_cm_task_type_ready_def())), goal_ccl(leaf->g));
  ACCEPT_TAC(leaf, eqt_elim_rule(target_view));
  return gnode_prove(root);
}
PROOF thm cm_s_control_task_ready =
    cm_prove_s_control_task_ready();

PROOF static thm cm_prove_condition_type_scalar(void) {
  gnode root = gnode_new_with_ccl(
      `!(ty:cm_type).
         (ty == CMIntTy || ty == CMCharTy || cm_is_pointer ty) ==>
         cm_scalar_expr_type ty`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm condition = assume_rule(
      `(ty:cm_type) == CMIntTy || ty == CMCharTy || cm_is_pointer ty`);
  gnode_list cases = DISJ_CASES_TAC(leaf, condition, "Hcondition");
  thm int_case = assume_rule(goal_lasmps(cases[0]->g)[
      labeled_term_list_index(goal_lasmps(cases[0]->g),
        "Hcondition")].tm);
  ACCEPT_TAC(cases[0], conv_rule(rewrite_conv(THM_LIST(
      sym_rule(int_case))), mp_rule(spec_rule(`CMIntTy`, cm_integer_expr_type),
        eqt_elim_rule(apply_conversion(reduce_rewrite_conv(THM_LIST(
          get_cm_integer_type_def())), `cm_integer_type CMIntTy`)))));
  thm char_case = assume_rule(goal_lasmps(cases[1]->g)[
      labeled_term_list_index(goal_lasmps(cases[1]->g),
        "Hcondition")].tm);
  ACCEPT_TAC(cases[1], conv_rule(rewrite_conv(THM_LIST(
      sym_rule(char_case))), mp_rule(spec_rule(`CMCharTy`, cm_integer_expr_type),
        eqt_elim_rule(apply_conversion(reduce_rewrite_conv(THM_LIST(
          get_cm_integer_type_def())), `cm_integer_type CMCharTy`)))));
  ACCEPT_TAC(cases[2], mp_rule(spec_rule(
      `ty:cm_type`, cm_pointer_expr_type), assume_rule(
        `cm_is_pointer (ty:cm_type)`)));
  return gnode_prove(root);
}
PROOF thm cm_condition_type_scalar =
    cm_prove_condition_type_scalar();

PROOF static thm cm_prove_local_slot_scalar_type(void) {
  term function =
      `inth (fid:int) (cm_program_functions (p:cm_program))`;
  term slot_value =
      `inth (slot:int) (cm_function_locals ${function:cm_function_d})`;
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (slot:int).
         cm_typed_program p ==>
         0i <= fid ==>
         fid < ilength (cm_program_functions p) ==>
         0i <= slot ==>
         slot < ilength
          (cm_function_locals
            (inth fid (cm_program_functions p))) ==>
         cm_scalar_type (cm_program_structs p)
           (cm_slot_ty
             (inth slot
               (cm_function_locals
                 (inth fid (cm_program_functions p)))))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm function_wf = mp_rule(mp_rule(mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`), cm_typed_function_at),
      assume_rule(`cm_typed_program (p:cm_program)`)),
      assume_rule(`0i <= (fid:int)`)), assume_rule(
        `(fid:int) < ilength
          (cm_program_functions (p:cm_program))`));
  thm function_open = conv_rule(rewrite_conv(THM_LIST(
      get_cm_function_wf_def())), function_wf);
  thm slots_wf = cm_tsss_pick_conjunct(function_open,
      `cm_slots_wf (cm_program_structs (p:cm_program))
        (cm_function_locals ${function:cm_function_d})`);
  thm slots_open = conv_rule(rewrite_conv(THM_LIST(
      get_cm_slots_wf_def())), slots_wf);
  thm slot_wf = spec_rule(`slot:int`, slots_open);
  slot_wf = mp_rule(slot_wf, assume_rule(`0i <= (slot:int)`));
  slot_wf = mp_rule(slot_wf, assume_rule(
      `(slot:int) < ilength
        (cm_function_locals ${function:cm_function_d})`));
  thm slot_open = conv_rule(rewrite_conv(THM_LIST(
      get_cm_slot_wf_def())), slot_wf);
  ACCEPT_TAC(leaf, cm_tsss_pick_conjunct(slot_open,
      `cm_scalar_type (cm_program_structs (p:cm_program))
        (cm_slot_ty ${slot_value:cm_slot_d})`));
  return gnode_prove(root);
}
PROOF thm cm_local_slot_scalar_type =
    cm_prove_local_slot_scalar_type();

PROOF static int cmc_preservation_type_source_s_support_final_checks(void) {
  ENSURE_COND(vector_size(hyp(cm_s_r_push_task_ready)) == 0 &&
      vector_size(hyp(cm_s_s_push_task_ready)) == 0 &&
      vector_size(hyp(cm_s_control_task_ready)) == 0 &&
      vector_size(hyp(cm_condition_type_scalar)) == 0 &&
      vector_size(hyp(cm_local_slot_scalar_type)) == 0,
      "statement type support theorem has assumptions");
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_type_source_s_support_axioms_before,
      "cmc_preservation_type_source_s_support introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_type_source_s_support_checks =
    cmc_preservation_type_source_s_support_final_checks();
