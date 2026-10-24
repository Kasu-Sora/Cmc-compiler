#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_type_source_c_support.h"

#pragma clang diagnostic ignored "-Wunused-function"

#require "cmc_preservation_type_source_v_total.c"

PROOF static size_t _cmc_preservation_type_source_c_support_axioms_before =
    vector_size(get_all_axioms());

PROOF thm cm_c_phase_family_def = new_rec_definition(
    get_cm_aphase_recursion(),
    `cm_c_phase_family CAHaltP = 4i &&
     (!ty. cm_c_phase_family (CALoadP (ty:cm_type)) = 0i) &&
     (!src ty. cm_c_phase_family
        (CAAssignLP (src:cm_expr) (ty:cm_type)) = 0i) &&
     (!ptr ty. cm_c_phase_family
        (CAAssignRP (ptr:cm_value) (ty:cm_type)) = 0i) &&
     (!op left right ty. cm_c_phase_family
        (CABinLP (op:int) (left:cm_expr) (right:cm_expr)
          (ty:cm_type)) = 0i) &&
     (!op left right saved ty. cm_c_phase_family
        (CABinRP (op:int) (left:cm_expr) (right:cm_expr)
          (saved:cm_value) (ty:cm_type)) = 0i) &&
     (!op. cm_c_phase_family (CAUnaryP (op:int)) = 0i) &&
     (!index ty. cm_c_phase_family
        (CAIndexLP (index:cm_expr) (ty:cm_type)) = 0i) &&
     (!base ty. cm_c_phase_family
        (CAIndexRP (base:cm_value) (ty:cm_type)) = 0i) &&
     (!mid base_ty. cm_c_phase_family
        (CAMemberP (mid:int) (base_ty:cm_type)) = 0i) &&
     cm_c_phase_family CAPutcP = 0i &&
     cm_c_phase_family CAPutiP = 0i &&
     cm_c_phase_family CAExitP = 0i &&
     cm_c_phase_family CAExprStmtP = 0i &&
     (!slot. cm_c_phase_family (CAInitP (slot:int)) = 0i) &&
     (!env regions jump target. cm_c_phase_family
        (CABlockP (env:int->int->cm_value) (regions:(cm_region)list)
          (jump:bool) (target:int)) = 0i) &&
     (!second. cm_c_phase_family
        (CASeqP (second:cm_stmt)) = 1i) &&
     (!yes no. cm_c_phase_family
        (CAIfP (yes:cm_stmt) (no:cm_stmt)) = 0i) &&
     (!guard body loop_start loop_end. cm_c_phase_family
        (CAWhileGuardP (guard:cm_expr) (body:cm_stmt)
          (loop_start:int) (loop_end:int)) = 0i) &&
     (!guard body env regions loop_start loop_end. cm_c_phase_family
        (CAWhileBodyP (guard:cm_expr) (body:cm_stmt)
          (env:int->int->cm_value) (regions:(cm_region)list)
          (loop_start:int) (loop_end:int)) = 2i) &&
     cm_c_phase_family CAReturnP = 0i &&
     (!callee rest values ret all_args base_slot current_slot scratch.
        cm_c_phase_family
          (CAArgP (callee:int) (rest:(cm_expr)list)
            (values:(cm_value)list) (ret:cm_type)
            (all_args:(cm_expr)list) (base_slot:int)
            (current_slot:int) (scratch:int)) = 0i) &&
     (!caller env fp regions ret. cm_c_phase_family
        (CACallP (caller:int) (env:int->int->cm_value) (fp:int)
          (regions:(cm_region)list) (ret:cm_type)) = 3i)`);
PROOF thm get_cm_c_phase_family_def(void) {
  return cm_c_phase_family_def;
}

PROOF static thm cm_tc_pick_conjunct(thm fact, term wanted) {
  if (alpha_compare(concl(fact), wanted) == 0) return fact;
  if (!is_conj(concl(fact))) return empty_theorem;
  thm left = cm_tc_pick_conjunct(conjunct1_rule(fact), wanted);
  if (!IS_NULL(left)) return left;
  return cm_tc_pick_conjunct(conjunct2_rule(fact), wanted);
}

PROOF static thm cm_prove_c_cursor_type_components(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (q:cm_program) (fid:int) (control:cm_control)
         (st:cm_src_state) (ks:(cm_frame)list) (phase:cm_aphase)
         (pc:int) (temp:int) (breakpc:int) (continuepc:int)
         (parent_temp:int) (parent_break:int) (parent_continue:int)
         (rest:(cm_acursor)list) (spills:(cm_spill)list)
         (saved:(cm_spill_frame)list) (calls:(cm_call_sim_frame)list).
         cm_task_type_ready p
           (CMCTask q fid control st ks)
           (CMAnnotation pc temp breakpc continuepc
             (CMACursor phase parent_temp parent_break parent_continue :: rest)
             spills saved calls) ==>
         q == p &&
         cm_control_type_ready p fid control &&
         cm_phase_static_type_ready p fid phase &&
         cm_phase_parent_type_ready p fid phase rest &&
         cm_phase_result_type_ready p fid phase rest &&
         cm_cursors_type_ready p (cm_phase_next_fid fid phase) rest`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm ready = assume_rule(
      `cm_task_type_ready (p:cm_program)
        (CMCTask (q:cm_program) (fid:int) (control:cm_control)
          (st:cm_src_state) (ks:(cm_frame)list))
        (CMAnnotation (pc:int) (temp:int) (breakpc:int) (continuepc:int)
          (CMACursor (phase:cm_aphase) (parent_temp:int)
            (parent_break:int) (parent_continue:int) ::
            (rest:(cm_acursor)list))
          (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
          (calls:(cm_call_sim_frame)list))`);
  thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_task_type_ready_def(), cm_ann_cursors_def,
      get_cm_cursors_type_ready_def(), cm_cursor_phase_def)), ready);
  thm target_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
      opened)), goal_ccl(leaf->g));
  ACCEPT_TAC(leaf, eqt_elim_rule(target_view));
  return gnode_prove(root);
}
PROOF thm cm_c_cursor_type_components =
    cm_prove_c_cursor_type_components();

PROOF static thm cm_prove_c_pop_control_task_ready(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (q:cm_program) (fid:int)
         (control:cm_control) (next_control:cm_control)
         (st:cm_src_state) (next_st:cm_src_state)
         (old_ks:(cm_frame)list) (next_ks:(cm_frame)list)
         (phase:cm_aphase)
         (pc:int) (temp:int) (breakpc:int) (continuepc:int)
         (parent_temp:int) (parent_break:int) (parent_continue:int)
         (rest:(cm_acursor)list) (spills:(cm_spill)list)
         (saved:(cm_spill_frame)list) (calls:(cm_call_sim_frame)list)
         (next_ann:cm_annotation).
         cm_task_type_ready p
           (CMCTask q fid control st old_ks)
           (CMAnnotation pc temp breakpc continuepc
             (CMACursor phase parent_temp parent_break parent_continue :: rest)
             spills saved calls) ==>
         cm_control_type_ready p
           (cm_phase_next_fid fid phase) next_control ==>
         cm_ann_cursors next_ann == rest ==>
         cm_task_type_ready p
           (CMCTask q (cm_phase_next_fid fid phase)
             next_control next_st next_ks) next_ann`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm components = specl_rule(TERM_LIST(
      `p:cm_program`, `q:cm_program`, `fid:int`, `control:cm_control`,
      `st:cm_src_state`, `old_ks:(cm_frame)list`, `phase:cm_aphase`,
      `pc:int`, `temp:int`, `breakpc:int`, `continuepc:int`,
      `parent_temp:int`, `parent_break:int`, `parent_continue:int`,
      `rest:(cm_acursor)list`, `spills:(cm_spill)list`,
      `saved:(cm_spill_frame)list`, `calls:(cm_call_sim_frame)list`),
      cm_c_cursor_type_components);
  components = mp_rule(components, assume_rule(
      `cm_task_type_ready (p:cm_program)
        (CMCTask (q:cm_program) (fid:int) (control:cm_control)
          (st:cm_src_state) (old_ks:(cm_frame)list))
        (CMAnnotation (pc:int) (temp:int) (breakpc:int) (continuepc:int)
          (CMACursor (phase:cm_aphase) (parent_temp:int)
            (parent_break:int) (parent_continue:int) ::
            (rest:(cm_acursor)list))
          (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
          (calls:(cm_call_sim_frame)list))`));
  thm same_program = cm_tc_pick_conjunct(components,
      `(q:cm_program) == (p:cm_program)`);
  thm rest_ready = cm_tc_pick_conjunct(components,
      `cm_cursors_type_ready (p:cm_program)
        (cm_phase_next_fid (fid:int) (phase:cm_aphase))
        (rest:(cm_acursor)list)`);
  thm cursor_equal = assume_rule(
      `cm_ann_cursors (next_ann:cm_annotation) ==
        (rest:(cm_acursor)list)`);
  thm next_cursors = conv_rule(rewrite_conv(THM_LIST(
      sym_rule(cursor_equal))), rest_ready);
  thm target_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
      get_cm_task_type_ready_def(), same_program,
      assume_rule(
        `cm_control_type_ready (p:cm_program)
          (cm_phase_next_fid (fid:int) (phase:cm_aphase))
          (next_control:cm_control)`), next_cursors)), goal_ccl(leaf->g));
  ACCEPT_TAC(leaf, eqt_elim_rule(target_view));
  return gnode_prove(root);
}
PROOF thm cm_c_pop_control_task_ready =
    cm_prove_c_pop_control_task_ready();

PROOF static thm cm_prove_c_pop_value_task_ready(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (q:cm_program) (fid:int) (control:cm_control)
         (result:cm_value) (result_ty:cm_type)
         (st:cm_src_state) (next_st:cm_src_state)
         (old_ks:(cm_frame)list) (next_ks:(cm_frame)list)
         (phase:cm_aphase)
         (pc:int) (temp:int) (breakpc:int) (continuepc:int)
         (parent_temp:int) (parent_break:int) (parent_continue:int)
         (rest:(cm_acursor)list) (spills:(cm_spill)list)
         (saved:(cm_spill_frame)list) (calls:(cm_call_sim_frame)list)
         (next_ann:cm_annotation).
         cm_task_type_ready p
           (CMCTask q fid control st old_ks)
           (CMAnnotation pc temp breakpc continuepc
             (CMACursor phase parent_temp parent_break parent_continue :: rest)
             spills saved calls) ==>
         cm_phase_result_type p fid phase result_ty ==>
         cm_value_type_compatible result result_ty ==>
         cm_ann_cursors next_ann == rest ==>
         cm_task_type_ready p
           (CMVTask q (cm_phase_next_fid fid phase)
             result next_st next_ks) next_ann`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm components = specl_rule(TERM_LIST(
      `p:cm_program`, `q:cm_program`, `fid:int`, `control:cm_control`,
      `st:cm_src_state`, `old_ks:(cm_frame)list`, `phase:cm_aphase`,
      `pc:int`, `temp:int`, `breakpc:int`, `continuepc:int`,
      `parent_temp:int`, `parent_break:int`, `parent_continue:int`,
      `rest:(cm_acursor)list`, `spills:(cm_spill)list`,
      `saved:(cm_spill_frame)list`, `calls:(cm_call_sim_frame)list`),
      cm_c_cursor_type_components);
  components = mp_rule(components, assume_rule(
      `cm_task_type_ready (p:cm_program)
        (CMCTask (q:cm_program) (fid:int) (control:cm_control)
          (st:cm_src_state) (old_ks:(cm_frame)list))
        (CMAnnotation (pc:int) (temp:int) (breakpc:int) (continuepc:int)
          (CMACursor (phase:cm_aphase) (parent_temp:int)
            (parent_break:int) (parent_continue:int) ::
            (rest:(cm_acursor)list))
          (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
          (calls:(cm_call_sim_frame)list))`));
  thm same_program = cm_tc_pick_conjunct(components,
      `(q:cm_program) == (p:cm_program)`);
  thm rest_ready = cm_tc_pick_conjunct(components,
      `cm_cursors_type_ready (p:cm_program)
        (cm_phase_next_fid (fid:int) (phase:cm_aphase))
        (rest:(cm_acursor)list)`);
  thm result_flow = cm_tc_pick_conjunct(components,
      `cm_phase_result_type_ready (p:cm_program) (fid:int)
        (phase:cm_aphase) (rest:(cm_acursor)list)`);
  result_flow = conv_rule(rewrite_conv(THM_LIST(
      get_cm_phase_result_type_ready_def())), result_flow);
  thm head_ready = mp_rule(mp_rule(specl_rule(TERM_LIST(
      `result_ty:cm_type`, `result:cm_value`), result_flow),
      assume_rule(
        `cm_phase_result_type (p:cm_program) (fid:int)
          (phase:cm_aphase) (result_ty:cm_type)`)),
      assume_rule(
        `cm_value_type_compatible (result:cm_value)
          (result_ty:cm_type)`));
  thm cursor_equal = assume_rule(
      `cm_ann_cursors (next_ann:cm_annotation) ==
        (rest:(cm_acursor)list)`);
  thm next_cursors = conv_rule(rewrite_conv(THM_LIST(
      sym_rule(cursor_equal))), rest_ready);
  thm next_head = conv_rule(rewrite_conv(THM_LIST(
      sym_rule(cursor_equal))), head_ready);
  thm target_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
      get_cm_task_type_ready_def(), same_program,
      next_cursors, next_head)), goal_ccl(leaf->g));
  ACCEPT_TAC(leaf, eqt_elim_rule(target_view));
  return gnode_prove(root);
}
PROOF thm cm_c_pop_value_task_ready =
    cm_prove_c_pop_value_task_ready();

PROOF static thm cm_prove_c_replace_r_task_ready(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (q:cm_program) (fid:int) (control:cm_control)
         (st:cm_src_state) (next_st:cm_src_state)
         (old_ks:(cm_frame)list) (next_ks:(cm_frame)list)
         (old_phase:cm_aphase) (new_phase:cm_aphase) (child:cm_expr)
         (pc:int) (temp:int) (breakpc:int) (continuepc:int)
         (parent_temp:int) (parent_break:int) (parent_continue:int)
         (rest:(cm_acursor)list) (spills:(cm_spill)list)
         (saved:(cm_spill_frame)list) (calls:(cm_call_sim_frame)list)
         (next_ann:cm_annotation).
         cm_task_type_ready p
           (CMCTask q fid control st old_ks)
           (CMAnnotation pc temp breakpc continuepc
             (CMACursor old_phase parent_temp parent_break parent_continue :: rest)
             spills saved calls) ==>
         0i <= fid ==>
         fid < ilength (cm_program_functions p) ==>
         cm_phase_next_fid fid old_phase == fid ==>
         cm_expr_wf p (inth fid (cm_program_functions p)) child ==>
         cm_scalar_expr_type (cm_expr_type child) ==>
         cm_phase_static_type_ready p fid new_phase ==>
         cm_phase_parent_type_ready p fid new_phase rest ==>
         cm_phase_result_type_ready p fid new_phase rest ==>
         cm_phase_next_fid fid new_phase == fid ==>
         cm_phase_input_type_ready p fid new_phase (cm_expr_type child) ==>
         cm_phase_expr_type_ready p fid new_phase child ==>
         cm_ann_cursors next_ann ==
           CMACursor new_phase parent_temp parent_break parent_continue ::
             rest ==>
         cm_task_type_ready p
           (CMRTask q fid child next_st next_ks) next_ann`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm components = specl_rule(TERM_LIST(
      `p:cm_program`, `q:cm_program`, `fid:int`, `control:cm_control`,
      `st:cm_src_state`, `old_ks:(cm_frame)list`, `old_phase:cm_aphase`,
      `pc:int`, `temp:int`, `breakpc:int`, `continuepc:int`,
      `parent_temp:int`, `parent_break:int`, `parent_continue:int`,
      `rest:(cm_acursor)list`, `spills:(cm_spill)list`,
      `saved:(cm_spill_frame)list`, `calls:(cm_call_sim_frame)list`),
      cm_c_cursor_type_components);
  components = mp_rule(components, assume_rule(
      `cm_task_type_ready (p:cm_program)
        (CMCTask (q:cm_program) (fid:int) (control:cm_control)
          (st:cm_src_state) (old_ks:(cm_frame)list))
        (CMAnnotation (pc:int) (temp:int) (breakpc:int) (continuepc:int)
          (CMACursor (old_phase:cm_aphase) (parent_temp:int)
            (parent_break:int) (parent_continue:int) ::
            (rest:(cm_acursor)list))
          (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
          (calls:(cm_call_sim_frame)list))`));
  thm same_program = cm_tc_pick_conjunct(components,
      `(q:cm_program) == (p:cm_program)`);
  thm old_rest = cm_tc_pick_conjunct(components,
      `cm_cursors_type_ready (p:cm_program)
        (cm_phase_next_fid (fid:int) (old_phase:cm_aphase))
        (rest:(cm_acursor)list)`);
  thm old_next = assume_rule(
      `cm_phase_next_fid (fid:int) (old_phase:cm_aphase) == fid`);
  thm rest_ready = conv_rule(rewrite_conv(THM_LIST(old_next)), old_rest);
  thm new_next = assume_rule(
      `cm_phase_next_fid (fid:int) (new_phase:cm_aphase) == fid`);
  thm next_rest_view = apply_conversion(rewrite_conv(THM_LIST(new_next)),
      `cm_cursors_type_ready (p:cm_program)
        (cm_phase_next_fid (fid:int) (new_phase:cm_aphase))
        (rest:(cm_acursor)list)`);
  thm next_rest = eq_mp_rule(sym_rule(next_rest_view), rest_ready);
  thm new_cursors = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `new_phase:cm_aphase`,
      `parent_temp:int`, `parent_break:int`, `parent_continue:int`,
      `rest:(cm_acursor)list`), cm_cursor_push_type_ready);
  new_cursors = mp_rule(new_cursors, assume_rule(
      `cm_phase_static_type_ready (p:cm_program) (fid:int)
        (new_phase:cm_aphase)`));
  new_cursors = mp_rule(new_cursors, assume_rule(
      `cm_phase_parent_type_ready (p:cm_program) (fid:int)
        (new_phase:cm_aphase) (rest:(cm_acursor)list)`));
  new_cursors = mp_rule(new_cursors, assume_rule(
      `cm_phase_result_type_ready (p:cm_program) (fid:int)
        (new_phase:cm_aphase) (rest:(cm_acursor)list)`));
  new_cursors = mp_rule(new_cursors, next_rest);
  thm cursor_equal = assume_rule(
      `cm_ann_cursors (next_ann:cm_annotation) ==
        CMACursor (new_phase:cm_aphase) (parent_temp:int)
          (parent_break:int) (parent_continue:int) ::
          (rest:(cm_acursor)list)`);
  thm next_cursors = conv_rule(rewrite_conv(THM_LIST(
      sym_rule(cursor_equal))), new_cursors);
  thm new_input = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `new_phase:cm_aphase`,
      `cm_expr_type (child:cm_expr)`, `parent_temp:int`,
      `parent_break:int`, `parent_continue:int`,
      `rest:(cm_acursor)list`), cm_cursor_push_input_ready),
      assume_rule(
        `cm_phase_input_type_ready (p:cm_program) (fid:int)
          (new_phase:cm_aphase) (cm_expr_type (child:cm_expr))`));
  thm next_input = conv_rule(rewrite_conv(THM_LIST(
      sym_rule(cursor_equal))), new_input);
  thm new_values = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `new_phase:cm_aphase`,
      `child:cm_expr`, `parent_temp:int`, `parent_break:int`,
      `parent_continue:int`, `rest:(cm_acursor)list`),
      cm_cursor_push_expr_values_ready), assume_rule(
        `cm_phase_expr_type_ready (p:cm_program) (fid:int)
          (new_phase:cm_aphase) (child:cm_expr)`));
  thm next_values = conv_rule(rewrite_conv(THM_LIST(
      sym_rule(cursor_equal))), new_values);
  thm target_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
      get_cm_task_type_ready_def(), same_program,
      assume_rule(`0i <= (fid:int)`),
      assume_rule(
        `(fid:int) < ilength (cm_program_functions (p:cm_program))`),
      assume_rule(
        `cm_expr_wf (p:cm_program)
          (inth (fid:int) (cm_program_functions p)) (child:cm_expr)`),
      assume_rule(`cm_scalar_expr_type (cm_expr_type (child:cm_expr))`),
      next_cursors, next_input, next_values)), goal_ccl(leaf->g));
  ACCEPT_TAC(leaf, eqt_elim_rule(target_view));
  return gnode_prove(root);
}
PROOF thm cm_c_replace_r_task_ready =
    cm_prove_c_replace_r_task_ready();

PROOF static thm cm_prove_c_pop_s_task_ready(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (q:cm_program) (fid:int) (control:cm_control)
         (child:cm_stmt) (st:cm_src_state) (next_st:cm_src_state)
         (old_ks:(cm_frame)list) (next_ks:(cm_frame)list)
         (phase:cm_aphase)
         (pc:int) (temp:int) (breakpc:int) (continuepc:int)
         (parent_temp:int) (parent_break:int) (parent_continue:int)
         (rest:(cm_acursor)list) (spills:(cm_spill)list)
         (saved:(cm_spill_frame)list) (calls:(cm_call_sim_frame)list)
         (next_ann:cm_annotation).
         cm_task_type_ready p
           (CMCTask q fid control st old_ks)
           (CMAnnotation pc temp breakpc continuepc
             (CMACursor phase parent_temp parent_break parent_continue :: rest)
             spills saved calls) ==>
         0i <= cm_phase_next_fid fid phase ==>
         cm_phase_next_fid fid phase <
           ilength (cm_program_functions p) ==>
         cm_stmt_wf p
           (inth (cm_phase_next_fid fid phase)
             (cm_program_functions p)) T child ==>
         cm_ann_cursors next_ann == rest ==>
         cm_task_type_ready p
           (CMSTask q (cm_phase_next_fid fid phase)
             child next_st next_ks) next_ann`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm components = specl_rule(TERM_LIST(
      `p:cm_program`, `q:cm_program`, `fid:int`, `control:cm_control`,
      `st:cm_src_state`, `old_ks:(cm_frame)list`, `phase:cm_aphase`,
      `pc:int`, `temp:int`, `breakpc:int`, `continuepc:int`,
      `parent_temp:int`, `parent_break:int`, `parent_continue:int`,
      `rest:(cm_acursor)list`, `spills:(cm_spill)list`,
      `saved:(cm_spill_frame)list`, `calls:(cm_call_sim_frame)list`),
      cm_c_cursor_type_components);
  components = mp_rule(components, assume_rule(
      `cm_task_type_ready (p:cm_program)
        (CMCTask (q:cm_program) (fid:int) (control:cm_control)
          (st:cm_src_state) (old_ks:(cm_frame)list))
        (CMAnnotation (pc:int) (temp:int) (breakpc:int) (continuepc:int)
          (CMACursor (phase:cm_aphase) (parent_temp:int)
            (parent_break:int) (parent_continue:int) ::
            (rest:(cm_acursor)list))
          (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
          (calls:(cm_call_sim_frame)list))`));
  thm same_program = cm_tc_pick_conjunct(components,
      `(q:cm_program) == (p:cm_program)`);
  thm rest_ready = cm_tc_pick_conjunct(components,
      `cm_cursors_type_ready (p:cm_program)
        (cm_phase_next_fid (fid:int) (phase:cm_aphase))
        (rest:(cm_acursor)list)`);
  thm cursor_equal = assume_rule(
      `cm_ann_cursors (next_ann:cm_annotation) ==
        (rest:(cm_acursor)list)`);
  thm next_cursors = conv_rule(rewrite_conv(THM_LIST(
      sym_rule(cursor_equal))), rest_ready);
  thm target_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
      get_cm_task_type_ready_def(), same_program,
      assume_rule(
        `0i <= cm_phase_next_fid (fid:int) (phase:cm_aphase)`),
      assume_rule(
        `cm_phase_next_fid (fid:int) (phase:cm_aphase) <
          ilength (cm_program_functions (p:cm_program))`),
      assume_rule(
        `cm_stmt_wf (p:cm_program)
          (inth (cm_phase_next_fid (fid:int) (phase:cm_aphase))
            (cm_program_functions p)) T (child:cm_stmt)`),
      next_cursors)), goal_ccl(leaf->g));
  ACCEPT_TAC(leaf, eqt_elim_rule(target_view));
  return gnode_prove(root);
}
PROOF thm cm_c_pop_s_task_ready =
    cm_prove_c_pop_s_task_ready();


PROOF static int cmc_preservation_type_source_c_support_final_checks(void) {
  ENSURE_COND(vector_size(hyp(cm_c_phase_family_def)) == 0 &&
      vector_size(hyp(cm_c_cursor_type_components)) == 0 &&
      vector_size(hyp(cm_c_pop_control_task_ready)) == 0 &&
      vector_size(hyp(cm_c_pop_value_task_ready)) == 0 &&
      vector_size(hyp(cm_c_replace_r_task_ready)) == 0 &&
      vector_size(hyp(cm_c_pop_s_task_ready)) == 0,
      "control type support theorem has assumptions");
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_type_source_c_support_axioms_before,
      "control type support proof introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_type_source_c_support_checks =
    cmc_preservation_type_source_c_support_final_checks();
