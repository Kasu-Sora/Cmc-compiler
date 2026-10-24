#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_code_expr.h"
#require "cmc_preservation_code_expr.c"
#include "cmc_preservation_code_stmt.h"

PROOF static size_t _cmc_preservation_code_stmt_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_prove_stmt_char_normalize_length(void) {
  gnode root = gnode_new_with_ccl(
      `!(ty:cm_type).
         ilength (cm_char_normalize_code ty) ==
         cm_char_normalize_count ty`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list cases = BOOL_CASES_TAC(
      leaf, `(ty:cm_type) == CMCharTy`, "Hchar");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    CONV_WITH_ASMP_TAC(cases[i], reduce_rewrite_conv,
        THM_LIST(get_cm_char_normalize_code_def(),
          get_cm_char_normalize_count_def(),
          get_theorem_by_name("ILENGTH_DEF"),
          get_theorem_by_name("ILENGTH_APPEND")));
  }
  return gnode_prove(root);
}
PROOF static thm cm_stmt_char_normalize_length =
    cm_prove_stmt_char_normalize_length();
PROOF static thm cm_stmt_char_normalize_expanded_length =
    conv_rule(rewrite_conv(
      THM_LIST(get_cm_char_normalize_code_def())),
      cm_stmt_char_normalize_length);


PROOF static thm cm_prove_stmt_fixed_length(
    const term statement, const thm_list rules) {
  gnode root = gnode_new_with_ccl(statement);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode reduced =
      CONV_TAC(leaf, reduce_rewrite_conv(rules));
  if (IS_NULL(reduced->solved)) {
    ACCEPT_TAC(reduced, int_arith_rule(goal_ccl(reduced->g)));
  }
  return gnode_prove(root);
}
PROOF static thm cm_stmt_fp_relative_length =
    cm_prove_stmt_fixed_length(
      `!(offset:int).
         ilength (cm_fp_relative_address_code offset) == 4i`,
      THM_LIST(get_cm_fp_relative_address_code_def(),
        get_theorem_by_name("ILENGTH_DEF"),
        get_theorem_by_name("ILENGTH_APPEND")));
PROOF static thm cm_stmt_store_length =
    cm_prove_stmt_fixed_length(
      `!(ty:cm_type). ilength (cm_store_code ty) == 1i`,
      THM_LIST(get_cm_store_code_def(),
        get_theorem_by_name("ILENGTH_DEF"),
        get_theorem_by_name("ILENGTH_APPEND")));


PROOF static thm cm_prove_cursor_code_empty_cond(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (pc:int) (temp:int)
         (normal:bool) (cursors:(cm_acursor)list).
         (if cursors == [] then []
          else cm_cursor_code p fid pc temp normal cursors) ==
         cm_cursor_code p fid pc temp normal cursors`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list cases = BOOL_CASES_TAC(
      leaf, `(cursors:(cm_acursor)list) == []`, "Hempty");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    CONV_WITH_ASMP_TAC(cases[i], reduce_rewrite_conv,
        THM_LIST(cm_cursor_code_def));
  }
  return gnode_prove(root);
}
PROOF static thm cm_cursor_code_empty_cond =
    cm_prove_cursor_code_empty_cond();


PROOF static thm_list cm_stmt_layout_rules(void) {
  return THM_LIST(
      get_cm_stmt_code_length(), get_cm_expr_code_lengths(),
      cm_task_layout_def, get_cm_task_done_def(),
      cm_task_code_def, cm_task_fid_def,
      cm_cont_code_def, cm_normal_cont_code_def,
      cm_cursor_code_def, cm_value_phase_code_def,
      cm_normal_phase_code_def, cm_phase_stops_def,
      cm_normal_phase_stops_def, cm_phase_yields_normal_def,
      cm_control_phase_code_def,
      cm_cursor_code_empty_cond,
      cm_saved_layout_def, cm_phase_site_def,
      cm_phase_is_call_def, cm_phase_caller_def,
      cm_annotation_step_def, cm_update_annotation_def,
      cm_update_s_def, cm_ann_pc_def, cm_ann_temp_def,
      cm_ann_break_def, cm_ann_continue_def, cm_ann_cursors_def,
      cm_ann_calls_def, cm_ann_push_def,
      cm_cursor_phase_def, cm_cursor_temp_def,
      cm_cursor_break_def, cm_cursor_continue_def,
      cm_phase_frame_def,
      get_cm_step_def(), get_cm_sstart_def(),
      get_cm_stmt_start_safe_def(), get_cm_local_slot_ok_def(),
      get_cm_control_kind_def(), get_cm_emit_stmt_def(),
      get_cm_stmt_code_count_def(), get_cm_emit_rvalue_def(),
      get_cm_rvalue_code_count_def(), cm_init_tail_code_def,
      cm_return_tail_code_def, get_cm_char_normalize_code_def(),
      get_cm_return_epilogue_def(),
      get_theorem_by_name("ILENGTH_DEF"),
      cm_stmt_char_normalize_length,
      cm_stmt_char_normalize_expanded_length,
      cm_stmt_fp_relative_length, cm_stmt_store_length,
      get_theorem_by_name("ILENGTH_APPEND"),
      get_theorem_by_name("HD"), get_theorem_by_name("TL"),
      get_theorem_by_name("APPEND"),
      get_theorem_by_name("APPEND_NIL"),
      gsym_rule(get_theorem_by_name("APPEND_ASSOC")),
      int_ring_rule(`(a:int) + 0i == a`),
      int_ring_rule(
        `((a:int) + (b:int)) + (c:int) == a + (b + c)`));
}

PROOF static thm cm_prove_s_structural_layout_step(
    const term statement, const term stmt,
    const thm_list extra_rules) {
  gnode root = gnode_new_with_ccl(statement);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm_list rules = cm_stmt_layout_rules();
  for (size_t i = 0; i < vector_size(extra_rules); ++i) {
    vector_add(&rules, extra_rules[i]);
  }
  thm old_layout = assume_rule(
      `cm_task_layout (p:cm_program)
         (CMSTask p (fid:int) ${stmt:cm_stmt}
           (st:cm_src_state) (ks:(cm_frame)list))
         (ann:cm_annotation)`);
  thm normalized =
      conv_rule(reduce_rewrite_conv(rules), old_layout);
  gnode reduced =
      CONV_TAC(leaf, reduce_rewrite_conv(rules));
  normalized =
      conv_rule(reduce_rewrite_conv(rules), normalized);
  reduced =
      CONV_TAC(reduced, reduce_rewrite_conv(rules));
  normalized = conv_rule(
      rewrite_conv(THM_LIST(cm_cursor_code_empty_cond)),
      normalized);
  reduced = CONV_TAC(reduced,
      rewrite_conv(THM_LIST(cm_cursor_code_empty_cond)));
  if (vector_size(extra_rules) > 0) {
    normalized = conv_rule(rewrite_conv(extra_rules), normalized);
    reduced = CONV_TAC(reduced, rewrite_conv(extra_rules));
  }
  ACCEPT_TAC(reduced, normalized);
  return gnode_prove(root);
}

PROOF static thm cm_prove_s_prefix_layout_step(
    const term statement, const term stmt) {
  gnode root = gnode_new_with_ccl(statement);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm old_layout = assume_rule(
      `cm_task_layout (p:cm_program)
         (CMSTask p (fid:int) ${stmt:cm_stmt}
           (st:cm_src_state) (ks:(cm_frame)list))
         (ann:cm_annotation)`);
  thm old_open = conv_rule(rewrite_conv(THM_LIST(
      cm_task_layout_def, get_cm_task_done_def(),
      cm_task_code_def)), old_layout);
  thm prefix_rule = ispecl_rule(TERM_LIST(
      `cm_model_code (p:cm_program)`,
      `cm_ann_pc (ann:cm_annotation)`,
      `cm_emit_stmt (p:cm_program) (fid:int)
         (cm_ann_pc (ann:cm_annotation)) (cm_ann_temp ann)
         (cm_ann_break ann) (cm_ann_continue ann)
         ${stmt:cm_stmt}`,
      `cm_normal_cont_code (p:cm_program) (fid:int)
         (cm_ann_pc (ann:cm_annotation) +
          cm_stmt_code_count p fid ${stmt:cm_stmt})
         (cm_ann_temp ann) (cm_ann_cursors ann)`),
      cm_code_at_append_left);
  thm prefix = mp_rule(prefix_rule, conjunct1_rule(old_open));
  thm result = conj_rule(prefix, conjunct2_rule(old_open));
  thm_list rules = cm_stmt_layout_rules();
  thm normalized = conv_rule(reduce_rewrite_conv(rules), result);
  gnode reduced = CONV_TAC(leaf, reduce_rewrite_conv(rules));
  ACCEPT_TAC(reduced, normalized);
  return gnode_prove(root);
}

PROOF static thm cm_s_skip_layout_step =
    cm_prove_s_structural_layout_step(
      `!(p:cm_program) (fid:int) (st:cm_src_state)
         (ks:(cm_frame)list) (ann:cm_annotation).
         cm_task_layout p (CMSTask p fid CMSkipS st ks) ann ==>
         cm_task_layout p
           (cm_step (CMSTask p fid CMSkipS st ks))
           (cm_update_annotation
             (cm_annotation_step
               (CMSTask p fid CMSkipS st ks) ann))`,
      `CMSkipS`, THM_LIST());

PROOF static thm cm_s_expr_layout_step =
    cm_prove_s_structural_layout_step(
      `!(p:cm_program) (fid:int) (expr:cm_expr)
         (st:cm_src_state) (ks:(cm_frame)list) (ann:cm_annotation).
         cm_task_layout p
           (CMSTask p fid (CMExprS expr) st ks) ann ==>
         cm_task_layout p
           (cm_step (CMSTask p fid (CMExprS expr) st ks))
           (cm_update_annotation
             (cm_annotation_step
               (CMSTask p fid (CMExprS expr) st ks) ann))`,
      `CMExprS (expr:cm_expr)`, THM_LIST());

PROOF static thm cm_s_decl_layout_step =
    cm_prove_s_structural_layout_step(
      `!(p:cm_program) (fid:int) (slot:int)
         (st:cm_src_state) (ks:(cm_frame)list) (ann:cm_annotation).
         cm_local_slot_ok p fid slot ==>
         cm_task_layout p
           (CMSTask p fid (CMDeclS slot) st ks) ann ==>
         cm_task_layout p
           (cm_step (CMSTask p fid (CMDeclS slot) st ks))
           (cm_update_annotation
             (cm_annotation_step
               (CMSTask p fid (CMDeclS slot) st ks) ann))`,
      `CMDeclS (slot:int)`, THM_LIST(
        assume_rule(
          `cm_local_slot_ok (p:cm_program) (fid:int) (slot:int)`)));

PROOF static thm cm_s_init_layout_step =
    cm_prove_s_structural_layout_step(
      `!(p:cm_program) (fid:int) (slot:int) (expr:cm_expr)
         (st:cm_src_state) (ks:(cm_frame)list) (ann:cm_annotation).
         cm_local_slot_ok p fid slot ==>
         cm_task_layout p
           (CMSTask p fid (CMInitS slot expr) st ks) ann ==>
         cm_task_layout p
           (cm_step (CMSTask p fid (CMInitS slot expr) st ks))
           (cm_update_annotation
             (cm_annotation_step
               (CMSTask p fid (CMInitS slot expr) st ks) ann))`,
      `CMInitS (slot:int) (expr:cm_expr)`, THM_LIST(
        assume_rule(
          `cm_local_slot_ok (p:cm_program) (fid:int) (slot:int)`)));

PROOF static thm cm_s_seq_layout_step =
    cm_prove_s_structural_layout_step(
      `!(p:cm_program) (fid:int) (first:cm_stmt) (second:cm_stmt)
         (st:cm_src_state) (ks:(cm_frame)list) (ann:cm_annotation).
         cm_task_layout p
           (CMSTask p fid (CMSeqS first second) st ks) ann ==>
         cm_task_layout p
           (cm_step (CMSTask p fid (CMSeqS first second) st ks))
           (cm_update_annotation
             (cm_annotation_step
               (CMSTask p fid (CMSeqS first second) st ks) ann))`,
      `CMSeqS (first:cm_stmt) (second:cm_stmt)`, THM_LIST());

PROOF static thm cm_s_block_layout_step =
    cm_prove_s_structural_layout_step(
      `!(p:cm_program) (fid:int) (body:cm_stmt)
         (st:cm_src_state) (ks:(cm_frame)list) (ann:cm_annotation).
         cm_task_layout p
           (CMSTask p fid (CMBlockS body) st ks) ann ==>
         cm_task_layout p
           (cm_step (CMSTask p fid (CMBlockS body) st ks))
           (cm_update_annotation
             (cm_annotation_step
               (CMSTask p fid (CMBlockS body) st ks) ann))`,
      `CMBlockS (body:cm_stmt)`, THM_LIST());

PROOF static thm cm_s_if_layout_step =
    cm_prove_s_structural_layout_step(
      `!(p:cm_program) (fid:int) (guard:cm_expr)
         (yes:cm_stmt) (no:cm_stmt) (st:cm_src_state)
         (ks:(cm_frame)list) (ann:cm_annotation).
         cm_task_layout p
           (CMSTask p fid (CMIfS guard yes no) st ks) ann ==>
         cm_task_layout p
           (cm_step (CMSTask p fid (CMIfS guard yes no) st ks))
           (cm_update_annotation
             (cm_annotation_step
               (CMSTask p fid (CMIfS guard yes no) st ks) ann))`,
      `CMIfS (guard:cm_expr) (yes:cm_stmt) (no:cm_stmt)`,
      THM_LIST(
        int_ring_rule(
          `(a:int) + 1i + (b:int) + 1i ==
           a + 2i + b`),
        int_ring_rule(
          `(a:int) + 1i + (b:int) + 1i + (c:int) ==
           a + 2i + b + c`)));

PROOF static thm cm_prove_s_while_layout_step(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (guard:cm_expr) (body:cm_stmt)
         (st:cm_src_state) (ks:(cm_frame)list) (ann:cm_annotation).
         cm_task_layout p
           (CMSTask p fid (CMWhileS guard body) st ks) ann ==>
         cm_task_layout p
           (cm_step (CMSTask p fid (CMWhileS guard body) st ks))
           (cm_update_annotation
             (cm_annotation_step
               (CMSTask p fid (CMWhileS guard body) st ks) ann))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm old_layout = assume_rule(
      `cm_task_layout (p:cm_program)
         (CMSTask p (fid:int)
           (CMWhileS (guard:cm_expr) (body:cm_stmt))
           (st:cm_src_state) (ks:(cm_frame)list))
         (ann:cm_annotation)`);
  thm old_open = conv_rule(rewrite_conv(THM_LIST(
      cm_task_layout_def, get_cm_task_done_def(),
      cm_task_code_def)), old_layout);
  thm old_code = conjunct1_rule(old_open);
  thm tail_rule = ispecl_rule(TERM_LIST(
      `cm_model_code (p:cm_program)`,
      `cm_ann_pc (ann:cm_annotation)`,
      `cm_emit_stmt (p:cm_program) (fid:int)
         (cm_ann_pc (ann:cm_annotation)) (cm_ann_temp ann)
         (cm_ann_break ann) (cm_ann_continue ann)
         (CMWhileS (guard:cm_expr) (body:cm_stmt))`,
      `cm_normal_cont_code (p:cm_program) (fid:int)
         (cm_ann_pc (ann:cm_annotation) +
          cm_stmt_code_count p fid
            (CMWhileS (guard:cm_expr) (body:cm_stmt)))
         (cm_ann_temp ann) (cm_ann_cursors ann)`),
      cm_code_at_append_right);
  thm tail = mp_rule(tail_rule, old_code);
  tail = conv_rule(rewrite_conv(
      THM_LIST(get_cm_stmt_code_length())), tail);
  thm result = conj_rule(old_code,
      conj_rule(conj_rule(old_code, tail),
        conjunct2_rule(old_open)));
  thm_list rules = cm_stmt_layout_rules();
  thm normalized =
      conv_rule(reduce_rewrite_conv(rules), result);
  normalized =
      conv_rule(reduce_rewrite_conv(rules), normalized);
  normalized = conv_rule(rewrite_conv(
      THM_LIST(cm_cursor_code_empty_cond)), normalized);
  gnode reduced =
      CONV_TAC(leaf, reduce_rewrite_conv(rules));
  reduced = CONV_TAC(reduced, reduce_rewrite_conv(rules));
  reduced = CONV_TAC(reduced, rewrite_conv(
      THM_LIST(cm_cursor_code_empty_cond)));
  ACCEPT_TAC(reduced, normalized);
  return gnode_prove(root);
}
PROOF static thm cm_s_while_layout_step =
    cm_prove_s_while_layout_step();

PROOF static thm cm_s_break_layout_step =
    cm_prove_s_prefix_layout_step(
      `!(p:cm_program) (fid:int) (st:cm_src_state)
         (ks:(cm_frame)list) (ann:cm_annotation).
         cm_task_layout p (CMSTask p fid CMBreakS st ks) ann ==>
         cm_task_layout p
           (cm_step (CMSTask p fid CMBreakS st ks))
           (cm_update_annotation
             (cm_annotation_step
               (CMSTask p fid CMBreakS st ks) ann))`,
      `CMBreakS`);

PROOF static thm cm_s_continue_layout_step =
    cm_prove_s_prefix_layout_step(
      `!(p:cm_program) (fid:int) (st:cm_src_state)
         (ks:(cm_frame)list) (ann:cm_annotation).
         cm_task_layout p (CMSTask p fid CMContinueS st ks) ann ==>
         cm_task_layout p
           (cm_step (CMSTask p fid CMContinueS st ks))
           (cm_update_annotation
             (cm_annotation_step
               (CMSTask p fid CMContinueS st ks) ann))`,
      `CMContinueS`);

PROOF static thm cm_s_return_layout_step =
    cm_prove_s_prefix_layout_step(
      `!(p:cm_program) (fid:int) (expr:cm_expr)
         (st:cm_src_state) (ks:(cm_frame)list) (ann:cm_annotation).
         cm_task_layout p
           (CMSTask p fid (CMReturnS expr) st ks) ann ==>
         cm_task_layout p
           (cm_step (CMSTask p fid (CMReturnS expr) st ks))
           (cm_update_annotation
             (cm_annotation_step
               (CMSTask p fid (CMReturnS expr) st ks) ann))`,
      `CMReturnS (expr:cm_expr)`);

PROOF static void cm_accept_s_constructor_layout(
    const gnode branch, const thm constructor_step,
    const size_t constructor_index) {
  labeled_term_list assumptions = goal_lasmps(branch->g);
  thm shape = assume_rule(
      assumptions[
        labeled_term_list_index(assumptions, "Hstmt")].tm);
  thm layout = conv_rule(rewrite_conv(THM_LIST(shape)),
      assume_rule(
        `cm_task_layout (p:cm_program)
           (CMSTask p (fid:int) (stmt:cm_stmt)
             (st:cm_src_state) (ks:(cm_frame)list))
           (ann:cm_annotation)`));
  thm result = constructor_step;
  if (constructor_index == 2 || constructor_index == 3) {
    thm safe = conv_rule(reduce_rewrite_conv(THM_LIST(
        shape, get_cm_stmt_start_safe_def())),
        assume_rule(
          `cm_stmt_start_safe
            (p:cm_program) (fid:int) (stmt:cm_stmt)`));
    result = match_mp_rule(result, safe);
  }
  result = match_mp_rule(result, layout);
  gnode shaped =
      CONV_TAC(branch, rewrite_conv(THM_LIST(shape)));
  ACCEPT_TAC(shaped, result);
}

PROOF static thm cm_prove_s_task_layout_step(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (stmt:cm_stmt)
         (st:cm_src_state) (ks:(cm_frame)list) (ann:cm_annotation).
         cm_stmt_start_safe p fid stmt ==>
         cm_task_layout p
           (CMSTask p fid stmt st ks) ann ==>
         cm_task_layout p
           (cm_step (CMSTask p fid stmt st ks))
           (cm_update_annotation
             (cm_annotation_step
               (CMSTask p fid stmt st ks) ann))`);
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list cases = DISJ_CASES_TAC(
      introduced,
      ispec_rule(`stmt:cm_stmt`, get_cm_stmt_cases()),
      "Hstmt");
  thm constructor_steps[11] = {
    cm_s_skip_layout_step, cm_s_expr_layout_step,
    cm_s_decl_layout_step, cm_s_init_layout_step,
    cm_s_seq_layout_step, cm_s_block_layout_step,
    cm_s_if_layout_step, cm_s_while_layout_step,
    cm_s_break_layout_step, cm_s_continue_layout_step,
    cm_s_return_layout_step
  };
  for (size_t i = 0; i < vector_size(cases); ++i) {
    while (true) {
      labeled_term_list assumptions = goal_lasmps(cases[i]->g);
      int index =
          labeled_term_list_index(assumptions, "Hstmt");
      if (!is_exists(assumptions[index].tm)) break;
      cases[i] = ASMP_EXISTS_TAC(cases[i], "Hstmt", NULL);
    }
    cm_accept_s_constructor_layout(
        cases[i], constructor_steps[i], i);
  }
  return gnode_prove(root);
}
PROOF thm cm_s_task_layout_step =
    cm_prove_s_task_layout_step();

PROOF thm get_cm_s_task_layout_step(void) {
  return cm_s_task_layout_step;
}

PROOF thm get_cm_cursor_code_empty_cond(void) {
  return cm_cursor_code_empty_cond;
}
PROOF thm get_cm_stmt_fp_relative_length(void) {
  return cm_stmt_fp_relative_length;
}
PROOF thm get_cm_stmt_char_normalize_expanded_length(void) {
  return cm_stmt_char_normalize_expanded_length;
}

PROOF static int cmc_preservation_code_stmt_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_code_stmt_axioms_before,
      "cmc_preservation_code_stmt introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_code_stmt_checks =
    cmc_preservation_code_stmt_final_checks();
