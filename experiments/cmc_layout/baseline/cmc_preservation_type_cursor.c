#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_type_cursor.h"

#require "cmc_preservation_type_phase.c"

PROOF static size_t _cmc_preservation_type_cursor_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_prove_cursor_push_type_ready(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (phase:cm_aphase)
         (temp:int) (breakpc:int) (continuepc:int)
         (rest:(cm_acursor)list).
         cm_phase_static_type_ready p fid phase ==>
         cm_phase_parent_type_ready p fid phase rest ==>
         cm_phase_result_type_ready p fid phase rest ==>
         cm_cursors_type_ready p (cm_phase_next_fid fid phase) rest ==>
         cm_cursors_type_ready p fid
           (CMACursor phase temp breakpc continuepc :: rest)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm target_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
      get_cm_cursors_type_ready_def(), cm_cursor_phase_def)),
      goal_ccl(leaf->g));
  thm result = conj_rule(assume_rule(
      `cm_phase_static_type_ready (p:cm_program) (fid:int)
        (phase:cm_aphase)`),
      conj_rule(assume_rule(
        `cm_phase_parent_type_ready (p:cm_program) (fid:int)
          (phase:cm_aphase) (rest:(cm_acursor)list)`),
        conj_rule(assume_rule(
          `cm_phase_result_type_ready (p:cm_program) (fid:int)
            (phase:cm_aphase) (rest:(cm_acursor)list)`),
          assume_rule(
            `cm_cursors_type_ready (p:cm_program)
              (cm_phase_next_fid (fid:int) (phase:cm_aphase))
              (rest:(cm_acursor)list)`))));
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), result));
  return gnode_prove(root);
}
PROOF thm cm_cursor_push_type_ready =
    cm_prove_cursor_push_type_ready();

PROOF static thm cm_prove_cursor_push_input_ready(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (phase:cm_aphase)
         (incoming:cm_type) (temp:int) (breakpc:int) (continuepc:int)
         (rest:(cm_acursor)list).
         cm_phase_input_type_ready p fid phase incoming ==>
         cm_cursor_head_input_type_ready p fid incoming
           (CMACursor phase temp breakpc continuepc :: rest)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm target_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
      get_cm_cursor_head_input_type_ready_def(), cm_cursor_phase_def)),
      goal_ccl(leaf->g));
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), assume_rule(
      `cm_phase_input_type_ready (p:cm_program) (fid:int)
        (phase:cm_aphase) (incoming:cm_type)`)));
  return gnode_prove(root);
}
PROOF thm cm_cursor_push_input_ready =
    cm_prove_cursor_push_input_ready();

PROOF static thm cm_prove_cursor_push_expr_values_ready(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (phase:cm_aphase)
         (expr:cm_expr) (temp:int) (breakpc:int) (continuepc:int)
         (rest:(cm_acursor)list).
         cm_phase_expr_type_ready p fid phase expr ==>
         cm_cursor_expr_values_type_ready p fid expr
           (CMACursor phase temp breakpc continuepc :: rest)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm head = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `expr:cm_expr`,
      `(CMACursor (phase:cm_aphase) (temp:int) (breakpc:int)
         (continuepc:int) :: (rest:(cm_acursor)list))`),
      cm_cursor_expr_rule_values),
      eq_mp_rule(sym_rule(apply_conversion(reduce_rewrite_conv(THM_LIST(
          get_cm_cursor_head_expr_type_ready_def(), cm_cursor_phase_def)),
          `cm_cursor_head_expr_type_ready (p:cm_program) (fid:int)
            (expr:cm_expr)
            (CMACursor (phase:cm_aphase) (temp:int) (breakpc:int)
              (continuepc:int) :: (rest:(cm_acursor)list))`)),
        assume_rule(
          `cm_phase_expr_type_ready (p:cm_program) (fid:int)
            (phase:cm_aphase) (expr:cm_expr)`)));
  ACCEPT_TAC(leaf, head);
  return gnode_prove(root);
}
PROOF thm cm_cursor_push_expr_values_ready =
    cm_prove_cursor_push_expr_values_ready();

PROOF static thm cm_prove_cursor_push_lvalue_ready(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (phase:cm_aphase)
         (output:cm_type) (temp:int) (breakpc:int) (continuepc:int)
         (rest:(cm_acursor)list).
         cm_phase_lvalue_type_ready p fid phase output ==>
         cm_cursor_head_lvalue_type_ready p fid output
           (CMACursor phase temp breakpc continuepc :: rest)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm target_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
      get_cm_cursor_head_lvalue_type_ready_def(), cm_cursor_phase_def)),
      goal_ccl(leaf->g));
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), assume_rule(
      `cm_phase_lvalue_type_ready (p:cm_program) (fid:int)
        (phase:cm_aphase) (output:cm_type)`)));
  return gnode_prove(root);
}
PROOF thm cm_cursor_push_lvalue_ready =
    cm_prove_cursor_push_lvalue_ready();

PROOF static thm cm_prove_lvalue_cursor_expr_values(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (output:cm_type)
         (expr:cm_expr) (cursors:(cm_acursor)list).
         cm_cursor_head_lvalue_type_ready p fid output cursors ==>
         output == cm_expr_type expr ==>
         cm_cursor_expr_values_type_ready p fid expr cursors`);
  gnode leaf = AUTO_INTROS_TAC(root);
  term value_ready_term =
      `cm_expr_value_type_ready (expr:cm_expr) (v:cm_value)`;
  thm value_ready = assume_rule(value_ready_term);
  thm compatible = conjunct1_rule(conv_rule(rewrite_conv(THM_LIST(
      get_cm_expr_value_type_ready_def())), value_ready));
  thm same = assume_rule(
      `(output:cm_type) == cm_expr_type (expr:cm_expr)`);
  thm output_compatible = conv_rule(rewrite_conv(THM_LIST(
      sym_rule(same))), compatible);
  thm result = mp_rule(mp_rule(specl_rule(TERM_LIST(
      `cursors:(cm_acursor)list`, `p:cm_program`, `fid:int`,
      `output:cm_type`, `v:cm_value`), cm_cursor_lvalue_value_ready),
      assume_rule(
        `cm_cursor_head_lvalue_type_ready (p:cm_program) (fid:int)
          (output:cm_type) (cursors:(cm_acursor)list)`)),
      output_compatible);
  result = gen_rule(`v:cm_value`, disch_rule(value_ready_term, result));
  thm target_view = apply_conversion(rewrite_conv(THM_LIST(
      get_cm_cursor_expr_values_type_ready_def())), goal_ccl(leaf->g));
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), result));
  return gnode_prove(root);
}
PROOF thm cm_lvalue_cursor_expr_values =
    cm_prove_lvalue_cursor_expr_values();

PROOF static thm cm_prove_expr_cursor_values_transport_nonzero(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (old_expr:cm_expr)
         (new_expr:cm_expr) (cursors:(cm_acursor)list).
         cm_cursor_expr_values_type_ready p fid old_expr cursors ==>
         cm_expr_type old_expr == cm_expr_type new_expr ==>
         ~cm_zero_literal old_expr ==>
         cm_cursor_expr_values_type_ready p fid new_expr cursors`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm old_ready = conv_rule(rewrite_conv(THM_LIST(
      get_cm_cursor_expr_values_type_ready_def())), assume_rule(
      `cm_cursor_expr_values_type_ready (p:cm_program) (fid:int)
        (old_expr:cm_expr) (cursors:(cm_acursor)list)`));
  term new_value_term =
      `cm_expr_value_type_ready (new_expr:cm_expr) (v:cm_value)`;
  thm new_value = conv_rule(rewrite_conv(THM_LIST(
      get_cm_expr_value_type_ready_def())), assume_rule(new_value_term));
  thm same = assume_rule(
      `cm_expr_type (old_expr:cm_expr) ==
        cm_expr_type (new_expr:cm_expr)`);
  thm old_compatible = conv_rule(rewrite_conv(THM_LIST(
      sym_rule(same))), conjunct1_rule(new_value));
  thm old_nonzero = assume_rule(
      `~cm_zero_literal (old_expr:cm_expr)`);
  thm zero_clause = mp_rule(taut_rule(
      `~cm_zero_literal (old_expr:cm_expr) ==>
       (cm_zero_literal old_expr ==> (v:cm_value) == CMIntV 0i)`),
      old_nonzero);
  thm old_value_open = conj_rule(old_compatible, zero_clause);
  thm old_value_view = apply_conversion(rewrite_conv(THM_LIST(
      get_cm_expr_value_type_ready_def())),
      `cm_expr_value_type_ready (old_expr:cm_expr) (v:cm_value)`);
  thm old_value = eq_mp_rule(sym_rule(old_value_view), old_value_open);
  thm result = mp_rule(spec_rule(`v:cm_value`, old_ready), old_value);
  result = gen_rule(`v:cm_value`, disch_rule(new_value_term, result));
  thm target_view = apply_conversion(rewrite_conv(THM_LIST(
      get_cm_cursor_expr_values_type_ready_def())), goal_ccl(leaf->g));
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), result));
  return gnode_prove(root);
}
PROOF thm cm_expr_cursor_values_transport_nonzero =
    cm_prove_expr_cursor_values_transport_nonzero();

PROOF static thm cm_prove_expr_cursor_values_lvalue(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (expr:cm_expr)
         (output:cm_type) (cursors:(cm_acursor)list).
         cm_cursor_expr_values_type_ready p fid expr cursors ==>
         output == cm_expr_type expr ==>
         ~cm_zero_literal expr ==>
         (?w. cm_value_type_compatible (w:cm_value) output) ==>
         cm_cursor_head_lvalue_type_ready p fid output cursors`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm all_values = conv_rule(rewrite_conv(THM_LIST(
      get_cm_cursor_expr_values_type_ready_def())), assume_rule(
        `cm_cursor_expr_values_type_ready (p:cm_program) (fid:int)
          (expr:cm_expr) (cursors:(cm_acursor)list)`));
  term compatible_term =
      `cm_value_type_compatible (v:cm_value) (output:cm_type)`;
  thm compatible = conv_rule(rewrite_conv(THM_LIST(assume_rule(
      `(output:cm_type) == cm_expr_type (expr:cm_expr)`))),
      assume_rule(compatible_term));
  thm zero_clause = mp_rule(taut_rule(
      `~cm_zero_literal (expr:cm_expr) ==>
       (cm_zero_literal expr ==> (v:cm_value) == CMIntV 0i)`),
      assume_rule(`~cm_zero_literal (expr:cm_expr)`));
  thm value_open = conj_rule(compatible, zero_clause);
  thm value_view = apply_conversion(rewrite_conv(THM_LIST(
      get_cm_expr_value_type_ready_def())),
      `cm_expr_value_type_ready (expr:cm_expr) (v:cm_value)`);
  thm value_ready = eq_mp_rule(sym_rule(value_view), value_open);
  thm result = mp_rule(spec_rule(`v:cm_value`, all_values),
      value_ready);
  result = gen_rule(`v:cm_value`,
      disch_rule(compatible_term, result));
  gnode_list cases = DISJ_CASES_TAC(leaf,
      ispec_rule(`cursors:(cm_acursor)list`,
        get_theorem_by_name("list_CASES")), "Hcursors");
  {
    labeled_term_list assumptions = goal_lasmps(cases[0]->g);
    thm nil_shape = assume_rule(assumptions[
        labeled_term_list_index(assumptions, "Hcursors")].tm);
    term witness_body =
        `cm_value_type_compatible (w:cm_value) (output:cm_type)`;
    thm head = mp_rule(spec_rule(`w:cm_value`, result),
        assume_rule(witness_body));
    thm impossible = conv_rule(reduce_rewrite_conv(THM_LIST(
        nil_shape, get_cm_cursor_head_value_type_ready_def())), head);
    impossible = choose_rule(`w:cm_value`, assume_rule(
        `?w. cm_value_type_compatible (w:cm_value) (output:cm_type)`),
        impossible);
    CONTR_TAC(cases[0], impossible);
  }
  {
    gnode cons_branch =
        ASMP_EXISTS_TAC(cases[1], "Hcursors", "head");
    cons_branch =
        ASMP_EXISTS_TAC(cons_branch, "Hcursors", "rest");
    labeled_term_list assumptions = goal_lasmps(cons_branch->g);
    thm cons_shape = assume_rule(assumptions[
        labeled_term_list_index(assumptions, "Hcursors")].tm);
    thm normalized_result = conv_rule(reduce_rewrite_conv(THM_LIST(
        cons_shape, get_cm_cursor_head_value_type_ready_def(),
        cm_cursor_phase_def)), result);
    thm target_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
        cons_shape, get_cm_cursor_head_lvalue_type_ready_def(),
        get_cm_phase_lvalue_type_ready_def(), cm_cursor_phase_def)),
        goal_ccl(cons_branch->g));
    ACCEPT_TAC(cons_branch,
        eq_mp_rule(sym_rule(target_view), normalized_result));
  }
  return gnode_prove(root);
}
PROOF thm cm_expr_cursor_values_lvalue =
    cm_prove_expr_cursor_values_lvalue();

PROOF static thm cm_prove_cursor_expr_result_ready(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (expr:cm_expr)
         (cursors:(cm_acursor)list).
         cm_cursor_expr_values_type_ready p fid expr cursors ==>
         ~cm_zero_literal expr ==>
         !(v:cm_value).
           cm_value_type_compatible v (cm_expr_type expr) ==>
           cm_cursor_head_value_type_ready p fid v cursors`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm all_values = conv_rule(rewrite_conv(THM_LIST(
      get_cm_cursor_expr_values_type_ready_def())), assume_rule(
      `cm_cursor_expr_values_type_ready (p:cm_program) (fid:int)
        (expr:cm_expr) (cursors:(cm_acursor)list)`));
  thm zero_clause = mp_rule(taut_rule(
      `~cm_zero_literal (expr:cm_expr) ==>
       (cm_zero_literal expr ==> (v:cm_value) == CMIntV 0i)`),
      assume_rule(`~cm_zero_literal (expr:cm_expr)`));
  thm value_open = conj_rule(assume_rule(
      `cm_value_type_compatible (v:cm_value)
        (cm_expr_type (expr:cm_expr))`), zero_clause);
  thm value_view = apply_conversion(rewrite_conv(THM_LIST(
      get_cm_expr_value_type_ready_def())),
      `cm_expr_value_type_ready (expr:cm_expr) (v:cm_value)`);
  thm value_ready = eq_mp_rule(sym_rule(value_view), value_open);
  ACCEPT_TAC(leaf, mp_rule(spec_rule(`v:cm_value`, all_values),
      value_ready));
  return gnode_prove(root);
}
PROOF thm cm_cursor_expr_result_ready =
    cm_prove_cursor_expr_result_ready();

PROOF static thm cm_prove_phase_result_type_unique(void) {
  gnode root = gnode_new_with_ccl(
      `!(phase:cm_aphase) (p:cm_program) (fid:int)
         (left:cm_type) (right:cm_type).
         cm_phase_result_type p fid phase left ==>
         cm_phase_result_type p fid phase right ==>
         left == right`);
  gnode_list cases = INDUCT_TAC(root, `phase:cm_aphase`);
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode reduced = CONV_TAC(cases[i],
        reduce_rewrite_conv(THM_LIST(
          get_cm_phase_result_type_def())));
    if (!IS_NULL(reduced->solved)) continue;
    gnode leaf = AUTO_INTROS_TAC(reduced);
    if (!IS_NULL(leaf->solved)) continue;
    labeled_term_list assumptions = goal_lasmps(leaf->g);
    if (i == 0 || (12 <= i && i <= 20)) {
      thm impossible = empty_theorem;
      for (size_t j = 0; j < vector_size(assumptions); ++j) {
        if (is_false(assumptions[j].tm)) {
          impossible = assume_rule(assumptions[j].tm);
          break;
        }
      }
      CONTR_TAC(leaf, impossible);
    } else {
      thm left_equal = assume_rule(
          assumptions[vector_size(assumptions) - 2].tm);
      thm right_equal = assume_rule(
          assumptions[vector_size(assumptions) - 1].tm);
      ACCEPT_TAC(leaf,
          trans_rule(left_equal, sym_rule(right_equal)));
    }
  }
  return gnode_prove(root);
}
PROOF static thm cm_phase_result_type_unique =
    cm_prove_phase_result_type_unique();

PROOF static thm cm_prove_phase_result_from_expr(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (phase:cm_aphase)
         (expr:cm_expr) (cursors:(cm_acursor)list).
         cm_cursor_expr_values_type_ready p fid expr cursors ==>
         ~cm_zero_literal expr ==>
         (!(result:cm_type).
            cm_phase_result_type p fid phase result ==>
            result == cm_expr_type expr) ==>
         cm_phase_next_fid fid phase == fid ==>
         cm_phase_result_type_ready p fid phase cursors`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm all_results = mp_rule(mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `expr:cm_expr`,
      `cursors:(cm_acursor)list`), cm_cursor_expr_result_ready),
      assume_rule(
        `cm_cursor_expr_values_type_ready (p:cm_program) (fid:int)
          (expr:cm_expr) (cursors:(cm_acursor)list)`)),
      assume_rule(`~cm_zero_literal (expr:cm_expr)`));
  term result_premise =
      `cm_phase_result_type (p:cm_program) (fid:int)
        (phase:cm_aphase) (result:cm_type)`;
  term compatible_premise =
      `cm_value_type_compatible (v:cm_value) (result:cm_type)`;
  thm result_equal = mp_rule(spec_rule(`result:cm_type`, assume_rule(
      `!(candidate:cm_type).
         cm_phase_result_type (p:cm_program) (fid:int)
           (phase:cm_aphase) candidate ==>
         candidate == cm_expr_type (expr:cm_expr)`)),
      assume_rule(result_premise));
  thm compatible = conv_rule(rewrite_conv(THM_LIST(result_equal)),
      assume_rule(compatible_premise));
  thm accepted = mp_rule(spec_rule(`v:cm_value`, all_results),
      compatible);
  thm next_fid = assume_rule(
      `cm_phase_next_fid (fid:int) (phase:cm_aphase) == fid`);
  thm body = disch_rule(compatible_premise, accepted);
  body = disch_rule(result_premise, body);
  body = gen_rule(`v:cm_value`, body);
  body = gen_rule(`result:cm_type`, body);
  thm target_view = apply_conversion(rewrite_conv(THM_LIST(
      get_cm_phase_result_type_ready_def(), next_fid)), goal_ccl(leaf->g));
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), body));
  return gnode_prove(root);
}
PROOF thm cm_phase_result_from_expr =
    cm_prove_phase_result_from_expr();

PROOF static thm cm_prove_phase_result_from_lvalue(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (phase:cm_aphase)
         (output:cm_type) (cursors:(cm_acursor)list).
         cm_cursor_head_lvalue_type_ready p fid output cursors ==>
         (!(result:cm_type).
            cm_phase_result_type p fid phase result ==>
            result == output) ==>
         cm_phase_next_fid fid phase == fid ==>
         cm_phase_result_type_ready p fid phase cursors`);
  gnode leaf = AUTO_INTROS_TAC(root);
  term result_premise =
      `cm_phase_result_type (p:cm_program) (fid:int)
        (phase:cm_aphase) (result:cm_type)`;
  term compatible_premise =
      `cm_value_type_compatible (v:cm_value) (result:cm_type)`;
  thm result_equal = mp_rule(spec_rule(`result:cm_type`, assume_rule(
      `!(candidate:cm_type).
         cm_phase_result_type (p:cm_program) (fid:int)
           (phase:cm_aphase) candidate ==>
         candidate == (output:cm_type)`)),
      assume_rule(result_premise));
  thm compatible = conv_rule(rewrite_conv(THM_LIST(result_equal)),
      assume_rule(compatible_premise));
  thm accepted = mp_rule(mp_rule(specl_rule(TERM_LIST(
      `cursors:(cm_acursor)list`, `p:cm_program`, `fid:int`,
      `output:cm_type`, `v:cm_value`), cm_cursor_lvalue_value_ready),
      assume_rule(
        `cm_cursor_head_lvalue_type_ready (p:cm_program) (fid:int)
          (output:cm_type) (cursors:(cm_acursor)list)`)), compatible);
  term next_fid_term =
      `cm_phase_next_fid (fid:int) (phase:cm_aphase) == fid`;
  thm body = disch_rule(compatible_premise, accepted);
  body = disch_rule(result_premise, body);
  body = gen_rule(`v:cm_value`, body);
  body = gen_rule(`result:cm_type`, body);
  thm target_view = apply_conversion(rewrite_conv(THM_LIST(
      get_cm_phase_result_type_ready_def(),
      assume_rule(next_fid_term))), goal_ccl(leaf->g));
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), body));
  return gnode_prove(root);
}
PROOF thm cm_phase_result_from_lvalue =
    cm_prove_phase_result_from_lvalue();

PROOF static thm cm_tc_pick_conjunct(thm fact, term wanted) {
  if (alpha_compare(concl(fact), wanted) == 0) return fact;
  if (!is_conj(concl(fact))) return empty_theorem;
  thm left = cm_tc_pick_conjunct(conjunct1_rule(fact), wanted);
  if (!IS_NULL(left)) return left;
  return cm_tc_pick_conjunct(conjunct2_rule(fact), wanted);
}

PROOF static thm cm_prove_r_value_task_ready(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (q:cm_program) (fid:int) (expr:cm_expr)
         (st:cm_src_state) (ks:(cm_frame)list) (ann:cm_annotation)
         (v:cm_value) (next_st:cm_src_state) (next_ann:cm_annotation).
         cm_task_type_ready p (CMRTask q fid expr st ks) ann ==>
         cm_expr_value_type_ready expr v ==>
         cm_ann_cursors next_ann == cm_ann_cursors ann ==>
         cm_task_type_ready p
           (CMVTask q fid v next_st ks) next_ann`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_task_type_ready_def())), assume_rule(
      `cm_task_type_ready (p:cm_program)
        (CMRTask (q:cm_program) (fid:int) (expr:cm_expr)
          (st:cm_src_state) (ks:(cm_frame)list))
        (ann:cm_annotation)`));
  thm same_program = cm_tc_pick_conjunct(opened,
      `(q:cm_program) == (p:cm_program)`);
  thm cursors_ready = cm_tc_pick_conjunct(opened,
      `cm_cursors_type_ready (p:cm_program) (fid:int)
        (cm_ann_cursors (ann:cm_annotation))`);
  thm values_ready = cm_tc_pick_conjunct(opened,
      `cm_cursor_expr_values_type_ready (p:cm_program) (fid:int)
        (expr:cm_expr) (cm_ann_cursors (ann:cm_annotation))`);
  values_ready = conv_rule(rewrite_conv(THM_LIST(
      get_cm_cursor_expr_values_type_ready_def())), values_ready);
  thm head_ready = mp_rule(spec_rule(`v:cm_value`, values_ready),
      assume_rule(
        `cm_expr_value_type_ready (expr:cm_expr) (v:cm_value)`));
  thm cursor_equal = assume_rule(
      `cm_ann_cursors (next_ann:cm_annotation) ==
        cm_ann_cursors (ann:cm_annotation)`);
  thm next_cursors = conv_rule(rewrite_conv(THM_LIST(
      sym_rule(cursor_equal))), cursors_ready);
  thm next_head = conv_rule(rewrite_conv(THM_LIST(
      sym_rule(cursor_equal))), head_ready);
  thm target_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
      get_cm_task_type_ready_def(), same_program,
      next_cursors, next_head)), goal_ccl(leaf->g));
  ACCEPT_TAC(leaf, eqt_elim_rule(target_view));
  return gnode_prove(root);
}
PROOF thm cm_r_value_task_ready =
    cm_prove_r_value_task_ready();

PROOF static thm cm_prove_l_value_task_ready(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (q:cm_program) (fid:int) (expr:cm_expr)
         (st:cm_src_state) (ks:(cm_frame)list) (ann:cm_annotation)
         (v:cm_value) (next_st:cm_src_state) (next_ann:cm_annotation).
         cm_task_type_ready p (CMLTask q fid expr st ks) ann ==>
         cm_value_type_compatible v
           (cm_lvalue_output_type p
             (inth fid (cm_program_functions p)) expr) ==>
         cm_ann_cursors next_ann == cm_ann_cursors ann ==>
         cm_task_type_ready p
           (CMVTask q fid v next_st ks) next_ann`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_task_type_ready_def())), assume_rule(
      `cm_task_type_ready (p:cm_program)
        (CMLTask (q:cm_program) (fid:int) (expr:cm_expr)
          (st:cm_src_state) (ks:(cm_frame)list))
        (ann:cm_annotation)`));
  thm same_program = cm_tc_pick_conjunct(opened,
      `(q:cm_program) == (p:cm_program)`);
  thm cursors_ready = cm_tc_pick_conjunct(opened,
      `cm_cursors_type_ready (p:cm_program) (fid:int)
        (cm_ann_cursors (ann:cm_annotation))`);
  thm lvalue_ready = cm_tc_pick_conjunct(opened,
      `cm_cursor_head_lvalue_type_ready (p:cm_program) (fid:int)
        (cm_lvalue_output_type p
          (inth fid (cm_program_functions p)) (expr:cm_expr))
        (cm_ann_cursors (ann:cm_annotation))`);
  thm head_ready = mp_rule(mp_rule(specl_rule(TERM_LIST(
      `cm_ann_cursors (ann:cm_annotation)`, `p:cm_program`, `fid:int`,
      `cm_lvalue_output_type p
        (inth fid (cm_program_functions p)) (expr:cm_expr)`,
      `v:cm_value`), cm_cursor_lvalue_value_ready), lvalue_ready),
      assume_rule(
        `cm_value_type_compatible (v:cm_value)
          (cm_lvalue_output_type (p:cm_program)
            (inth (fid:int) (cm_program_functions p)) (expr:cm_expr))`));
  thm cursor_equal = assume_rule(
      `cm_ann_cursors (next_ann:cm_annotation) ==
        cm_ann_cursors (ann:cm_annotation)`);
  thm next_cursors = conv_rule(rewrite_conv(THM_LIST(
      sym_rule(cursor_equal))), cursors_ready);
  thm next_head = conv_rule(rewrite_conv(THM_LIST(
      sym_rule(cursor_equal))), head_ready);
  thm target_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
      get_cm_task_type_ready_def(), same_program,
      next_cursors, next_head)), goal_ccl(leaf->g));
  ACCEPT_TAC(leaf, eqt_elim_rule(target_view));
  return gnode_prove(root);
}
PROOF thm cm_l_value_task_ready =
    cm_prove_l_value_task_ready();

PROOF static thm cm_prove_r_push_task_ready(void) {
  term old_cursors =
      `cm_ann_cursors (ann:cm_annotation)`;
  term child_type =
      `cm_expr_type (child:cm_expr)`;
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (q:cm_program) (fid:int)
         (parent:cm_expr) (child:cm_expr) (st:cm_src_state)
         (ks:(cm_frame)list) (frame:cm_frame)
         (ann:cm_annotation) (phase:cm_aphase).
         cm_task_type_ready p (CMRTask q fid parent st ks) ann ==>
         ~cm_zero_literal parent ==>
         (!(result:cm_type).
            cm_phase_result_type p fid phase result ==>
            result == cm_expr_type parent) ==>
         cm_expr_wf p (inth fid (cm_program_functions p)) child ==>
         cm_scalar_expr_type (cm_expr_type child) ==>
         cm_phase_static_type_ready p fid phase ==>
         cm_phase_parent_type_ready p fid phase
           (cm_ann_cursors ann) ==>
         cm_phase_next_fid fid phase == fid ==>
         cm_phase_input_type_ready p fid phase
           (cm_expr_type child) ==>
         cm_phase_expr_type_ready p fid phase child ==>
         cm_task_type_ready p
           (CMRTask q fid child st (frame :: ks))
           (cm_ann_push phase (cm_ann_pc ann)
             (cm_ann_temp ann) (cm_ann_break ann)
             (cm_ann_continue ann) ann)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_task_type_ready_def())), assume_rule(
      `cm_task_type_ready (p:cm_program)
        (CMRTask (q:cm_program) (fid:int) (parent:cm_expr)
          (st:cm_src_state) (ks:(cm_frame)list))
        (ann:cm_annotation)`));
  thm same_program = cm_tc_pick_conjunct(
      opened, `(q:cm_program) == (p:cm_program)`);
  thm fid_low = cm_tc_pick_conjunct(opened, `0i <= (fid:int)`);
  thm fid_high = cm_tc_pick_conjunct(opened,
      `(fid:int) < ilength (cm_program_functions (p:cm_program))`);
  thm cursors_ready = cm_tc_pick_conjunct(opened,
      `cm_cursors_type_ready (p:cm_program) (fid:int)
        ${old_cursors:(cm_acursor)list}`);
  thm parent_values = cm_tc_pick_conjunct(opened,
      `cm_cursor_expr_values_type_ready (p:cm_program) (fid:int)
        (parent:cm_expr) ${old_cursors:(cm_acursor)list}`);
  thm next_fid = assume_rule(
      `cm_phase_next_fid (fid:int) (phase:cm_aphase) == fid`);
  thm next_rest_view = apply_conversion(rewrite_conv(THM_LIST(
      next_fid)),
      `cm_cursors_type_ready (p:cm_program)
        (cm_phase_next_fid (fid:int) (phase:cm_aphase))
        ${old_cursors:(cm_acursor)list}`);
  thm next_rest =
      eq_mp_rule(sym_rule(next_rest_view), cursors_ready);
  thm phase_result = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `phase:cm_aphase`,
      `parent:cm_expr`, old_cursors), cm_phase_result_from_expr);
  phase_result = mp_rule(phase_result, parent_values);
  phase_result = mp_rule(phase_result,
      assume_rule(`~cm_zero_literal (parent:cm_expr)`));
  phase_result = mp_rule(phase_result, assume_rule(
      `!(result:cm_type).
         cm_phase_result_type (p:cm_program) (fid:int)
           (phase:cm_aphase) result ==>
         result == cm_expr_type (parent:cm_expr)`));
  phase_result = mp_rule(phase_result, next_fid);
  thm new_cursors = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `phase:cm_aphase`,
      `cm_ann_temp (ann:cm_annotation)`, `cm_ann_break ann`,
      `cm_ann_continue ann`, old_cursors),
      cm_cursor_push_type_ready);
  new_cursors = mp_rule(new_cursors, assume_rule(
      `cm_phase_static_type_ready (p:cm_program) (fid:int)
        (phase:cm_aphase)`));
  new_cursors = mp_rule(new_cursors, assume_rule(
      `cm_phase_parent_type_ready (p:cm_program) (fid:int)
        (phase:cm_aphase) ${old_cursors:(cm_acursor)list}`));
  new_cursors = mp_rule(new_cursors, phase_result);
  new_cursors = mp_rule(new_cursors, next_rest);
  thm new_input = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `phase:cm_aphase`, child_type,
      `cm_ann_temp (ann:cm_annotation)`, `cm_ann_break ann`,
      `cm_ann_continue ann`, old_cursors),
      cm_cursor_push_input_ready), assume_rule(
        `cm_phase_input_type_ready (p:cm_program) (fid:int)
          (phase:cm_aphase) ${child_type:cm_type}`));
  thm new_values = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `phase:cm_aphase`,
      `child:cm_expr`, `cm_ann_temp (ann:cm_annotation)`,
      `cm_ann_break ann`, `cm_ann_continue ann`, old_cursors),
      cm_cursor_push_expr_values_ready), assume_rule(
        `cm_phase_expr_type_ready (p:cm_program) (fid:int)
          (phase:cm_aphase) (child:cm_expr)`));
  thm target_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
      same_program, fid_low, fid_high,
      assume_rule(
        `cm_expr_wf (p:cm_program)
          (inth (fid:int) (cm_program_functions p))
          (child:cm_expr)`),
      assume_rule(
        `cm_scalar_expr_type (cm_expr_type (child:cm_expr))`),
      new_cursors, new_input, new_values,
      get_cm_task_type_ready_def(), cm_ann_push_def,
      cm_ann_cursors_def)), goal_ccl(leaf->g));
  ACCEPT_TAC(leaf, eqt_elim_rule(target_view));
  return gnode_prove(root);
}
PROOF thm cm_r_push_task_ready =
    cm_prove_r_push_task_ready();

PROOF static thm cm_prove_r_push_task_ready_at(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (q:cm_program) (fid:int)
         (parent:cm_expr) (child:cm_expr) (st:cm_src_state)
         (ks:(cm_frame)list) (frame:cm_frame)
         (ann:cm_annotation) (phase:cm_aphase)
         (pc:int) (temp:int) (breakpc:int) (continuepc:int).
         cm_task_type_ready p (CMRTask q fid parent st ks) ann ==>
         ~cm_zero_literal parent ==>
         (!(result:cm_type).
            cm_phase_result_type p fid phase result ==>
            result == cm_expr_type parent) ==>
         cm_expr_wf p (inth fid (cm_program_functions p)) child ==>
         cm_scalar_expr_type (cm_expr_type child) ==>
         cm_phase_static_type_ready p fid phase ==>
         cm_phase_parent_type_ready p fid phase
           (cm_ann_cursors ann) ==>
         cm_phase_next_fid fid phase == fid ==>
         cm_phase_input_type_ready p fid phase
           (cm_expr_type child) ==>
         cm_phase_expr_type_ready p fid phase child ==>
         cm_task_type_ready p
           (CMRTask q fid child st (frame :: ks))
           (cm_ann_push phase pc temp breakpc continuepc ann)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm result = specl_rule(TERM_LIST(
      `p:cm_program`, `q:cm_program`, `fid:int`,
      `parent:cm_expr`, `child:cm_expr`, `st:cm_src_state`,
      `ks:(cm_frame)list`, `frame:cm_frame`,
      `ann:cm_annotation`, `phase:cm_aphase`),
      cm_r_push_task_ready);
  labeled_term_list assumptions = goal_lasmps(leaf->g);
  for (size_t i = 0; i < vector_size(assumptions); ++i) {
    result = mp_rule(result, assume_rule(assumptions[i].tm));
  }
  thm result_open = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_task_type_ready_def(), cm_ann_push_def,
      cm_ann_cursors_def)), result);
  thm target_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
      get_cm_task_type_ready_def(), cm_ann_push_def,
      cm_ann_cursors_def)), goal_ccl(leaf->g));
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), result_open));
  return gnode_prove(root);
}
PROOF thm cm_r_push_task_ready_at =
    cm_prove_r_push_task_ready_at();

PROOF static thm cm_prove_l_push_task_ready(void) {
  term old_cursors =
      `cm_ann_cursors (ann:cm_annotation)`;
  term output =
      `cm_lvalue_output_type (p:cm_program)
        (inth (fid:int) (cm_program_functions p)) (child:cm_expr)`;
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (q:cm_program) (fid:int)
         (parent:cm_expr) (child:cm_expr) (st:cm_src_state)
         (ks:(cm_frame)list) (frame:cm_frame)
         (ann:cm_annotation) (phase:cm_aphase).
         cm_task_type_ready p (CMRTask q fid parent st ks) ann ==>
         ~cm_zero_literal parent ==>
         (!(result:cm_type).
            cm_phase_result_type p fid phase result ==>
            result == cm_expr_type parent) ==>
         cm_expr_wf p (inth fid (cm_program_functions p)) child ==>
         cm_lvalue child ==>
         cm_phase_static_type_ready p fid phase ==>
         cm_phase_parent_type_ready p fid phase
           (cm_ann_cursors ann) ==>
         cm_phase_next_fid fid phase == fid ==>
         cm_phase_input_type_ready p fid phase
           (cm_lvalue_output_type p
             (inth fid (cm_program_functions p)) child) ==>
         cm_phase_lvalue_type_ready p fid phase
           (cm_lvalue_output_type p
             (inth fid (cm_program_functions p)) child) ==>
         cm_task_type_ready p
           (CMLTask q fid child st (frame :: ks))
           (cm_ann_push phase (cm_ann_pc ann)
             (cm_ann_temp ann) (cm_ann_break ann)
             (cm_ann_continue ann) ann)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_task_type_ready_def())), assume_rule(
      `cm_task_type_ready (p:cm_program)
        (CMRTask (q:cm_program) (fid:int) (parent:cm_expr)
          (st:cm_src_state) (ks:(cm_frame)list))
        (ann:cm_annotation)`));
  thm same_program = cm_tc_pick_conjunct(
      opened, `(q:cm_program) == (p:cm_program)`);
  thm fid_low = cm_tc_pick_conjunct(opened, `0i <= (fid:int)`);
  thm fid_high = cm_tc_pick_conjunct(opened,
      `(fid:int) < ilength (cm_program_functions (p:cm_program))`);
  thm cursors_ready = cm_tc_pick_conjunct(opened,
      `cm_cursors_type_ready (p:cm_program) (fid:int)
        ${old_cursors:(cm_acursor)list}`);
  thm parent_values = cm_tc_pick_conjunct(opened,
      `cm_cursor_expr_values_type_ready (p:cm_program) (fid:int)
        (parent:cm_expr) ${old_cursors:(cm_acursor)list}`);
  thm next_fid = assume_rule(
      `cm_phase_next_fid (fid:int) (phase:cm_aphase) == fid`);
  thm next_rest_view = apply_conversion(rewrite_conv(THM_LIST(
      next_fid)),
      `cm_cursors_type_ready (p:cm_program)
        (cm_phase_next_fid (fid:int) (phase:cm_aphase))
        ${old_cursors:(cm_acursor)list}`);
  thm next_rest =
      eq_mp_rule(sym_rule(next_rest_view), cursors_ready);
  thm phase_result = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `phase:cm_aphase`,
      `parent:cm_expr`, old_cursors), cm_phase_result_from_expr);
  phase_result = mp_rule(phase_result, parent_values);
  phase_result = mp_rule(phase_result,
      assume_rule(`~cm_zero_literal (parent:cm_expr)`));
  phase_result = mp_rule(phase_result, assume_rule(
      `!(result:cm_type).
         cm_phase_result_type (p:cm_program) (fid:int)
           (phase:cm_aphase) result ==>
         result == cm_expr_type (parent:cm_expr)`));
  phase_result = mp_rule(phase_result, next_fid);
  thm new_cursors = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `phase:cm_aphase`,
      `cm_ann_temp (ann:cm_annotation)`, `cm_ann_break ann`,
      `cm_ann_continue ann`, old_cursors),
      cm_cursor_push_type_ready);
  new_cursors = mp_rule(new_cursors, assume_rule(
      `cm_phase_static_type_ready (p:cm_program) (fid:int)
        (phase:cm_aphase)`));
  new_cursors = mp_rule(new_cursors, assume_rule(
      `cm_phase_parent_type_ready (p:cm_program) (fid:int)
        (phase:cm_aphase) ${old_cursors:(cm_acursor)list}`));
  new_cursors = mp_rule(new_cursors, phase_result);
  new_cursors = mp_rule(new_cursors, next_rest);
  thm new_input = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `phase:cm_aphase`, output,
      `cm_ann_temp (ann:cm_annotation)`, `cm_ann_break ann`,
      `cm_ann_continue ann`, old_cursors),
      cm_cursor_push_input_ready), assume_rule(
        `cm_phase_input_type_ready (p:cm_program) (fid:int)
          (phase:cm_aphase) ${output:cm_type}`));
  thm new_lvalue = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `phase:cm_aphase`, output,
      `cm_ann_temp (ann:cm_annotation)`, `cm_ann_break ann`,
      `cm_ann_continue ann`, old_cursors),
      cm_cursor_push_lvalue_ready), assume_rule(
        `cm_phase_lvalue_type_ready (p:cm_program) (fid:int)
          (phase:cm_aphase) ${output:cm_type}`));
  thm target_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
      same_program, fid_low, fid_high,
      assume_rule(
        `cm_expr_wf (p:cm_program)
          (inth (fid:int) (cm_program_functions p))
          (child:cm_expr)`),
      assume_rule(`cm_lvalue (child:cm_expr)`),
      new_cursors, new_input, new_lvalue,
      get_cm_task_type_ready_def(), cm_ann_push_def,
      cm_ann_cursors_def)), goal_ccl(leaf->g));
  ACCEPT_TAC(leaf, eqt_elim_rule(target_view));
  return gnode_prove(root);
}
PROOF thm cm_l_push_task_ready =
    cm_prove_l_push_task_ready();

PROOF static int cmc_preservation_type_cursor_final_checks(void) {
  ENSURE_COND(vector_size(hyp(cm_cursor_push_type_ready)) == 0 &&
      vector_size(hyp(cm_cursor_push_input_ready)) == 0 &&
      vector_size(hyp(cm_cursor_push_expr_values_ready)) == 0 &&
      vector_size(hyp(cm_cursor_push_lvalue_ready)) == 0 &&
      vector_size(hyp(cm_lvalue_cursor_expr_values)) == 0 &&
      vector_size(hyp(cm_expr_cursor_values_transport_nonzero)) == 0 &&
      vector_size(hyp(cm_expr_cursor_values_lvalue)) == 0 &&
      vector_size(hyp(cm_r_value_task_ready)) == 0 &&
      vector_size(hyp(cm_l_value_task_ready)) == 0 &&
      vector_size(hyp(cm_r_push_task_ready)) == 0 &&
      vector_size(hyp(cm_r_push_task_ready_at)) == 0 &&
      vector_size(hyp(cm_l_push_task_ready)) == 0,
      "cursor type theorem has assumptions");
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_type_cursor_axioms_before,
      "cmc_preservation_type_cursor introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_type_cursor_checks =
    cmc_preservation_type_cursor_final_checks();
