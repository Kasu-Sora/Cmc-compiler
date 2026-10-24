#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_type_phase.h"

#require "cmc_preservation_type_facts.c"

PROOF static size_t _cmc_preservation_type_phase_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_prove_convertible_pointer_target(void) {
  gnode root = gnode_new_with_ccl(
      `!(from:cm_type) (to:cm_type).
         cm_is_pointer from ==>
         cm_convertible from to ==>
         cm_is_pointer to`);
  gnode_list from_cases = INDUCT_TAC(root, `from:cm_type`);
  for (size_t i = 0; i < vector_size(from_cases); ++i) {
    gnode_list to_cases = INDUCT_TAC(from_cases[i], `to:cm_type`);
    for (size_t j = 0; j < vector_size(to_cases); ++j) {
      thm view = apply_conversion(reduce_rewrite_conv(THM_LIST(
          get_cm_convertible_def(), get_cm_is_pointer_def(),
          get_cm_is_struct_def(), get_datatype_distinctness("cm_type"),
          get_datatype_injectivity("cm_type"))),
          goal_ccl(to_cases[j]->g));
      ACCEPT_TAC(to_cases[j], eqt_elim_rule(view));
    }
  }
  return gnode_prove(root);
}
PROOF static thm cm_convertible_pointer_target =
    cm_prove_convertible_pointer_target();

PROOF static thm cm_prove_null_value_convertible(void) {
  gnode root = gnode_new_with_ccl(
      `!(ty:cm_type).
         cm_is_pointer ty ==>
         cm_value_convertible_to CMNullV ty`);
  gnode_list type_cases = INDUCT_TAC(root, `ty:cm_type`);
  for (size_t i = 0; i < vector_size(type_cases); ++i) {
    thm view = apply_conversion(reduce_rewrite_conv(THM_LIST(
        get_cm_value_convertible_to_def(), get_cm_value_type_def(),
        get_cm_convertible_def(), get_cm_is_pointer_def(),
        get_cm_is_struct_def(), get_datatype_distinctness("cm_type"),
        get_datatype_injectivity("cm_type"),
        get_datatype_distinctness("cm_value"))),
        goal_ccl(type_cases[i]->g));
    ACCEPT_TAC(type_cases[i], eqt_elim_rule(view));
  }
  return gnode_prove(root);
}
PROOF static thm cm_null_value_convertible =
    cm_prove_null_value_convertible();

PROOF static thm cm_prove_compatible_convertible(void) {
  gnode root = gnode_new_with_ccl(
      `!(v:cm_value) (from:cm_type) (to:cm_type).
         cm_value_type_compatible v from ==>
         cm_convertible from to ==>
         cm_value_convertible_to v to`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm compatible = conv_rule(rewrite_conv(THM_LIST(
      get_cm_value_type_compatible_def())), assume_rule(
      `cm_value_type_compatible (v:cm_value) (from:cm_type)`));
  dest_disj_results parts = dest_disj(concl(compatible));
  gnode_list cases = DISJ_CASES_TAC(leaf, compatible, "Hcompatible");
  {
    thm same_type = assume_rule(parts.tm1);
    thm converted = conv_rule(rewrite_conv(THM_LIST(
        sym_rule(same_type))), assume_rule(
        `cm_convertible (from:cm_type) (to:cm_type)`));
    thm target_view = apply_conversion(rewrite_conv(THM_LIST(
        get_cm_value_convertible_to_def())),
        `cm_value_convertible_to (v:cm_value) (to:cm_type)`);
    thm result = taut_rule(mk_imp(concl(converted),
        rhs_of(target_view)));
    ACCEPT_TAC(cases[0], eq_mp_rule(sym_rule(target_view),
        mp_rule(result, converted)));
  }
  {
    thm exceptional = assume_rule(parts.tm2);
    thm value_null = conjunct1_rule(exceptional);
    thm from_pointer = conjunct2_rule(exceptional);
    thm to_pointer = mp_rule(mp_rule(specl_rule(TERM_LIST(
        `from:cm_type`, `to:cm_type`), cm_convertible_pointer_target),
        from_pointer), assume_rule(
        `cm_convertible (from:cm_type) (to:cm_type)`));
    thm null_ready = mp_rule(spec_rule(
        `to:cm_type`, cm_null_value_convertible), to_pointer);
    thm result = conv_rule(rewrite_conv(THM_LIST(
        sym_rule(value_null))), null_ready);
    ACCEPT_TAC(cases[1], result);
  }
  return gnode_prove(root);
}
PROOF thm cm_compatible_convertible =
    cm_prove_compatible_convertible();

PROOF static thm cm_prove_expr_value_convertible(void) {
  gnode root = gnode_new_with_ccl(
      `!(expr:cm_expr) (v:cm_value) (ty:cm_type).
         cm_expr_value_type_ready expr v ==>
         cm_expr_convertible expr ty ==>
         cm_value_convertible_to v ty`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm value_ready = conv_rule(rewrite_conv(THM_LIST(
      get_cm_expr_value_type_ready_def())), assume_rule(
      `cm_expr_value_type_ready (expr:cm_expr) (v:cm_value)`));
  thm compatible = conjunct1_rule(value_ready);
  thm zero_value = conjunct2_rule(value_ready);
  thm convertible = conv_rule(rewrite_conv(THM_LIST(
      get_cm_expr_convertible_def())), assume_rule(
      `cm_expr_convertible (expr:cm_expr) (ty:cm_type)`));
  dest_disj_results parts = dest_disj(concl(convertible));
  gnode_list cases = DISJ_CASES_TAC(leaf, convertible, "Hconvertible");
  ACCEPT_TAC(cases[0], mp_rule(mp_rule(specl_rule(TERM_LIST(
      `v:cm_value`, `cm_expr_type (expr:cm_expr)`, `ty:cm_type`),
      cm_compatible_convertible), compatible),
      assume_rule(parts.tm1)));
  {
    thm exceptional = assume_rule(parts.tm2);
    thm target_pointer = conjunct1_rule(exceptional);
    thm zero = conjunct2_rule(exceptional);
    thm value_zero = mp_rule(zero_value, zero);
    thm target_view = apply_conversion(rewrite_conv(THM_LIST(
        get_cm_value_convertible_to_def())),
        `cm_value_convertible_to (v:cm_value) (ty:cm_type)`);
    thm result = taut_rule(imp_chain(TERM_LIST(
        concl(value_zero), concl(target_pointer)), rhs_of(target_view)));
    result = mp_rule(mp_rule(result, value_zero), target_pointer);
    ACCEPT_TAC(cases[1], eq_mp_rule(sym_rule(target_view), result));
  }
  return gnode_prove(root);
}
PROOF thm cm_expr_value_convertible =
    cm_prove_expr_value_convertible();

PROOF static thm cm_prove_integer_not_pointer(void) {
  gnode root = gnode_new_with_ccl(
      `!(ty:cm_type).
         cm_integer_type ty ==> ~cm_is_pointer ty`);
  gnode_list cases = INDUCT_TAC(root, `ty:cm_type`);
  for (size_t i = 0; i < vector_size(cases); ++i) {
    thm view = apply_conversion(reduce_rewrite_conv(THM_LIST(
        get_cm_integer_type_def(), get_cm_is_pointer_def(),
        get_datatype_distinctness("cm_type"))), goal_ccl(cases[i]->g));
    ACCEPT_TAC(cases[i], eqt_elim_rule(view));
  }
  return gnode_prove(root);
}
PROOF static thm cm_integer_not_pointer =
    cm_prove_integer_not_pointer();

PROOF static thm cm_prove_compatible_integer(void) {
  gnode root = gnode_new_with_ccl(
      `!(v:cm_value) (ty:cm_type).
         cm_value_type_compatible v ty ==>
         cm_integer_type ty ==>
         cm_integer_type (cm_value_type v)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm compatible = conv_rule(rewrite_conv(THM_LIST(
      get_cm_value_type_compatible_def())), assume_rule(
      `cm_value_type_compatible (v:cm_value) (ty:cm_type)`));
  dest_disj_results parts = dest_disj(concl(compatible));
  gnode_list cases = DISJ_CASES_TAC(leaf, compatible, "Hcompatible");
  {
    thm same = assume_rule(parts.tm1);
    thm result = conv_rule(rewrite_conv(THM_LIST(
        sym_rule(same))), assume_rule(
        `cm_integer_type (ty:cm_type)`));
    ACCEPT_TAC(cases[0], result);
  }
  {
    thm exceptional = assume_rule(parts.tm2);
    thm pointer = conjunct2_rule(exceptional);
    thm not_pointer = mp_rule(spec_rule(
        `ty:cm_type`, cm_integer_not_pointer),
        assume_rule(`cm_integer_type (ty:cm_type)`));
    CONTR_TAC(cases[1], contra(not_pointer, pointer));
  }
  return gnode_prove(root);
}
PROOF static thm cm_compatible_integer =
    cm_prove_compatible_integer();

PROOF static thm cm_prove_compatible_scalar(void) {
  gnode root = gnode_new_with_ccl(
      `!(v:cm_value) (ty:cm_type).
         cm_value_type_compatible v ty ==>
         cm_scalar_expr_type ty ==>
         cm_scalar_expr_type (cm_value_type v)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm compatible = conv_rule(rewrite_conv(THM_LIST(
      get_cm_value_type_compatible_def())), assume_rule(
      `cm_value_type_compatible (v:cm_value) (ty:cm_type)`));
  dest_disj_results parts = dest_disj(concl(compatible));
  gnode_list cases = DISJ_CASES_TAC(leaf, compatible, "Hcompatible");
  {
    thm same = assume_rule(parts.tm1);
    thm result = conv_rule(rewrite_conv(THM_LIST(
        sym_rule(same))), assume_rule(
        `cm_scalar_expr_type (ty:cm_type)`));
    ACCEPT_TAC(cases[0], result);
  }
  {
    thm exceptional = assume_rule(parts.tm2);
    thm value_null = conjunct1_rule(exceptional);
    thm null_scalar = eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          get_cm_value_type_def(), get_cm_scalar_expr_type_def(),
          get_cm_integer_type_def(), get_cm_is_pointer_def())),
        `cm_scalar_expr_type (cm_value_type CMNullV)`));
    thm result = conv_rule(rewrite_conv(THM_LIST(
        sym_rule(value_null))), null_scalar);
    ACCEPT_TAC(cases[1], result);
  }
  return gnode_prove(root);
}
PROOF static thm cm_compatible_scalar =
    cm_prove_compatible_scalar();

PROOF static thm cm_prove_phase_expr_value_ready(void) {
  gnode root = gnode_new_with_ccl(
      `!(phase:cm_aphase) (p:cm_program) (fid:int)
         (expr:cm_expr) (v:cm_value).
         cm_phase_expr_type_ready p fid phase expr ==>
         cm_expr_value_type_ready expr v ==>
         cm_phase_value_type_ready p fid phase v`);
  gnode_list cases = INDUCT_TAC(root, `phase:cm_aphase`);
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode leaf = AUTO_INTROS_TAC(cases[i]);
    labeled_term_list assumptions = goal_lasmps(leaf->g);
    thm phase_ready = assume_rule(assumptions[
        vector_size(assumptions) - 2].tm);
    thm value_ready = assume_rule(assumptions[
        vector_size(assumptions) - 1].tm);
    thm phase_open = conv_rule(reduce_rewrite_conv(THM_LIST(
        get_cm_phase_expr_type_ready_def())), phase_ready);
    thm value_open = conv_rule(reduce_rewrite_conv(THM_LIST(
        get_cm_expr_value_type_ready_def())), value_ready);
    thm compatible = conjunct1_rule(value_open);
    if (i == 3 || i == 14 || i == 20 || i == 21) {
      term target_type = dest_comb(concl(phase_open)).tm2;
      thm result = mp_rule(specl_rule(TERM_LIST(
          `expr:cm_expr`, `v:cm_value`, target_type),
          cm_expr_value_convertible), value_ready);
      result = match_mp_rule(result, phase_open);
      thm target_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
          get_cm_phase_value_type_ready_def())), goal_ccl(leaf->g));
      ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), result));
    } else if (i == 6 || i == 8 || i == 11 || i == 12) {
      thm result = mp_rule(mp_rule(specl_rule(TERM_LIST(
          `v:cm_value`, `cm_expr_type (expr:cm_expr)`),
          cm_compatible_integer), compatible), phase_open);
      thm target_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
          get_cm_phase_value_type_ready_def())), goal_ccl(leaf->g));
      ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), result));
    } else if (i == 10 || i == 13 || i == 17 || i == 18) {
      thm result = mp_rule(mp_rule(specl_rule(TERM_LIST(
          `v:cm_value`, `cm_expr_type (expr:cm_expr)`),
          cm_compatible_scalar), compatible), phase_open);
      thm target_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
          get_cm_phase_value_type_ready_def())), goal_ccl(leaf->g));
      ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), result));
    } else if (i == 15 || i == 16 || i == 19 || i == 22) {
      CONTR_TAC(leaf, phase_open);
    } else if (i == 0) {
      thm view = apply_conversion(reduce_rewrite_conv(THM_LIST(
          get_cm_phase_value_type_ready_def())), goal_ccl(leaf->g));
      ACCEPT_TAC(leaf, eqt_elim_rule(view));
    } else {
      thm result = conv_rule(rewrite_conv(THM_LIST(
          phase_open)), compatible);
      thm target_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
          get_cm_phase_value_type_ready_def())), goal_ccl(leaf->g));
      ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), result));
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_phase_expr_value_ready =
    cm_prove_phase_expr_value_ready();

PROOF static thm cm_prove_cursor_expr_value_ready(void) {
  gnode root = gnode_new_with_ccl(
      `!(cursors:(cm_acursor)list) (p:cm_program) (fid:int)
         (expr:cm_expr) (v:cm_value).
         cm_cursor_head_expr_type_ready p fid expr cursors ==>
         cm_expr_value_type_ready expr v ==>
         cm_cursor_head_value_type_ready p fid v cursors`);
  gnode_list cases = INDUCT_TAC(root, `cursors:(cm_acursor)list`);
  {
    thm view = apply_conversion(reduce_rewrite_conv(THM_LIST(
        get_cm_cursor_head_expr_type_ready_def(),
        get_cm_cursor_head_value_type_ready_def())),
        goal_ccl(cases[0]->g));
    ACCEPT_TAC(cases[0], eqt_elim_rule(view));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm phase_ready = conv_rule(reduce_rewrite_conv(THM_LIST(
        get_cm_cursor_head_expr_type_ready_def(),
        cm_cursor_phase_def)), assume_rule(
        `cm_cursor_head_expr_type_ready (p:cm_program) (fid:int)
          (expr:cm_expr)
          ((a0:cm_acursor) :: (a1:(cm_acursor)list))`));
    thm result = mp_rule(mp_rule(specl_rule(TERM_LIST(
        `cm_cursor_phase (a0:cm_acursor)`, `p:cm_program`, `fid:int`,
        `expr:cm_expr`, `v:cm_value`), cm_phase_expr_value_ready),
        phase_ready), assume_rule(
        `cm_expr_value_type_ready (expr:cm_expr) (v:cm_value)`));
    thm target_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
        get_cm_cursor_head_value_type_ready_def(),
        cm_cursor_phase_def)), goal_ccl(leaf->g));
    ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), result));
  }
  return gnode_prove(root);
}
PROOF thm cm_cursor_expr_value_ready =
    cm_prove_cursor_expr_value_ready();

PROOF static thm cm_prove_cursor_expr_rule_values(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (expr:cm_expr)
         (cursors:(cm_acursor)list).
         cm_cursor_head_expr_type_ready p fid expr cursors ==>
         cm_cursor_expr_values_type_ready p fid expr cursors`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm target_view = apply_conversion(rewrite_conv(THM_LIST(
      get_cm_cursor_expr_values_type_ready_def())), goal_ccl(leaf->g));
  thm body = mp_rule(specl_rule(TERM_LIST(
      `cursors:(cm_acursor)list`, `p:cm_program`, `fid:int`,
      `expr:cm_expr`, `v:cm_value`), cm_cursor_expr_value_ready),
      assume_rule(
        `cm_cursor_head_expr_type_ready (p:cm_program) (fid:int)
          (expr:cm_expr) (cursors:(cm_acursor)list)`));
  thm result = gen_rule(`v:cm_value`, body);
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), result));
  return gnode_prove(root);
}
PROOF thm cm_cursor_expr_rule_values =
    cm_prove_cursor_expr_rule_values();

PROOF static thm cm_prove_cursor_lvalue_value_ready(void) {
  gnode root = gnode_new_with_ccl(
      `!(cursors:(cm_acursor)list) (p:cm_program) (fid:int)
         (output:cm_type) (v:cm_value).
         cm_cursor_head_lvalue_type_ready p fid output cursors ==>
         cm_value_type_compatible v output ==>
         cm_cursor_head_value_type_ready p fid v cursors`);
  gnode_list cases = INDUCT_TAC(root, `cursors:(cm_acursor)list`);
  {
    thm view = apply_conversion(reduce_rewrite_conv(THM_LIST(
        get_cm_cursor_head_lvalue_type_ready_def(),
        get_cm_cursor_head_value_type_ready_def())),
        goal_ccl(cases[0]->g));
    ACCEPT_TAC(cases[0], eqt_elim_rule(view));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm ready = conv_rule(reduce_rewrite_conv(THM_LIST(
        get_cm_cursor_head_lvalue_type_ready_def(),
        get_cm_phase_lvalue_type_ready_def(),
        cm_cursor_phase_def)), assume_rule(
        `cm_cursor_head_lvalue_type_ready (p:cm_program) (fid:int)
          (output:cm_type)
          ((a0:cm_acursor) :: (a1:(cm_acursor)list))`));
    thm result = mp_rule(spec_rule(`v:cm_value`, ready), assume_rule(
        `cm_value_type_compatible (v:cm_value) (output:cm_type)`));
    thm target_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
        get_cm_cursor_head_value_type_ready_def(),
        cm_cursor_phase_def)), goal_ccl(leaf->g));
    ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), result));
  }
  return gnode_prove(root);
}
PROOF thm cm_cursor_lvalue_value_ready =
    cm_prove_cursor_lvalue_value_ready();
PROOF static int cmc_preservation_type_phase_final_checks(void) {
  ENSURE_COND(vector_size(hyp(cm_compatible_convertible)) == 0 &&
      vector_size(hyp(cm_expr_value_convertible)) == 0 &&
      vector_size(hyp(cm_phase_expr_value_ready)) == 0 &&
      vector_size(hyp(cm_cursor_expr_value_ready)) == 0 &&
      vector_size(hyp(cm_cursor_expr_rule_values)) == 0 &&
      vector_size(hyp(cm_cursor_lvalue_value_ready)) == 0,
      "type phase theorem has assumptions");
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_type_phase_axioms_before,
      "cmc_preservation_type_phase introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_type_phase_checks =
    cmc_preservation_type_phase_final_checks();
