#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_type_facts.h"

#require "cmc_preservation_type_ready.c"

PROOF static size_t _cmc_preservation_type_facts_axioms_before =
    vector_size(get_all_axioms());
PROOF static thm cm_type_stmt_taut_from_assumptions(const gnode node) {
  labeled_term_list assumptions = goal_lasmps(node->g);
  thm_list facts = vector_create();
  term_list premises = vector_create();
  thm target_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
      get_cm_stmt_wf_def())), goal_ccl(node->g));
  for (size_t i = 0; i < vector_size(assumptions); ++i) {
    thm raw = assume_rule(assumptions[i].tm);
    if (is_forall(concl(raw))) {
      raw = specl_rule(TERM_LIST(
          `p:cm_program`, `f:cm_function_d`, `loop:bool`), raw);
    }
    thm fact = conv_rule(reduce_rewrite_conv(THM_LIST(
        get_cm_stmt_wf_def())), raw);
    vector_add(&facts, fact);
    vector_add(&premises, concl(fact));
  }
  thm result = taut_rule(imp_chain(
      premises, rhs_of(target_view)));
  for (size_t i = 0; i < vector_size(facts); ++i) {
    result = mp_rule(result, facts[i]);
  }
  return eq_mp_rule(sym_rule(target_view), result);
}

PROOF static thm cm_prove_scalar_type_is_expr_type(void) {
  gnode root = gnode_new_with_ccl(
      `!(ty:cm_type). !(structs:(cm_struct_d)list).
         cm_scalar_type structs ty ==> cm_scalar_expr_type ty`);
  gnode_list cases = INDUCT_TAC(root, `ty:cm_type`);
  for (size_t i = 0; i < vector_size(cases); ++i) {
    thm view = apply_conversion(reduce_rewrite_conv(THM_LIST(
        get_cm_scalar_type_def(), get_cm_scalar_expr_type_def(),
        get_cm_integer_type_def(), get_cm_is_pointer_def(),
        get_cm_is_struct_def(), get_cm_type_code_wf_def(),
        get_cm_type_refs_def())), goal_ccl(cases[i]->g));
    ACCEPT_TAC(cases[i], eqt_elim_rule(view));
  }
  return gnode_prove(root);
}
PROOF thm cm_scalar_type_is_expr_type =
    cm_prove_scalar_type_is_expr_type();

PROOF static thm cm_prove_convertible_scalar_types(void) {
  gnode root = gnode_new_with_ccl(
      `!(from:cm_type). !(to:cm_type).
         cm_convertible from to ==>
         cm_scalar_expr_type from && cm_scalar_expr_type to`);
  gnode_list from_cases = INDUCT_TAC(root, `from:cm_type`);
  for (size_t i = 0; i < vector_size(from_cases); ++i) {
    gnode_list to_cases = INDUCT_TAC(from_cases[i], `to:cm_type`);
    for (size_t j = 0; j < vector_size(to_cases); ++j) {
      thm view = apply_conversion(reduce_rewrite_conv(THM_LIST(
          get_cm_convertible_def(), get_cm_scalar_expr_type_def(),
          get_cm_integer_type_def(), get_cm_is_pointer_def(),
          get_cm_is_struct_def())), goal_ccl(to_cases[j]->g));
      ACCEPT_TAC(to_cases[j], eqt_elim_rule(view));
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_convertible_scalar_types =
    cm_prove_convertible_scalar_types();

PROOF static thm cm_prove_typed_function_at(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int).
         cm_typed_program p ==>
         0i <= fid ==>
         fid < ilength (cm_program_functions p) ==>
         cm_function_wf p (inth fid (cm_program_functions p))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm opened = conv_rule(rewrite_conv(THM_LIST(
      get_cm_typed_program_def())),
      assume_rule(`cm_typed_program (p:cm_program)`));
  thm functions = conjunct1_rule(conjunct2_rule(conjunct2_rule(
      conjunct2_rule(opened))));
  thm result = mp_rule(mp_rule(spec_rule(`fid:int`, functions),
      assume_rule(`0i <= (fid:int)`)),
      assume_rule(`(fid:int) < ilength (cm_program_functions p)`));
  ACCEPT_TAC(leaf, result);
  return gnode_prove(root);
}
PROOF thm cm_typed_function_at = cm_prove_typed_function_at();

PROOF static thm cm_prove_expr_convertible_source_scalar(void) {
  gnode root = gnode_new_with_ccl(
      `!(expr:cm_expr) (ty:cm_type).
         cm_expr_convertible expr ty ==>
         cm_scalar_expr_type (cm_expr_type expr)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm opened = conv_rule(rewrite_conv(THM_LIST(
      get_cm_expr_convertible_def())),
      assume_rule(`cm_expr_convertible (expr:cm_expr) (ty:cm_type)`));
  gnode_list cases = DISJ_CASES_TAC(leaf, opened, "Hconvertible");
  {
    thm scalar_pair = match_mp_rule(specl_rule(TERM_LIST(
        `cm_expr_type (expr:cm_expr)`, `ty:cm_type`),
        cm_convertible_scalar_types), assume_rule(
          `cm_convertible (cm_expr_type (expr:cm_expr)) (ty:cm_type)`));
    ACCEPT_TAC(cases[0], conjunct1_rule(scalar_pair));
  }
  {
    labeled_term_list assumptions = goal_lasmps(cases[1]->g);
    thm zero_case = assume_rule(assumptions[
        labeled_term_list_index(assumptions, "Hconvertible")].tm);
    thm zero = conjunct2_rule(zero_case);
    thm zero_eq = conv_rule(rewrite_conv(THM_LIST(
        get_cm_zero_literal_def())), zero);
    thm const_scalar = eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          get_cm_expr_type_def(), get_cm_scalar_expr_type_def(),
          get_cm_integer_type_def(), get_cm_is_pointer_def())),
        `cm_scalar_expr_type (cm_expr_type (CMConstE 0i CMIntTy))`));
    thm congruence = beta_norm(ap_term_rule(
        `\e:cm_expr. cm_scalar_expr_type (cm_expr_type e)`, zero_eq));
    ACCEPT_TAC(cases[1],
        eq_mp_rule(sym_rule(congruence), const_scalar));
  }
  return gnode_prove(root);
}
PROOF thm cm_expr_convertible_source_scalar =
    cm_prove_expr_convertible_source_scalar();

PROOF static thm cm_prove_stmt_wf_loop_mono(void) {
  gnode root = gnode_new_with_ccl(
      `!(stmt:cm_stmt). !(p:cm_program) (f:cm_function_d) (loop:bool).
         cm_stmt_wf p f loop stmt ==> cm_stmt_wf p f T stmt`);
  gnode_list cases = INDUCT_TAC(root, `stmt:cm_stmt`);
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode constructor = AUTO_INTROS_TAC(cases[i]);
    gnode_list frontier = AUTO_ASMP_DESTRUCT_TAC(constructor);
    gnode leaf = AUTO_INTROS_TAC(frontier[0]);
    ACCEPT_TAC(leaf, cm_type_stmt_taut_from_assumptions(leaf));
  }
  return gnode_prove(root);
}
PROOF thm cm_stmt_wf_loop_mono = cm_prove_stmt_wf_loop_mono();

PROOF static thm cm_prove_args_wf_exprs(void) {
  gnode root = gnode_new_with_ccl(
      `!(args:(cm_expr)list). !(p:cm_program) (f:cm_function_d)
         (slots:(cm_slot_d)list).
         cm_args_wf p f args slots ==>
         cm_exprs_type_ready p f args`);
  gnode_list cases = INDUCT_TAC(root, `args:(cm_expr)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        get_cm_args_wf_def(), cm_exprs_type_ready_def)));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
        get_cm_args_wf_def())), assume_rule(
          `cm_args_wf (p:cm_program) (f:cm_function_d)
            ((a0:cm_expr) :: (a1:(cm_expr)list))
            (slots:(cm_slot_d)list)`));
    thm expression_wf = conjunct1_rule(conjunct2_rule(opened));
    thm convertible = conjunct1_rule(conjunct2_rule(
        conjunct2_rule(opened)));
    thm tail_wf = conjunct2_rule(conjunct2_rule(
        conjunct2_rule(opened)));
    thm scalar = match_mp_rule(specl_rule(TERM_LIST(
        `a0:cm_expr`, `cm_slot_ty (HD (slots:(cm_slot_d)list))`),
        cm_expr_convertible_source_scalar), convertible);
    thm ih = specl_rule(TERM_LIST(`p:cm_program`, `f:cm_function_d`,
        `TL (slots:(cm_slot_d)list)`),
        assume_rule(goal_lasmps(leaf->g)[0].tm));
    thm tail_ready = match_mp_rule(ih, tail_wf);
    thm ready = conj_rule(expression_wf,
        conj_rule(scalar, tail_ready));
    thm view = apply_conversion(rewrite_conv(THM_LIST(
        cm_exprs_type_ready_def)), goal_ccl(leaf->g));
    ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(view), ready));
  }
  return gnode_prove(root);
}
PROOF thm cm_args_wf_exprs = cm_prove_args_wf_exprs();

PROOF static thm cm_prove_value_type_compatible_refl(void) {
  gnode root = gnode_new_with_ccl(
      `!(v:cm_value).
         cm_value_type_compatible v (cm_value_type v)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
      cm_value_type_compatible_def)));
  return gnode_prove(root);
}
PROOF thm cm_value_type_compatible_refl =
    cm_prove_value_type_compatible_refl();

PROOF static thm cm_prove_pointer_value_view(void) {
  gnode root = gnode_new_with_ccl(
      `!(v:cm_value) (ty:cm_type) (st:cm_src_state).
         cm_value_type_compatible v (CMPtrTy ty) ==>
         cm_pointer_live st v ==>
         cm_ptr_view v == ty`);
  gnode_list cases = INDUCT_TAC(root, `v:cm_value`);
  for (size_t i = 0; i < vector_size(cases); ++i) {
    thm view = apply_conversion(reduce_rewrite_conv(THM_LIST(
        cm_value_type_compatible_def, get_cm_value_type_def(),
        get_cm_pointer_live_def(), get_cm_ptr_gen_def(),
        get_cm_ptr_view_def(), get_cm_is_pointer_def(),
        get_datatype_distinctness("cm_type"),
        get_datatype_injectivity("cm_type"),
        get_datatype_distinctness("cm_value"))),
        goal_ccl(cases[i]->g));
    thm normalized = taut_rule(rhs_of(view));
    ACCEPT_TAC(cases[i], eq_mp_rule(sym_rule(view), normalized));
  }
  return gnode_prove(root);
}
PROOF thm cm_pointer_value_view = cm_prove_pointer_value_view();

PROOF static thm cm_prove_referenced_type_size_signed(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (ty:cm_type).
         cm_typed_program p ==>
         cm_type_refs (cm_program_structs p) ty ==>
         tower_signed64 (cm_type_size (cm_program_structs p) ty)`);
  gnode_list cases = INDUCT_TAC(root, `ty:cm_type`);
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode leaf = AUTO_INTROS_TAC(cases[i]);
    if (i != 2) {
      CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
          get_cm_type_size_def(), get_tower_signed64_def())));
      continue;
    }
    thm refs = conv_rule(reduce_rewrite_conv(THM_LIST(
        get_cm_type_refs_def())), assume_rule(
          `cm_type_refs (cm_program_structs (p:cm_program))
            (CMStructTy (a:int))`));
    thm sid_nonnegative = conjunct1_rule(refs);
    thm sid_upper = conjunct2_rule(refs);
    thm typed_open = conv_rule(rewrite_conv(THM_LIST(
        get_cm_typed_program_def())), assume_rule(
          `cm_typed_program (p:cm_program)`));
    thm struct_wf = match_mp_rule(match_mp_rule(
        spec_rule(`a:int`, conjunct1_rule(typed_open)),
        sid_nonnegative), sid_upper);
    thm struct_open = conv_rule(rewrite_conv(THM_LIST(
        get_cm_struct_wf_def())), struct_wf);
    thm size_positive = conjunct1_rule(conjunct2_rule(
        conjunct2_rule(struct_open)));
    thm size_upper = conjunct2_rule(conjunct2_rule(
        conjunct2_rule(struct_open)));
    term size = `cm_struct_slots_size
        (cm_struct_members
          (inth (a:int) (cm_program_structs (p:cm_program))))`;
    thm raw_bounds = mp_rule(int_arith_rule(mk_imp(
        list_mk_conj(TERM_LIST(concl(size_positive), concl(size_upper))),
        `--9223372036854775808i <= ${size:int} &&
         ${size:int} <= 9223372036854775807i`)),
        conj_rule(size_positive, size_upper));
    thm size_view = apply_conversion(rewrite_conv(THM_LIST(
        get_tower_signed64_def())), `tower_signed64 ${size:int}`);
    thm size_is_signed = eq_mp_rule(sym_rule(size_view), raw_bounds);
    thm_list normalize = THM_LIST(
        get_cm_type_size_def(), get_cm_struct_size_def(),
        sid_nonnegative, sid_upper);
    thm normalized = conv_rule(reduce_rewrite_conv(normalize),
        size_is_signed);
    thm target_view = apply_conversion(
        reduce_rewrite_conv(normalize), goal_ccl(leaf->g));
    ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), normalized));
  }
  return gnode_prove(root);
}
PROOF thm cm_referenced_type_size_signed =
    cm_prove_referenced_type_size_signed();

PROOF thm get_cm_referenced_type_size_signed(void) {
  return cm_referenced_type_size_signed;
}

PROOF static int cmc_preservation_type_facts_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_type_facts_axioms_before,
      "cmc_preservation_type_facts introduced an axiom");
  ENSURE_COND(vector_size(hyp(cm_scalar_type_is_expr_type)) == 0,
      "scalar type theorem is not closed");
  ENSURE_COND(vector_size(hyp(cm_convertible_scalar_types)) == 0,
      "convertible type theorem is not closed");
  ENSURE_COND(vector_size(hyp(cm_typed_function_at)) == 0,
      "typed function theorem is not closed");
  ENSURE_COND(vector_size(hyp(cm_stmt_wf_loop_mono)) == 0,
      "statement loop theorem is not closed");
  ENSURE_COND(vector_size(hyp(cm_args_wf_exprs)) == 0,
      "argument expression theorem is not closed");
  ENSURE_COND(vector_size(hyp(cm_pointer_value_view)) == 0,
      "pointer view theorem is not closed");
  ENSURE_COND(vector_size(hyp(cm_referenced_type_size_signed)) == 0,
      "referenced type-size theorem is not closed");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_type_facts_checks =
    cmc_preservation_type_facts_final_checks();
