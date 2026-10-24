#include "proof/proof.h"
#include "userlib/renderers.h"
#include "cmc_temp_algebra.h"
#include "cmc_preservation_budget_arith.h"
#require "cmc_temp_algebra.c"
#include "userlib/proof.h"

PROOF static size_t _cmc_preservation_budget_arith_axioms_before =
    vector_size(get_all_axioms());

PROOF static void cm_budget_arith_close(const gnode node) {
  if (!IS_NULL(node->solved)) return;
  if (is_conj(goal_ccl(node->g))) {
    gnode_list parts = CONJ_TAC(node);
    cm_budget_arith_close(parts[0]);
    cm_budget_arith_close(parts[1]);
    return;
  }
  labeled_term_list assumptions = goal_lasmps(node->g);
  thm facts = assume_rule(assumptions[0].tm);
  for (size_t i = 1; i < vector_size(assumptions); ++i) {
    facts = conj_rule(facts, assume_rule(assumptions[i].tm));
  }
  ACCEPT_TAC(node, mp_rule(int_arith_rule(
      mk_imp(concl(facts), goal_ccl(node->g))), facts));
}
PROOF static gnode cm_budget_add_normalized(
    const gnode node, term source, thm equation) {
  return ASSUME_TAC(node, conv_rule(
      rewrite_conv(THM_LIST(equation)), assume_rule(source)), NULL);
}
PROOF static thm cm_budget_not_intro(
    term proposition, thm contradiction) {
  thm implication = disch_rule(proposition, contradiction);
  thm not_as_imp = beta_rule(ap_thm_rule(
      get_theorem_by_name("NOT_DEF"), proposition));
  return eq_mp_rule(sym_rule(not_as_imp), implication);
}



PROOF static thm cm_prove_r_assign_budget_parts(void) {
  gnode root = gnode_new_with_ccl(
      `!(base:int) (limit:int) (dst:cm_expr) (src:cm_expr)
          (ty:cm_type).
         base + cm_rtemps (CMAssignE dst src ty) <= limit ==>
         base + cm_ltemps dst <= limit &&
         base + 1i + cm_rtemps src <= limit`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm measure = by_rewrite(
      `cm_rtemps
         (CMAssignE (dst:cm_expr) (src:cm_expr) (ty:cm_type)) ==
       cm_imax (cm_ltemps dst) (1i + cm_rtemps src)`,
      THM_LIST(get_cm_ltemps_def(), get_cm_rtemps_def(),
        get_cm_expr_tpair_def(), get_cm_tleft_def(),
        get_cm_tright_def()));
  leaf = cm_budget_add_normalized(leaf,
      `(base:int) +
         cm_rtemps
           (CMAssignE (dst:cm_expr) (src:cm_expr) (ty:cm_type)) <=
       (limit:int)`,
      measure);
  leaf = ASSUME_TAC(leaf, specl_rule(TERM_LIST(
      `cm_ltemps (dst:cm_expr)`,
      `1i + cm_rtemps (src:cm_expr)`), cm_imax_left_bound), NULL);
  leaf = ASSUME_TAC(leaf, specl_rule(TERM_LIST(
      `cm_ltemps (dst:cm_expr)`,
      `1i + cm_rtemps (src:cm_expr)`), cm_imax_right_bound), NULL);
  gnode reduced = CONV_WITH_ASMP_TAC(
      leaf, reduce_rewrite_conv, THM_LIST(measure));
  cm_budget_arith_close(reduced);
  return gnode_prove(root);
}
PROOF thm cm_r_assign_budget_parts =
    cm_prove_r_assign_budget_parts();

PROOF static thm cm_prove_r_binary_budget_parts(void) {
  gnode root = gnode_new_with_ccl(
      `!(base:int) (limit:int) (op:int) (left:cm_expr)
          (right:cm_expr) (ty:cm_type).
         base + cm_rtemps (CMBinaryE op left right ty) <= limit ==>
         base + cm_rtemps left <= limit &&
         base +
           (if op == 0i || op == 1i
            then cm_rtemps right
            else 1i + cm_rtemps right) <= limit`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm measure = by_rewrite(
      `cm_rtemps
         (CMBinaryE (op:int) (left:cm_expr) (right:cm_expr)
           (ty:cm_type)) ==
       (if op == 0i || op == 1i
        then cm_imax (cm_rtemps left) (cm_rtemps right)
        else cm_imax (cm_rtemps left) (1i + cm_rtemps right))`,
      THM_LIST(get_cm_rtemps_def(), get_cm_expr_tpair_def(),
        get_cm_tright_def()));
  gnode_list zero_cases = BOOL_CASES_TAC(
      leaf, `(op:int) == 0i`, "Hzero_budget");
  gnode_list one_cases = BOOL_CASES_TAC(
      zero_cases[1], `(op:int) == 1i`, "Hone_budget");
  gnode_list cases = LIST_GNODE(
      zero_cases[0], one_cases[0], one_cases[1]);
  for (size_t i = 0; i < vector_size(cases); ++i) {
    term logical_term = `(op:int) == 0i || op == 1i`;
    thm logical;
    if (i == 0) {
      logical = disj1_rule(
          assume_rule(`(op:int) == 0i`), `(op:int) == 1i`);
    } else if (i == 1) {
      logical = disj2_rule(
          `(op:int) == 0i`, assume_rule(`(op:int) == 1i`));
    } else {
      thm assumed = assume_rule(logical_term);
      dest_disj_results parts = dest_disj(concl(assumed));
      thm left_false = not_elim_rule(
          assume_rule(`~((op:int) == 0i)`),
          assume_rule(parts.tm1));
      thm right_false = not_elim_rule(
          assume_rule(`~((op:int) == 1i)`),
          assume_rule(parts.tm2));
      logical = cm_budget_not_intro(logical_term,
          disj_cases_rule(assumed, left_false, right_false));
    }
    thm condition = i < 2
        ? eqt_intro_rule(logical)
        : eqf_intro_rule(logical);
    term right_need = i < 2
        ? `cm_rtemps (right:cm_expr)`
        : `1i + cm_rtemps (right:cm_expr)`;
    gnode branch = ASSUME_TAC(cases[i], conv_rule(
        reduce_rewrite_conv(THM_LIST(measure, condition)),
        assume_rule(
          `(base:int) +
             cm_rtemps
               (CMBinaryE (op:int) (left:cm_expr) (right:cm_expr)
                 (ty:cm_type)) <=
           (limit:int)`)), NULL);
    branch = ASSUME_TAC(branch, specl_rule(TERM_LIST(
        `cm_rtemps (left:cm_expr)`, right_need),
        cm_imax_left_bound), NULL);
    branch = ASSUME_TAC(branch, specl_rule(TERM_LIST(
        `cm_rtemps (left:cm_expr)`, right_need),
        cm_imax_right_bound), NULL);
    gnode reduced = CONV_WITH_ASMP_TAC(
        branch, reduce_rewrite_conv, THM_LIST(condition));
    cm_budget_arith_close(reduced);
  }
  return gnode_prove(root);
}
PROOF thm cm_r_binary_budget_parts =
    cm_prove_r_binary_budget_parts();

PROOF static thm cm_prove_r_unary_budget_part(void) {
  gnode root = gnode_new_with_ccl(
      `!(base:int) (limit:int) (op:int) (arg:cm_expr)
          (ty:cm_type).
         base + cm_rtemps (CMUnaryE op arg ty) <= limit ==>
         (if op == 3i
          then base + cm_ltemps arg <= limit
          else base + cm_rtemps arg <= limit)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list deref_cases = BOOL_CASES_TAC(
      leaf, `(op:int) == 2i`, "Hderef_budget");
  gnode_list address_cases = BOOL_CASES_TAC(
      deref_cases[1], `(op:int) == 3i`, "Haddress_budget");
  gnode_list cases = LIST_GNODE(
      deref_cases[0], address_cases[0], address_cases[1]);
  for (size_t i = 0; i < vector_size(cases); ++i) {
    thm deref_condition;
    thm address_condition;
    if (i == 0) {
      deref_condition = assume_rule(`(op:int) == 2i`);
      thm address_false = int_arith_rule(
          `((op:int) == 2i) ==> ~((op:int) == 3i)`);
      address_condition = eqf_intro_rule(mp_rule(
          address_false, deref_condition));
    } else if (i == 1) {
      deref_condition = eqf_intro_rule(
          assume_rule(`~((op:int) == 2i)`));
      address_condition = assume_rule(`(op:int) == 3i`);
    } else {
      deref_condition = eqf_intro_rule(
          assume_rule(`~((op:int) == 2i)`));
      address_condition = eqf_intro_rule(
          assume_rule(`~((op:int) == 3i)`));
    }
    term needed = i == 1
        ? `cm_ltemps (arg:cm_expr)`
        : `cm_rtemps (arg:cm_expr)`;
    thm measure = by_rewrite(
        mk_eq(
          `cm_rtemps
             (CMUnaryE (op:int) (arg:cm_expr) (ty:cm_type))`,
          needed),
        THM_LIST(deref_condition, address_condition,
          get_cm_ltemps_def(), get_cm_rtemps_def(),
          get_cm_expr_tpair_def(), get_cm_tleft_def(),
          get_cm_tright_def()));
    gnode branch = ASSUME_TAC(cases[i], conv_rule(
        reduce_rewrite_conv(THM_LIST(measure)),
        assume_rule(
          `(base:int) +
             cm_rtemps
               (CMUnaryE (op:int) (arg:cm_expr) (ty:cm_type)) <=
           (limit:int)`)), NULL);
    gnode reduced = CONV_WITH_ASMP_TAC(
        branch, reduce_rewrite_conv,
        THM_LIST(deref_condition, address_condition));
    cm_budget_arith_close(reduced);
  }
  return gnode_prove(root);
}
PROOF thm cm_r_unary_budget_part =
    cm_prove_r_unary_budget_part();

PROOF static thm cm_prove_l_index_budget_parts(void) {
  gnode root = gnode_new_with_ccl(
      `!(base_slot:int) (limit:int) (base:cm_expr)
          (index:cm_expr) (ty:cm_type).
         base_slot + cm_ltemps (CMIndexE base index ty) <= limit ==>
         base_slot + cm_rtemps base <= limit &&
         base_slot + 1i + cm_rtemps index <= limit`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm measure = by_rewrite(
      `cm_ltemps
         (CMIndexE (base:cm_expr) (index:cm_expr) (ty:cm_type)) ==
       cm_imax (cm_rtemps base) (1i + cm_rtemps index)`,
      THM_LIST(get_cm_ltemps_def(), get_cm_rtemps_def(),
        get_cm_expr_tpair_def(), get_cm_tleft_def(),
        get_cm_tright_def()));
  leaf = cm_budget_add_normalized(leaf,
      `(base_slot:int) +
         cm_ltemps
           (CMIndexE (base:cm_expr) (index:cm_expr) (ty:cm_type)) <=
       (limit:int)`,
      measure);
  leaf = ASSUME_TAC(leaf, specl_rule(TERM_LIST(
      `cm_rtemps (base:cm_expr)`,
      `1i + cm_rtemps (index:cm_expr)`), cm_imax_left_bound), NULL);
  leaf = ASSUME_TAC(leaf, specl_rule(TERM_LIST(
      `cm_rtemps (base:cm_expr)`,
      `1i + cm_rtemps (index:cm_expr)`), cm_imax_right_bound), NULL);
  gnode reduced = CONV_WITH_ASMP_TAC(
      leaf, reduce_rewrite_conv, THM_LIST(measure));
  cm_budget_arith_close(reduced);
  return gnode_prove(root);
}
PROOF thm cm_l_index_budget_parts =
    cm_prove_l_index_budget_parts();

PROOF static thm cm_prove_r_index_budget_parts(void) {
  gnode root = gnode_new_with_ccl(
      `!(base_slot:int) (limit:int) (base:cm_expr)
          (index:cm_expr) (ty:cm_type).
         base_slot + cm_rtemps (CMIndexE base index ty) <= limit ==>
         base_slot + cm_rtemps base <= limit &&
         base_slot + 1i + cm_rtemps index <= limit`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm result = specl_rule(TERM_LIST(
      `base_slot:int`, `limit:int`, `base:cm_expr`,
      `index:cm_expr`, `ty:cm_type`), cm_l_index_budget_parts);
  thm same_measure = by_rewrite(
      `cm_rtemps
         (CMIndexE (base:cm_expr) (index:cm_expr) (ty:cm_type)) ==
       cm_ltemps (CMIndexE base index ty)`,
      THM_LIST(get_cm_ltemps_def(), get_cm_rtemps_def(),
        get_cm_expr_tpair_def(), get_cm_tleft_def(),
        get_cm_tright_def()));
  thm premise = conv_rule(rewrite_conv(THM_LIST(same_measure)),
      assume_rule(
        `(base_slot:int) +
         cm_rtemps (CMIndexE (base:cm_expr) (index:cm_expr)
           (ty:cm_type)) <= (limit:int)`));
  result = match_mp_rule(result, premise);
  ACCEPT_TAC(leaf, result);
  return gnode_prove(root);
}
PROOF thm cm_r_index_budget_parts =
    cm_prove_r_index_budget_parts();

PROOF static thm cm_prove_l_member_budget_part(void) {
  gnode root = gnode_new_with_ccl(
      `!(base_slot:int) (limit:int) (base:cm_expr)
          (mid:int) (ty:cm_type).
         base_slot + cm_ltemps (CMMemberE base mid ty) <= limit ==>
         base_slot + cm_rtemps base <= limit`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm measure = by_rewrite(
      `cm_ltemps
         (CMMemberE (base:cm_expr) (mid:int) (ty:cm_type)) ==
       cm_rtemps base`,
      THM_LIST(get_cm_ltemps_def(), get_cm_rtemps_def(),
        get_cm_expr_tpair_def(), get_cm_tleft_def(),
        get_cm_tright_def()));
  leaf = cm_budget_add_normalized(leaf,
      `(base_slot:int) +
         cm_ltemps
           (CMMemberE (base:cm_expr) (mid:int) (ty:cm_type)) <=
       (limit:int)`,
      measure);
  CONV_WITH_ASMP_TAC(
      leaf, reduce_rewrite_conv, THM_LIST(measure));
  return gnode_prove(root);
}
PROOF thm cm_l_member_budget_part =
    cm_prove_l_member_budget_part();

PROOF static thm cm_prove_s_seq_budget_parts(void) {
  gnode root = gnode_new_with_ccl(
      `!(base:int) (limit:int) (first:cm_stmt) (second:cm_stmt).
         base + cm_stemps (CMSeqS first second) <= limit ==>
         base + cm_stemps first <= limit &&
         base + cm_stemps second <= limit`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm measure = by_rewrite(
      `cm_stemps (CMSeqS (first:cm_stmt) (second:cm_stmt)) ==
       cm_imax (cm_stemps first) (cm_stemps second)`,
      THM_LIST(get_cm_stemps_def()));
  leaf = cm_budget_add_normalized(leaf,
      `(base:int) +
         cm_stemps (CMSeqS (first:cm_stmt) (second:cm_stmt)) <=
       (limit:int)`,
      measure);
  leaf = ASSUME_TAC(leaf, specl_rule(TERM_LIST(
      `cm_stemps (first:cm_stmt)`, `cm_stemps (second:cm_stmt)`),
      cm_imax_left_bound), NULL);
  leaf = ASSUME_TAC(leaf, specl_rule(TERM_LIST(
      `cm_stemps (first:cm_stmt)`, `cm_stemps (second:cm_stmt)`),
      cm_imax_right_bound), NULL);
  gnode reduced = CONV_WITH_ASMP_TAC(
      leaf, reduce_rewrite_conv, THM_LIST(measure));
  cm_budget_arith_close(reduced);
  return gnode_prove(root);
}
PROOF thm cm_s_seq_budget_parts =
    cm_prove_s_seq_budget_parts();

PROOF static thm cm_prove_s_if_budget_parts(void) {
  gnode root = gnode_new_with_ccl(
      `!(base:int) (limit:int) (guard:cm_expr)
          (yes:cm_stmt) (no:cm_stmt).
         base + cm_stemps (CMIfS guard yes no) <= limit ==>
         base + cm_rtemps guard <= limit &&
         base + cm_stemps yes <= limit &&
         base + cm_stemps no <= limit`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm measure = by_rewrite(
      `cm_stemps
         (CMIfS (guard:cm_expr) (yes:cm_stmt) (no:cm_stmt)) ==
       cm_imax (cm_rtemps guard)
         (cm_imax (cm_stemps yes) (cm_stemps no))`,
      THM_LIST(get_cm_stemps_def()));
  leaf = cm_budget_add_normalized(leaf,
      `(base:int) +
         cm_stemps
           (CMIfS (guard:cm_expr) (yes:cm_stmt) (no:cm_stmt)) <=
       (limit:int)`,
      measure);
  term branches = `cm_imax (cm_stemps (yes:cm_stmt))
      (cm_stemps (no:cm_stmt))`;
  leaf = ASSUME_TAC(leaf, specl_rule(TERM_LIST(
      `cm_rtemps (guard:cm_expr)`, branches),
      cm_imax_left_bound), NULL);
  leaf = ASSUME_TAC(leaf, specl_rule(TERM_LIST(
      `cm_rtemps (guard:cm_expr)`, branches),
      cm_imax_right_bound), NULL);
  leaf = ASSUME_TAC(leaf, specl_rule(TERM_LIST(
      `cm_stemps (yes:cm_stmt)`, `cm_stemps (no:cm_stmt)`),
      cm_imax_left_bound), NULL);
  leaf = ASSUME_TAC(leaf, specl_rule(TERM_LIST(
      `cm_stemps (yes:cm_stmt)`, `cm_stemps (no:cm_stmt)`),
      cm_imax_right_bound), NULL);
  gnode reduced = CONV_WITH_ASMP_TAC(
      leaf, reduce_rewrite_conv, THM_LIST(measure));
  cm_budget_arith_close(reduced);
  return gnode_prove(root);
}
PROOF thm cm_s_if_budget_parts =
    cm_prove_s_if_budget_parts();

PROOF static thm cm_prove_s_while_budget_parts(void) {
  gnode root = gnode_new_with_ccl(
      `!(base:int) (limit:int) (guard:cm_expr) (body:cm_stmt).
         base + cm_stemps (CMWhileS guard body) <= limit ==>
         base + cm_rtemps guard <= limit &&
         base + cm_stemps body <= limit`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm measure = by_rewrite(
      `cm_stemps
         (CMWhileS (guard:cm_expr) (body:cm_stmt)) ==
       cm_imax (cm_rtemps guard) (cm_stemps body)`,
      THM_LIST(get_cm_stemps_def()));
  leaf = cm_budget_add_normalized(leaf,
      `(base:int) +
         cm_stemps
           (CMWhileS (guard:cm_expr) (body:cm_stmt)) <=
       (limit:int)`,
      measure);
  leaf = ASSUME_TAC(leaf, specl_rule(TERM_LIST(
      `cm_rtemps (guard:cm_expr)`, `cm_stemps (body:cm_stmt)`),
      cm_imax_left_bound), NULL);
  leaf = ASSUME_TAC(leaf, specl_rule(TERM_LIST(
      `cm_rtemps (guard:cm_expr)`, `cm_stemps (body:cm_stmt)`),
      cm_imax_right_bound), NULL);
  gnode reduced = CONV_WITH_ASMP_TAC(
      leaf, reduce_rewrite_conv, THM_LIST(measure));
  cm_budget_arith_close(reduced);
  return gnode_prove(root);
}
PROOF thm cm_s_while_budget_parts =
    cm_prove_s_while_budget_parts();

PROOF static thm cm_prove_r_call_budget_parts(void) {
  gnode root = gnode_new_with_ccl(
      `!(base:int) (limit:int) (callee:int) (arg:cm_expr)
          (rest:(cm_expr)list) (ty:cm_type).
         base +
           cm_rtemps (CMCallE callee (arg :: rest) ty) <= limit ==>
         base < limit &&
         base + ilength (arg :: rest) + cm_rtemps arg <= limit &&
         base + ilength (arg :: rest) +
           cm_adepth (cm_args_apair rest) <= limit`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm measure = by_rewrite(
      `cm_rtemps
         (CMCallE (callee:int)
           ((arg:cm_expr) :: (rest:(cm_expr)list)) (ty:cm_type)) ==
       ilength (arg :: rest) +
         cm_adepth (cm_args_apair (arg :: rest))`,
      THM_LIST(get_cm_rtemps_def(), get_cm_expr_tpair_def(),
        get_cm_tright_def(), cm_args_count_matches_length));
  leaf = cm_budget_add_normalized(leaf,
      `(base:int) +
         cm_rtemps
           (CMCallE (callee:int)
             ((arg:cm_expr) :: (rest:(cm_expr)list)) (ty:cm_type)) <=
       (limit:int)`,
      measure);
  leaf = ASSUME_TAC(leaf, specl_rule(TERM_LIST(
      `arg:cm_expr`, `rest:(cm_expr)list`),
      cm_adepth_head_bound), NULL);
  leaf = ASSUME_TAC(leaf, specl_rule(TERM_LIST(
      `arg:cm_expr`, `rest:(cm_expr)list`),
      cm_adepth_tail_bound), NULL);
  leaf = ASSUME_TAC(leaf, spec_rule(
      `(arg:cm_expr) :: (rest:(cm_expr)list)`,
      cm_adepth_nonnegative), NULL);
  leaf = ASSUME_TAC(leaf, ispec_rule(
      `rest:(cm_expr)list`,
      get_theorem_by_name("ILENGTH_NONNEG")), NULL);
  leaf = ASSUME_TAC(leaf, apply_conversion(
      rewrite_conv(THM_LIST(get_theorem_by_name("ILENGTH_DEF"))),
      `ilength ((arg:cm_expr) :: (rest:(cm_expr)list))`), NULL);
  gnode reduced = CONV_WITH_ASMP_TAC(
      leaf, reduce_rewrite_conv,
      THM_LIST(measure, get_theorem_by_name("ILENGTH_DEF")));
  cm_budget_arith_close(reduced);
  return gnode_prove(root);
}
PROOF thm cm_r_call_budget_parts =
    cm_prove_r_call_budget_parts();

PROOF static thm cm_prove_arg_budget_tail_parts(void) {
  gnode root = gnode_new_with_ccl(
      `!(current:int) (scratch:int) (limit:int) (arg:cm_expr)
          (rest:(cm_expr)list).
         current + 1i + ilength (arg :: rest) == scratch ==>
         scratch + cm_adepth (cm_args_apair (arg :: rest)) <= limit ==>
         scratch + cm_rtemps arg <= limit &&
         current + 1i < limit &&
         (current + 1i) + 1i + ilength rest == scratch &&
         scratch + cm_adepth (cm_args_apair rest) <= limit`);
  gnode leaf = AUTO_INTROS_TAC(root);
  leaf = ASSUME_TAC(leaf, specl_rule(TERM_LIST(
      `arg:cm_expr`, `rest:(cm_expr)list`),
      cm_adepth_head_bound), NULL);
  leaf = ASSUME_TAC(leaf, specl_rule(TERM_LIST(
      `arg:cm_expr`, `rest:(cm_expr)list`),
      cm_adepth_tail_bound), NULL);
  leaf = ASSUME_TAC(leaf, spec_rule(
      `(arg:cm_expr) :: (rest:(cm_expr)list)`,
      cm_adepth_nonnegative), NULL);
  leaf = ASSUME_TAC(leaf, ispec_rule(
      `rest:(cm_expr)list`,
      get_theorem_by_name("ILENGTH_NONNEG")), NULL);
  thm length_step = get_theorem_by_name("ILENGTH_DEF");
  leaf = ASSUME_TAC(leaf, conv_rule(
      rewrite_conv(THM_LIST(length_step)),
      assume_rule(
        `(current:int) + 1i +
           ilength ((arg:cm_expr) :: (rest:(cm_expr)list)) ==
         (scratch:int)`)), NULL);
  gnode reduced = CONV_WITH_ASMP_TAC(
      leaf, reduce_rewrite_conv, THM_LIST(length_step));
  cm_budget_arith_close(reduced);
  return gnode_prove(root);
}
PROOF thm cm_arg_budget_tail_parts =
    cm_prove_arg_budget_tail_parts();

PROOF static int cmc_preservation_budget_arith_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_budget_arith_axioms_before,
      "cmc_preservation_budget_arith introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_budget_arith_checks =
    cmc_preservation_budget_arith_final_checks();
