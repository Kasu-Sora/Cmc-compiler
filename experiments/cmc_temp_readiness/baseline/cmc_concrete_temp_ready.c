#include "cmc_concrete_temp_ready.h"
#require "cmc_concrete_counts.c"

PROOF static size_t _cmc_temp_ready_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_prove_imax_upper(void) {
  gnode root = gnode_new_with_ccl(
      `!(x:int) y z. cm_imax x y <= z <=> x <= z && y <= z`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list cases = BOOL_CASES_TAC(leaf, `(x:int) <= (y:int)`, "Hxy");
  {
    thm le = assume_rule(`(x:int) <= (y:int)`);
    thm maximum = mp_rule(specl_rule(TERM_LIST(
        `x:int`, `y:int`), cmc_imax_le_case()), le);
    thm facts = conj_rule(le, maximum);
    ACCEPT_TAC(cases[0], mp_rule(int_arith_rule(
        mk_imp(concl(facts), goal_ccl(cases[0]->g))), facts));
  }
  {
    thm nle = assume_rule(`~((x:int) <= (y:int))`);
    thm gt = mp_rule(int_arith_rule(
        `~((x:int) <= (y:int)) ==> x > y`), nle);
    thm maximum = mp_rule(specl_rule(TERM_LIST(
        `x:int`, `y:int`), cmc_imax_gt_case()), gt);
    thm facts = conj_rule(nle, maximum);
    ACCEPT_TAC(cases[1], mp_rule(int_arith_rule(
        mk_imp(concl(facts), goal_ccl(cases[1]->g))), facts));
  }
  return gnode_prove(root);
}
PROOF static thm cm_temp_imax_upper = cm_prove_imax_upper();

PROOF static thm cm_prove_imax_add_upper(void) {
  gnode root = gnode_new_with_ccl(
      `!(base:int) x y z.
         base + cm_imax x y <= z <=>
         base + x <= z && base + y <= z`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list cases = BOOL_CASES_TAC(leaf, `(x:int) <= (y:int)`, "Hxy");
  {
    thm le = assume_rule(`(x:int) <= (y:int)`);
    thm maximum = mp_rule(specl_rule(TERM_LIST(
        `x:int`, `y:int`), cmc_imax_le_case()), le);
    thm facts = conj_rule(le, maximum);
    ACCEPT_TAC(cases[0], mp_rule(int_arith_rule(
        mk_imp(concl(facts), goal_ccl(cases[0]->g))), facts));
  }
  {
    thm nle = assume_rule(`~((x:int) <= (y:int))`);
    thm gt = mp_rule(int_arith_rule(
        `~((x:int) <= (y:int)) ==> x > y`), nle);
    thm maximum = mp_rule(specl_rule(TERM_LIST(
        `x:int`, `y:int`), cmc_imax_gt_case()), gt);
    thm facts = conj_rule(nle, maximum);
    ACCEPT_TAC(cases[1], mp_rule(int_arith_rule(
        mk_imp(concl(facts), goal_ccl(cases[1]->g))), facts));
  }
  return gnode_prove(root);
}
PROOF static thm cm_temp_imax_add_upper =
    cm_prove_imax_add_upper();

PROOF static thm cm_prove_binary_tail_positive(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (op:int) (left:cm_expr) (right:cm_expr).
         1i <= cm_binary_tail_count p op left right`);
  gnode leaf = AUTO_INTROS_TAC(root);
  term first_choice =
      `(op:int) == 8i && cm_is_pointer (cm_expr_type (right:cm_expr))`;
  gnode_list first = BOOL_CASES_TAC(leaf, first_choice, "Htail_first");
  CONV_WITH_ASMP_TAC(first[0], reduce_rewrite_conv, THM_LIST(
      get_cm_binary_tail_count_def()));

  term second_choice =
      `(op:int) == 8i && cm_is_pointer (cm_expr_type (left:cm_expr))`;
  gnode_list second = BOOL_CASES_TAC(
      first[1], second_choice, "Htail_second");
  CONV_WITH_ASMP_TAC(second[0], reduce_rewrite_conv, THM_LIST(
      get_cm_binary_tail_count_def()));

  term third_choice =
      `(op:int) == 9i && cm_is_pointer (cm_expr_type (left:cm_expr)) &&
       cm_is_pointer (cm_expr_type (right:cm_expr))`;
  gnode_list third = BOOL_CASES_TAC(
      second[1], third_choice, "Htail_third");
  CONV_WITH_ASMP_TAC(third[0], reduce_rewrite_conv, THM_LIST(
      get_cm_binary_tail_count_def()));

  term fourth_choice =
      `(op:int) == 9i && cm_is_pointer (cm_expr_type (left:cm_expr))`;
  gnode_list fourth = BOOL_CASES_TAC(
      third[1], fourth_choice, "Htail_fourth");
  for (size_t i = 0; i < 2; ++i) {
    CONV_WITH_ASMP_TAC(fourth[i], reduce_rewrite_conv, THM_LIST(
        get_cm_binary_tail_count_def()));
  }
  return gnode_prove(root);
}
PROOF static thm cm_binary_tail_positive =
    cm_prove_binary_tail_positive();

PROOF static thm cm_prove_expr_count_node_from_tree(void) {
  gnode root = gnode_new_with_ccl(
      `!(e:cm_expr) (p:cm_program) fid.
         cm_expr_counts_representable p fid e ==>
         cm_expr_count_node_representable p fid e`);
  gnode introduced = AUTO_INTROS_TAC(root);
  thm cases_th = ispec_rule(`e:cm_expr`, get_cm_expr_cases());
  gnode_list cases = DISJ_CASES_TAC(introduced, cases_th, "He");
  for (size_t i = 0; i < 14; ++i) {
    while (true) {
      labeled_term_list assumptions = goal_lasmps(cases[i]->g);
      int index = labeled_term_list_index(assumptions, "He");
      if (!is_exists(assumptions[index].tm)) break;
      cases[i] = ASMP_EXISTS_TAC(cases[i], "He", NULL);
    }
    labeled_term_list assumptions = goal_lasmps(cases[i]->g);
    int index = labeled_term_list_index(assumptions, "He");
    thm shape = assume_rule(assumptions[index].tm);
    thm opened = conv_rule(rewrite_conv(THM_LIST(
        shape, get_cm_expr_counts_representable_def())), assume_rule(
        `cm_expr_counts_representable
          (p:cm_program) (fid:int) (e:cm_expr)`));
    thm node = (i == 0 || i == 10)
        ? opened : conjunct1_rule(opened);
    thm generic = conv_rule(rewrite_conv(THM_LIST(
        sym_rule(shape))), node);
    ACCEPT_TAC(cases[i], generic);
  }
  return gnode_prove(root);
}
PROOF static thm cm_expr_count_node_from_tree =
    cm_prove_expr_count_node_from_tree();

PROOF static thm cm_prove_args_count_node_from_tree(void) {
  gnode root = gnode_new_with_ccl(
      `!(args:(cm_expr)list) (p:cm_program) fid.
         cm_args_counts_representable p fid args ==>
         cm_i32_code_count
           (cm_args_code_count_of (cm_args_code_counts p fid args))`);
  gnode_list cases = INDUCT_TAC(root, `args:(cm_expr)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm opened = conv_rule(rewrite_conv(THM_LIST(
        get_cm_expr_counts_representable_def())), assume_rule(
        `cm_args_counts_representable
          (p:cm_program) (fid:int) ([]:(cm_expr)list)`));
    ACCEPT_TAC(leaf, opened);
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm opened = conv_rule(rewrite_conv(THM_LIST(
        get_cm_expr_counts_representable_def())), assume_rule(
        `cm_args_counts_representable (p:cm_program) (fid:int)
          ((a0:cm_expr) :: (a1:(cm_expr)list))`));
    ACCEPT_TAC(leaf, conjunct1_rule(opened));
  }
  return gnode_prove(root);
}
PROOF static thm cm_args_count_node_from_tree =
    cm_prove_args_count_node_from_tree();

PROOF static thm cm_prove_args_temps_safe_pair(void) {
  gnode root = gnode_new_with_ccl(
      `!(args:(cm_expr)list).
         cm_rep_args_temps_safe args ==>
         cm_rep_apair_safe (cm_args_apair args)`);
  gnode_list cases = INDUCT_TAC(root, `args:(cm_expr)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm opened = conv_rule(rewrite_conv(THM_LIST(
        get_cm_rep_expr_temps_safe_def())), assume_rule(
        `cm_rep_args_temps_safe ([]:(cm_expr)list)`));
    ACCEPT_TAC(leaf, opened);
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm opened = conv_rule(rewrite_conv(THM_LIST(
        get_cm_rep_expr_temps_safe_def())), assume_rule(
        `cm_rep_args_temps_safe
          ((a0:cm_expr) :: (a1:(cm_expr)list))`));
    ACCEPT_TAC(leaf, conjunct1_rule(opened));
  }
  return gnode_prove(root);
}
PROOF static thm cm_args_temps_safe_pair =
    cm_prove_args_temps_safe_pair();


PROOF static gnode cm_add_ready_parts(gnode node, thm parts) {
  node = ASSUME_TAC(node, parts, NULL);
  if (!is_conj(concl(parts))) {
    thm opened = conv_rule(rewrite_conv(THM_LIST(
        get_cm_expr_count_node_representable_def(),
        get_cm_code_counts_representable_def(),
        get_cm_i32_code_count_def(),
        get_cm_expr_code_counts_def(),
        get_cm_lvalue_code_count_def(),
        get_cm_rvalue_code_count_def(),
        get_cm_lcount_of_def(),
        get_cm_rcount_of_def(),
        get_cm_args_code_counts_def(),
        get_cm_args_code_count_of_def(),
        get_cm_rep_tpair_safe_def(),
        get_cm_ltemps_def(),
        get_cm_rtemps_def(),
        get_cm_args_temps_def(),
        get_cm_stmt_code_count_def(),
        get_cm_stemps_def(),
        get_cm_rep_stmt_temps_safe_def(),
        get_cm_rep_stmt_children_safe_def(),
        get_cm_rep_apair_safe_def())), parts);
    if (alpha_compare(concl(opened), concl(parts)) != 0) {
      return cm_add_ready_parts(node, opened);
    }
    return node;
  }
  thm first = conjunct1_rule(parts);
  if (is_comb(concl(first))) {
    dest_comb_results application = dest_comb(concl(first));
    if (alpha_compare(application.tm1,
          `cm_rep_expr_temps_safe:cm_expr->bool`) == 0) {
      thm pair = mp_rule(spec_rule(application.tm2,
          get_cm_rep_expr_temps_safe_pair()), first);
      thm opened = conv_rule(rewrite_conv(THM_LIST(
          get_cm_rep_tpair_safe_def())), pair);
      node = cm_add_ready_parts(node, opened);
    } else if (alpha_compare(application.tm1,
          `cm_rep_args_temps_safe:(cm_expr)list->bool`) == 0) {
      thm pair = mp_rule(spec_rule(application.tm2,
          cm_args_temps_safe_pair), first);
      thm opened = conv_rule(rewrite_conv(THM_LIST(
          get_cm_rep_apair_safe_def())), pair);
      node = cm_add_ready_parts(node, opened);
    }
  }
  node = cm_add_ready_parts(node, first);
  return cm_add_ready_parts(node, conjunct2_rule(parts));
}

PROOF static thm cm_expr_ready_ih(
    const term child, const thm induction_hypothesis,
    const thm representable) {
  thm ready = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`), induction_hypothesis), representable);
  thm count_node = mp_rule(specl_rule(TERM_LIST(
      child, `p:cm_program`, `fid:int`),
      cm_expr_count_node_from_tree), representable);
  return conj_rule(count_node, ready);
}

PROOF static gnode cm_prepare_expr_ready_case(
    gnode node, size_t constructor_index) {
  if (constructor_index == 3) {
    thm representable = conv_rule(rewrite_conv(THM_LIST(
        get_cm_expr_counts_representable_def())), assume_rule(
        `cm_expr_counts_representable (p:cm_program) (fid:int)
          (CMAssignE (a0:cm_expr) (a1:cm_expr) (a2:cm_type))`));
    node = cm_add_ready_parts(node, representable);
    thm left_rep = conjunct1_rule(conjunct2_rule(representable));
    thm right_rep = conjunct2_rule(conjunct2_rule(representable));
    node = cm_add_ready_parts(node, cm_expr_ready_ih(`a0:cm_expr`,
        assume_rule(
          `!(p:cm_program) fid.
             cm_expr_counts_representable p fid (a0:cm_expr) ==>
             cm_rep_expr_temps_safe a0 &&
             cm_ltemps a0 <= cm_lvalue_code_count p fid a0 &&
             cm_rtemps a0 <= cm_rvalue_code_count p fid a0`),
        left_rep));
    node = cm_add_ready_parts(node, cm_expr_ready_ih(`a1:cm_expr`,
        assume_rule(
          `!(p:cm_program) fid.
             cm_expr_counts_representable p fid (a1:cm_expr) ==>
             cm_rep_expr_temps_safe a1 &&
             cm_ltemps a1 <= cm_lvalue_code_count p fid a1 &&
             cm_rtemps a1 <= cm_rvalue_code_count p fid a1`),
        right_rep));
    node = ASSUME_TAC(node, spec_rule(`a2:cm_type`,
        cm_char_normalize_nonnegative), NULL);
  } else if (constructor_index == 4) {
    thm representable = conv_rule(rewrite_conv(THM_LIST(
        get_cm_expr_counts_representable_def())), assume_rule(
        `cm_expr_counts_representable (p:cm_program) (fid:int)
          (CMBinaryE (a0:int) (a1:cm_expr) (a2:cm_expr)
            (a3:cm_type))`));
    node = cm_add_ready_parts(node, representable);
    thm left_rep = conjunct1_rule(conjunct2_rule(representable));
    thm right_rep = conjunct2_rule(conjunct2_rule(representable));
    node = cm_add_ready_parts(node, cm_expr_ready_ih(`a1:cm_expr`,
        assume_rule(
          `!(p:cm_program) fid.
             cm_expr_counts_representable p fid (a1:cm_expr) ==>
             cm_rep_expr_temps_safe a1 &&
             cm_ltemps a1 <= cm_lvalue_code_count p fid a1 &&
             cm_rtemps a1 <= cm_rvalue_code_count p fid a1`),
        left_rep));
    node = cm_add_ready_parts(node, cm_expr_ready_ih(`a2:cm_expr`,
        assume_rule(
          `!(p:cm_program) fid.
             cm_expr_counts_representable p fid (a2:cm_expr) ==>
             cm_rep_expr_temps_safe a2 &&
             cm_ltemps a2 <= cm_lvalue_code_count p fid a2 &&
             cm_rtemps a2 <= cm_rvalue_code_count p fid a2`),
        right_rep));
    node = ASSUME_TAC(node, ispecl_rule(TERM_LIST(
        `p:cm_program`, `a0:int`, `a1:cm_expr`, `a2:cm_expr`),
        cm_binary_tail_positive), NULL);
  } else if (constructor_index == 5) {
    thm representable = conv_rule(rewrite_conv(THM_LIST(
        get_cm_expr_counts_representable_def())), assume_rule(
        `cm_expr_counts_representable (p:cm_program) (fid:int)
          (CMUnaryE (a0:int) (a1:cm_expr) (a2:cm_type))`));
    node = cm_add_ready_parts(node, representable);
    node = cm_add_ready_parts(node, cm_expr_ready_ih(`a1:cm_expr`,
        assume_rule(
          `!(p:cm_program) fid.
             cm_expr_counts_representable p fid (a1:cm_expr) ==>
             cm_rep_expr_temps_safe a1 &&
             cm_ltemps a1 <= cm_lvalue_code_count p fid a1 &&
             cm_rtemps a1 <= cm_rvalue_code_count p fid a1`),
        conjunct2_rule(representable)));
  } else if (constructor_index == 6) {
    thm representable = conv_rule(rewrite_conv(THM_LIST(
        get_cm_expr_counts_representable_def())), assume_rule(
        `cm_expr_counts_representable (p:cm_program) (fid:int)
          (CMIndexE (a0:cm_expr) (a1:cm_expr) (a2:cm_type))`));
    node = cm_add_ready_parts(node, representable);
    thm base_rep = conjunct1_rule(conjunct2_rule(representable));
    thm index_rep = conjunct2_rule(conjunct2_rule(representable));
    node = cm_add_ready_parts(node, cm_expr_ready_ih(`a0:cm_expr`,
        assume_rule(
          `!(p:cm_program) fid.
             cm_expr_counts_representable p fid (a0:cm_expr) ==>
             cm_rep_expr_temps_safe a0 &&
             cm_ltemps a0 <= cm_lvalue_code_count p fid a0 &&
             cm_rtemps a0 <= cm_rvalue_code_count p fid a0`),
        base_rep));
    node = cm_add_ready_parts(node, cm_expr_ready_ih(`a1:cm_expr`,
        assume_rule(
          `!(p:cm_program) fid.
             cm_expr_counts_representable p fid (a1:cm_expr) ==>
             cm_rep_expr_temps_safe a1 &&
             cm_ltemps a1 <= cm_lvalue_code_count p fid a1 &&
             cm_rtemps a1 <= cm_rvalue_code_count p fid a1`),
        index_rep));
  } else if (constructor_index == 7) {
    thm representable = conv_rule(rewrite_conv(THM_LIST(
        get_cm_expr_counts_representable_def())), assume_rule(
        `cm_expr_counts_representable (p:cm_program) (fid:int)
          (CMMemberE (a0:cm_expr) (a1:int) (a2:cm_type))`));
    node = cm_add_ready_parts(node, representable);
    thm base_rep = conjunct2_rule(conjunct2_rule(representable));
    node = cm_add_ready_parts(node, cm_expr_ready_ih(`a0:cm_expr`,
        assume_rule(
          `!(p:cm_program) fid.
             cm_expr_counts_representable p fid (a0:cm_expr) ==>
             cm_rep_expr_temps_safe a0 &&
             cm_ltemps a0 <= cm_lvalue_code_count p fid a0 &&
             cm_rtemps a0 <= cm_rvalue_code_count p fid a0`),
        base_rep));
  } else if (constructor_index == 8) {
    thm representable = conv_rule(rewrite_conv(THM_LIST(
        get_cm_expr_counts_representable_def())), assume_rule(
        `cm_expr_counts_representable (p:cm_program) (fid:int)
          (CMCallE (a0:int) (a1:(cm_expr)list) (a2:cm_type))`));
    node = cm_add_ready_parts(node, representable);
    thm args_rep = conjunct2_rule(conjunct2_rule(representable));
    thm args_ready = mp_rule(specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`), assume_rule(
          `!(p:cm_program) fid.
             cm_args_counts_representable p fid (a1:(cm_expr)list) ==>
             cm_rep_args_temps_safe a1 &&
             cm_args_temps a1 <=
               cm_args_code_count_of (cm_args_code_counts p fid a1)`)),
        args_rep);
    node = cm_add_ready_parts(node, args_ready);
  } else if (constructor_index >= 11 && constructor_index <= 13) {
    thm source = constructor_index == 11
        ? assume_rule(
            `cm_expr_counts_representable (p:cm_program) (fid:int)
              (CMPutcE (a0:cm_expr) (a1:cm_type))`)
        : constructor_index == 12
          ? assume_rule(
              `cm_expr_counts_representable (p:cm_program) (fid:int)
                (CMPutiE (a0:cm_expr) (a1:cm_type))`)
          : assume_rule(
              `cm_expr_counts_representable (p:cm_program) (fid:int)
                (CMExitE (a0:cm_expr) (a1:cm_type))`);
    thm representable = conv_rule(rewrite_conv(THM_LIST(
        get_cm_expr_counts_representable_def())), source);
    node = cm_add_ready_parts(node, representable);
    node = cm_add_ready_parts(node, cm_expr_ready_ih(`a0:cm_expr`,
        assume_rule(
          `!(p:cm_program) fid.
             cm_expr_counts_representable p fid (a0:cm_expr) ==>
             cm_rep_expr_temps_safe a0 &&
             cm_ltemps a0 <= cm_lvalue_code_count p fid a0 &&
             cm_rtemps a0 <= cm_rvalue_code_count p fid a0`),
        conjunct2_rule(representable)));
  } else if (constructor_index == 15) {
    thm representable = conv_rule(rewrite_conv(THM_LIST(
        get_cm_expr_counts_representable_def())), assume_rule(
        `cm_args_counts_representable (p:cm_program) (fid:int)
          ((a0:cm_expr) :: (a1:(cm_expr)list))`));
    node = cm_add_ready_parts(node, representable);
    thm expr_rep = conjunct1_rule(conjunct2_rule(representable));
    thm tail_rep = conjunct2_rule(conjunct2_rule(representable));
    node = cm_add_ready_parts(node, cm_expr_ready_ih(`a0:cm_expr`,
        assume_rule(
          `!(p:cm_program) fid.
             cm_expr_counts_representable p fid (a0:cm_expr) ==>
             cm_rep_expr_temps_safe a0 &&
             cm_ltemps a0 <= cm_lvalue_code_count p fid a0 &&
             cm_rtemps a0 <= cm_rvalue_code_count p fid a0`),
        expr_rep));
    thm tail_ready = mp_rule(specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`), assume_rule(
          `!(p:cm_program) fid.
             cm_args_counts_representable p fid (a1:(cm_expr)list) ==>
             cm_rep_args_temps_safe a1 &&
             cm_args_temps a1 <=
               cm_args_code_count_of (cm_args_code_counts p fid a1)`)),
        tail_rep);
    thm tail_count = mp_rule(specl_rule(TERM_LIST(
        `a1:(cm_expr)list`, `p:cm_program`, `fid:int`),
        cm_args_count_node_from_tree), tail_rep);
    node = cm_add_ready_parts(node, conj_rule(tail_count, tail_ready));
  }
  return node;
}

PROOF static void cm_close_ready_arithmetic(gnode node) {
  if (!IS_NULL(node->solved)) return;
  if (is_conj(goal_ccl(node->g))) {
    gnode_list parts = CONJ_TAC(node);
    cm_close_ready_arithmetic(parts[0]);
    cm_close_ready_arithmetic(parts[1]);
    return;
  }
  term proposition_head = goal_ccl(node->g);
  while (is_comb(proposition_head)) {
    proposition_head = dest_comb(proposition_head).tm1;
  }
  if (alpha_compare(
        proposition_head, `(<=):int->int->bool`) == 0) {
    dest_binop_results comparison = dest_binop(
        `(<=):int->int->bool`, goal_ccl(node->g));
    term maximum_head = comparison.tm2;
    while (is_comb(maximum_head)) {
      maximum_head = dest_comb(maximum_head).tm1;
    }
    if (alpha_compare(maximum_head, `cm_imax:int->int->int`) == 0) {
      dest_comb_results outer = dest_comb(comparison.tm2);
      dest_comb_results inner = dest_comb(outer.tm1);
      node = ASSUME_TAC(node, specl_rule(TERM_LIST(
          inner.tm2, outer.tm2), cm_imax_left_bound), NULL);
    }
  }
  labeled_term_list assumptions = goal_lasmps(node->g);
  thm facts = assume_rule(assumptions[0].tm);
  for (size_t i = 1; i < vector_size(assumptions); ++i) {
    facts = conj_rule(facts, assume_rule(assumptions[i].tm));
  }
  ACCEPT_TAC(node, mp_rule(int_arith_rule(
      mk_imp(concl(facts), goal_ccl(node->g))), facts));
}

PROOF static void cm_reduce_expr_ready_branch(gnode node) {
  gnode_list frontier = LIST_GNODE(node);
  for (size_t i = 0; i < vector_size(frontier); ++i) {
    gnode reduced = CONV_WITH_ASMP_TAC(frontier[i],
        reduce_rewrite_conv, THM_LIST(
          get_cm_expr_counts_representable_def(),
          get_cm_expr_count_node_representable_def(),
          get_cm_code_counts_representable_def(),
          get_cm_i32_code_count_def(),
          get_cm_expr_code_counts_def(),
          get_cm_lvalue_code_count_def(),
          get_cm_rvalue_code_count_def(),
          get_cm_binding_address_count_def(),
          get_cm_lcount_of_def(), get_cm_rcount_of_def(),
          get_cm_args_code_counts_def(),
          get_cm_args_code_count_of_def(),
          get_cm_rep_expr_temps_safe_def(),
          get_cm_rep_tpair_safe_def(), get_cm_rep_apair_safe_def(),
          get_cm_expr_tpair_def(), get_cm_ltemps_def(),
          get_cm_rtemps_def(), get_cm_args_temps_def(),
          get_cm_tleft_def(), get_cm_tright_def(),
          get_cm_acount_def(), get_cm_adepth_def(),
          cm_temp_imax_add_upper, cm_temp_imax_upper,
          cm_expr_temps_nonnegative));
    cm_close_ready_arithmetic(reduced);
  }
}

PROOF static gnode cm_find_open_temp_leaf(const gnode node) {
  if (!IS_NULL(node->solved)) return NULL;
  if (vector_size(node->children) == 0) return node;
  for (size_t i = 0; i < vector_size(node->children); ++i) {
    gnode open = cm_find_open_temp_leaf(node->children[i]);
    if (open != NULL) return open;
  }
  return NULL;
}

PROOF static thm cm_prove_expr_and_args_temps_ready(void) {
  gnode root = gnode_new_with_ccl(
      `((!(expr:cm_expr). !(p:cm_program) fid.
           cm_expr_counts_representable p fid expr ==>
           cm_rep_expr_temps_safe expr &&
           cm_ltemps expr <= cm_lvalue_code_count p fid expr &&
           cm_rtemps expr <= cm_rvalue_code_count p fid expr) &&
        (!(args:(cm_expr)list). !(p:cm_program) fid.
           cm_args_counts_representable p fid args ==>
           cm_rep_args_temps_safe args &&
           cm_args_temps args <=
             cm_args_code_count_of (cm_args_code_counts p fid args)))`);
  gnode matched = MATCH_MP_TAC(root, get_cm_expr_induction());
  gnode cursor = CONV_TAC(matched, reduce_rewrite_conv(THM_LIST()));
  gnode cases[16];
  for (size_t i = 0; i < 15; ++i) {
    gnode_list split = CONJ_TAC(cursor);
    cases[i] = split[0];
    cursor = split[1];
  }
  cases[15] = cursor;
  for (size_t i = 0; i < 16; ++i) {
    gnode leaf = AUTO_INTROS_TAC(cases[i]);
    gnode_list introduced = AUTO_ASMP_DESTRUCT_TAC(leaf);
    if (vector_size(introduced) == 0) {
      introduced = LIST_GNODE(leaf);
    }
    for (size_t j = 0; j < vector_size(introduced); ++j) {
      gnode current = cm_prepare_expr_ready_case(introduced[j], i);
      if (i == 2) {
        gnode_list branches = BOOL_CASES_TAC(
            current, `(a0:int) == 0i`, "Hbinding_scope");
        cm_reduce_expr_ready_branch(branches[0]);
        cm_reduce_expr_ready_branch(branches[1]);
      } else if (i == 4) {
        gnode_list branches = BOOL_CASES_TAC(
            current, `(a0:int) == 0i || a0 == 1i`, "Hlogical_op");
        for (size_t k = 0; k < vector_size(branches); ++k) {
          cm_reduce_expr_ready_branch(branches[k]);
        }
      } else if (i == 5) {
        gnode_list deref = BOOL_CASES_TAC(
            current, `(a0:int) == 2i`, "Haddress_op");
        cm_reduce_expr_ready_branch(deref[0]);
        gnode_list address = BOOL_CASES_TAC(
            deref[1], `(a0:int) == 3i`, "Hderef_op");
        cm_reduce_expr_ready_branch(address[0]);
        cm_reduce_expr_ready_branch(address[1]);
      } else if (i == 7) {
        gnode_list branches = BOOL_CASES_TAC(current,
            `cm_member_array (p:cm_program)
               (cm_expr_type (a0:cm_expr)) (a1:int)`, "Hmember_array");
        cm_reduce_expr_ready_branch(branches[0]);
        cm_reduce_expr_ready_branch(branches[1]);
      } else {
        cm_reduce_expr_ready_branch(current);
      }
    }
  }
  for (size_t i = 0; i < 16; ++i) {
    gnode open = cm_find_open_temp_leaf(cases[i]);
    ENSURE_COND(open == NULL,
        "temporary readiness case %zu has an open leaf: %s",
        i, cstr_gnode(open));
  }
  return gnode_prove(root);
err:
  return empty_theorem;
}
PROOF static thm cm_expr_and_args_temps_ready =
    cm_prove_expr_and_args_temps_ready();
PROOF thm cm_expr_temps_ready_from_counts =
    conjunct1_rule(cm_expr_and_args_temps_ready);
PROOF thm cm_args_temps_ready_from_counts =
    conjunct2_rule(cm_expr_and_args_temps_ready);

PROOF static thm cm_prove_stmt_count_node_from_tree(void) {
  gnode root = gnode_new_with_ccl(
      `!(s:cm_stmt) (p:cm_program) fid.
         cm_stmt_counts_representable p fid s ==>
         cm_i32_code_count (cm_stmt_code_count p fid s)`);
  gnode introduced = AUTO_INTROS_TAC(root);
  thm cases_th = ispec_rule(`s:cm_stmt`, get_cm_stmt_cases());
  gnode_list cases = DISJ_CASES_TAC(introduced, cases_th, "Hs");
  for (size_t i = 0; i < 11; ++i) {
    while (true) {
      labeled_term_list assumptions = goal_lasmps(cases[i]->g);
      int index = labeled_term_list_index(assumptions, "Hs");
      if (!is_exists(assumptions[index].tm)) break;
      cases[i] = ASMP_EXISTS_TAC(cases[i], "Hs", NULL);
    }
    labeled_term_list assumptions = goal_lasmps(cases[i]->g);
    int index = labeled_term_list_index(assumptions, "Hs");
    thm shape = assume_rule(assumptions[index].tm);
    thm opened = conv_rule(rewrite_conv(THM_LIST(
        shape, get_cm_stmt_counts_representable_def())), assume_rule(
        `cm_stmt_counts_representable
          (p:cm_program) (fid:int) (s:cm_stmt)`));
    thm count = (i == 0 || i == 2 || i == 8 || i == 9)
        ? opened : conjunct1_rule(opened);
    thm generic = conv_rule(rewrite_conv(THM_LIST(
        sym_rule(shape))), count);
    ACCEPT_TAC(cases[i], generic);
  }
  return gnode_prove(root);
}
PROOF static thm cm_stmt_count_node_from_tree =
    cm_prove_stmt_count_node_from_tree();

PROOF static thm cm_expr_ready_from_counts(
    const term expression, const thm representable) {
  thm ready = mp_rule(specl_rule(TERM_LIST(
      expression, `p:cm_program`, `fid:int`),
      cm_expr_temps_ready_from_counts), representable);
  thm count = mp_rule(specl_rule(TERM_LIST(
      expression, `p:cm_program`, `fid:int`),
      cm_expr_count_node_from_tree), representable);
  return conj_rule(count, ready);
}

PROOF static thm cm_stmt_ready_ih(
    const term child, const thm induction_hypothesis,
    const thm representable) {
  thm ready = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`), induction_hypothesis), representable);
  thm count = mp_rule(specl_rule(TERM_LIST(
      child, `p:cm_program`, `fid:int`),
      cm_stmt_count_node_from_tree), representable);
  return conj_rule(count, ready);
}

PROOF static gnode cm_prepare_stmt_ready_case(
    gnode node, size_t constructor_index) {
  if (constructor_index == 1) {
    thm representable = conv_rule(rewrite_conv(THM_LIST(
        get_cm_stmt_counts_representable_def())), assume_rule(
        `cm_stmt_counts_representable (p:cm_program) (fid:int)
          (CMExprS (a:cm_expr))`));
    node = cm_add_ready_parts(node, representable);
    node = cm_add_ready_parts(node, cm_expr_ready_from_counts(
        `a:cm_expr`, conjunct2_rule(representable)));
  } else if (constructor_index == 3) {
    thm representable = conv_rule(rewrite_conv(THM_LIST(
        get_cm_stmt_counts_representable_def())), assume_rule(
        `cm_stmt_counts_representable (p:cm_program) (fid:int)
          (CMInitS (a0:int) (a1:cm_expr))`));
    node = cm_add_ready_parts(node, representable);
    thm expression_rep = conjunct2_rule(conjunct2_rule(representable));
    node = cm_add_ready_parts(node, cm_expr_ready_from_counts(
        `a1:cm_expr`, expression_rep));
    node = ASSUME_TAC(node, spec_rule(
        `cm_slot_ty
          (inth (a0:int)
            (cm_function_locals
              (inth (fid:int)
                (cm_program_functions (p:cm_program)))))`,
        cm_char_normalize_nonnegative), NULL);
  } else if (constructor_index == 4) {
    thm representable = conv_rule(rewrite_conv(THM_LIST(
        get_cm_stmt_counts_representable_def())), assume_rule(
        `cm_stmt_counts_representable (p:cm_program) (fid:int)
          (CMSeqS (a0:cm_stmt) (a1:cm_stmt))`));
    node = cm_add_ready_parts(node, representable);
    thm first_rep = conjunct1_rule(conjunct2_rule(representable));
    thm second_rep = conjunct2_rule(conjunct2_rule(representable));
    node = cm_add_ready_parts(node, cm_stmt_ready_ih(`a0:cm_stmt`,
        assume_rule(
          `!(p:cm_program) fid.
             cm_stmt_counts_representable p fid (a0:cm_stmt) ==>
             cm_rep_stmt_temps_safe a0 &&
             cm_stemps a0 <= cm_stmt_code_count p fid a0`),
        first_rep));
    node = cm_add_ready_parts(node, cm_stmt_ready_ih(`a1:cm_stmt`,
        assume_rule(
          `!(p:cm_program) fid.
             cm_stmt_counts_representable p fid (a1:cm_stmt) ==>
             cm_rep_stmt_temps_safe a1 &&
             cm_stemps a1 <= cm_stmt_code_count p fid a1`),
        second_rep));
  } else if (constructor_index == 5) {
    thm representable = conv_rule(rewrite_conv(THM_LIST(
        get_cm_stmt_counts_representable_def())), assume_rule(
        `cm_stmt_counts_representable (p:cm_program) (fid:int)
          (CMBlockS (a:cm_stmt))`));
    node = cm_add_ready_parts(node, representable);
    thm child_rep = conjunct2_rule(representable);
    node = cm_add_ready_parts(node, cm_stmt_ready_ih(`a:cm_stmt`,
        assume_rule(
          `!(p:cm_program) fid.
             cm_stmt_counts_representable p fid (a:cm_stmt) ==>
             cm_rep_stmt_temps_safe a &&
             cm_stemps a <= cm_stmt_code_count p fid a`),
        child_rep));
  } else if (constructor_index == 6) {
    thm representable = conv_rule(rewrite_conv(THM_LIST(
        get_cm_stmt_counts_representable_def())), assume_rule(
        `cm_stmt_counts_representable (p:cm_program) (fid:int)
          (CMIfS (a0:cm_expr) (a1:cm_stmt) (a2:cm_stmt))`));
    node = cm_add_ready_parts(node, representable);
    thm expression_rep = conjunct1_rule(conjunct2_rule(representable));
    thm yes_rep = conjunct1_rule(conjunct2_rule(
        conjunct2_rule(representable)));
    thm no_rep = conjunct2_rule(conjunct2_rule(
        conjunct2_rule(representable)));
    node = cm_add_ready_parts(node, cm_expr_ready_from_counts(
        `a0:cm_expr`, expression_rep));
    node = cm_add_ready_parts(node, cm_stmt_ready_ih(`a1:cm_stmt`,
        assume_rule(
          `!(p:cm_program) fid.
             cm_stmt_counts_representable p fid (a1:cm_stmt) ==>
             cm_rep_stmt_temps_safe a1 &&
             cm_stemps a1 <= cm_stmt_code_count p fid a1`),
        yes_rep));
    node = cm_add_ready_parts(node, cm_stmt_ready_ih(`a2:cm_stmt`,
        assume_rule(
          `!(p:cm_program) fid.
             cm_stmt_counts_representable p fid (a2:cm_stmt) ==>
             cm_rep_stmt_temps_safe a2 &&
             cm_stemps a2 <= cm_stmt_code_count p fid a2`),
        no_rep));
  } else if (constructor_index == 7) {
    thm representable = conv_rule(rewrite_conv(THM_LIST(
        get_cm_stmt_counts_representable_def())), assume_rule(
        `cm_stmt_counts_representable (p:cm_program) (fid:int)
          (CMWhileS (a0:cm_expr) (a1:cm_stmt))`));
    node = cm_add_ready_parts(node, representable);
    thm expression_rep = conjunct1_rule(conjunct2_rule(representable));
    thm body_rep = conjunct2_rule(conjunct2_rule(representable));
    node = cm_add_ready_parts(node, cm_expr_ready_from_counts(
        `a0:cm_expr`, expression_rep));
    node = cm_add_ready_parts(node, cm_stmt_ready_ih(`a1:cm_stmt`,
        assume_rule(
          `!(p:cm_program) fid.
             cm_stmt_counts_representable p fid (a1:cm_stmt) ==>
             cm_rep_stmt_temps_safe a1 &&
             cm_stemps a1 <= cm_stmt_code_count p fid a1`),
        body_rep));
  } else if (constructor_index == 10) {
    thm representable = conv_rule(rewrite_conv(THM_LIST(
        get_cm_stmt_counts_representable_def())), assume_rule(
        `cm_stmt_counts_representable (p:cm_program) (fid:int)
          (CMReturnS (a:cm_expr))`));
    node = cm_add_ready_parts(node, representable);
    thm expression_rep = conjunct2_rule(conjunct2_rule(representable));
    node = cm_add_ready_parts(node, cm_expr_ready_from_counts(
        `a:cm_expr`, expression_rep));
    node = ASSUME_TAC(node, spec_rule(
        `cm_function_ret
          (inth (fid:int) (cm_program_functions (p:cm_program)))`,
        cm_char_normalize_nonnegative), NULL);
  }
  return node;
}

PROOF static thm cm_prove_stmt_temps_ready(void) {
  gnode root = gnode_new_with_ccl(
      `!(stmt:cm_stmt). !(p:cm_program) fid.
         cm_stmt_counts_representable p fid stmt ==>
         cm_rep_stmt_temps_safe stmt &&
         cm_stemps stmt <= cm_stmt_code_count p fid stmt`);
  gnode_list cases = INDUCT_TAC(root, `stmt:cm_stmt`);
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode leaf = AUTO_INTROS_TAC(cases[i]);
    gnode_list frontier = AUTO_ASMP_DESTRUCT_TAC(leaf);
    if (vector_size(frontier) == 0) frontier = LIST_GNODE(leaf);
    for (size_t j = 0; j < vector_size(frontier); ++j) {
      gnode current = cm_prepare_stmt_ready_case(frontier[j], i);
      gnode reduced = CONV_WITH_ASMP_TAC(current,
          reduce_rewrite_conv, THM_LIST(
            get_cm_stmt_counts_representable_def(),
            get_cm_stmt_code_count_def(),
            get_cm_i32_code_count_def(),
            get_cm_rep_stmt_temps_safe_def(),
            get_cm_rep_stmt_children_safe_def(),
            get_cm_stemps_def(), cm_temp_imax_add_upper,
            get_cm_rtemps_def(),
            get_cm_rvalue_code_count_def(),
            cm_temp_imax_upper));
      cm_close_ready_arithmetic(reduced);
    }
  }
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode open = cm_find_open_temp_leaf(cases[i]);
    ENSURE_COND(open == NULL,
        "statement temporary readiness case %zu has an open leaf: %s",
        i, cstr_gnode(open));
  }
  return gnode_prove(root);
err:
  return empty_theorem;
}
PROOF thm cm_stmt_temps_ready_with_bound =
    cm_prove_stmt_temps_ready();

PROOF static thm cm_prove_stmt_temps_ready_from_counts(void) {
  gnode root = gnode_new_with_ccl(
      `!(stmt:cm_stmt) (p:cm_program) fid.
         cm_stmt_counts_representable p fid stmt ==>
         cm_rep_stmt_temps_safe stmt`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm ready = mp_rule(specl_rule(TERM_LIST(
      `stmt:cm_stmt`, `p:cm_program`, `fid:int`),
      cm_stmt_temps_ready_with_bound), assume_rule(
      `cm_stmt_counts_representable
        (p:cm_program) (fid:int) (stmt:cm_stmt)`));
  ACCEPT_TAC(leaf, conjunct1_rule(ready));
  return gnode_prove(root);
}
PROOF thm cm_stmt_temps_ready_from_counts =
    cm_prove_stmt_temps_ready_from_counts();

PROOF static int _cmc_temp_ready_no_axioms =
    vector_size(get_all_axioms()) == _cmc_temp_ready_axioms_before
        ? 1 : (abort(), 0);
