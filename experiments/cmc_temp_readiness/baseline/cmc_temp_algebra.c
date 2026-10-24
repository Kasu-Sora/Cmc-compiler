#include "proof/proof.h"
#include "userlib/renderers.h"
#include "cmc_lang.h"
#require "cmc_lang.c"
#include "userlib/proof.h"
#include "cmc_temp_algebra.h"

PROOF static size_t _cmc_temp_algebra_axioms_before =
    vector_size(get_all_axioms());

/* Shared temporary-slot arithmetic proofs. */
PROOF thm cmc_imax_le_case(void) {
  thm reduced = by_rewrite(
      `cm_imax (a:int) (b:int) == b`,
      THM_LIST(
        get_cm_imax_def(),
        eqt_intro_rule(assume_rule(`(a:int) <= (b:int)`)),
        get_theorem_by_name("COND_CLAUSES")));
  return close_implication(
      `!(a:int) (b:int). a <= b ==> cm_imax a b == b`, reduced);
}

PROOF thm cmc_imax_gt_case(void) {
  thm nle = int_arith_rule(`(a:int) > (b:int) ==> ~(a <= b)`);
  thm reduced = by_rewrite(
      `cm_imax (a:int) (b:int) == a`,
      THM_LIST(
        get_cm_imax_def(),
        eqf_intro_rule(mp_rule(nle, assume_rule(`(a:int) > (b:int)`))),
        get_theorem_by_name("COND_CLAUSES")));
  return close_implication(
      `!(a:int) (b:int). a > b ==> cm_imax a b == a`, reduced);
}

PROOF static thm cm_prove_imax_left_bound(void) {
  gnode root = gnode_new_with_ccl(
      `!(a:int) (b:int). a <= cm_imax a b`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list cases = BOOL_CASES_TAC(
      leaf, `(a:int) <= (b:int)`, "Hle");
  {
    thm le = assume_rule(`(a:int) <= (b:int)`);
    thm maximum = mp_rule(specl_rule(TERM_LIST(
        `a:int`, `b:int`), cmc_imax_le_case()), le);
    thm transport = beta_norm(ap_term_rule(
        `\x:int. (a:int) <= x`, sym_rule(maximum)));
    ACCEPT_TAC(cases[0], eq_mp_rule(transport, le));
  }
  {
    thm nle = assume_rule(`~((a:int) <= (b:int))`);
    thm gt = mp_rule(
        int_arith_rule(
          `~((a:int) <= (b:int)) ==> a > b`), nle);
    thm maximum = mp_rule(specl_rule(TERM_LIST(
        `a:int`, `b:int`), cmc_imax_gt_case()), gt);
    thm transport = beta_norm(ap_term_rule(
        `\x:int. (a:int) <= x`, sym_rule(maximum)));
    ACCEPT_TAC(cases[1], eq_mp_rule(
        transport, int_arith_rule(`(a:int) <= a`)));
  }
  return gnode_prove(root);
}
PROOF thm cm_imax_left_bound = cm_prove_imax_left_bound();

PROOF static thm cm_prove_imax_right_bound(void) {
  gnode root = gnode_new_with_ccl(
      `!(a:int) (b:int). b <= cm_imax a b`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list cases = BOOL_CASES_TAC(
      leaf, `(a:int) <= (b:int)`, "Hle");
  {
    thm le = assume_rule(`(a:int) <= (b:int)`);
    thm maximum = mp_rule(specl_rule(TERM_LIST(
        `a:int`, `b:int`), cmc_imax_le_case()), le);
    thm transport = beta_norm(ap_term_rule(
        `\x:int. (b:int) <= x`, sym_rule(maximum)));
    ACCEPT_TAC(cases[0], eq_mp_rule(
        transport, int_arith_rule(`(b:int) <= b`)));
  }
  {
    thm nle = assume_rule(`~((a:int) <= (b:int))`);
    thm gt = mp_rule(
        int_arith_rule(
          `~((a:int) <= (b:int)) ==> a > b`), nle);
    thm maximum = mp_rule(specl_rule(TERM_LIST(
        `a:int`, `b:int`), cmc_imax_gt_case()), gt);
    thm transport = beta_norm(ap_term_rule(
        `\x:int. (b:int) <= x`, sym_rule(maximum)));
    thm bound = mp_rule(
        int_arith_rule(
          `~((a:int) <= (b:int)) ==> b <= a`), nle);
    ACCEPT_TAC(cases[1], eq_mp_rule(transport, bound));
  }
  return gnode_prove(root);
}
PROOF thm cm_imax_right_bound = cm_prove_imax_right_bound();

PROOF static thm cm_prove_imax_nonnegative(void) {
  gnode root = gnode_new_with_ccl(
      `!(x:int) (y:int).
         0i <= x && 0i <= y ==> 0i <= cm_imax x y`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm inputs = assume_rule(
      `0i <= (x:int) && 0i <= (y:int)`);
  thm left_bound = specl_rule(TERM_LIST(
      `x:int`, `y:int`), cm_imax_left_bound);
  thm facts = conj_rule(left_bound, conjunct1_rule(inputs));
  ACCEPT_TAC(leaf, mp_rule(int_arith_rule(mk_imp(
      concl(facts), goal_ccl(leaf->g))), facts));
  return gnode_prove(root);
}
PROOF thm cm_imax_nonnegative = cm_prove_imax_nonnegative();

PROOF static void cm_lang_close_nonnegative_expression(
    const gnode node) {
  if (!IS_NULL(node->solved)) return;
  if (is_conj(goal_ccl(node->g))) {
    gnode_list parts = CONJ_TAC(node);
    cm_lang_close_nonnegative_expression(parts[0]);
    cm_lang_close_nonnegative_expression(parts[1]);
    return;
  }
  term proposition_head = goal_ccl(node->g);
  while (is_comb(proposition_head)) {
    proposition_head = dest_comb(proposition_head).tm1;
  }
  if (alpha_compare(
        proposition_head, `COND:bool->bool->bool->bool`) == 0) {
    dest_comb_results outer = dest_comb(goal_ccl(node->g));
    dest_comb_results middle = dest_comb(outer.tm1);
    term choice = dest_comb(middle.tm1).tm2;
    gnode_list cases = BOOL_CASES_TAC(
        node, choice, "Htemp_choice");
    for (size_t i = 0; i < vector_size(cases); ++i) {
      gnode reduced = CONV_WITH_ASMP_TAC(
          cases[i], reduce_rewrite_conv, THM_LIST());
      cm_lang_close_nonnegative_expression(reduced);
    }
    return;
  }
  dest_binop_results comparison = dest_binop(
      `(<=):int->int->bool`, goal_ccl(node->g));
  term head = comparison.tm2;
  while (is_comb(head)) head = dest_comb(head).tm1;
  if (alpha_compare(head, `cm_imax:int->int->int`) == 0) {
    gnode premise = MATCH_MP_TAC(node, cm_imax_nonnegative);
    gnode_list parts = CONJ_TAC(premise);
    cm_lang_close_nonnegative_expression(parts[0]);
    cm_lang_close_nonnegative_expression(parts[1]);
    return;
  }
  labeled_term_list context = goal_lasmps(node->g);
  thm facts = assume_rule(context[0].tm);
  for (size_t i = 1; i < vector_size(context); ++i) {
    facts = conj_rule(facts, assume_rule(context[i].tm));
  }
  ACCEPT_TAC(node, mp_rule(int_arith_rule(
      mk_imp(concl(facts), goal_ccl(node->g))), facts));
}

PROOF static thm cm_prove_expr_and_args_temps_nonnegative(void) {
  gnode root = gnode_new_with_ccl(
      `(!(expr:cm_expr).
          0i <= cm_ltemps expr && 0i <= cm_rtemps expr) &&
       (!(args:(cm_expr)list).
          0i <= cm_acount (cm_args_apair args) &&
          0i <= cm_adepth (cm_args_apair args))`);
  gnode matched = MATCH_MP_TAC(root, get_cm_expr_induction());
  gnode cursor = CONV_TAC(
      matched, reduce_rewrite_conv(THM_LIST()));
  gnode cases[16];
  for (size_t i = 0; i < 15; ++i) {
    gnode_list split = CONJ_TAC(cursor);
    cases[i] = split[0];
    cursor = split[1];
  }
  cases[15] = cursor;
  for (size_t i = 0; i < 16; ++i) {
    gnode leaf = AUTO_INTROS_TAC(cases[i]);
    gnode_list frontier = AUTO_ASMP_DESTRUCT_TAC(leaf);
    for (size_t j = 0; j < vector_size(frontier); ++j) {
      gnode_list branches = LIST_GNODE(frontier[j]);
      if (i == 4) {
        branches = BOOL_CASES_TAC(frontier[j],
            `(a0:int) == 0i || a0 == 1i`, "Hlogical_temp");
      } else if (i == 5) {
        gnode_list deref_cases = BOOL_CASES_TAC(
            frontier[j], `(a0:int) == 2i`, "Hderef_temp");
        gnode_list address_cases = BOOL_CASES_TAC(
            deref_cases[1], `(a0:int) == 3i`, "Haddress_temp");
        branches = LIST_GNODE(
            deref_cases[0], address_cases[0], address_cases[1]);
      }
      for (size_t branch_index = 0;
           branch_index < vector_size(branches); ++branch_index) {
        gnode current = branches[branch_index];
        labeled_term_list assumptions =
            goal_lasmps(current->g);
        size_t assumption_count = vector_size(assumptions);
        for (size_t k = 0; k < assumption_count; ++k) {
          thm normalized = conv_rule(rewrite_conv(THM_LIST(
              get_cm_ltemps_def(), get_cm_rtemps_def())),
              assume_rule(assumptions[k].tm));
          if (alpha_compare(
                concl(normalized), assumptions[k].tm) != 0) {
            current = ASSUME_TAC(current, normalized, NULL);
          }
        }
        gnode closed = CONV_WITH_ASMP_TAC(
            current, reduce_rewrite_conv, THM_LIST(
              get_cm_ltemps_def(), get_cm_rtemps_def(),
              get_cm_expr_tpair_def(), get_cm_tleft_def(),
              get_cm_tright_def(), get_cm_acount_def(),
              get_cm_adepth_def(), cm_imax_nonnegative));
        cm_lang_close_nonnegative_expression(closed);
      }
    }
  }
  return gnode_prove(root);
}
PROOF static thm cm_expr_and_args_temps_nonnegative =
    cm_prove_expr_and_args_temps_nonnegative();
PROOF thm cm_expr_temps_nonnegative =
    conjunct1_rule(cm_expr_and_args_temps_nonnegative);
PROOF thm cm_args_temps_nonnegative =
    conjunct2_rule(cm_expr_and_args_temps_nonnegative);
PROOF static thm cm_prove_ltemps_nonnegative(void) {
  term expr = `expr:cm_expr`;
  return gen_rule(expr, conjunct1_rule(
      spec_rule(expr, cm_expr_temps_nonnegative)));
}
PROOF thm cm_ltemps_nonnegative =
    cm_prove_ltemps_nonnegative();

PROOF static thm cm_prove_rtemps_nonnegative(void) {
  term expr = `expr:cm_expr`;
  return gen_rule(expr, conjunct2_rule(
      spec_rule(expr, cm_expr_temps_nonnegative)));
}
PROOF thm cm_rtemps_nonnegative =
    cm_prove_rtemps_nonnegative();

PROOF static thm cm_prove_acount_nonnegative(void) {
  term args = `args:(cm_expr)list`;
  return gen_rule(args, conjunct1_rule(
      spec_rule(args, cm_args_temps_nonnegative)));
}
PROOF thm cm_acount_nonnegative =
    cm_prove_acount_nonnegative();

PROOF static thm cm_prove_adepth_nonnegative(void) {
  term args = `args:(cm_expr)list`;
  return gen_rule(args, conjunct2_rule(
      spec_rule(args, cm_args_temps_nonnegative)));
}
PROOF thm cm_adepth_nonnegative =
    cm_prove_adepth_nonnegative();
PROOF static thm cm_prove_args_count_matches_length(void) {
  gnode root = gnode_new_with_ccl(
      `!(args:(cm_expr)list).
         cm_acount (cm_args_apair args) == ilength args`);
  gnode_list cases = INDUCT_TAC(root, `args:(cm_expr)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        get_cm_expr_tpair_def(), get_cm_acount_def(),
        get_theorem_by_name("ILENGTH_DEF"))));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    CONV_WITH_ASMP_TAC(leaf, reduce_rewrite_conv, THM_LIST(
        get_cm_expr_tpair_def(), get_cm_acount_def(),
        get_theorem_by_name("ILENGTH_DEF")));
  }
  return gnode_prove(root);
}
PROOF thm cm_args_count_matches_length =
    cm_prove_args_count_matches_length();

PROOF static thm cm_prove_adepth_head_bound(void) {
  gnode root = gnode_new_with_ccl(
      `!(arg:cm_expr) (args:(cm_expr)list).
         cm_rtemps arg <=
         cm_adepth (cm_args_apair (arg :: args))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm bound = specl_rule(TERM_LIST(
      `cm_rtemps (arg:cm_expr)`,
      `cm_adepth (cm_args_apair (args:(cm_expr)list))`),
      cm_imax_left_bound);
  thm_list rules = THM_LIST(
      get_cm_rtemps_def(), get_cm_expr_tpair_def(),
      get_cm_adepth_def());
  thm target_view = apply_conversion(
      reduce_rewrite_conv(rules), goal_ccl(leaf->g));
  thm normalized = conv_rule(reduce_rewrite_conv(rules), bound);
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), normalized));
  return gnode_prove(root);
}
PROOF thm cm_adepth_head_bound =
    cm_prove_adepth_head_bound();

PROOF static thm cm_prove_adepth_tail_bound(void) {
  gnode root = gnode_new_with_ccl(
      `!(arg:cm_expr) (args:(cm_expr)list).
         cm_adepth (cm_args_apair args) <=
         cm_adepth (cm_args_apair (arg :: args))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm bound = specl_rule(TERM_LIST(
      `cm_rtemps (arg:cm_expr)`,
      `cm_adepth (cm_args_apair (args:(cm_expr)list))`),
      cm_imax_right_bound);
  thm_list rules = THM_LIST(
      get_cm_rtemps_def(), get_cm_expr_tpair_def(),
      get_cm_adepth_def());
  thm target_view = apply_conversion(
      reduce_rewrite_conv(rules), goal_ccl(leaf->g));
  thm normalized = conv_rule(reduce_rewrite_conv(rules), bound);
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), normalized));
  return gnode_prove(root);
}
PROOF thm cm_adepth_tail_bound =
    cm_prove_adepth_tail_bound();





PROOF static int cmc_temp_algebra_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_temp_algebra_axioms_before,
      "cmc_temp_algebra introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_temp_algebra_checks =
    cmc_temp_algebra_final_checks();
