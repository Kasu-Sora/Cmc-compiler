#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_stack_local.h"
#require "cmc_stack_local.c"
#include "cmc_stack_bound.h"

PROOF static size_t _cmc_stack_bound_axioms_before = vector_size(get_all_axioms());

PROOF static gnode cm_bound_assume_conjunct_leaves(
    gnode branch, const thm fact, size_t *counter) {
  if (is_conj(concl(fact))) {
    branch = cm_bound_assume_conjunct_leaves(
        branch, conjunct1_rule(fact), counter);
    return cm_bound_assume_conjunct_leaves(
        branch, conjunct2_rule(fact), counter);
  }
  return ASSUME_TAC(branch, fact,
      gc_sprintf("hwfpart%zu", (*counter)++));
}

PROOF thm cm_heights_le_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(!bound.
       cm_heights_le (bound:int) ([]:(int)list) = T) &&
     (!bound height rest.
       cm_heights_le bound
         ((height:int) :: (rest:(int)list)) =
       (height <= bound && cm_heights_le bound rest))`);

PROOF static thm cm_prove_heights_le_append(void) {
  gnode root = gnode_new_with_ccl(
      `!(left:(int)list). !right bound.
         cm_heights_le (bound:int) (left ++ right) <=>
         cm_heights_le bound left &&
         cm_heights_le bound right`);
  gnode_list cases =
      INDUCT_TAC(root, `left:(int)list`);
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode leaf = AUTO_INTROS_TAC(cases[i]);
    gnode reduced = CONV_WITH_ASMP_TAC(
        leaf, reduce_rewrite_conv,
        THM_LIST(cm_heights_le_def,
          get_theorem_by_name("APPEND")));
    if (IS_NULL(reduced->solved)) {
      ACCEPT_TAC(reduced, taut_rule(goal_ccl(reduced->g)));
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_heights_le_append =
    cm_prove_heights_le_append();

PROOF static thm cm_prove_heights_le_mono(void) {
  gnode root = gnode_new_with_ccl(
      `!(heights:(int)list). !small large.
         cm_heights_le (small:int) heights ==>
         small <= large ==>
         cm_heights_le (large:int) heights`);
  gnode_list cases =
      INDUCT_TAC(root, `heights:(int)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, reduce_rewrite_conv(
        THM_LIST(cm_heights_le_def)));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm small_bound = cm_matching_assumption(leaf,
        `cm_heights_le (small:int)
           ((a0:int) :: (a1:(int)list))`);
    thm order = cm_matching_assumption(
        leaf, `(small:int) <= (large:int)`);
    thm ih = cm_matching_assumption(leaf,
        `!small large.
           cm_heights_le (small:int) (a1:(int)list) ==>
           small <= large ==>
           cm_heights_le (large:int) a1`);
    thm parts = conv_rule(rewrite_conv(
        THM_LIST(cm_heights_le_def)), small_bound);
    thm head_large = mp_rule(int_arith_rule(mk_imp(
        mk_conj(concl(conjunct1_rule(parts)), concl(order)),
        `(a0:int) <= (large:int)`)),
        conj_rule(conjunct1_rule(parts), order));
    thm tail_large = mp_rule(mp_rule(specl_rule(
        TERM_LIST(`small:int`, `large:int`), ih),
        conjunct2_rule(parts)), order);
    gnode reduced = CONV_TAC(leaf,
        rewrite_conv(THM_LIST(cm_heights_le_def)));
    ACCEPT_TAC(reduced, conj_rule(head_large, tail_large));
  }
  return gnode_prove(root);
}
PROOF thm cm_heights_le_mono =
    cm_prove_heights_le_mono();

PROOF static thm cm_prove_imax_bounds(void) {
  gnode root = gnode_new_with_ccl(
      `!(x:int) y.
         x <= cm_imax x y && y <= cm_imax x y`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list cases = BOOL_CASES_TAC(
      leaf, `(x:int) <= (y:int)`, "hxy");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode reduced = CONV_WITH_ASMP_TAC(
        cases[i], reduce_rewrite_conv,
        THM_LIST(get_cm_imax_def()));
    if (IS_NULL(reduced->solved)) {
      thm condition = i == 0
          ? cm_matching_assumption(
              cases[i], `(x:int) <= (y:int)`)
          : cm_matching_assumption(
              cases[i], `~((x:int) <= (y:int))`);
      ACCEPT_TAC(reduced, mp_rule(int_arith_rule(mk_imp(
          concl(condition), goal_ccl(reduced->g))),
          condition));
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_imax_bounds =
    cm_prove_imax_bounds();
PROOF static thm cm_prove_imax_upper(void) {
  gnode root = gnode_new_with_ccl(
      `!(x:int) y bound.
         x <= bound ==> y <= bound ==>
         cm_imax x y <= bound`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list cases = BOOL_CASES_TAC(
      leaf, `(x:int) <= (y:int)`, "hxy");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode reduced = CONV_TAC(cases[i],
        reduce_rewrite_conv(THM_LIST(
          get_cm_imax_def(),
          i == 0
            ? cm_matching_assumption(
                cases[i], `(x:int) <= (y:int)`)
            : cm_matching_assumption(
                cases[i], `~((x:int) <= (y:int))`))));
    if (IS_NULL(reduced->solved)) {
      thm result = i == 0
          ? cm_matching_assumption(
              reduced, `(y:int) <= (bound:int)`)
          : cm_matching_assumption(
              reduced, `(x:int) <= (bound:int)`);
      ACCEPT_TAC(reduced, result);
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_imax_upper =
    cm_prove_imax_upper();


PROOF static thm cm_prove_max_arity_nonnegative_from(void) {
  gnode root = gnode_new_with_ccl(
      `!(functions:(cm_function_d)list).
         0i <= cm_max_function_arity_from functions`);
  gnode_list cases =
      INDUCT_TAC(root, `functions:(cm_function_d)list`);
  {
    CONV_TAC(cases[0], reduce_rewrite_conv(THM_LIST(
        get_cm_max_function_arity_from_def())));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm rest_nonnegative = cm_matching_assumption(leaf,
        `0i <= cm_max_function_arity_from
           (a1:(cm_function_d)list)`);
    thm right = conjunct2_rule(specl_rule(TERM_LIST(
        `ilength (cm_function_params (a0:cm_function_d))`,
        `cm_max_function_arity_from
           (a1:(cm_function_d)list)`),
        cm_imax_bounds));
    thm result = mp_rule(int_arith_rule(mk_imp(
        mk_conj(concl(rest_nonnegative), concl(right)),
        `0i <= cm_imax
           (ilength (cm_function_params (a0:cm_function_d)))
           (cm_max_function_arity_from
             (a1:(cm_function_d)list))`)),
        conj_rule(rest_nonnegative, right));
    gnode reduced = CONV_TAC(leaf,
        rewrite_conv(THM_LIST(
          get_cm_max_function_arity_from_def())));
    ACCEPT_TAC(reduced, result);
  }
  return gnode_prove(root);
}
PROOF thm cm_max_arity_nonnegative_from =
    cm_prove_max_arity_nonnegative_from();

PROOF static thm cm_prove_max_arity_nonnegative(void) {
  thm result = spec_rule(
      `cm_program_functions (p:cm_program)`,
      cm_max_arity_nonnegative_from);
  return gen_rule(`p:cm_program`,
      conv_rule(rewrite_conv(THM_LIST(
        gsym_rule(get_cm_max_function_arity_def()))),
        result));
}
PROOF thm cm_max_arity_nonnegative =
    cm_prove_max_arity_nonnegative();

PROOF static thm cm_prove_stack_bound_three(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program). 3i <= cm_stack_bound_model p`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm nonnegative = spec_rule(
      `p:cm_program`, cm_max_arity_nonnegative);
  gnode reduced = CONV_TAC(leaf,
      rewrite_conv(THM_LIST(
        get_cm_stack_bound_model_def())));
  ACCEPT_TAC(reduced, mp_rule(int_arith_rule(mk_imp(
      concl(nonnegative), goal_ccl(reduced->g))),
      nonnegative));
  return gnode_prove(root);
}
PROOF thm cm_stack_bound_three =
    cm_prove_stack_bound_three();

PROOF static thm cm_prove_heights_le_max(void) {
  gnode root = gnode_new_with_ccl(
      `!(heights:(int)list). !bound.
         0i <= bound ==>
         cm_heights_le (bound:int) heights ==>
         cm_stack_height_max heights <= bound`);
  gnode_list cases =
      INDUCT_TAC(root, `heights:(int)list`);
  gnode base_leaf = AUTO_INTROS_TAC(cases[0]);
  CONV_WITH_ASMP_TAC(base_leaf,
      reduce_rewrite_conv, THM_LIST(
        get_cm_stack_height_max_def()));
  gnode cons_leaf = AUTO_INTROS_TAC(cases[1]);
  thm nonnegative = cm_matching_assumption(
      cons_leaf, `0i <= (bound:int)`);
  thm bounded = cm_matching_assumption(cons_leaf,
      `cm_heights_le (bound:int)
         ((a0:int) :: (a1:(int)list))`);
  thm ih = cm_matching_assumption(cons_leaf,
      `!bound.
         0i <= bound ==>
         cm_heights_le (bound:int) (a1:(int)list) ==>
         cm_stack_height_max a1 <= bound`);
  thm parts = conv_rule(rewrite_conv(
      THM_LIST(cm_heights_le_def)), bounded);
  thm tail_max = mp_rule(mp_rule(
      spec_rule(`bound:int`, ih),
      nonnegative), conjunct2_rule(parts));
  thm result = mp_rule(mp_rule(specl_rule(
      TERM_LIST(`a0:int`,
        `cm_stack_height_max (a1:(int)list)`,
        `bound:int`), cm_imax_upper),
      conjunct1_rule(parts)), tail_max);
  gnode cons_reduced = CONV_TAC(cons_leaf,
      rewrite_conv(THM_LIST(
        get_cm_stack_height_max_def())));
  ACCEPT_TAC(cons_reduced, result);
  return gnode_prove(root);
}
PROOF thm cm_heights_le_max =
    cm_prove_heights_le_max();

PROOF static thm cm_prove_function_arity_le_max_from(void) {
  gnode root = gnode_new_with_ccl(
      `!(functions:(cm_function_d)list). !index.
         0i <= index && index < ilength functions ==>
         ilength
           (cm_function_params (inth index functions)) <=
         cm_max_function_arity_from functions`);
  gnode_list cases =
      INDUCT_TAC(root, `functions:(cm_function_d)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm bounds = cm_matching_assumption(leaf,
        `0i <= (index:int) &&
         index < ilength ([]:(cm_function_d)list)`);
    thm reduced_bounds = pure_rewrite_rule(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF")), bounds);
    CONTR_TAC(leaf, mp_rule(int_arith_rule(mk_imp(
        concl(reduced_bounds), `F`)), reduced_bounds));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm bounds = cm_matching_assumption(leaf,
        `0i <= (index:int) &&
         index < ilength
           ((a0:cm_function_d) :: (a1:(cm_function_d)list))`);
    gnode_list index_cases =
        BOOL_CASES_TAC(leaf, `(index:int) == 0i`, "hindex");
    {
      thm head_bound = conjunct1_rule(specl_rule(TERM_LIST(
          `ilength (cm_function_params (a0:cm_function_d))`,
          `cm_max_function_arity_from
             (a1:(cm_function_d)list)`), cm_imax_bounds));
      gnode reduced = CONV_WITH_ASMP_TAC(
          index_cases[0], reduce_rewrite_conv, THM_LIST(
            cm_inth_zero_cons,
            get_cm_max_function_arity_from_def()));
      if (IS_NULL(reduced->solved)) {
        ACCEPT_TAC(reduced, head_bound);
      }
    }
    {
      thm not_zero = cm_matching_assumption(
          index_cases[1], `~((index:int) == 0i)`);
      thm reduced_bounds = pure_rewrite_rule(THM_LIST(
          get_theorem_by_name("ILENGTH_DEF")), bounds);
      thm one_le = mp_rule(int_arith_rule(mk_imp(
          mk_conj(concl(reduced_bounds), concl(not_zero)),
          `1i <= (index:int)`)),
          conj_rule(reduced_bounds, not_zero));
      thm tail_bounds = mp_rule(int_arith_rule(mk_imp(
          mk_conj(concl(reduced_bounds), concl(not_zero)),
          `0i <= (index:int) - 1i &&
           index - 1i <
             ilength (a1:(cm_function_d)list)`)),
          conj_rule(reduced_bounds, not_zero));
      thm ih = cm_matching_assumption(index_cases[1],
          `!index.
             0i <= index &&
             index < ilength (a1:(cm_function_d)list) ==>
             ilength
               (cm_function_params (inth index a1)) <=
             cm_max_function_arity_from a1`);
      thm tail_result = mp_rule(spec_rule(
          `(index:int) - 1i`, ih), tail_bounds);
      thm function_step = mp_rule(ispecl_rule(TERM_LIST(
          `a0:cm_function_d`, `a1:(cm_function_d)list`,
          `index:int`), cm_inth_cons_tail), one_le);
      thm arity_step = beta_norm(ap_term_rule(
          `\fn:cm_function_d.
             ilength (cm_function_params fn)`,
          function_step));
      thm max_tail_bound = conjunct2_rule(specl_rule(TERM_LIST(
          `ilength (cm_function_params (a0:cm_function_d))`,
          `cm_max_function_arity_from
             (a1:(cm_function_d)list)`), cm_imax_bounds));
      thm result = mp_rule(int_arith_rule(mk_imp(
          mk_conj(concl(tail_result), concl(max_tail_bound)),
          `ilength (cm_function_params
             (inth ((index:int) - 1i)
               (a1:(cm_function_d)list))) <=
           cm_imax
             (ilength
               (cm_function_params (a0:cm_function_d)))
             (cm_max_function_arity_from a1)`)),
          conj_rule(tail_result, max_tail_bound));
      gnode reduced = CONV_TAC(index_cases[1],
          rewrite_conv(THM_LIST(
            arity_step,
            get_cm_max_function_arity_from_def())));
      ACCEPT_TAC(reduced, result);
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_function_arity_le_max_from =
    cm_prove_function_arity_le_max_from();

PROOF static thm cm_prove_function_arity_le_max(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) fid.
         0i <= fid &&
         fid < ilength (cm_program_functions p) ==>
         ilength (cm_function_params
           (inth fid (cm_program_functions p))) <=
         cm_max_function_arity p`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm bounds = cm_matching_assumption(leaf,
      `0i <= (fid:int) &&
       fid < ilength
         (cm_program_functions (p:cm_program))`);
  thm result = mp_rule(specl_rule(TERM_LIST(
      `cm_program_functions (p:cm_program)`,
      `fid:int`), cm_function_arity_le_max_from), bounds);
  gnode reduced = CONV_TAC(leaf,
      rewrite_conv(THM_LIST(
        get_cm_max_function_arity_def())));
  ACCEPT_TAC(reduced, result);
  return gnode_prove(root);
}
PROOF thm cm_function_arity_le_max =
    cm_prove_function_arity_le_max();

PROOF static thm cm_heights_le_join(
    const term bound, const term left, const term right,
    const thm left_bound, const thm right_bound) {
  thm split = specl_rule(TERM_LIST(
      left, right, bound), cm_heights_le_append);
  return eq_mp_rule(sym_rule(split),
      conj_rule(left_bound, right_bound));
}

PROOF static thm cm_prove_fp_address_bounded(void) {
  gnode root = gnode_new_with_ccl(
      `!(height:int) bound.
         0i <= height ==>
         height + 2i <= bound ==>
         cm_heights_le bound
           (cm_fp_address_heights height)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm result = by_defs_arith(goal_ccl(leaf->g),
      THM_LIST(cm_fp_address_heights_def,
        cm_heights_le_def),
      THM_LIST(
        cm_matching_assumption(leaf,
          `0i <= (height:int)`),
        cm_matching_assumption(leaf,
          `(height:int) + 2i <= (bound:int)`)));
  ACCEPT_TAC(leaf, result);
  return gnode_prove(root);
}
PROOF thm cm_fp_address_bounded =
    cm_prove_fp_address_bounded();

PROOF static thm cm_prove_temp_access_bounded(void) {
  gnode root = gnode_new_with_ccl(
      `!(height:int) bound.
         0i <= height ==>
         height + 2i <= bound ==>
         cm_heights_le bound
           (cm_temp_access_heights height)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm result = by_defs_arith(goal_ccl(leaf->g),
      THM_LIST(cm_temp_access_heights_def,
        cm_heights_le_def),
      THM_LIST(
        cm_matching_assumption(leaf,
          `0i <= (height:int)`),
        cm_matching_assumption(leaf,
          `(height:int) + 2i <= (bound:int)`)));
  ACCEPT_TAC(leaf, result);
  return gnode_prove(root);
}
PROOF thm cm_temp_access_bounded =
    cm_prove_temp_access_bounded();

PROOF static thm cm_prove_normalize_bounded(void) {
  gnode root = gnode_new_with_ccl(
      `!(ty:cm_type) height bound.
         0i <= height ==>
         height + 1i <= bound ==>
         cm_heights_le bound
           (cm_normalize_heights ty height)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list cases = BOOL_CASES_TAC(
      leaf, `(ty:cm_type) == CMCharTy`, "hchar");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    thm condition = i == 0
        ? cm_matching_assumption(
            cases[i], `(ty:cm_type) == CMCharTy`)
        : cm_matching_assumption(
            cases[i], `~((ty:cm_type) == CMCharTy)`);
    thm result = by_defs_arith(goal_ccl(cases[i]->g),
        THM_LIST(condition, cm_normalize_heights_def,
          cm_heights_le_def),
        THM_LIST(
          cm_matching_assumption(cases[i],
            `0i <= (height:int)`),
          cm_matching_assumption(cases[i],
            `(height:int) + 1i <= (bound:int)`)));
    ACCEPT_TAC(cases[i], result);
  }
  return gnode_prove(root);
}
PROOF thm cm_normalize_bounded =
    cm_prove_normalize_bounded();

PROOF static thm cm_prove_binding_address_bounded(void) {
  gnode root = gnode_new_with_ccl(
      `!(scope:int) bound.
         2i <= bound ==>
         cm_heights_le bound
           (cm_binding_address_heights scope)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list cases = BOOL_CASES_TAC(
      leaf, `(scope:int) == 0i`, "hglobal");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    thm condition = i == 0
        ? cm_matching_assumption(
            cases[i], `(scope:int) == 0i`)
        : cm_matching_assumption(
            cases[i], `~((scope:int) == 0i)`);
    thm result = by_defs_arith(goal_ccl(cases[i]->g),
        THM_LIST(condition, cm_binding_address_heights_def,
          cm_heights_le_def),
        THM_LIST(cm_matching_assumption(
          cases[i], `2i <= (bound:int)`)));
    ACCEPT_TAC(cases[i], result);
  }
  return gnode_prove(root);
}
PROOF thm cm_binding_address_bounded =
    cm_prove_binding_address_bounded();

PROOF static void cm_accept_binary_finish_bound(
    const gnode branch, const thm lower,
    const thm_list conditions) {
  thm_list rules = THM_LIST();
  for (size_t i = 0; i < vector_size(conditions); ++i) {
    vector_add(&rules, is_not(concl(conditions[i]))
        ? eqf_intro_rule(conditions[i])
        : eqt_intro_rule(conditions[i]));
  }
  vector_add(&rules, cm_binary_finish_heights_def);
  vector_add(&rules, cm_temp_access_heights_def);
  vector_add(&rules, cm_heights_le_append);
  vector_add(&rules, cm_heights_le_def);
  vector_add(&rules, get_theorem_by_name("APPEND"));
  ACCEPT_TAC(branch, by_defs_arith(
      goal_ccl(branch->g), rules, THM_LIST(lower)));
}

PROOF static thm cm_prove_binary_finish_bounded(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) op left right bound.
         3i <= bound ==>
         cm_heights_le bound
           (cm_binary_finish_heights
             p op (left:cm_expr) (right:cm_expr))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm lower = cm_matching_assumption(
      leaf, `3i <= (bound:int)`);
  term conditions[4] = {
      `(op:int) == 8i &&
       cm_is_pointer (cm_expr_type (right:cm_expr))`,
      `(op:int) == 8i &&
       cm_is_pointer (cm_expr_type (left:cm_expr))`,
      `(op:int) == 9i &&
       cm_is_pointer (cm_expr_type (left:cm_expr)) &&
       cm_is_pointer (cm_expr_type (right:cm_expr))`,
      `(op:int) == 9i &&
       cm_is_pointer (cm_expr_type (left:cm_expr))`
  };
  thm_list negatives = THM_LIST();
  gnode frontier = leaf;
  for (size_t i = 0; i < 4; ++i) {
    gnode_list cases = BOOL_CASES_TAC(
        frontier, conditions[i], gc_sprintf("hbound%zu", i));
    thm positive = cm_matching_assumption(
        cases[0], conditions[i]);
    thm_list branch_conditions =
        (thm_list)vector_copy(negatives);
    vector_add(&branch_conditions, positive);
    cm_accept_binary_finish_bound(
        cases[0], lower, branch_conditions);
    thm negative = cm_matching_assumption(
        cases[1], mk_not(conditions[i]));
    vector_add(&negatives, negative);
    frontier = cases[1];
  }
  cm_accept_binary_finish_bound(frontier, lower, negatives);
  return gnode_prove(root);
}
PROOF thm cm_binary_finish_bounded =
    cm_prove_binary_finish_bounded();

PROOF static thm cm_prove_return_heights_bounded(void) {
  gnode root = gnode_new_with_ccl(
      `!bound.
         3i <= bound ==>
         cm_heights_le bound cm_return_heights`);
  gnode leaf = AUTO_INTROS_TAC(root);
  ACCEPT_TAC(leaf, by_defs_arith(goal_ccl(leaf->g),
      THM_LIST(cm_return_heights_def,
        cm_heights_le_def),
      THM_LIST(cm_matching_assumption(
        leaf, `3i <= (bound:int)`))));
  return gnode_prove(root);
}
PROOF thm cm_return_heights_bounded =
    cm_prove_return_heights_bounded();

PROOF static thm cm_prove_prelude_heights_bounded(void) {
  gnode root = gnode_new_with_ccl(
      `!bound.
         3i <= bound ==>
         cm_heights_le bound cm_prelude_heights`);
  gnode leaf = AUTO_INTROS_TAC(root);
  ACCEPT_TAC(leaf, by_defs_arith(goal_ccl(leaf->g),
      THM_LIST(cm_prelude_heights_def,
        cm_heights_le_def),
      THM_LIST(cm_matching_assumption(
        leaf, `3i <= (bound:int)`))));
  return gnode_prove(root);
}
PROOF thm cm_prelude_heights_bounded =
    cm_prove_prelude_heights_bounded();

PROOF static thm cm_prove_fixed_prologue_bounded(void) {
  gnode root = gnode_new_with_ccl(
      `!(arity:int) bound.
         0i <= arity ==>
         arity + 3i <= bound ==>
         cm_heights_le bound
           (cm_fixed_prologue_heights arity)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  ACCEPT_TAC(leaf, by_defs_arith(goal_ccl(leaf->g),
      THM_LIST(cm_fixed_prologue_heights_def,
        cm_heights_le_def),
      THM_LIST(
        cm_matching_assumption(
          leaf, `0i <= (arity:int)`),
        cm_matching_assumption(leaf,
          `(arity:int) + 3i <= (bound:int)`))));
  return gnode_prove(root);
}
PROOF thm cm_fixed_prologue_bounded =
    cm_prove_fixed_prologue_bounded();

PROOF static thm cm_prove_param_store_heights_bounded(void) {
  gnode root = gnode_new_with_ccl(
      `!(params:(cm_slot_d)list). !height bound.
         0i <= height ==>
         ilength params <= height ==>
         height + 3i <= bound ==>
         cm_heights_le bound
           (cm_param_store_heights params height)`);
  gnode_list cases =
      INDUCT_TAC(root, `params:(cm_slot_d)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        cm_param_store_heights_def,
        cm_heights_le_def)));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm lower = cm_matching_assumption(
        leaf, `0i <= (height:int)`);
    thm length_bound = cm_matching_assumption(leaf,
        `ilength
           ((a0:cm_slot_d) :: (a1:(cm_slot_d)list)) <=
         (height:int)`);
    thm upper = cm_matching_assumption(
        leaf, `(height:int) + 3i <= (bound:int)`);
    thm tail_length_bound = mp_rule(int_arith_rule(mk_imp(
        concl(pure_rewrite_rule(THM_LIST(
          get_theorem_by_name("ILENGTH_DEF")),
          length_bound)),
        `ilength (a1:(cm_slot_d)list) <= (height:int)`)),
        pure_rewrite_rule(THM_LIST(
          get_theorem_by_name("ILENGTH_DEF")),
          length_bound));
    thm ih = cm_matching_assumption(leaf,
        `!height bound.
           0i <= height ==>
           ilength (a1:(cm_slot_d)list) <= height ==>
           height + 3i <= bound ==>
           cm_heights_le bound
             (cm_param_store_heights a1 height)`);
    thm tail_bound = mp_rule(mp_rule(mp_rule(
        specl_rule(TERM_LIST(
          `height:int`, `bound:int`), ih),
        lower), tail_length_bound), upper);
    thm tail_nonnegative = ispec_rule(
        `a1:(cm_slot_d)list`,
        get_theorem_by_name("ILENGTH_NONNEG"));
    gnode_list type_cases = BOOL_CASES_TAC(leaf,
        `cm_slot_ty (a0:cm_slot_d) == CMCharTy`,
        "hparamchar");
    for (size_t i = 0;
         i < vector_size(type_cases); ++i) {
      thm condition = i == 0
          ? cm_matching_assumption(type_cases[i],
              `cm_slot_ty (a0:cm_slot_d) == CMCharTy`)
          : cm_matching_assumption(type_cases[i],
              `~(cm_slot_ty (a0:cm_slot_d) == CMCharTy)`);
      ACCEPT_TAC(type_cases[i], by_defs_arith(
          goal_ccl(type_cases[i]->g),
          THM_LIST(
            condition,
            cm_param_store_heights_def,
            cm_normalize_heights_def,
            cm_fp_address_heights_def,
            cm_heights_le_append,
            cm_heights_le_def,
            get_theorem_by_name("ILENGTH_DEF"),
            get_theorem_by_name("APPEND"),
            tail_bound),
          THM_LIST(lower, tail_nonnegative, upper)));
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_param_store_heights_bounded =
    cm_prove_param_store_heights_bounded();

PROOF static thm cm_prove_args_reload_heights_bounded(void) {
  gnode root = gnode_new_with_ccl(
      `!(args:(cm_expr)list). !height bound.
         0i <= height ==>
         height + ilength args + 2i <= bound ==>
         cm_heights_le bound
           (cm_args_reload_heights height args)`);
  gnode_list cases =
      INDUCT_TAC(root, `args:(cm_expr)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        cm_args_reload_heights_def,
        cm_heights_le_def)));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm lower = cm_matching_assumption(
        leaf, `0i <= (height:int)`);
    thm upper = cm_matching_assumption(leaf,
        `(height:int) +
           ilength
             ((a0:cm_expr) :: (a1:(cm_expr)list)) +
           2i <= (bound:int)`);
    thm reduced_upper = pure_rewrite_rule(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF")), upper);
    thm tail_nonnegative = ispec_rule(
        `a1:(cm_expr)list`,
        get_theorem_by_name("ILENGTH_NONNEG"));
    thm ih = cm_matching_assumption(leaf,
        `!height bound.
           0i <= height ==>
           height + ilength (a1:(cm_expr)list) + 2i <=
             bound ==>
           cm_heights_le bound
             (cm_args_reload_heights height a1)`);
    thm next_lower = mp_rule(int_arith_rule(mk_imp(
        concl(lower), `0i <= (height:int) + 1i`)), lower);
    thm next_upper = mp_rule(int_arith_rule(mk_imp(
        concl(reduced_upper),
        `((height:int) + 1i) +
           ilength (a1:(cm_expr)list) + 2i <=
         (bound:int)`)),
        reduced_upper);
    thm tail_bound = mp_rule(mp_rule(specl_rule(TERM_LIST(
        `(height:int) + 1i`, `bound:int`), ih),
        next_lower), next_upper);
    ACCEPT_TAC(leaf, by_defs_arith(goal_ccl(leaf->g),
        THM_LIST(
          cm_args_reload_heights_def,
          cm_temp_access_heights_def,
          cm_heights_le_append,
          cm_heights_le_def,
          get_theorem_by_name("ILENGTH_DEF"),
          get_theorem_by_name("APPEND"),
          tail_bound),
        THM_LIST(lower, reduced_upper, tail_nonnegative)));
  }
  return gnode_prove(root);
}
PROOF thm cm_args_reload_heights_bounded =
    cm_prove_args_reload_heights_bounded();

PROOF static thm cm_prove_heights_le_cond(void) {
  gnode root = gnode_new_with_ccl(
      `!(condition:bool) (yes:(int)list) no bound.
         cm_heights_le (bound:int)
           (if condition then yes else no) <=>
         (if condition
          then cm_heights_le bound yes
          else cm_heights_le bound no)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list cases = BOOL_CASES_TAC(
      leaf, `condition:bool`, "hcondition");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    CONV_WITH_ASMP_TAC(
        cases[i], reduce_rewrite_conv, THM_LIST());
  }
  return gnode_prove(root);
}
PROOF thm cm_heights_le_cond =
    cm_prove_heights_le_cond();

PROOF static thm cm_prove_lheights_cond(void) {
  gnode root = gnode_new_with_ccl(
      `!(condition:bool) (yes:cm_height_pair) no.
         cm_lheights_of
           (if condition then yes else no) ==
         (if condition
          then cm_lheights_of yes
          else cm_lheights_of no)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list cases = BOOL_CASES_TAC(
      leaf, `condition:bool`, "hlcondition");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    CONV_WITH_ASMP_TAC(
        cases[i], reduce_rewrite_conv, THM_LIST());
  }
  return gnode_prove(root);
}
PROOF thm cm_lheights_cond =
    cm_prove_lheights_cond();

PROOF static thm cm_prove_rheights_cond(void) {
  gnode root = gnode_new_with_ccl(
      `!(condition:bool) (yes:cm_height_pair) no.
         cm_rheights_of
           (if condition then yes else no) ==
         (if condition
          then cm_rheights_of yes
          else cm_rheights_of no)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list cases = BOOL_CASES_TAC(
      leaf, `condition:bool`, "hrcondition");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    CONV_WITH_ASMP_TAC(
        cases[i], reduce_rewrite_conv, THM_LIST());
  }
  return gnode_prove(root);
}
PROOF thm cm_rheights_cond =
    cm_prove_rheights_cond();

PROOF static thm cm_stack_small_bound(
    const term p, const term value) {
  thm three = spec_rule(p, cm_stack_bound_three);
  return mp_rule(int_arith_rule(mk_imp(
      concl(three),
      `${value:int} <= cm_stack_bound_model ${p:cm_program}`)),
      three);
}

PROOF static thm cm_expr_bound_ih(
    const gnode branch, const term expr) {
  thm ih = cm_matching_assumption(branch,
      `!(p:cm_program) (f:cm_function_d) fid.
         cm_expr_wf p f ${expr:cm_expr} ==>
         cm_heights_le (cm_stack_bound_model p)
           (cm_lvalue_heights p fid ${expr:cm_expr}) &&
         cm_heights_le (cm_stack_bound_model p)
           (cm_rvalue_heights p fid ${expr:cm_expr})`);
  thm wf = cm_matching_assumption(branch,
      `cm_expr_wf (p:cm_program) (f:cm_function_d)
         ${expr:cm_expr}`);
  return mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `f:cm_function_d`, `fid:int`), ih), wf);
}

PROOF static thm cm_args_bound_ih(
    const gnode branch, const term args, const term slots) {
  thm ih = cm_matching_assumption(branch,
      `!(p:cm_program) (f:cm_function_d)
          (slots:(cm_slot_d)list) fid.
         cm_args_wf p f ${args:(cm_expr)list} slots ==>
         cm_heights_le (cm_stack_bound_model p)
           (cm_args_store_heights p fid ${args:(cm_expr)list})`);
  thm wf = cm_matching_assumption(branch,
      `cm_args_wf (p:cm_program) (f:cm_function_d)
         ${args:(cm_expr)list} ${slots:(cm_slot_d)list}`);
  return mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `f:cm_function_d`, slots,
      `fid:int`), ih), wf);
}

PROOF static thm_list cm_expr_standard_bound_facts(
    const term p, const term scope,
    const term normalize_ty, const term op,
    const term left, const term right) {
  thm zero = cm_stack_small_bound(p, `0i`);
  thm one = cm_stack_small_bound(p, `1i`);
  thm two = cm_stack_small_bound(p, `2i`);
  thm three = cm_stack_small_bound(p, `3i`);
  thm zero_plus_two = by_defs_arith(
      `0i + 2i <= cm_stack_bound_model ${p:cm_program}`,
      THM_LIST(), THM_LIST(two));
  thm one_plus_two = by_defs_arith(
      `1i + 2i <= cm_stack_bound_model ${p:cm_program}`,
      THM_LIST(), THM_LIST(three));
  thm one_plus_one = by_defs_arith(
      `1i + 1i <= cm_stack_bound_model ${p:cm_program}`,
      THM_LIST(), THM_LIST(two));
  thm temp_zero = mp_rule(mp_rule(specl_rule(TERM_LIST(
      `0i`, `cm_stack_bound_model ${p:cm_program}`),
      cm_temp_access_bounded),
      int_arith_rule(`0i <= 0i`)), zero_plus_two);
  thm temp_one = mp_rule(mp_rule(specl_rule(TERM_LIST(
      `1i`, `cm_stack_bound_model ${p:cm_program}`),
      cm_temp_access_bounded),
      int_arith_rule(`0i <= 1i`)), one_plus_two);
  thm fp_one = mp_rule(mp_rule(specl_rule(TERM_LIST(
      `1i`, `cm_stack_bound_model ${p:cm_program}`),
      cm_fp_address_bounded),
      int_arith_rule(`0i <= 1i`)), one_plus_two);
  thm normalize = mp_rule(mp_rule(specl_rule(TERM_LIST(
      normalize_ty, `1i`,
      `cm_stack_bound_model ${p:cm_program}`),
      cm_normalize_bounded),
      int_arith_rule(`0i <= 1i`)), one_plus_one);
  thm binding = mp_rule(specl_rule(TERM_LIST(
      scope, `cm_stack_bound_model ${p:cm_program}`),
      cm_binding_address_bounded), two);
  thm finish = mp_rule(specl_rule(TERM_LIST(
      p, op, left, right,
      `cm_stack_bound_model ${p:cm_program}`),
      cm_binary_finish_bounded), three);
  thm returned = mp_rule(spec_rule(
      `cm_stack_bound_model ${p:cm_program}`,
      cm_return_heights_bounded), three);
  return THM_LIST(
      zero, one, two, three,
      temp_zero, temp_one, fp_one,
      normalize, binding, finish, returned);
}

PROOF static void cm_add_expr_bound_pair(
    thm_list *facts, const thm pair) {
  thm left = conv_rule(rewrite_conv(THM_LIST(
      cm_lvalue_heights_def)), conjunct1_rule(pair));
  thm right = conv_rule(rewrite_conv(THM_LIST(
      cm_rvalue_heights_def)), conjunct2_rule(pair));
  vector_add(facts, left);
  vector_add(facts, right);
}

PROOF static thm cm_prove_expr_heights_bounded(void) {
  gnode root = gnode_new_with_ccl(
      `((!(expr:cm_expr).
           !(p:cm_program) (f:cm_function_d) fid.
           cm_expr_wf p f expr ==>
           cm_heights_le (cm_stack_bound_model p)
             (cm_lvalue_heights p fid expr) &&
           cm_heights_le (cm_stack_bound_model p)
             (cm_rvalue_heights p fid expr)) &&
        (!(args:(cm_expr)list).
           !(p:cm_program) (f:cm_function_d)
             (slots:(cm_slot_d)list) fid.
           cm_args_wf p f args slots ==>
           cm_heights_le (cm_stack_bound_model p)
             (cm_args_store_heights p fid args)))`);
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
    gnode constructor = AUTO_INTROS_TAC(cases[i]);
    gnode_list opened = AUTO_ASMP_DESTRUCT_TAC(constructor);
    gnode branch = opened[0];
    thm wf;
    thm parts;
    if (i < 14) {
      wf = cm_predicate_assumption(branch, "cm_expr_wf");
      parts = conv_rule(reduce_rewrite_conv(
          THM_LIST(get_cm_expr_wf_def())), wf);
    } else {
      wf = cm_predicate_assumption(branch, "cm_args_wf");
      parts = conv_rule(reduce_rewrite_conv(
          THM_LIST(get_cm_args_wf_def())), wf);
    }
    size_t wf_part = 0;
    branch = cm_bound_assume_conjunct_leaves(
        branch, parts, &wf_part);
    thm_list facts = cm_expr_standard_bound_facts(
        `p:cm_program`, `a0:int`, `a2:cm_type`,
        `a0:int`, `a1:cm_expr`, `a2:cm_expr`);
    if (i == 3) {
      thm dst = cm_expr_bound_ih(branch, `a0:cm_expr`);
      thm src = cm_expr_bound_ih(branch, `a1:cm_expr`);
      cm_add_expr_bound_pair(&facts, dst);
      cm_add_expr_bound_pair(&facts, src);
    } else if (i == 4 || i == 6) {
      term first_expr =
          i == 6 ? `a0:cm_expr` : `a1:cm_expr`;
      term second_expr =
          i == 6 ? `a1:cm_expr` : `a2:cm_expr`;
      thm first = cm_expr_bound_ih(branch, first_expr);
      thm second = cm_expr_bound_ih(branch, second_expr);
      cm_add_expr_bound_pair(&facts, first);
      cm_add_expr_bound_pair(&facts, second);
    } else if (i == 5 || i == 7 ||
               i == 11 || i == 12 || i == 13) {
      term child_expr =
          i == 5 ? `a1:cm_expr` : `a0:cm_expr`;
      thm child = cm_expr_bound_ih(branch, child_expr);
      cm_add_expr_bound_pair(&facts, child);
    } else if (i == 8) {
      term slots =
          `cm_function_params
             (inth (a0:int)
               (cm_program_functions (p:cm_program)))`;
      thm stored = cm_args_bound_ih(
          branch, `a1:(cm_expr)list`, slots);
      thm args_wf = cm_matching_assumption(branch,
          `cm_args_wf (p:cm_program) (f:cm_function_d)
             (a1:(cm_expr)list) ${slots:(cm_slot_d)list}`);
      thm args_length = mp_rule(specl_rule(TERM_LIST(
          `a1:(cm_expr)list`, `p:cm_program`,
          `f:cm_function_d`, slots), cm_args_wf_length),
          args_wf);
      thm lower = cm_matching_assumption(
          branch, `0i <= (a0:int)`);
      thm upper = cm_matching_assumption(branch,
          `(a0:int) <
           ilength (cm_program_functions (p:cm_program))`);
      thm arity_max = mp_rule(specl_rule(TERM_LIST(
          `p:cm_program`, `a0:int`),
          cm_function_arity_le_max),
          conj_rule(lower, upper));
      thm args_max = conv_rule(rewrite_conv(
          THM_LIST(sym_rule(args_length))), arity_max);
      thm max_nonnegative = spec_rule(
          `p:cm_program`, cm_max_arity_nonnegative);
      thm reload_upper = by_defs_arith(
          `0i + ilength (a1:(cm_expr)list) + 2i <=
           cm_stack_bound_model (p:cm_program)`,
          THM_LIST(get_cm_stack_bound_model_def()),
          THM_LIST(args_max, max_nonnegative));
      thm reloaded = mp_rule(mp_rule(specl_rule(TERM_LIST(
          `a1:(cm_expr)list`, `0i`,
          `cm_stack_bound_model (p:cm_program)`),
          cm_args_reload_heights_bounded),
          int_arith_rule(`0i <= 0i`)), reload_upper);
      thm call_height = by_defs_arith(
          `ilength (a1:(cm_expr)list) <=
           cm_stack_bound_model (p:cm_program)`,
          THM_LIST(get_cm_stack_bound_model_def()),
          THM_LIST(args_max, max_nonnegative));
      vector_add(&facts, stored);
      vector_add(&facts, reloaded);
      vector_add(&facts, call_height);
    } else if (i == 15) {
      thm arg = cm_expr_bound_ih(branch, `a0:cm_expr`);
      thm rest = cm_args_bound_ih(branch,
          `a1:(cm_expr)list`,
          `TL (slots:(cm_slot_d)list)`);
      cm_add_expr_bound_pair(&facts, arg);
      vector_add(&facts, rest);
    }
    thm_list rules = THM_LIST();
    for (size_t j = 0; j < vector_size(facts); ++j) {
      vector_add(&rules, facts[j]);
    }
    vector_add(&rules, cm_expr_heights_def);
    vector_add(&rules, cm_lvalue_heights_def);
    vector_add(&rules, cm_rvalue_heights_def);
    vector_add(&rules, cm_lheights_cond);
    vector_add(&rules, cm_rheights_cond);
    vector_add(&rules, cm_lheights_of_def);
    vector_add(&rules, cm_rheights_of_def);
    vector_add(&rules, cm_heights_le_append);
    vector_add(&rules, cm_heights_le_cond);
    vector_add(&rules, cm_heights_le_def);
    vector_add(&rules, get_theorem_by_name("APPEND"));
    gnode reduced = CONV_WITH_ASMP_TAC(
        branch, reduce_rewrite_conv, rules);
    if (IS_NULL(reduced->solved)) {
      ACCEPT_TAC(reduced, taut_rule(goal_ccl(reduced->g)));
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_expr_heights_bounded =
    cm_prove_expr_heights_bounded();

PROOF static thm cm_generated_expr_bound(
    const gnode branch, const term expr) {
  thm theorem = conjunct1_rule(cm_expr_heights_bounded);
  thm wf = cm_matching_assumption(branch,
      `cm_expr_wf (p:cm_program) (f:cm_function_d)
         ${expr:cm_expr}`);
  return conjunct2_rule(mp_rule(specl_rule(TERM_LIST(
      expr, `p:cm_program`, `f:cm_function_d`, `fid:int`),
      theorem), wf));
}

PROOF static thm cm_stmt_bound_ih(
    const gnode branch, const term stmt,
    const term loop) {
  thm ih = cm_matching_assumption(branch,
      `!(p:cm_program) (f:cm_function_d) (loop:bool) fid.
         cm_stmt_wf p f loop ${stmt:cm_stmt} ==>
         cm_heights_le (cm_stack_bound_model p)
           (cm_stmt_heights p fid ${stmt:cm_stmt})`);
  thm wf = cm_matching_assumption(branch,
      `cm_stmt_wf (p:cm_program) (f:cm_function_d)
         ${loop:bool} ${stmt:cm_stmt}`);
  return mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `f:cm_function_d`,
      loop, `fid:int`), ih), wf);
}

PROOF static thm cm_prove_stmt_heights_bounded(void) {
  gnode root = gnode_new_with_ccl(
      `!(stmt:cm_stmt).
         !(p:cm_program) (f:cm_function_d) (loop:bool) fid.
         cm_stmt_wf p f loop stmt ==>
         cm_heights_le (cm_stack_bound_model p)
           (cm_stmt_heights p fid stmt)`);
  gnode_list cases = INDUCT_TAC(root, `stmt:cm_stmt`);
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode constructor = AUTO_INTROS_TAC(cases[i]);
    gnode leaf = AUTO_ASMP_DESTRUCT_TAC(constructor)[0];
    leaf = AUTO_INTROS_TAC(leaf);
    if (i == 1 || i == 3 || i == 4 || i == 5 ||
        i == 6 || i == 7 || i == 10) {
      thm wf = cm_predicate_assumption(leaf, "cm_stmt_wf");
      thm parts = conv_rule(reduce_rewrite_conv(
          THM_LIST(get_cm_stmt_wf_def())), wf);
      size_t wf_part = 0;
      leaf = cm_bound_assume_conjunct_leaves(
          leaf, parts, &wf_part);
    }
    term normalize_ty = `CMIntTy`;
    if (i == 3) {
      normalize_ty =
          `cm_slot_ty
             (inth (a0:int)
               (cm_function_locals
                 (inth (fid:int)
                   (cm_program_functions (p:cm_program)))))`;
    } else if (i == 10) {
      normalize_ty =
          `cm_function_ret
             (inth (fid:int)
               (cm_program_functions (p:cm_program)))`;
    }
    thm_list facts = cm_expr_standard_bound_facts(
        `p:cm_program`, `0i`, normalize_ty,
        `0i`, `CMConstE 0i CMIntTy`,
        `CMConstE 0i CMIntTy`);
    if (i == 1) {
      vector_add(&facts,
          cm_generated_expr_bound(leaf, `a:cm_expr`));
    } else if (i == 3) {
      vector_add(&facts,
          cm_generated_expr_bound(leaf, `a1:cm_expr`));
    } else if (i == 4) {
      vector_add(&facts, cm_stmt_bound_ih(
          leaf, `a0:cm_stmt`, `loop:bool`));
      vector_add(&facts, cm_stmt_bound_ih(
          leaf, `a1:cm_stmt`, `loop:bool`));
    } else if (i == 5) {
      vector_add(&facts, cm_stmt_bound_ih(
          leaf, `a:cm_stmt`, `loop:bool`));
    } else if (i == 6) {
      vector_add(&facts,
          cm_generated_expr_bound(leaf, `a0:cm_expr`));
      vector_add(&facts, cm_stmt_bound_ih(
          leaf, `a1:cm_stmt`, `loop:bool`));
      vector_add(&facts, cm_stmt_bound_ih(
          leaf, `a2:cm_stmt`, `loop:bool`));
    } else if (i == 7) {
      vector_add(&facts,
          cm_generated_expr_bound(leaf, `a0:cm_expr`));
      vector_add(&facts, cm_stmt_bound_ih(
          leaf, `a1:cm_stmt`, `T`));
    } else if (i == 10) {
      vector_add(&facts,
          cm_generated_expr_bound(leaf, `a:cm_expr`));
    }
    thm_list rules = THM_LIST();
    for (size_t j = 0; j < vector_size(facts); ++j) {
      vector_add(&rules, facts[j]);
    }
    vector_add(&rules, cm_stmt_heights_def);
    vector_add(&rules, cm_heights_le_append);
    vector_add(&rules, cm_heights_le_cond);
    vector_add(&rules, cm_heights_le_def);
    vector_add(&rules, get_theorem_by_name("APPEND"));
    gnode reduced = CONV_WITH_ASMP_TAC(
        leaf, reduce_rewrite_conv, rules);
    if (IS_NULL(reduced->solved)) {
      ACCEPT_TAC(reduced, taut_rule(goal_ccl(reduced->g)));
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_stmt_heights_bounded =
    cm_prove_stmt_heights_bounded();

PROOF static thm cm_prove_prologue_heights_bounded(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (f:cm_function_d).
         ilength (cm_function_params f) <=
           cm_max_function_arity p ==>
         cm_heights_le (cm_stack_bound_model p)
           (cm_prologue_heights f)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  term arity =
      `ilength (cm_function_params (f:cm_function_d))`;
  thm arity_max = cm_matching_assumption(leaf,
      `${arity:int} <= cm_max_function_arity (p:cm_program)`);
  thm arity_nonnegative = ispec_rule(
      `cm_function_params (f:cm_function_d)`,
      get_theorem_by_name("ILENGTH_NONNEG"));
  thm upper = by_defs_arith(
      `${arity:int} + 3i <=
       cm_stack_bound_model (p:cm_program)`,
      THM_LIST(get_cm_stack_bound_model_def()),
      THM_LIST(arity_max));
  thm fixed = mp_rule(mp_rule(specl_rule(TERM_LIST(
      arity, `cm_stack_bound_model (p:cm_program)`),
      cm_fixed_prologue_bounded),
      arity_nonnegative), upper);
  thm params = mp_rule(mp_rule(mp_rule(specl_rule(TERM_LIST(
      `cm_function_params (f:cm_function_d)`,
      arity, `cm_stack_bound_model (p:cm_program)`),
      cm_param_store_heights_bounded),
      arity_nonnegative), int_arith_rule(
        `${arity:int} <= ${arity:int}`)), upper);
  thm result = cm_heights_le_join(
      `cm_stack_bound_model (p:cm_program)`,
      `cm_fixed_prologue_heights ${arity:int}`,
      `cm_param_store_heights
         (cm_function_params (f:cm_function_d)) ${arity:int}`,
      fixed, params);
  gnode reduced = CONV_TAC(leaf,
      rewrite_conv(THM_LIST(cm_prologue_heights_def)));
  ACCEPT_TAC(reduced, result);
  return gnode_prove(root);
}
PROOF thm cm_prologue_heights_bounded =
    cm_prove_prologue_heights_bounded();

PROOF static thm cm_prove_function_heights_bounded(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) fid (f:cm_function_d).
         cm_function_wf p
           (inth fid (cm_program_functions p)) ==>
         0i <= fid &&
         fid < ilength (cm_program_functions p) ==>
         cm_heights_le (cm_stack_bound_model p)
           (cm_function_heights p fid f)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  term actual =
      `inth (fid:int)
         (cm_program_functions (p:cm_program))`;
  thm function_wf = cm_matching_assumption(leaf,
      `cm_function_wf (p:cm_program) ${actual:cm_function_d}`);
  thm bounds = cm_matching_assumption(leaf,
      `0i <= (fid:int) &&
       fid < ilength
         (cm_program_functions (p:cm_program))`);
  thm arity_max = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`),
      cm_function_arity_le_max), bounds);
  thm prologue = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, actual),
      cm_prologue_heights_bounded), arity_max);
  thm function_parts = conv_rule(rewrite_conv(
      THM_LIST(get_cm_function_wf_def())), function_wf);
  thm stmt_wf = cm_pick_conjunct(function_parts,
      `cm_stmt_wf (p:cm_program) ${actual:cm_function_d}
         F (cm_function_body ${actual:cm_function_d})`);
  thm body = mp_rule(specl_rule(TERM_LIST(
      `cm_function_body ${actual:cm_function_d}`,
      `p:cm_program`, actual, `F`, `fid:int`),
      cm_stmt_heights_bounded), stmt_wf);
  thm zero = cm_stack_small_bound(`p:cm_program`, `0i`);
  thm returned = mp_rule(spec_rule(
      `cm_stack_bound_model (p:cm_program)`,
      cm_return_heights_bounded),
      spec_rule(`p:cm_program`, cm_stack_bound_three));
  gnode reduced = CONV_TAC(leaf,
      reduce_rewrite_conv(THM_LIST(
        prologue, body, zero, returned,
        cm_function_heights_def,
        cm_heights_le_append,
        cm_heights_le_def,
        get_theorem_by_name("APPEND"))));
  if (IS_NULL(reduced->solved)) {
    ACCEPT_TAC(reduced, taut_rule(goal_ccl(reduced->g)));
  }
  return gnode_prove(root);
}
PROOF thm cm_function_heights_bounded =
    cm_prove_function_heights_bounded();

PROOF static thm cm_prove_functions_heights_bounded(void) {
  gnode root = gnode_new_with_ccl(
      `!(functions:(cm_function_d)list).
         !(p:cm_program) fid.
         cm_typed_program p ==>
         0i <= fid ==>
         fid + ilength functions ==
           ilength (cm_program_functions p) ==>
         cm_heights_le (cm_stack_bound_model p)
           (cm_functions_heights p fid functions)`);
  gnode_list cases =
      INDUCT_TAC(root, `functions:(cm_function_d)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        cm_functions_heights_def,
        cm_heights_le_def)));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm typed = cm_matching_assumption(
        leaf, `cm_typed_program (p:cm_program)`);
    thm fid_lower = cm_matching_assumption(
        leaf, `0i <= (fid:int)`);
    thm alignment = cm_matching_assumption(leaf,
        `(fid:int) +
           ilength ((a0:cm_function_d) ::
             (a1:(cm_function_d)list)) ==
         ilength (cm_program_functions (p:cm_program))`);
    thm cons_length = apply_conversion(
        rewrite_conv(THM_LIST(
          get_theorem_by_name("ILENGTH_DEF"))),
        `ilength ((a0:cm_function_d) ::
          (a1:(cm_function_d)list))`);
    thm rest_nonnegative = ispec_rule(
        `a1:(cm_function_d)list`,
        get_theorem_by_name("ILENGTH_NONNEG"));
    thm numeric = conj_rule(conj_rule(
        fid_lower, alignment),
        conj_rule(cons_length, rest_nonnegative));
    thm fid_upper = mp_rule(int_arith_rule(mk_imp(
        concl(numeric),
        `(fid:int) <
         ilength (cm_program_functions (p:cm_program))`)),
        numeric);
    thm bounds = conj_rule(fid_lower, fid_upper);
    thm typed_parts = conv_rule(rewrite_conv(
        THM_LIST(get_cm_typed_program_def())), typed);
    thm all_functions = cm_pick_conjunct(typed_parts,
        `!(i:int).
           0i <= i ==>
           i < ilength
             (cm_program_functions (p:cm_program)) ==>
           cm_function_wf p
             (inth i (cm_program_functions p))`);
    thm function_wf = mp_rule(mp_rule(
        spec_rule(`fid:int`, all_functions),
        fid_lower), fid_upper);
    thm current = mp_rule(mp_rule(specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `a0:cm_function_d`),
        cm_function_heights_bounded),
        function_wf), bounds);
    thm next_lower = mp_rule(int_arith_rule(mk_imp(
        concl(fid_lower), `0i <= (fid:int) + 1i`)),
        fid_lower);
    thm tail_alignment = mp_rule(int_arith_rule(mk_imp(
        mk_conj(concl(alignment), concl(cons_length)),
        `((fid:int) + 1i) +
           ilength (a1:(cm_function_d)list) ==
         ilength (cm_program_functions (p:cm_program))`)),
        conj_rule(alignment, cons_length));
    thm ih = cm_matching_assumption(leaf,
        `!(p:cm_program) fid.
           cm_typed_program p ==>
           0i <= fid ==>
           fid + ilength (a1:(cm_function_d)list) ==
             ilength (cm_program_functions p) ==>
           cm_heights_le (cm_stack_bound_model p)
             (cm_functions_heights p fid a1)`);
    thm tail = mp_rule(mp_rule(mp_rule(specl_rule(TERM_LIST(
        `p:cm_program`, `(fid:int) + 1i`), ih),
        typed), next_lower), tail_alignment);
    gnode reduced = CONV_TAC(leaf,
        reduce_rewrite_conv(THM_LIST(
          current, tail,
          cm_functions_heights_def,
          cm_heights_le_append)));
    if (IS_NULL(reduced->solved)) {
      ACCEPT_TAC(reduced, taut_rule(goal_ccl(reduced->g)));
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_functions_heights_bounded =
    cm_prove_functions_heights_bounded();

PROOF static thm cm_prove_direct_codegen_bounded(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program).
         cm_wf_program p ==>
         cm_heights_le (cm_stack_bound_model p)
           (cm_codegen_direct_heights p)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm wf = cm_matching_assumption(
      leaf, `cm_wf_program (p:cm_program)`);
  thm wf_parts = conv_rule(rewrite_conv(THM_LIST(
      get_cm_wf_program_def(),
      get_cm_codegen_admissible_def())), wf);
  thm typed = cm_pick_conjunct(
      wf_parts, `cm_typed_program (p:cm_program)`);
  thm functions = mp_rule(mp_rule(mp_rule(specl_rule(TERM_LIST(
      `cm_program_functions (p:cm_program)`,
      `p:cm_program`, `0i`),
      cm_functions_heights_bounded),
      typed), int_arith_rule(`0i <= 0i`)),
      int_arith_rule(
        `0i + ilength
           (cm_program_functions (p:cm_program)) ==
         ilength (cm_program_functions p)`));
  thm prelude = mp_rule(spec_rule(
      `cm_stack_bound_model (p:cm_program)`,
      cm_prelude_heights_bounded),
      spec_rule(`p:cm_program`, cm_stack_bound_three));
  thm result = cm_heights_le_join(
      `cm_stack_bound_model (p:cm_program)`,
      `cm_prelude_heights`,
      `cm_functions_heights p 0i
         (cm_program_functions p)`,
      prelude, functions);
  gnode reduced = CONV_TAC(leaf,
      rewrite_conv(THM_LIST(
        cm_codegen_direct_heights_def)));
  ACCEPT_TAC(reduced, result);
  return gnode_prove(root);
}
PROOF thm cm_direct_codegen_bounded =
    cm_prove_direct_codegen_bounded();

PROOF static thm cm_prove_direct_codegen_edges(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program).
         cm_wf_program p ==>
         cm_stack_edges_from
           (cm_model_code p)
           (cm_codegen_direct_heights p) 0i
           (cm_model_code p)
           (cm_codegen_direct_heights p)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm wf = cm_matching_assumption(
      leaf, `cm_wf_program (p:cm_program)`);
  thm local = mp_rule(spec_rule(
      `p:cm_program`, cm_direct_codegen_local), wf);
  thm stream = spec_rule(
      `cm_codegen_direct_heights (p:cm_program)`,
      cm_identity_height_stream);
  thm result = mp_rule(specl_rule(TERM_LIST(
      `cm_model_code (p:cm_program)`,
      `p:cm_program`,
      `cm_model_code (p:cm_program)`,
      `cm_codegen_direct_heights (p:cm_program)`,
      `0i`,
      `cm_codegen_direct_heights (p:cm_program)`),
      cm_local_codegen_edges), conj_rule(stream, local));
  ACCEPT_TAC(leaf, result);
  return gnode_prove(root);
}
PROOF thm cm_direct_codegen_edges =
    cm_prove_direct_codegen_edges();

PROOF static thm cm_prove_direct_stack_certificate(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program).
         cm_wf_program p ==>
         cm_stack_certificate
           (cm_compile_model p)
           (cm_codegen_direct_heights p)
           (cm_codegen_function_entries p)
           (cm_codegen_function_arities p)
           (cm_stack_height_max
             (cm_codegen_direct_heights p))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm wf = cm_matching_assumption(
      leaf, `cm_wf_program (p:cm_program)`);
  thm object_wf = mp_rule(spec_rule(
      `p:cm_program`, get_cmc_object_wf()), wf);
  thm direct_length = spec_rule(
      `p:cm_program`, cm_direct_heights_length);
  thm code_length = spec_rule(
      `p:cm_program`, get_cm_model_code_length_exact());
  thm length = trans_rule(
      direct_length, sym_rule(code_length));
  thm entry = beta_norm(spec_rule(
      `p:cm_program`, cm_direct_target_zero));
  thm edges = mp_rule(spec_rule(
      `p:cm_program`, cm_direct_codegen_edges), wf);
  thm peak = refl_rule(
      `cm_stack_height_max
         (cm_codegen_direct_heights (p:cm_program))`);
  thm local = mp_rule(spec_rule(
      `p:cm_program`, cm_direct_codegen_local), wf);
  thm calls = mp_rule(spec_rule(
      `p:cm_program`, cm_codegen_call_sites), local);
  thm object_code = by_rewrite(
      `tvm_object_code (cm_compile_model (p:cm_program)) ==
       cm_model_code p`,
      THM_LIST(get_cm_compile_model_def(),
        get_tvm_object_code_def()));
  thm object_entry = by_rewrite(
      `tvm_object_entry (cm_compile_model (p:cm_program)) ==
       0i`,
      THM_LIST(get_cm_compile_model_def(),
        get_tvm_object_entry_def()));
  gnode reduced = CONV_TAC(leaf,
      rewrite_conv(THM_LIST(
        get_cm_stack_certificate_def(),
        object_code, object_entry)));
  CONV_TAC(reduced, reduce_rewrite_conv(THM_LIST(
      object_wf, length, entry, edges, peak, calls)));
  return gnode_prove(root);
}
PROOF thm cm_direct_stack_certificate =
    cm_prove_direct_stack_certificate();

PROOF static thm cm_prove_stack_discipline(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program).
         cm_wf_program p ==>
         cm_stack_summary
           (cm_compile_model p)
           (cm_stack_bound_model p)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm wf = cm_matching_assumption(
      leaf, `cm_wf_program (p:cm_program)`);
  thm certificate = mp_rule(spec_rule(
      `p:cm_program`, cm_direct_stack_certificate), wf);
  thm bounded = mp_rule(spec_rule(
      `p:cm_program`, cm_direct_codegen_bounded), wf);
  thm nonnegative = mp_rule(int_arith_rule(mk_imp(
      concl(spec_rule(`p:cm_program`, cm_stack_bound_three)),
      `0i <= cm_stack_bound_model (p:cm_program)`)),
      spec_rule(`p:cm_program`, cm_stack_bound_three));
  thm peak_bound = mp_rule(mp_rule(specl_rule(TERM_LIST(
      `cm_codegen_direct_heights (p:cm_program)`,
      `cm_stack_bound_model (p:cm_program)`),
      cm_heights_le_max), nonnegative), bounded);
  thm body = conj_rule(certificate, peak_bound);
  term heights =
      `cm_codegen_direct_heights (p:cm_program)`;
  term entries =
      `cm_codegen_function_entries (p:cm_program)`;
  term arities =
      `cm_codegen_function_arities (p:cm_program)`;
  term peak =
      `cm_stack_height_max
         (cm_codegen_direct_heights (p:cm_program))`;
  term exists_all =
      `?heights entries arities peak.
         cm_stack_certificate
           (cm_compile_model (p:cm_program))
           (heights:(int)list) (entries:(int)list)
           (arities:(int)list) (peak:int) &&
         peak <= cm_stack_bound_model p`;
  thm witness = exists_rule(exists_all, heights,
      exists_rule(
        `?entries arities peak.
           cm_stack_certificate
             (cm_compile_model (p:cm_program))
             ${heights:(int)list} (entries:(int)list)
             (arities:(int)list) (peak:int) &&
           peak <= cm_stack_bound_model p`,
        entries,
        exists_rule(
          `?arities peak.
             cm_stack_certificate
               (cm_compile_model (p:cm_program))
               ${heights:(int)list} ${entries:(int)list}
               (arities:(int)list) (peak:int) &&
             peak <= cm_stack_bound_model p`,
          arities,
          exists_rule(
            `?peak.
               cm_stack_certificate
                 (cm_compile_model (p:cm_program))
                 ${heights:(int)list} ${entries:(int)list}
                 ${arities:(int)list} (peak:int) &&
               peak <= cm_stack_bound_model p`,
            peak, body))));
  gnode reduced = CONV_TAC(leaf,
      rewrite_conv(THM_LIST(
        get_cm_stack_summary_def())));
  ACCEPT_TAC(reduced, witness);
  return gnode_prove(root);
}
PROOF thm cmc_stack_discipline =
    cm_prove_stack_discipline();
