#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_lang.h"
#include "cmc_preservation_type_ready.h"
#include "cmc_preservation_type_args.h"

#require "cmc_preservation_type_value.c"

PROOF static size_t _cmc_preservation_type_args_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_args_pick_conjunct(thm fact, term wanted) {
  if (alpha_compare(concl(fact), wanted) == 0) return fact;
  if (is_conj(concl(fact))) {
    thm left = cm_args_pick_conjunct(conjunct1_rule(fact), wanted);
    if (!IS_NULL(left)) return left;
    return cm_args_pick_conjunct(conjunct2_rule(fact), wanted);
  }
  return empty_theorem;
}

PROOF static thm cm_prove_args_wf_slots_nonempty(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (f:cm_function_d)
         (args:(cm_expr)list) (slots:(cm_slot_d)list).
         cm_args_wf p f args slots ==>
         ~(args == []) ==>
         ~(slots == [])`);
  gnode_list cases = INDUCT_TAC(root, `args:(cm_expr)list`);
  for (size_t i = 0; i < vector_size(cases); ++i) {
    thm view = apply_conversion(reduce_rewrite_conv(THM_LIST(
        get_cm_args_wf_def(), get_theorem_by_name("NOT_CONS_NIL"),
        get_theorem_by_name("HD"), get_theorem_by_name("TL"))),
        goal_ccl(cases[i]->g));
    ACCEPT_TAC(cases[i], eq_mp_rule(sym_rule(view),
        taut_rule(rhs_of(view))));
  }
  return gnode_prove(root);
}
PROOF thm cm_args_wf_slots_nonempty =
    cm_prove_args_wf_slots_nonempty();

PROOF static thm cm_prove_args_wf_head_convertible(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (f:cm_function_d)
         (args:(cm_expr)list) (slots:(cm_slot_d)list).
         cm_args_wf p f args slots ==>
         ~(args == []) ==>
         cm_expr_convertible (HD args) (cm_slot_ty (HD slots))`);
  gnode_list cases = INDUCT_TAC(root, `args:(cm_expr)list`);
  for (size_t i = 0; i < vector_size(cases); ++i) {
    thm view = apply_conversion(reduce_rewrite_conv(THM_LIST(
        get_cm_args_wf_def(), get_theorem_by_name("NOT_CONS_NIL"),
        get_theorem_by_name("HD"), get_theorem_by_name("TL"))),
        goal_ccl(cases[i]->g));
    ACCEPT_TAC(cases[i], eq_mp_rule(sym_rule(view),
        taut_rule(rhs_of(view))));
  }
  return gnode_prove(root);
}
PROOF static thm cm_args_wf_head_convertible =
    cm_prove_args_wf_head_convertible();


PROOF static thm cm_prove_args_wf_tails(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (f:cm_function_d)
         (args:(cm_expr)list) (slots:(cm_slot_d)list).
         cm_args_wf p f args slots ==>
         ~(args == []) ==>
         cm_args_wf p f (TL args) (TL slots)`);
  gnode_list cases = INDUCT_TAC(root, `args:(cm_expr)list`);
  for (size_t i = 0; i < vector_size(cases); ++i) {
    thm view = apply_conversion(reduce_rewrite_conv(THM_LIST(
        get_cm_args_wf_def(), get_theorem_by_name("NOT_CONS_NIL"),
        get_theorem_by_name("HD"), get_theorem_by_name("TL"))),
        goal_ccl(cases[i]->g));
    ACCEPT_TAC(cases[i], eq_mp_rule(sym_rule(view),
        taut_rule(rhs_of(view))));
  }
  return gnode_prove(root);
}
PROOF static thm cm_args_wf_tails = cm_prove_args_wf_tails();

PROOF static thm cm_args_apply_imp_chain(
    term conclusion, thm_list facts) {
  term_list premises = vector_create();
  for (size_t i = 0; i < vector_size(facts); ++i) {
    vector_add(&premises, concl(facts[i]));
  }
  thm result = taut_rule(imp_chain(premises, conclusion));
  for (size_t i = 0; i < vector_size(facts); ++i) {
    result = mp_rule(result, facts[i]);
  }
  return result;
}

PROOF static thm cm_prove_arg_progress_extend(void) {
  gnode root = gnode_new_with_ccl(
      `!(done:(cm_value)list). !p f all_args slots rest.
         !(incoming:cm_value).
         cm_args_wf (p:cm_program) (f:cm_function_d)
           (all_args:(cm_expr)list) (slots:(cm_slot_d)list) ==>
         cm_arg_progress_type_ready all_args slots done
           (rest:(cm_expr)list) ==>
         ~(rest == []) ==>
         cm_value_convertible_to incoming
           (cm_arg_next_type slots done) ==>
         cm_arg_progress_type_ready all_args slots
           (done ++ [incoming]) (TL rest)`);
  gnode_list cases = INDUCT_TAC(root, `done:(cm_value)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm args_wf = assume_rule(
        `cm_args_wf (p:cm_program) (f:cm_function_d)
          (all_args:(cm_expr)list) (slots:(cm_slot_d)list)`);
    thm progress = conv_rule(reduce_rewrite_conv(THM_LIST(
        get_cm_arg_progress_type_ready_def())), assume_rule(
        `cm_arg_progress_type_ready
          (all_args:(cm_expr)list) (slots:(cm_slot_d)list)
          ([]:(cm_value)list) (rest:(cm_expr)list)`));
    thm all_nonempty = cm_args_pick_conjunct(progress,
        `~((all_args:(cm_expr)list) == [])`);
    thm slots_nonempty = cm_args_pick_conjunct(progress,
        `~((slots:(cm_slot_d)list) == [])`);
    thm tail_equal = progress;
    while (is_conj(concl(tail_equal))) {
      tail_equal = conjunct2_rule(tail_equal);
    }
    thm tail_wf = mp_rule(mp_rule(specl_rule(TERM_LIST(
        `p:cm_program`, `f:cm_function_d`,
        `all_args:(cm_expr)list`, `slots:(cm_slot_d)list`),
        cm_args_wf_tails), args_wf), all_nonempty);
    thm rest_nonempty = assume_rule(
        `~((rest:(cm_expr)list) == [])`);
    thm tail_nonempty_view = beta_norm(ap_term_rule(
        `\xs:(cm_expr)list. ~(xs == [])`, tail_equal));
    thm tail_all_nonempty = eq_mp_rule(
        sym_rule(tail_nonempty_view), rest_nonempty);
    thm tail_slots_nonempty = mp_rule(mp_rule(specl_rule(TERM_LIST(
        `p:cm_program`, `f:cm_function_d`,
        `TL (all_args:(cm_expr)list)`,
        `TL (slots:(cm_slot_d)list)`),
        cm_args_wf_slots_nonempty), tail_wf), tail_all_nonempty);
    thm next_tail_equal = beta_norm(ap_term_rule(
        `\xs:(cm_expr)list. TL xs`, tail_equal));
    thm convertible = conv_rule(reduce_rewrite_conv(THM_LIST(
        get_cm_arg_next_type_def())), assume_rule(
        `cm_value_convertible_to (incoming:cm_value)
          (cm_arg_next_type (slots:(cm_slot_d)list) [])`));
    thm view = apply_conversion(reduce_rewrite_conv(THM_LIST(
        get_cm_arg_progress_type_ready_def(),
        get_cm_arg_next_type_def(), get_theorem_by_name("APPEND"),
        get_theorem_by_name("HD"), get_theorem_by_name("TL"))),
        goal_ccl(leaf->g));
    thm ready = cm_args_apply_imp_chain(rhs_of(view), THM_LIST(
        all_nonempty, slots_nonempty, convertible,
        tail_all_nonempty, tail_slots_nonempty, next_tail_equal));
    ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(view), ready));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    labeled_term_list assumptions = goal_lasmps(leaf->g);
    thm induction = empty_theorem;
    for (size_t i = 0; i < vector_size(assumptions); ++i) {
      if (is_forall(assumptions[i].tm)) {
        induction = assume_rule(assumptions[i].tm);
        break;
      }
    }
    thm args_wf = assume_rule(
        `cm_args_wf (p:cm_program) (f:cm_function_d)
          (all_args:(cm_expr)list) (slots:(cm_slot_d)list)`);
    thm progress = conv_rule(reduce_rewrite_conv(THM_LIST(
        get_cm_arg_progress_type_ready_def())), assume_rule(
        `cm_arg_progress_type_ready
          (all_args:(cm_expr)list) (slots:(cm_slot_d)list)
          ((a0:cm_value) :: (a1:(cm_value)list))
          (rest:(cm_expr)list)`));
    thm all_nonempty = cm_args_pick_conjunct(progress,
        `~((all_args:(cm_expr)list) == [])`);
    thm slots_nonempty = cm_args_pick_conjunct(progress,
        `~((slots:(cm_slot_d)list) == [])`);
    thm head_convertible = cm_args_pick_conjunct(progress,
        `cm_value_convertible_to (a0:cm_value)
          (cm_slot_ty (HD (slots:(cm_slot_d)list)))`);
    thm recursive_progress = progress;
    while (is_conj(concl(recursive_progress))) {
      recursive_progress = conjunct2_rule(recursive_progress);
    }
    thm tail_wf = mp_rule(mp_rule(specl_rule(TERM_LIST(
        `p:cm_program`, `f:cm_function_d`,
        `all_args:(cm_expr)list`, `slots:(cm_slot_d)list`),
        cm_args_wf_tails), args_wf), all_nonempty);
    thm recursive_convertible = conv_rule(
        reduce_rewrite_conv(THM_LIST(get_cm_arg_next_type_def())),
        assume_rule(
          `cm_value_convertible_to (incoming:cm_value)
            (cm_arg_next_type (slots:(cm_slot_d)list)
              ((a0:cm_value) :: (a1:(cm_value)list)))`));
    thm recursive_ready = specl_rule(TERM_LIST(
        `p:cm_program`, `f:cm_function_d`,
        `TL (all_args:(cm_expr)list)`,
        `TL (slots:(cm_slot_d)list)`,
        `rest:(cm_expr)list`, `incoming:cm_value`), induction);
    recursive_ready = mp_rule(recursive_ready, tail_wf);
    recursive_ready = mp_rule(recursive_ready, recursive_progress);
    recursive_ready = mp_rule(recursive_ready, assume_rule(
        `~((rest:(cm_expr)list) == [])`));
    recursive_ready = mp_rule(recursive_ready, recursive_convertible);
    thm view = apply_conversion(reduce_rewrite_conv(THM_LIST(
        get_cm_arg_progress_type_ready_def(),
        get_cm_arg_next_type_def(), get_theorem_by_name("APPEND"),
        get_theorem_by_name("HD"), get_theorem_by_name("TL"))),
        goal_ccl(leaf->g));
    thm ready = cm_args_apply_imp_chain(rhs_of(view), THM_LIST(
        all_nonempty, slots_nonempty,
        head_convertible, recursive_ready));
    ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(view), ready));
  }
  return gnode_prove(root);
}
PROOF thm cm_arg_progress_extend =
    cm_prove_arg_progress_extend();

PROOF static thm cm_prove_arg_progress_next_expr(void) {
  gnode root = gnode_new_with_ccl(
      `!(done:(cm_value)list). !p f all_args slots rest.
         !(incoming:cm_value).
         cm_args_wf (p:cm_program) (f:cm_function_d)
           (all_args:(cm_expr)list) (slots:(cm_slot_d)list) ==>
         cm_arg_progress_type_ready all_args slots done
           (rest:(cm_expr)list) ==>
         ~(rest == []) ==>
         cm_value_convertible_to incoming
           (cm_arg_next_type slots done) ==>
         cm_expr_convertible (HD rest)
           (cm_arg_next_type slots (done ++ [incoming]))`);
  gnode_list cases = INDUCT_TAC(root, `done:(cm_value)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm args_wf = assume_rule(
        `cm_args_wf (p:cm_program) (f:cm_function_d)
          (all_args:(cm_expr)list) (slots:(cm_slot_d)list)`);
    thm progress = conv_rule(reduce_rewrite_conv(THM_LIST(
        get_cm_arg_progress_type_ready_def())), assume_rule(
        `cm_arg_progress_type_ready
          (all_args:(cm_expr)list) (slots:(cm_slot_d)list)
          ([]:(cm_value)list) (rest:(cm_expr)list)`));
    thm all_nonempty = cm_args_pick_conjunct(progress,
        `~((all_args:(cm_expr)list) == [])`);
    thm tail_equal = progress;
    while (is_conj(concl(tail_equal))) {
      tail_equal = conjunct2_rule(tail_equal);
    }
    thm tail_wf = mp_rule(mp_rule(specl_rule(TERM_LIST(
        `p:cm_program`, `f:cm_function_d`,
        `all_args:(cm_expr)list`, `slots:(cm_slot_d)list`),
        cm_args_wf_tails), args_wf), all_nonempty);
    tail_wf = conv_rule(rewrite_conv(THM_LIST(tail_equal)), tail_wf);
    thm rest_nonempty = assume_rule(
        `~((rest:(cm_expr)list) == [])`);
    thm convertible = mp_rule(mp_rule(specl_rule(TERM_LIST(
        `p:cm_program`, `f:cm_function_d`,
        `rest:(cm_expr)list`, `TL (slots:(cm_slot_d)list)`),
        cm_args_wf_head_convertible), tail_wf), rest_nonempty);
    thm target_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
        get_cm_arg_next_type_def(), get_theorem_by_name("APPEND"),
        get_theorem_by_name("HD"), get_theorem_by_name("TL"))),
        goal_ccl(leaf->g));
    ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), convertible));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    labeled_term_list assumptions = goal_lasmps(leaf->g);
    thm induction = empty_theorem;
    for (size_t i = 0; i < vector_size(assumptions); ++i) {
      if (is_forall(assumptions[i].tm)) {
        induction = assume_rule(assumptions[i].tm);
        break;
      }
    }
    thm args_wf = assume_rule(
        `cm_args_wf (p:cm_program) (f:cm_function_d)
          (all_args:(cm_expr)list) (slots:(cm_slot_d)list)`);
    thm progress = conv_rule(reduce_rewrite_conv(THM_LIST(
        get_cm_arg_progress_type_ready_def())), assume_rule(
        `cm_arg_progress_type_ready
          (all_args:(cm_expr)list) (slots:(cm_slot_d)list)
          ((a0:cm_value) :: (a1:(cm_value)list))
          (rest:(cm_expr)list)`));
    thm all_nonempty = cm_args_pick_conjunct(progress,
        `~((all_args:(cm_expr)list) == [])`);
    thm recursive_progress = progress;
    while (is_conj(concl(recursive_progress))) {
      recursive_progress = conjunct2_rule(recursive_progress);
    }
    thm tail_wf = mp_rule(mp_rule(specl_rule(TERM_LIST(
        `p:cm_program`, `f:cm_function_d`,
        `all_args:(cm_expr)list`, `slots:(cm_slot_d)list`),
        cm_args_wf_tails), args_wf), all_nonempty);
    thm recursive_convertible = conv_rule(
        reduce_rewrite_conv(THM_LIST(get_cm_arg_next_type_def())),
        assume_rule(
          `cm_value_convertible_to (incoming:cm_value)
            (cm_arg_next_type (slots:(cm_slot_d)list)
              ((a0:cm_value) :: (a1:(cm_value)list)))`));
    thm recursive_ready = specl_rule(TERM_LIST(
        `p:cm_program`, `f:cm_function_d`,
        `TL (all_args:(cm_expr)list)`,
        `TL (slots:(cm_slot_d)list)`,
        `rest:(cm_expr)list`, `incoming:cm_value`), induction);
    recursive_ready = mp_rule(recursive_ready, tail_wf);
    recursive_ready = mp_rule(recursive_ready, recursive_progress);
    recursive_ready = mp_rule(recursive_ready, assume_rule(
        `~((rest:(cm_expr)list) == [])`));
    recursive_ready = mp_rule(recursive_ready, recursive_convertible);
    thm target_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
        get_cm_arg_next_type_def(), get_theorem_by_name("APPEND"),
        get_theorem_by_name("HD"), get_theorem_by_name("TL"))),
        goal_ccl(leaf->g));
    ACCEPT_TAC(leaf,
        eq_mp_rule(sym_rule(target_view), recursive_ready));
  }
  return gnode_prove(root);
}
PROOF thm cm_arg_progress_next_expr =
    cm_prove_arg_progress_next_expr();


PROOF static int cmc_preservation_type_args_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_type_args_axioms_before,
      "argument type proofs introduced axioms");
  ENSURE_COND(vector_size(hyp(cm_args_wf_slots_nonempty)) == 0 &&
      vector_size(hyp(cm_args_wf_head_convertible)) == 0,
      "argument shape theorem is not closed");
  ENSURE_COND(vector_size(hyp(cm_arg_progress_extend)) == 0 &&
      vector_size(hyp(cm_arg_progress_next_expr)) == 0,
      "argument progress theorem is not closed");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_type_args_checks =
    cmc_preservation_type_args_final_checks();
