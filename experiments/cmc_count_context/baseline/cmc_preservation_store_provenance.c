#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_store_memory.h"
#require "cmc_preservation_store_memory.c"
#include "cmc_preservation_store_provenance.h"

PROOF static size_t _cmc_preservation_store_provenance_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_prove_value_number_state_store(void) {
  gnode root = gnode_new_with_ccl(
      `!(ty:cm_type) (ptr:cm_value) (stored:cm_value)
         (st:cm_src_state) (v:cm_value).
         cm_value_number (cm_state_store ty ptr stored st) v ==
         cm_value_number st v`);
  gnode with_type = GEN_TAC(root, "ty");
  gnode with_ptr = GEN_TAC(with_type, "ptr");
  gnode with_stored = GEN_TAC(with_ptr, "stored");
  gnode with_state = GEN_TAC(with_stored, "st");
  gnode_list cases = INDUCT_TAC(with_state, `v:cm_value`);
  thm_list rules = get_cm_state_core_defs();
  vector_add(&rules, get_cm_state_store_def());
  vector_add(&rules, get_cm_value_number_def());
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode leaf = AUTO_INTROS_TAC(cases[i]);
    CONV_TAC(leaf, reduce_rewrite_conv(rules));
  }
  return gnode_prove(root);
}
PROOF thm cm_value_number_state_store =
    cm_prove_value_number_state_store();

PROOF static thm cm_prove_pointer_not_char(void) {
  gnode root = gnode_new_with_ccl(
      `!(ty:cm_type).
         cm_is_pointer ty ==> ~((ty:cm_type) == CMCharTy)`);
  gnode_list cases = INDUCT_TAC(root, `ty:cm_type`);
  thm distinct = get_datatype_distinctness("cm_type");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    CONV_TAC(cases[i], reduce_rewrite_conv(THM_LIST(
        get_cm_is_pointer_def(), distinct)));
  }
  return gnode_prove(root);
}
PROOF static thm cm_pointer_not_char =
    cm_prove_pointer_not_char();

PROOF static thm cm_prove_store_width_positive_local(void) {
  gnode root = gnode_new_with_ccl(
      `!(ty:cm_type). 0i < cm_store_width ty`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list cases = BOOL_CASES_TAC(
      leaf, `(ty:cm_type) == CMCharTy`, "Hchar");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    CONV_WITH_ASMP_TAC(cases[i], reduce_rewrite_conv,
        THM_LIST(get_cm_store_width_def()));
  }
  return gnode_prove(root);
}
PROOF static thm cm_store_width_positive_local =
    cm_prove_store_width_positive_local();

PROOF static thm cm_prove_stored_provenance_store_sim(void) {
  gnode root = gnode_new_with_ccl(
      `!(ty:cm_type) (ptr:cm_value) (v:cm_value)
         (st:cm_src_state) (vmem:int->int).
         cm_stored_provenance_sim st vmem ==>
         cm_stored_provenance_sim
           (cm_state_store ty ptr v st)
           (cm_store_mem ty (cm_value_number st ptr)
             (cm_value_number st (cm_convert_value st ty v)) vmem)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm old_simulation = assume_rule(
      `cm_stored_provenance_sim (st:cm_src_state) (vmem:int->int)`);
  thm old_pointwise = conv_rule(rewrite_conv(THM_LIST(
      cm_stored_provenance_sim_def)), old_simulation);
  thm_list rules = get_cm_state_core_defs();
  vector_add(&rules, cm_stored_provenance_sim_def);
  vector_add(&rules, get_cm_state_store_def());
  vector_add(&rules, get_cm_mark_init_def());
  vector_add(&rules, get_cm_clear_tagged_def());
  vector_add(&rules, cm_value_number_state_store);
  vector_add(&rules, cm_live_address_def);
  thm store_positive =
      spec_rule(`ty:cm_type`, cm_store_width_positive_local);
  vector_add(&rules, store_positive);
  gnode opened = CONV_TAC(leaf, reduce_rewrite_conv(rules));
  gnode at_address = AUTO_INTROS_TAC(opened);
  gnode_list pointer_cases = BOOL_CASES_TAC(
      at_address, `cm_is_pointer (ty:cm_type)`, "hpointer");
  term base =
      `cm_value_number (st:cm_src_state) (ptr:cm_value)`;
  term number =
      `cm_value_number (st:cm_src_state)
        (cm_convert_value st (ty:cm_type) (v:cm_value))`;
  term raw_new_tag =
      `(if cm_is_pointer (ty:cm_type)
        then (\a:int.
          (a == ${base:int} && ~(${number:int} == 0i)) ||
          (cm_state_tagged (st:cm_src_state) a &&
           ~(a < ${base:int} + 8i && ${base:int} < a + 8i)))
        else (\a:int.
          cm_state_tagged (st:cm_src_state) a &&
          ~(a < ${base:int} + cm_store_width (ty:cm_type) &&
            ${base:int} < a + 8i))) (addr:int)`;
  thm raw_tagged =
      cm_store_normalized_assumption(at_address, raw_new_tag, rules);
  thm live = cm_store_normalized_assumption(
      at_address,
      `cm_live_address (st:cm_src_state) (addr:int)`,
      rules);
  thm is_pointer = assume_rule(`cm_is_pointer (ty:cm_type)`);
  thm not_char = mp_rule(
      spec_rule(`ty:cm_type`, cm_pointer_not_char), is_pointer);
  gnode_list address_cases = BOOL_CASES_TAC(
      pointer_cases[0], `(addr:int) == ${base:int}`, "hatbase");
  {
    thm at_base = assume_rule(`(addr:int) == ${base:int}`);
    thm signed_range = specl_rule(TERM_LIST(
        `st:cm_src_state`,
        `cm_convert_value (st:cm_src_state)
          (ty:cm_type) (v:cm_value)`),
        get_cm_value_number_signed_bridge());
    thm wrap_fixed = mp_rule(spec_rule(number,
        get_tower_wrap64_fixed()), signed_range);
    gnode reduced = CONV_TAC(address_cases[0],
        reduce_rewrite_conv(THM_LIST(
          is_pointer, at_base, not_char,
          get_cm_store_width_def(), get_cm_store_mem_def(),
          get_tower_getw_setw(), wrap_fixed)));
    ACCEPT_TAC(reduced, int_arith_rule(goal_ccl(reduced->g)));
  }
  {
    thm not_at_base =
        assume_rule(`~((addr:int) == ${base:int})`);
    thm surviving = conv_rule(reduce_rewrite_conv(THM_LIST(
        is_pointer, not_at_base)), raw_tagged);
    thm old_tagged = conjunct1_rule(surviving);
    thm no_overlap = conjunct2_rule(surviving);
    thm old_parts = mp_rule(spec_rule(`addr:int`, old_pointwise),
        conj_rule(old_tagged, live));
    thm raw_disjoint = mp_rule(int_arith_rule(mk_imp(
        concl(no_overlap),
        `(${base:int} + 8i <= (addr:int) ||
          addr + 8i <= ${base:int})`)), no_overlap);
    term disjoint_term =
        `cm_range_disjoint ${base:int}
           (cm_store_width (ty:cm_type)) (addr:int) 8i`;
    thm disjoint = eq_mp_rule(sym_rule(apply_conversion(
        rewrite_conv(THM_LIST(cm_range_disjoint_def,
          get_cm_store_width_def(), not_char)),
        disjoint_term)), raw_disjoint);
    thm unchanged = mp_rule(specl_rule(TERM_LIST(
        `ty:cm_type`, base, number, `vmem:int->int`, `addr:int`),
        cm_store_mem_word_other), disjoint);
    thm result = conj_rule(
        disj1_rule(conjunct1_rule(old_parts),
          `${base:int} <= (addr:int) &&
           addr < ${base:int} + cm_store_width (ty:cm_type)`),
        trans_rule(unchanged, conjunct2_rule(old_parts)));
    thm normalized = apply_conversion(reduce_rewrite_conv(THM_LIST(
        is_pointer, not_at_base)), goal_ccl(address_cases[1]->g));
    ACCEPT_TAC(address_cases[1],
        eq_mp_rule(sym_rule(normalized), result));
  }
  {
    thm not_pointer =
        assume_rule(`~(cm_is_pointer (ty:cm_type))`);
    thm surviving = conv_rule(reduce_rewrite_conv(THM_LIST(
        not_pointer)), raw_tagged);
    thm old_tagged = conjunct1_rule(surviving);
    thm no_overlap = conjunct2_rule(surviving);
    thm old_parts = mp_rule(spec_rule(`addr:int`, old_pointwise),
        conj_rule(old_tagged, live));
    thm raw_disjoint = mp_rule(int_arith_rule(mk_imp(
        concl(no_overlap),
        `(${base:int} + cm_store_width (ty:cm_type) <= (addr:int) ||
          addr + 8i <= ${base:int})`)), no_overlap);
    term disjoint_term =
        `cm_range_disjoint ${base:int}
           (cm_store_width (ty:cm_type)) (addr:int) 8i`;
    thm disjoint = eq_mp_rule(sym_rule(apply_conversion(
        rewrite_conv(THM_LIST(cm_range_disjoint_def)),
        disjoint_term)), raw_disjoint);
    thm unchanged = mp_rule(specl_rule(TERM_LIST(
        `ty:cm_type`, base, number, `vmem:int->int`, `addr:int`),
        cm_store_mem_word_other), disjoint);
    thm result = conj_rule(
        disj1_rule(conjunct1_rule(old_parts),
          `${base:int} <= (addr:int) &&
           addr < ${base:int} + cm_store_width (ty:cm_type)`),
        trans_rule(unchanged, conjunct2_rule(old_parts)));
    thm normalized = apply_conversion(reduce_rewrite_conv(THM_LIST(
        not_pointer)), goal_ccl(pointer_cases[1]->g));
    ACCEPT_TAC(pointer_cases[1],
        eq_mp_rule(sym_rule(normalized), result));
  }
  return gnode_prove(root);
}
PROOF thm cm_stored_provenance_store_sim =
    cm_prove_stored_provenance_store_sim();

PROOF thm get_cm_value_number_state_store(void) {
  return cm_value_number_state_store;
}
PROOF thm get_cm_stored_provenance_store_sim(void) {
  return cm_stored_provenance_store_sim;
}

PROOF static int cmc_preservation_store_provenance_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_store_provenance_axioms_before,
      "cmc_preservation_store_provenance introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_store_provenance_final_checks =
    cmc_preservation_store_provenance_final_checks();
