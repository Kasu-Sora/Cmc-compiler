#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_machine_load.h"
#require "cmc_preservation_machine_load.c"
#include "cmc_preservation_store_memory.h"

PROOF static size_t _cmc_preservation_store_memory_axioms_before =
    vector_size(get_all_axioms());

PROOF thm cm_range_disjoint_def = new_fun_definition(
    `cm_range_disjoint (left:int) (left_width:int)
       (right:int) (right_width:int) : bool =
       (left + left_width <= right ||
        right + right_width <= left)`);
PROOF static int _e_cm_range_disjoint =
    cst_add_const_to_header(`cm_range_disjoint`);

PROOF static thm cm_prove_store_mem_byte_same(void) {
  gnode root = gnode_new_with_ccl(
      `!(ty:cm_type) (base:int) (n:int) (left:int->int)
         (right:int->int) (addr:int).
         base <= addr ==>
         addr < base + cm_store_width ty ==>
         tower_getb (cm_store_mem ty base n left) addr ==
         tower_getb (cm_store_mem ty base n right) addr`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list type_cases = BOOL_CASES_TAC(
      leaf, `(ty:cm_type) == CMCharTy`, "hchar");
  thm is_char = assume_rule(`(ty:cm_type) == CMCharTy`);
  thm char_upper = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_store_width_def(), is_char)),
      assume_rule(
        `(addr:int) < base + cm_store_width (ty:cm_type)`));
  thm at_base = mp_rule(mp_rule(int_arith_rule(
      `(base:int) <= (addr:int) ==> addr < base + 1i ==>
       addr == base`),
      assume_rule(`(base:int) <= (addr:int)`)), char_upper);
  ACCEPT_TAC(type_cases[0], eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_store_width_def(), get_cm_store_mem_def(),
        get_tower_getb_def(), get_tower_setb_def(), is_char, at_base)),
      goal_ccl(type_cases[0]->g))));
  gnode current = type_cases[1];
  term offsets[8] = {
      `0i`, `1i`, `2i`, `3i`, `4i`, `5i`, `6i`, `7i`};
  const char *labels[8] = {
      "hoffset0", "hoffset1", "hoffset2", "hoffset3",
      "hoffset4", "hoffset5", "hoffset6", "hoffset7"};
  for (int offset = 0; offset < 8; ++offset) {
    term equality = mk_eq(`addr:int`, mk_binop(`(+):int->int->int`,
        `base:int`, offsets[offset]));
    gnode_list address_cases = BOOL_CASES_TAC(
        current, equality, labels[offset]);
    thm at_offset = assume_rule(equality);
    ACCEPT_TAC(address_cases[0], eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          get_cm_store_width_def(), get_cm_store_mem_def(),
          get_tower_getb_def(), get_tower_setw_def(),
          assume_rule(`~((ty:cm_type) == CMCharTy)`), at_offset)),
        goal_ccl(address_cases[0]->g))));
    current = address_cases[1];
  }
  thm upper = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_store_width_def(),
      assume_rule(`~((ty:cm_type) == CMCharTy)`))),
      assume_rule(
        `(addr:int) < base + cm_store_width (ty:cm_type)`));
  thm impossible = int_arith_rule(
      `(base:int) <= (addr:int) ==>
       addr < base + 8i ==>
       ~(addr == base + 0i) ==> ~(addr == base + 1i) ==>
       ~(addr == base + 2i) ==> ~(addr == base + 3i) ==>
       ~(addr == base + 4i) ==> ~(addr == base + 5i) ==>
       ~(addr == base + 6i) ==> ~(addr == base + 7i) ==> F`);
  impossible = mp_rule(impossible,
      assume_rule(`(base:int) <= (addr:int)`));
  impossible = mp_rule(impossible, upper);
  for (int offset = 0; offset < 8; ++offset) {
    term inequality = mk_not(mk_eq(`addr:int`,
        mk_binop(`(+):int->int->int`, `base:int`, offsets[offset])));
    impossible = mp_rule(impossible, assume_rule(inequality));
  }
  CONTR_TAC(current, impossible);
  return gnode_prove(root);
}
PROOF thm cm_store_mem_byte_same =
    cm_prove_store_mem_byte_same();

PROOF static thm cm_prove_store_mem_byte_other(void) {
  gnode root = gnode_new_with_ccl(
      `!(ty:cm_type) (base:int) (n:int) (mem:int->int) (addr:int).
         ~(base <= addr && addr < base + cm_store_width ty) ==>
         tower_getb (cm_store_mem ty base n mem) addr ==
         tower_getb mem addr`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list type_cases = BOOL_CASES_TAC(
      leaf, `(ty:cm_type) == CMCharTy`, "hchar");
  thm char_outside = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_store_width_def(),
      assume_rule(`(ty:cm_type) == CMCharTy`))),
      assume_rule(
        `~((base:int) <= (addr:int) &&
           addr < base + cm_store_width (ty:cm_type))`));
  thm char_other = mp_rule(int_arith_rule(
      `~((base:int) <= (addr:int) && addr < base + 1i) ==>
       ~(addr == base)`), char_outside);
  ACCEPT_TAC(type_cases[0], eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_store_mem_def(), get_tower_getb_def(),
        get_tower_setb_def(),
        assume_rule(`(ty:cm_type) == CMCharTy`), char_other)),
      goal_ccl(type_cases[0]->g))));
  thm word_outside = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_store_width_def(),
      assume_rule(`~((ty:cm_type) == CMCharTy)`))),
      assume_rule(
        `~((base:int) <= (addr:int) &&
           addr < base + cm_store_width (ty:cm_type))`));
  thm word_other = mp_rule(int_arith_rule(
      `~((base:int) <= (addr:int) && addr < base + 8i) ==>
       ~(addr == base + 0i) && ~(addr == base + 1i) &&
       ~(addr == base + 2i) && ~(addr == base + 3i) &&
       ~(addr == base + 4i) && ~(addr == base + 5i) &&
       ~(addr == base + 6i) && ~(addr == base + 7i)`),
      word_outside);
  ACCEPT_TAC(type_cases[1], eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_store_mem_def(), get_tower_getb_def(),
        get_tower_setw_def(),
        assume_rule(`~((ty:cm_type) == CMCharTy)`), word_other)),
      goal_ccl(type_cases[1]->g))));
  return gnode_prove(root);
}
PROOF thm cm_store_mem_byte_other =
    cm_prove_store_mem_byte_other();

PROOF static thm cm_prove_store_mem_word_other(void) {
  gnode root = gnode_new_with_ccl(
      `!(ty:cm_type) (base:int) (n:int) (mem:int->int)
         (word_addr:int).
         cm_range_disjoint base (cm_store_width ty) word_addr 8i ==>
         tower_getw (cm_store_mem ty base n mem) word_addr ==
         tower_getw mem word_addr`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm disjoint = conv_rule(rewrite_conv(THM_LIST(
      cm_range_disjoint_def)), assume_rule(
      `cm_range_disjoint (base:int)
         (cm_store_width (ty:cm_type)) (word_addr:int) 8i`));
  thm_list bytes = THM_LIST();
  term offsets[8] = {
      `0i`, `1i`, `2i`, `3i`, `4i`, `5i`, `6i`, `7i`};
  for (int offset = 0; offset < 8; ++offset) {
    term addr = mk_binop(`(+):int->int->int`,
        `word_addr:int`, offsets[offset]);
    term outside_goal =
        `~((base:int) <= ${addr:int} &&
           ${addr:int} < base + cm_store_width (ty:cm_type))`;
    thm outside = mp_rule(int_arith_rule(mk_imp(
        concl(disjoint), outside_goal)), disjoint);
    vector_add(&bytes, mp_rule(specl_rule(TERM_LIST(
        `ty:cm_type`, `base:int`, `n:int`, `mem:int->int`, addr),
        cm_store_mem_byte_other), outside));
  }
  vector_add(&bytes, get_tower_getw_def());
  ACCEPT_TAC(leaf, eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(bytes), goal_ccl(leaf->g))));
  return gnode_prove(root);
}
PROOF thm cm_store_mem_word_other =
    cm_prove_store_mem_word_other();

PROOF static thm cm_prove_live_address_store(void) {
  gnode root = gnode_new_with_ccl(
      `!(ty:cm_type) (ptr:cm_value) (v:cm_value)
         (st:cm_src_state) (addr:int).
         cm_live_address (cm_state_store ty ptr v st) addr <=>
         cm_live_address st addr`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm_list rules = get_cm_state_core_defs();
  vector_add(&rules, cm_live_address_def);
  vector_add(&rules, get_cm_state_store_def());
  ACCEPT_TAC(leaf, eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(rules), goal_ccl(leaf->g))));
  return gnode_prove(root);
}
PROOF thm cm_live_address_store =
    cm_prove_live_address_store();

PROOF static bool cm_store_has_conjunct(
    const term tree, const term wanted) {
  if (alpha_compare(tree, wanted) == 0) return true;
  if (!is_conj(tree)) return false;
  dest_conj_results parts = dest_conj(tree);
  return cm_store_has_conjunct(parts.tm1, wanted) ||
      cm_store_has_conjunct(parts.tm2, wanted);
}

PROOF static thm cm_store_pick_conjunct(
    const thm fact, const term wanted) {
  if (alpha_compare(concl(fact), wanted) == 0) return fact;
  dest_conj_results parts = dest_conj(concl(fact));
  return cm_store_has_conjunct(parts.tm1, wanted)
      ? cm_store_pick_conjunct(conjunct1_rule(fact), wanted)
      : cm_store_pick_conjunct(conjunct2_rule(fact), wanted);
}

PROOF thm cm_store_normalized_assumption(
    const gnode leaf, const term wanted, const thm_list rules) {
  thm wanted_normalized =
      apply_conversion(reduce_rewrite_conv(rules), wanted);
  term normalized_conclusion = rhs_of(wanted_normalized);
  labeled_term_list assumptions = goal_lasmps(leaf->g);
  for (size_t i = 0; i < vector_size(assumptions); ++i) {
    thm direct = assume_rule(assumptions[i].tm);
    thm normalized =
        conv_rule(reduce_rewrite_conv(rules), direct);
    if (cm_store_has_conjunct(
          concl(normalized), normalized_conclusion)) {
      thm selected =
          cm_store_pick_conjunct(normalized, normalized_conclusion);
      return eq_mp_rule(sym_rule(wanted_normalized), selected);
    }
  }
  ENSURE_COND(false,
      "required normalized store assumption is absent: %s in %s",
      cstr_term(normalized_conclusion), cstr_gnode(leaf));
err:
  return empty_theorem;
}

PROOF static thm cm_prove_initialized_store_sim(void) {
  gnode root = gnode_new_with_ccl(
      `!(ty:cm_type) (ptr:cm_value) (v:cm_value)
         (st:cm_src_state) (vmem:int->int).
         cm_initialized_bytes_sim st vmem ==>
         cm_initialized_bytes_sim
           (cm_state_store ty ptr v st)
           (cm_store_mem ty (cm_value_number st ptr)
             (cm_value_number st (cm_convert_value st ty v)) vmem)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm simulation = assume_rule(
      `cm_initialized_bytes_sim (st:cm_src_state) (vmem:int->int)`);
  thm old_pointwise = conv_rule(rewrite_conv(THM_LIST(
      cm_initialized_bytes_sim_def)), simulation);
  thm_list rules = get_cm_state_core_defs();
  vector_add(&rules, cm_initialized_bytes_sim_def);
  vector_add(&rules, get_cm_state_store_def());
  vector_add(&rules, get_cm_mark_init_def());
  vector_add(&rules, cm_live_address_def);
  gnode opened = CONV_TAC(leaf, reduce_rewrite_conv(rules));
  gnode at_address = AUTO_INTROS_TAC(opened);
  term base =
      `cm_value_number (st:cm_src_state) (ptr:cm_value)`;
  term number =
      `cm_value_number (st:cm_src_state)
         (cm_convert_value st (ty:cm_type) (v:cm_value))`;
  term inside =
      `(${base:int} <= (addr:int) &&
        addr < ${base:int} + cm_store_width (ty:cm_type))`;
  gnode_list cases =
      BOOL_CASES_TAC(at_address, inside, "hinside");
  {
    thm inside_fact = assume_rule(inside);
    ACCEPT_TAC(cases[0], mp_rule(mp_rule(specl_rule(TERM_LIST(
        `ty:cm_type`, base, number, `vmem:int->int`,
        `cm_state_mem (st:cm_src_state)`, `addr:int`),
        cm_store_mem_byte_same), conjunct1_rule(inside_fact)),
        conjunct2_rule(inside_fact)));
  }
  {
    thm outside = assume_rule(mk_not(inside));
    thm initialized = conv_rule(reduce_rewrite_conv(THM_LIST(outside)),
        cm_store_normalized_assumption(cases[1],
          `cm_state_init (st:cm_src_state) (addr:int) ||
           ${inside:bool}`,
          rules));
    thm live = cm_store_normalized_assumption(
        cases[1],
        `cm_live_address (st:cm_src_state) (addr:int)`,
        rules);
    thm old_equal = mp_rule(spec_rule(`addr:int`, old_pointwise),
        conj_rule(initialized, live));
    thm target_other = mp_rule(specl_rule(TERM_LIST(
        `ty:cm_type`, base, number, `vmem:int->int`, `addr:int`),
        cm_store_mem_byte_other), outside);
    thm source_other = mp_rule(specl_rule(TERM_LIST(
        `ty:cm_type`, base, number,
        `cm_state_mem (st:cm_src_state)`, `addr:int`),
        cm_store_mem_byte_other), outside);
    ACCEPT_TAC(cases[1], trans_rule(target_other,
        trans_rule(old_equal, sym_rule(source_other))));
  }
  return gnode_prove(root);
}
PROOF thm cm_initialized_store_sim =
    cm_prove_initialized_store_sim();

PROOF static thm cm_prove_store_mem_target(void) {
  gnode root = gnode_new_with_ccl(
      `!(ty:cm_type) (ptr:cm_value) (v:cm_value)
         (st:cm_src_state) (vmem:int->int).
         cm_store_mem ty (cm_value_number st ptr)
          (cm_value_number st (cm_convert_value st ty v)) vmem ==
         (if ty == CMCharTy
          then tower_setb vmem (cm_value_number st ptr)
                 (cm_value_number st v)
          else tower_setw vmem (cm_value_number st ptr)
                 (cm_value_number st v))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm converted = specl_rule(TERM_LIST(
      `st:cm_src_state`, `ty:cm_type`, `v:cm_value`),
      get_cm_convert_value_number_bridge());
  thm signed_range = specl_rule(TERM_LIST(
      `st:cm_src_state`, `v:cm_value`),
      get_cm_value_number_signed_bridge());
  thm wrap_fixed = mp_rule(spec_rule(
      `cm_value_number (st:cm_src_state) (v:cm_value)`,
      get_tower_wrap64_fixed()), signed_range);
  gnode_list type_cases = BOOL_CASES_TAC(
      leaf, `(ty:cm_type) == CMCharTy`, "hchar");
  ACCEPT_TAC(type_cases[0], eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_store_mem_def(), converted, get_tower_u8_idempotent(),
        get_tower_setb_def(), get_theorem_by_name("FUN_EQ_THM"),
        assume_rule(`(ty:cm_type) == CMCharTy`))),
      goal_ccl(type_cases[0]->g))));
  ACCEPT_TAC(type_cases[1], eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_store_mem_def(), converted, wrap_fixed,
        assume_rule(`~((ty:cm_type) == CMCharTy)`))),
      goal_ccl(type_cases[1]->g))));
  return gnode_prove(root);
}
PROOF thm cm_store_mem_target = cm_prove_store_mem_target();

PROOF thm get_cm_range_disjoint_def(void) {
  return cm_range_disjoint_def;
}
PROOF thm get_cm_store_mem_byte_same(void) {
  return cm_store_mem_byte_same;
}
PROOF thm get_cm_live_address_store(void) {
  return cm_live_address_store;
}
PROOF thm get_cm_store_mem_byte_other(void) {
  return cm_store_mem_byte_other;
}
PROOF thm get_cm_store_mem_word_other(void) {
  return cm_store_mem_word_other;
}
PROOF thm get_cm_initialized_store_sim(void) {
  return cm_initialized_store_sim;
}
PROOF thm get_cm_store_mem_target(void) {
  return cm_store_mem_target;
}

PROOF static int cmc_preservation_store_memory_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_store_memory_axioms_before,
      "cmc_preservation_store_memory introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_store_memory_checks =
    cmc_preservation_store_memory_final_checks();
