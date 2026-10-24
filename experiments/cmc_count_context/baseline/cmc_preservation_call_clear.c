#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_call_clear.h"

#require "cmc_preservation_call_finish.c"

PROOF static size_t _cmc_preservation_call_clear_axioms_before =
    vector_size(get_all_axioms());

PROOF thm cm_state_clear_range_def = new_fun_definition(
    `cm_state_clear_range (st:cm_src_state)
       (span_base:int) (span_width:int) : cm_src_state =
       cm_state_make
         (cm_state_mem st)
         (cm_clear_init (cm_state_init st) span_base span_width)
         (cm_state_tags st)
         (cm_clear_tagged (cm_state_tagged st)
           span_base span_width)
         (cm_state_env st)
         (cm_state_input st)
         (cm_state_output st)
         (cm_state_fp st)
         (cm_state_nextgen st)
         (cm_state_regions st)`);

PROOF static thm cm_prove_clear_init_join(void) {
  gnode root = gnode_new_with_ccl(
      `!(old:int->bool) (span_base:int)
         (first_width:int) (second_width:int).
         0i < first_width ==> 0i < second_width ==>
         cm_clear_init old span_base (first_width + second_width) ==
         cm_clear_init
           (cm_clear_init old span_base first_width)
           (span_base + first_width) second_width`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode opened = CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
      get_cm_clear_init_def(), get_theorem_by_name("FUN_EQ_THM"))));
  gnode point = AUTO_INTROS_TAC(opened);
  gnode_list old_cases = BOOL_CASES_TAC(
      point, `(old:int->bool) (x:int)`, "Hold");
  for (size_t index = 0; index < vector_size(old_cases); ++index) {
    gnode reduced = CONV_WITH_ASMP_TAC(
        old_cases[index], reduce_rewrite_conv, THM_LIST());
    if (IS_NULL(reduced->solved)) {
      thm first_positive =
          assume_rule(`0i < (first_width:int)`);
      thm second_positive =
          assume_rule(`0i < (second_width:int)`);
      thm arithmetic = mp_rule(mp_rule(int_arith_rule(
          mk_imp(concl(first_positive),
            mk_imp(concl(second_positive),
              goal_ccl(reduced->g)))),
          first_positive), second_positive);
      ACCEPT_TAC(reduced, arithmetic);
    }
  }
  return gnode_prove(root);
}
PROOF static thm cm_clear_init_join =
    cm_prove_clear_init_join();

PROOF static thm cm_prove_clear_tagged_join(void) {
  gnode root = gnode_new_with_ccl(
      `!(old:int->bool) (span_base:int)
         (first_width:int) (second_width:int).
         0i < first_width ==> 0i < second_width ==>
         cm_clear_tagged old span_base
           (first_width + second_width) ==
         cm_clear_tagged
           (cm_clear_tagged old span_base first_width)
           (span_base + first_width) second_width`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode opened = CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
      get_cm_clear_tagged_def(), get_theorem_by_name("FUN_EQ_THM"))));
  gnode point = AUTO_INTROS_TAC(opened);
  gnode_list old_cases = BOOL_CASES_TAC(
      point, `(old:int->bool) (x:int)`, "Hold");
  for (size_t index = 0; index < vector_size(old_cases); ++index) {
    gnode reduced = CONV_WITH_ASMP_TAC(
        old_cases[index], reduce_rewrite_conv, THM_LIST());
    if (IS_NULL(reduced->solved)) {
      thm first_positive =
          assume_rule(`0i < (first_width:int)`);
      thm second_positive =
          assume_rule(`0i < (second_width:int)`);
      thm arithmetic = mp_rule(mp_rule(int_arith_rule(
          mk_imp(concl(first_positive),
            mk_imp(concl(second_positive),
              goal_ccl(reduced->g)))),
          first_positive), second_positive);
      ACCEPT_TAC(reduced, arithmetic);
    }
  }
  return gnode_prove(root);
}
PROOF static thm cm_clear_tagged_join =
    cm_prove_clear_tagged_join();

PROOF static thm cm_prove_value_number_clear_range(void) {
  gnode root = gnode_new_with_ccl(
      `!(st:cm_src_state) (span_base:int) (span_width:int)
         (v:cm_value).
         cm_value_number
           (cm_state_clear_range st span_base span_width) v ==
         cm_value_number st v`);
  gnode with_state = GEN_TAC(root, "st");
  gnode with_base = GEN_TAC(with_state, "span_base");
  gnode with_width = GEN_TAC(with_base, "span_width");
  gnode_list cases = INDUCT_TAC(with_width, `v:cm_value`);
  thm_list rules = get_cm_state_core_defs();
  vector_add(&rules, cm_state_clear_range_def);
  vector_add(&rules, get_cm_value_number_def());
  for (size_t index = 0; index < vector_size(cases); ++index) {
    gnode leaf = AUTO_INTROS_TAC(cases[index]);
    CONV_TAC(leaf, reduce_rewrite_conv(rules));
  }
  return gnode_prove(root);
}
PROOF static thm cm_value_number_clear_range =
    cm_prove_value_number_clear_range();

PROOF static thm cm_prove_convert_value_clear_range(void) {
  gnode root = gnode_new_with_ccl(
      `!(st:cm_src_state) (span_base:int) (span_width:int)
         (ty:cm_type) (v:cm_value).
         cm_convert_value
           (cm_state_clear_range st span_base span_width) ty v ==
         cm_convert_value st ty v`);
  gnode leaf = AUTO_INTROS_TAC(root);
  CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
      get_cm_convert_value_def(), cm_value_number_clear_range)));
  return gnode_prove(root);
}
PROOF static thm cm_convert_value_clear_range =
    cm_prove_convert_value_clear_range();

PROOF static thm cm_prove_clear_init_absorb(void) {
  gnode root = gnode_new_with_ccl(
      `!(old:int->bool) (span_base:int) (span_width:int).
         cm_mark_init
           (cm_clear_init old span_base span_width)
           span_base span_width ==
         cm_mark_init old span_base span_width`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode opened = CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
      get_cm_mark_init_def(), get_cm_clear_init_def(),
      get_theorem_by_name("FUN_EQ_THM"))));
  gnode point = AUTO_INTROS_TAC(opened);
  ACCEPT_TAC(point, taut_rule(goal_ccl(point->g)));
  return gnode_prove(root);
}
PROOF static thm cm_clear_init_absorb =
    cm_prove_clear_init_absorb();

PROOF static thm cm_prove_clear_tagged_idempotent(void) {
  gnode root = gnode_new_with_ccl(
      `!(old:int->bool) (span_base:int) (span_width:int).
         cm_clear_tagged
           (cm_clear_tagged old span_base span_width)
           span_base span_width ==
         cm_clear_tagged old span_base span_width`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode opened = CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
      get_cm_clear_tagged_def(),
      get_theorem_by_name("FUN_EQ_THM"))));
  gnode point = AUTO_INTROS_TAC(opened);
  ACCEPT_TAC(point, taut_rule(goal_ccl(point->g)));
  return gnode_prove(root);
}
PROOF static thm cm_clear_tagged_idempotent =
    cm_prove_clear_tagged_idempotent();

PROOF static thm cm_prove_pointer_store_width_clear(void) {
  gnode root = gnode_new_with_ccl(
      `!(ty:cm_type).
         cm_is_pointer ty ==> cm_store_width ty == 8i`);
  gnode_list cases = INDUCT_TAC(root, `ty:cm_type`);
  thm distinct = get_datatype_distinctness("cm_type");
  for (size_t index = 0; index < vector_size(cases); ++index) {
    CONV_TAC(cases[index], reduce_rewrite_conv(THM_LIST(
        get_cm_is_pointer_def(), get_cm_store_width_def(),
        distinct)));
  }
  return gnode_prove(root);
}
PROOF static thm cm_pointer_store_width_clear =
    cm_prove_pointer_store_width_clear();

PROOF static thm cm_prove_state_clear_range_join(void) {
  gnode root = gnode_new_with_ccl(
      `!(st:cm_src_state) (span_base:int)
         (first_width:int) (second_width:int).
         0i < first_width ==> 0i < second_width ==>
         cm_state_clear_range st span_base
           (first_width + second_width) ==
         cm_state_clear_range
           (cm_state_clear_range st span_base first_width)
           (span_base + first_width) second_width`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm init_join = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
      `cm_state_init (st:cm_src_state)`, `span_base:int`,
      `first_width:int`, `second_width:int`),
      cm_clear_init_join),
      assume_rule(`0i < (first_width:int)`)),
      assume_rule(`0i < (second_width:int)`));
  thm tagged_join = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
      `cm_state_tagged (st:cm_src_state)`, `span_base:int`,
      `first_width:int`, `second_width:int`),
      cm_clear_tagged_join),
      assume_rule(`0i < (first_width:int)`)),
      assume_rule(`0i < (second_width:int)`));
  thm_list rules = get_cm_state_core_defs();
  vector_add(&rules, cm_state_clear_range_def);
  vector_add(&rules, init_join);
  vector_add(&rules, tagged_join);
  CONV_TAC(leaf, reduce_rewrite_conv(rules));
  return gnode_prove(root);
}
PROOF thm cm_state_clear_range_join =
    cm_prove_state_clear_range_join();

PROOF static thm cm_prove_state_store_absorb_clear(void) {
  gnode root = gnode_new_with_ccl(
      `!(ty:cm_type) (ptr:cm_value) (stored:cm_value)
         (st:cm_src_state) (span_base:int).
         cm_value_number st ptr == span_base ==>
         cm_state_store ty ptr stored
           (cm_state_clear_range st span_base
             (cm_store_width ty)) ==
         cm_state_store ty ptr stored st`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list pointer_cases = BOOL_CASES_TAC(
      leaf, `cm_is_pointer (ty:cm_type)`, "Hpointer");
  for (size_t index = 0;
       index < vector_size(pointer_cases); ++index) {
    thm_list rules = get_cm_state_core_defs();
    vector_add(&rules, cm_state_clear_range_def);
    vector_add(&rules, get_cm_state_store_def());
    vector_add(&rules, cm_value_number_clear_range);
    vector_add(&rules, cm_convert_value_clear_range);
    vector_add(&rules, cm_clear_init_absorb);
    vector_add(&rules, cm_clear_tagged_idempotent);
    if (index == 0) {
      vector_add(&rules, match_mp_rule(
          spec_rule(`ty:cm_type`, cm_pointer_store_width_clear),
          assume_rule(`cm_is_pointer (ty:cm_type)`)));
    }
    CONV_WITH_ASMP_TAC(
        pointer_cases[index], reduce_rewrite_conv, rules);
  }
  return gnode_prove(root);
}
PROOF thm cm_state_store_absorb_clear =
    cm_prove_state_store_absorb_clear();

PROOF thm get_cm_state_store_absorb_clear(void) {
  return cm_state_store_absorb_clear;
}

PROOF static thm cm_prove_mark_clear_commute(void) {
  gnode root = gnode_new_with_ccl(
      `!(old:int->bool) (store_base:int) (store_width:int)
         (clear_base:int) (clear_width:int).
         0i < store_width ==> 0i < clear_width ==>
         cm_range_disjoint store_base store_width
           clear_base clear_width ==>
         cm_mark_init
           (cm_clear_init old clear_base clear_width)
           store_base store_width ==
         cm_clear_init
           (cm_mark_init old store_base store_width)
           clear_base clear_width`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm disjoint = conv_rule(rewrite_conv(THM_LIST(
      cm_range_disjoint_def)), assume_rule(
      `cm_range_disjoint (store_base:int) (store_width:int)
        (clear_base:int) (clear_width:int)`));
  gnode opened = CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
      get_cm_mark_init_def(), get_cm_clear_init_def(),
      get_theorem_by_name("FUN_EQ_THM"))));
  gnode point = AUTO_INTROS_TAC(opened);
  gnode_list old_cases = BOOL_CASES_TAC(
      point, `(old:int->bool) (x:int)`, "Hold");
  for (size_t index = 0; index < vector_size(old_cases); ++index) {
    gnode reduced = CONV_WITH_ASMP_TAC(
        old_cases[index], reduce_rewrite_conv, THM_LIST());
    if (IS_NULL(reduced->solved)) {
      thm store_positive =
          assume_rule(`0i < (store_width:int)`);
      thm clear_positive =
          assume_rule(`0i < (clear_width:int)`);
      thm arithmetic = mp_rule(mp_rule(mp_rule(int_arith_rule(
          mk_imp(concl(store_positive),
            mk_imp(concl(clear_positive),
              mk_imp(concl(disjoint),
                goal_ccl(reduced->g))))),
          store_positive), clear_positive), disjoint);
      ACCEPT_TAC(reduced, arithmetic);
    }
  }
  return gnode_prove(root);
}
PROOF static thm cm_mark_clear_commute =
    cm_prove_mark_clear_commute();

PROOF static thm cm_prove_clear_tagged_commute_raw(void) {
  gnode root = gnode_new_with_ccl(
      `!(old:int->bool) (first_base:int) (first_width:int)
         (second_base:int) (second_width:int).
         cm_clear_tagged
           (cm_clear_tagged old second_base second_width)
           first_base first_width ==
         cm_clear_tagged
           (cm_clear_tagged old first_base first_width)
           second_base second_width`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode opened = CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
      get_cm_clear_tagged_def(),
      get_theorem_by_name("FUN_EQ_THM"))));
  gnode point = AUTO_INTROS_TAC(opened);
  ACCEPT_TAC(point, taut_rule(goal_ccl(point->g)));
  return gnode_prove(root);
}
PROOF static thm cm_clear_tagged_commute_raw =
    cm_prove_clear_tagged_commute_raw();

PROOF static thm cm_prove_pointer_tag_clear_commute(void) {
  gnode root = gnode_new_with_ccl(
      `!(old:int->bool) (store_base:int) (number:int)
         (clear_base:int) (clear_width:int).
         0i < clear_width ==>
         cm_range_disjoint store_base 8i
           clear_base clear_width ==>
         cm_clear_tagged
           (\a:int.
              (a == store_base && ~(number == 0i)) ||
              cm_clear_tagged old store_base 8i a)
           clear_base clear_width ==
         (\a:int.
            (a == store_base && ~(number == 0i)) ||
            cm_clear_tagged
              (cm_clear_tagged old clear_base clear_width)
              store_base 8i a)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm disjoint = conv_rule(rewrite_conv(THM_LIST(
      cm_range_disjoint_def)), assume_rule(
      `cm_range_disjoint (store_base:int) 8i
        (clear_base:int) (clear_width:int)`));
  gnode opened = CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
      get_cm_clear_tagged_def(),
      get_theorem_by_name("FUN_EQ_THM"))));
  gnode point = AUTO_INTROS_TAC(opened);
  gnode_list base_cases = BOOL_CASES_TAC(
      point, `(x:int) == (store_base:int)`, "Hat_base");
  for (size_t branch = 0;
       branch < vector_size(base_cases); ++branch) {
    gnode_list old_cases = BOOL_CASES_TAC(
        base_cases[branch], `(old:int->bool) (x:int)`, "Hold");
    for (size_t index = 0;
         index < vector_size(old_cases); ++index) {
      gnode reduced = CONV_WITH_ASMP_TAC(
          old_cases[index], reduce_rewrite_conv, THM_LIST());
      if (IS_NULL(reduced->solved)) {
        thm clear_positive =
            assume_rule(`0i < (clear_width:int)`);
        thm arithmetic = mp_rule(mp_rule(int_arith_rule(
            mk_imp(concl(clear_positive),
              mk_imp(concl(disjoint),
                goal_ccl(reduced->g)))),
            clear_positive), disjoint);
        ACCEPT_TAC(reduced, arithmetic);
      }
    }
  }
  return gnode_prove(root);
}
PROOF static thm cm_pointer_tag_clear_commute =
    cm_prove_pointer_tag_clear_commute();

PROOF static thm cm_prove_state_store_clear_commute(void) {
  gnode root = gnode_new_with_ccl(
      `!(ty:cm_type) (ptr:cm_value) (stored:cm_value)
         (st:cm_src_state) (store_base:int)
         (clear_base:int) (clear_width:int).
         cm_value_number st ptr == store_base ==>
         0i < clear_width ==>
         cm_range_disjoint store_base (cm_store_width ty)
           clear_base clear_width ==>
         cm_state_store ty ptr stored
           (cm_state_clear_range st clear_base clear_width) ==
         cm_state_clear_range
           (cm_state_store ty ptr stored st)
           clear_base clear_width`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm width_at_least_one =
      spec_rule(`ty:cm_type`, get_cm_store_width_positive());
  thm store_positive = mp_rule(int_arith_rule(
      `1i <= cm_store_width (ty:cm_type) ==>
       0i < cm_store_width ty`), width_at_least_one);
  thm clear_positive =
      assume_rule(`0i < (clear_width:int)`);
  thm disjoint = assume_rule(
      `cm_range_disjoint (store_base:int)
        (cm_store_width (ty:cm_type))
        (clear_base:int) (clear_width:int)`);
  thm init_commutes = match_mp_rule(match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(
        `cm_state_init (st:cm_src_state)`, `store_base:int`,
        `cm_store_width (ty:cm_type)`, `clear_base:int`,
        `clear_width:int`), cm_mark_clear_commute),
      store_positive), clear_positive), disjoint);
  gnode_list pointer_cases = BOOL_CASES_TAC(
      leaf, `cm_is_pointer (ty:cm_type)`, "Hpointer");
  for (size_t index = 0;
       index < vector_size(pointer_cases); ++index) {
    thm tagged_commutes;
    thm_list rules = get_cm_state_core_defs();
    vector_add(&rules, cm_state_clear_range_def);
    vector_add(&rules, get_cm_state_store_def());
    vector_add(&rules, cm_value_number_clear_range);
    vector_add(&rules, cm_convert_value_clear_range);
    if (index == 0) {
      thm pointer_width = match_mp_rule(
          spec_rule(`ty:cm_type`, cm_pointer_store_width_clear),
          assume_rule(`cm_is_pointer (ty:cm_type)`));
      thm pointer_disjoint =
          conv_rule(rewrite_conv(THM_LIST(pointer_width)), disjoint);
      thm pointer_init = conv_rule(
          rewrite_conv(THM_LIST(pointer_width)), init_commutes);
      vector_add(&rules, pointer_init);
      tagged_commutes = match_mp_rule(match_mp_rule(
          specl_rule(TERM_LIST(
            `cm_state_tagged (st:cm_src_state)`,
            `store_base:int`,
            `cm_value_number (st:cm_src_state)
              (cm_convert_value st (ty:cm_type)
                (stored:cm_value))`,
            `clear_base:int`, `clear_width:int`),
            cm_pointer_tag_clear_commute),
          clear_positive), pointer_disjoint);
      vector_add(&rules, pointer_width);
    } else {
      vector_add(&rules, init_commutes);
      tagged_commutes = specl_rule(TERM_LIST(
          `cm_state_tagged (st:cm_src_state)`,
          `store_base:int`, `cm_store_width (ty:cm_type)`,
          `clear_base:int`, `clear_width:int`),
          cm_clear_tagged_commute_raw);
    }
    vector_add(&rules, tagged_commutes);
    gnode reduced = CONV_WITH_ASMP_TAC(
        pointer_cases[index], reduce_rewrite_conv, rules);
    ENSURE_COND(!IS_NULL(reduced->solved),
        "store-clear branch remains open: %s",
        cstr_gnode(reduced));
  }
  return gnode_prove(root);
err:
  return empty_theorem;
}
PROOF thm cm_state_store_clear_commute =
    cm_prove_state_store_clear_commute();

PROOF thm get_cm_state_store_clear_commute(void) {
  return cm_state_store_clear_commute;
}

PROOF thm get_cm_state_clear_range_def(void) {
  return cm_state_clear_range_def;
}
PROOF thm get_cm_state_clear_range_join(void) {
  return cm_state_clear_range_join;
}

PROOF static int cmc_preservation_call_clear_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_call_clear_axioms_before,
      "cmc_preservation_call_clear introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_call_clear_checks =
    cmc_preservation_call_clear_final_checks();
