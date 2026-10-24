#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_call_finish.h"

#require "cmc_preservation_call_param.c"

PROOF static size_t _cmc_preservation_call_finish_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_call_finish_assumption(
    const gnode node, const term wanted) {
  labeled_term_list assumptions = goal_lasmps(node->g);
  for (size_t index = 0; index < vector_size(assumptions); ++index) {
    if (alpha_compare(assumptions[index].tm, wanted) == 0) {
      return assume_rule(assumptions[index].tm);
    }
  }
  return empty_theorem;
}


PROOF static thm cm_prove_convert_value_state_store(void) {
  gnode root = gnode_new_with_ccl(
      `!(stored_ty:cm_type) (ptr:cm_value) (stored:cm_value)
         (st:cm_src_state) (ty:cm_type) (v:cm_value).
         cm_convert_value (cm_state_store stored_ty ptr stored st) ty v ==
         cm_convert_value st ty v`);
  gnode leaf = AUTO_INTROS_TAC(root);
  CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
      get_cm_convert_value_def(), get_cm_value_number_state_store())));
  return gnode_prove(root);
}
PROOF static thm cm_convert_value_state_store =
    cm_prove_convert_value_state_store();

PROOF static thm cm_prove_store_mem_raw_same(void) {
  gnode root = gnode_new_with_ccl(
      `!(ty:cm_type) (base:int) (number:int)
         (left:int->int) (right:int->int) (addr:int).
         base <= addr ==>
         addr < base + cm_store_width ty ==>
         cm_store_mem ty base number left addr ==
         cm_store_mem ty base number right addr`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list type_cases = BOOL_CASES_TAC(
      leaf, `(ty:cm_type) == CMCharTy`, "Hchar");
  {
    thm is_char = assume_rule(`(ty:cm_type) == CMCharTy`);
    thm upper = conv_rule(reduce_rewrite_conv(THM_LIST(
        get_cm_store_width_def(), is_char)), assume_rule(
          `(addr:int) < (base:int) + cm_store_width (ty:cm_type)`));
    thm at_base = mp_rule(mp_rule(int_arith_rule(
        `(base:int) <= (addr:int) ==> addr < base + 1i ==>
         addr == base`), assume_rule(
           `(base:int) <= (addr:int)`)), upper);
    CONV_TAC(type_cases[0], reduce_rewrite_conv(THM_LIST(
        get_cm_store_mem_def(), get_tower_setb_def(),
        is_char, at_base)));
  }
  {
    gnode current = type_cases[1];
    term offsets[8] = {
        `0i`, `1i`, `2i`, `3i`, `4i`, `5i`, `6i`, `7i`};
    const char *labels[8] = {
        "Hoffset0", "Hoffset1", "Hoffset2", "Hoffset3",
        "Hoffset4", "Hoffset5", "Hoffset6", "Hoffset7"};
    for (int offset = 0; offset < 8; ++offset) {
      term equality = mk_eq(`addr:int`,
          mk_binop(`(+):int->int->int`, `base:int`,
            offsets[offset]));
      gnode_list address_cases =
          BOOL_CASES_TAC(current, equality, labels[offset]);
      CONV_TAC(address_cases[0], reduce_rewrite_conv(THM_LIST(
          get_cm_store_mem_def(), get_tower_setw_def(),
          assume_rule(`~((ty:cm_type) == CMCharTy)`),
          assume_rule(equality))));
      current = address_cases[1];
    }
    thm upper = conv_rule(reduce_rewrite_conv(THM_LIST(
        get_cm_store_width_def(),
        assume_rule(`~((ty:cm_type) == CMCharTy)`))),
        assume_rule(
          `(addr:int) < (base:int) + cm_store_width (ty:cm_type)`));
    thm impossible = int_arith_rule(
        `(base:int) <= (addr:int) ==> addr < base + 8i ==>
         ~(addr == base + 0i) ==> ~(addr == base + 1i) ==>
         ~(addr == base + 2i) ==> ~(addr == base + 3i) ==>
         ~(addr == base + 4i) ==> ~(addr == base + 5i) ==>
         ~(addr == base + 6i) ==> ~(addr == base + 7i) ==> F`);
    impossible = mp_rule(impossible,
        assume_rule(`(base:int) <= (addr:int)`));
    impossible = mp_rule(impossible, upper);
    for (int offset = 0; offset < 8; ++offset) {
      impossible = mp_rule(impossible, assume_rule(mk_not(mk_eq(
          `addr:int`, mk_binop(`(+):int->int->int`,
            `base:int`, offsets[offset])))));
    }
    CONTR_TAC(current, impossible);
  }
  return gnode_prove(root);
}
PROOF static thm cm_store_mem_raw_same =
    cm_prove_store_mem_raw_same();

PROOF static thm cm_prove_store_mem_raw_other(void) {
  gnode root = gnode_new_with_ccl(
      `!(ty:cm_type) (base:int) (number:int)
         (mem:int->int) (addr:int).
         ~((base <= addr &&
            addr < base + cm_store_width ty)) ==>
         cm_store_mem ty base number mem addr == mem addr`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list type_cases = BOOL_CASES_TAC(
      leaf, `(ty:cm_type) == CMCharTy`, "Hchar");
  {
    thm outside = conv_rule(reduce_rewrite_conv(THM_LIST(
        get_cm_store_width_def(),
        assume_rule(`(ty:cm_type) == CMCharTy`))), assume_rule(
          `~((base:int) <= (addr:int) &&
             addr < base + cm_store_width (ty:cm_type))`));
    thm unequal = mp_rule(int_arith_rule(
        `~((base:int) <= (addr:int) && addr < base + 1i) ==>
         ~(addr == base)`), outside);
    CONV_TAC(type_cases[0], reduce_rewrite_conv(THM_LIST(
        get_cm_store_mem_def(), get_tower_setb_def(),
        assume_rule(`(ty:cm_type) == CMCharTy`), unequal)));
  }
  {
    thm outside = conv_rule(reduce_rewrite_conv(THM_LIST(
        get_cm_store_width_def(),
        assume_rule(`~((ty:cm_type) == CMCharTy)`))), assume_rule(
          `~((base:int) <= (addr:int) &&
             addr < base + cm_store_width (ty:cm_type))`));
    thm unequal = mp_rule(int_arith_rule(
        `~((base:int) <= (addr:int) && addr < base + 8i) ==>
         ~(addr == base + 0i) && ~(addr == base + 1i) &&
         ~(addr == base + 2i) && ~(addr == base + 3i) &&
         ~(addr == base + 4i) && ~(addr == base + 5i) &&
         ~(addr == base + 6i) && ~(addr == base + 7i)`),
        outside);
    CONV_TAC(type_cases[1], reduce_rewrite_conv(THM_LIST(
        get_cm_store_mem_def(), get_tower_setw_def(),
        assume_rule(`~((ty:cm_type) == CMCharTy)`), unequal)));
  }
  return gnode_prove(root);
}
PROOF static thm cm_store_mem_raw_other =
    cm_prove_store_mem_raw_other();

PROOF static thm cm_prove_store_mem_commute(void) {
  gnode root = gnode_new_with_ccl(
      `!(ty1:cm_type) (base1:int) (number1:int)
         (ty2:cm_type) (base2:int) (number2:int) (mem:int->int).
         cm_range_disjoint base1 (cm_store_width ty1)
           base2 (cm_store_width ty2) ==>
         cm_store_mem ty1 base1 number1
           (cm_store_mem ty2 base2 number2 mem) ==
         cm_store_mem ty2 base2 number2
           (cm_store_mem ty1 base1 number1 mem)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm disjoint = conv_rule(rewrite_conv(THM_LIST(
      cm_range_disjoint_def)), assume_rule(
        `cm_range_disjoint (base1:int)
          (cm_store_width (ty1:cm_type)) (base2:int)
          (cm_store_width (ty2:cm_type))`));
  gnode pointwise = CONV_TAC(leaf, rewrite_conv(THM_LIST(
      get_theorem_by_name("FUN_EQ_THM"))));
  gnode at_address = AUTO_INTROS_TAC(pointwise);
  term in_first =
      `(base1:int) <= (x:int) &&
       x < base1 + cm_store_width (ty1:cm_type)`;
  term in_second =
      `(base2:int) <= (x:int) &&
       x < base2 + cm_store_width (ty2:cm_type)`;
  gnode_list first_cases =
      BOOL_CASES_TAC(at_address, in_first, "Hin_first");
  {
    thm first = assume_rule(in_first);
    thm outside_second = mp_rule(int_arith_rule(mk_imp(
        concl(disjoint), mk_imp(in_first, mk_not(in_second)))),
        disjoint);
    outside_second = mp_rule(outside_second, first);
    thm left_same = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
        `ty1:cm_type`, `base1:int`, `number1:int`,
        `cm_store_mem (ty2:cm_type) (base2:int)
          (number2:int) (mem:int->int)`,
        `mem:int->int`, `x:int`), cm_store_mem_raw_same),
        conjunct1_rule(first)), conjunct2_rule(first));
    thm right_other = match_mp_rule(specl_rule(TERM_LIST(
        `ty2:cm_type`, `base2:int`, `number2:int`,
        `cm_store_mem (ty1:cm_type) (base1:int)
          (number1:int) (mem:int->int)`,
        `x:int`), cm_store_mem_raw_other), outside_second);
    ACCEPT_TAC(first_cases[0],
        trans_rule(left_same, sym_rule(right_other)));
  }
  gnode_list second_cases =
      BOOL_CASES_TAC(first_cases[1], in_second, "Hin_second");
  {
    thm not_first = assume_rule(mk_not(in_first));
    thm second = assume_rule(in_second);
    thm left_other = match_mp_rule(specl_rule(TERM_LIST(
        `ty1:cm_type`, `base1:int`, `number1:int`,
        `cm_store_mem (ty2:cm_type) (base2:int)
          (number2:int) (mem:int->int)`,
        `x:int`), cm_store_mem_raw_other), not_first);
    thm right_same = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
        `ty2:cm_type`, `base2:int`, `number2:int`,
        `cm_store_mem (ty1:cm_type) (base1:int)
          (number1:int) (mem:int->int)`,
        `mem:int->int`, `x:int`), cm_store_mem_raw_same),
        conjunct1_rule(second)), conjunct2_rule(second));
    ACCEPT_TAC(second_cases[0],
        trans_rule(left_other, sym_rule(right_same)));
  }
  {
    thm not_first = assume_rule(mk_not(in_first));
    thm not_second = assume_rule(mk_not(in_second));
    thm left_outer = match_mp_rule(specl_rule(TERM_LIST(
        `ty1:cm_type`, `base1:int`, `number1:int`,
        `cm_store_mem (ty2:cm_type) (base2:int)
          (number2:int) (mem:int->int)`,
        `x:int`), cm_store_mem_raw_other), not_first);
    thm left_inner = match_mp_rule(specl_rule(TERM_LIST(
        `ty2:cm_type`, `base2:int`, `number2:int`,
        `mem:int->int`, `x:int`), cm_store_mem_raw_other),
        not_second);
    thm right_outer = match_mp_rule(specl_rule(TERM_LIST(
        `ty2:cm_type`, `base2:int`, `number2:int`,
        `cm_store_mem (ty1:cm_type) (base1:int)
          (number1:int) (mem:int->int)`,
        `x:int`), cm_store_mem_raw_other), not_second);
    thm right_inner = match_mp_rule(specl_rule(TERM_LIST(
        `ty1:cm_type`, `base1:int`, `number1:int`,
        `mem:int->int`, `x:int`), cm_store_mem_raw_other),
        not_first);
    ACCEPT_TAC(second_cases[1], trans_rule(
        trans_rule(left_outer, left_inner),
        sym_rule(trans_rule(right_outer, right_inner))));
  }
  return gnode_prove(root);
}
PROOF static thm cm_store_mem_commute =
    cm_prove_store_mem_commute();

PROOF static thm cm_prove_pointer_store_width(void) {
  gnode root = gnode_new_with_ccl(
      `!(ty:cm_type).
         cm_is_pointer ty ==> cm_store_width ty == 8i`);
  gnode_list cases = INDUCT_TAC(root, `ty:cm_type`);
  thm distinct = get_datatype_distinctness("cm_type");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    CONV_TAC(cases[i], reduce_rewrite_conv(THM_LIST(
        get_cm_is_pointer_def(), get_cm_store_width_def(), distinct)));
  }
  return gnode_prove(root);
}
PROOF static thm cm_pointer_store_width =
    cm_prove_pointer_store_width();

PROOF static thm cm_prove_mark_init_commute(void) {
  gnode root = gnode_new_with_ccl(
      `!(old:int->bool) (base1:int) width1 base2 width2.
         cm_mark_init (cm_mark_init old base2 width2) base1 width1 ==
         cm_mark_init (cm_mark_init old base1 width1) base2 width2`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode reduced = CONV_WITH_ASMP_TAC(leaf, reduce_rewrite_conv,
      THM_LIST(get_cm_mark_init_def(),
        get_theorem_by_name("FUN_EQ_THM")));
  if (IS_NULL(reduced->solved)) {
    ACCEPT_TAC(reduced, taut_rule(goal_ccl(reduced->g)));
  }
  return gnode_prove(root);
}
PROOF static thm cm_mark_init_commute =
    cm_prove_mark_init_commute();

PROOF static thm cm_prove_store_tags_commute(void) {
  gnode root = gnode_new_with_ccl(
      `!(ty1:cm_type) (base1:int) (value1:cm_value)
         (ty2:cm_type) (base2:int) (value2:cm_value)
         (old:int->cm_value).
         ~(base1 == base2) ==>
         (if cm_is_pointer ty1
          then (\a:int.
             if a == base1 then value1
             else (if cm_is_pointer ty2
                   then (\b:int.
                      if b == base2 then value2 else old b)
                   else old) a)
          else if cm_is_pointer ty2
               then (\a:int.
                  if a == base2 then value2 else old a)
               else old) ==
         (if cm_is_pointer ty2
          then (\a:int.
             if a == base2 then value2
             else (if cm_is_pointer ty1
                   then (\b:int.
                      if b == base1 then value1 else old b)
                   else old) a)
          else if cm_is_pointer ty1
               then (\a:int.
                  if a == base1 then value1 else old a)
               else old)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list first_cases = BOOL_CASES_TAC(
      leaf, `cm_is_pointer (ty1:cm_type)`, "Hfirst_pointer");
  for (size_t i = 0; i < vector_size(first_cases); ++i) {
    gnode_list second_cases = BOOL_CASES_TAC(
        first_cases[i], `cm_is_pointer (ty2:cm_type)`,
        "Hsecond_pointer");
    for (size_t j = 0; j < vector_size(second_cases); ++j) {
      gnode pointwise = CONV_WITH_ASMP_TAC(
          second_cases[j], reduce_rewrite_conv, THM_LIST(
            get_theorem_by_name("FUN_EQ_THM")));
      if (!IS_NULL(pointwise->solved)) {
        continue;
      }
      gnode at_address = AUTO_INTROS_TAC(pointwise);
      gnode_list first_address = BOOL_CASES_TAC(
          at_address, `(x:int) == (base1:int)`, "Hat_first");
      for (size_t k = 0; k < vector_size(first_address); ++k) {
        gnode_list second_address = BOOL_CASES_TAC(
            first_address[k], `(x:int) == (base2:int)`,
            "Hat_second");
        for (size_t m = 0; m < vector_size(second_address); ++m) {
          CONV_WITH_ASMP_TAC(second_address[m],
              reduce_rewrite_conv, THM_LIST());
        }
      }
    }
  }
  return gnode_prove(root);
}
PROOF static thm cm_store_tags_commute =
    cm_prove_store_tags_commute();

PROOF static thm cm_prove_store_tagged_commute(void) {
  gnode root = gnode_new_with_ccl(
      `!(ty1:cm_type) (base1:int) (number1:int)
         (ty2:cm_type) (base2:int) (number2:int)
         (old:int->bool).
         cm_range_disjoint base1 (cm_store_width ty1)
           base2 (cm_store_width ty2) ==>
         (if cm_is_pointer ty1
          then (\a:int.
             (a == base1 && ~(number1 == 0i)) ||
             cm_clear_tagged
               (if cm_is_pointer ty2
                then (\b:int.
                   (b == base2 && ~(number2 == 0i)) ||
                   cm_clear_tagged old base2 8i b)
                else cm_clear_tagged old base2
                       (cm_store_width ty2))
               base1 8i a)
          else cm_clear_tagged
                 (if cm_is_pointer ty2
                  then (\a:int.
                     (a == base2 && ~(number2 == 0i)) ||
                     cm_clear_tagged old base2 8i a)
                  else cm_clear_tagged old base2
                         (cm_store_width ty2))
                 base1 (cm_store_width ty1)) ==
         (if cm_is_pointer ty2
          then (\a:int.
             (a == base2 && ~(number2 == 0i)) ||
             cm_clear_tagged
               (if cm_is_pointer ty1
                then (\b:int.
                   (b == base1 && ~(number1 == 0i)) ||
                   cm_clear_tagged old base1 8i b)
                else cm_clear_tagged old base1
                       (cm_store_width ty1))
               base2 8i a)
          else cm_clear_tagged
                 (if cm_is_pointer ty1
                  then (\a:int.
                     (a == base1 && ~(number1 == 0i)) ||
                     cm_clear_tagged old base1 8i a)
                  else cm_clear_tagged old base1
                         (cm_store_width ty1))
                 base2 (cm_store_width ty2))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm disjoint = conv_rule(rewrite_conv(THM_LIST(
      cm_range_disjoint_def)), assume_rule(
        `cm_range_disjoint (base1:int)
          (cm_store_width (ty1:cm_type)) (base2:int)
          (cm_store_width (ty2:cm_type))`));
  thm first_positive =
      spec_rule(`ty1:cm_type`, get_cm_store_width_positive());
  thm second_positive =
      spec_rule(`ty2:cm_type`, get_cm_store_width_positive());
  thm bases_unequal = mp_rule(mp_rule(mp_rule(int_arith_rule(
      mk_imp(concl(disjoint), mk_imp(concl(first_positive),
        mk_imp(concl(second_positive),
          `~((base1:int) == (base2:int))`)))),
      disjoint), first_positive), second_positive);
  thm first_self = int_arith_rule(
      `(base1:int) < base1 + 8i`);
  thm second_self = int_arith_rule(
      `(base2:int) < base2 + 8i`);
  thm no_overlap = mp_rule(int_arith_rule(
      mk_imp(concl(disjoint),
        `~((base1:int) < base2 + cm_store_width (ty2:cm_type) &&
           base2 < base1 + cm_store_width (ty1:cm_type))`)),
      disjoint);
  thm no_overlap_symmetric = mp_rule(int_arith_rule(
      mk_imp(concl(disjoint),
        `~((base2:int) < base1 + cm_store_width (ty1:cm_type) &&
           base1 < base2 + cm_store_width (ty2:cm_type))`)),
      disjoint);
  gnode_list first_cases = BOOL_CASES_TAC(
      leaf, `cm_is_pointer (ty1:cm_type)`, "Hfirst_pointer");
  for (size_t i = 0; i < vector_size(first_cases); ++i) {
    gnode_list second_cases = BOOL_CASES_TAC(
        first_cases[i], `cm_is_pointer (ty2:cm_type)`,
        "Hsecond_pointer");
    for (size_t j = 0; j < vector_size(second_cases); ++j) {
      thm_list rules = THM_LIST(
          get_cm_clear_tagged_def(),
          get_theorem_by_name("FUN_EQ_THM"),
          bases_unequal, first_self, second_self);
      thm branch_no_overlap = no_overlap;
      thm branch_no_overlap_symmetric = no_overlap_symmetric;
      if (i == 0) {
        thm width = match_mp_rule(
            spec_rule(`ty1:cm_type`, cm_pointer_store_width),
            assume_rule(`cm_is_pointer (ty1:cm_type)`));
        vector_add(&rules, width);
        branch_no_overlap = conv_rule(
            rewrite_conv(THM_LIST(width)), branch_no_overlap);
        branch_no_overlap_symmetric = conv_rule(
            rewrite_conv(THM_LIST(width)), branch_no_overlap_symmetric);
      }
      if (j == 0) {
        thm width = match_mp_rule(
            spec_rule(`ty2:cm_type`, cm_pointer_store_width),
            assume_rule(`cm_is_pointer (ty2:cm_type)`));
        vector_add(&rules, width);
        branch_no_overlap = conv_rule(
            rewrite_conv(THM_LIST(width)), branch_no_overlap);
        branch_no_overlap_symmetric = conv_rule(
            rewrite_conv(THM_LIST(width)), branch_no_overlap_symmetric);
      }
      vector_add(&rules, branch_no_overlap);
      vector_add(&rules, branch_no_overlap_symmetric);
      gnode pointwise = CONV_WITH_ASMP_TAC(
          second_cases[j], reduce_rewrite_conv, rules);
      if (!IS_NULL(pointwise->solved)) {
        continue;
      }
      gnode at_address = AUTO_INTROS_TAC(pointwise);
      gnode_list first_address = BOOL_CASES_TAC(
          at_address, `(x:int) == (base1:int)`, "Hat_first");
      for (size_t k = 0; k < vector_size(first_address); ++k) {
        gnode_list second_address = BOOL_CASES_TAC(
            first_address[k], `(x:int) == (base2:int)`,
            "Hat_second");
        for (size_t m = 0; m < vector_size(second_address); ++m) {
          thm_list local = (thm_list)vector_copy(rules);
          vector_add(&local, disjoint);
          gnode reduced = CONV_WITH_ASMP_TAC(second_address[m],
              reduce_rewrite_conv, local);
          if (IS_NULL(reduced->solved)) {
            ACCEPT_TAC(reduced, taut_rule(goal_ccl(reduced->g)));
          }
        }
      }
    }
  }
  return gnode_prove(root);
}
PROOF static thm cm_store_tagged_commute =
    cm_prove_store_tagged_commute();

PROOF static thm cm_prove_state_store_commute(void) {
  gnode root = gnode_new_with_ccl(
      `!(ty1:cm_type) (ptr1:cm_value) (v1:cm_value)
         (ty2:cm_type) (ptr2:cm_value) (v2:cm_value)
         (st:cm_src_state).
         cm_range_disjoint
           (cm_value_number st ptr1) (cm_store_width ty1)
           (cm_value_number st ptr2) (cm_store_width ty2) ==>
         cm_state_store ty1 ptr1 v1
           (cm_state_store ty2 ptr2 v2 st) ==
         cm_state_store ty2 ptr2 v2
           (cm_state_store ty1 ptr1 v1 st)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm disjoint_assumption = assume_rule(
      `cm_range_disjoint
        (cm_value_number (st:cm_src_state) (ptr1:cm_value))
        (cm_store_width (ty1:cm_type))
        (cm_value_number st (ptr2:cm_value))
        (cm_store_width (ty2:cm_type))`);
  thm disjoint = conv_rule(rewrite_conv(THM_LIST(
      cm_range_disjoint_def)), disjoint_assumption);
  thm first_positive =
      spec_rule(`ty1:cm_type`, get_cm_store_width_positive());
  thm second_positive =
      spec_rule(`ty2:cm_type`, get_cm_store_width_positive());
  thm bases_unequal = mp_rule(mp_rule(mp_rule(int_arith_rule(
      mk_imp(concl(disjoint), mk_imp(concl(first_positive),
        mk_imp(concl(second_positive),
          `~(cm_value_number (st:cm_src_state) (ptr1:cm_value) ==
             cm_value_number st (ptr2:cm_value))`)))),
      disjoint), first_positive), second_positive);
  thm memory_commutes = match_mp_rule(specl_rule(TERM_LIST(
      `ty1:cm_type`,
      `cm_value_number (st:cm_src_state) (ptr1:cm_value)`,
      `cm_value_number st
        (cm_convert_value st ty1 (v1:cm_value))`,
      `ty2:cm_type`,
      `cm_value_number st (ptr2:cm_value)`,
      `cm_value_number st
        (cm_convert_value st ty2 (v2:cm_value))`,
      `cm_state_mem st`), cm_store_mem_commute),
      disjoint_assumption);
  thm tags_commute = match_mp_rule(specl_rule(TERM_LIST(
      `ty1:cm_type`,
      `cm_value_number (st:cm_src_state) (ptr1:cm_value)`,
      `cm_convert_value st ty1 (v1:cm_value)`,
      `ty2:cm_type`,
      `cm_value_number st (ptr2:cm_value)`,
      `cm_convert_value st ty2 (v2:cm_value)`,
      `cm_state_tags st`), cm_store_tags_commute),
      bases_unequal);
  thm tagged_commutes = match_mp_rule(specl_rule(TERM_LIST(
      `ty1:cm_type`,
      `cm_value_number (st:cm_src_state) (ptr1:cm_value)`,
      `cm_value_number st
        (cm_convert_value st ty1 (v1:cm_value))`,
      `ty2:cm_type`,
      `cm_value_number st (ptr2:cm_value)`,
      `cm_value_number st
        (cm_convert_value st ty2 (v2:cm_value))`,
      `cm_state_tagged st`), cm_store_tagged_commute),
      disjoint_assumption);
  thm_list rules = get_cm_state_core_defs();
  vector_add(&rules, get_cm_state_store_def());
  vector_add(&rules, get_cm_value_number_state_store());
  vector_add(&rules, cm_convert_value_state_store);
  vector_add(&rules, memory_commutes);
  vector_add(&rules, cm_mark_init_commute);
  vector_add(&rules, tags_commute);
  vector_add(&rules, tagged_commutes);
  CONV_WITH_ASMP_TAC(leaf, reduce_rewrite_conv, rules);
  return gnode_prove(root);
}
PROOF thm cm_state_store_commute = cm_prove_state_store_commute();

PROOF static thm cm_prove_slot_cells_disjoint(void) {
  gnode root = gnode_new_with_ccl(
      `!(structs:(cm_struct_d)list) (slots:(cm_slot_d)list).
         cm_slot_sizes_positive structs slots ==>
         !(left:int) right base.
           0i <= left ==> left < right ==>
           right < ilength slots ==>
           cm_range_disjoint
             (base + cm_slots_prefix structs slots left)
             (cm_slot_size structs (inth left slots))
             (base + cm_slots_prefix structs slots right)
             (cm_slot_size structs (inth right slots))`);
  gnode with_structs = GEN_TAC(root, "structs");
  gnode_list cases = INDUCT_TAC(with_structs, `slots:(cm_slot_d)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm right_upper = conv_rule(reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF"))), assume_rule(
          `(right:int) < ilength ([]:(cm_slot_d)list)`));
    thm impossible = mp_rule(mp_rule(mp_rule(int_arith_rule(
        `0i <= (left:int) ==> left < (right:int) ==>
         right < 0i ==> F`),
        assume_rule(`0i <= (left:int)`)),
        assume_rule(`(left:int) < (right:int)`)), right_upper);
    CONTR_TAC(leaf, impossible);
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm positive = conv_rule(rewrite_conv(THM_LIST(
        cm_slot_sizes_positive_def)), assume_rule(
          `cm_slot_sizes_positive (structs:(cm_struct_d)list)
            ((a0:cm_slot_d) :: (a1:(cm_slot_d)list))`));
    thm left_lower = assume_rule(`0i <= (left:int)`);
    thm left_right = assume_rule(`(left:int) < (right:int)`);
    thm right_upper = conv_rule(rewrite_conv(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF"))), assume_rule(
          `(right:int) <
            ilength ((a0:cm_slot_d) :: (a1:(cm_slot_d)list))`));
    gnode_list zero_cases = BOOL_CASES_TAC(
        leaf, `(left:int) == 0i`, "Hleft_zero");
    {
      thm left_zero = assume_rule(`(left:int) == 0i`);
      thm right_one = mp_rule(mp_rule(int_arith_rule(
          `0i <= (left:int) ==> left < (right:int) ==>
           1i <= right`), left_lower), left_right);
      thm right_nonzero = mp_rule(int_arith_rule(
          `1i <= (right:int) ==> ~(right == 0i)`), right_one);
      thm head_at = ispecl_rule(TERM_LIST(
          `a0:cm_slot_d`, `a1:(cm_slot_d)list`),
          cm_inth_zero_cons);
      thm tail_index_bounds = mp_rule(mp_rule(int_arith_rule(
          `1i <= (right:int) ==>
           right < 1i + ilength (a1:(cm_slot_d)list) ==>
           0i <= right - 1i &&
           right - 1i < ilength a1`), right_one), right_upper);
      thm tail_prefix = match_mp_rule(specl_rule(TERM_LIST(
          `structs:(cm_struct_d)list`, `a1:(cm_slot_d)list`),
          cm_slots_prefix_cell_bounds), conjunct2_rule(positive));
      tail_prefix = spec_rule(`(right:int) - 1i`, tail_prefix);
      tail_prefix = match_mp_rule(match_mp_rule(tail_prefix,
          conjunct1_rule(tail_index_bounds)),
          conjunct2_rule(tail_index_bounds));
      thm right_at_tail = mp_rule(ispecl_rule(TERM_LIST(
          `a0:cm_slot_d`, `a1:(cm_slot_d)list`, `right:int`),
          cm_inth_cons_tail), right_one);
      gnode reduced = CONV_WITH_ASMP_TAC(
          zero_cases[0], reduce_rewrite_conv, THM_LIST(
            get_cm_slots_prefix_def(), left_zero, right_one,
            right_nonzero, head_at, right_at_tail,
            cm_range_disjoint_def));
      thm inputs = conj_rule(conjunct1_rule(positive),
          conjunct1_rule(tail_prefix));
      ACCEPT_TAC(reduced, mp_rule(int_arith_rule(mk_imp(
          concl(inputs), goal_ccl(reduced->g))), inputs));
    }
    {
      thm left_nonzero =
          assume_rule(`~((left:int) == 0i)`);
      thm left_one = mp_rule(mp_rule(int_arith_rule(
          `0i <= (left:int) ==> ~(left == 0i) ==>
           1i <= left`), left_lower), left_nonzero);
      thm tail_bounds = mp_rule(mp_rule(mp_rule(int_arith_rule(
          `1i <= (left:int) ==> left < (right:int) ==>
           right < 1i + ilength (a1:(cm_slot_d)list) ==>
           0i <= left - 1i &&
           left - 1i < right - 1i &&
           right - 1i < ilength a1`),
          left_one), left_right), right_upper);
      thm ih = match_mp_rule(
          cm_call_finish_assumption(zero_cases[1],
            `cm_slot_sizes_positive
               (structs:(cm_struct_d)list) (a1:(cm_slot_d)list) ==>
             !(left:int) right base.
               0i <= left ==> left < right ==>
               right < ilength a1 ==>
               cm_range_disjoint
                 (base + cm_slots_prefix structs a1 left)
                 (cm_slot_size structs (inth left a1))
                 (base + cm_slots_prefix structs a1 right)
                 (cm_slot_size structs (inth right a1))`),
          conjunct2_rule(positive));
      thm tail_result = match_mp_rule(match_mp_rule(match_mp_rule(
          specl_rule(TERM_LIST(
            `(left:int) - 1i`, `(right:int) - 1i`,
            `(base:int) + cm_slot_size
              (structs:(cm_struct_d)list) (a0:cm_slot_d)`), ih),
          conjunct1_rule(tail_bounds)),
          conjunct1_rule(conjunct2_rule(tail_bounds))),
          conjunct2_rule(conjunct2_rule(tail_bounds)));
      thm right_one = mp_rule(int_arith_rule(
          `1i <= (left:int) ==> left < (right:int) ==>
           1i <= right`), left_one);
      right_one = mp_rule(right_one, left_right);
      thm right_nonzero = mp_rule(int_arith_rule(
          `1i <= (right:int) ==> ~(right == 0i)`), right_one);
      thm left_at_tail = mp_rule(ispecl_rule(TERM_LIST(
          `a0:cm_slot_d`, `a1:(cm_slot_d)list`, `left:int`),
          cm_inth_cons_tail), left_one);
      thm right_at_tail = mp_rule(ispecl_rule(TERM_LIST(
          `a0:cm_slot_d`, `a1:(cm_slot_d)list`, `right:int`),
          cm_inth_cons_tail), right_one);
      gnode reduced = CONV_WITH_ASMP_TAC(
          zero_cases[1], reduce_rewrite_conv, THM_LIST(
            get_cm_slots_prefix_def(), left_nonzero,
            right_nonzero,
            left_at_tail, right_at_tail,
            int_ring_rule(
              `!(base:int) head prefix.
                 base + (head + prefix) ==
                 (base + head) + prefix`)));
      ACCEPT_TAC(reduced, tail_result);
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_slot_cells_disjoint =
    cm_prove_slot_cells_disjoint();


PROOF thm get_cm_state_store_commute(void) {
  return cm_state_store_commute;
}
PROOF thm get_cm_slot_cells_disjoint(void) {
  return cm_slot_cells_disjoint;
}


PROOF static int cmc_preservation_call_finish_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_call_finish_axioms_before,
      "cmc_preservation_call_finish introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_call_finish_checks =
    cmc_preservation_call_finish_final_checks();
