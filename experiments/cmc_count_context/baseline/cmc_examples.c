#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_sim.h"
#require "cmc_sim.c"
#include "cmc_stack.h"
#require "cmc_stack.c"
#include "cmc_examples.h"
#include "cmc_examples_internal.h"

PROOF static size_t _cmc_examples_axioms_before = vector_size(get_all_axioms());

PROOF static thm cm_prove_all_inth(void) {
  gnode root = gnode_new_with_ccl(
      `!(values:(A)list) (predicate:A->bool).
         (!index.
            0i <= index && index < ilength values ==>
            predicate (inth index values)) <=>
         ALL predicate values`);
  gnode_list list_cases = INDUCT_TAC(root, `values:(A)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(list_cases[0]);
    gnode_list directions = EQ_TAC(leaf);
    {
      gnode reduced = CONV_TAC(directions[0],
          reduce_rewrite_conv(THM_LIST(
            get_theorem_by_name("ALL"))));
      if (IS_NULL(reduced->solved)) {
        ACCEPT_TAC(reduced, taut_rule(goal_ccl(reduced->g)));
      }
    }
    {
      gnode impossible = AUTO_INTROS_TAC(directions[1]);
      thm bounds = assume_rule(
          `0i <= (index:int) &&
           index < ilength ([]:(A)list)`);
      bounds = pure_rewrite_rule(THM_LIST(
          get_theorem_by_name("ILENGTH_DEF")), bounds);
      CONTR_TAC(impossible, mp_rule(
          int_arith_rule(mk_imp(concl(bounds), `F`)), bounds));
    }
  }
  {
    gnode leaf = AUTO_INTROS_TAC(list_cases[1]);
    thm ih = assume_rule(
        `!(predicate:A->bool).
           (!index.
              0i <= index &&
              index < ilength (a1:(A)list) ==>
              predicate (inth index a1)) <=>
           ALL predicate a1`);
    gnode_list directions = EQ_TAC(leaf);
    {
      gnode forward = AUTO_INTROS_TAC(directions[0]);
      thm indexed = assume_rule(
          `!index.
             0i <= index &&
             index < ilength ((a0:A) :: (a1:(A)list)) ==>
             (predicate:A->bool)
               (inth index (a0 :: a1))`);
      thm tail_nonnegative = ispec_rule(
          `a1:(A)list`, get_theorem_by_name("ILENGTH_NONNEG"));
      thm head_bounds = by_defs_arith(
          `0i <= 0i &&
           0i < ilength ((a0:A) :: (a1:(A)list))`,
          THM_LIST(get_theorem_by_name("ILENGTH_DEF")),
          THM_LIST(tail_nonnegative));
      thm head = mp_rule(spec_rule(`0i`, indexed), head_bounds);
      head = conv_rule(rewrite_conv(THM_LIST(
          cm_inth_zero_cons)), head);

      gnode tail_root = gnode_new_with_ccl(
          `(!parent_index.
              0i <= parent_index &&
              parent_index <
                ilength ((a0:A) :: (a1:(A)list)) ==>
              (predicate:A->bool)
                (inth parent_index (a0 :: a1))) ==>
           !index.
             0i <= index &&
             index < ilength (a1:(A)list) ==>
             predicate (inth index a1)`);
      gnode tail_leaf = AUTO_INTROS_TAC(tail_root);
      thm parent_indexed = assume_rule(
          `!parent_index.
             0i <= parent_index &&
             parent_index <
               ilength ((a0:A) :: (a1:(A)list)) ==>
             (predicate:A->bool)
               (inth parent_index (a0 :: a1))`);
      thm tail_bounds = assume_rule(
          `0i <= (index:int) &&
           index < ilength (a1:(A)list)`);
      thm parent_bounds = by_defs_arith(
          `0i <= (index:int) + 1i &&
           index + 1i <
             ilength ((a0:A) :: (a1:(A)list))`,
          THM_LIST(get_theorem_by_name("ILENGTH_DEF")),
          THM_LIST(tail_bounds, tail_nonnegative));
      thm parent = mp_rule(spec_rule(
          `(index:int) + 1i`, parent_indexed), parent_bounds);
      thm shifted = mp_rule(ispecl_rule(TERM_LIST(
          `a0:A`, `a1:(A)list`, `(index:int) + 1i`),
          cm_inth_cons_tail),
          mp_rule(int_arith_rule(
            `0i <= (index:int) ==> 1i <= index + 1i`),
            conjunct1_rule(tail_bounds)));
      shifted = conv_rule(rewrite_conv(THM_LIST(
          int_arith_rule(`((index:int) + 1i) - 1i == index`))),
          shifted);
      ACCEPT_TAC(tail_leaf, eq_mp_rule(
          beta_norm(ap_term_rule(
            `\element:A. (predicate:A->bool) element`,
            shifted)), parent));
      thm tail_indexed = mp_rule(
          gnode_prove(tail_root), indexed);
      thm tail_all = eq_mp_rule(
          spec_rule(`predicate:A->bool`, ih), tail_indexed);
      gnode reduced = CONV_TAC(forward,
          reduce_rewrite_conv(THM_LIST(
            get_theorem_by_name("ALL"))));
      if (IS_NULL(reduced->solved)) {
        ACCEPT_TAC(reduced, conj_rule(head, tail_all));
      }
    }
    {
      gnode backward = AUTO_INTROS_TAC(directions[1]);
      thm all_values = assume_rule(
          `ALL (predicate:A->bool)
             ((a0:A) :: (a1:(A)list))`);
      thm all_parts = conv_rule(reduce_rewrite_conv(THM_LIST(
          get_theorem_by_name("ALL"))), all_values);
      thm tail_indexed = eq_mp_rule(
          sym_rule(spec_rule(`predicate:A->bool`, ih)),
          conjunct2_rule(all_parts));
      thm parent_bounds = assume_rule(
          `0i <= (index:int) &&
           index <
             ilength ((a0:A) :: (a1:(A)list))`);
      thm parent_nonnegative = conjunct1_rule(parent_bounds);
      gnode_list index_cases = BOOL_CASES_TAC(
          backward, `(index:int) == 0i`, "hindex_zero");
      {
        thm zero = assume_rule(`(index:int) == 0i`);
        gnode reduced = CONV_TAC(index_cases[0],
            reduce_rewrite_conv(THM_LIST(
              zero, cm_inth_zero_cons)));
        if (IS_NULL(reduced->solved)) {
          ACCEPT_TAC(reduced, conjunct1_rule(all_parts));
        }
      }
      {
        thm nonzero = assume_rule(
            `~((index:int) == 0i)`);
        thm one = mp_rule(mp_rule(int_arith_rule(
            `0i <= (index:int) ==>
             ~(index == 0i) ==> 1i <= index`),
            parent_nonnegative), nonzero);
        thm expanded_bounds = conv_rule(
            reduce_rewrite_conv(THM_LIST(
              get_theorem_by_name("ILENGTH_DEF"))),
            parent_bounds);
        thm tail_bounds = mp_rule(int_arith_rule(mk_imp(
            mk_conj(concl(expanded_bounds), concl(one)),
            `0i <= (index:int) - 1i &&
             index - 1i < ilength (a1:(A)list)`)),
            conj_rule(expanded_bounds, one));
        thm tail = mp_rule(spec_rule(
            `(index:int) - 1i`, tail_indexed), tail_bounds);
        thm shifted = mp_rule(ispecl_rule(TERM_LIST(
            `a0:A`, `a1:(A)list`, `index:int`),
            cm_inth_cons_tail), one);
        ACCEPT_TAC(index_cases[1], eq_mp_rule(
            beta_norm(ap_term_rule(
              `\element:A. (predicate:A->bool) element`,
              sym_rule(shifted))), tail));
      }
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_all_inth = cm_prove_all_inth();

PROOF static thm cm_prove_all_inth_imp(void) {
  gnode root = gnode_new_with_ccl(
      `!(values:(A)list) (predicate:A->bool).
         (!index.
            0i <= index ==> index < ilength values ==>
            predicate (inth index values)) <=>
         ALL predicate values`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list directions = EQ_TAC(leaf);
  {
    gnode forward = AUTO_INTROS_TAC(directions[0]);
    thm nested = assume_rule(
        `!index.
           0i <= index ==> index < ilength (values:(A)list) ==>
           (predicate:A->bool) (inth index values)`);
    gnode rewritten = CONV_TAC(forward,
        once_rewrite_conv(THM_LIST(
          sym_rule(specl_rule(TERM_LIST(
            `values:(A)list`, `predicate:A->bool`),
            cm_all_inth)))));
    gnode indexed = AUTO_INTROS_TAC(rewritten);
    thm bounds = assume_rule(
        `0i <= (index:int) &&
         index < ilength (values:(A)list)`);
    ACCEPT_TAC(indexed, mp_rule(mp_rule(
        spec_rule(`index:int`, nested),
        conjunct1_rule(bounds)), conjunct2_rule(bounds)));
  }
  {
    gnode backward = AUTO_INTROS_TAC(directions[1]);
    thm all_values = assume_rule(
        `ALL (predicate:A->bool) (values:(A)list)`);
    thm indexed_values = eq_mp_rule(
        sym_rule(specl_rule(TERM_LIST(
          `values:(A)list`, `predicate:A->bool`),
          cm_all_inth)), all_values);
    gnode indexed = AUTO_INTROS_TAC(backward);
    thm lower = assume_rule(`0i <= (index:int)`);
    thm upper = assume_rule(
        `(index:int) < ilength (values:(A)list)`);
    ACCEPT_TAC(indexed, mp_rule(spec_rule(
        `index:int`, indexed_values),
        conj_rule(lower, upper)));
  }
  return gnode_prove(root);
}
PROOF thm cm_all_inth_imp = cm_prove_all_inth_imp();

PROOF static thm cm_prove_code_shape_all(void) {
  thm result = apply_conversion(rewrite_conv(THM_LIST(
      get_tvm_code_shape_def(), cm_all_inth_imp)),
      `tvm_code_shape (code:(tvm_inst)list)`);
  return gen_rule(`code:(tvm_inst)list`, result);
}
PROOF thm cm_tvm_code_shape_all = cm_prove_code_shape_all();

PROOF static thm cm_prove_patches_valid_all(void) {
  thm result = apply_conversion(rewrite_conv(THM_LIST(
      get_tvm_patches_valid_def(), cm_all_inth_imp)),
      `tvm_patches_valid (patches:(tvm_patch)list)`);
  return gen_rule(`patches:(tvm_patch)list`, result);
}
PROOF thm cm_tvm_patches_valid_all =
    cm_prove_patches_valid_all();

PROOF static thm cm_prove_targets_valid_all(void) {
  thm result = apply_conversion(rewrite_conv(THM_LIST(
      get_tvm_targets_valid_def(), cm_all_inth_imp)),
      `tvm_targets_valid (code:(tvm_inst)list)`);
  return gen_rule(`code:(tvm_inst)list`, result);
}
PROOF thm cm_tvm_targets_valid_all =
    cm_prove_targets_valid_all();

PROOF static term cm_example_putc_neg1_program(void) {
  return
    `CMProgram [] [] []
       [CMFunctionD CMIntTy [] []
         (CMSeqS
           (CMExprS
             (CMPutcE (CMConstE 65i CMIntTy) CMIntTy))
           (CMReturnS (CMConstE (--1i) CMIntTy)))]
       0i`;
}

PROOF static term cm_example_short_circuit_program(void) {
  return
    `CMProgram [] [] []
       [CMFunctionD CMIntTy [] []
         (CMReturnS
           (CMBinaryE 1i
             (CMConstE 0i CMIntTy)
             (CMPutcE (CMConstE 88i CMIntTy) CMIntTy)
             CMIntTy))]
       0i`;
}

PROOF static term cm_example_pointer_stride_program(void) {
  return
    `CMProgram [] [] []
       [CMFunctionD CMIntTy []
         [CMSlotD CMIntTy 2i]
         (CMSeqS (CMDeclS 0i)
           (CMSeqS
             (CMExprS
               (CMAssignE
                 (CMIndexE
                   (CMVarE 1i 0i (CMPtrTy CMIntTy))
                   (CMConstE 0i CMIntTy) CMIntTy)
                 (CMConstE 1i CMIntTy) CMIntTy))
             (CMSeqS
               (CMExprS
                 (CMAssignE
                   (CMIndexE
                     (CMVarE 1i 0i (CMPtrTy CMIntTy))
                     (CMConstE 1i CMIntTy) CMIntTy)
                   (CMConstE 7i CMIntTy) CMIntTy))
               (CMSeqS
                 (CMExprS
                   (CMPutiE
                     (CMIndexE
                       (CMVarE 1i 0i (CMPtrTy CMIntTy))
                       (CMConstE 0i CMIntTy) CMIntTy)
                     CMIntTy))
                 (CMSeqS
                   (CMExprS
                     (CMPutiE
                       (CMIndexE
                         (CMVarE 1i 0i (CMPtrTy CMIntTy))
                         (CMConstE 1i CMIntTy) CMIntTy)
                       CMIntTy))
                   (CMReturnS (CMConstE 0i CMIntTy)))))))]
       0i`;
}

PROOF static thm cm_num_step_at(
    const thm step, const term variable, const term index);
PROOF static void cm_add_num_steps(
    thm_list *rules, const thm step, const size_t count);
PROOF static void cm_add_free_num_steps(
    thm_list *rules, const thm step, const term variable,
    const size_t count);

PROOF static thm_list cm_source_closed_eval_rules_count(
    const size_t iteration_count) {
  thm_list rules = get_cm_wf_eval_defs();
  vector_add(&rules, get_tower_wrap64_def());
  vector_add(&rules, get_tower_u8_def());
  vector_add(&rules, get_tower_add_def());
  vector_add(&rules, get_tower_sub_def());
  vector_add(&rules, get_tower_mul_def());
  vector_add(&rules, get_tower_neg_def());
  vector_add(&rules, get_tower_tquot_def());
  vector_add(&rules, get_tower_trem_def());
  vector_add(&rules, get_tower_div_def());
  vector_add(&rules, get_tower_mod_def());
  vector_add(&rules, get_tower_bool_def());
  vector_add(&rules, get_cm_struct_size_def());
  vector_add(&rules, get_cm_local_slot_ok_def());
  vector_add(&rules, get_cm_member_offset_def());
  vector_add(&rules, get_datatype_distinctness("cm_type"));
  vector_add(&rules, get_datatype_injectivity("cm_type"));
  vector_add(&rules, get_tower_status_def());
  vector_add(&rules, get_tower_setw_def());
  vector_add(&rules, get_tower_setb_def());
  vector_add(&rules, get_tower_getb_def());
  vector_add(&rules, get_tower_getw_def());
  vector_add(&rules, get_tower_zero_mem_def());
  vector_add(&rules, get_theorem_by_name("APPEND"));
  vector_add(&rules, get_theorem_by_name("ALL"));
  vector_add(&rules, get_theorem_by_name("APPEND_NIL"));
  vector_add(&rules, get_theorem_by_name("ILENGTH_DEF"));
  vector_add(&rules, get_cm_type_int_char_distinct());
  vector_add(&rules, get_tower_signed64_def());
  vector_add(&rules, get_tower_byte_value_def());
  vector_add(&rules, get_tower_digit_def());
  vector_add(&rules, get_tower_digits_def());
  vector_add(&rules, get_tower_decimal_def());
  vector_add(&rules, get_tower_addr_valid_def());
  vector_add(&rules, get_tower_word_valid_def());
  vector_add(&rules, get_tower_encode_byte_def());
  vector_add(&rules, get_tower_decode8_def());
  vector_add(&rules, get_theorem_by_name("INTH_DEF"));
  vector_add(&rules, get_theorem_by_name("NUM_OF_INT_OF_NUM"));
  vector_add(&rules, get_theorem_by_name("NTH_DEF"));
  vector_add(&rules, get_theorem_by_name("HD"));
  vector_add(&rules, get_theorem_by_name("TL"));
  vector_add(&rules, get_theorem_by_name("NOT_CONS_NIL"));
  vector_add(&rules, get_theorem_by_name("COND_ID"));
  vector_add(&rules, get_theorem_by_name("REVERSE"));
  vector_add(&rules, get_theorem_by_name("LENGTH"));
  cm_add_num_steps(&rules, conjunct2_rule(get_cm_iter_def()),
      iteration_count);
  cm_add_free_num_steps(&rules,
      conjunct2_rule(get_theorem_by_name("NTH_DEF")),
      `n:num`, iteration_count);
  return rules;
}

PROOF static thm_list cm_source_closed_eval_rules(void) {
  return cm_source_closed_eval_rules_count(13);
}

PROOF conv cm_source_closed_eval_conv_count(
    const size_t iteration_count) {
  conv pass = reduce_rewrite_conv(
      cm_source_closed_eval_rules_count(iteration_count));
  conv result = pass;
  for (size_t i = 1; i < iteration_count * 64 + 257; ++i) {
    result = then_conv(result, pass);
  }
  return result;
}

PROOF static conv cm_source_closed_eval_conv(void) {
  return cm_source_closed_eval_conv_count(13);
}


PROOF static thm_list cm_target_closed_eval_rules_count(
    const size_t iteration_count) {
  thm_list rules = get_cm_codegen_eval_defs();
  thm_list source_rules = get_cm_wf_eval_defs();
  thm_list target_rules = get_tvm_eval_defs();
  for (size_t i = 0; i < vector_size(source_rules); ++i) {
    vector_add(&rules, source_rules[i]);
  }
  for (size_t i = 0; i < vector_size(target_rules); ++i) {
    vector_add(&rules, target_rules[i]);
  }
  thm_list shared = THM_LIST(
      get_tower_signed64_def(), get_tower_byte_value_def(),
      get_tower_wrap64_def(), get_tower_u8_def(),
      get_tower_status_def(), get_tower_bool_def(),
      get_tower_add_def(), get_tower_sub_def(),
      get_tower_mul_def(), get_tower_neg_def(),
      get_tower_tquot_def(), get_tower_trem_def(),
      get_tower_div_def(), get_tower_mod_def(),
      get_tower_encode_byte_def(), get_tower_decode8_def(),
      get_tower_word_bytes_def(), get_tower_addr_valid_def(),
      get_cm_struct_size_def(), get_cm_member_offset_def(),
      get_theorem_by_name("APPEND_NIL"),
      get_theorem_by_name("ALL"),
      get_theorem_by_name("HD"), get_theorem_by_name("TL"),
      get_theorem_by_name("NOT_CONS_NIL"),
      get_theorem_by_name("INTH_DEF"),
      get_theorem_by_name("NUM_OF_INT_OF_NUM"),
      get_theorem_by_name("NTH_DEF"),
      get_tower_word_valid_def(), get_tower_zero_mem_def(),
      get_tower_getb_def(), get_tower_setb_def(),
      get_cm_imax_def(),
      get_theorem_by_name("IREPLICATE_DEF"),
      get_theorem_by_name("REPLICATE"),
      get_tower_getw_def(), get_tower_setw_def(),
      get_tower_digit_def(), get_tower_digits_def(),
      get_tower_decimal_def(),
      get_theorem_by_name("REVERSE"),
      get_theorem_by_name("LENGTH"),
      get_theorem_by_name("APPEND"),
      get_theorem_by_name("APPEND_NIL"),
      get_theorem_by_name("ILENGTH_DEF"));
  for (size_t i = 0; i < vector_size(shared); ++i) {
    vector_add(&rules, shared[i]);
  }
  vector_add(&rules, get_cm_type_int_char_distinct());
  vector_add(&rules, get_datatype_distinctness("cm_type"));
  vector_add(&rules, get_datatype_injectivity("cm_type"));
  cm_add_num_steps(&rules, conjunct2_rule(get_tvm_iter_def()),
      iteration_count);
  cm_add_free_num_steps(&rules,
      conjunct2_rule(get_theorem_by_name("REPLICATE")),
      `n:num`, 32);
  cm_add_free_num_steps(&rules,
      conjunct2_rule(get_theorem_by_name("NTH_DEF")),
      `n:num`, iteration_count);
  return rules;
}

PROOF static thm_list cm_target_closed_eval_rules(void) {
  return cm_target_closed_eval_rules_count(100);
}

PROOF conv cm_target_closed_eval_conv_count(
    const size_t iteration_count) {
  conv pass = reduce_rewrite_conv(
      cm_target_closed_eval_rules_count(iteration_count));
  conv result = pass;
  for (size_t i = 1; i < iteration_count * 8 + 257; ++i) {
    result = then_conv(result, pass);
  }
  return result;
}

PROOF static conv cm_target_closed_eval_conv(void) {
  return cm_target_closed_eval_conv_count(100);
}

PROOF static thm cm_prove_nonnegative_not_negative(void) {
  gnode root = gnode_new_with_ccl(
      `!(number:int). 0i <= number ==> ~(number < 0i)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm nonnegative = assume_rule(`0i <= (number:int)`);
  thm negative = assume_rule(`(number:int) < 0i`);
  CONTR_TAC(leaf, mp_rule(int_arith_rule(
      `0i <= (number:int) && number < 0i ==> F`),
      conj_rule(nonnegative, negative)));
  return gnode_prove(root);
}
PROOF thm cm_nonnegative_not_negative =
    cm_prove_nonnegative_not_negative();
PROOF static thm cm_num_step_at(
    const thm step, const term variable, const term index) {
  thm successor = apply_conversion(
      get_conversion_by_name("NUM_SUC_CONV"),
      mk_comb(`SUC`, index));
  return conv_rule(rewrite_conv(THM_LIST(successor)),
      inst_rule(TERM_PAIR_LIST(
        (term_pair){index, variable}), step));
}
PROOF static void cm_add_num_steps(
    thm_list *rules, const thm step, const size_t count) {
  term index = `0`;
  for (size_t i = 0; i < count; ++i) {
    thm successor = apply_conversion(
        get_conversion_by_name("NUM_SUC_CONV"),
        mk_comb(`SUC`, index));
    vector_add(rules, conv_rule(
        rewrite_conv(THM_LIST(successor)),
        spec_rule(index, step)));
    index = rhs_of(successor);
  }
}
PROOF static void cm_add_free_num_steps(
    thm_list *rules, const thm step, const term variable,
    const size_t count) {
  term index = `0`;
  for (size_t i = 0; i < count; ++i) {
    vector_add(rules, cm_num_step_at(step, variable, index));
    thm successor = apply_conversion(
        get_conversion_by_name("NUM_SUC_CONV"),
        mk_comb(`SUC`, index));
    index = rhs_of(successor);
  }
}

PROOF static thm cm_prove_forall_below_one(void) {
  gnode root = gnode_new_with_ccl(
      `!(predicate:int->bool).
         (!index. 0i <= index ==> index < 1i ==> predicate index) <=>
         predicate 0i`);
  gnode quantified = GEN_TAC(root, "predicate");
  gnode_list directions = EQ_TAC(quantified);
  {
    gnode leaf = AUTO_INTROS_TAC(directions[0]);
    thm indexed = assume_rule(
        `!index. 0i <= index ==> index < 1i ==>
           (predicate:int->bool) index`);
    ACCEPT_TAC(leaf, mp_rule(mp_rule(
        spec_rule(`0i`, indexed),
        int_arith_rule(`0i <= 0i`)),
        int_arith_rule(`0i < 1i`)));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(directions[1]);
    thm at_zero = assume_rule(`(predicate:int->bool) 0i`);
    thm lower = assume_rule(`0i <= (index:int)`);
    thm upper = assume_rule(`(index:int) < 1i`);
    thm zero = mp_rule(int_arith_rule(
        `0i <= (index:int) && index < 1i ==> index == 0i`),
        conj_rule(lower, upper));
    ACCEPT_TAC(leaf, eq_mp_rule(
        sym_rule(beta_norm(ap_term_rule(
          `\x0:int. (predicate:int->bool) x0`, zero))),
        at_zero));
  }
  return gnode_prove(root);
}

PROOF thm cm_forall_below_one = cm_prove_forall_below_one();

PROOF static thm cm_prove_forall_below_two(void) {
  gnode root = gnode_new_with_ccl(
      `!(predicate:int->bool).
         (!index. 0i <= index ==> index < 2i ==> predicate index) <=>
         predicate 0i && predicate 1i`);
  gnode quantified = GEN_TAC(root, "predicate");
  gnode_list directions = EQ_TAC(quantified);
  {
    gnode leaf = AUTO_INTROS_TAC(directions[0]);
    thm indexed = assume_rule(
        `!index. 0i <= index ==> index < 2i ==>
           (predicate:int->bool) index`);
    thm at_zero = mp_rule(mp_rule(spec_rule(`0i`, indexed),
        int_arith_rule(`0i <= 0i`)), int_arith_rule(`0i < 2i`));
    thm at_one = mp_rule(mp_rule(spec_rule(`1i`, indexed),
        int_arith_rule(`0i <= 1i`)), int_arith_rule(`1i < 2i`));
    ACCEPT_TAC(leaf, conj_rule(at_zero, at_one));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(directions[1]);
    thm values = assume_rule(
        `(predicate:int->bool) 0i && predicate 1i`);
    thm lower = assume_rule(`0i <= (index:int)`);
    thm upper = assume_rule(`(index:int) < 2i`);
    gnode_list cases = BOOL_CASES_TAC(
        leaf, `(index:int) == 0i`, "below_two_zero");
    {
      thm zero = assume_rule(`(index:int) == 0i`);
      ACCEPT_TAC(cases[0], eq_mp_rule(
          sym_rule(beta_norm(ap_term_rule(
            `\x0:int. (predicate:int->bool) x0`, zero))),
          conjunct1_rule(values)));
    }
    {
      thm nonzero = assume_rule(`~((index:int) == 0i)`);
      thm one = mp_rule(int_arith_rule(
          `0i <= (index:int) && index < 2i &&
           ~(index == 0i) ==> index == 1i`),
          conj_rule(lower, conj_rule(upper, nonzero)));
      ACCEPT_TAC(cases[1], eq_mp_rule(
          sym_rule(beta_norm(ap_term_rule(
            `\x0:int. (predicate:int->bool) x0`, one))),
          conjunct2_rule(values)));
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_forall_below_two = cm_prove_forall_below_two();




PROOF static thm_list cm_closed_wf_rules(void) {
  thm_list rules = get_cm_wf_eval_defs();
  thm_list codegen_rules = get_cm_codegen_eval_defs();
  for (size_t i = 0; i < vector_size(codegen_rules); ++i) {
    vector_add(&rules, codegen_rules[i]);
  }
  vector_add(&rules, get_datatype_distinctness("cm_type"));
  vector_add(&rules, get_datatype_injectivity("cm_type"));
  thm_list runtime_rules = get_cm_runtime_defs();
  for (size_t i = 0; i < vector_size(runtime_rules); ++i) {
    vector_add(&rules, runtime_rules[i]);
  }
  thm_list shared = THM_LIST(
      get_cm_wf_program_def(), get_cm_codegen_admissible_def(),
      get_cm_codegen_fields_representable_def(),
      get_cm_codegen_counts_representable_def(),
      get_cm_functions_counts_representable_def(),
      get_cm_function_pcs_representable_def(),
      get_cm_function_counts_representable_def(),
      get_cm_param_counts_representable_def(),
      get_cm_stmt_counts_representable_def(),
      get_cm_expr_counts_representable_def(),
      get_cm_expr_count_node_representable_def(),
      get_cm_args_counts_representable_def(),
      get_cm_code_counts_representable_def(),
      get_cm_i32_code_count_def(),
      get_cm_stack_bound_model_def(),
      get_cm_max_function_arity_from_def(),
      cm_forall_below_one, cm_forall_below_two,
      get_cm_max_function_arity_def(),
      get_cm_type_int_char_distinct(), cm_nonnegative_not_negative,
      cm_all_inth_imp,
      cm_tvm_code_shape_all, cm_tvm_patches_valid_all,
      cm_tvm_targets_valid_all,
      get_tvm_target_valid_def(), get_tvm_opcode_has_imm_def(),
      get_tvm_opcode_is_target_def(), get_tvm_inst_shape_def(),
      get_tvm_patch_valid_def(), get_tvm_inst_op_def(),
      get_tvm_inst_imm_def(), get_tvm_patch_addr_def(),
      get_tvm_patch_byte_def(),
      get_tower_signed64_def(), get_tower_byte_value_def(),
      get_tower_addr_valid_def(), get_tower_wrap64_def(),
      get_cm_struct_size_def(), get_cm_member_offset_def(),
      get_cm_static_size_def(),
      get_theorem_by_name("ALL"), get_theorem_by_name("APPEND"),
      get_theorem_by_name("NOT_CONS_NIL"),
      get_theorem_by_name("APPEND_NIL"),
      get_theorem_by_name("ILENGTH_DEF"),
      get_theorem_by_name("INTH_DEF"),
      get_theorem_by_name("NUM_OF_INT_OF_NUM"),
      get_theorem_by_name("NTH_DEF"),
      get_theorem_by_name("IREPLICATE_DEF"),
      get_theorem_by_name("REPLICATE"),
      cm_num_step_at(
        conjunct2_rule(get_theorem_by_name("REPLICATE")),
        `n:num`, `0`),
      cm_num_step_at(
        conjunct2_rule(get_theorem_by_name("REPLICATE")),
        `n:num`, `1`),
      cm_num_step_at(
        conjunct2_rule(get_theorem_by_name("REPLICATE")),
        `n:num`, `2`),
      cm_num_step_at(
        conjunct2_rule(get_theorem_by_name("REPLICATE")),
        `n:num`, `3`),
      cm_num_step_at(
        conjunct2_rule(get_theorem_by_name("REPLICATE")),
        `n:num`, `4`),
      cm_num_step_at(
        conjunct2_rule(get_theorem_by_name("REPLICATE")),
        `n:num`, `5`),
      cm_num_step_at(
        conjunct2_rule(get_theorem_by_name("REPLICATE")),
        `n:num`, `6`),
      cm_num_step_at(
        conjunct2_rule(get_theorem_by_name("REPLICATE")),
        `n:num`, `7`));
  cm_add_free_num_steps(&rules,
      conjunct2_rule(get_theorem_by_name("NTH_DEF")),
      `n:num`, 32);
  cm_add_free_num_steps(&rules,
      conjunct2_rule(get_theorem_by_name("REPLICATE")),
      `n:num`, 32);
  for (size_t i = 0; i < vector_size(shared); ++i) {
    vector_add(&rules, shared[i]);
  }
  return rules;
}

PROOF conv cm_closed_wf_conv(void) {
  conv pass = reduce_rewrite_conv(cm_closed_wf_rules());
  conv result = pass;
  for (size_t i = 1; i < 240; ++i) {
    result = then_conv(result, pass);
  }
  return result;
}

PROOF thm cm_example_putc_neg1_wf = eqt_elim_rule(apply_conversion(
    cm_closed_wf_conv(),
    mk_comb(`cm_wf_program`, cm_example_putc_neg1_program())));

PROOF thm cm_example_putc_neg1_target_iter = apply_conversion(
    cm_target_closed_eval_conv(),
    mk_comb(mk_comb(`tvm_iter`, `100`),
      mk_comb(mk_comb(`TVMRunTask`,
        mk_comb(`cm_compile_model`, cm_example_putc_neg1_program())),
        mk_comb(mk_comb(`tvm_initial_state`,
          mk_comb(`cm_compile_model`, cm_example_putc_neg1_program())),
          `[]:(int)list`))));

PROOF thm cm_example_putc_neg1_source_iter = apply_conversion(
    cm_source_closed_eval_conv(),
    mk_comb(mk_comb(`cm_iter`, `13`),
      mk_comb(mk_comb(`CMStartTask`,
        cm_example_putc_neg1_program()), `[]:(int)list`)));

PROOF thm cm_prove_closed_example_source(
    const term program, const term input, const term output,
    const term expected_status, const term iteration_count,
    const size_t evaluation_count, const thm iteration_theorem) {
  term iteration = dest_eq(concl(iteration_theorem)).tm1;
  term task = dest_comb(iteration).tm2;
  thm_list rules = cm_source_closed_eval_rules_count(evaluation_count);
  vector_add(&rules, iteration_theorem);
  thm done = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(rules),
      mk_comb(`cm_task_done`, iteration)));
  thm run = mp_rule(specl_rule(
      TERM_LIST(iteration_count, task), get_cm_done_iter_exec()), done);
  run = conv_rule(reduce_rewrite_conv(rules), run);

  term outcome = dest_comb(concl(run)).tm2;
  dest_comb_results status_app = dest_comb(outcome);
  term actual_status = status_app.tm2;
  dest_comb_results control_app = dest_comb(status_app.tm1);
  term control = control_app.tm2;
  term state = dest_comb(control_app.tm1).tm2;

  thm valid = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(rules),
      mk_comb(`cm_valid_input`, input)));
  thm byte = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(rules),
      mk_comb(`tower_byte_value`, actual_status)));
  thm success = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(rules),
      mk_comb(`cm_success_control`, control)));
  thm observed_output = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(rules),
      mk_eq(mk_comb(`cm_state_output`, state), output)));

  gnode root = gnode_new_with_ccl(
      `cm_source_terminates (${program:cm_program})
         (${input:(int)list}) (${output:(int)list})
         (${expected_status:int})`);
  gnode expanded = CONV_TAC(root,
      rewrite_conv(THM_LIST(get_cm_source_terminates_def())));
  gnode_list outer = CONJ_TAC(expanded);
  ACCEPT_TAC(outer[0], valid);
  gnode_list rest = CONJ_TAC(outer[1]);
  ACCEPT_TAC(rest[0], byte);
  gnode with_state = EXISTS_TAC(rest[1], state);
  gnode with_control = EXISTS_TAC(with_state, control);
  ACCEPT_TAC(with_control,
      conj_rule(run, conj_rule(success, observed_output)));
  return gnode_prove(root);
}

PROOF static thm cm_prove_example_putc_neg1_source(void) {
  return cm_prove_closed_example_source(
      cm_example_putc_neg1_program(), `[]:(int)list`, `[65i]`,
      `255i`, `13`, 13, cm_example_putc_neg1_source_iter);
}

PROOF thm cm_example_putc_neg1_source =
    cm_prove_example_putc_neg1_source();

PROOF thm cm_prove_closed_example_target(
    const term program, const term input, const term output,
    const term expected_status, const term iteration_count,
    const thm wf_theorem, const thm iteration_theorem) {
  term object = mk_comb(`cm_compile_model`, program);
  term iteration = dest_eq(concl(iteration_theorem)).tm1;
  term run_task = dest_comb(iteration).tm2;
  term done_task = dest_eq(concl(iteration_theorem)).tm2;
  dest_comb_results kind_app = dest_comb(done_task);
  term kind = kind_app.tm2;
  dest_comb_results status_app = dest_comb(kind_app.tm1);
  term status = status_app.tm2;
  term state = dest_comb(status_app.tm1).tm2;
  term outcome = mk_comb(mk_comb(mk_comb(
      `TVMOutcome`, state), status), kind);

  thm final_exec = specl_rule(
      TERM_LIST(state, status, kind), get_tvm_exec_done());
  thm iter_exec = conv_rule(rewrite_conv(THM_LIST(
      sym_rule(iteration_theorem))), final_exec);
  thm run_exec = mp_rule(specl_rule(
      TERM_LIST(iteration_count, run_task, outcome),
      get_tvm_exec_prefix()), iter_exec);

  thm object_wf = mp_rule(spec_rule(
      program, get_cmc_object_wf()), wf_theorem);
  thm load = mp_rule(spec_rule(
      object, get_tvm_object_wf_load()), object_wf);
  term boot = mk_comb(mk_comb(`TVMBoot`, object), input);
  thm boot_step = apply_conversion(reduce_rewrite_conv(
      THM_LIST(load, get_tvm_step_def())),
      mk_comb(`tvm_step`, boot));
  thm step_exec = conv_rule(rewrite_conv(
      THM_LIST(sym_rule(boot_step))), run_exec);
  thm boot_exec = mp_rule(specl_rule(
      TERM_LIST(boot, outcome), get_tvm_exec_rule()), step_exec);

  thm_list rules = cm_target_closed_eval_rules();
  thm valid = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(rules),
      mk_comb(`tvm_valid_input`, input)));
  thm byte = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(rules),
      mk_comb(`tower_byte_value`, status)));
  thm observed_output = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(rules),
      mk_eq(mk_comb(`tvm_output`, state), output)));

  gnode root = gnode_new_with_ccl(
      `tvm_terminates (${object:tvm_object})
         (${input:(int)list}) (${output:(int)list})
         (${expected_status:int})`);
  gnode expanded = CONV_TAC(root,
      rewrite_conv(THM_LIST(get_tvm_terminates_def())));
  gnode_list outer = CONJ_TAC(expanded);
  ACCEPT_TAC(outer[0], valid);
  gnode_list rest = CONJ_TAC(outer[1]);
  ACCEPT_TAC(rest[0], byte);
  gnode with_state = EXISTS_TAC(rest[1], state);
  ACCEPT_TAC(with_state, conj_rule(boot_exec, observed_output));
  return gnode_prove(root);
}

PROOF static thm cm_prove_example_putc_neg1_target(void) {
  return cm_prove_closed_example_target(
      cm_example_putc_neg1_program(), `[]:(int)list`, `[65i]`,
      `255i`, `100`, cm_example_putc_neg1_wf,
      cm_example_putc_neg1_target_iter);
}

PROOF thm cm_example_putc_neg1_target =
    cm_prove_example_putc_neg1_target();

PROOF static thm cm_prove_example_putc_neg1(void) {
  thm layout = spec_rule(cm_example_putc_neg1_program(),
      get_cm_codegen_two_pass_layout());
  return conj_rule(cm_example_putc_neg1_wf,
      conj_rule(cm_example_putc_neg1_source,
      conj_rule(cm_example_putc_neg1_target, layout)));
}

PROOF thm cmc_example_putc_neg1 =
    cm_prove_example_putc_neg1();

PROOF thm get_cmc_example_putc_neg1(void) {
  return cmc_example_putc_neg1;
}

PROOF thm cm_example_short_circuit_wf =
    eqt_elim_rule(apply_conversion(
      cm_closed_wf_conv(),
      mk_comb(`cm_wf_program`,
        cm_example_short_circuit_program())));

PROOF thm cm_example_short_circuit_source_iter =
    apply_conversion(
      cm_source_closed_eval_conv(),
      mk_comb(mk_comb(`cm_iter`, `13`),
        mk_comb(mk_comb(`CMStartTask`,
          cm_example_short_circuit_program()), `[]:(int)list`)));

PROOF thm cm_example_short_circuit_target_iter =
    apply_conversion(
      cm_target_closed_eval_conv(),
      mk_comb(mk_comb(`tvm_iter`, `100`),
        mk_comb(mk_comb(`TVMRunTask`,
          mk_comb(`cm_compile_model`,
            cm_example_short_circuit_program())),
          mk_comb(mk_comb(`tvm_initial_state`,
            mk_comb(`cm_compile_model`,
              cm_example_short_circuit_program())),
            `[]:(int)list`))));

PROOF thm cm_example_short_circuit_source =
    cm_prove_closed_example_source(
      cm_example_short_circuit_program(), `[]:(int)list`,
      `[]:(int)list`, `0i`, `13`, 13,
      cm_example_short_circuit_source_iter);

PROOF thm cm_example_short_circuit_target =
    cm_prove_closed_example_target(
      cm_example_short_circuit_program(), `[]:(int)list`,
      `[]:(int)list`, `0i`, `100`,
      cm_example_short_circuit_wf,
      cm_example_short_circuit_target_iter);

PROOF thm cmc_example_short_circuit =
    conj_rule(cm_example_short_circuit_wf,
      conj_rule(cm_example_short_circuit_source,
      conj_rule(cm_example_short_circuit_target,
        spec_rule(cm_example_short_circuit_program(),
          get_cm_codegen_two_pass_layout()))));

PROOF thm get_cmc_example_short_circuit(void) {
  return cmc_example_short_circuit;
}

PROOF thm cm_example_pointer_stride_wf =
    eqt_elim_rule(apply_conversion(
      cm_closed_wf_conv(),
      mk_comb(`cm_wf_program`,
        cm_example_pointer_stride_program())));

PROOF thm cm_example_pointer_stride_source_iter =
    apply_conversion(
      cm_source_closed_eval_conv_count(100),
      mk_comb(mk_comb(`cm_iter`, `100`),
        mk_comb(mk_comb(`CMStartTask`,
          cm_example_pointer_stride_program()), `[]:(int)list`)));



PROOF thm cm_example_pointer_stride_target_iter =
    apply_conversion(
      cm_target_closed_eval_conv_count(400),
      mk_comb(mk_comb(`tvm_iter`, `400`),
        mk_comb(mk_comb(`TVMRunTask`,
          mk_comb(`cm_compile_model`,
            cm_example_pointer_stride_program())),
          mk_comb(mk_comb(`tvm_initial_state`,
            mk_comb(`cm_compile_model`,
              cm_example_pointer_stride_program())),
            `[]:(int)list`))));

PROOF thm cm_example_pointer_stride_source =
    cm_prove_closed_example_source(
      cm_example_pointer_stride_program(), `[]:(int)list`,
      `[49i; 55i]`, `0i`, `100`, 100,
      cm_example_pointer_stride_source_iter);

PROOF thm cm_example_pointer_stride_target =
    cm_prove_closed_example_target(
      cm_example_pointer_stride_program(), `[]:(int)list`,
      `[49i; 55i]`, `0i`, `400`,
      cm_example_pointer_stride_wf,
      cm_example_pointer_stride_target_iter);

PROOF thm cm_example_pointer_stride_address =
    eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(cm_source_closed_eval_rules_count(0)),
      `cm_ptr_offset
         (cm_ptr_add []
           (CMPtrV 1i 0i 16i 0i CMIntTy) 1i) ==
       cm_ptr_offset
         (CMPtrV 1i 0i 16i 0i CMIntTy) + 8i`));

PROOF thm cmc_example_pointer_stride =
    conj_rule(cm_example_pointer_stride_wf,
      conj_rule(cm_example_pointer_stride_source,
      conj_rule(cm_example_pointer_stride_target,
        cm_example_pointer_stride_address)));

PROOF thm get_cmc_example_pointer_stride(void) {
  return cmc_example_pointer_stride;
}

PROOF static term cm_example_expected(
    term program, term input, term output, term status, term extra) {
  term source = `cm_source_terminates (${program:cm_program})
      (${input:(int)list}) (${output:(int)list}) (${status:int})`;
  term target = `tvm_terminates (cm_compile_model (${program:cm_program}))
      (${input:(int)list}) (${output:(int)list}) (${status:int})`;
  return mk_conj(mk_comb(`cm_wf_program`, program),
      mk_conj(source, mk_conj(target, extra)));
}

PROOF static int cmc_examples_final_checks(void) {
  term putc_program = cm_example_putc_neg1_program();
  term short_program = cm_example_short_circuit_program();
  term pointer_program = cm_example_pointer_stride_program();
  term putc_expected = cm_example_expected(
      putc_program, `[]:(int)list`, `[65i]`, `255i`,
      concl(spec_rule(putc_program, get_cm_codegen_two_pass_layout())));
  term short_expected = cm_example_expected(
      short_program, `[]:(int)list`, `[]:(int)list`, `0i`,
      concl(spec_rule(short_program, get_cm_codegen_two_pass_layout())));
  term pointer_expected = cm_example_expected(
      pointer_program, `[]:(int)list`, `[49i; 55i]`, `0i`,
      `cm_ptr_offset
         (cm_ptr_add []
           (CMPtrV 1i 0i 16i 0i CMIntTy) 1i) ==
       cm_ptr_offset
         (CMPtrV 1i 0i 16i 0i CMIntTy) + 8i`);
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_examples_axioms_before,
      "cmc_examples introduced an axiom");
  ENSURE_COND(!IS_NULL(get_cmc_example_putc_neg1()) &&
      vector_size(hyp(get_cmc_example_putc_neg1())) == 0 &&
      vector_size(free_vars(concl(get_cmc_example_putc_neg1()))) == 0 &&
      alpha_compare(concl(get_cmc_example_putc_neg1()),
        putc_expected) == 0,
      "status-normalization example has the wrong contract");
  ENSURE_COND(!IS_NULL(get_cmc_example_short_circuit()) &&
      vector_size(hyp(get_cmc_example_short_circuit())) == 0 &&
      vector_size(free_vars(concl(get_cmc_example_short_circuit()))) == 0 &&
      alpha_compare(concl(get_cmc_example_short_circuit()),
        short_expected) == 0,
      "short-circuit example has the wrong contract");
  ENSURE_COND(!IS_NULL(get_cmc_example_pointer_stride()) &&
      vector_size(hyp(get_cmc_example_pointer_stride())) == 0 &&
      vector_size(free_vars(concl(get_cmc_example_pointer_stride()))) == 0 &&
      alpha_compare(concl(get_cmc_example_pointer_stride()),
        pointer_expected) == 0,
      "pointer-stride example has the wrong contract");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_examples_checks = cmc_examples_final_checks();
