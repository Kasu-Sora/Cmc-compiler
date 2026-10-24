#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_stack.h"
#require "cmc_stack.c"
#include "cmc_preservation_layout.h"

PROOF static size_t _cmc_preservation_layout_axioms_before =
    vector_size(get_all_axioms());

PROOF thm cm_code_at_def = new_fun_definition(
    `cm_code_at (code:(A)list) (pc:int) (fragment:(A)list) : bool =
       (?before after.
          code == APPEND before (APPEND fragment after) &&
          ilength before == pc)`);

PROOF thm cm_function_code_prefix_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(!p start index.
        cm_function_code_prefix (p:cm_program) (start:int)
          ([]:(cm_function_d)list) (index:int) =
        ([]:(tvm_inst)list)) &&
     (!p start fn rest index.
        cm_function_code_prefix (p:cm_program) (start:int)
          ((fn:cm_function_d) :: (rest:(cm_function_d)list))
          (index:int) =
        (if index == 0i
         then []
         else APPEND (cm_emit_function p start)
           (cm_function_code_prefix p (start + 1i) rest
             (index - 1i))))`);
PROOF int _e_cm_function_code_prefix =
    cst_add_const_to_header(`cm_function_code_prefix`);

PROOF static thm cm_prove_code_at_append_left(void) {
  gnode root = gnode_new_with_ccl(
      `!(code:(A)list) (pc:int) (left:(A)list) (right:(A)list).
         cm_code_at code pc (APPEND left right) ==>
         cm_code_at code pc left`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm source = assume_rule(
      `cm_code_at (code:(A)list) (pc:int)
         (APPEND (left:(A)list) (right:(A)list))`);
  thm opened = eq_mp_rule(apply_conversion(
      rewrite_conv(THM_LIST(cm_code_at_def)), concl(source)), source);
  thm body = assume_rule(
      `(code:(A)list) ==
         APPEND (before:(A)list)
           (APPEND (APPEND (left:(A)list) (right:(A)list))
             (after:(A)list)) &&
       ilength before == (pc:int)`);
  thm reassociated = conv_rule(rewrite_conv(THM_LIST(
      gsym_rule(get_theorem_by_name("APPEND_ASSOC")))),
      conjunct1_rule(body));
  thm witness = exists_rule(
      `?before after.
         (code:(A)list) ==
           APPEND before (APPEND (left:(A)list) after) &&
         ilength before == (pc:int)`,
      `before:(A)list`,
      exists_rule(
        `?after.
           (code:(A)list) ==
             APPEND (before:(A)list) (APPEND (left:(A)list) after) &&
           ilength before == (pc:int)`,
        `APPEND (right:(A)list) (after:(A)list)`,
        conj_rule(reassociated, conjunct2_rule(body))));
  thm inner = assume_rule(
      `?after.
         (code:(A)list) ==
           APPEND (before:(A)list)
             (APPEND (APPEND (left:(A)list) (right:(A)list)) after) &&
         ilength before == (pc:int)`);
  thm selected_after =
      choose_rule(`after:(A)list`, inner, witness);
  thm selected_before =
      choose_rule(`before:(A)list`, opened, selected_after);
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(apply_conversion(
      rewrite_conv(THM_LIST(cm_code_at_def)),
      `cm_code_at (code:(A)list) (pc:int) (left:(A)list)`)),
      selected_before));
  return gnode_prove(root);
}

PROOF static thm cm_prove_code_at_front(void) {
  gnode root = gnode_new_with_ccl(
      `!(left:(A)list) (right:(A)list).
         cm_code_at (APPEND left right) 0i left`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm equation = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("APPEND"))),
      `APPEND (left:(A)list) (right:(A)list) ==
         APPEND ([]:(A)list)
           (APPEND left right)`));
  thm empty_length = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF"))),
      `ilength ([]:(A)list) == 0i`));
  thm witness = exists_rule(
      `?before after.
         APPEND (left:(A)list) (right:(A)list) ==
           APPEND before (APPEND left after) &&
         ilength before == 0i`,
      `[]:(A)list`,
      exists_rule(
        `?after.
           APPEND (left:(A)list) (right:(A)list) ==
             APPEND ([]:(A)list) (APPEND left after) &&
           ilength ([]:(A)list) == 0i`,
        `right:(A)list`,
        conj_rule(equation, empty_length)));
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(apply_conversion(
      rewrite_conv(THM_LIST(cm_code_at_def)),
      `cm_code_at
         (APPEND (left:(A)list) (right:(A)list)) 0i left`)),
      witness));
  return gnode_prove(root);
}
PROOF thm cm_code_at_front = cm_prove_code_at_front();
PROOF thm cm_code_at_append_left = cm_prove_code_at_append_left();


PROOF static thm cm_prove_code_at_append_right(void) {
  gnode root = gnode_new_with_ccl(
      `!(code:(A)list) (pc:int) (left:(A)list) (right:(A)list).
         cm_code_at code pc (APPEND left right) ==>
         cm_code_at code (pc + ilength left) right`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm source = assume_rule(
      `cm_code_at (code:(A)list) (pc:int)
         (APPEND (left:(A)list) (right:(A)list))`);
  thm opened = eq_mp_rule(apply_conversion(
      rewrite_conv(THM_LIST(cm_code_at_def)), concl(source)), source);
  thm body = assume_rule(
      `(code:(A)list) ==
         APPEND (before:(A)list)
           (APPEND (APPEND (left:(A)list) (right:(A)list))
             (after:(A)list)) &&
       ilength before == (pc:int)`);
  thm right_associated = conv_rule(rewrite_conv(THM_LIST(
      gsym_rule(get_theorem_by_name("APPEND_ASSOC")))),
      conjunct1_rule(body));
  thm outer_association = specl_rule(TERM_LIST(
      `before:(A)list`, `left:(A)list`,
      `APPEND (right:(A)list) (after:(A)list)`),
      get_theorem_by_name("APPEND_ASSOC"));
  thm arranged = trans_rule(right_associated, outer_association);
  thm joined_length = apply_conversion(
      rewrite_conv(THM_LIST(
        get_theorem_by_name("ILENGTH_APPEND"))),
      `ilength (APPEND (before:(A)list) (left:(A)list))`);
  thm target_length = conv_rule(rewrite_conv(THM_LIST(
      conjunct2_rule(body))), joined_length);
  thm candidate = conj_rule(arranged, target_length);
  thm suffix_witness = exists_rule(
      `?suffix.
         (code:(A)list) ==
           APPEND (APPEND (before:(A)list) (left:(A)list))
             (APPEND (right:(A)list) suffix) &&
         ilength (APPEND before left) ==
           (pc:int) + ilength left`,
      `after:(A)list`, candidate);
  thm witness = exists_rule(
      `?prefix suffix.
         (code:(A)list) ==
           APPEND prefix (APPEND (right:(A)list) suffix) &&
         ilength prefix ==
           (pc:int) + ilength (left:(A)list)`,
      `APPEND (before:(A)list) (left:(A)list)`,
      suffix_witness);
  thm inner = assume_rule(
      `?after.
         (code:(A)list) ==
           APPEND (before:(A)list)
             (APPEND (APPEND (left:(A)list) (right:(A)list)) after) &&
         ilength before == (pc:int)`);
  thm selected_after =
      choose_rule(`after:(A)list`, inner, witness);
  thm selected_before =
      choose_rule(`before:(A)list`, opened, selected_after);
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(apply_conversion(
      rewrite_conv(THM_LIST(cm_code_at_def)),
      `cm_code_at (code:(A)list)
         ((pc:int) + ilength (left:(A)list)) (right:(A)list)`)),
      selected_before));
  return gnode_prove(root);
}
PROOF thm cm_code_at_append_right =
    cm_prove_code_at_append_right();

PROOF static thm cm_prove_code_at_head(void) {
  gnode root = gnode_new_with_ccl(
      `!(code:(A)list) (pc:int) (inst:A) (rest:(A)list).
         cm_code_at code pc (inst :: rest) ==>
         0i <= pc && pc < ilength code && inth pc code == inst`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm source = assume_rule(
      `cm_code_at (code:(A)list) (pc:int)
         ((inst:A) :: (rest:(A)list))`);
  thm opened = eq_mp_rule(apply_conversion(
      rewrite_conv(THM_LIST(cm_code_at_def)), concl(source)), source);
  thm body = assume_rule(
      `(code:(A)list) ==
         APPEND (before:(A)list)
           (APPEND ((inst:A) :: (rest:(A)list)) (after:(A)list)) &&
       ilength before == (pc:int)`);
  thm before_nonnegative = spec_rule(
      `before:(A)list`, get_theorem_by_name("ILENGTH_NONNEG"));
  thm pc_nonnegative = conv_rule(rewrite_conv(THM_LIST(
      conjunct2_rule(body))), before_nonnegative);
  thm rest_nonnegative = spec_rule(
      `rest:(A)list`, get_theorem_by_name("ILENGTH_NONNEG"));
  thm after_nonnegative = spec_rule(
      `after:(A)list`, get_theorem_by_name("ILENGTH_NONNEG"));
  thm code_length = apply_conversion(rewrite_conv(THM_LIST(
      conjunct1_rule(body),
      get_theorem_by_name("ILENGTH_APPEND"),
      get_theorem_by_name("ILENGTH_DEF"))),
      `ilength (code:(A)list)`);
  thm code_length_at_pc = conv_rule(rewrite_conv(THM_LIST(
      conjunct2_rule(body))), code_length);
  thm pc_upper = mp_rule(int_arith_rule(mk_imp(
      list_mk_conj(TERM_LIST(
        concl(pc_nonnegative), concl(rest_nonnegative),
        concl(after_nonnegative), concl(code_length_at_pc))),
      `(pc:int) < ilength (code:(A)list)`)),
      conj_rule(pc_nonnegative,
        conj_rule(rest_nonnegative,
          conj_rule(after_nonnegative, code_length_at_pc))));
  thm at_suffix = mp_rule(specl_rule(TERM_LIST(
      `before:(A)list`,
      `APPEND ((inst:A) :: (rest:(A)list)) (after:(A)list)`,
      `0i`), cm_inth_append_right),
      int_arith_rule(`0i <= 0i`));
  thm at_head_raw = conv_rule(reduce_rewrite_conv(THM_LIST(
      conjunct2_rule(body),
      get_theorem_by_name("APPEND"),
      get_theorem_by_name("ILENGTH_DEF"),
      cm_inth_zero_cons)), at_suffix);
  thm code_expanded = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_theorem_by_name("APPEND"))), conjunct1_rule(body));
  thm at_head = conv_rule(reduce_rewrite_conv(THM_LIST(
      gsym_rule(code_expanded),
      int_arith_rule(`(pc:int) + 0i == pc`))), at_head_raw);
  thm result = conj_rule(pc_nonnegative,
      conj_rule(pc_upper, at_head));
  thm inner = assume_rule(
      `?after.
         (code:(A)list) ==
           APPEND (before:(A)list)
             (APPEND ((inst:A) :: (rest:(A)list)) after) &&
         ilength before == (pc:int)`);
  thm selected_after =
      choose_rule(`after:(A)list`, inner, result);
  thm selected_before =
      choose_rule(`before:(A)list`, opened, selected_after);
  ACCEPT_TAC(leaf, selected_before);
  return gnode_prove(root);
}
PROOF thm cm_code_at_head = cm_prove_code_at_head();

PROOF thm get_cm_code_at_head(void) {
  return cm_code_at_head;
}

PROOF static thm cm_prove_code_at_prepend(void) {
  gnode root = gnode_new_with_ccl(
      `!(prefix:(A)list) (code:(A)list) (pc:int)
         (fragment:(A)list).
         cm_code_at code pc fragment ==>
         cm_code_at (APPEND prefix code)
           (ilength prefix + pc) fragment`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm source = assume_rule(
      `cm_code_at (code:(A)list) (pc:int) (fragment:(A)list)`);
  thm opened = eq_mp_rule(apply_conversion(
      rewrite_conv(THM_LIST(cm_code_at_def)), concl(source)), source);
  thm body = assume_rule(
      `(code:(A)list) ==
         APPEND (before:(A)list)
           (APPEND (fragment:(A)list) (after:(A)list)) &&
       ilength before == (pc:int)`);
  thm prefixed = beta_norm(ap_term_rule(
      `\tail:(A)list. APPEND (prefix:(A)list) tail`,
      conjunct1_rule(body)));
  thm arranged = conv_rule(once_rewrite_conv(THM_LIST(
      get_theorem_by_name("APPEND_ASSOC"))), prefixed);
  thm prefix_length = apply_conversion(rewrite_conv(THM_LIST(
      get_theorem_by_name("ILENGTH_APPEND"))),
      `ilength
         (APPEND (prefix:(A)list) (before:(A)list))`);
  thm target_length = conv_rule(rewrite_conv(THM_LIST(
      conjunct2_rule(body))), prefix_length);
  thm candidate = conj_rule(arranged, target_length);
  thm suffix_witness = exists_rule(
      `?suffix.
         APPEND (prefix:(A)list) (code:(A)list) ==
           APPEND (APPEND prefix (before:(A)list))
             (APPEND (fragment:(A)list) suffix) &&
         ilength (APPEND prefix before) ==
           ilength prefix + (pc:int)`,
      `after:(A)list`, candidate);
  thm witness = exists_rule(
      `?new_before suffix.
         APPEND (prefix:(A)list) (code:(A)list) ==
           APPEND new_before
             (APPEND (fragment:(A)list) suffix) &&
         ilength new_before ==
           ilength (prefix:(A)list) + (pc:int)`,
      `APPEND (prefix:(A)list) (before:(A)list)`,
      suffix_witness);
  thm inner = assume_rule(
      `?after.
         (code:(A)list) ==
           APPEND (before:(A)list)
             (APPEND (fragment:(A)list) after) &&
         ilength before == (pc:int)`);
  thm selected_after =
      choose_rule(`after:(A)list`, inner, witness);
  thm selected_before =
      choose_rule(`before:(A)list`, opened, selected_after);
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(apply_conversion(
      rewrite_conv(THM_LIST(cm_code_at_def)),
      `cm_code_at
         (APPEND (prefix:(A)list) (code:(A)list))
         (ilength prefix + (pc:int)) (fragment:(A)list)`)),
      selected_before));
  return gnode_prove(root);
}
PROOF thm cm_code_at_prepend = cm_prove_code_at_prepend();

PROOF thm get_cm_code_at_prepend(void) {
  return cm_code_at_prepend;
}

PROOF static thm cm_prove_emit_functions_contains(void) {
  gnode root = gnode_new_with_ccl(
      `!(functions:(cm_function_d)list).
       !(p:cm_program) (start:int) (index:int).
         0i <= index && index < ilength functions ==>
         cm_code_at
           (cm_emit_functions p start functions)
           (ilength
             (cm_function_code_prefix p start functions index))
           (cm_emit_function p (start + index))`);
  gnode_list cases = INDUCT_TAC(
      root, `functions:(cm_function_d)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    leaf = AUTO_ASMP_DESTRUCT_TAC(leaf)[0];
    thm upper = conv_rule(reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF"))),
        assume_rule(`(index:int) <
          ilength ([]:(cm_function_d)list)`));
    CONTR_TAC(leaf, mp_rule(mp_rule(int_arith_rule(
        `0i <= (index:int) ==> index < 0i ==> F`),
        assume_rule(`0i <= (index:int)`)), upper));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    leaf = AUTO_ASMP_DESTRUCT_TAC(leaf)[0];
    thm lower = assume_rule(`0i <= (index:int)`);
    thm upper = assume_rule(
        `(index:int) <
          ilength ((a0:cm_function_d) ::
            (a1:(cm_function_d)list))`);
    thm ih = assume_rule(
        `!(p:cm_program) (start:int) (index:int).
           0i <= index && index < ilength (a1:(cm_function_d)list) ==>
           cm_code_at
             (cm_emit_functions p start a1)
             (ilength
               (cm_function_code_prefix p start a1 index))
             (cm_emit_function p (start + index))`);
    gnode_list index_cases = BOOL_CASES_TAC(
        leaf, `(index:int) == 0i`, "hindex_zero");
    {
      gnode reduced = CONV_WITH_ASMP_TAC(
          index_cases[0], reduce_rewrite_conv, THM_LIST(
            get_cm_emit_functions_def(),
            cm_function_code_prefix_def,
            get_theorem_by_name("ILENGTH_DEF"),
            cm_code_at_front));
      if (IS_NULL(reduced->solved)) {
        thm normalized = conv_rule(reduce_rewrite_conv(THM_LIST(
            get_cm_emit_functions_def(),
            cm_function_code_prefix_def,
            get_theorem_by_name("ILENGTH_DEF"),
            assume_rule(`(index:int) == 0i`),
            int_arith_rule(`(start:int) + 0i == start`))),
            ispecl_rule(TERM_LIST(
              `cm_emit_function (p:cm_program) (start:int)`,
              `cm_emit_functions (p:cm_program) (start + 1i)
                (a1:(cm_function_d)list)`),
              cm_code_at_front));
        thm target_equation = apply_conversion(
            reduce_rewrite_conv(THM_LIST(
              int_arith_rule(`(start:int) + 0i == start`))),
            reduced->g.ccl);
        ACCEPT_TAC(reduced,
            eq_mp_rule(sym_rule(target_equation), normalized));
      }
    }
    {
      thm nonzero = assume_rule(`~((index:int) == 0i)`);
      thm one = mp_rule(mp_rule(int_arith_rule(
          `0i <= (index:int) ==> ~(index == 0i) ==> 1i <= index`),
          lower), nonzero);
      thm expanded_upper = conv_rule(reduce_rewrite_conv(THM_LIST(
          get_theorem_by_name("ILENGTH_DEF"))), upper);
      thm child_bounds = mp_rule(int_arith_rule(mk_imp(
          list_mk_conj(TERM_LIST(
            concl(one), concl(expanded_upper))),
          `0i <= (index:int) - 1i &&
           index - 1i < ilength (a1:(cm_function_d)list)`)),
          conj_rule(one, expanded_upper));
      thm child = mp_rule(specl_rule(TERM_LIST(
          `p:cm_program`, `(start:int) + 1i`,
          `(index:int) - 1i`), ih), child_bounds);
      thm lifted = mp_rule(ispecl_rule(TERM_LIST(
          `cm_emit_function (p:cm_program) (start:int)`,
          `cm_emit_functions (p:cm_program) (start + 1i)
             (a1:(cm_function_d)list)`,
          `ilength
             (cm_function_code_prefix (p:cm_program)
               ((start:int) + 1i) (a1:(cm_function_d)list)
               ((index:int) - 1i))`,
          `cm_emit_function (p:cm_program)
             (((start:int) + 1i) + (index - 1i))`),
          cm_code_at_prepend), child);
      thm normalized = conv_rule(reduce_rewrite_conv(THM_LIST(
          get_cm_emit_functions_def(),
          cm_function_code_prefix_def,
          get_theorem_by_name("ILENGTH_APPEND"),
          nonzero,
          int_arith_rule(
            `((start:int) + 1i) + ((index:int) - 1i) ==
             start + index`))), lifted);
      thm target_equation = apply_conversion(
          reduce_rewrite_conv(THM_LIST(
            get_cm_emit_functions_def(),
            cm_function_code_prefix_def,
            get_theorem_by_name("ILENGTH_APPEND"),
            nonzero)),
          index_cases[1]->g.ccl);
      ACCEPT_TAC(index_cases[1],
          eq_mp_rule(sym_rule(target_equation), normalized));
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_emit_functions_contains =
    cm_prove_emit_functions_contains();

PROOF thm get_cm_function_code_prefix_def(void) {
  return cm_function_code_prefix_def;
}

PROOF thm get_cm_emit_functions_contains(void) {
  return cm_emit_functions_contains;
}

PROOF static thm cm_prove_function_code_prefix_length(void) {
  gnode root = gnode_new_with_ccl(
      `!(functions:(cm_function_d)list).
       !(p:cm_program) (start:int).
         start ==
           ilength (cm_program_functions p) - ilength functions ==>
         !index.
           ilength
             (cm_function_code_prefix p start functions index) ==
           cm_function_prefix p functions index`);
  gnode_list cases = INDUCT_TAC(
      root, `functions:(cm_function_d)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_WITH_ASMP_TAC(
        leaf, reduce_rewrite_conv, THM_LIST(
          cm_function_code_prefix_def,
          get_cm_function_prefix_def(),
          get_theorem_by_name("ILENGTH_DEF")));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm ih = assume_rule(
        `!(p:cm_program) (start:int).
           start ==
             ilength (cm_program_functions p) -
             ilength (a1:(cm_function_d)list) ==>
           !index.
             ilength
               (cm_function_code_prefix p start a1 index) ==
             cm_function_prefix p a1 index`);
    thm start_exact = assume_rule(
        `(start:int) ==
          ilength (cm_program_functions (p:cm_program)) -
          ilength ((a0:cm_function_d) ::
            (a1:(cm_function_d)list))`);
    gnode_list index_cases = BOOL_CASES_TAC(
        leaf, `(index:int) == 0i`, "hindex_zero");
    {
      CONV_WITH_ASMP_TAC(index_cases[0],
          reduce_rewrite_conv, THM_LIST(
            cm_function_code_prefix_def,
            get_cm_function_prefix_def(),
            get_theorem_by_name("ILENGTH_DEF")));
    }
    {
      thm nonzero = assume_rule(`~((index:int) == 0i)`);
      thm expanded_start = conv_rule(reduce_rewrite_conv(THM_LIST(
          get_theorem_by_name("ILENGTH_DEF"))), start_exact);
      thm tail_start = mp_rule(int_arith_rule(mk_imp(
          concl(expanded_start),
          `(start:int) + 1i ==
            ilength (cm_program_functions (p:cm_program)) -
            ilength (a1:(cm_function_d)list)`)),
          expanded_start);
      thm tail_length = spec_rule(`(index:int) - 1i`,
          mp_rule(specl_rule(TERM_LIST(
            `p:cm_program`, `(start:int) + 1i`), ih),
            tail_start));
      thm tail_arithmetic = int_arith_rule(
          `((n:int) - (1i + (m:int))) + 1i == n - m`);
      thm normalized_tail_length = conv_rule(
          reduce_rewrite_conv(THM_LIST(
            expanded_start, tail_arithmetic)),
          tail_length);
      thm head_length = specl_rule(TERM_LIST(
          `p:cm_program`, `start:int`),
          get_cm_function_code_length());
      gnode reduced = CONV_WITH_ASMP_TAC(index_cases[1],
          reduce_rewrite_conv, THM_LIST(
            cm_function_code_prefix_def,
            get_cm_function_prefix_def(),
            get_theorem_by_name("ILENGTH_APPEND"),
            nonzero, head_length, normalized_tail_length,
            expanded_start,
            get_theorem_by_name("ILENGTH_DEF")));
      if (IS_NULL(reduced->solved)) {
        thm normalized_start = mp_rule(int_arith_rule(mk_imp(
            concl(expanded_start),
            `(start:int) ==
              ilength (cm_program_functions (p:cm_program)) -
              (1i + ilength (a1:(cm_function_d)list))`)),
            expanded_start);
        CONV_WITH_ASMP_TAC(
            reduced, reduce_rewrite_conv, THM_LIST(
              normalized_start, tail_arithmetic,
              normalized_tail_length));
      }
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_function_code_prefix_length =
    cm_prove_function_code_prefix_length();

PROOF thm get_cm_function_code_prefix_length(void) {
  return cm_function_code_prefix_length;
}

PROOF static thm cm_prove_model_function_at(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int).
         0i <= fid &&
         fid < ilength (cm_program_functions p) ==>
         cm_code_at
           (cm_model_code p)
           (cm_function_pc p fid)
           (cm_emit_function p fid)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm bounds = assume_rule(
      `0i <= (fid:int) &&
       fid < ilength (cm_program_functions (p:cm_program))`);
  thm contained = mp_rule(specl_rule(TERM_LIST(
      `cm_program_functions (p:cm_program)`,
      `p:cm_program`, `0i:int`, `fid:int`),
      cm_emit_functions_contains), bounds);
  thm prefix_base = mp_rule(specl_rule(TERM_LIST(
      `cm_program_functions (p:cm_program)`,
      `p:cm_program`, `0i:int`),
      cm_function_code_prefix_length),
      int_arith_rule(
        `0i ==
         ilength (cm_program_functions (p:cm_program)) -
         ilength (cm_program_functions p)`));
  thm relative = conv_rule(reduce_rewrite_conv(THM_LIST(
      spec_rule(`fid:int`, prefix_base),
      int_arith_rule(`0i + (fid:int) == fid`))),
      contained);
  thm lifted = mp_rule(ispecl_rule(TERM_LIST(
      `cm_emit_prelude (p:cm_program)`,
      `cm_emit_functions (p:cm_program) 0i
         (cm_program_functions p)`,
      `cm_function_prefix (p:cm_program)
         (cm_program_functions p) (fid:int)`,
      `cm_emit_function (p:cm_program) (fid:int)`),
      cm_code_at_prepend), relative);
  conv normalize_layout = reduce_rewrite_conv(THM_LIST(
      get_cm_model_code_def(),
      get_cm_function_pc_def(),
      get_cm_emit_prelude_def(),
      get_theorem_by_name("ILENGTH_DEF")));
  thm normalized = conv_rule(normalize_layout, lifted);
  thm target_equation = apply_conversion(
      normalize_layout, leaf->g.ccl);
  ACCEPT_TAC(leaf,
      eq_mp_rule(sym_rule(target_equation), normalized));
  return gnode_prove(root);
}
PROOF thm cm_model_function_at =
    cm_prove_model_function_at();

PROOF thm get_cm_model_function_at(void) {
  return cm_model_function_at;
}

PROOF static thm cm_prove_model_function_body_at(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int).
         0i <= fid &&
         fid < ilength (cm_program_functions p) ==>
         cm_code_at
           (cm_model_code p)
           (cm_function_pc p fid +
            cm_function_prologue_count
              (inth fid (cm_program_functions p)))
           (cm_emit_stmt p fid
             (cm_function_pc p fid +
              cm_function_prologue_count
                (inth fid (cm_program_functions p)))
             0i 0i 0i
             (cm_function_body
               (inth fid (cm_program_functions p))))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm bounds = assume_rule(
      `0i <= (fid:int) &&
       fid < ilength (cm_program_functions (p:cm_program))`);
  thm function_at = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`), cm_model_function_at),
      bounds);
  thm opened = conv_rule(rewrite_conv(THM_LIST(
      get_cm_emit_function_def())), function_at);
  term body_code =
      `cm_emit_stmt (p:cm_program) (fid:int)
         (cm_function_pc p fid +
          cm_function_prologue_count
            (inth fid (cm_program_functions p)))
         0i 0i 0i
         (cm_function_body
           (inth fid (cm_program_functions p)))`;
  term function_tail =
      `APPEND
         (cm_emit_stmt (p:cm_program) (fid:int)
           (cm_function_pc p fid +
            cm_function_prologue_count
              (inth fid (cm_program_functions p)))
           0i 0i 0i
           (cm_function_body
             (inth fid (cm_program_functions p))))
         (APPEND
           [TVMInst TVMPushOp 0i]
           cm_return_epilogue)`;
  thm tail_at = mp_rule(ispecl_rule(TERM_LIST(
      `cm_model_code (p:cm_program)`,
      `cm_function_pc (p:cm_program) (fid:int)`,
      `cm_emit_prologue (p:cm_program) (fid:int)`,
      function_tail),
      cm_code_at_append_right), opened);
  thm body_at = mp_rule(ispecl_rule(TERM_LIST(
      `cm_model_code (p:cm_program)`,
      `cm_function_pc (p:cm_program) (fid:int) +
       ilength (cm_emit_prologue p fid)`,
      body_code,
      `APPEND
         [TVMInst TVMPushOp 0i]
         cm_return_epilogue`),
      cm_code_at_append_left), tail_at);
  thm normalized = conv_rule(rewrite_conv(THM_LIST(
      specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`),
        get_cm_prologue_length()))), body_at);
  ACCEPT_TAC(leaf, normalized);
  return gnode_prove(root);
}
PROOF thm cm_model_function_body_at =
    cm_prove_model_function_body_at();

PROOF static thm cm_prove_model_function_body_tail_at(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int).
         0i <= fid &&
         fid < ilength (cm_program_functions p) ==>
         cm_code_at
           (cm_model_code p)
           (cm_function_pc p fid +
            cm_function_prologue_count
              (inth fid (cm_program_functions p)))
           (cm_emit_stmt p fid
              (cm_function_pc p fid +
               cm_function_prologue_count
                 (inth fid (cm_program_functions p)))
              0i 0i 0i
              (cm_function_body
                (inth fid (cm_program_functions p))) ++
            [TVMInst TVMPushOp 0i] ++
            cm_return_epilogue)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm bounds = assume_rule(
      `0i <= (fid:int) &&
       fid < ilength (cm_program_functions (p:cm_program))`);
  thm function_at = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`), cm_model_function_at),
      bounds);
  thm opened = conv_rule(rewrite_conv(THM_LIST(
      get_cm_emit_function_def())), function_at);
  term function_tail =
      `APPEND
         (cm_emit_stmt (p:cm_program) (fid:int)
           (cm_function_pc p fid +
            cm_function_prologue_count
              (inth fid (cm_program_functions p)))
           0i 0i 0i
           (cm_function_body
             (inth fid (cm_program_functions p))))
         (APPEND
           [TVMInst TVMPushOp 0i]
           cm_return_epilogue)`;
  thm tail_at = mp_rule(ispecl_rule(TERM_LIST(
      `cm_model_code (p:cm_program)`,
      `cm_function_pc (p:cm_program) (fid:int)`,
      `cm_emit_prologue (p:cm_program) (fid:int)`,
      function_tail),
      cm_code_at_append_right), opened);
  thm normalized = conv_rule(rewrite_conv(THM_LIST(
      specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`),
        get_cm_prologue_length()))), tail_at);
  ACCEPT_TAC(leaf, normalized);
  return gnode_prove(root);
}
PROOF thm cm_model_function_body_tail_at =
    cm_prove_model_function_body_tail_at();

PROOF thm get_cm_model_function_body_tail_at(void) {
  return cm_model_function_body_tail_at;
}

PROOF thm get_cm_model_function_body_at(void) {
  return cm_model_function_body_at;
}
PROOF static thm cm_prove_model_prelude_at(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program).
         cm_code_at (cm_model_code p) 0i (cm_emit_prelude p)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm equation = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_model_code_def(), get_theorem_by_name("APPEND"),
        get_theorem_by_name("ILENGTH_DEF"))),
      `cm_model_code (p:cm_program) ==
         APPEND ([]:(tvm_inst)list)
           (APPEND (cm_emit_prelude p)
             (cm_emit_functions p 0i (cm_program_functions p)))`));
  thm empty_length = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF"))),
      `ilength ([]:(tvm_inst)list) == 0i`));
  thm body = conj_rule(equation, empty_length);
  thm witness = exists_rule(
      `?before after.
         cm_model_code (p:cm_program) ==
           APPEND before (APPEND (cm_emit_prelude p) after) &&
         ilength before == 0i`,
      `[]:(tvm_inst)list`,
      exists_rule(
        `?after.
           cm_model_code (p:cm_program) ==
             APPEND ([]:(tvm_inst)list)
               (APPEND (cm_emit_prelude p) after) &&
           ilength ([]:(tvm_inst)list) == 0i`,
        `cm_emit_functions (p:cm_program) 0i
           (cm_program_functions p)`,
        body));
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(apply_conversion(
      rewrite_conv(THM_LIST(cm_code_at_def)),
      `cm_code_at (cm_model_code (p:cm_program)) 0i
         (cm_emit_prelude p)`)), witness));
  return gnode_prove(root);
}
PROOF thm cm_model_prelude_at = cm_prove_model_prelude_at();

PROOF thm get_cm_model_prelude_at(void) {
  return cm_model_prelude_at;
}
PROOF thm get_cm_code_at_append_right(void) {
  return cm_code_at_append_right;
}
PROOF thm get_cm_code_at_def(void) { return cm_code_at_def; }
PROOF thm get_cm_code_at_append_left(void) {
  return cm_code_at_append_left;
}

PROOF static int cmc_preservation_layout_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_layout_axioms_before,
      "cmc_preservation_layout introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_layout_checks =
    cmc_preservation_layout_final_checks();
