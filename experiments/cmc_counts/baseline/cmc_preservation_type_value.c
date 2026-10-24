#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_lang.h"
#include "cmc_sim.h"
#include "cmc_preservation_type_ready.h"
#include "cmc_preservation_type_value.h"

#require "cmc_preservation_type_facts.c"

PROOF static size_t _cmc_preservation_type_value_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_prove_pointer_retype_type_ready(void) {
  gnode root = gnode_new_with_ccl(
      `!(v:cm_value) (ty:cm_type).
         cm_is_pointer (cm_value_type v) ==>
         cm_is_pointer ty ==>
         cm_value_type_compatible (cm_pointer_retype ty v) ty`);
  gnode_list value_cases = INDUCT_TAC(root, `v:cm_value`);
  for (size_t i = 0; i < vector_size(value_cases); ++i) {
    gnode_list type_cases = INDUCT_TAC(value_cases[i], `ty:cm_type`);
    for (size_t j = 0; j < vector_size(type_cases); ++j) {
      thm view = apply_conversion(reduce_rewrite_conv(THM_LIST(
          get_cm_pointer_retype_def(), get_cm_value_type_def(),
          get_cm_value_type_compatible_def(), get_cm_is_pointer_def(),
          get_cm_pointee_def(), get_theorem_by_name("COND_CLAUSES"))),
          goal_ccl(type_cases[j]->g));
      ACCEPT_TAC(type_cases[j], eqt_elim_rule(view));
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_pointer_retype_type_ready =
    cm_prove_pointer_retype_type_ready();

PROOF static thm cm_prove_convertible_convert_value_type_ready(void) {
  gnode root = gnode_new_with_ccl(
      `!(st:cm_src_state) (v:cm_value) (ty:cm_type).
         cm_convertible (cm_value_type v) ty ==>
         cm_value_type_compatible (cm_convert_value st ty v) ty`);
  gnode_list value_cases = INDUCT_TAC(root, `v:cm_value`);
  for (size_t i = 0; i < vector_size(value_cases); ++i) {
    gnode_list type_cases = INDUCT_TAC(value_cases[i], `ty:cm_type`);
    for (size_t j = 0; j < vector_size(type_cases); ++j) {
      conv normalize = reduce_rewrite_conv(THM_LIST(
          get_cm_convertible_def(), get_cm_convert_value_def(),
          get_cm_pointer_retype_def(), get_cm_value_number_def(),
          get_cm_value_type_def(), get_cm_value_type_compatible_def(),
          get_cm_integer_type_def(), get_cm_is_pointer_def(),
          get_cm_is_struct_def(), get_cm_pointee_def(),
          get_datatype_distinctness("cm_type"),
          get_datatype_injectivity("cm_type"),
          get_theorem_by_name("COND_CLAUSES")));
      thm first = apply_conversion(normalize,
          goal_ccl(type_cases[j]->g));
      thm second = apply_conversion(normalize, rhs_of(first));
      ACCEPT_TAC(type_cases[j],
          eqt_elim_rule(trans_rule(first, second)));
    }
  }
  return gnode_prove(root);
}
PROOF static thm cm_convertible_convert_value_type_ready =
    cm_prove_convertible_convert_value_type_ready();

PROOF static thm cm_prove_zero_convert_value_type_ready(void) {
  gnode root = gnode_new_with_ccl(
      `!(st:cm_src_state) (ty:cm_type).
         cm_is_pointer ty ==>
         cm_value_type_compatible
           (cm_convert_value st ty (CMIntV 0i)) ty`);
  gnode_list type_cases = INDUCT_TAC(root, `ty:cm_type`);
  for (size_t i = 0; i < vector_size(type_cases); ++i) {
    thm view = apply_conversion(reduce_rewrite_conv(THM_LIST(
        get_cm_convert_value_def(), get_cm_pointer_retype_def(),
        get_cm_value_number_def(), get_cm_value_type_def(),
        get_cm_value_type_compatible_def(), get_cm_is_pointer_def(),
        get_cm_pointee_def(), get_tower_wrap64_def(),
        get_datatype_distinctness("cm_type"),
        get_datatype_injectivity("cm_type"),
        get_theorem_by_name("COND_CLAUSES"))),
        goal_ccl(type_cases[i]->g));
    ACCEPT_TAC(type_cases[i], eqt_elim_rule(view));
  }
  return gnode_prove(root);
}
PROOF static thm cm_zero_convert_value_type_ready =
    cm_prove_zero_convert_value_type_ready();

PROOF static thm cm_prove_convert_value_type_ready(void) {
  gnode root = gnode_new_with_ccl(
      `!(st:cm_src_state) (v:cm_value) (ty:cm_type).
         cm_value_convertible_to v ty ==>
         cm_value_type_compatible (cm_convert_value st ty v) ty`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm opened = conv_rule(rewrite_conv(THM_LIST(
      get_cm_value_convertible_to_def())),
      assume_rule(`cm_value_convertible_to (v:cm_value) (ty:cm_type)`));
  dest_disj_results parts = dest_disj(concl(opened));
  gnode_list cases = DISJ_CASES_TAC(leaf, opened, "Hconvertible");
  ACCEPT_TAC(cases[0], mp_rule(specl_rule(TERM_LIST(
      `st:cm_src_state`, `v:cm_value`, `ty:cm_type`),
      cm_convertible_convert_value_type_ready),
      assume_rule(parts.tm1)));
  thm exceptional = assume_rule(parts.tm2);
  thm is_zero = conjunct1_rule(exceptional);
  thm is_pointer = conjunct2_rule(exceptional);
  thm zero_ready = mp_rule(specl_rule(TERM_LIST(
      `st:cm_src_state`, `ty:cm_type`),
      cm_zero_convert_value_type_ready), is_pointer);
  thm transported = conv_rule(rewrite_conv(THM_LIST(
      sym_rule(is_zero))), zero_ready);
  ACCEPT_TAC(cases[1], transported);
  return gnode_prove(root);
}
PROOF thm cm_convert_value_type_ready =
    cm_prove_convert_value_type_ready();

PROOF static thm cm_type_last_conjunct(thm fact) {
  while (is_conj(concl(fact))) {
    fact = conjunct2_rule(fact);
  }
  return fact;
}

PROOF static thm cm_prove_load_value_type_ready(void) {
  gnode root = gnode_new_with_ccl(
      `!(st:cm_src_state) (ptr:cm_value) (ty:cm_type).
         cm_scalar_expr_type ty ==>
         cm_load_ok ty ptr st ==>
         cm_value_type_compatible (cm_load_value ty ptr st) ty`);
  gnode_list type_cases = INDUCT_TAC(root, `ty:cm_type`);
  thm distinct = get_datatype_distinctness("cm_type");
  for (size_t i = 0; i < 3; ++i) {
    thm view = apply_conversion(reduce_rewrite_conv(THM_LIST(
        get_cm_scalar_expr_type_def(), get_cm_integer_type_def(),
        get_cm_is_pointer_def(), get_cm_load_value_def(),
        get_cm_value_type_def(), get_cm_value_type_compatible_def(),
        distinct, get_theorem_by_name("COND_CLAUSES"))),
        goal_ccl(type_cases[i]->g));
    ACCEPT_TAC(type_cases[i], eqt_elim_rule(view));
  }
  gnode pointer_leaf = AUTO_INTROS_TAC(type_cases[3]);
  term word_zero =
      `tower_getw (cm_state_mem (st:cm_src_state))
         (cm_value_number st (ptr:cm_value)) == 0i`;
  gnode_list word_cases = BOOL_CASES_TAC(
      pointer_leaf, word_zero, "Hword_zero");
  thm source_zero = assume_rule(word_zero);
  thm zero_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
      get_cm_load_value_def(), source_zero,
      get_cm_value_type_compatible_def(), get_cm_value_type_def(),
      get_cm_is_pointer_def(), distinct,
      get_theorem_by_name("COND_CLAUSES"))),
      goal_ccl(word_cases[0]->g));
  ACCEPT_TAC(word_cases[0], eqt_elim_rule(zero_view));

  thm source_nonzero = assume_rule(mk_not(word_zero));
  thm expanded_load = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_load_ok_def(), get_cm_store_width_def(),
      get_cm_type_int_char_distinct(), distinct)),
      assume_rule(
        `cm_load_ok (CMPtrTy a) (ptr:cm_value) (st:cm_src_state)`));
  thm tagged_implication = cm_type_last_conjunct(expanded_load);
  thm pointer_kind = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(get_cm_is_pointer_def())),
      `cm_is_pointer (CMPtrTy a)`));
  thm tagged_disjunction = mp_rule(tagged_implication, pointer_kind);
  thm tagged_and_type = mp_rule(taut_rule(mk_imp(
      list_mk_conj(TERM_LIST(
        concl(tagged_disjunction), concl(source_nonzero))),
      `cm_state_tagged (st:cm_src_state)
          (cm_value_number st (ptr:cm_value)) &&
       cm_is_pointer
         (cm_value_type
           (cm_state_tags st (cm_value_number st ptr)))`)),
      conj_rule(tagged_disjunction, source_nonzero));
  thm retyped = mp_rule(mp_rule(specl_rule(TERM_LIST(
      `cm_state_tags (st:cm_src_state)
         (cm_value_number st (ptr:cm_value))`,
      `CMPtrTy a:cm_type`), cm_pointer_retype_type_ready),
      conjunct2_rule(tagged_and_type)), pointer_kind);
  thm nonzero_view = apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_load_value_def(), source_nonzero, distinct,
        get_theorem_by_name("COND_CLAUSES"))),
      goal_ccl(word_cases[1]->g));
  ACCEPT_TAC(word_cases[1],
      eq_mp_rule(sym_rule(nonzero_view), retyped));
  return gnode_prove(root);
}
PROOF thm cm_load_value_type_ready =
    cm_prove_load_value_type_ready();

PROOF static thm cm_prove_binding_value_type_ready(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (scope:int) (slot:int)
         (st:cm_src_state).
         cm_binding_address_ok p fid scope slot st ==>
         cm_value_type_compatible
           (if scope == 0i then cm_global_pointer p slot
            else cm_state_env st scope slot)
           (CMPtrTy
             (if scope == 0i
              then cm_global_ty
                (inth slot (cm_program_globals p))
              else if scope == 1i
                   then cm_slot_ty
                     (inth slot
                       (cm_function_locals
                         (inth fid (cm_program_functions p))))
                   else cm_slot_ty
                     (inth slot
                       (cm_function_params
                         (inth fid (cm_program_functions p))))))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm expanded = conv_rule(rewrite_conv(THM_LIST(
      get_cm_binding_address_ok_def())),
      assume_rule(
        `cm_binding_address_ok (p:cm_program) (fid:int)
           (scope:int) (slot:int) (st:cm_src_state)`));
  thm type_equal = cm_type_last_conjunct(expanded);
  thm target_view = apply_conversion(rewrite_conv(THM_LIST(
      get_cm_value_type_compatible_def())), goal_ccl(leaf->g));
  dest_disj_results target_parts = dest_disj(rhs_of(target_view));
  thm ready = disj1_rule(type_equal, target_parts.tm2);
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), ready));
  return gnode_prove(root);
}
PROOF thm cm_binding_value_type_ready =
    cm_prove_binding_value_type_ready();


PROOF static thm cm_prove_ptr_add_type_ready(void) {
  gnode root = gnode_new_with_ccl(
      `!(structs:(cm_struct_d)list) (st:cm_src_state)
         (ptr:cm_value) (ty:cm_type) (index:int).
         cm_value_type_compatible ptr (CMPtrTy ty) ==>
         cm_pointer_live st ptr ==>
         cm_value_type_compatible
           (cm_ptr_add structs ptr index) (CMPtrTy ty)`);
  gnode_list value_cases = INDUCT_TAC(root, `ptr:cm_value`);
  for (size_t i = 0; i < vector_size(value_cases); ++i) {
    thm view = apply_conversion(reduce_rewrite_conv(THM_LIST(
        get_cm_value_type_compatible_def(), get_cm_value_type_def(),
        get_cm_pointer_live_def(), get_cm_ptr_gen_def(),
        get_cm_ptr_add_def(), get_cm_ptr_view_def(),
        get_cm_is_pointer_def(),
        get_datatype_distinctness("cm_value"),
        get_datatype_injectivity("cm_value"),
        get_datatype_distinctness("cm_type"),
        get_datatype_injectivity("cm_type"))),
        goal_ccl(value_cases[i]->g));
    ACCEPT_TAC(value_cases[i], eq_mp_rule(sym_rule(view),
        taut_rule(rhs_of(view))));
  }
  return gnode_prove(root);
}
PROOF thm cm_ptr_add_type_ready =
    cm_prove_ptr_add_type_ready();

PROOF static thm cm_prove_ptr_member_type_ready(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (ptr:cm_value) (mid:int).
         cm_value_type_compatible
           (cm_ptr_member p ptr mid)
           (CMPtrTy (cm_slot_ty (cm_member_slot p ptr mid)))`);
  thm view = apply_conversion(reduce_rewrite_conv(THM_LIST(
      get_cm_ptr_member_def(), get_cm_value_type_def(),
      get_cm_value_type_compatible_def())),
      goal_ccl(root->g));
  ACCEPT_TAC(root, eqt_elim_rule(view));
  return gnode_prove(root);
}
PROOF thm cm_ptr_member_type_ready =
    cm_prove_ptr_member_type_ready();

PROOF static thm cm_prove_unary_value_type_ready(void) {
  gnode root = gnode_new_with_ccl(
      `!(op:int) (arg:cm_value) (st:cm_src_state).
         cm_value_type_compatible
           (cm_unary_value op arg st) CMIntTy`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list cases = BOOL_CASES_TAC(
      leaf, `(op:int) == 0i`, "Hop_zero");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    labeled_term_list assumptions = goal_lasmps(cases[i]->g);
    thm branch = assume_rule(assumptions[0].tm);
    thm view = apply_conversion(reduce_rewrite_conv(THM_LIST(
        get_cm_unary_value_def(), branch,
        get_cm_value_type_def(), get_cm_value_type_compatible_def(),
        get_datatype_distinctness("cm_value"),
        get_datatype_distinctness("cm_type"),
        get_theorem_by_name("COND_CLAUSES"))),
        goal_ccl(cases[i]->g));
    ACCEPT_TAC(cases[i], eqt_elim_rule(view));
  }
  return gnode_prove(root);
}
PROOF thm cm_unary_value_type_ready =
    cm_prove_unary_value_type_ready();

PROOF static thm cm_prove_compatible_pointer_kind(void) {
  gnode root = gnode_new_with_ccl(
      `!(v:cm_value) (ty:cm_type).
         cm_scalar_expr_type ty ==>
         cm_value_type_compatible v ty ==>
         (cm_is_pointer (cm_value_type v) <=> cm_is_pointer ty)`);
  gnode_list value_cases = INDUCT_TAC(root, `v:cm_value`);
  for (size_t i = 0; i < vector_size(value_cases); ++i) {
    gnode_list type_cases = INDUCT_TAC(value_cases[i], `ty:cm_type`);
    for (size_t j = 0; j < vector_size(type_cases); ++j) {
      thm view = apply_conversion(reduce_rewrite_conv(THM_LIST(
          get_cm_scalar_expr_type_def(), get_cm_integer_type_def(),
          get_cm_value_type_compatible_def(), get_cm_value_type_def(),
          get_cm_is_pointer_def(), get_datatype_distinctness("cm_value"),
          get_datatype_injectivity("cm_value"),
          get_datatype_distinctness("cm_type"),
          get_datatype_injectivity("cm_type"))),
          goal_ccl(type_cases[j]->g));
      ACCEPT_TAC(type_cases[j], eqt_elim_rule(view));
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_compatible_pointer_kind =
    cm_prove_compatible_pointer_kind();

PROOF static thm cm_type_pick_conjunct(thm fact, term wanted) {
  if (alpha_compare(concl(fact), wanted) == 0) return fact;
  if (is_conj(concl(fact))) {
    thm left = cm_type_pick_conjunct(conjunct1_rule(fact), wanted);
    if (!IS_NULL(left)) return left;
    return cm_type_pick_conjunct(conjunct2_rule(fact), wanted);
  }
  return empty_theorem;
}

PROOF static thm cm_prove_integer_expr_type(void) {
  gnode root = gnode_new_with_ccl(
      `!(ty:cm_type).
         cm_integer_type ty ==> cm_scalar_expr_type ty`);
  gnode_list cases = INDUCT_TAC(root, `ty:cm_type`);
  for (size_t i = 0; i < vector_size(cases); ++i) {
    thm view = apply_conversion(reduce_rewrite_conv(THM_LIST(
        get_cm_integer_type_def(), get_cm_scalar_expr_type_def(),
        get_cm_is_pointer_def())), goal_ccl(cases[i]->g));
    ACCEPT_TAC(cases[i], eqt_elim_rule(view));
  }
  return gnode_prove(root);
}
PROOF thm cm_integer_expr_type =
    cm_prove_integer_expr_type();

PROOF static thm cm_prove_pointer_expr_type(void) {
  gnode root = gnode_new_with_ccl(
      `!(ty:cm_type).
         cm_is_pointer ty ==> cm_scalar_expr_type ty`);
  gnode_list cases = INDUCT_TAC(root, `ty:cm_type`);
  for (size_t i = 0; i < vector_size(cases); ++i) {
    thm view = apply_conversion(reduce_rewrite_conv(THM_LIST(
        get_cm_integer_type_def(), get_cm_scalar_expr_type_def(),
        get_cm_is_pointer_def())), goal_ccl(cases[i]->g));
    ACCEPT_TAC(cases[i], eqt_elim_rule(view));
  }
  return gnode_prove(root);
}
PROOF thm cm_pointer_expr_type =
    cm_prove_pointer_expr_type();

PROOF static thm cm_prove_integer_not_pointer(void) {
  gnode root = gnode_new_with_ccl(
      `!(ty:cm_type).
         cm_integer_type ty ==> ~cm_is_pointer ty`);
  gnode_list cases = INDUCT_TAC(root, `ty:cm_type`);
  for (size_t i = 0; i < vector_size(cases); ++i) {
    thm view = apply_conversion(reduce_rewrite_conv(THM_LIST(
        get_cm_integer_type_def(), get_cm_is_pointer_def(),
        get_datatype_distinctness("cm_type"))),
        goal_ccl(cases[i]->g));
    ACCEPT_TAC(cases[i], eqt_elim_rule(view));
  }
  return gnode_prove(root);
}
PROOF static thm cm_integer_not_pointer =
    cm_prove_integer_not_pointer();

PROOF static thm cm_runtime_pointer_kind(
    term value, term ty, thm static_kind, thm compatible) {
  thm scalar = mp_rule(spec_rule(ty, cm_pointer_expr_type),
      static_kind);
  thm bridge = mp_rule(mp_rule(specl_rule(TERM_LIST(value, ty),
      cm_compatible_pointer_kind), scalar), compatible);
  return eq_mp_rule(sym_rule(bridge), static_kind);
}

PROOF static thm cm_runtime_integer_not_pointer(
    term value, term ty, thm integer_kind, thm compatible) {
  thm scalar = mp_rule(spec_rule(ty, cm_integer_expr_type),
      integer_kind);
  thm bridge = mp_rule(mp_rule(specl_rule(TERM_LIST(value, ty),
      cm_compatible_pointer_kind), scalar), compatible);
  thm static_not = mp_rule(spec_rule(ty, cm_integer_not_pointer),
      integer_kind);
  dest_iff_results bridge_parts = dest_iff(concl(bridge));
  return mp_rule(taut_rule(mk_imp(
      list_mk_conj(TERM_LIST(concl(bridge), concl(static_not))),
      mk_not(bridge_parts.tm1))),
      conj_rule(bridge, static_not));
}
PROOF static thm cm_binary_int_value_ready(
    thm op_equal, thm_list extra) {
  thm_list rules = THM_LIST(
      get_cm_binary_value_def(), op_equal,
      get_cm_value_type_def(), get_cm_value_type_compatible_def(),
      get_cm_is_pointer_def(),
      get_datatype_distinctness("cm_value"),
      get_datatype_distinctness("cm_type"),
      get_theorem_by_name("COND_CLAUSES"));
  for (size_t i = 0; i < vector_size(extra); ++i) {
    vector_add(&rules, extra[i]);
  }
  thm first = apply_conversion(reduce_rewrite_conv(rules),
      `cm_value_type_compatible
         (cm_binary_value (p:cm_program) (op:int)
           (left:cm_value) (right:cm_value) (result:cm_type)
           (st:cm_src_state))
         CMIntTy`);
  thm second = apply_conversion(reduce_rewrite_conv(rules),
      rhs_of(first));
  return eqt_elim_rule(trans_rule(first, second));
}

PROOF static thm cm_prove_pointer_type_reconstruct(void) {
  gnode root = gnode_new_with_ccl(
      `!(ty:cm_type).
         cm_is_pointer ty ==> CMPtrTy (cm_pointee ty) == ty`);
  gnode_list cases = INDUCT_TAC(root, `ty:cm_type`);
  for (size_t i = 0; i < vector_size(cases); ++i) {
    thm view = apply_conversion(reduce_rewrite_conv(THM_LIST(
        get_cm_is_pointer_def(), get_cm_pointee_def())),
        goal_ccl(cases[i]->g));
    ACCEPT_TAC(cases[i], eqt_elim_rule(view));
  }
  return gnode_prove(root);
}
PROOF thm cm_pointer_type_reconstruct =
    cm_prove_pointer_type_reconstruct();

PROOF static thm cm_ptr_add_static_type_ready(
    term ptr, term ty, term structs, term st, term index,
    thm compatible, thm pointer_kind, thm live) {
  thm shape = mp_rule(spec_rule(ty, cm_pointer_type_reconstruct),
      pointer_kind);
  thm compatible_view = beta_norm(ap_term_rule(
      `\target:cm_type.
         cm_value_type_compatible ${ptr:cm_value} target`,
      sym_rule(shape)));
  thm compatible_shaped = eq_mp_rule(
      compatible_view, compatible);
  thm ready = mp_rule(mp_rule(specl_rule(TERM_LIST(
      structs, st, ptr, `cm_pointee ${ty:cm_type}`, index),
      cm_ptr_add_type_ready), compatible_shaped), live);
  thm result_view = beta_norm(ap_term_rule(
      `\target:cm_type.
         cm_value_type_compatible
           (cm_ptr_add ${structs:(cm_struct_d)list}
             ${ptr:cm_value} ${index:int}) target`,
      shape));
  return eq_mp_rule(result_view, ready);
}

PROOF static thm cm_open_binary_types(thm op_equal) {
  return conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_binary_types_def(), op_equal)),
      assume_rule(
        `cm_binary_types (op:int) (left_ty:cm_type)
           (right_ty:cm_type) (result:cm_type)`));
}

PROOF static thm cm_binary_result_transport(
    thm ready, thm result_equal) {
  return conv_rule(rewrite_conv(THM_LIST(
      sym_rule(result_equal))), ready);
}

PROOF static thm cm_binary_shift_live(
    thm op_equal, thm runtime_left, thm runtime_right) {
  thm shift = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_binary_ok_def(), op_equal,
      runtime_left, runtime_right,
      get_theorem_by_name("COND_CLAUSES"))),
      assume_rule(
        `cm_binary_ok (p:cm_program) (op:int)
           (left:cm_value) (right:cm_value) (st:cm_src_state)`));
  thm opened = conv_rule(rewrite_conv(THM_LIST(
      get_cm_ptr_shift_ok_def())), shift);
  return conjunct1_rule(opened);
}

PROOF static thm cm_binary_pointer_value_ready(
    thm op_equal, thm runtime_left, thm runtime_right,
    term ptr, term target_ty, term index, thm compatible,
    thm pointer_kind, thm live) {
  thm ready = cm_ptr_add_static_type_ready(
      ptr, target_ty, `cm_program_structs (p:cm_program)`,
      `st:cm_src_state`, index, compatible, pointer_kind, live);
  thm view = apply_conversion(reduce_rewrite_conv(THM_LIST(
      get_cm_binary_value_def(), op_equal,
      runtime_left, runtime_right,
      get_theorem_by_name("COND_CLAUSES"))),
      `cm_value_type_compatible
         (cm_binary_value (p:cm_program) (op:int)
           (left:cm_value) (right:cm_value) (result:cm_type)
           (st:cm_src_state))
         ${target_ty:cm_type}`);
  return eq_mp_rule(sym_rule(view), ready);
}

PROOF static void cm_solve_binary_integer_mode(
    gnode node, thm mode, thm op_equal) {
  thm left_integer = cm_type_pick_conjunct(mode,
      `cm_integer_type (left_ty:cm_type)`);
  thm right_integer = cm_type_pick_conjunct(mode,
      `cm_integer_type (right_ty:cm_type)`);
  thm result_equal = cm_type_pick_conjunct(mode,
      `(result:cm_type) == CMIntTy`);
  thm left_compatible = assume_rule(
      `cm_value_type_compatible (left:cm_value) (left_ty:cm_type)`);
  thm right_compatible = assume_rule(
      `cm_value_type_compatible (right:cm_value) (right_ty:cm_type)`);
  thm runtime_left = cm_runtime_integer_not_pointer(
      `left:cm_value`, `left_ty:cm_type`,
      left_integer, left_compatible);
  thm runtime_right = cm_runtime_integer_not_pointer(
      `right:cm_value`, `right_ty:cm_type`,
      right_integer, right_compatible);
  thm ready = cm_binary_int_value_ready(
      op_equal, THM_LIST(runtime_left, runtime_right));
  ACCEPT_TAC(node, cm_binary_result_transport(ready, result_equal));
}

PROOF static void cm_solve_binary_left_pointer_mode(
    gnode node, thm mode, thm op_equal, term index) {
  thm left_pointer = cm_type_pick_conjunct(mode,
      `cm_is_pointer (left_ty:cm_type)`);
  thm right_integer = cm_type_pick_conjunct(mode,
      `cm_integer_type (right_ty:cm_type)`);
  thm result_equal = cm_type_pick_conjunct(mode,
      `(result:cm_type) == (left_ty:cm_type)`);
  thm left_compatible = assume_rule(
      `cm_value_type_compatible (left:cm_value) (left_ty:cm_type)`);
  thm right_compatible = assume_rule(
      `cm_value_type_compatible (right:cm_value) (right_ty:cm_type)`);
  thm runtime_left = cm_runtime_pointer_kind(
      `left:cm_value`, `left_ty:cm_type`,
      left_pointer, left_compatible);
  thm runtime_right = cm_runtime_integer_not_pointer(
      `right:cm_value`, `right_ty:cm_type`,
      right_integer, right_compatible);
  thm live = cm_binary_shift_live(
      op_equal, runtime_left, runtime_right);
  thm ready = cm_binary_pointer_value_ready(
      op_equal, runtime_left, runtime_right,
      `left:cm_value`, `left_ty:cm_type`, index,
      left_compatible, left_pointer, live);
  ACCEPT_TAC(node, cm_binary_result_transport(ready, result_equal));
}

PROOF static void cm_solve_binary_right_pointer_mode(
    gnode node, thm mode, thm op_equal) {
  thm right_pointer = cm_type_pick_conjunct(mode,
      `cm_is_pointer (right_ty:cm_type)`);
  thm left_integer = cm_type_pick_conjunct(mode,
      `cm_integer_type (left_ty:cm_type)`);
  thm result_equal = cm_type_pick_conjunct(mode,
      `(result:cm_type) == (right_ty:cm_type)`);
  thm left_compatible = assume_rule(
      `cm_value_type_compatible (left:cm_value) (left_ty:cm_type)`);
  thm right_compatible = assume_rule(
      `cm_value_type_compatible (right:cm_value) (right_ty:cm_type)`);
  thm runtime_left = cm_runtime_integer_not_pointer(
      `left:cm_value`, `left_ty:cm_type`,
      left_integer, left_compatible);
  thm runtime_right = cm_runtime_pointer_kind(
      `right:cm_value`, `right_ty:cm_type`,
      right_pointer, right_compatible);
  thm live = cm_binary_shift_live(
      op_equal, runtime_left, runtime_right);
  thm ready = cm_binary_pointer_value_ready(
      op_equal, runtime_left, runtime_right,
      `right:cm_value`, `right_ty:cm_type`,
      `cm_value_number (st:cm_src_state) (left:cm_value)`,
      right_compatible, right_pointer, live);
  ACCEPT_TAC(node, cm_binary_result_transport(ready, result_equal));
}

PROOF static void cm_solve_binary_pointer_diff_mode(
    gnode node, thm mode, thm op_equal) {
  thm types_equal = cm_type_pick_conjunct(mode,
      `(left_ty:cm_type) == (right_ty:cm_type)`);
  thm left_pointer = cm_type_pick_conjunct(mode,
      `cm_is_pointer (left_ty:cm_type)`);
  thm result_equal = cm_type_pick_conjunct(mode,
      `(result:cm_type) == CMIntTy`);
  thm right_pointer = conv_rule(
      rewrite_conv(THM_LIST(types_equal)), left_pointer);
  thm left_compatible = assume_rule(
      `cm_value_type_compatible (left:cm_value) (left_ty:cm_type)`);
  thm right_compatible = assume_rule(
      `cm_value_type_compatible (right:cm_value) (right_ty:cm_type)`);
  thm runtime_left = cm_runtime_pointer_kind(
      `left:cm_value`, `left_ty:cm_type`,
      left_pointer, left_compatible);
  thm runtime_right = cm_runtime_pointer_kind(
      `right:cm_value`, `right_ty:cm_type`,
      right_pointer, right_compatible);
  thm ready = cm_binary_int_value_ready(
      op_equal, THM_LIST(runtime_left, runtime_right));
  ACCEPT_TAC(node, cm_binary_result_transport(ready, result_equal));
}

PROOF static void cm_solve_binary_ordinary_op(
    gnode node, thm op_equal) {
  thm opened = cm_open_binary_types(op_equal);
  thm result_equal = cm_type_pick_conjunct(opened,
      `(result:cm_type) == CMIntTy`);
  thm ready = cm_binary_int_value_ready(
      op_equal, THM_LIST());
  ACCEPT_TAC(node, cm_binary_result_transport(ready, result_equal));
}

PROOF static void cm_solve_binary_add(
    gnode node, thm op_equal) {
  thm modes = cm_type_last_conjunct(
      cm_open_binary_types(op_equal));
  dest_disj_results first = dest_disj(concl(modes));
  dest_disj_results second = dest_disj(first.tm2);
  gnode_list cases = DISJ_CASES_TAC(
      node, modes, "Hadd_kind");
  cm_solve_binary_integer_mode(
      cases[0], assume_rule(first.tm1), op_equal);
  cm_solve_binary_left_pointer_mode(
      cases[1], assume_rule(second.tm1), op_equal,
      `cm_value_number (st:cm_src_state) (right:cm_value)`);
  cm_solve_binary_right_pointer_mode(
      cases[2], assume_rule(second.tm2), op_equal);
}

PROOF static void cm_solve_binary_subtract(
    gnode node, thm op_equal) {
  thm modes = cm_type_last_conjunct(
      cm_open_binary_types(op_equal));
  dest_disj_results first = dest_disj(concl(modes));
  dest_disj_results second = dest_disj(first.tm2);
  gnode_list cases = DISJ_CASES_TAC(
      node, modes, "Hsub_kind");
  cm_solve_binary_integer_mode(
      cases[0], assume_rule(first.tm1), op_equal);
  cm_solve_binary_left_pointer_mode(
      cases[1], assume_rule(second.tm1), op_equal,
      `tower_neg
         (cm_value_number (st:cm_src_state) (right:cm_value))`);
  cm_solve_binary_pointer_diff_mode(
      cases[2], assume_rule(second.tm2), op_equal);
}

PROOF static thm cm_prove_binary_value_type_ready(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (op:int) (left:cm_value)
         (right:cm_value) (left_ty:cm_type)
         (right_ty:cm_type) (result:cm_type) (st:cm_src_state).
         cm_binary_types op left_ty right_ty result ==>
         cm_value_type_compatible left left_ty ==>
         cm_value_type_compatible right right_ty ==>
         cm_binary_ok p op left right st ==>
         cm_value_type_compatible
           (cm_binary_value p op left right result st) result`);
  gnode current = AUTO_INTROS_TAC(root);
  term_list op_cases = TERM_LIST(
      `(op:int) == 0i`, `(op:int) == 1i`,
      `(op:int) == 2i`, `(op:int) == 3i`,
      `(op:int) == 4i`, `(op:int) == 5i`,
      `(op:int) == 6i`, `(op:int) == 7i`,
      `(op:int) == 8i`, `(op:int) == 9i`,
      `(op:int) == 10i`, `(op:int) == 11i`,
      `(op:int) == 12i`);
  thm_list negative_cases = vector_create();
  for (size_t i = 0; i < vector_size(op_cases); ++i) {
    gnode_list cases = BOOL_CASES_TAC(
        current, op_cases[i], gc_sprintf("Hop_case_%zu", i));
    thm op_equal = assume_rule(op_cases[i]);
    if (i == 8) {
      cm_solve_binary_add(cases[0], op_equal);
    } else if (i == 9) {
      cm_solve_binary_subtract(cases[0], op_equal);
    } else {
      cm_solve_binary_ordinary_op(cases[0], op_equal);
    }
    thm negative = assume_rule(mk_not(op_cases[i]));
    vector_add(&negative_cases, negative);
    current = cases[1];
  }
  thm opened = conv_rule(rewrite_conv(THM_LIST(
      get_cm_binary_types_def())),
      assume_rule(
        `cm_binary_types (op:int) (left_ty:cm_type)
           (right_ty:cm_type) (result:cm_type)`));
  thm lower = cm_type_pick_conjunct(opened, `0i <= (op:int)`);
  thm upper = cm_type_pick_conjunct(opened, `(op:int) <= 12i`);
  thm_list contradiction_facts = vector_create();
  vector_add(&contradiction_facts, lower);
  vector_add(&contradiction_facts, upper);
  for (size_t i = 0; i < vector_size(negative_cases); ++i) {
    vector_add(&contradiction_facts, negative_cases[i]);
  }
  term_list contradiction_terms = vector_create();
  for (size_t i = 0; i < vector_size(contradiction_facts); ++i) {
    vector_add(&contradiction_terms, concl(contradiction_facts[i]));
  }
  thm contradiction = int_arith_rule(
      imp_chain(contradiction_terms, mk_false()));
  for (size_t i = 0; i < vector_size(contradiction_facts); ++i) {
    contradiction = mp_rule(
        contradiction, contradiction_facts[i]);
  }
  CONTR_TAC(current, contradiction);
  return gnode_prove(root);
}
PROOF thm cm_binary_value_type_ready =
    cm_prove_binary_value_type_ready();

PROOF static thm cm_prove_pointer_view_type(void) {
  gnode root = gnode_new_with_ccl(
      `!(st:cm_src_state) (v:cm_value) (ty:cm_type).
         cm_value_type_compatible v ty ==>
         cm_is_pointer ty ==>
         cm_pointer_live st v ==>
         cm_ptr_view v == cm_pointee ty`);
  gnode_list value_cases = INDUCT_TAC(root, `v:cm_value`);
  for (size_t i = 0; i < vector_size(value_cases); ++i) {
    gnode_list type_cases = INDUCT_TAC(value_cases[i], `ty:cm_type`);
    for (size_t j = 0; j < vector_size(type_cases); ++j) {
      thm view = apply_conversion(reduce_rewrite_conv(THM_LIST(
          get_cm_value_type_compatible_def(), get_cm_value_type_def(),
          get_cm_is_pointer_def(), get_cm_pointer_live_def(),
          get_cm_ptr_gen_def(), get_cm_ptr_view_def(),
          get_cm_pointee_def(),
          get_datatype_distinctness("cm_value"),
          get_datatype_injectivity("cm_value"),
          get_datatype_distinctness("cm_type"),
          get_datatype_injectivity("cm_type"))),
          goal_ccl(type_cases[j]->g));
      ACCEPT_TAC(type_cases[j], eq_mp_rule(sym_rule(view),
          taut_rule(rhs_of(view))));
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_pointer_view_type =
    cm_prove_pointer_view_type();

PROOF static thm cm_prove_ptr_add_result_type_ready(void) {
  gnode root = gnode_new_with_ccl(
      `!(structs:(cm_struct_d)list) (st:cm_src_state)
         (ptr:cm_value) (ty:cm_type) (index:int).
         cm_value_type_compatible ptr ty ==>
         cm_is_pointer ty ==>
         cm_pointer_live st ptr ==>
         cm_value_type_compatible
           (cm_ptr_add structs ptr index) ty`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm ready = cm_ptr_add_static_type_ready(
      `ptr:cm_value`, `ty:cm_type`,
      `structs:(cm_struct_d)list`, `st:cm_src_state`, `index:int`,
      assume_rule(
        `cm_value_type_compatible (ptr:cm_value) (ty:cm_type)`),
      assume_rule(`cm_is_pointer (ty:cm_type)`),
      assume_rule(`cm_pointer_live (st:cm_src_state) (ptr:cm_value)`));
  ACCEPT_TAC(leaf, ready);
  return gnode_prove(root);
}
PROOF thm cm_ptr_add_result_type_ready =
    cm_prove_ptr_add_result_type_ready();

PROOF static thm cm_prove_string_value_type_ready(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (sid:int).
         cm_value_type_compatible
           (cm_string_pointer p sid) (CMPtrTy CMCharTy)`);
  thm view = apply_conversion(reduce_rewrite_conv(THM_LIST(
      get_cm_string_pointer_def(), get_cm_value_type_def(),
      get_cm_value_type_compatible_def(),
      get_datatype_distinctness("cm_value"),
      get_datatype_distinctness("cm_type"))),
      goal_ccl(root->g));
  ACCEPT_TAC(root, eqt_elim_rule(view));
  return gnode_prove(root);
}
PROOF thm cm_string_value_type_ready =
    cm_prove_string_value_type_ready();

PROOF static thm cm_prove_const_value_type_ready(void) {
  gnode root = gnode_new_with_ccl(
      `!(st:cm_src_state) (n:int) (ty:cm_type).
         cm_integer_type ty ==>
         cm_value_type_compatible
           (cm_convert_value st ty (CMIntV n)) ty`);
  gnode_list type_cases = INDUCT_TAC(root, `ty:cm_type`);
  for (size_t i = 0; i < vector_size(type_cases); ++i) {
    thm view = apply_conversion(reduce_rewrite_conv(THM_LIST(
        get_cm_integer_type_def(), get_cm_convert_value_def(),
        get_cm_value_number_def(), get_cm_value_type_def(),
        get_cm_value_type_compatible_def(), get_cm_is_pointer_def(),
        get_datatype_distinctness("cm_value"),
        get_datatype_distinctness("cm_type"),
        get_theorem_by_name("COND_CLAUSES"))),
        goal_ccl(type_cases[i]->g));
    thm second = apply_conversion(reduce_rewrite_conv(THM_LIST(
        get_cm_value_type_def(), get_cm_value_type_compatible_def(),
        get_cm_is_pointer_def(),
        get_datatype_distinctness("cm_value"),
        get_datatype_distinctness("cm_type"))), rhs_of(view));
    ACCEPT_TAC(type_cases[i],
        eqt_elim_rule(trans_rule(view, second)));
  }
  return gnode_prove(root);
}
PROOF thm cm_const_value_type_ready =
    cm_prove_const_value_type_ready();

PROOF static int cmc_preservation_type_value_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_type_value_axioms_before,
      "value type proofs introduced axioms");
  ENSURE_COND(vector_size(hyp(cm_pointer_retype_type_ready)) == 0,
      "pointer retype theorem is not closed");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_type_value_checks =
    cmc_preservation_type_value_final_checks();
