#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_store_semantic.h"
#include "cmc_preservation_type_value.h"

#require "cmc_preservation_runtime.c"
#require "cmc_preservation_store_provenance.c"
#require "cmc_preservation_type_value.c"

PROOF static size_t _cmc_preservation_store_semantic_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_prove_store_runtime_layout(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (ty:cm_type) (ptr:cm_value) (v:cm_value)
         (st:cm_src_state) (calls:(cm_call_sim_frame)list)
         (frames:(cm_spill_frame)list).
         cm_runtime_memory_layout p st calls frames ==>
         cm_runtime_memory_layout p (cm_state_store ty ptr v st)
           calls frames`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm_list rules = get_cm_state_core_defs();
  vector_add(&rules, get_cm_state_store_def());
  vector_add(&rules, get_cm_runtime_memory_layout_def());
  thm old_layout = assume_rule(
      `cm_runtime_memory_layout (p:cm_program) (st:cm_src_state)
        (calls:(cm_call_sim_frame)list)
        (frames:(cm_spill_frame)list)`);
  thm normalized = conv_rule(
      reduce_rewrite_conv(rules), old_layout);
  thm target_view = apply_conversion(
      reduce_rewrite_conv(rules), goal_ccl(leaf->g));
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), normalized));
  return gnode_prove(root);
}
PROOF thm cm_store_runtime_layout =
    cm_prove_store_runtime_layout();

PROOF static thm cm_prove_store_live_span(void) {
  gnode root = gnode_new_with_ccl(
      `!(ty:cm_type) (ptr:cm_value) (v:cm_value)
         (st:cm_src_state) (base:int) (width:int).
         cm_live_span st base width ==>
         cm_live_span (cm_state_store ty ptr v st) base width`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm old_span = assume_rule(
      `cm_live_span (st:cm_src_state) (base:int) (width:int)`);
  thm_list rules = THM_LIST(
      cm_live_span_def, get_cm_live_address_store());
  thm normalized = conv_rule(
      reduce_rewrite_conv(rules), old_span);
  thm target_view = apply_conversion(
      reduce_rewrite_conv(rules), goal_ccl(leaf->g));
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), normalized));
  return gnode_prove(root);
}
PROOF thm cm_store_live_span = cm_prove_store_live_span();

PROOF static thm cm_prove_pointer_retype_idempotent(void) {
  gnode root = gnode_new_with_ccl(
      `!(v:cm_value) (ty:cm_type).
         cm_pointer_retype ty (cm_pointer_retype ty v) ==
         cm_pointer_retype ty v`);
  gnode_list cases = INDUCT_TAC(root, `v:cm_value`);
  for (size_t i = 0; i < 2; ++i) {
    gnode leaf = AUTO_INTROS_TAC(cases[i]);
    term condition = i == 0
        ? `tower_wrap64 (a:int) == 0i`
        : `tower_u8 (a:int) == 0i`;
    gnode_list zero_cases =
        BOOL_CASES_TAC(leaf, condition, "Hzero");
    for (size_t j = 0; j < vector_size(zero_cases); ++j) {
      CONV_WITH_ASMP_TAC(
          zero_cases[j], reduce_rewrite_conv,
          THM_LIST(get_cm_pointer_retype_def()));
    }
  }
  for (size_t i = 2; i < vector_size(cases); ++i) {
    CONV_TAC(cases[i], reduce_rewrite_conv(
        THM_LIST(get_cm_pointer_retype_def())));
  }
  return gnode_prove(root);
}
PROOF static thm cm_pointer_retype_idempotent =
    cm_prove_pointer_retype_idempotent();

PROOF static thm cm_prove_convert_value_idempotent(void) {
  gnode root = gnode_new_with_ccl(
      `!(st:cm_src_state) (ty:cm_type) (v:cm_value).
         cm_convert_value st ty (cm_convert_value st ty v) ==
         cm_convert_value st ty v`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list int_cases = BOOL_CASES_TAC(
      leaf, `(ty:cm_type) == CMIntTy`, "Hint");
  {
    CONV_WITH_ASMP_TAC(
        int_cases[0], reduce_rewrite_conv,
        THM_LIST(get_cm_convert_value_def(),
          get_cm_value_number_def(),
          get_tower_wrap64_idempotent()));
  }
  gnode_list char_cases = BOOL_CASES_TAC(
      int_cases[1], `(ty:cm_type) == CMCharTy`, "Hchar");
  {
    CONV_WITH_ASMP_TAC(
        char_cases[0], reduce_rewrite_conv,
        THM_LIST(get_cm_convert_value_def(),
          get_cm_value_number_def(),
          get_tower_u8_idempotent()));
  }
  {
    CONV_WITH_ASMP_TAC(
        char_cases[1], reduce_rewrite_conv,
        THM_LIST(get_cm_convert_value_def(),
          cm_pointer_retype_idempotent));
  }
  return gnode_prove(root);
}
PROOF static thm cm_convert_value_idempotent =
    cm_prove_convert_value_idempotent();

PROOF static thm cm_prove_state_store_converted(void) {
  gnode root = gnode_new_with_ccl(
      `!(ty:cm_type) (ptr:cm_value) (v:cm_value)
         (st:cm_src_state).
         cm_state_store ty ptr (cm_convert_value st ty v) st ==
         cm_state_store ty ptr v st`);
  gnode leaf = AUTO_INTROS_TAC(root);
  CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
      get_cm_state_store_def(), cm_convert_value_idempotent)));
  return gnode_prove(root);
}
PROOF thm cm_state_store_converted =
    cm_prove_state_store_converted();

PROOF static thm cm_prove_store_load_ok(void) {
  gnode root = gnode_new_with_ccl(
      `!(ty:cm_type) (ptr:cm_value) (v:cm_value)
         (st:cm_src_state).
         cm_store_ok ty ptr st ==>
         (ty == CMCharTy || ty == CMIntTy || cm_is_pointer ty) ==>
         cm_scalar_expr_type ty ==>
         cm_value_convertible_to v ty ==>
         cm_load_ok ty ptr (cm_state_store ty ptr v st)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm store_ok = assume_rule(
      `cm_store_ok (ty:cm_type) (ptr:cm_value) (st:cm_src_state)`);
  thm kinds = assume_rule(
      `(ty:cm_type) == CMCharTy || ty == CMIntTy ||
       cm_is_pointer ty`);
  thm scalar = assume_rule(`cm_scalar_expr_type (ty:cm_type)`);
  thm convertible = assume_rule(
      `cm_value_convertible_to (v:cm_value) (ty:cm_type)`);
  thm converted_type = match_mp_rule(specl_rule(TERM_LIST(
      `st:cm_src_state`, `v:cm_value`, `ty:cm_type`),
      cm_convert_value_type_ready), convertible);
  thm pointer_equiv = match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(
        `cm_convert_value (st:cm_src_state) (ty:cm_type) (v:cm_value)`,
        `ty:cm_type`), cm_compatible_pointer_kind), scalar),
      converted_type);
  term base =
      `cm_value_number (st:cm_src_state) (ptr:cm_value)`;
  term converted =
      `cm_value_number (st:cm_src_state)
        (cm_convert_value st (ty:cm_type) (v:cm_value))`;
  thm converted_signed = specl_rule(TERM_LIST(
      `st:cm_src_state`,
      `cm_convert_value st (ty:cm_type) (v:cm_value)`),
      get_cm_value_number_signed_bridge());
  thm converted_fixed = mp_rule(
      spec_rule(converted, get_tower_wrap64_fixed()),
      converted_signed);
  thm_list common = get_cm_state_core_defs();
  vector_add(&common, get_cm_state_store_def());
  vector_add(&common, get_cm_store_ok_def());
  vector_add(&common, get_cm_load_ok_def());
  vector_add(&common, get_cm_store_width_def());
  vector_add(&common, get_cm_mark_init_def());
  vector_add(&common, get_cm_bytes_initialized_def());
  vector_add(&common, get_cm_pointer_writable_def());
  vector_add(&common, get_cm_is_pointer_def());
  vector_add(&common, get_cm_pointer_live_def());
  vector_add(&common, get_cm_store_mem_def());
  vector_add(&common, get_cm_clear_tagged_def());
  vector_add(&common, get_cm_value_number_state_store());
  vector_add(&common, get_tower_getw_setw());
  vector_add(&common, converted_fixed);
  vector_add(&common, int_arith_rule(
      `${base:int} <= ${base:int}`));
  vector_add(&common, int_arith_rule(
      `${base:int} < ${base:int} + 1i`));
  vector_add(&common, int_arith_rule(
      `${base:int} < ${base:int} + 8i`));
  term_list offsets = TERM_LIST(
      `0i`, `1i`, `2i`, `3i`, `4i`, `5i`, `6i`, `7i`);
  for (size_t i = 0; i < vector_size(offsets); ++i) {
    term address = `${base:int} + ${offsets[i]:int}`;
    vector_add(&common, int_arith_rule(
        `${base:int} <= ${address:int}`));
    vector_add(&common, int_arith_rule(
        `${address:int} < ${base:int} + 8i`));
  }
  gnode_list char_cases =
      BOOL_CASES_TAC(leaf, `(ty:cm_type) == CMCharTy`, "Hchar");
  {
    thm is_char = assume_rule(`(ty:cm_type) == CMCharTy`);
    thm_list rules = (thm_list)vector_copy(common);
    vector_add(&rules, is_char);
    vector_add(&rules, kinds);
    thm normalized =
        conv_rule(reduce_rewrite_conv(rules), store_ok);
    thm target_view = apply_conversion(
        reduce_rewrite_conv(rules), goal_ccl(char_cases[0]->g));
    thm target_normal = mp_rule(taut_rule(mk_imp(
        concl(normalized), rhs_of(target_view))), normalized);
    ACCEPT_TAC(char_cases[0],
        eq_mp_rule(sym_rule(target_view), target_normal));
  }
  gnode_list int_cases = BOOL_CASES_TAC(
      char_cases[1], `(ty:cm_type) == CMIntTy`, "Hint");
  {
    thm not_char =
        assume_rule(`~((ty:cm_type) == CMCharTy)`);
    thm is_int = assume_rule(`(ty:cm_type) == CMIntTy`);
    thm_list rules = (thm_list)vector_copy(common);
    vector_add(&rules, not_char);
    vector_add(&rules, is_int);
    vector_add(&rules, kinds);
    thm normalized =
        conv_rule(reduce_rewrite_conv(rules), store_ok);
    thm target_view = apply_conversion(
        reduce_rewrite_conv(rules), goal_ccl(int_cases[0]->g));
    thm target_normal = mp_rule(taut_rule(mk_imp(
        concl(normalized), rhs_of(target_view))), normalized);
    ACCEPT_TAC(int_cases[0],
        eq_mp_rule(sym_rule(target_view), target_normal));
  }
  {
    thm not_char =
        assume_rule(`~((ty:cm_type) == CMCharTy)`);
    thm not_int =
        assume_rule(`~((ty:cm_type) == CMIntTy)`);
    thm pointer_kind = conv_rule(
        reduce_rewrite_conv(THM_LIST(not_char, not_int)),
        kinds);
    thm_list rules = (thm_list)vector_copy(common);
    vector_add(&rules, not_char);
    vector_add(&rules, not_int);
    vector_add(&rules, pointer_kind);
    thm converted_pointer =
        eq_mp_rule(gsym_rule(pointer_equiv), pointer_kind);
    vector_add(&rules, converted_pointer);
    thm normalized =
        conv_rule(reduce_rewrite_conv(rules), store_ok);
    thm target_view = apply_conversion(
        reduce_rewrite_conv(rules), goal_ccl(int_cases[1]->g));
    thm target_normal = mp_rule(taut_rule(mk_imp(
        concl(normalized), rhs_of(target_view))), normalized);
    ACCEPT_TAC(int_cases[1],
        eq_mp_rule(sym_rule(target_view), target_normal));
  }
  return gnode_prove(root);
}
PROOF thm cm_store_load_ok = cm_prove_store_load_ok();

PROOF static thm cm_prove_store_load_number(void) {
  gnode root = gnode_new_with_ccl(
      `!(ty:cm_type) (ptr:cm_value) (v:cm_value)
         (st:cm_src_state).
         (ty == CMCharTy || ty == CMIntTy || cm_is_pointer ty) ==>
         cm_value_number (cm_state_store ty ptr v st)
           (cm_load_value ty ptr (cm_state_store ty ptr v st)) ==
         cm_value_number (cm_state_store ty ptr v st)
           (cm_convert_value st ty v)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm kinds = assume_rule(
      `(ty:cm_type) == CMCharTy || ty == CMIntTy ||
       cm_is_pointer ty`);
  term converted =
      `cm_value_number (st:cm_src_state)
        (cm_convert_value st (ty:cm_type) (v:cm_value))`;
  thm converted_signed = specl_rule(TERM_LIST(
      `st:cm_src_state`,
      `cm_convert_value st (ty:cm_type) (v:cm_value)`),
      get_cm_value_number_signed_bridge());
  thm converted_fixed = mp_rule(
      spec_rule(converted, get_tower_wrap64_fixed()),
      converted_signed);
  thm original_signed = specl_rule(TERM_LIST(
      `st:cm_src_state`, `v:cm_value`),
      get_cm_value_number_signed_bridge());
  thm original_fixed = mp_rule(
      spec_rule(
        `cm_value_number (st:cm_src_state) (v:cm_value)`,
        get_tower_wrap64_fixed()),
      original_signed);
  thm zero_signed = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(get_tower_signed64_def())),
      `tower_signed64 0i`));
  thm zero_fixed = mp_rule(
      spec_rule(`0i`, get_tower_wrap64_fixed()), zero_signed);
  thm_list common = get_cm_state_core_defs();
  vector_add(&common, get_cm_state_store_def());
  vector_add(&common, get_cm_store_mem_def());
  vector_add(&common, get_cm_load_value_def());
  vector_add(&common, get_cm_value_number_def());
  vector_add(&common, get_cm_value_number_state_store());
  vector_add(&common, get_cm_is_pointer_def());
  vector_add(&common, get_tower_getb_setb_same());
  vector_add(&common, get_tower_getw_setw());
  vector_add(&common, get_tower_u8_idempotent());
  vector_add(&common, get_tower_wrap64_idempotent());
  vector_add(&common, get_cm_pointer_retype_number_bridge());
  vector_add(&common, specl_rule(TERM_LIST(
      `st:cm_src_state`, `ty:cm_type`, `v:cm_value`),
      get_cm_convert_value_number_bridge()));
  vector_add(&common, converted_fixed);
  gnode_list char_cases =
      BOOL_CASES_TAC(leaf, `(ty:cm_type) == CMCharTy`, "Hchar");
  vector_add(&common, original_fixed);
  vector_add(&common, zero_fixed);
  {
    thm_list rules = (thm_list)vector_copy(common);
    vector_add(&rules,
        assume_rule(`(ty:cm_type) == CMCharTy`));
    CONV_WITH_ASMP_TAC(
        char_cases[0], reduce_rewrite_conv, rules);
  }
  gnode_list int_cases = BOOL_CASES_TAC(
      char_cases[1], `(ty:cm_type) == CMIntTy`, "Hint");
  {
    thm_list rules = (thm_list)vector_copy(common);
    vector_add(&rules,
        assume_rule(`~((ty:cm_type) == CMCharTy)`));
    vector_add(&rules,
        assume_rule(`(ty:cm_type) == CMIntTy`));
    CONV_WITH_ASMP_TAC(
        int_cases[0], reduce_rewrite_conv, rules);
  }
  {
    thm not_char =
        assume_rule(`~((ty:cm_type) == CMCharTy)`);
    thm not_int =
        assume_rule(`~((ty:cm_type) == CMIntTy)`);
    thm pointer_kind = conv_rule(
        reduce_rewrite_conv(THM_LIST(not_char, not_int)),
        kinds);
    thm pointer_number = conv_rule(
        reduce_rewrite_conv(THM_LIST(not_char)),
        specl_rule(TERM_LIST(
          `st:cm_src_state`, `ty:cm_type`, `v:cm_value`),
          get_cm_convert_value_number_bridge()));
    gnode_list zero_cases = BOOL_CASES_TAC(
        int_cases[1], `${converted:int} == 0i`, "Hzero");
    for (size_t i = 0; i < vector_size(zero_cases); ++i) {
      thm_list rules = (thm_list)vector_copy(common);
      vector_add(&rules, not_char);
      vector_add(&rules, not_int);
      vector_add(&rules, pointer_kind);
      thm zero_fact = assume_rule(i == 0
          ? `${converted:int} == 0i`
          : `~(${converted:int} == 0i)`);
      vector_add(&rules, zero_fact);
      vector_add(&rules, conv_rule(
          rewrite_conv(THM_LIST(pointer_number)), zero_fact));
      CONV_WITH_ASMP_TAC(
          zero_cases[i], reduce_rewrite_conv, rules);
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_store_load_number =
    cm_prove_store_load_number();

PROOF thm get_cm_state_store_converted(void) {
  return cm_state_store_converted;
}
PROOF thm get_cm_store_runtime_layout(void) {
  return cm_store_runtime_layout;
}
PROOF thm get_cm_store_live_span(void) {
  return cm_store_live_span;
}
PROOF thm get_cm_store_load_ok(void) {
  return cm_store_load_ok;
}
PROOF thm get_cm_store_load_number(void) {
  return cm_store_load_number;
}

PROOF static int cmc_preservation_store_semantic_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_store_semantic_axioms_before,
      "cmc_preservation_store_semantic introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_store_semantic_checks =
    cmc_preservation_store_semantic_final_checks();
