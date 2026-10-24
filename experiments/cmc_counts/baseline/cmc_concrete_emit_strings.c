#include "cmc_concrete_emit_strings.h"
#include "userlib/pure_lists.h"
#include "cmc_list_selectors.h"
#require "cmc_list_selectors.c"
#include "userlib/proof.h"
#include "userlib/operational.h"
#require "cmc_concrete_copy_bytes.c"
#require "userlib/pure_lists.c"


PROOF static thm cmc_ilength_nonnegative(void) {
  gnode root = gnode_new_with_ccl(
      `!(xs:(int)list). 0i <= ilength xs`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm model = spec_rule(`xs:(int)list`, mk_ilength_of_num_length());
  thm lifted = beta_norm(ap_term_rule(`\x:int. 0i <= x`, model));
  thm positive = spec_rule(`LENGTH (xs:(int)list)`,
      get_theorem_by_name("INT_POS"));
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(lifted), positive));
  return gnode_prove(root);
}
PROOF static thm cmc_ilength_nonnegative_rule =
    cmc_ilength_nonnegative();

PROOF static thm cmc_string_length_model(const term string_model) {
  return inst_rule(TERM_PAIR_LIST(
      (term_pair){string_model, `string:cm_string_d`}),
      get_cm_rep_string_length_def());
}

int cmc_emit_strings(struct cm_string *node,
                      unsigned char *data, int capacity, int cursor)
    [[cst::param(`strings:(cm_string_d)list`, `prefix:(int)list`)]]
    [[cst::require(
      `fact(cm_rep_strings_safe strings <=> true) **
       fact(0i <= cursor) **
       fact(cursor + cm_rep_strings_size strings <= capacity) **
       fact(capacity <= 2147483647i) **
       cm_string_list_rep node strings **
       store_uint8_array data cursor prefix **
       store_undef_uint8_array
         (data + cursor * sizeof Tuchar) (capacity - cursor)`)]]
    [[cst::ensure(
      `fact(cm_rep_strings_safe strings <=> true) **
       cm_string_list_rep node strings **
       store_uint8_array data
         (cursor + cm_rep_strings_size strings)
         (prefix ++ cm_strings_bytes strings) **
       store_undef_uint8_array
         (data + (cursor + cm_rep_strings_size strings) * sizeof Tuchar)
         (capacity - (cursor + cm_rep_strings_size strings)) **
       fact((__return:int) ==
         cursor + cm_rep_strings_size strings)`)]]
{
  if (node == 0) {
    [[cst::proof]] {
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          mp_rule(specl_rule(TERM_LIST(
              `node__pre:int`, `strings:(cm_string_d)list`),
              get_cm_string_null()),
            assume_rule(`node__pre == 0i`))));
      thm nil_model = assume_rule(
          `strings == ([]:(cm_string_d)list)`);
      thm list_view = apply_conversion(rewrite_conv(THM_LIST(
          nil_model, get_cm_string_list_rep_def())),
          `cm_string_list_rep (node__pre:int) strings`);
      apply_hconv_st(eq2ent(sym_rule(list_view)));
      thm destination_view = apply_conversion(rewrite_conv(THM_LIST(
          nil_model, get_cm_rep_strings_size_def(),
          get_cm_strings_bytes_def(), get_theorem_by_name("APPEND_NIL"),
          get_theorem_by_name("INT_ADD_RID"))),
          `store_uint8_array (data__pre:int)
            ((cursor__pre:int) + cm_rep_strings_size strings)
            ((prefix:(int)list) ++ cm_strings_bytes strings)`);
      apply_hconv_st(eq2ent(sym_rule(destination_view)));
      thm undefined_view = apply_conversion(rewrite_conv(THM_LIST(
          nil_model, get_cm_rep_strings_size_def(),
          get_theorem_by_name("INT_ADD_RID"))),
          `store_undef_uint8_array
            ((data__pre:int) +
              ((cursor__pre:int) + cm_rep_strings_size strings) *
                sizeof Tuchar)
            ((capacity__pre:int) -
              (cursor__pre + cm_rep_strings_size strings))`);
      apply_hconv_st(eq2ent(sym_rule(undefined_view)));
      thm cursor_view = by_rewrite(
          `(cursor__pre:int) ==
           cursor__pre + cm_rep_strings_size strings`,
          THM_LIST(nil_model, get_cm_rep_strings_size_def(),
            get_theorem_by_name("INT_ADD_RID")));
      add_fact_st(cursor_view);
    }
    return cursor;
  };

  [[cst::proof]] {
    thm opened = mp_rule(specl_rule(TERM_LIST(
        `node__pre:int`, `strings:(cm_string_d)list`),
        get_cm_string_unfold()),
        assume_rule(`~(node__pre == 0i)`));
    cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
        rename_exists_hconv(opened, TERM_LIST(
          `string_:cm_string_d`, `rest_:(cm_string_d)list`,
          `bytes_ptr_:int`, `next_:int`))));

    thm shape = assume_rule(
        `strings == (string_:cm_string_d) ::
          (rest_:(cm_string_d)list)`);
    thm safe = from_state_bool(
        `cm_rep_strings_safe (strings:(cm_string_d)list)`);
    thm opened_safe = conv_rule(rewrite_conv(THM_LIST(
        shape, get_cm_rep_strings_safe_def())), safe);
    add_fact_st(conjunct1_rule(opened_safe));
    thm safe_tail = conjunct2_rule(opened_safe);
    add_fact_st(conjunct1_rule(safe_tail));
    safe_tail = conjunct2_rule(safe_tail);
    add_fact_st(conjunct1_rule(safe_tail));
    add_fact_st(eqt_intro_rule(conjunct2_rule(safe_tail)));

    thm length_model = cmc_string_length_model(`string_:cm_string_d`);
    add_fact_st(length_model);
    add_fact_st(sym_rule(length_model));
    add_fact_st(spec_rule(`cm_string_bytes (string_:cm_string_d)`,
        cmc_ilength_nonnegative_rule));

    thm total_model = trans_rule(beta_norm(ap_term_rule(
        `cm_rep_strings_size:(cm_string_d)list->int`, shape)),
        apply_conversion(rewrite_conv(THM_LIST(
          get_cm_rep_strings_size_def(), get_cm_rep_string_size_def(),
          get_cm_rep_string_length_def())),
          `cm_rep_strings_size
            ((string_:cm_string_d) ::
             (rest_:(cm_string_d)list))`));
    add_fact_st(total_model);
    thm bytes_model = trans_rule(beta_norm(ap_term_rule(
        `cm_strings_bytes:(cm_string_d)list->(int)list`, shape)),
        apply_conversion(rewrite_conv(THM_LIST(
          get_cm_strings_bytes_def())),
          `cm_strings_bytes
            ((string_:cm_string_d) ::
             (rest_:(cm_string_d)list))`));
    add_fact_st(bytes_model);

    cst_set_symbolic_state(add_arith_fact_st(
        cst_get_symbolic_state(),
        "0i <= cursor__pre ==> "
        "cursor__pre + cm_rep_strings_size strings <= capacity__pre ==> "
        "cm_rep_strings_size strings == ("
        "  ilength (cm_string_bytes (string_:cm_string_d)) + 1i) + "
        "  cm_rep_strings_size (rest_:(cm_string_d)list) ==> "
        "0i <= ilength (cm_string_bytes string_) ==> "
        "0i <= cm_rep_strings_size rest_ ==> "
        "capacity__pre <= 2147483647i ==> "
        "(cursor__pre + ilength (cm_string_bytes string_) <= capacity__pre && "
        " cursor__pre + (ilength (cm_string_bytes string_) + 1i) <= "
        "   capacity__pre && "
        " 0i <= cursor__pre + (ilength (cm_string_bytes string_) + 1i) && "
        " cursor__pre + (ilength (cm_string_bytes string_) + 1i) + "
        "   cm_rep_strings_size rest_ <= capacity__pre && "
        " cursor__pre + (ilength (cm_string_bytes string_) + 1i) <= "
        "   2147483647i)"));
    thm head_model = apply_conversion(rewrite_conv(THM_LIST(
        shape, get_theorem_by_name("HD"))),
        `HD (strings:(cm_string_d)list)`);
    thm tail_model = apply_conversion(rewrite_conv(THM_LIST(
        shape, get_theorem_by_name("TL"))),
        `TL (strings:(cm_string_d)list)`);
    thm stable_shape = conv_rule(rewrite_conv(THM_LIST(
        sym_rule(head_model), sym_rule(tail_model))), shape);
    add_fact_st(stable_shape);
    substitute_st(sym_rule(head_model));
    substitute_st(sym_rule(tail_model));
  }

  unsigned char *source = node->bytes;
  int length = node->length;
  struct cm_string *next = node->next;

  cmc_copy_bytes(source, length, data, capacity, cursor);

  [[cst::proof]] {
    thm zero_byte = conv_rule(reduce_rewrite_conv(THM_LIST(
        get_tower_u8_def())), spec_rule(`0i:int`,
          get_tower_u8_range()));
    add_fact_st(eqt_intro_rule(zero_byte));
    add_fact_st(refl_rule(`0i:int`));
    cst_set_symbolic_state(add_arith_fact_st(
        cst_get_symbolic_state(),
        "0i <= cursor__pre ==> "
        "0i <= ilength (cm_string_bytes "
        "  (HD (strings:(cm_string_d)list))) ==> "
        "cm_rep_string_length (HD strings) == "
        "  ilength (cm_string_bytes (HD strings)) ==> "
        "cursor__pre + ilength (cm_string_bytes (HD strings)) + 1i <= "
        "  capacity__pre ==> "
        "(0i <= cursor__pre + cm_rep_string_length (HD strings) && "
        " cursor__pre + cm_rep_string_length (HD strings) < "
        "   capacity__pre)"));
  }
  cmc_write_byte(data, capacity,
      cursor + length, (unsigned char)0);
  [[cst::proof]] {
    thm assoc = ispecl_rule(TERM_LIST(
        `prefix:(int)list`,
        `cm_string_bytes (HD (strings:(cm_string_d)list))`,
        `[0i]:(int)list`), get_theorem_by_name("APPEND_ASSOC"));
    substitute_st(sym_rule(assoc));
    cst_set_symbolic_state(add_arith_fact_st(
        cst_get_symbolic_state(),
        "cm_rep_string_length "
        "  (HD (strings:(cm_string_d)list)) == "
        "  ilength (cm_string_bytes (HD strings)) ==> "
        "0i <= cursor__pre + ilength (cm_string_bytes (HD strings)) + 1i ==> "
        "cursor__pre + (ilength (cm_string_bytes (HD strings)) + 1i) + "
        "  cm_rep_strings_size (TL strings) <= capacity__pre ==> "
        "cursor__pre + ilength (cm_string_bytes (HD strings)) + 1i <= "
        "  2147483647i ==> "
        "(0i <= cursor__pre + cm_rep_string_length (HD strings) + 1i && "
        " cursor__pre + cm_rep_string_length (HD strings) + 1i + "
        "   cm_rep_strings_size (TL strings) <= capacity__pre && "
        " cursor__pre + cm_rep_string_length (HD strings) + 1i <= "
        "   2147483647i)"));
  }

  [[cst::where(`strings`,
      `TL (strings:(cm_string_d)list)`)]]
  [[cst::where(`prefix`,
      `(prefix:(int)list) ++
       (cm_string_bytes (HD (strings:(cm_string_d)list)) ++ [0i])`)]]
  int final_cursor = cmc_emit_strings(next, data, capacity,
      cursor + length + 1);

  [[cst::proof]] {
    thm shape = assume_rule(
        `strings ==
          HD (strings:(cm_string_d)list) :: TL strings`);
    thm total_model = trans_rule(beta_norm(ap_term_rule(
        `cm_rep_strings_size:(cm_string_d)list->int`, shape)),
        apply_conversion(rewrite_conv(THM_LIST(
          get_cm_rep_strings_size_def(),
          get_cm_rep_string_size_def())),
          `cm_rep_strings_size
            (HD (strings:(cm_string_d)list) :: TL strings)`));
    thm total_step = mp_rule(int_arith_rule(
        `cm_rep_strings_size strings ==
           (cm_rep_string_length
              (HD (strings:(cm_string_d)list)) + 1i) +
             cm_rep_strings_size (TL strings) ==>
         (((cursor__pre:int) +
             cm_rep_string_length (HD strings)) + 1i) +
           cm_rep_strings_size (TL strings) ==
         cursor__pre + cm_rep_strings_size strings`),
        total_model);
    thm assoc = ispecl_rule(TERM_LIST(
        `prefix:(int)list`,
        `cm_string_bytes (HD (strings:(cm_string_d)list)) ++ [0i]`,
        `cm_strings_bytes (TL (strings:(cm_string_d)list))`),
        get_theorem_by_name("APPEND_ASSOC"));
    thm bytes_model = trans_rule(beta_norm(ap_term_rule(
        `cm_strings_bytes:(cm_string_d)list->(int)list`, shape)),
        apply_conversion(rewrite_conv(THM_LIST(
          get_cm_strings_bytes_def())),
          `cm_strings_bytes
            (HD (strings:(cm_string_d)list) :: TL strings)`));
    thm prefix_model = beta_norm(ap_term_rule(
        `\xs:(int)list. (prefix:(int)list) ++ xs`,
        sym_rule(bytes_model)));
    thm inner_assoc = ispecl_rule(TERM_LIST(
        `cm_string_bytes (HD (strings:(cm_string_d)list))`,
        `[0i]:(int)list`,
        `cm_strings_bytes (TL (strings:(cm_string_d)list))`),
        get_theorem_by_name("APPEND_ASSOC"));
    thm lifted_inner = beta_norm(ap_term_rule(
        `\xs:(int)list. (prefix:(int)list) ++ xs`,
        sym_rule(inner_assoc)));
    thm list_step = trans_rule(sym_rule(assoc),
        trans_rule(lifted_inner, prefix_model));

    substitute_st(total_step);
    substitute_st(list_step);

    thm folded = mp_rule(specl_rule(TERM_LIST(
        `node__pre:int`, `HD (strings:(cm_string_d)list)`,
        `TL (strings:(cm_string_d)list)`,
        `bytes_ptr_:int`, `next_:int`),
        get_cm_string_fold()),
        assume_rule(`~(node__pre == 0i)`));
    apply_hconv_st(folded);
    thm list_view = beta_norm(ap_term_rule(
        `\xs:(cm_string_d)list.
           cm_string_list_rep (node__pre:int) xs`, shape));
    apply_hconv_st(eq2ent(sym_rule(list_view)));
  }
  return final_cursor;
}
