#include "cmc_concrete_copy_bytes.h"
#include "userlib/array.h"
#include "userlib/pure_lists.h"
#include "userlib/proof.h"
#include "userlib/operational.h"
#require "cmc_concrete_emit_bytes.c"
#require "userlib/array.c"
#require "userlib/pure_lists.c"

PROOF int _e_cmc_copy_sublist =
    cst_add_const_to_header(`sublist:int->int->(int)list->(int)list`);

PROOF static thm cmc_ilength_eq_nil(void) {
  gnode root = gnode_new_with_ccl(
      `!(xs:(int)list). ilength xs == 0i <=> xs == []`);
  gnode leaf = AUTO_INTROS_TAC(root);
  CONV_TAC(leaf, rewrite_conv(THM_LIST(
      mk_ilength_of_num_length(),
      get_theorem_by_name("INT_OF_NUM_EQ"),
      get_theorem_by_name("LENGTH_EQ_NIL"))));
  return gnode_prove(root);
}
PROOF static thm cmc_ilength_nil = cmc_ilength_eq_nil();

PROOF static thm cmc_uint8_buffer_view(const thm nonempty,
                                       const thm length_model) {
  return apply_conversion(rewrite_conv(THM_LIST(
      get_cm_uint8_buffer_def(), eqf_intro_rule(nonempty), length_model)),
      `cm_uint8_buffer (source__pre:int) (bytes:(int)list)`);
}

void cmc_copy_bytes(unsigned char *source, int length,
                    unsigned char *data, int capacity, int cursor)
    [[cst::param(`prefix:(int)list`, `bytes:(int)list`)]]
    [[cst::require(
      `fact(0i <= length) ** fact(ilength bytes == length) **
       fact(0i <= cursor) ** fact(cursor + length <= capacity) **
       fact(capacity <= 2147483647i) **
       cm_uint8_buffer source bytes **
       store_uint8_array data cursor prefix **
       store_undef_uint8_array
         (data + cursor * sizeof Tuchar) (capacity - cursor)`)]]
    [[cst::ensure(
      `cm_uint8_buffer source bytes **
       store_uint8_array data (cursor + length)
         (prefix ++ bytes) **
       store_undef_uint8_array
         (data + (cursor + length) * sizeof Tuchar)
         (capacity - (cursor + length))`)]]
{
  if (length == 0) {
    [[cst::proof]] {
      thm length_zero = trans_rule(
          assume_rule(`ilength (bytes:(int)list) == (length__pre:int)`),
          assume_rule(`(length__pre:int) == 0i`));
      thm bytes_nil = eq_mp_rule(
          spec_rule(`bytes:(int)list`, cmc_ilength_nil), length_zero);
      substitute_st(bytes_nil);
      substitute_st(assume_rule(`(length__pre:int) == 0i`));
      thm retained_nil = eq_mp_rule(
          spec_rule(`bytes:(int)list`, cmc_ilength_nil),
          assume_rule(`ilength (bytes:(int)list) == 0i`));
      add_fact_st(retained_nil);
      thm buffer_view = apply_conversion(rewrite_conv(THM_LIST(
          retained_nil)), `cm_uint8_buffer (source__pre:int) bytes`);
      apply_hconv_st(eq2ent(sym_rule(buffer_view)));
      thm destination_view = apply_conversion(rewrite_conv(THM_LIST(
          assume_rule(`(length__pre:int) == 0i`), retained_nil,
          get_theorem_by_name("APPEND_NIL"),
          get_theorem_by_name("INT_ADD_RID"))),
          `store_uint8_array (data__pre:int)
            ((cursor__pre:int) + length__pre)
            ((prefix:(int)list) ++ bytes)`);
      apply_hconv_st(eq2ent(sym_rule(destination_view)));
      thm undefined_view = apply_conversion(rewrite_conv(THM_LIST(
          assume_rule(`(length__pre:int) == 0i`),
          get_theorem_by_name("INT_ADD_RID"))),
          `store_undef_uint8_array
            ((data__pre:int) +
              ((cursor__pre:int) + length__pre) * sizeof Tuchar)
            ((capacity__pre:int) - (cursor__pre + length__pre))`);
      apply_hconv_st(eq2ent(sym_rule(undefined_view)));
    }
    return;
  };

  int index = 0;
  [[cst::proof]] {
    thm length_model = assume_rule(
        `ilength (bytes:(int)list) == (length__pre:int)`);
    thm length_nonzero = assume_rule(`~((length__pre:int) == 0i)`);
    thm ilength_nonzero = mp_rule(mp_rule(int_arith_rule(
        `ilength (bytes:(int)list) == (length__pre:int) ==>
         ~(length__pre == 0i) ==> ~(ilength bytes == 0i)`),
        length_model), length_nonzero);
    thm nil_iff = spec_rule(`bytes:(int)list`, cmc_ilength_nil);
    thm nonempty = eq_mp_rule(beta_norm(ap_term_rule(
        `\b:bool. ~b`, nil_iff)), ilength_nonzero);
    cst_set_symbolic_state(add_arith_fact_st(
        cst_get_symbolic_state(),
        "0i <= cursor__pre ==> "
        "cursor__pre + length__pre <= capacity__pre ==> "
        "capacity__pre <= 2147483647i ==> "
        "length__pre <= 2147483647i"));
    thm buffer_view = cmc_uint8_buffer_view(nonempty, length_model);
    apply_hconv_st(eq2ent(buffer_view));

    thm empty = spec_rule(`bytes:(int)list`, mk_sublist_empty());
    thm initial = by_rewrite(
        `(prefix:(int)list) ++ sublist 0i 0i bytes == prefix`,
        THM_LIST(empty, get_theorem_by_name("APPEND_NIL")));
    substitute_st(sym_rule(initial));
    add_fact_st(int_arith_rule(`0i <= 0i`));
    thm total_zero = int_arith_rule(
        `(cursor__pre:int) + 0i == cursor__pre`);
    thm destination_view = apply_conversion(
        rewrite_conv(THM_LIST(total_zero)),
        `store_uint8_array (data__pre:int)
          ((cursor__pre:int) + 0i)
          ((prefix:(int)list) ++ sublist 0i 0i bytes)`);
    apply_hconv_st(eq2ent(sym_rule(destination_view)));
    thm undefined_view = apply_conversion(
        rewrite_conv(THM_LIST(total_zero)),
        `store_undef_uint8_array
          ((data__pre:int) +
            ((cursor__pre:int) + 0i) * sizeof Tuchar)
          ((capacity__pre:int) - (cursor__pre + 0i))`);
    apply_hconv_st(eq2ent(sym_rule(undefined_view)));

    thm divide = eq2ent(mp_rule(mp_rule(mp_rule(
        spec_rule(`0i:int`, spec_rule(`bytes:(int)list`,
          spec_rule(`length__pre:int`, spec_rule(`Tuchar`,
            spec_rule(`source__pre:int`,
              get_theorem_by_name("array_at_divide")))))),
        int_arith_rule(`0i <= 0i`)),
        assume_rule(`0i <= (length__pre:int)`)), length_model));
    divide = conv_rule(rewrite_conv(THM_LIST(
        gsym_rule(get_theorem_by_name("store_uint8_array_def")))), divide);
    apply_hconv_st(divide);
  }

  while (index < length)
      [[cst::invariant(`exists iv.
          fact(0i <= iv) ** fact(iv <= length__pre) **
          fact(length__pre <= 2147483647i) **
          fact(~(length__pre == 0i)) **
          fact(ilength bytes == length__pre) **
          fact(0i <= cursor__pre) **
          fact(cursor__pre + length__pre <= capacity__pre) **
          fact(capacity__pre <= 2147483647i) **
          data_at index__addr Tint iv **
          data_at length__addr Tint length__pre **
          data_at source__addr Tptr source__pre **
          data_at data__addr Tptr data__pre **
          data_at capacity__addr Tint capacity__pre **
          data_at cursor__addr Tint cursor__pre **
          fact(~(source__pre == 0i)) **
          store_uint8_array data__pre (cursor__pre + iv)
            (prefix ++ sublist 0i iv bytes) **
          store_undef_uint8_array
            (data__pre + (cursor__pre + iv) * sizeof Tuchar)
            (capacity__pre - (cursor__pre + iv)) **
          store_uint8_array source__pre iv
            (sublist 0i iv bytes) **
          store_uint8_array
            (source__pre + iv * sizeof Tuchar)
            (length__pre - iv) (sublist iv length__pre bytes)`)]]
  {
    [[cst::proof]] {
      cst_set_symbolic_state(add_arith_fact_st(
          cst_get_symbolic_state(),
          "0i <= iv ==> iv < length__pre ==> "
          "length__pre <= 2147483647i ==> "
          "ilength (bytes:(int)list) == length__pre ==> "
          "0i <= cursor__pre ==> "
          "cursor__pre + length__pre <= capacity__pre ==> "
          "capacity__pre <= 2147483647i ==> "
          "(iv + 1i <= length__pre && 0i <= iv + 1i && "
          "iv + 1i <= 2147483647i && length__pre - iv >= 1i && "
          "iv < ilength (bytes:(int)list) && "
          "length__pre <= ilength (bytes:(int)list) && "
          "0i <= cursor__pre + iv && "
          "cursor__pre + iv < capacity__pre && "
          "capacity__pre - (cursor__pre + iv) >= 1i && "
          "cursor__pre + (iv + 1i) <= 2147483647i)"));
      thm cons_eq = sym_rule(mp_rule(mp_rule(mp_rule(
          spec_rule(`bytes:(int)list`,
            spec_rule(`length__pre:int`,
              spec_rule(`iv:int`, mk_sublist_cons()))),
          assume_rule(`0i <= (iv:int)`)),
          assume_rule(`(iv:int) < (length__pre:int)`)),
          assume_rule(
            `(length__pre:int) <= ilength (bytes:(int)list)`)));
      thm address_step = spec_rule(`Tuchar`, spec_rule(`iv:int`,
          spec_rule(`source__pre:int`, mk_addr_step())));
      thm length_step = spec_rule(`iv:int`,
          spec_rule(`length__pre:int`, mk_len_step()));
      thm split = conv_rule(rewrite_conv(THM_LIST(
          cons_eq, address_step, length_step,
          gsym_rule(get_theorem_by_name("store_uint8_array_def")))),
          spec_rule(`sublist ((iv:int) + 1i) length__pre
                       (bytes:(int)list)`,
            spec_rule(`inth (iv:int) (bytes:(int)list)`,
              spec_rule(`(length__pre:int) - iv`,
                spec_rule(`Tuchar`,
                  spec_rule(
                    `(source__pre:int) + iv * sizeof Tuchar`,
                    get_theorem_by_name("array_at_split_first")))))));
      apply_hconv_st(split);
    }
    unsigned char byte = source[index];
    [[cst::proof]] {
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          specl_rule(TERM_LIST(
            `data__pre:int`, `capacity__pre:int`,
            `(cursor__pre:int) + (iv:int)`),
            get_cm_open_uint8_fill())));
    }
    data[cursor + index] = byte;
    index = index + 1;
    [[cst::proof]] {
      thm snoc = mp_rule(mp_rule(
          spec_rule(`bytes:(int)list`,
            spec_rule(`iv:int`, mk_sublist_snoc())),
          assume_rule(`0i <= (iv:int)`)),
          assume_rule(`(iv:int) < ilength (bytes:(int)list)`));

      thm destination_close = specl_rule(TERM_LIST(
          `data__pre:int`, `(cursor__pre:int) + (iv:int)`,
          `(prefix:(int)list) ++ sublist 0i (iv:int)
             (bytes:(int)list)`,
          `inth (iv:int) (bytes:(int)list)`),
          get_cm_close_uint8_fill());
      apply_hconv_st(destination_close);
      thm assoc = ispecl_rule(TERM_LIST(
          `prefix:(int)list`,
          `sublist 0i (iv:int) (bytes:(int)list)`,
          `[inth (iv:int) (bytes:(int)list)]:(int)list`),
          get_theorem_by_name("APPEND_ASSOC"));
      thm lifted_snoc = mk_comb_rule(mk_comb_rule(refl_rule(
          `APPEND:(int)list->(int)list->(int)list`),
          refl_rule(`prefix:(int)list`)), snoc);
      thm list_step = trans_rule(sym_rule(assoc), lifted_snoc);
      thm total_step = int_arith_rule(
          `((cursor__pre:int) + (iv:int)) + 1i ==
           cursor__pre + (iv + 1i)`);
      substitute_st(total_step);
      substitute_st(list_step);

      thm source_close = specl_rule(TERM_LIST(
          `source__pre:int`, `iv:int`,
          `sublist 0i (iv:int) (bytes:(int)list)`,
          `inth (iv:int) (bytes:(int)list)`),
          get_cm_close_uint8_fill());
      source_close = conv_rule(rewrite_conv(THM_LIST(snoc)), source_close);
      apply_hconv_st(source_close);
    }
  }

  [[cst::proof]] {
    cst_set_symbolic_state(add_arith_fact_st(cst_get_symbolic_state(),
        "iv <= length__pre ==> iv >= length__pre ==> iv == length__pre"));
    thm iv_equal = assume_rule(`(iv:int) == (length__pre:int)`);
    thm length_equal = sym_rule(
        assume_rule(`ilength (bytes:(int)list) == (length__pre:int)`));
    thm full = spec_rule(`bytes:(int)list`, mk_sublist_full());
    thm list_full = apply_conversion(rewrite_conv(THM_LIST(
        iv_equal, length_equal, full)),
        `sublist 0i (iv:int) (bytes:(int)list)`);
    substitute_st(list_full);
    substitute_st(iv_equal);

    thm zero = int_arith_rule(
        `(length__pre:int) - length__pre == 0i`);
    thm empty_tail = spec_rule(
        `bytes:(int)list`, mk_sublist_self_empty());
    thm vanish = eq2ent(apply_conversion(rewrite_conv(THM_LIST(
        zero, length_equal, empty_tail)),
        `store_uint8_array
          ((source__pre:int) + length__pre * sizeof Tuchar)
          ((length__pre:int) - length__pre)
          (sublist (length__pre:int) length__pre
            (bytes:(int)list))`));
    apply_hconv_st(vanish);
    thm zero_array = eq2ent(mp_rule(mp_rule(
        spec_rule(`[]:(int)list`, spec_rule(`0i:int`,
          spec_rule(`Tuchar`, spec_rule(
            `(source__pre:int) +
              ilength (bytes:(int)list) * sizeof Tuchar`,
            get_theorem_by_name("array_at_zero"))))),
        refl_rule(`0i:int`)), refl_rule(`[]:(int)list`)));
    zero_array = conv_rule(rewrite_conv(THM_LIST(
        gsym_rule(get_theorem_by_name("store_uint8_array_def")))), zero_array);
    apply_hconv_st(zero_array);

    thm length_model = assume_rule(
        `ilength (bytes:(int)list) == (length__pre:int)`);
    thm length_nonzero = assume_rule(
        `~((length__pre:int) == 0i)`);
    thm ilength_nonzero = mp_rule(mp_rule(int_arith_rule(
        `ilength (bytes:(int)list) == (length__pre:int) ==>
         ~(length__pre == 0i) ==> ~(ilength bytes == 0i)`),
        length_model), length_nonzero);
    thm nil_iff = spec_rule(`bytes:(int)list`, cmc_ilength_nil);
    thm nonempty = eq_mp_rule(beta_norm(ap_term_rule(
        `\b:bool. ~b`, nil_iff)), ilength_nonzero);
    thm buffer_view = cmc_uint8_buffer_view(nonempty, length_model);
    apply_hconv_st(eq2ent(sym_rule(buffer_view)));
  }
}
