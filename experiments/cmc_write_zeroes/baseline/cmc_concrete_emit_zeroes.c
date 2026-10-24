#include "cmc_concrete_emit_zeroes.h"
#include "userlib/pure_lists.h"
#include "userlib/proof.h"
#include "userlib/operational.h"
#require "cmc_concrete_emit_bytes.c"
#require "userlib/pure_lists.c"

void cmc_write_zeroes(unsigned char *data, int capacity,
                      int cursor, int count)
    [[cst::param(`prefix:(int)list`)]]
    [[cst::require(
      `fact(0i <= cursor) ** fact(0i <= count) **
       fact(cursor + count <= capacity) **
       fact(capacity <= 2147483647i) **
       store_uint8_array data cursor prefix **
       store_undef_uint8_array
         (data + cursor * sizeof Tuchar) (capacity - cursor)`)]]
    [[cst::ensure(
      `store_uint8_array data (cursor + count)
         (prefix ++ ireplicate count 0i) **
       store_undef_uint8_array
         (data + (cursor + count) * sizeof Tuchar)
         (capacity - (cursor + count))`)]]
{
  int index = 0;
  [[cst::proof]] {
    thm empty = ispec_rule(`0i:int`, mk_ireplicate_empty());
    thm initial = by_rewrite(
        `(prefix:(int)list) ++ ireplicate 0i 0i == prefix`,
        THM_LIST(empty, get_theorem_by_name("APPEND_NIL")));
    substitute_st(sym_rule(initial));
    add_fact_st(int_arith_rule(`0i <= 0i`));
    thm total_zero = int_arith_rule(
        `(cursor__pre:int) + 0i == cursor__pre`);
    thm prefix_view = apply_conversion(
        rewrite_conv(THM_LIST(total_zero)),
        `store_uint8_array (data__pre:int)
          ((cursor__pre:int) + 0i)
          ((prefix:(int)list) ++ ireplicate 0i 0i)`);
    apply_hconv_st(eq2ent(sym_rule(prefix_view)));
    thm suffix_view = apply_conversion(
        rewrite_conv(THM_LIST(total_zero)),
        `store_undef_uint8_array
          ((data__pre:int) +
            ((cursor__pre:int) + 0i) * sizeof Tuchar)
          ((capacity__pre:int) - (cursor__pre + 0i))`);
    apply_hconv_st(eq2ent(sym_rule(suffix_view)));
  }
  while (index != count)
      [[cst::invariant(`exists iv.
          fact(0i <= iv) ** fact(iv <= count__pre) **
          fact(0i <= cursor__pre) ** fact(0i <= count__pre) **
          fact(cursor__pre + count__pre <= capacity__pre) **
          fact(capacity__pre <= 2147483647i) **
          data_at index__addr Tint iv **
          data_at count__addr Tint count__pre **
          data_at cursor__addr Tint cursor__pre **
          data_at capacity__addr Tint capacity__pre **
          data_at data__addr Tptr data__pre **
          store_uint8_array data__pre (cursor__pre + iv)
            (prefix ++ ireplicate iv 0i) **
          store_undef_uint8_array
            (data__pre + (cursor__pre + iv) * sizeof Tuchar)
            (capacity__pre - (cursor__pre + iv))`)]]
  {
    [[cst::proof]] {
      cst_set_symbolic_state(add_arith_fact_st(
          cst_get_symbolic_state(),
          "0i <= iv ==> iv <= count__pre ==> "
          "~(iv == count__pre) ==> "
          "0i <= cursor__pre ==> "
          "cursor__pre + count__pre <= capacity__pre ==> "
          "capacity__pre <= 2147483647i ==> "
          "(iv < count__pre && 0i <= iv + 1i &&"
          " iv + 1i <= count__pre &&"
          " 0i <= cursor__pre + iv &&"
          " cursor__pre + iv < capacity__pre &&"
          " capacity__pre - (cursor__pre + iv) >= 1i &&"
          " cursor__pre + (iv + 1i) <= 2147483647i)"));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          specl_rule(TERM_LIST(
            `data__pre:int`, `capacity__pre:int`,
            `(cursor__pre:int) + (iv:int)`),
            get_cm_open_uint8_fill())));
    }
    data[cursor + index] = 0;
    [[cst::proof]] {
      thm snoc = sym_rule(mp_rule(
          ispec_rule(`0i:int`,
              spec_rule(`iv:int`, mk_ireplicate_snoc())),
          assume_rule(`0i <= (iv:int)`)));
      thm closed = specl_rule(TERM_LIST(
          `data__pre:int`, `(cursor__pre:int) + (iv:int)`,
          `(prefix:(int)list) ++ ireplicate (iv:int) 0i`, `0i:int`),
          get_cm_close_uint8_fill());
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(), closed));

      thm assoc = ispecl_rule(TERM_LIST(
          `prefix:(int)list`, `ireplicate (iv:int) 0i`,
          `[0i]:(int)list`), get_theorem_by_name("APPEND_ASSOC"));
      thm lifted_snoc = mk_comb_rule(mk_comb_rule(refl_rule(
          `APPEND:(int)list->(int)list->(int)list`),
          refl_rule(`prefix:(int)list`)), snoc);
      thm list_step = trans_rule(sym_rule(assoc), lifted_snoc);
      thm total_step = int_arith_rule(
          `((cursor__pre:int) + (iv:int)) + 1i ==
           cursor__pre + (iv + 1i)`);
      thm prefix_view = apply_conversion(
          rewrite_conv(THM_LIST(
            sym_rule(total_step), sym_rule(list_step))),
          `store_uint8_array (data__pre:int)
            ((cursor__pre:int) + ((iv:int) + 1i))
            ((prefix:(int)list) ++ ireplicate (iv + 1i) 0i)`);
      apply_hconv_st(eq2ent(sym_rule(prefix_view)));
      thm suffix_view = apply_conversion(
          rewrite_conv(THM_LIST(sym_rule(total_step))),
          `store_undef_uint8_array
            ((data__pre:int) +
              ((cursor__pre:int) + ((iv:int) + 1i)) * sizeof Tuchar)
            ((capacity__pre:int) - (cursor__pre + (iv + 1i)))`);
      apply_hconv_st(eq2ent(sym_rule(suffix_view)));
    }
    index = index + 1;
  }
  [[cst::proof]] {
    substitute_st(assume_rule(`(iv:int) == (count__pre:int)`));
  }
}
