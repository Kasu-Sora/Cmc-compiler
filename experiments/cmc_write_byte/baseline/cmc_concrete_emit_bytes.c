#include "cmc_concrete_emit_bytes.h"
#include "userlib/pure_lists.h"
#include "userlib/proof.h"
#include "userlib/operational.h"
#require "cmc_concrete_defs.c"
#require "userlib/pure_lists.c"

PROOF int _e_cmc_ireplicate =
    cst_add_const_to_header(`ireplicate:int->int->(int)list`);

void cmc_write_byte(unsigned char *data, int capacity, int cursor,
                    unsigned char byte)
    [[cst::param(`prefix:(int)list`, `model_byte:int`)]]
    [[cst::require(
      `fact(0i <= cursor) ** fact(cursor < capacity) **
       fact(byte == model_byte) **
       fact(tower_byte_value model_byte <=> true) **
       store_uint8_array data cursor prefix **
       store_undef_uint8_array
         (data + cursor * sizeof Tuchar) (capacity - cursor)`)]]
    [[cst::ensure(
      `store_uint8_array data (cursor + 1i)
         (prefix ++ [model_byte]) **
       store_undef_uint8_array
         (data + (cursor + 1i) * sizeof Tuchar)
         (capacity - (cursor + 1i))`)]]
{
  [[cst::proof]] {
    cst_set_symbolic_state(add_arith_fact_st(
        cst_get_symbolic_state(),
        "cursor__pre < capacity__pre ==>"
        " capacity__pre - cursor__pre >= 1i"));
    cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
        specl_rule(TERM_LIST(
          `data__pre:int`, `capacity__pre:int`, `cursor__pre:int`),
          get_cm_open_uint8_fill())));
  }
  data[cursor] = byte;
  [[cst::proof]] {
    substitute_st(assume_rule(
        `(byte__pre:int) == (model_byte:int)`));
    cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
        specl_rule(TERM_LIST(
          `data__pre:int`, `cursor__pre:int`,
          `prefix:(int)list`, `model_byte:int`),
          get_cm_close_uint8_fill())));
  }
}
