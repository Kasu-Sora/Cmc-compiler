#include "cmc_concrete_emit_char.h"
#include "userlib/proof.h"
#include "userlib/operational.h"
#require "cmc_concrete_emit_word.c"

void cmc_write_char(unsigned char *data, int capacity,
                    int cursor, long long char_value)
    [[cst::param(`prefix:(int)list`)]]
    [[cst::require(
      `fact(0i <= cursor) ** fact(cursor + 1i <= capacity) **
       fact(capacity <= 2147483647i) **
       store_uint8_array data cursor prefix **
       store_undef_uint8_array
         (data + cursor * sizeof Tuchar) (capacity - cursor)`)]]
    [[cst::ensure(
      `store_uint8_array data (cursor + 1i)
         (prefix ++ [tower_u8 char_value]) **
       store_undef_uint8_array
         (data + (cursor + 1i) * sizeof Tuchar)
         (capacity - (cursor + 1i))`)]]
{
  unsigned long long bits = (unsigned long long)char_value;
  unsigned char byte = (unsigned char)(bits % 256ULL);
  [[cst::proof]] {
    thm concrete = spec_rule(`char_value__pre:int`,
        cmc_unsigned_byte0_bridge);
    thm model = apply_conversion(reduce_rewrite_conv(THM_LIST(
        get_tower_encode_byte_def())),
        `tower_encode_byte (char_value__pre:int) 0i`);
    add_fact_st(trans_rule(concrete, model));
    add_fact_st(eqt_intro_rule(spec_rule(`char_value__pre:int`,
        get_tower_u8_range())));
  }
  [[cst::where(`prefix`, `prefix:(int)list`)]]
  [[cst::where(`model_byte`,
      `tower_u8 (char_value__pre:int)`)]]
  cmc_write_byte(data, capacity, cursor, byte);
}
