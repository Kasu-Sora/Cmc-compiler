#pragma once

#include "cmc_concrete_emit_bytes.h"
#require "cmc_concrete_emit_bytes.c"
PROOF extern thm cmc_unsigned_byte0_bridge;


void cmc_write_word(unsigned char *data, int capacity,
                    int cursor, long long word_value)
    [[cst::param(`prefix:(int)list`)]]
    [[cst::require(
      `fact(0i <= cursor) ** fact(cursor + 8i <= capacity) **
       fact(capacity <= 2147483647i) **
       store_uint8_array data cursor prefix **
       store_undef_uint8_array
         (data + cursor * sizeof Tuchar) (capacity - cursor)`)]]
    [[cst::ensure(
      `store_uint8_array data (cursor + 8i)
         (prefix ++ tower_word_bytes word_value) **
       store_undef_uint8_array
         (data + (cursor + 8i) * sizeof Tuchar)
         (capacity - (cursor + 8i))`)]];
