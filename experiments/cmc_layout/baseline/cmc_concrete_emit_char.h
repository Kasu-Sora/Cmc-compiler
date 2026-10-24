#pragma once

#include "cmc_concrete_emit_word.h"
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
         (capacity - (cursor + 1i))`)]];
