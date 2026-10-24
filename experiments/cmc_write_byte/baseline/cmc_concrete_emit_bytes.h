#pragma once

#include "cmc_concrete_defs.h"

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
         (capacity - (cursor + 1i))`)]];
