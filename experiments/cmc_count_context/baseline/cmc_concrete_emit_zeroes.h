#pragma once

#include "cmc_concrete_emit_bytes.h"
#require "cmc_concrete_emit_bytes.c"

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
         (capacity - (cursor + count))`)]];
