#pragma once

#include "cmc_concrete_emit_bytes.h"
#require "cmc_concrete_emit_bytes.c"

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
         (capacity - (cursor + length))`)]];
