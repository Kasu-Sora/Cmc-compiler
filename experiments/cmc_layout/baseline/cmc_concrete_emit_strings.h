#pragma once

#include "cmc_concrete_copy_bytes.h"
#include "cmc_codegen.h"
#require "cmc_codegen.c"
#require "cmc_concrete_copy_bytes.c"

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
         cursor + cm_rep_strings_size strings)`)]];
