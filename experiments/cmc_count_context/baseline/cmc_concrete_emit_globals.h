#pragma once

#include "cmc_concrete_emit_char.h"
#include "cmc_concrete_emit_zeroes.h"
#include "cmc_concrete_layout.h"
#include "cmc_codegen.h"
#include "cmc_concrete_data_ready.h"
#require "cmc_concrete_data_ready.c"
#require "cmc_concrete_emit_char.c"
#require "cmc_concrete_emit_zeroes.c"
#require "cmc_concrete_layout.c"
#require "cmc_codegen.c"

int cmc_emit_globals(struct cm_global *node,
                      unsigned char *data, int capacity, int cursor)
    [[cst::param(`structs:(cm_struct_d)list`,
                 `globals:(cm_global_d)list`, `prefix:(int)list`)]]
    [[cst::require(
      `fact(cm_rep_globals_safe globals <=> true) **
       fact(cm_data_globals_wf structs globals <=> true) **
       fact(0i <= cursor) **
       fact(cursor + cm_rep_globals_size globals <= capacity) **
       fact(capacity <= 2147483647i) **
       cm_global_list_rep node globals **
       store_uint8_array data cursor prefix **
       store_undef_uint8_array
         (data + cursor * sizeof Tuchar) (capacity - cursor)`)]]
    [[cst::ensure(
      `fact(cm_rep_globals_safe globals <=> true) **
       fact(cm_data_globals_wf structs globals <=> true) **
       cm_global_list_rep node globals **
       store_uint8_array data
         (cursor + cm_rep_globals_size globals)
         (prefix ++ cm_globals_bytes structs globals) **
       store_undef_uint8_array
         (data + (cursor + cm_rep_globals_size globals) * sizeof Tuchar)
         (capacity - (cursor + cm_rep_globals_size globals)) **
       fact((__return:int) ==
         cursor + cm_rep_globals_size globals)`)]];
