#pragma once

#include "cmc_concrete_emit_globals.h"
#include "cmc_concrete_emit_strings.h"
#require "cmc_concrete_emit_globals.c"
#require "cmc_concrete_emit_strings.c"

int cmc_emit_data(struct cm_global *global_node,
                  struct cm_string *string_node,
                  unsigned char *data, int capacity)
    [[cst::param(`structs:(cm_struct_d)list`,
                 `globals:(cm_global_d)list`,
                 `strings:(cm_string_d)list`)]]
    [[cst::require(
      `fact(cm_rep_globals_safe globals <=> true) **
       fact(cm_data_globals_wf structs globals <=> true) **
       fact(cm_rep_strings_safe strings <=> true) **
       fact(0i <= cm_rep_globals_size globals) **
       fact(0i <= cm_rep_strings_size strings) **
       fact((8i + cm_rep_globals_size globals) +
              cm_rep_strings_size strings <= capacity) **
       fact(capacity <= 2147483647i) **
       cm_global_list_rep global_node globals **
       cm_string_list_rep string_node strings **
       store_uint8_array data 0i ([]:(int)list) **
       store_undef_uint8_array data capacity`)]]
    [[cst::ensure(
      `fact(cm_rep_globals_safe globals <=> true) **
       fact(cm_data_globals_wf structs globals <=> true) **
       fact(cm_rep_strings_safe strings <=> true) **
       fact(0i <= cm_rep_globals_size globals) **
       fact(0i <= cm_rep_strings_size strings) **
       fact((8i + cm_rep_globals_size globals) +
              cm_rep_strings_size strings <= capacity) **
       fact(capacity <= 2147483647i) **
       cm_global_list_rep global_node globals **
       cm_string_list_rep string_node strings **
       store_uint8_array data
         ((8i + cm_rep_globals_size globals) +
            cm_rep_strings_size strings)
         ((ireplicate 8i 0i ++ cm_globals_bytes structs globals) ++
            cm_strings_bytes strings) **
       store_undef_uint8_array
         (data + ((8i + cm_rep_globals_size globals) +
                    cm_rep_strings_size strings) * sizeof Tuchar)
         (capacity - ((8i + cm_rep_globals_size globals) +
                        cm_rep_strings_size strings)) **
       fact((__return:int) ==
         (8i + cm_rep_globals_size globals) +
           cm_rep_strings_size strings)`)]];
