#include "cmc_concrete_emit_data.h"
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
           cm_rep_strings_size strings)`)]]
{
  [[cst::proof]] {
    cst_set_symbolic_state(add_arith_fact_st(
        cst_get_symbolic_state(),
        "0i <= cm_rep_globals_size (globals:(cm_global_d)list) ==> "
        "0i <= cm_rep_strings_size (strings:(cm_string_d)list) ==> "
        "(8i + cm_rep_globals_size globals) + "
        "  cm_rep_strings_size strings <= capacity__pre ==> "
        "capacity__pre <= 2147483647i ==> "
        "(0i <= 0i && 0i <= 8i && 8i <= capacity__pre && "
        " 0i <= 8i && "
        " 8i + cm_rep_globals_size globals <= capacity__pre && "
        " 8i <= 2147483647i)"));
    thm undefined_view = apply_conversion(rewrite_conv(THM_LIST(
        get_theorem_by_name("INT_MUL_LZERO"),
        get_theorem_by_name("INT_ADD_RID"),
        get_theorem_by_name("INT_SUB_RZERO"))),
        `store_undef_uint8_array
          ((data__pre:int) + 0i * sizeof Tuchar)
          ((capacity__pre:int) - 0i)`);
    apply_hconv_st(eq2ent(sym_rule(undefined_view)));
  }
  [[cst::where(`prefix`, `[]:(int)list`)]]
  cmc_write_zeroes(data, capacity, 0, 8);
  [[cst::proof]] {
    rewrite_st(THM_LIST(get_theorem_by_name("APPEND"),
        get_theorem_by_name("INT_ADD_LID")));
  }

  [[cst::where(`structs`, `structs:(cm_struct_d)list`)]]
  [[cst::where(`globals`, `globals:(cm_global_d)list`)]]
  [[cst::where(`prefix`, `ireplicate 8i 0i`)]]
  int globals_cursor =
      cmc_emit_globals(global_node, data, capacity, 8);
  [[cst::proof]] {
    thm cursor_model = assume_rule(
        `retval == 8i + cm_rep_globals_size
          (globals:(cm_global_d)list)`);
    cst_set_symbolic_state(retarget_cell_st(
        cst_get_symbolic_state(), `globals_cursor__addr:addr`,
        `retval:int`,
        `8i + cm_rep_globals_size (globals:(cm_global_d)list)`));
    cst_set_symbolic_state(add_arith_fact_st(
        cst_get_symbolic_state(),
        "0i <= cm_rep_globals_size (globals:(cm_global_d)list) ==> "
        "0i <= cm_rep_strings_size (strings:(cm_string_d)list) ==> "
        "(8i + cm_rep_globals_size globals) + "
        "  cm_rep_strings_size strings <= capacity__pre ==> "
        "(0i <= 8i + cm_rep_globals_size globals && "
        " (8i + cm_rep_globals_size globals) + "
        "   cm_rep_strings_size strings <= capacity__pre)"));
  }

  [[cst::where(`strings`, `strings:(cm_string_d)list`)]]
  [[cst::where(`prefix`,
      `ireplicate 8i 0i ++
       cm_globals_bytes (structs:(cm_struct_d)list)
         (globals:(cm_global_d)list)`)]]
  int final_cursor =
      cmc_emit_strings(string_node, data, capacity, globals_cursor);
  [[cst::proof]] {
    thm final_model = assume_rule(
        `retval_1 ==
         (8i + cm_rep_globals_size (globals:(cm_global_d)list)) +
           cm_rep_strings_size (strings:(cm_string_d)list)`);
    cst_set_symbolic_state(retarget_cell_st(
        cst_get_symbolic_state(), `final_cursor__addr:addr`,
        `retval_1:int`,
        `(8i + cm_rep_globals_size (globals:(cm_global_d)list)) +
           cm_rep_strings_size (strings:(cm_string_d)list)`));
  }
  return final_cursor;
}
