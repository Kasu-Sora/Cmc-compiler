#include "cmc_layout_migration_abi.h"

/*@ Extern Coq (cm_struct_d :: *) (cm_global_d :: *) (cm_string_d :: *) */
/*@ Extern Coq
    (cm_rep_globals_size : list cm_global_d -> Z)
    (cm_rep_globals_safe : list cm_global_d -> Prop)
    (cm_data_globals_wf : list cm_struct_d -> list cm_global_d -> Prop)
    (cm_globals_bytes : list cm_struct_d -> list cm_global_d -> list Z)
    (cm_global_list_rep : Z -> list cm_global_d -> Assertion)
    (cm_rep_strings_size : list cm_string_d -> Z)
    (cm_rep_strings_safe : list cm_string_d -> Prop)
    (cm_strings_bytes : list cm_string_d -> list Z)
    (cm_string_list_rep : Z -> list cm_string_d -> Assertion)
    (UCharArray::seg : Z -> Z -> Z -> list Z -> Assertion)
    (UCharArray::undef_seg : Z -> Z -> Z -> Assertion)
    (zeros : Z -> list Z)
*/
/*@ Import Coq Require Import SimpleC.EE.QCP_demos_human.cmc_emit_data_migration_lib */

void cmc_write_zeroes(unsigned char *data, int capacity,
                      int cursor, int count)
/*@ With (prefix : list Z)
    Require 0 <= cursor && 0 <= count &&
            cursor + count <= capacity && capacity <= 2147483647 &&
            UCharArray::seg(data, 0, cursor, prefix) *
            UCharArray::undef_seg(data, cursor, capacity)
    Ensure UCharArray::seg(data, 0, cursor + count,
                          app(prefix, zeros(count))) *
           UCharArray::undef_seg(data, cursor + count, capacity)
*/;

int cmc_emit_globals(struct cm_global *node,
                      unsigned char *data, int capacity, int cursor)
/*@ With (structs : list cm_struct_d) (globals : list cm_global_d) (prefix : list Z)
    Require cm_rep_globals_safe(globals) && cm_data_globals_wf(structs, globals) &&
            0 <= cursor && cursor + cm_rep_globals_size(globals) <= capacity &&
            capacity <= 2147483647 &&
            cm_global_list_rep(node, globals) *
            UCharArray::seg(data, 0, cursor, prefix) *
            UCharArray::undef_seg(data, cursor, capacity)
    Ensure cm_rep_globals_safe(globals) && cm_data_globals_wf(structs, globals) &&
           __return == cursor + cm_rep_globals_size(globals) &&
           cm_global_list_rep(node, globals) *
           UCharArray::seg(data, 0, cursor + cm_rep_globals_size(globals),
                          app(prefix, cm_globals_bytes(structs, globals))) *
           UCharArray::undef_seg(data, cursor + cm_rep_globals_size(globals), capacity)
*/;

int cmc_emit_strings(struct cm_string *node,
                      unsigned char *data, int capacity, int cursor)
/*@ With (strings : list cm_string_d) (prefix : list Z)
    Require cm_rep_strings_safe(strings) &&
            0 <= cursor && cursor + cm_rep_strings_size(strings) <= capacity &&
            capacity <= 2147483647 &&
            cm_string_list_rep(node, strings) *
            UCharArray::seg(data, 0, cursor, prefix) *
            UCharArray::undef_seg(data, cursor, capacity)
    Ensure cm_rep_strings_safe(strings) &&
           __return == cursor + cm_rep_strings_size(strings) &&
           cm_string_list_rep(node, strings) *
           UCharArray::seg(data, 0, cursor + cm_rep_strings_size(strings),
                          app(prefix, cm_strings_bytes(strings))) *
           UCharArray::undef_seg(data, cursor + cm_rep_strings_size(strings), capacity)
*/;

int cmc_emit_data(struct cm_global *global_node,
                  struct cm_string *string_node,
                  unsigned char *data, int capacity)
/*@ With (structs : list cm_struct_d) (globals : list cm_global_d)
         (strings : list cm_string_d)
    Require cm_rep_globals_safe(globals) && cm_data_globals_wf(structs, globals) &&
            cm_rep_strings_safe(strings) &&
            0 <= cm_rep_globals_size(globals) && 0 <= cm_rep_strings_size(strings) &&
            (8 + cm_rep_globals_size(globals)) + cm_rep_strings_size(strings) <= capacity &&
            capacity <= 2147483647 &&
            cm_global_list_rep(global_node, globals) *
            cm_string_list_rep(string_node, strings) *
            UCharArray::seg(data, 0, 0, nil) *
            UCharArray::undef_seg(data, 0, capacity)
    Ensure cm_rep_globals_safe(globals) && cm_data_globals_wf(structs, globals) &&
           cm_rep_strings_safe(strings) &&
           0 <= cm_rep_globals_size(globals) && 0 <= cm_rep_strings_size(strings) &&
           (8 + cm_rep_globals_size(globals)) + cm_rep_strings_size(strings) <= capacity &&
           capacity <= 2147483647 &&
           __return == (8 + cm_rep_globals_size(globals)) + cm_rep_strings_size(strings) &&
           cm_global_list_rep(global_node, globals) *
           cm_string_list_rep(string_node, strings) *
           UCharArray::seg(data, 0,
             (8 + cm_rep_globals_size(globals)) + cm_rep_strings_size(strings),
             app(app(zeros(8), cm_globals_bytes(structs, globals)), cm_strings_bytes(strings))) *
           UCharArray::undef_seg(data,
             (8 + cm_rep_globals_size(globals)) + cm_rep_strings_size(strings), capacity)
*/
{
  cmc_write_zeroes(data, capacity, 0, 8)
    /*@ where prefix = nil */;
  /*@ Assert
      global_node == global_node@pre && string_node == string_node@pre &&
      data == data@pre && capacity == capacity@pre &&
      cm_rep_globals_safe(globals) && cm_data_globals_wf(structs, globals) &&
      cm_rep_strings_safe(strings) &&
      0 <= cm_rep_globals_size(globals) && 0 <= cm_rep_strings_size(strings) &&
      (8 + cm_rep_globals_size(globals)) + cm_rep_strings_size(strings) <= capacity &&
      capacity <= 2147483647 &&
      cm_global_list_rep(global_node, globals) *
      cm_string_list_rep(string_node, strings) *
      UCharArray::seg(data, 0, 8, zeros(8)) *
      UCharArray::undef_seg(data, 8, capacity)
  */
  int globals_cursor =
      cmc_emit_globals(global_node, data, capacity, 8)
        /*@ where structs = structs, globals = globals */;
  int final_cursor =
      cmc_emit_strings(string_node, data, capacity, globals_cursor)
        /*@ where strings = strings */;
  return final_cursor;
}
