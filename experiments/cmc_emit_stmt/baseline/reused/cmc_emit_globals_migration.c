#include "cmc_layout_migration_abi.h"

/*@ Extern Coq
    (bool :: *) (cm_type :: *) (cm_struct_d :: *) (cm_global_d :: *)
*/
/*@ Extern Coq
    (cm_type_encode : cm_type -> Z)
    (cm_global_ty : cm_global_d -> cm_type)
    (cm_global_count : cm_global_d -> Z)
    (cm_global_has_init : cm_global_d -> bool)
    (cm_global_init : cm_global_d -> Z)
    (cm_rep_bool : bool -> Z)
    (cm_rep_code_slot_size : Z -> Z -> Z)
    (cm_rep_global_size : cm_global_d -> Z)
    (cm_rep_globals_size : list cm_global_d -> Z)
    (cm_rep_globals_safe : list cm_global_d -> Prop)
    (cm_global_wf : list cm_struct_d -> cm_global_d -> Prop)
    (cm_data_globals_wf : list cm_struct_d -> list cm_global_d -> Prop)
    (cm_global_bytes : list cm_struct_d -> cm_global_d -> list Z)
    (cm_globals_bytes : list cm_struct_d -> list cm_global_d -> list Z)
    (cm_global_list_rep : Z -> list cm_global_d -> Assertion)
    (UCharArray::seg : Z -> Z -> Z -> list Z -> Assertion)
    (UCharArray::undef_seg : Z -> Z -> Z -> Assertion)
    (tower_u8 : Z -> Z) (tower_word_bytes : Z -> list Z)
    (zeros : Z -> list Z)
*/
/*@ Import Coq Require Import SimpleC.EE.QCP_demos_human.cmc_emit_globals_migration_lib */

long long cmc_code_slot_size(int code, int count)
/*@ Require emp
    Ensure __return == cm_rep_code_slot_size(code, count) && emp
*/;

void cmc_write_char(unsigned char *data, int capacity,
                    int cursor, long long char_value)
/*@ With (prefix : list Z)
    Require 0 <= cursor && cursor + 1 <= capacity &&
            capacity <= 2147483647 &&
            UCharArray::seg(data, 0, cursor, prefix) *
            UCharArray::undef_seg(data, cursor, capacity)
    Ensure UCharArray::seg(data, 0, cursor + 1,
                          app(prefix, cons(tower_u8(char_value), nil))) *
           UCharArray::undef_seg(data, cursor + 1, capacity)
*/;

void cmc_write_word(unsigned char *data, int capacity,
                    int cursor, long long word_value)
/*@ With (prefix : list Z)
    Require 0 <= cursor && cursor + 8 <= capacity &&
            capacity <= 2147483647 &&
            UCharArray::seg(data, 0, cursor, prefix) *
            UCharArray::undef_seg(data, cursor, capacity)
    Ensure UCharArray::seg(data, 0, cursor + 8,
                          app(prefix, tower_word_bytes(word_value))) *
           UCharArray::undef_seg(data, cursor + 8, capacity)
*/;

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
*/
{
  if (node == 0) {
    return cursor;
  };
  /*@ Assert exists (head : cm_global_d) (tail : list cm_global_d) (nextp : Z),
      node == node@pre && data == data@pre &&
      capacity == capacity@pre && cursor == cursor@pre && node != 0 &&
      globals == cons(head, tail) &&
      cm_rep_globals_safe(globals) && cm_data_globals_wf(structs, globals) &&
      cm_rep_globals_safe(tail) && cm_data_globals_wf(structs, tail) &&
      cm_global_wf(structs, head) &&
      0 <= cursor && capacity <= 2147483647 &&
      0 <= cm_rep_global_size(head) && cm_rep_global_size(head) <= 1048560 &&
      0 <= cm_rep_globals_size(tail) &&
      cursor + cm_rep_global_size(head) + cm_rep_globals_size(tail) <= capacity &&
      data_at(&(node->ty), int, cm_type_encode(cm_global_ty(head))) *
      data_at(&(node->count), int, cm_global_count(head)) *
      data_at(&(node->has_init), int, cm_rep_bool(cm_global_has_init(head))) *
      data_at(&(node->init), long long, cm_global_init(head)) *
      data_at(&(node->next), struct cm_global *, nextp) *
      cm_global_list_rep(nextp, tail) *
      UCharArray::seg(data, 0, cursor, prefix) *
      UCharArray::undef_seg(data, cursor, capacity)
  */
  int type_code = node->ty;
  int count = node->count;
  int has_init = node->has_init;
  long long init_value = node->init;
  struct cm_global *next = node->next;
  long long size64 = cmc_code_slot_size(type_code, count);
  int size = (int)size64;
  if (has_init) {
    if (type_code == CMC_TYPE_CHAR) {
      cmc_write_char(data, capacity, cursor, init_value)
        /*@ where prefix = prefix */;
    } else {
      cmc_write_word(data, capacity, cursor, init_value)
        /*@ where prefix = prefix */;
    }
  } else {
    cmc_write_zeroes(data, capacity, cursor, size)
      /*@ where prefix = prefix */;
  }
  /*@ Assert exists (head : cm_global_d) (tail : list cm_global_d) (nextp : Z),
      node == node@pre && data == data@pre &&
      capacity == capacity@pre && cursor == cursor@pre && node != 0 &&
      globals == cons(head, tail) &&
      cm_rep_globals_safe(globals) && cm_data_globals_wf(structs, globals) &&
      cm_rep_globals_safe(tail) && cm_data_globals_wf(structs, tail) &&
      cm_global_wf(structs, head) &&
      0 <= cursor && capacity <= 2147483647 &&
      0 <= cm_rep_global_size(head) && cm_rep_global_size(head) <= 1048560 &&
      0 <= cm_rep_globals_size(tail) &&
      cursor + cm_rep_global_size(head) + cm_rep_globals_size(tail) <= capacity &&
      type_code == cm_type_encode(cm_global_ty(head)) &&
      count == cm_global_count(head) &&
      has_init == cm_rep_bool(cm_global_has_init(head)) &&
      init_value == cm_global_init(head) && next == nextp &&
      size64 == cm_rep_global_size(head) && size == cm_rep_global_size(head) &&
      data_at(&(node->ty), int, cm_type_encode(cm_global_ty(head))) *
      data_at(&(node->count), int, cm_global_count(head)) *
      data_at(&(node->has_init), int, cm_rep_bool(cm_global_has_init(head))) *
      data_at(&(node->init), long long, cm_global_init(head)) *
      data_at(&(node->next), struct cm_global *, nextp) *
      cm_global_list_rep(nextp, tail) *
      UCharArray::seg(data, 0, cursor + size, app(prefix, cm_global_bytes(structs, head))) *
      UCharArray::undef_seg(data, cursor + size, capacity)
  */
  int final_cursor =
      cmc_emit_globals(next, data, capacity, cursor + size)
        /*@ where structs = structs */;
  return final_cursor;
}
