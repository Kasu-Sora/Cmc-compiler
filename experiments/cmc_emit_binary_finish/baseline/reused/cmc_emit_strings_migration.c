#include "cmc_layout_migration_abi.h"

/*@ Extern Coq (cm_string_d :: *) */
/*@ Extern Coq
    (cm_string_bytes : cm_string_d -> list Z)
    (cm_rep_string_length : cm_string_d -> Z)
    (cm_rep_strings_size : list cm_string_d -> Z)
    (cm_rep_strings_safe : list cm_string_d -> Prop)
    (cm_strings_bytes : list cm_string_d -> list Z)
    (cm_string_list_rep : Z -> list cm_string_d -> Assertion)
    (cmc_uint8_buffer_nonnull : Z -> list Z -> Prop)
    (UCharArray::full : Z -> Z -> list Z -> Assertion)
    (UCharArray::seg : Z -> Z -> Z -> list Z -> Assertion)
    (UCharArray::undef_seg : Z -> Z -> Z -> Assertion)
*/
/*@ Import Coq Require Import SimpleC.EE.QCP_demos_human.cmc_emit_strings_migration_lib */

void cmc_copy_bytes(unsigned char *source, int length,
                    unsigned char *data, int capacity, int cursor)
/*@ With (prefix : list Z) (bytes : list Z)
    Require 0 <= length && Zlength(bytes) == length &&
            0 <= cursor && cursor + length <= capacity &&
            capacity <= 2147483647 &&
            cmc_uint8_buffer_nonnull(source, bytes) &&
            UCharArray::full(source, length, bytes) *
            UCharArray::seg(data, 0, cursor, prefix) *
            UCharArray::undef_seg(data, cursor, capacity)
    Ensure cmc_uint8_buffer_nonnull(source, bytes) &&
           UCharArray::full(source, length, bytes) *
           UCharArray::seg(data, 0, cursor + length, app(prefix, bytes)) *
           UCharArray::undef_seg(data, cursor + length, capacity)
*/;

void cmc_write_byte(unsigned char *data, int capacity, int cursor,
                    unsigned char byte)
/*@ With (prefix : list Z) (model_byte : Z)
    Require 0 <= cursor && cursor < capacity &&
            byte == model_byte && 0 <= model_byte && model_byte < 256 &&
            UCharArray::seg(data, 0, cursor, prefix) *
            UCharArray::undef_seg(data, cursor, capacity)
    Ensure UCharArray::seg(data, 0, cursor + 1,
                          app(prefix, cons(model_byte, nil))) *
           UCharArray::undef_seg(data, cursor + 1, capacity)
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
*/
{
  if (node == 0) {
    return cursor;
  };
  /*@ Assert exists (head : cm_string_d) (tail : list cm_string_d)
                    (sourcep : Z) (nextp : Z),
      node == node@pre && data == data@pre &&
      capacity == capacity@pre && cursor == cursor@pre && node != 0 &&
      strings == cons(head, tail) &&
      cm_rep_strings_safe(strings) && cm_rep_strings_safe(tail) &&
      0 <= cursor && capacity <= 2147483647 &&
      0 <= cm_rep_string_length(head) &&
      cm_rep_string_length(head) == Zlength(cm_string_bytes(head)) &&
      0 <= cm_rep_strings_size(tail) &&
      cursor + cm_rep_string_length(head) + 1 + cm_rep_strings_size(tail) <= capacity &&
      cmc_uint8_buffer_nonnull(sourcep, cm_string_bytes(head)) &&
      data_at(&(node->bytes), unsigned char *, sourcep) *
      data_at(&(node->length), int, cm_rep_string_length(head)) *
      data_at(&(node->next), struct cm_string *, nextp) *
      UCharArray::full(sourcep, cm_rep_string_length(head), cm_string_bytes(head)) *
      cm_string_list_rep(nextp, tail) *
      UCharArray::seg(data, 0, cursor, prefix) *
      UCharArray::undef_seg(data, cursor, capacity)
  */
  unsigned char *source = node->bytes;
  int length = node->length;
  struct cm_string *next = node->next;
  cmc_copy_bytes(source, length, data, capacity, cursor)
    /*@ where prefix = prefix */;
  cmc_write_byte(data, capacity,
      cursor + length, (unsigned char)0)
    /*@ where model_byte = 0 */;
  int final_cursor = cmc_emit_strings(next, data, capacity,
      cursor + length + 1);
  return final_cursor;
}
