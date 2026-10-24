#include "cmc_layout_migration_abi.h"

/*@ Extern Coq
    (bool :: *)
    (cm_type :: *)
    (cm_expr :: *)
    (cm_stmt :: *)
    (cm_slot_d :: *)
    (cm_struct_d :: *)
    (cm_global_d :: *)
    (cm_string_d :: *)
    (cm_function_d :: *)
    (cm_program :: *)
    (cm_tpair :: *)
    (cm_apair :: *)
    (cm_lookup_policy :: *)
*/
/*@ Extern Coq
    (cm_type_encode : cm_type -> Z)
    (cm_rep_is_pointer_code : Z -> Z)
    (cm_rep_leaf_size : Z -> Z)
    (cm_rep_nonzero : Z -> Z)
    (cm_normalize_code_value : Z -> Z)
    (cm_rep_expr_kind : cm_expr -> Z)
    (cm_rep_expr_op : cm_expr -> Z)
    (cm_rep_expr_value : cm_expr -> Z)
    (cm_rep_stmt_kind : cm_stmt -> Z)
    (cm_rep_stmt_slot : cm_stmt -> Z)
    (cm_imax : Z -> Z -> Z)
    (cm_rep_code_slot_size : Z -> Z -> Z)
    (cm_slot_ty : cm_slot_d -> cm_type)
    (cm_slot_count : cm_slot_d -> Z)
    (cm_struct_members : cm_struct_d -> list cm_slot_d)
    (cm_global_ty : cm_global_d -> cm_type)
    (cm_global_count : cm_global_d -> Z)
    (cm_global_has_init : cm_global_d -> bool)
    (cm_global_init : cm_global_d -> Z)
    (cm_rep_bool : bool -> Z)
    (cm_string_bytes : cm_string_d -> list Z)
    (cm_rep_string_length : cm_string_d -> Z)
    (cm_rep_string_size : cm_string_d -> Z)
    (cm_expr_type : cm_expr -> cm_type)
    (cm_member_list_rep : Z -> list cm_slot_d -> Assertion)
    (cm_rep_members_safe : list cm_slot_d -> Prop)
    (cm_rep_members_size : list cm_slot_d -> Z)
    (cm_struct_list_rep : Z -> list cm_struct_d -> Assertion)
    (cm_rep_structs_safe : list cm_struct_d -> Prop)
    (cm_rep_struct_size : list cm_struct_d -> Z -> Z)
    (cm_global_list_rep : Z -> list cm_global_d -> Assertion)
    (cm_rep_global_array : list cm_global_d -> Z -> Z)
    (cm_slot_list_rep : Z -> list cm_slot_d -> Assertion)
    (cm_rep_member_array : list cm_slot_d -> Z -> Z)
    (cm_rep_slot_type : list cm_slot_d -> Z -> Z)
    (cm_rep_type_size : list cm_struct_d -> Z -> Z)
    (cm_rep_member_prefix : list cm_slot_d -> Z -> Z)
    (cm_rep_struct_member_prefix : list cm_struct_d -> Z -> Z -> Z)
    (cm_rep_struct_member_array : list cm_struct_d -> Z -> Z -> Z)
    (cm_rep_globals_safe : list cm_global_d -> Prop)
    (cm_rep_globals_size : list cm_global_d -> Z)
    (cm_rep_globals_prefix : list cm_global_d -> Z -> Z)
    (cm_string_list_rep : Z -> list cm_string_d -> Assertion)
    (cm_rep_strings_safe : list cm_string_d -> Prop)
    (cm_rep_strings_size : list cm_string_d -> Z)
    (cm_rep_strings_prefix : list cm_string_d -> Z -> Z)
    (cm_rep_global_address : list cm_global_d -> Z -> Z)
    (cm_rep_string_address : list cm_global_d -> list cm_string_d -> Z -> Z)
    (cm_program_globals : cm_program -> list cm_global_d)
    (cm_program_structs : cm_program -> list cm_struct_d)
    (cm_program_functions : cm_program -> list cm_function_d)
    (cm_function_locals : cm_function_d -> list cm_slot_d)
    (cm_function_at : cm_lookup_policy -> Z -> list cm_function_d -> cm_function_d)
    (cm_binding_valid : cm_program -> cm_function_d -> Z -> Z -> Prop)
    (cm_binding_array_code : cm_lookup_policy -> cm_program -> Z -> Z -> Z -> Z)
    (cm_member_valid : cm_program -> cm_type -> Z -> Prop)
    (cm_member_array_code : cm_program -> cm_type -> Z -> Z)
    (cm_type_code_wf : cm_type -> Prop)
    (cm_rep_args_safe : list cm_expr -> Prop)
    (cm_rep_args_temps_safe : list cm_expr -> Prop)
    (cm_rep_args_length : list cm_expr -> Z)
    (cm_rep_expr_temps_safe : cm_expr -> Prop)
    (cm_rep_stmt_temps_safe : cm_stmt -> Prop)
    (cm_expr_rep : Z -> cm_expr -> Assertion)
    (cm_arg_list_rep : Z -> list cm_expr -> Assertion)
    (cm_stmt_rep : Z -> cm_stmt -> Assertion)
    (cm_expr_payload : cm_expr -> Z -> Z -> Z -> Assertion)
    (cm_stmt_payload : cm_stmt -> Z -> Z -> Z -> Assertion)
    (cm_expr_tpair : cm_expr -> cm_tpair)
    (cm_args_apair : list cm_expr -> cm_apair)
    (cm_tleft : cm_tpair -> Z)
    (cm_tright : cm_tpair -> Z)
    (cm_acount : cm_apair -> Z)
    (cm_adepth : cm_apair -> Z)
    (cm_stemps : cm_stmt -> Z)
    (cm_uint8_buffer : Z -> list Z -> Assertion)
*/
/*@ Extern Coq
    (CMAssignE : cm_expr -> cm_expr -> cm_type -> cm_expr)
    (CMBinaryE : Z -> cm_expr -> cm_expr -> cm_type -> cm_expr)
    (CMUnaryE : Z -> cm_expr -> cm_type -> cm_expr)
    (CMIndexE : cm_expr -> cm_expr -> cm_type -> cm_expr)
    (CMMemberE : cm_expr -> Z -> cm_type -> cm_expr)
    (CMCallE : Z -> list cm_expr -> cm_type -> cm_expr)
    (CMPutcE : cm_expr -> cm_type -> cm_expr)
    (CMPutiE : cm_expr -> cm_type -> cm_expr)
    (CMExitE : cm_expr -> cm_type -> cm_expr)
    (CMExprS : cm_expr -> cm_stmt)
    (CMInitS : Z -> cm_expr -> cm_stmt)
    (CMReturnS : cm_expr -> cm_stmt)
    (CMSeqS : cm_stmt -> cm_stmt -> cm_stmt)
    (CMBlockS : cm_stmt -> cm_stmt)
    (CMIfS : cm_expr -> cm_stmt -> cm_stmt -> cm_stmt)
    (CMWhileS : cm_expr -> cm_stmt -> cm_stmt)
*/
/*@ Import Coq Require Import SimpleC.EE.QCP_demos_human.cmc_layout_migration_lib */


static int cm_max(int a, int b)
/*@ Require emp
    Ensure __return == cm_imax(a, b) && emp
*/
{
  int result;
  if (a <= b) {
    result = b;
  } else {
    result = a;
  }
  return result;
}

int cmc_is_pointer(int ty)
/*@ Require emp
    Ensure __return == cm_rep_is_pointer_code(ty) && emp
*/
{
  int result;
  if (ty >= 1024) {
    result = 1;
  } else {
    result = 0;
  }
  return result;
}

void cmc_is_pointer_value(int ty, int *pointer)
/*@ Require undef_data_at(pointer, int)
    Ensure data_at(pointer, int, cm_rep_is_pointer_code(ty))
*/
{
  int result = cmc_is_pointer(ty);
  *pointer = result;
}

int cmc_pointee(int ty)
/*@ Require 1024 <= ty && ty <= 2147483647 && emp
    Ensure __return == ty - 1024 && emp
*/
{
  return ty - 1024;
}

static int cmc_leaf_size(int ty)
/*@ Require emp
    Ensure __return == cm_rep_leaf_size(ty) && emp
*/
{
  int result;
  if (ty >= 1024) {
    result = 8;
  } else if (ty == CMC_TYPE_INT) {
    result = 8;
  } else if (ty == CMC_TYPE_CHAR) {
    result = 1;
  } else {
    result = 0;
  }
  return result;
}

long long cmc_code_slot_size(int code, int count)
/*@ Require emp
    Ensure __return == cm_rep_code_slot_size(code, count) && emp
*/
{
  int leaf = cmc_leaf_size(code);
  long long result;
  if (count == 0) {
    result = leaf;
  } else {
    result = (long long)count * leaf;
  }
  return result;
}

static long long cmc_members_size(struct cm_member *member)
/*@ With (members : list cm_slot_d)
    Require cm_rep_members_safe(members) && cm_member_list_rep(member, members)
    Ensure cm_rep_members_safe(members) && __return == cm_rep_members_size(members) && cm_member_list_rep(member, members)
*/
{
  long long total;
  if (member == 0) {
    total = 0;
  } else {
    /*@ Assert exists (head : cm_slot_d) (tail : list cm_slot_d) (nextp : Z),
      member == member@pre &&
      member != 0 &&
      members == cons(head, tail) &&
      cm_rep_members_safe(members) &&
      cm_rep_members_safe(tail) &&
      data_at(&(member->ty), int, cm_type_encode(cm_slot_ty(head))) *
      data_at(&(member->count), int, cm_slot_count(head)) *
      data_at(&(member->next), struct cm_member *, nextp) *
      cm_member_list_rep(nextp, tail) *
      undef_data_at(&total, long long)
    */
    long long size = cmc_code_slot_size(member->ty, member->count);
    struct cm_member *next = member->next;
    long long rest_size = cmc_members_size(next);
    total = size + rest_size;
  }
  return total;
}

static long long cmc_struct_size_at(struct cm_struct *item, int sid)
/*@ With (structs : list cm_struct_d)
    Require 0 <= sid && cm_rep_structs_safe(structs) && cm_struct_list_rep(item, structs)
    Ensure 0 <= sid && cm_rep_structs_safe(structs) && __return == cm_rep_struct_size(structs, sid) && cm_struct_list_rep(item, structs)
*/
{
  long long total;
  if (item == 0) {
    total = 0;
  } else {
    /*@ Assert exists (head : cm_struct_d) (tail : list cm_struct_d) (nextp : Z) (memberp : Z),
      item == item@pre &&
      item != 0 &&
      structs == cons(head, tail) &&
      sid == sid@pre &&
      0 <= sid &&
      cm_rep_structs_safe(structs) &&
      cm_rep_structs_safe(tail) &&
      cm_rep_members_safe(cm_struct_members(head)) &&
      data_at(&(item->members), struct cm_member *, memberp) *
      cm_member_list_rep(memberp, cm_struct_members(head)) *
      data_at(&(item->next), struct cm_struct *, nextp) *
      cm_struct_list_rep(nextp, tail) *
      undef_data_at(&total, long long)
    */
    if (sid == 0) {
      total = cmc_members_size(item->members);
    } else {
      struct cm_struct *next = item->next;
      total = cmc_struct_size_at(next, sid - 1);
    }
  }
  return total;
}

static int cmc_nonzero(int n)
/*@ Require emp
    Ensure __return == cm_rep_nonzero(n) && emp
*/
{
  int result;
  if (n == 0) {
    result = 0;
  } else {
    result = 1;
  }
  return result;
}

static int cmc_global_array_at(struct cm_global *item, int index)
/*@ With (globals : list cm_global_d)
    Require 0 <= index && cm_global_list_rep(item, globals)
    Ensure 0 <= index && __return == cm_rep_global_array(globals, index) && cm_global_list_rep(item, globals)
*/
{
  int result;
  if (item == 0) {
    result = 0;
  } else {
    /*@ Assert exists (head : cm_global_d) (tail : list cm_global_d) (nextp : Z),
      item == item@pre &&
      item != 0 &&
      globals == cons(head, tail) &&
      index == index@pre &&
      0 <= index &&
      data_at(&(item->ty), int, cm_type_encode(cm_global_ty(head))) *
      data_at(&(item->count), int, cm_global_count(head)) *
      data_at(&(item->has_init), int, cm_rep_bool(cm_global_has_init(head))) *
      data_at(&(item->init), long long, cm_global_init(head)) *
      data_at(&(item->next), struct cm_global *, nextp) *
      cm_global_list_rep(nextp, tail) *
      undef_data_at(&result, int)
    */
    if (index == 0) {
      result = cmc_nonzero(item->count);
    } else {
      struct cm_global *next = item->next;
      result = cmc_global_array_at(next, index - 1);
    }
  }
  return result;
}

static int cmc_slot_array_at(struct cm_slot *item, int index)
/*@ With (slots : list cm_slot_d)
    Require 0 <= index && cm_slot_list_rep(item, slots)
    Ensure 0 <= index && __return == cm_rep_member_array(slots, index) && cm_slot_list_rep(item, slots)
*/
{
  int result;
  if (item == 0) {
    result = 0;
  } else {
    /*@ Assert exists (head : cm_slot_d) (tail : list cm_slot_d) (nextp : Z),
      item == item@pre &&
      item != 0 &&
      slots == cons(head, tail) &&
      index == index@pre &&
      0 <= index &&
      data_at(&(item->ty), int, cm_type_encode(cm_slot_ty(head))) *
      data_at(&(item->count), int, cm_slot_count(head)) *
      data_at(&(item->next), struct cm_slot *, nextp) *
      cm_slot_list_rep(nextp, tail) *
      undef_data_at(&result, int)
    */
    if (index == 0) {
      result = cmc_nonzero(item->count);
    } else {
      struct cm_slot *next = item->next;
      result = cmc_slot_array_at(next, index - 1);
    }
  }
  return result;
}

int cmc_slot_type_at(struct cm_slot *item, int index)
/*@ With (slots : list cm_slot_d)
    Require 0 <= index && cm_slot_list_rep(item, slots)
    Ensure 0 <= index && __return == cm_rep_slot_type(slots, index) && cm_slot_list_rep(item, slots)
*/
{
  int result;
  if (item == 0) {
    result = 0;
  } else {
    /*@ Assert exists (head : cm_slot_d) (tail : list cm_slot_d) (nextp : Z),
      item == item@pre &&
      item != 0 &&
      slots == cons(head, tail) &&
      index == index@pre &&
      0 <= index &&
      data_at(&(item->ty), int, cm_type_encode(cm_slot_ty(head))) *
      data_at(&(item->count), int, cm_slot_count(head)) *
      data_at(&(item->next), struct cm_slot *, nextp) *
      cm_slot_list_rep(nextp, tail) *
      undef_data_at(&result, int)
    */
    if (index == 0) {
      result = item->ty;
    } else {
      struct cm_slot *next = item->next;
      result = cmc_slot_type_at(next, index - 1);
    }
  }
  return result;
}

static int cmc_member_array_at(struct cm_member *item, int index)
/*@ With (members : list cm_slot_d)
    Require 0 <= index && cm_member_list_rep(item, members)
    Ensure 0 <= index && __return == cm_rep_member_array(members, index) && cm_member_list_rep(item, members)
*/
{
  int result;
  if (item == 0) {
    result = 0;
  } else {
    /*@ Assert exists (head : cm_slot_d) (tail : list cm_slot_d) (nextp : Z),
      item == item@pre &&
      item != 0 &&
      members == cons(head, tail) &&
      index == index@pre &&
      0 <= index &&
      data_at(&(item->ty), int, cm_type_encode(cm_slot_ty(head))) *
      data_at(&(item->count), int, cm_slot_count(head)) *
      data_at(&(item->next), struct cm_member *, nextp) *
      cm_member_list_rep(nextp, tail) *
      undef_data_at(&result, int)
    */
    if (index == 0) {
      result = cmc_nonzero(item->count);
    } else {
      struct cm_member *next = item->next;
      result = cmc_member_array_at(next, index - 1);
    }
  }
  return result;
}

long long cmc_type_size_at(struct cm_struct *items, int ty)
/*@ With (structs : list cm_struct_d)
    Require 0 <= ty && cm_rep_structs_safe(structs) && cm_struct_list_rep(items, structs)
    Ensure 0 <= ty && cm_rep_structs_safe(structs) && __return == cm_rep_type_size(structs, ty) && cm_struct_list_rep(items, structs)
*/
{
  long long result;
  if (ty >= 1024) {
    result = 8;
  } else if (ty == CMC_TYPE_INT) {
    result = 8;
  } else if (ty == CMC_TYPE_CHAR) {
    result = 1;
  } else {
    result = cmc_struct_size_at(items, ty - 2);
  }
  return result;
}

static long long cmc_slots_size(struct cm_slot *slot)
/*@ With (slots : list cm_slot_d)
    Require cm_rep_members_safe(slots) && cm_slot_list_rep(slot, slots)
    Ensure cm_rep_members_safe(slots) && __return == cm_rep_members_size(slots) && 0 <= __return && __return <= 1048576 && cm_slot_list_rep(slot, slots)
*/
{
  long long total;
  if (slot == 0) {
    total = 0;
  } else {
    /*@ Assert exists (head : cm_slot_d) (tail : list cm_slot_d) (nextp : Z),
      slot == slot@pre &&
      slot != 0 &&
      slots == cons(head, tail) &&
      cm_rep_members_safe(slots) &&
      cm_rep_members_safe(tail) &&
      data_at(&(slot->ty), int, cm_type_encode(cm_slot_ty(head))) *
      data_at(&(slot->count), int, cm_slot_count(head)) *
      data_at(&(slot->next), struct cm_slot *, nextp) *
      cm_slot_list_rep(nextp, tail) *
      undef_data_at(&total, long long)
    */
    long long size = cmc_code_slot_size(slot->ty, slot->count);
    struct cm_slot *next = slot->next;
    long long rest_size = cmc_slots_size(next);
    total = size + rest_size;
  }
  return total;
}

static long long cmc_slots_prefix(struct cm_slot *slot, int index)
/*@ With (slots : list cm_slot_d)
    Require 0 <= index && cm_rep_members_safe(slots) && cm_slot_list_rep(slot, slots)
    Ensure 0 <= index && cm_rep_members_safe(slots) && __return == cm_rep_member_prefix(slots, index) && 0 <= __return && __return <= 1048576 && __return <= cm_rep_members_size(slots) && cm_slot_list_rep(slot, slots)
*/
{
  long long total;
  if (slot == 0) {
    total = 0;
  } else {
    /*@ Assert exists (head : cm_slot_d) (tail : list cm_slot_d) (nextp : Z),
      slot == slot@pre &&
      slot != 0 &&
      slots == cons(head, tail) &&
      index == index@pre &&
      0 <= index &&
      cm_rep_members_safe(slots) &&
      cm_rep_members_safe(tail) &&
      data_at(&(slot->ty), int, cm_type_encode(cm_slot_ty(head))) *
      data_at(&(slot->count), int, cm_slot_count(head)) *
      data_at(&(slot->next), struct cm_slot *, nextp) *
      cm_slot_list_rep(nextp, tail) *
      undef_data_at(&total, long long)
    */
    if (index == 0) {
      total = 0;
    } else {
      long long size = cmc_code_slot_size(slot->ty, slot->count);
      struct cm_slot *next = slot->next;
      long long rest_size = cmc_slots_prefix(next, index - 1);
      total = size + rest_size;
    }
  }
  return total;
}

static long long cmc_members_prefix(struct cm_member *node, int index)
/*@ With (members : list cm_slot_d)
    Require 0 <= index && cm_rep_members_safe(members) && cm_member_list_rep(node, members)
    Ensure 0 <= index && cm_rep_members_safe(members) && __return == cm_rep_member_prefix(members, index) && 0 <= __return && __return <= 1048576 && __return <= cm_rep_members_size(members) && cm_member_list_rep(node, members)
*/
{
  long long total;
  if (node == 0) {
    total = 0;
  } else {
    /*@ Assert exists (head : cm_slot_d) (tail : list cm_slot_d) (nextp : Z),
      node == node@pre &&
      node != 0 &&
      members == cons(head, tail) &&
      index == index@pre &&
      0 <= index &&
      cm_rep_members_safe(members) &&
      cm_rep_members_safe(tail) &&
      data_at(&(node->ty), int, cm_type_encode(cm_slot_ty(head))) *
      data_at(&(node->count), int, cm_slot_count(head)) *
      data_at(&(node->next), struct cm_member *, nextp) *
      cm_member_list_rep(nextp, tail) *
      undef_data_at(&total, long long)
    */
    if (index == 0) {
      total = 0;
    } else {
      long long size = cmc_code_slot_size(node->ty, node->count);
      struct cm_member *next = node->next;
      long long rest_size = cmc_members_prefix(next, index - 1);
      total = size + rest_size;
    }
  }
  return total;
}

long long cmc_member_offset_at(struct cm_struct *item,
                                      int sid, int index)
/*@ With (structs : list cm_struct_d)
    Require 0 <= sid && 0 <= index && cm_rep_structs_safe(structs) && cm_struct_list_rep(item, structs)
    Ensure 0 <= sid && 0 <= index && cm_rep_structs_safe(structs) && __return == cm_rep_struct_member_prefix(structs, sid, index) && 0 <= __return && __return <= 1048576 && cm_struct_list_rep(item, structs)
*/
{
  long long total;
  if (item == 0) {
    total = 0;
  } else {
    /*@ Assert exists (head : cm_struct_d) (tail : list cm_struct_d) (nextp : Z) (memberp : Z),
      item == item@pre &&
      item != 0 &&
      structs == cons(head, tail) &&
      sid == sid@pre &&
      0 <= sid &&
      index == index@pre &&
      0 <= index &&
      cm_rep_structs_safe(structs) &&
      cm_rep_structs_safe(tail) &&
      cm_rep_members_safe(cm_struct_members(head)) &&
      data_at(&(item->members), struct cm_member *, memberp) *
      cm_member_list_rep(memberp, cm_struct_members(head)) *
      data_at(&(item->next), struct cm_struct *, nextp) *
      cm_struct_list_rep(nextp, tail) *
      undef_data_at(&total, long long)
    */
    if (sid == 0) {
      total = cmc_members_prefix(item->members, index);
    } else {
      struct cm_struct *next = item->next;
      total = cmc_member_offset_at(next, sid - 1, index);
    }
  }
  return total;
}

static int cmc_struct_member_array_at(struct cm_struct *item,
                                      int sid, int index)
/*@ With (structs : list cm_struct_d)
    Require 0 <= sid && 0 <= index && cm_rep_structs_safe(structs) && cm_struct_list_rep(item, structs)
    Ensure 0 <= sid && 0 <= index && cm_rep_structs_safe(structs) && __return == cm_rep_struct_member_array(structs, sid, index) && cm_struct_list_rep(item, structs)
*/
{
  int result;
  if (item == 0) {
    result = 0;
  } else {
    /*@ Assert exists (head : cm_struct_d) (tail : list cm_struct_d) (nextp : Z) (memberp : Z),
      item == item@pre &&
      item != 0 &&
      structs == cons(head, tail) &&
      sid == sid@pre &&
      0 <= sid &&
      index == index@pre &&
      0 <= index &&
      cm_rep_structs_safe(structs) &&
      cm_rep_structs_safe(tail) &&
      cm_rep_members_safe(cm_struct_members(head)) &&
      data_at(&(item->members), struct cm_member *, memberp) *
      cm_member_list_rep(memberp, cm_struct_members(head)) *
      data_at(&(item->next), struct cm_struct *, nextp) *
      cm_struct_list_rep(nextp, tail) *
      undef_data_at(&result, int)
    */
    if (sid == 0) {
      result = cmc_member_array_at(item->members, index);
    } else {
      struct cm_struct *next = item->next;
      result = cmc_struct_member_array_at(next, sid - 1, index);
    }
  }
  return result;
}

long long cmc_globals_size(struct cm_global *node)
/*@ With (globals : list cm_global_d)
    Require cm_rep_globals_safe(globals) && cm_global_list_rep(node, globals)
    Ensure cm_rep_globals_safe(globals) && __return == cm_rep_globals_size(globals) && 0 <= __return && __return <= 1048560 && cm_global_list_rep(node, globals)
*/
{
  long long total;
  if (node == 0) {
    total = 0;
  } else {
    /*@ Assert exists (head : cm_global_d) (tail : list cm_global_d) (nextp : Z),
      node == node@pre &&
      node != 0 &&
      globals == cons(head, tail) &&
      cm_rep_globals_safe(globals) &&
      cm_rep_globals_safe(tail) &&
      data_at(&(node->ty), int, cm_type_encode(cm_global_ty(head))) *
      data_at(&(node->count), int, cm_global_count(head)) *
      data_at(&(node->has_init), int, cm_rep_bool(cm_global_has_init(head))) *
      data_at(&(node->init), long long, cm_global_init(head)) *
      data_at(&(node->next), struct cm_global *, nextp) *
      cm_global_list_rep(nextp, tail) *
      undef_data_at(&total, long long)
    */
    long long size = cmc_code_slot_size(node->ty, node->count);
    struct cm_global *next = node->next;
    long long rest_size = cmc_globals_size(next);
    total = size + rest_size;
  }
  return total;
}

static long long cmc_globals_prefix(struct cm_global *node, int index)
/*@ With (globals : list cm_global_d)
    Require 0 <= index && cm_rep_globals_safe(globals) && cm_global_list_rep(node, globals)
    Ensure 0 <= index && cm_rep_globals_safe(globals) && __return == cm_rep_globals_prefix(globals, index) && 0 <= __return && __return <= 1048560 && __return <= cm_rep_globals_size(globals) && cm_global_list_rep(node, globals)
*/
{
  long long total;
  if (node == 0) {
    total = 0;
  } else {
    /*@ Assert exists (head : cm_global_d) (tail : list cm_global_d) (nextp : Z),
      node == node@pre &&
      node != 0 &&
      globals == cons(head, tail) &&
      index == index@pre &&
      0 <= index &&
      cm_rep_globals_safe(globals) &&
      cm_rep_globals_safe(tail) &&
      data_at(&(node->ty), int, cm_type_encode(cm_global_ty(head))) *
      data_at(&(node->count), int, cm_global_count(head)) *
      data_at(&(node->has_init), int, cm_rep_bool(cm_global_has_init(head))) *
      data_at(&(node->init), long long, cm_global_init(head)) *
      data_at(&(node->next), struct cm_global *, nextp) *
      cm_global_list_rep(nextp, tail) *
      undef_data_at(&total, long long)
    */
    if (index == 0) {
      total = 0;
    } else {
      long long size = cmc_code_slot_size(node->ty, node->count);
      struct cm_global *next = node->next;
      long long rest_size = cmc_globals_prefix(next, index - 1);
      total = size + rest_size;
    }
  }
  return total;
}

long long cmc_strings_size(struct cm_string *node)
/*@ With (strings : list cm_string_d)
    Require cm_rep_strings_safe(strings) && cm_string_list_rep(node, strings)
    Ensure cm_rep_strings_safe(strings) && __return == cm_rep_strings_size(strings) && 0 <= __return && __return <= 1048560 && cm_string_list_rep(node, strings)
*/
{
  long long total;
  if (node == 0) {
    total = 0;
  } else {
    /*@ Assert exists (head : cm_string_d) (tail : list cm_string_d) (nextp : Z) (bytesp : Z),
      node == node@pre &&
      node != 0 &&
      strings == cons(head, tail) &&
      cm_rep_strings_safe(strings) &&
      cm_rep_strings_safe(tail) &&
      data_at(&(node->bytes), unsigned char *, bytesp) *
      data_at(&(node->length), int, cm_rep_string_length(head)) *
      cm_uint8_buffer(bytesp, cm_string_bytes(head)) *
      data_at(&(node->next), struct cm_string *, nextp) *
      cm_string_list_rep(nextp, tail) *
      undef_data_at(&total, long long)
    */
    long long size = node->length;
    size = size + 1;
    struct cm_string *next = node->next;
    long long rest_size = cmc_strings_size(next);
    total = size + rest_size;
  }
  return total;
}

static long long cmc_strings_prefix(struct cm_string *node, int index)
/*@ With (strings : list cm_string_d)
    Require 0 <= index && cm_rep_strings_safe(strings) && cm_string_list_rep(node, strings)
    Ensure 0 <= index && cm_rep_strings_safe(strings) && __return == cm_rep_strings_prefix(strings, index) && 0 <= __return && __return <= 1048560 && __return <= cm_rep_strings_size(strings) && cm_string_list_rep(node, strings)
*/
{
  long long total;
  if (node == 0) {
    total = 0;
  } else {
    /*@ Assert exists (head : cm_string_d) (tail : list cm_string_d) (nextp : Z) (bytesp : Z),
      node == node@pre &&
      node != 0 &&
      strings == cons(head, tail) &&
      index == index@pre &&
      0 <= index &&
      cm_rep_strings_safe(strings) &&
      cm_rep_strings_safe(tail) &&
      data_at(&(node->bytes), unsigned char *, bytesp) *
      data_at(&(node->length), int, cm_rep_string_length(head)) *
      cm_uint8_buffer(bytesp, cm_string_bytes(head)) *
      data_at(&(node->next), struct cm_string *, nextp) *
      cm_string_list_rep(nextp, tail) *
      undef_data_at(&total, long long)
    */
    if (index == 0) {
      total = 0;
    } else {
      long long size = node->length;
      size = size + 1;
      struct cm_string *next = node->next;
      long long rest_size = cmc_strings_prefix(next, index - 1);
      total = size + rest_size;
    }
  }
  return total;
}

long long cmc_global_address(struct cm_global *globals, int index)
/*@ With (items : list cm_global_d)
    Require 0 <= index && cm_rep_globals_safe(items) && cm_global_list_rep(globals, items)
    Ensure 0 <= index && cm_rep_globals_safe(items) && __return == cm_rep_global_address(items, index) && 16 <= __return && __return <= 1048576 && cm_global_list_rep(globals, items)
*/
{
  long long prefix = cmc_globals_prefix(globals, index);
  long long address = 16LL + prefix;
  return address;
}

long long cmc_string_address(struct cm_global *globals,
                                    struct cm_string *strings, int index)
/*@ With (global_items : list cm_global_d) (string_items : list cm_string_d)
    Require 0 <= index && cm_rep_globals_safe(global_items) && cm_rep_strings_safe(string_items) && cm_rep_globals_size(global_items) + cm_rep_strings_size(string_items) <= 1048560 && cm_global_list_rep(globals, global_items) * cm_string_list_rep(strings, string_items)
    Ensure 0 <= index && cm_rep_globals_safe(global_items) && cm_rep_strings_safe(string_items) && cm_rep_globals_size(global_items) + cm_rep_strings_size(string_items) <= 1048560 && __return == cm_rep_string_address(global_items, string_items, index) && 16 <= __return && __return <= 1048576 && cm_global_list_rep(globals, global_items) * cm_string_list_rep(strings, string_items)
*/
{
  long long global_size = cmc_globals_size(globals);
  long long prefix = cmc_strings_prefix(strings, index);
  long long address = 16LL + global_size;
  address = address + prefix;
  return address;
}

void cmc_binding_array_value(struct cm_program *program, int fid,
                                    struct cm_function *fn,
                                    int scope, int slot, int *array)
/*@ With (policy : cm_lookup_policy) (p : cm_program) (f : cm_function_d) (globals : list cm_global_d) (locals : list cm_slot_d) (zg : Z) (zl : Z)
    Require 0 <= slot && globals == cm_program_globals(p) && locals == cm_function_locals(f) && f == cm_function_at(policy, fid, cm_program_functions(p)) && cm_binding_valid(p, f, scope, slot) && data_at(&(program->globals), struct cm_global *, zg) * cm_global_list_rep(zg, globals) * data_at(&(fn->locals), struct cm_slot *, zl) * cm_slot_list_rep(zl, locals) * undef_data_at(array, int)
    Ensure 0 <= slot && globals == cm_program_globals(p) && locals == cm_function_locals(f) && f == cm_function_at(policy, fid, cm_program_functions(p)) && cm_binding_valid(p, f, scope, slot) && data_at(&(program->globals), struct cm_global *, zg) * cm_global_list_rep(zg, globals) * data_at(&(fn->locals), struct cm_slot *, zl) * cm_slot_list_rep(zl, locals) * data_at(array, int, cm_binding_array_code(policy, p, fid, scope, slot))
*/
{
  int result;
  if (scope == CMC_BIND_GLOBAL) {
    result = cmc_global_array_at(program->globals, slot);
  } else if (scope == CMC_BIND_LOCAL) {
    result = cmc_slot_array_at(fn->locals, slot);
  } else {
    result = 0;
  }
  *array = result;
}

int cmc_binding_array(struct cm_program *program, int fid,
                             struct cm_function *fn,
                             int scope, int slot)
/*@ With (policy : cm_lookup_policy) (p : cm_program) (f : cm_function_d) (globals : list cm_global_d) (locals : list cm_slot_d) (zg : Z) (zl : Z)
    Require 0 <= slot && globals == cm_program_globals(p) && locals == cm_function_locals(f) && f == cm_function_at(policy, fid, cm_program_functions(p)) && cm_binding_valid(p, f, scope, slot) && data_at(&(program->globals), struct cm_global *, zg) * cm_global_list_rep(zg, globals) * data_at(&(fn->locals), struct cm_slot *, zl) * cm_slot_list_rep(zl, locals)
    Ensure 0 <= slot && globals == cm_program_globals(p) && locals == cm_function_locals(f) && f == cm_function_at(policy, fid, cm_program_functions(p)) && cm_binding_valid(p, f, scope, slot) && __return == cm_binding_array_code(policy, p, fid, scope, slot) && data_at(&(program->globals), struct cm_global *, zg) * cm_global_list_rep(zg, globals) * data_at(&(fn->locals), struct cm_slot *, zl) * cm_slot_list_rep(zl, locals)
*/
{
  int result;
  cmc_binding_array_value(program, fid, fn, scope, slot, &result) /*@ where policy = policy, p = p, f = f, globals = globals, locals = locals, zg = zg, zl = zl */;
  return result;
}

int cmc_member_array(struct cm_program *program, int base_ty, int mid)
/*@ With (p : cm_program) (base : cm_type) (structs : list cm_struct_d) (zs : Z)
    Require 1024 <= base_ty && base_ty <= 2147483647 && 0 <= (base_ty - 1024) % 1024 - 2 && 0 <= mid && structs == cm_program_structs(p) && base_ty == cm_type_encode(base) && cm_type_code_wf(base) && cm_member_valid(p, base, mid) && cm_rep_structs_safe(structs) && data_at(&(program->structs), struct cm_struct *, zs) * cm_struct_list_rep(zs, structs)
    Ensure 1024 <= base_ty && base_ty <= 2147483647 && 0 <= (base_ty - 1024) % 1024 - 2 && 0 <= mid && structs == cm_program_structs(p) && base_ty == cm_type_encode(base) && cm_type_code_wf(base) && cm_member_valid(p, base, mid) && cm_rep_structs_safe(structs) && __return == cm_member_array_code(p, base, mid) && data_at(&(program->structs), struct cm_struct *, zs) * cm_struct_list_rep(zs, structs)
*/
{
  int pointee = cmc_pointee(base_ty);
  int sid = (pointee % 1024) - 2;
  int result = cmc_struct_member_array_at(program->structs, sid, mid);
  return result;
}

void cmc_member_array_value(struct cm_program *program,
                                   int base_ty, int mid, int *array)
/*@ With (p : cm_program) (base : cm_type) (structs : list cm_struct_d) (zs : Z)
    Require 1024 <= base_ty && base_ty <= 2147483647 && 0 <= (base_ty - 1024) % 1024 - 2 && 0 <= mid && structs == cm_program_structs(p) && base_ty == cm_type_encode(base) && cm_type_code_wf(base) && cm_member_valid(p, base, mid) && cm_rep_structs_safe(structs) && data_at(&(program->structs), struct cm_struct *, zs) * cm_struct_list_rep(zs, structs) * undef_data_at(array, int)
    Ensure 1024 <= base_ty && base_ty <= 2147483647 && 0 <= (base_ty - 1024) % 1024 - 2 && 0 <= mid && structs == cm_program_structs(p) && base_ty == cm_type_encode(base) && cm_type_code_wf(base) && cm_member_valid(p, base, mid) && cm_rep_structs_safe(structs) && data_at(&(program->structs), struct cm_struct *, zs) * cm_struct_list_rep(zs, structs) * data_at(array, int, cm_member_array_code(p, base, mid))
*/
{
  int result;
  result = cmc_member_array(program, base_ty, mid) /*@ where p = p, base = base, structs = structs, zs = zs */;
  *array = result;
}

static void cm_expr_temps(struct cm_expr *expr,
                          int *lvalue, int *rvalue)
/*@ With (e : cm_expr)
    Require cm_rep_expr_temps_safe(e) && cm_expr_rep(expr, e) * undef_data_at(lvalue, int) * undef_data_at(rvalue, int)
    Ensure cm_rep_expr_temps_safe(e) && cm_expr_rep(expr, e) * data_at(lvalue, int, cm_tleft(cm_expr_tpair(e))) * data_at(rvalue, int, cm_tright(cm_expr_tpair(e)))
*/
;

int cm_args_length(struct cm_arg *arg)
/*@ With (args : list cm_expr)
    Require cm_rep_args_safe(args) && cm_arg_list_rep(arg, args)
    Ensure cm_rep_args_safe(args) && __return == cm_rep_args_length(args) && cm_arg_list_rep(arg, args)
*/
{
  int count;
  if (arg == 0) {
    count = 0;
  } else {
    /*@ Assert exists (head : cm_expr) (tail : list cm_expr) (ep : Z) (np : Z),
      arg == arg@pre &&
      arg != 0 &&
      args == cons(head, tail) &&
      cm_rep_args_safe(args) &&
      cm_rep_args_safe(tail) &&
      data_at(&(arg->expr), struct cm_expr *, ep) *
      data_at(&(arg->next), struct cm_arg *, np) *
      cm_expr_rep(ep, head) * cm_arg_list_rep(np, tail) * undef_data_at(&count, int)
    */
    count = cm_args_length(arg->next);
    count = count + 1;
  }
  return count;
}

static void cmc_args_tpair(struct cm_arg *arg, int *count, int *depth)
/*@ With (args : list cm_expr)
    Require cm_rep_args_temps_safe(args) && cm_arg_list_rep(arg, args) * undef_data_at(count, int) * undef_data_at(depth, int)
    Ensure cm_rep_args_temps_safe(args) && cm_arg_list_rep(arg, args) * data_at(count, int, cm_acount(cm_args_apair(args))) * data_at(depth, int, cm_adepth(cm_args_apair(args)))
*/
{
  if (arg == 0) {
    *count = 0;
    *depth = 0;
  } else {
    /*@ Assert exists (head : cm_expr) (tail : list cm_expr) (ep : Z) (np : Z),
      arg == arg@pre &&
      arg != 0 &&
      args == cons(head, tail) &&
      cm_rep_args_temps_safe(args) &&
      cm_rep_args_temps_safe(tail) &&
      count == count@pre &&
      depth == depth@pre &&
      cm_rep_expr_temps_safe(head) &&
      data_at(&(arg->expr), struct cm_expr *, ep) *
      data_at(&(arg->next), struct cm_arg *, np) *
      cm_expr_rep(ep, head) * cm_arg_list_rep(np, tail) * undef_data_at(count, int) * undef_data_at(depth, int)
    */
    struct cm_expr *child = arg->expr;
    int child_lvalue;
    int child_rvalue;
    cm_expr_temps(child, &child_lvalue, &child_rvalue);
    int rest_count;
    int rest_depth;
    cmc_args_tpair(arg->next, &rest_count, &rest_depth);
    int new_count = rest_count + 1;
    int new_depth = cm_max(child_rvalue, rest_depth);
    *count = new_count;
    *depth = new_depth;
  }
}

static void cm_expr_temps(struct cm_expr *expr,
                          int *lvalue, int *rvalue)
/*@ With (e : cm_expr)
    Require cm_rep_expr_temps_safe(e) && cm_expr_rep(expr, e) * undef_data_at(lvalue, int) * undef_data_at(rvalue, int)
    Ensure cm_rep_expr_temps_safe(e) && cm_expr_rep(expr, e) * data_at(lvalue, int, cm_tleft(cm_expr_tpair(e))) * data_at(rvalue, int, cm_tright(cm_expr_tpair(e)))
*/
{
  /*@ Assert exists (pa : Z) (pb : Z) (pargs : Z),
    expr == expr@pre &&
    lvalue == lvalue@pre &&
    rvalue == rvalue@pre &&
    expr != 0 &&
    cm_rep_expr_temps_safe(e) &&
    data_at(&(expr->kind), int, cm_rep_expr_kind(e)) *
    data_at(&(expr->op), int, cm_rep_expr_op(e)) *
    data_at(&(expr->ty), int, cm_type_encode(cm_expr_type(e))) *
    data_at(&(expr->value), long long, cm_rep_expr_value(e)) *
    data_at(&(expr->a), struct cm_expr *, pa) *
    data_at(&(expr->b), struct cm_expr *, pb) *
    data_at(&(expr->args), struct cm_arg *, pargs) *
    cm_expr_payload(e, pa, pb, pargs) *
    undef_data_at(lvalue, int) *
    undef_data_at(rvalue, int)
  */
  int out_lvalue = 0;
  int out_rvalue = 0;
  if (expr->kind == CMC_EXPR_ASSIGN) {
    /*@ Assert exists (pa : Z) (pb : Z) (pargs : Z) (x : cm_expr) (y : cm_expr) (t : cm_type),
      expr == expr@pre &&
      lvalue == lvalue@pre &&
      rvalue == rvalue@pre &&
      expr != 0 &&
      cm_rep_expr_temps_safe(e) &&
      e == CMAssignE(x, y, t) &&
      out_lvalue == 0 &&
      out_rvalue == 0 &&
      cm_rep_expr_temps_safe(x) &&
      cm_rep_expr_temps_safe(y) &&
      pargs == 0 &&
      data_at(&(expr->kind), int, cm_rep_expr_kind(e)) *
      data_at(&(expr->op), int, cm_rep_expr_op(e)) *
      data_at(&(expr->ty), int, cm_type_encode(cm_expr_type(e))) *
      data_at(&(expr->value), long long, cm_rep_expr_value(e)) *
      data_at(&(expr->a), struct cm_expr *, pa) *
      data_at(&(expr->b), struct cm_expr *, pb) *
      data_at(&(expr->args), struct cm_arg *, pargs) *
      cm_expr_rep(pa, x) *
      cm_expr_rep(pb, y) *
      undef_data_at(lvalue, int) *
      undef_data_at(rvalue, int)
    */
    int left_lvalue;
    int left_rvalue;
    int right_lvalue;
    int right_rvalue;
    cm_expr_temps(expr->a, &left_lvalue, &left_rvalue);
    cm_expr_temps(expr->b, &right_lvalue, &right_rvalue);
    out_rvalue = cm_max(left_lvalue, 1 + right_rvalue);
  } else if (expr->kind == CMC_EXPR_BINARY) {
    /*@ Assert exists (pa : Z) (pb : Z) (pargs : Z) (op : Z) (x : cm_expr) (y : cm_expr) (t : cm_type),
      expr == expr@pre &&
      lvalue == lvalue@pre &&
      rvalue == rvalue@pre &&
      expr != 0 &&
      cm_rep_expr_temps_safe(e) &&
      e == CMBinaryE(op, x, y, t) &&
      out_lvalue == 0 &&
      out_rvalue == 0 &&
      cm_rep_expr_temps_safe(x) &&
      cm_rep_expr_temps_safe(y) &&
      pargs == 0 &&
      data_at(&(expr->kind), int, cm_rep_expr_kind(e)) *
      data_at(&(expr->op), int, cm_rep_expr_op(e)) *
      data_at(&(expr->ty), int, cm_type_encode(cm_expr_type(e))) *
      data_at(&(expr->value), long long, cm_rep_expr_value(e)) *
      data_at(&(expr->a), struct cm_expr *, pa) *
      data_at(&(expr->b), struct cm_expr *, pb) *
      data_at(&(expr->args), struct cm_arg *, pargs) *
      cm_expr_rep(pa, x) *
      cm_expr_rep(pb, y) *
      undef_data_at(lvalue, int) *
      undef_data_at(rvalue, int)
    */
    int left_lvalue;
    int left_rvalue;
    int right_lvalue;
    int right_rvalue;
    cm_expr_temps(expr->a, &left_lvalue, &left_rvalue);
    cm_expr_temps(expr->b, &right_lvalue, &right_rvalue);
    if (expr->op == CMC_BIN_OR) {
      out_rvalue = cm_max(left_rvalue, right_rvalue);
    } else if (expr->op == CMC_BIN_AND) {
      out_rvalue = cm_max(left_rvalue, right_rvalue);
    } else {
      out_rvalue = cm_max(left_rvalue, 1 + right_rvalue);
    }
  } else if (expr->kind == CMC_EXPR_UNARY) {
    /*@ Assert exists (pa : Z) (pb : Z) (pargs : Z) (op : Z) (x : cm_expr) (t : cm_type),
      expr == expr@pre &&
      lvalue == lvalue@pre &&
      rvalue == rvalue@pre &&
      expr != 0 &&
      cm_rep_expr_temps_safe(e) &&
      e == CMUnaryE(op, x, t) &&
      out_lvalue == 0 &&
      out_rvalue == 0 &&
      cm_rep_expr_temps_safe(x) &&
      pa != 0 &&
      pb == 0 &&
      pargs == 0 &&
      data_at(&(expr->kind), int, cm_rep_expr_kind(e)) *
      data_at(&(expr->op), int, cm_rep_expr_op(e)) *
      data_at(&(expr->ty), int, cm_type_encode(cm_expr_type(e))) *
      data_at(&(expr->value), long long, cm_rep_expr_value(e)) *
      data_at(&(expr->a), struct cm_expr *, pa) *
      data_at(&(expr->b), struct cm_expr *, pb) *
      data_at(&(expr->args), struct cm_arg *, pargs) *
      cm_expr_rep(pa, x) *
      undef_data_at(lvalue, int) *
      undef_data_at(rvalue, int)
    */
    int child_lvalue;
    int child_rvalue;
    cm_expr_temps(expr->a, &child_lvalue, &child_rvalue);
    if (expr->op == CMC_UN_DEREF) {
      out_lvalue = child_rvalue;
      out_rvalue = child_rvalue;
    } else if (expr->op == CMC_UN_ADDR) {
      out_rvalue = child_lvalue;
    } else {
      out_rvalue = child_rvalue;
    }
  } else if (expr->kind == CMC_EXPR_INDEX) {
    /*@ Assert exists (pa : Z) (pb : Z) (pargs : Z) (x : cm_expr) (y : cm_expr) (t : cm_type),
      expr == expr@pre &&
      lvalue == lvalue@pre &&
      rvalue == rvalue@pre &&
      expr != 0 &&
      cm_rep_expr_temps_safe(e) &&
      e == CMIndexE(x, y, t) &&
      out_lvalue == 0 &&
      out_rvalue == 0 &&
      cm_rep_expr_temps_safe(x) &&
      cm_rep_expr_temps_safe(y) &&
      pargs == 0 &&
      data_at(&(expr->kind), int, cm_rep_expr_kind(e)) *
      data_at(&(expr->op), int, cm_rep_expr_op(e)) *
      data_at(&(expr->ty), int, cm_type_encode(cm_expr_type(e))) *
      data_at(&(expr->value), long long, cm_rep_expr_value(e)) *
      data_at(&(expr->a), struct cm_expr *, pa) *
      data_at(&(expr->b), struct cm_expr *, pb) *
      data_at(&(expr->args), struct cm_arg *, pargs) *
      cm_expr_rep(pa, x) *
      cm_expr_rep(pb, y) *
      undef_data_at(lvalue, int) *
      undef_data_at(rvalue, int)
    */
    int base_lvalue;
    int base_rvalue;
    int index_lvalue;
    int index_rvalue;
    cm_expr_temps(expr->a, &base_lvalue, &base_rvalue);
    cm_expr_temps(expr->b, &index_lvalue, &index_rvalue);
    out_lvalue = cm_max(base_rvalue, 1 + index_rvalue);
    out_rvalue = out_lvalue;
  } else if (expr->kind == CMC_EXPR_MEMBER) {
    /*@ Assert exists (pa : Z) (pb : Z) (pargs : Z) (x : cm_expr) (mid : Z) (t : cm_type),
      expr == expr@pre &&
      lvalue == lvalue@pre &&
      rvalue == rvalue@pre &&
      expr != 0 &&
      cm_rep_expr_temps_safe(e) &&
      e == CMMemberE(x, mid, t) &&
      out_lvalue == 0 &&
      out_rvalue == 0 &&
      cm_rep_expr_temps_safe(x) &&
      pa != 0 &&
      pb == 0 &&
      pargs == 0 &&
      data_at(&(expr->kind), int, cm_rep_expr_kind(e)) *
      data_at(&(expr->op), int, cm_rep_expr_op(e)) *
      data_at(&(expr->ty), int, cm_type_encode(cm_expr_type(e))) *
      data_at(&(expr->value), long long, cm_rep_expr_value(e)) *
      data_at(&(expr->a), struct cm_expr *, pa) *
      data_at(&(expr->b), struct cm_expr *, pb) *
      data_at(&(expr->args), struct cm_arg *, pargs) *
      cm_expr_rep(pa, x) *
      undef_data_at(lvalue, int) *
      undef_data_at(rvalue, int)
    */
    int base_lvalue;
    int base_rvalue;
    cm_expr_temps(expr->a, &base_lvalue, &base_rvalue);
    out_lvalue = base_rvalue;
    out_rvalue = base_rvalue;
  } else if (expr->kind == CMC_EXPR_CALL) {
    /*@ Assert exists (pa : Z) (pb : Z) (pargs : Z) (fid : Z) (eargs : list cm_expr) (t : cm_type),
      expr == expr@pre &&
      lvalue == lvalue@pre &&
      rvalue == rvalue@pre &&
      expr != 0 &&
      cm_rep_expr_temps_safe(e) &&
      e == CMCallE(fid, eargs, t) &&
      out_lvalue == 0 &&
      out_rvalue == 0 &&
      cm_rep_args_temps_safe(eargs) &&
      pa == 0 &&
      pb == 0 &&
      data_at(&(expr->kind), int, cm_rep_expr_kind(e)) *
      data_at(&(expr->op), int, cm_rep_expr_op(e)) *
      data_at(&(expr->ty), int, cm_type_encode(cm_expr_type(e))) *
      data_at(&(expr->value), long long, cm_rep_expr_value(e)) *
      data_at(&(expr->a), struct cm_expr *, pa) *
      data_at(&(expr->b), struct cm_expr *, pb) *
      data_at(&(expr->args), struct cm_arg *, pargs) *
      cm_arg_list_rep(pargs, eargs) *
      undef_data_at(lvalue, int) *
      undef_data_at(rvalue, int)
    */
    int count;
    int depth;
    cmc_args_tpair(expr->args, &count, &depth);
    out_rvalue = count + depth;
  } else if (expr->kind == CMC_EXPR_PUTC) {
    /*@ Assert exists (pa : Z) (pb : Z) (pargs : Z) (x : cm_expr) (t : cm_type),
      expr == expr@pre &&
      lvalue == lvalue@pre &&
      rvalue == rvalue@pre &&
      expr != 0 &&
      cm_rep_expr_temps_safe(e) &&
      e == CMPutcE(x, t) &&
      out_lvalue == 0 &&
      out_rvalue == 0 &&
      cm_rep_expr_temps_safe(x) &&
      pa != 0 &&
      pb == 0 &&
      pargs == 0 &&
      data_at(&(expr->kind), int, cm_rep_expr_kind(e)) *
      data_at(&(expr->op), int, cm_rep_expr_op(e)) *
      data_at(&(expr->ty), int, cm_type_encode(cm_expr_type(e))) *
      data_at(&(expr->value), long long, cm_rep_expr_value(e)) *
      data_at(&(expr->a), struct cm_expr *, pa) *
      data_at(&(expr->b), struct cm_expr *, pb) *
      data_at(&(expr->args), struct cm_arg *, pargs) *
      cm_expr_rep(pa, x) *
      undef_data_at(lvalue, int) *
      undef_data_at(rvalue, int)
    */
    int child_lvalue;
    int child_rvalue;
    cm_expr_temps(expr->a, &child_lvalue, &child_rvalue);
    out_rvalue = child_rvalue;
  } else if (expr->kind == CMC_EXPR_PUTI) {
    /*@ Assert exists (pa : Z) (pb : Z) (pargs : Z) (x : cm_expr) (t : cm_type),
      expr == expr@pre &&
      lvalue == lvalue@pre &&
      rvalue == rvalue@pre &&
      expr != 0 &&
      cm_rep_expr_temps_safe(e) &&
      e == CMPutiE(x, t) &&
      out_lvalue == 0 &&
      out_rvalue == 0 &&
      cm_rep_expr_temps_safe(x) &&
      pa != 0 &&
      pb == 0 &&
      pargs == 0 &&
      data_at(&(expr->kind), int, cm_rep_expr_kind(e)) *
      data_at(&(expr->op), int, cm_rep_expr_op(e)) *
      data_at(&(expr->ty), int, cm_type_encode(cm_expr_type(e))) *
      data_at(&(expr->value), long long, cm_rep_expr_value(e)) *
      data_at(&(expr->a), struct cm_expr *, pa) *
      data_at(&(expr->b), struct cm_expr *, pb) *
      data_at(&(expr->args), struct cm_arg *, pargs) *
      cm_expr_rep(pa, x) *
      undef_data_at(lvalue, int) *
      undef_data_at(rvalue, int)
    */
    int child_lvalue;
    int child_rvalue;
    cm_expr_temps(expr->a, &child_lvalue, &child_rvalue);
    out_rvalue = child_rvalue;
  } else if (expr->kind == CMC_EXPR_EXIT) {
    /*@ Assert exists (pa : Z) (pb : Z) (pargs : Z) (x : cm_expr) (t : cm_type),
      expr == expr@pre &&
      lvalue == lvalue@pre &&
      rvalue == rvalue@pre &&
      expr != 0 &&
      cm_rep_expr_temps_safe(e) &&
      e == CMExitE(x, t) &&
      out_lvalue == 0 &&
      out_rvalue == 0 &&
      cm_rep_expr_temps_safe(x) &&
      pa != 0 &&
      pb == 0 &&
      pargs == 0 &&
      data_at(&(expr->kind), int, cm_rep_expr_kind(e)) *
      data_at(&(expr->op), int, cm_rep_expr_op(e)) *
      data_at(&(expr->ty), int, cm_type_encode(cm_expr_type(e))) *
      data_at(&(expr->value), long long, cm_rep_expr_value(e)) *
      data_at(&(expr->a), struct cm_expr *, pa) *
      data_at(&(expr->b), struct cm_expr *, pb) *
      data_at(&(expr->args), struct cm_arg *, pargs) *
      cm_expr_rep(pa, x) *
      undef_data_at(lvalue, int) *
      undef_data_at(rvalue, int)
    */
    int child_lvalue;
    int child_rvalue;
    cm_expr_temps(expr->a, &child_lvalue, &child_rvalue);
    out_rvalue = child_rvalue;
  } else if (expr->kind == CMC_EXPR_CONST) {
  } else if (expr->kind == CMC_EXPR_STRING) {
  } else if (expr->kind == CMC_EXPR_VAR) {
  } else if (expr->kind == CMC_EXPR_SIZEOF) {
  } else if (expr->kind == CMC_EXPR_GETC) {
  } else {
  }
  *lvalue = out_lvalue;
  *rvalue = out_rvalue;
}

static int cm_expr_rtemps(struct cm_expr *expr)
/*@ With (e : cm_expr)
    Require cm_rep_expr_temps_safe(e) && cm_expr_rep(expr, e)
    Ensure cm_rep_expr_temps_safe(e) && __return == cm_tright(cm_expr_tpair(e)) && cm_expr_rep(expr, e)
*/
{
  int lvalue;
  int rvalue;
  cm_expr_temps(expr, &lvalue, &rvalue);
  return rvalue;
}

int cmc_stmt_temps(struct cm_stmt *stmt)
/*@ With (s : cm_stmt)
    Require cm_rep_stmt_temps_safe(s) && cm_stmt_rep(stmt, s)
    Ensure cm_rep_stmt_temps_safe(s) && __return == cm_stemps(s) && 0 <= cm_stemps(s) && cm_stemps(s) <= 2147483647 && cm_stmt_rep(stmt, s)
*/
{
  /*@ Assert exists (pe : Z) (pa : Z) (pb : Z),
    stmt == stmt@pre &&
    stmt != 0 &&
    cm_rep_stmt_temps_safe(s) &&
    data_at(&(stmt->kind), int, cm_rep_stmt_kind(s)) *
    data_at(&(stmt->slot), int, cm_rep_stmt_slot(s)) *
    data_at(&(stmt->expr), struct cm_expr *, pe) *
    data_at(&(stmt->a), struct cm_stmt *, pa) *
    data_at(&(stmt->b), struct cm_stmt *, pb) *
    cm_stmt_payload(s, pe, pa, pb)
  */
  int result = 0;
  if (stmt->kind == CMC_STMT_EXPR) {
    /*@ Assert exists (pe : Z) (pa : Z) (pb : Z) (x : cm_expr),
      stmt == stmt@pre &&
      stmt != 0 &&
      cm_rep_stmt_temps_safe(s) &&
      s == CMExprS(x) &&
      result == 0 &&
      cm_rep_expr_temps_safe(x) &&
      pe != 0 &&
      pa == 0 &&
      pb == 0 &&
      data_at(&(stmt->kind), int, cm_rep_stmt_kind(s)) *
      data_at(&(stmt->slot), int, cm_rep_stmt_slot(s)) *
      data_at(&(stmt->expr), struct cm_expr *, pe) *
      data_at(&(stmt->a), struct cm_stmt *, pa) *
      data_at(&(stmt->b), struct cm_stmt *, pb) *
      cm_expr_rep(pe, x)
    */
    result = cm_expr_rtemps(stmt->expr);
  } else if (stmt->kind == CMC_STMT_INIT) {
    /*@ Assert exists (pe : Z) (pa : Z) (pb : Z) (slotid : Z) (x : cm_expr),
      stmt == stmt@pre &&
      stmt != 0 &&
      cm_rep_stmt_temps_safe(s) &&
      s == CMInitS(slotid, x) &&
      result == 0 &&
      cm_rep_expr_temps_safe(x) &&
      pe != 0 &&
      pa == 0 &&
      pb == 0 &&
      data_at(&(stmt->kind), int, cm_rep_stmt_kind(s)) *
      data_at(&(stmt->slot), int, cm_rep_stmt_slot(s)) *
      data_at(&(stmt->expr), struct cm_expr *, pe) *
      data_at(&(stmt->a), struct cm_stmt *, pa) *
      data_at(&(stmt->b), struct cm_stmt *, pb) *
      cm_expr_rep(pe, x)
    */
    result = cm_expr_rtemps(stmt->expr);
  } else if (stmt->kind == CMC_STMT_RETURN) {
    /*@ Assert exists (pe : Z) (pa : Z) (pb : Z) (x : cm_expr),
      stmt == stmt@pre &&
      stmt != 0 &&
      cm_rep_stmt_temps_safe(s) &&
      s == CMReturnS(x) &&
      result == 0 &&
      cm_rep_expr_temps_safe(x) &&
      pe != 0 &&
      pa == 0 &&
      pb == 0 &&
      data_at(&(stmt->kind), int, cm_rep_stmt_kind(s)) *
      data_at(&(stmt->slot), int, cm_rep_stmt_slot(s)) *
      data_at(&(stmt->expr), struct cm_expr *, pe) *
      data_at(&(stmt->a), struct cm_stmt *, pa) *
      data_at(&(stmt->b), struct cm_stmt *, pb) *
      cm_expr_rep(pe, x)
    */
    result = cm_expr_rtemps(stmt->expr);
  } else if (stmt->kind == CMC_STMT_SEQ) {
    /*@ Assert exists (pe : Z) (pa : Z) (pb : Z) (x : cm_stmt) (y : cm_stmt),
      stmt == stmt@pre &&
      stmt != 0 &&
      cm_rep_stmt_temps_safe(s) &&
      s == CMSeqS(x, y) &&
      result == 0 &&
      cm_rep_stmt_temps_safe(x) &&
      cm_rep_stmt_temps_safe(y) &&
      pe == 0 &&
      data_at(&(stmt->kind), int, cm_rep_stmt_kind(s)) *
      data_at(&(stmt->slot), int, cm_rep_stmt_slot(s)) *
      data_at(&(stmt->expr), struct cm_expr *, pe) *
      data_at(&(stmt->a), struct cm_stmt *, pa) *
      data_at(&(stmt->b), struct cm_stmt *, pb) *
      cm_stmt_rep(pa, x) *
      cm_stmt_rep(pb, y)
    */
    int first_temps = cmc_stmt_temps(stmt->a);
    int second_temps = cmc_stmt_temps(stmt->b);
    result = cm_max(first_temps, second_temps);
  } else if (stmt->kind == CMC_STMT_BLOCK) {
    /*@ Assert exists (pe : Z) (pa : Z) (pb : Z) (x : cm_stmt),
      stmt == stmt@pre &&
      stmt != 0 &&
      cm_rep_stmt_temps_safe(s) &&
      s == CMBlockS(x) &&
      result == 0 &&
      cm_rep_stmt_temps_safe(x) &&
      pe == 0 &&
      pa != 0 &&
      pb == 0 &&
      data_at(&(stmt->kind), int, cm_rep_stmt_kind(s)) *
      data_at(&(stmt->slot), int, cm_rep_stmt_slot(s)) *
      data_at(&(stmt->expr), struct cm_expr *, pe) *
      data_at(&(stmt->a), struct cm_stmt *, pa) *
      data_at(&(stmt->b), struct cm_stmt *, pb) *
      cm_stmt_rep(pa, x)
    */
    result = cmc_stmt_temps(stmt->a);
  } else if (stmt->kind == CMC_STMT_IF) {
    /*@ Assert exists (pe : Z) (pa : Z) (pb : Z) (x : cm_expr) (y : cm_stmt) (z : cm_stmt),
      stmt == stmt@pre &&
      stmt != 0 &&
      cm_rep_stmt_temps_safe(s) &&
      s == CMIfS(x, y, z) &&
      result == 0 &&
      cm_rep_expr_temps_safe(x) &&
      cm_rep_stmt_temps_safe(y) &&
      cm_rep_stmt_temps_safe(z) &&
      data_at(&(stmt->kind), int, cm_rep_stmt_kind(s)) *
      data_at(&(stmt->slot), int, cm_rep_stmt_slot(s)) *
      data_at(&(stmt->expr), struct cm_expr *, pe) *
      data_at(&(stmt->a), struct cm_stmt *, pa) *
      data_at(&(stmt->b), struct cm_stmt *, pb) *
      cm_expr_rep(pe, x) *
      cm_stmt_rep(pa, y) *
      cm_stmt_rep(pb, z)
    */
    int guard_temps = cm_expr_rtemps(stmt->expr);
    int yes_temps = cmc_stmt_temps(stmt->a);
    int no_temps = cmc_stmt_temps(stmt->b);
    int branch_temps = cm_max(yes_temps, no_temps);
    result = cm_max(guard_temps, branch_temps);
  } else if (stmt->kind == CMC_STMT_WHILE) {
    /*@ Assert exists (pe : Z) (pa : Z) (pb : Z) (x : cm_expr) (y : cm_stmt),
      stmt == stmt@pre &&
      stmt != 0 &&
      cm_rep_stmt_temps_safe(s) &&
      s == CMWhileS(x, y) &&
      result == 0 &&
      cm_rep_expr_temps_safe(x) &&
      cm_rep_stmt_temps_safe(y) &&
      pe != 0 &&
      pa != 0 &&
      pb == 0 &&
      data_at(&(stmt->kind), int, cm_rep_stmt_kind(s)) *
      data_at(&(stmt->slot), int, cm_rep_stmt_slot(s)) *
      data_at(&(stmt->expr), struct cm_expr *, pe) *
      data_at(&(stmt->a), struct cm_stmt *, pa) *
      data_at(&(stmt->b), struct cm_stmt *, pb) *
      cm_expr_rep(pe, x) *
      cm_stmt_rep(pa, y)
    */
    int guard_temps = cm_expr_rtemps(stmt->expr);
    int body_temps = cmc_stmt_temps(stmt->a);
    result = cm_max(guard_temps, body_temps);
  } else if (stmt->kind == CMC_STMT_SKIP) {
    result = 0;
  } else if (stmt->kind == CMC_STMT_DECL) {
    result = 0;
  } else if (stmt->kind == CMC_STMT_BREAK) {
    result = 0;
  } else if (stmt->kind == CMC_STMT_CONTINUE) {
    result = 0;
  } else {
    result = 0;
  }
  return result;
}

long long cmc_frame_size(struct cm_function *fn)
/*@ With (params : list cm_slot_d) (zp : Z) (locals : list cm_slot_d) (zl : Z) (body : cm_stmt) (zb : Z)
    Require cm_rep_members_safe(params) && cm_rep_members_safe(locals) && cm_rep_stmt_temps_safe(body) && 8 + cm_rep_members_size(params) + cm_rep_members_size(locals) + 8 * cm_stemps(body) <= 2147483647 && data_at(&(fn->params), struct cm_slot *, zp) * cm_slot_list_rep(zp, params) * data_at(&(fn->locals), struct cm_slot *, zl) * cm_slot_list_rep(zl, locals) * data_at(&(fn->body), struct cm_stmt *, zb) * cm_stmt_rep(zb, body)
    Ensure cm_rep_members_safe(params) && cm_rep_members_safe(locals) && cm_rep_stmt_temps_safe(body) && 8 + cm_rep_members_size(params) + cm_rep_members_size(locals) + 8 * cm_stemps(body) <= 2147483647 && __return == 8 + cm_rep_members_size(params) + cm_rep_members_size(locals) + 8 * cm_stemps(body) && data_at(&(fn->params), struct cm_slot *, zp) * cm_slot_list_rep(zp, params) * data_at(&(fn->locals), struct cm_slot *, zl) * cm_slot_list_rep(zl, locals) * data_at(&(fn->body), struct cm_stmt *, zb) * cm_stmt_rep(zb, body)
*/
{
  long long params_size = cmc_slots_size(fn->params);
  long long locals_size = cmc_slots_size(fn->locals);
  int temps = cmc_stmt_temps(fn->body);
  return 8 + params_size + locals_size + 8LL * temps;
}

long long cmc_param_offset(struct cm_function *fn, int slot)
/*@ With (params : list cm_slot_d) (zp : Z)
    Require cm_rep_members_safe(params) && 0 <= slot && data_at(&(fn->params), struct cm_slot *, zp) * cm_slot_list_rep(zp, params)
    Ensure cm_rep_members_safe(params) && 0 <= slot && __return == 8 + cm_rep_member_prefix(params, slot) && data_at(&(fn->params), struct cm_slot *, zp) * cm_slot_list_rep(zp, params)
*/
{
  long long prefix = cmc_slots_prefix(fn->params, slot);
  return 8 + prefix;
}

long long cmc_local_offset(struct cm_function *fn, int slot)
/*@ With (params : list cm_slot_d) (zp : Z) (locals : list cm_slot_d) (zl : Z)
    Require cm_rep_members_safe(params) && cm_rep_members_safe(locals) && 0 <= slot && data_at(&(fn->params), struct cm_slot *, zp) * cm_slot_list_rep(zp, params) * data_at(&(fn->locals), struct cm_slot *, zl) * cm_slot_list_rep(zl, locals)
    Ensure cm_rep_members_safe(params) && cm_rep_members_safe(locals) && 0 <= slot && __return == 8 + cm_rep_members_size(params) + cm_rep_member_prefix(locals, slot) && data_at(&(fn->params), struct cm_slot *, zp) * cm_slot_list_rep(zp, params) * data_at(&(fn->locals), struct cm_slot *, zl) * cm_slot_list_rep(zl, locals)
*/
{
  long long params_size = cmc_slots_size(fn->params);
  long long prefix = cmc_slots_prefix(fn->locals, slot);
  return 8 + params_size + prefix;
}

long long cmc_temp_offset(struct cm_function *fn, int temp)
/*@ With (params : list cm_slot_d) (zp : Z) (locals : list cm_slot_d) (zl : Z)
    Require cm_rep_members_safe(params) && cm_rep_members_safe(locals) && 0 <= temp && 8 + cm_rep_members_size(params) + cm_rep_members_size(locals) + 8 * temp <= 2147483647 && data_at(&(fn->params), struct cm_slot *, zp) * cm_slot_list_rep(zp, params) * data_at(&(fn->locals), struct cm_slot *, zl) * cm_slot_list_rep(zl, locals)
    Ensure cm_rep_members_safe(params) && cm_rep_members_safe(locals) && 0 <= temp && 8 + cm_rep_members_size(params) + cm_rep_members_size(locals) + 8 * temp <= 2147483647 && __return == 8 + cm_rep_members_size(params) + cm_rep_members_size(locals) + 8 * temp && data_at(&(fn->params), struct cm_slot *, zp) * cm_slot_list_rep(zp, params) * data_at(&(fn->locals), struct cm_slot *, zl) * cm_slot_list_rep(zl, locals)
*/
{
  long long params_size = cmc_slots_size(fn->params);
  long long locals_size = cmc_slots_size(fn->locals);
  return 8 + params_size + locals_size + 8LL * temp;
}

int cm_normalize_count(int ty)
/*@ Require emp
    Ensure __return == cm_normalize_code_value(ty) && emp
*/
{
  int result;
  if (ty == CMC_TYPE_CHAR) {
    result = 6;
  } else {
    result = 0;
  }
  return result;
}
