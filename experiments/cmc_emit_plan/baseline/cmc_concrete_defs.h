#pragma once

#include "cmc_abi.h"

#require "cmc_abi.c"

struct cm_emitter {
  struct cm_output *output;
  int pc;
};

#include "proof/proof.h"

#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "userlib/operational.h"
#include "cmc_rep.h"
#include "cmc_temp_algebra.h"
#include "cmc_stack_annotations.h"
#include "cmc_stack_local_core.h"

PROOF extern thm cm_binding_array_code_def;
PROOF extern thm cm_member_array_code_def;
PROOF extern thm cm_binding_array_code_zero;
PROOF extern thm cm_binding_array_code_nonzero;
PROOF extern thm cm_char_encode;
PROOF extern thm cm_expr_code_for_def;
PROOF extern thm cm_expr_load_suffix_def;
PROOF extern thm cm_member_load_suffix_def;
PROOF extern thm cm_expr_temps_for_def;
PROOF extern thm cm_leaf_expr_def;
PROOF extern thm cm_char_normalize_bridge;
PROOF extern thm cm_char_normalize_nonnegative;
PROOF extern thm cm_simple_expr_def;
PROOF extern thm cm_emitter_plan_rep_def;
PROOF extern thm cm_patch_code_append;
PROOF extern thm cm_patch_code_def;
PROOF extern thm cm_intrinsic_expr_def;
PROOF extern thm cm_patch_code_length;
PROOF extern thm cm_patch_inst_def;
PROOF extern thm cm_resolved_emitter_rep_def;
PROOF extern thm cm_resolved_emitter_plan_rep_def;
PROOF void cm_open_program_context_st(void);
PROOF void cm_close_program_context_st(void);
PROOF void cm_open_function_context_st(void);
PROOF void cm_close_function_context_st(void);
PROOF void cm_add_opcode_facts_st(
    const term concrete, const term opcode);
PROOF void cm_retarget_i64_st(const term cell, const thm result);
PROOF void cm_add_count_facts(const thm theorem);
PROOF thm cm_first_expr_count_node_fact(const thm theorem);
PROOF extern thm cm_expr_counts_node;
PROOF void cm_open_expr_count_facts(const thm shape);
PROOF void cm_open_expr_rep_st(void);
PROOF void cm_open_single_child_count_payload(const thm shape);
PROOF void cm_close_single_child_count_payload(const thm shape);
PROOF void cm_open_two_child_count_payload(const thm shape);
PROOF void cm_close_two_child_count_payload(const thm shape);
PROOF void cm_plan_open(const term fragment);
PROOF void cm_plan_close(const term fragment);
PROOF void cm_select_code_plan_st(const thm code_shape);
PROOF void cm_restore_code_plan_st(const thm code_shape);
PROOF void cm_restore_code_plan_end_st(const thm code_shape);
PROOF void cm_empty_code_plan_end_st(const thm code_shape);
PROOF void cm_close_expr_rep_st(void);
PROOF void cm_add_temp_offset_bound_st(const term at);
PROOF extern thm cm_temp_offset_mono;
PROOF extern thm cm_emitter_rep_def;
PROOF extern thm cm_function_context_cons_close;
PROOF extern thm cm_function_context_cons_open;
PROOF thm cm_function_context_fold_hconv(
    const term function_ptr, const term descriptor,
    const term body_ptr, const term next_ptr,
    const term params_ptr, const term locals_ptr);
PROOF extern thm cm_function_context_rep_def;
PROOF extern thm cm_function_list_nonnull_shape;
PROOF extern thm cm_function_list_null_shape;
PROOF extern thm cm_functions_code_size_nonnegative;
PROOF extern thm cm_functions_length_le_code_size;
PROOF extern thm cm_normalize_code_value_def;
PROOF extern thm cm_pointer_code_bridge;
PROOF extern thm cm_pointer_code_value_cases;
PROOF extern thm cm_pointer_encode_threshold;
PROOF extern thm cm_pointer_encode_pointee;
PROOF extern thm cm_type_refs_pointee;
PROOF extern thm cm_type_code_wf_pointee;
PROOF thm cm_program_context_fold_hconv(
    const term root, const term program,
    const term functions_ptr, const term structs_ptr,
    const term globals_ptr, const term strings_ptr);
PROOF extern thm cm_program_context_rep_def;
PROOF extern thm cm_rep_imms_append;
PROOF extern thm cm_rep_ops_append;
PROOF extern thm cm_rep_ops_length;
PROOF extern thm cm_slots_wf_head;
PROOF extern thm cm_slots_wf_tail;
PROOF extern thm cm_rep_members_size_matches;
PROOF extern thm cm_rep_struct_member_size_matches;
PROOF extern thm cm_rep_struct_members_size_matches;
PROOF extern thm cm_rep_struct_size_at;
PROOF extern thm cm_rep_struct_size_matches;
PROOF extern thm cm_rep_type_size_matches;
PROOF extern thm cm_rep_member_prefix_matches;
PROOF extern thm cm_rep_struct_member_prefix_slots_matches;
PROOF extern thm cm_rep_struct_member_prefix_at;
PROOF extern thm cm_rep_struct_member_prefix_matches;
PROOF extern thm cm_rep_global_size_matches;
PROOF extern thm cm_globals_wf_head;
PROOF extern thm cm_globals_wf_tail;
PROOF extern thm cm_type_encode_nonnegative;
PROOF extern thm cm_rep_globals_prefix_matches;
PROOF extern thm cm_rep_globals_size_matches;
PROOF extern thm cm_rep_strings_prefix_matches;
PROOF extern thm cm_rep_member_size_matches;
PROOF extern thm cm_rep_string_address_matches;
PROOF thm cmc_code_slot_nonzero_case(void);
PROOF thm cmc_code_slot_zero_case(void);
PROOF extern thm cm_expr_result_refs;
PROOF thm cmc_leaf_cases(void);
PROOF thm cmc_leaf_char_case(void);
PROOF thm cmc_leaf_int_case(void);
PROOF thm cmc_leaf_other_case(void);
PROOF thm cmc_leaf_pointer_case(void);
PROOF thm cmc_pointer_code_false(void);
PROOF thm cmc_pointer_code_true(void);
