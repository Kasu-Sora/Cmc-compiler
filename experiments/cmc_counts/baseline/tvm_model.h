#pragma once

#include "proof/proof.h"
#include "tower_base.h"

/* Resolved TVM object, loader, transition, and termination proofs. */
PROOF thm get_tvm_opcode_recursion(void);
PROOF thm get_tvm_inst_recursion(void);
PROOF thm get_tvm_patch_recursion(void);
PROOF thm get_tvm_object_recursion(void);
PROOF thm get_tvm_state_recursion(void);
PROOF thm get_tvm_task_recursion(void);
PROOF thm get_tvm_outcome_recursion(void);

PROOF thm get_tvm_opcode_code_def(void);
PROOF thm get_tvm_opcode_decode_def(void);
PROOF thm get_tvm_opcode_roundtrip(void);
PROOF thm get_tvm_opcode_code_range(void);
PROOF thm get_tvm_inst_op_def(void);
PROOF thm get_tvm_inst_imm_def(void);
PROOF thm get_tvm_patch_addr_def(void);
PROOF thm get_tvm_patch_byte_def(void);
PROOF thm get_tvm_object_entry_def(void);
PROOF thm get_tvm_object_code_def(void);
PROOF thm get_tvm_object_patches_def(void);
PROOF thm get_tvm_state_selectors_def(void);

PROOF thm get_tvm_target_valid_def(void);
PROOF thm get_tvm_opcode_has_imm_def(void);
PROOF thm get_tvm_opcode_is_target_def(void);
PROOF thm get_tvm_inst_shape_def(void);
PROOF thm get_tvm_patch_valid_def(void);
PROOF thm get_tvm_patches_valid_def(void);
PROOF thm get_tvm_code_shape_def(void);
PROOF thm get_tvm_targets_valid_def(void);
PROOF thm get_tvm_load_ok_def(void);
PROOF thm get_tvm_object_wf_def(void);
PROOF thm get_tvm_apply_patches_def(void);
PROOF thm get_tvm_initial_state_def(void);
PROOF thm get_tvm_unloaded_state_def(void);
PROOF thm get_tvm_next_state_def(void);
PROOF thm get_tvm_jump_state_def(void);
PROOF thm get_tvm_decode_pair_valid_def(void);
PROOF thm get_tvm_decode_pair_def(void);
PROOF thm get_tvm_decode_encode_inst(void);
PROOF thm get_tvm_inst_reconstruct(void);
PROOF thm get_tvm_object_wf_load(void);

PROOF thm get_tvm_inst_step_def(void);
PROOF thm get_tvm_push_transition(void);
PROOF thm get_tvm_pop_transition(void);
PROOF thm get_tvm_dup_transition(void);
PROOF thm get_tvm_swap_transition(void);
PROOF thm get_tvm_load_transition(void);
PROOF thm get_tvm_store_transition(void);
PROOF thm get_tvm_loadb_transition(void);
PROOF thm get_tvm_storeb_transition(void);
PROOF thm get_tvm_add_transition(void);
PROOF thm get_tvm_sub_transition(void);
PROOF thm get_tvm_mul_transition(void);
PROOF thm get_tvm_div_transition(void);
PROOF thm get_tvm_mod_transition(void);
PROOF thm get_tvm_eq_transition(void);
PROOF thm get_tvm_ne_transition(void);
PROOF thm get_tvm_lt_transition(void);
PROOF thm get_tvm_le_transition(void);
PROOF thm get_tvm_gt_transition(void);
PROOF thm get_tvm_ge_transition(void);
PROOF thm get_tvm_jmp_transition(void);
PROOF thm get_tvm_jz_transition(void);
PROOF thm get_tvm_jnz_transition(void);
PROOF thm get_tvm_call_transition(void);
PROOF thm get_tvm_ret_transition(void);
PROOF thm get_tvm_getc_transition(void);
PROOF thm get_tvm_putc_transition(void);
PROOF thm get_tvm_puti_transition(void);
PROOF thm get_tvm_halt_transition(void);

PROOF thm get_tvm_step_def(void);
PROOF thm get_tvm_action_task_def(void);
PROOF thm get_tvm_iter_def(void);
PROOF thm_list get_tvm_eval_defs(void);
PROOF thm get_tvm_step_deterministic(void);
PROOF thm get_tvm_exec_def(void);
PROOF thm get_tvm_exec_done(void);
PROOF thm get_tvm_exec_rule(void);
PROOF thm get_tvm_exec_prefix(void);
PROOF thm get_tvm_deterministic(void);
PROOF thm get_tvm_terminates_def(void);
PROOF thm get_tvm_errors_def(void);
PROOF thm get_tvm_malformed_def(void);
PROOF thm get_tvm_load_rejects(void);
PROOF thm get_tvm_runtime_pc_error(void);
PROOF thm get_tvm_edge_semantics(void);
