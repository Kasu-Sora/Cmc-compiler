#pragma once

#include "proof/proof.h"
#include "cmc_stack_annotations.h"

PROOF extern thm cm_local_next_def;
PROOF extern thm cm_local_head_ok_def;
PROOF extern thm cm_local_codegen_ok_def;
PROOF extern thm cm_height_stream_def;
PROOF extern thm cm_function_target_heights_def;
PROOF extern thm cm_height_stream_tail;
PROOF extern thm cm_stream_next_at;
PROOF extern thm cm_local_head_sound;
PROOF extern thm cm_local_codegen_edges;
PROOF extern thm cm_inth_cons_tail;
PROOF extern thm cm_function_entries_at;
PROOF extern thm cm_function_arities_at;
PROOF extern thm cm_function_arities_length;
PROOF extern thm cm_local_call_listed;
PROOF extern thm cm_local_codegen_calls;
PROOF extern thm cm_codegen_entries_at;
PROOF extern thm cm_codegen_arities_at;
PROOF extern thm cm_codegen_entries_length;
PROOF extern thm cm_codegen_entries_function_length;
PROOF extern thm cm_codegen_call_sites;
PROOF extern thm cm_height_stream_drop;
PROOF extern thm cm_local_codegen_cons;
PROOF extern thm cm_binary_opcode_noncall;
PROOF extern thm cm_binary_opcode_head;
PROOF extern thm cm_inth_zero_cons;
PROOF extern thm cm_height_stream_head;
PROOF extern thm cm_stream_local_next;
PROOF extern thm cm_args_wf_length;
PROOF extern thm cm_local_push_fragment;
PROOF extern thm cm_local_fp_address;
PROOF extern thm cm_local_temp_store;
PROOF extern thm cm_local_temp_load;
PROOF extern thm cm_local_char_normalize;
PROOF extern thm cm_local_load;
PROOF extern thm cm_local_store;
PROOF extern thm cm_local_binding_address;
PROOF extern thm cm_local_return_epilogue;
PROOF extern thm cm_local_binary_finish;
PROOF extern thm cm_args_reload_starts;
PROOF extern thm cm_local_args_reload;

PROOF thm cm_pick_conjunct(const thm fact, const term wanted);
PROOF thm cm_matching_assumption(const gnode leaf, const term wanted);
PROOF thm cm_local_fixed(
    const term p, const term target,
    const term instructions, const term annotations,
    const term tail, const term tail_annotations,
    const thm tail_ok, const thm boundary,
    const thm_list facts);
PROOF bool cm_term_head_named(const term tm, const char *name);
PROOF thm cm_predicate_assumption(const gnode branch, const char *name);
PROOF thm cm_expr_start_ih(
    const gnode branch, const term expr, bool lvalue,
    const term suffix, const thm boundary);
PROOF thm cm_args_start_ih(
    const gnode branch, const term args, const term slots,
    const term suffix, const thm boundary);
PROOF thm cm_fixed_local_next(
    const term annotations, const term height,
    const thm_list extra_rules);
