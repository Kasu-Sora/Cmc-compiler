#pragma once

#include "proof/proof.h"
#include "cmc_stack_local_core.h"

PROOF extern thm cm_binding_heights_start;
PROOF extern thm cm_binding_heights_start_nested;
PROOF extern thm cm_codegen_height_starts;
PROOF extern thm cm_normalize_heights_start;
PROOF extern thm cm_expr_local_codegen;
PROOF extern thm cm_stmt_height_starts;
PROOF extern thm cm_stmt_local_codegen;
PROOF extern thm cm_local_param_stores;
PROOF extern thm cm_param_store_heights_start;
PROOF extern thm cm_local_prologue;
PROOF extern thm cm_local_function;
PROOF extern thm cm_function_prefix_zero;
PROOF extern thm cm_function_prefix_step;
PROOF extern thm cm_function_pc_step;
PROOF extern thm cm_local_functions;
PROOF extern thm cm_identity_height_stream;
PROOF extern thm cm_direct_target_heights;
PROOF extern thm cm_direct_target_zero;
PROOF extern thm cm_function_pc_zero;
PROOF extern thm cm_direct_functions_stream;
PROOF extern thm cm_direct_functions_local;
PROOF extern thm cm_direct_codegen_local;
