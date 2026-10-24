#pragma once

#include "proof/proof.h"
#include "cmc_stack_local.h"

PROOF extern thm cm_heights_le_def;
PROOF extern thm cm_heights_le_append;
PROOF extern thm cm_heights_le_mono;
PROOF extern thm cm_imax_bounds;
PROOF extern thm cm_imax_upper;
PROOF extern thm cm_max_arity_nonnegative_from;
PROOF extern thm cm_max_arity_nonnegative;
PROOF extern thm cm_stack_bound_three;
PROOF extern thm cm_heights_le_max;
PROOF extern thm cm_function_arity_le_max_from;
PROOF extern thm cm_function_arity_le_max;
PROOF extern thm cm_fp_address_bounded;
PROOF extern thm cm_temp_access_bounded;
PROOF extern thm cm_normalize_bounded;
PROOF extern thm cm_binding_address_bounded;
PROOF extern thm cm_binary_finish_bounded;
PROOF extern thm cm_return_heights_bounded;
PROOF extern thm cm_prelude_heights_bounded;
PROOF extern thm cm_fixed_prologue_bounded;
PROOF extern thm cm_param_store_heights_bounded;
PROOF extern thm cm_args_reload_heights_bounded;
PROOF extern thm cm_heights_le_cond;
PROOF extern thm cm_lheights_cond;
PROOF extern thm cm_rheights_cond;
PROOF extern thm cm_expr_heights_bounded;
PROOF extern thm cm_stmt_heights_bounded;
PROOF extern thm cm_prologue_heights_bounded;
PROOF extern thm cm_function_heights_bounded;
PROOF extern thm cm_functions_heights_bounded;
PROOF extern thm cm_direct_codegen_bounded;
PROOF extern thm cm_direct_codegen_edges;
PROOF extern thm cm_direct_stack_certificate;
PROOF extern thm cmc_stack_discipline;
