#pragma once

#include "proof/proof.h"
#include "cmc_preservation_type_ready.h"

PROOF extern thm cm_scalar_type_is_expr_type;
PROOF extern thm cm_convertible_scalar_types;
PROOF extern thm cm_typed_function_at;
PROOF extern thm cm_expr_convertible_source_scalar;
PROOF extern thm cm_stmt_wf_loop_mono;
PROOF extern thm cm_args_wf_exprs;
PROOF extern thm cm_value_type_compatible_refl;
PROOF extern thm cm_pointer_value_view;
PROOF extern thm cm_referenced_type_size_signed;
PROOF thm get_cm_referenced_type_size_signed(void);
