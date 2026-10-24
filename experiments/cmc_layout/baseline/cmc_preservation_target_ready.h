#pragma once

#include "proof/proof.h"
#include "cmc_preservation_target_call_complete.h"
#include "cmc_preservation_binding_numeric.h"

PROOF extern thm cm_call_target_ready_def;
PROOF extern thm cm_function_arity_le_max;
PROOF extern thm cm_runtime_calls_depth;
PROOF extern thm cm_target_call_ready;

PROOF thm get_cm_function_arity_le_max(void);
PROOF thm get_cm_runtime_calls_depth(void);
PROOF thm get_cm_target_call_ready(void);

PROOF thm get_cm_scratch_outside_live(void);
