#pragma once

#include "proof/proof.h"
#include "cmc_preservation_call_finish.h"

PROOF extern thm cm_param_store_context_def;
PROOF extern thm cm_parameter_state_store_def;
PROOF extern thm cm_parameter_offsets_disjoint;
PROOF extern thm cm_parameter_pointer_number;
PROOF extern thm cm_param_store_context_store;

PROOF thm get_cm_param_store_context_def(void);
PROOF thm get_cm_parameter_state_store_def(void);
PROOF thm get_cm_parameter_offsets_disjoint(void);
PROOF thm get_cm_parameter_pointer_number(void);
PROOF thm get_cm_param_store_context_store(void);
