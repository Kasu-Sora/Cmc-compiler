#pragma once

#include "proof/proof.h"
#include "cmc_preservation_call_params_order.h"

PROOF extern thm cm_parameter_state_store_commute;
PROOF extern thm cm_store_params_push_parameter;
PROOF extern thm cm_store_params_reverse_forward;

PROOF thm get_cm_parameter_state_store_commute(void);
PROOF thm get_cm_store_params_push_parameter(void);
PROOF thm get_cm_store_params_reverse_forward(void);
