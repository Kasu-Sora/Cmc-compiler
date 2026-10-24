#pragma once

#include "proof/proof.h"
#include "cmc_preservation_call_params_complete.h"
#include "cmc_preservation_target_call_pending.h"
#include "cmc_preservation_target_call_params.h"

PROOF extern thm cm_target_call_complete;
PROOF thm get_cm_target_call_complete(void);
