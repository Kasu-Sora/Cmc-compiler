#pragma once

#include "proof/proof.h"
#include "cmc_preservation_call_clear.h"
#include "cmc_preservation_call_params_permute.h"

PROOF extern thm cm_store_params_absorb_clear;
PROOF extern thm cm_pending_params_enter_call;

PROOF thm get_cm_store_params_absorb_clear(void);
PROOF thm get_cm_pending_params_enter_call(void);
