#pragma once

#include "proof/proof.h"
#include "cmc_preservation_target_state.h"
#include "cmc_preservation_generation.h"
#include "cmc_preservation_binding_numeric.h"

PROOF extern thm cm_target_s_step;
PROOF thm get_cm_target_s_step(void);
