#pragma once

#include "proof/proof.h"
#include "cmc_preservation_target_spill.h"
#include "cmc_preservation_spill_safety.h"

PROOF extern thm cm_target_temp_store_runtime;
PROOF thm get_cm_target_temp_store_runtime(void);
