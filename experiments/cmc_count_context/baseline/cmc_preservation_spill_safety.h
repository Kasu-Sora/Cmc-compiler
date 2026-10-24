#pragma once

#include "proof/proof.h"
#include "cmc_preservation_invariant.h"

PROOF extern thm cm_runtime_spill_metadata_safe;
PROOF extern thm cm_runtime_spill_address_safe;
PROOF extern thm cm_runtime_spill_outside_live;

PROOF thm get_cm_runtime_spill_metadata_safe(void);
PROOF thm get_cm_runtime_spill_address_safe(void);
PROOF thm get_cm_runtime_spill_outside_live(void);
