#pragma once

#include "proof/proof.h"

PROOF extern thm cm_spills_within_holds_bounds;
PROOF extern thm cm_runtime_spill_holds_address_safe;

PROOF thm get_cm_spills_within_holds_bounds(void);
PROOF thm get_cm_runtime_spill_holds_address_safe(void);
