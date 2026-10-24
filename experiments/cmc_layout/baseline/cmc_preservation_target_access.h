#pragma once

#include "proof/proof.h"
#include "cmc_preservation_runtime.h"

PROOF extern thm cm_pointer_live_region_witness;
PROOF extern thm cm_pointer_live_number;
PROOF extern thm cm_runtime_pointer_live_span;

PROOF thm get_cm_pointer_live_region_witness(void);
PROOF thm get_cm_pointer_live_number(void);
PROOF thm get_cm_runtime_pointer_live_span(void);
