#pragma once

#include "proof/proof.h"
#include "cmc_preservation_runtime.h"
#include "cmc_preservation_store_provenance.h"

PROOF extern thm cm_state_store_converted;
PROOF thm get_cm_state_store_converted(void);
PROOF extern thm cm_store_runtime_layout;
PROOF thm get_cm_store_runtime_layout(void);
PROOF extern thm cm_store_live_span;
PROOF thm get_cm_store_live_span(void);
PROOF extern thm cm_store_load_ok;
PROOF thm get_cm_store_load_ok(void);
PROOF extern thm cm_store_load_number;
PROOF thm get_cm_store_load_number(void);
