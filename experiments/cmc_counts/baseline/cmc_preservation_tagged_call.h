#pragma once

#include "proof/proof.h"
#include "cmc_preservation_tagged_allocation.h"
#include "cmc_preservation_call_pending_live.h"
#include "cmc_preservation_target_call_params.h"

PROOF extern thm cm_call_pending_live_old;
PROOF extern thm cm_tagged_span_call_pending;
PROOF extern thm cm_param_stores_ok_def;
PROOF extern thm cm_tagged_span_store_params_reverse;
