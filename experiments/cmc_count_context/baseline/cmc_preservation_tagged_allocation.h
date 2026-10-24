#pragma once

#include "proof/proof.h"
#include "cmc_preservation_tagged.h"
#include "cmc_preservation_invariant_step.h"

PROOF extern thm cm_live_span_forward;
PROOF extern thm cm_tagged_span_clear_extension;
PROOF extern thm cm_activate_live_old;
PROOF extern thm cm_activate_live_old_or_local;
PROOF extern thm cm_tagged_span_activate_local;
