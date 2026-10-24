#pragma once

#include "proof/proof.h"
#include "cmc_preservation_target_access.h"
#include "cmc_preservation_fid.h"
#include "cmc_preservation_type_source_v_support.h"
#include "cmc_preservation_spill_semantic.h"
#include "cmc_preservation_invariant_transition.h"

PROOF extern thm cm_target_v_context;
PROOF thm get_cm_target_v_context(void);
