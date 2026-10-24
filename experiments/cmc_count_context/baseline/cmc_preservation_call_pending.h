#pragma once

#include "proof/proof.h"
#include "cmc_preservation_call_value.h"
#include "cmc_preservation_invariant_frame.h"

PROOF extern thm cm_call_param_span_def;
PROOF extern thm cm_call_pending_base_def;
PROOF extern thm cm_store_params_reverse_def;
PROOF extern thm cm_call_pending_structure;
PROOF extern thm cm_store_params_reverse_structure;
PROOF extern thm cm_call_pending_regions_bases;

PROOF thm get_cm_call_param_span_def(void);
PROOF thm get_cm_call_pending_base_def(void);
PROOF thm get_cm_store_params_reverse_def(void);
PROOF thm get_cm_call_pending_structure(void);
PROOF thm get_cm_store_params_reverse_structure(void);
PROOF thm get_cm_call_pending_regions_bases(void);
