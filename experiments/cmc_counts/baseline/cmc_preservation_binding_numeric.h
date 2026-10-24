#pragma once

#include "proof/proof.h"
#include "cmc_preservation_invariant_frame.h"

PROOF extern thm cm_local_offset_signed;
PROOF extern thm cm_param_offset_signed;
PROOF extern thm cm_runtime_stack_fid_valid;

PROOF thm get_cm_local_offset_signed(void);
PROOF thm get_cm_param_offset_signed(void);
PROOF thm get_cm_runtime_stack_fid_valid(void);
