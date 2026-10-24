#pragma once

#include "proof/proof.h"
#include "cmc_preservation_target_value_arg.h"
#include "cmc_preservation_spill_safety.h"

PROOF extern thm cm_forward_spills_def;
PROOF extern thm cm_staged_reverse_spills;
PROOF extern thm cm_target_args_reload;

PROOF thm get_cm_forward_spills_def(void);
PROOF thm get_cm_staged_reverse_spills(void);
PROOF thm get_cm_target_args_reload(void);
