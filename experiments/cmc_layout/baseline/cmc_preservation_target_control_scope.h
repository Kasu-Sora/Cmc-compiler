#pragma once

#include "proof/proof.h"
#include "cmc_preservation_target_restore.h"
#include "cmc_preservation_target_jump_valid.h"

PROOF extern thm cm_target_c_scope_step;
PROOF thm get_cm_target_c_scope_step(void);
