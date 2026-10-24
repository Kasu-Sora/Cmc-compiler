#pragma once

#include "proof/proof.h"
#include "cmc_preservation_target_value_control.h"

PROOF extern thm cm_target_v_if_step;
PROOF extern thm cm_target_v_while_guard_step;

PROOF thm get_cm_target_v_if_step(void);
PROOF thm get_cm_target_v_while_guard_step(void);
