#pragma once

#include "proof/proof.h"
#include "cmc_preservation_target_machine.h"

PROOF extern thm cm_target_v_load_step;
PROOF thm get_cm_target_v_load_step(void);
PROOF extern thm cm_target_v_assign_left_step;
PROOF thm get_cm_target_v_assign_left_step(void);
PROOF extern thm cm_target_v_assign_right_step;
PROOF thm get_cm_target_v_assign_right_step(void);
