#pragma once

#include "proof/proof.h"
#include "cmc_preservation_target_machine.h"

PROOF extern thm cm_target_temp_load;
PROOF thm get_cm_target_temp_load(void);
PROOF extern thm cm_target_temp_store;
PROOF thm get_cm_target_temp_store(void);
