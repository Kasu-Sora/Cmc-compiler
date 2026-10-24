#pragma once

#include "proof/proof.h"
#include "cmc_preservation_machine_ops.h"
#include "cmc_sim_ops.h"

PROOF extern thm cm_machine_load;
PROOF thm get_cm_machine_load(void);
PROOF extern thm cm_machine_load_fp;
PROOF thm get_cm_machine_load_fp(void);
PROOF extern thm cm_spill_list_sim_holds;
PROOF extern thm cm_machine_spill_load;
PROOF thm get_cm_machine_spill_load(void);
