#pragma once

#include "proof/proof.h"
#include "cmc_preservation_call_param.h"

PROOF extern thm cm_state_store_commute;
PROOF extern thm cm_slot_cells_disjoint;


PROOF thm get_cm_state_store_commute(void);
PROOF thm get_cm_slot_cells_disjoint(void);
