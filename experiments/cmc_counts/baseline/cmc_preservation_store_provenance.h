#pragma once

#include "proof/proof.h"
#include "cmc_preservation_store_memory.h"

PROOF extern thm cm_value_number_state_store;
PROOF extern thm cm_stored_provenance_store_sim;

PROOF thm get_cm_value_number_state_store(void);
PROOF thm get_cm_stored_provenance_store_sim(void);
