#pragma once

#include "proof/proof.h"
#include "cmc_preservation_store_metadata.h"

PROOF extern thm cm_machine_store;
PROOF extern thm cm_machine_spill_store;

PROOF thm get_cm_machine_store(void);
PROOF thm get_cm_machine_spill_store(void);
PROOF thm get_cm_initialized_scratch_store_sim(void);
PROOF thm get_cm_provenance_scratch_store_sim(void);
PROOF thm get_cm_spill_frames_scratch_store_sim(void);
