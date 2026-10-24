#pragma once

#include "proof/proof.h"
#include "cmc_preservation_store_provenance.h"

PROOF extern thm cm_call_frames_store_safe_def;
PROOF extern thm cm_spill_list_store_safe_def;
PROOF extern thm cm_spill_frames_store_safe_def;
PROOF extern thm cm_machine_store_safe_def;
PROOF extern thm cm_encode_values_state_store;
PROOF extern thm cm_call_frames_store_sim;
PROOF extern thm cm_spill_list_store_sim;
PROOF extern thm cm_spill_frames_store_sim;

PROOF thm get_cm_call_frames_store_safe_def(void);
PROOF thm get_cm_spill_list_store_safe_def(void);
PROOF thm get_cm_spill_frames_store_safe_def(void);
PROOF thm get_cm_machine_store_safe_def(void);
PROOF thm get_cm_encode_values_state_store(void);
PROOF thm get_cm_call_frames_store_sim(void);
PROOF thm get_cm_spill_list_store_sim(void);
PROOF thm get_cm_spill_frames_store_sim(void);
