#pragma once

#include "proof/proof.h"
#include "cmc_preservation_call_finish.h"

PROOF extern thm cm_state_clear_range_def;
PROOF extern thm cm_state_clear_range_join;
PROOF extern thm cm_state_store_absorb_clear;
PROOF extern thm cm_state_store_clear_commute;

PROOF thm get_cm_state_clear_range_def(void);
PROOF thm get_cm_state_clear_range_join(void);
PROOF thm get_cm_state_store_absorb_clear(void);
PROOF thm get_cm_state_store_clear_commute(void);
