#pragma once

#include "proof/proof.h"
#include "cmc_preservation_call_pending.h"

PROOF extern thm cm_spills_generation_below_def;
PROOF extern thm cm_spill_frames_generation_below_def;
PROOF extern thm cm_state_tags_generation_below_def;
PROOF extern thm cm_spill_list_sim_bases;
PROOF extern thm cm_spill_frames_sim_bases;
PROOF extern thm cm_operand_suffix_sim_bases;

PROOF thm get_cm_spills_generation_below_def(void);
PROOF thm get_cm_spill_frames_generation_below_def(void);
PROOF thm get_cm_state_tags_generation_below_def(void);
PROOF thm get_cm_spill_list_sim_bases(void);
PROOF thm get_cm_spill_frames_sim_bases(void);
PROOF thm get_cm_operand_suffix_sim_bases(void);
