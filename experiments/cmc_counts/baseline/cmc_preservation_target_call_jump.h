#pragma once

#include "proof/proof.h"
#include "cmc_preservation_target_machine.h"

PROOF extern thm cm_ann_call_jump_def;
PROOF extern thm cm_call_frames_sim_length;
PROOF extern thm cm_machine_call_jump;
PROOF extern thm cm_target_call_jump;

PROOF thm get_cm_ann_call_jump_def(void);
PROOF thm get_cm_call_frames_sim_length(void);
PROOF thm get_cm_machine_call_jump(void);
PROOF thm get_cm_target_call_jump(void);
