#pragma once

#include "proof/proof.h"
#include "cmc_annotate.h"
#include "cmc_sim_ops.h"

PROOF extern thm cm_active_spill_frames_def;
PROOF extern thm cm_running_target_sim_def;
PROOF extern thm cm_halted_target_sim_def;
PROOF extern thm cm_task_target_sim_def;
PROOF extern thm cm_astate_sim_def;
PROOF extern thm cm_task_succeeds_def;
PROOF extern thm cm_done_target_observation;

PROOF thm get_cm_task_target_sim_def(void);
PROOF thm get_cm_astate_sim_def(void);
PROOF thm get_cm_task_succeeds_def(void);
PROOF thm get_cm_done_target_observation(void);
