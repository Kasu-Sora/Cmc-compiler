#pragma once

#include "proof/proof.h"
#include "cmc_preservation_code_control.h"

PROOF extern thm cm_task_layout_ready_def;
PROOF extern thm cm_start_task_layout_step;
PROOF extern thm cm_done_task_layout_step;
PROOF extern thm cm_task_layout_step;
PROOF thm get_cm_task_layout_step(void);
