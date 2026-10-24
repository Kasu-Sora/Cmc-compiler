#pragma once

#include "proof/proof.h"

PROOF extern thm cm_error_task_def;
PROOF extern thm cm_error_task_step;
PROOF extern thm cm_error_outcome_def;
PROOF extern thm cm_error_exec;
PROOF extern thm cm_task_succeeds_step;
PROOF extern thm cm_task_succeeds_not_error;
PROOF extern thm cm_done_succeeds;

PROOF thm get_cm_error_exec(void);
PROOF thm get_cm_task_succeeds_step(void);
PROOF thm get_cm_done_succeeds(void);
