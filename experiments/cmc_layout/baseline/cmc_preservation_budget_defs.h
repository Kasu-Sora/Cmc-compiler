#pragma once

#include "proof/proof.h"
#include "cmc_annotate_model.h"

PROOF extern thm cm_phase_budget_def;
PROOF extern thm cm_cursors_budget_def;
PROOF extern thm cm_task_budget_def;

PROOF thm get_cm_phase_budget_def(void);
PROOF thm get_cm_cursors_budget_def(void);
PROOF thm get_cm_task_budget_def(void);
