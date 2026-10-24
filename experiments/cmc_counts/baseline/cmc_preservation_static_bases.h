#pragma once

#include "proof/proof.h"
#include "cmc_preservation_generation_task.h"
#include "cmc_preservation_invariant_step.h"

PROOF extern thm cm_task_static_bases_def;
PROOF extern thm cm_task_static_bases_initial;
PROOF extern thm cm_task_static_bases_string_number;

PROOF thm get_cm_task_static_bases_def(void);
PROOF thm get_cm_task_static_bases_initial(void);
PROOF thm get_cm_task_static_bases_string_number(void);
