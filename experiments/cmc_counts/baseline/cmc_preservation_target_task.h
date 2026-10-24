#pragma once

#include "proof/proof.h"
#include "cmc_preservation_target_start.h"
#include "cmc_preservation_target_expr_total.h"
#include "cmc_preservation_target_stmt.h"
#include "cmc_preservation_target_value_total.h"
#include "cmc_preservation_target_control_total.h"
#include "cmc_preservation_target_control_halt.h"
#include "cmc_preservation_source.h"

PROOF extern thm cm_target_task_step;
PROOF thm get_cm_target_task_step(void);
