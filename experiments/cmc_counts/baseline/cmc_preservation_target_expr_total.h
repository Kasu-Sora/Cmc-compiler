#pragma once

#include "proof/proof.h"
#include "cmc_preservation_target_expr.h"
#include "cmc_preservation_static_bases.h"

PROOF extern thm cm_target_r_step;
PROOF extern thm cm_target_l_step;

PROOF thm get_cm_target_r_step(void);
PROOF thm get_cm_target_l_step(void);
