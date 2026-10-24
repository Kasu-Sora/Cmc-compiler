#pragma once

#include "proof/proof.h"
#include "cmc_preservation_code_value.h"

PROOF thm_list cm_v_layout_rules(void);
PROOF thm cm_prove_v_linear_layout_step(
    const term statement, const term task, const term annotation,
    const term prefix, const term_list conditions,
    const thm_list extra_rules);
