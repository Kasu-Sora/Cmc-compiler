#pragma once

#include "proof/proof.h"
#include "cmc_preservation_code_value_linear.h"

PROOF extern thm cm_v_bin_l_layout_step;
PROOF extern thm cm_v_bin_r_layout_step;
PROOF void cm_accept_v_flow_branch(
    const gnode branch, thm rule, const term_list conditions,
    const term old_layout);
