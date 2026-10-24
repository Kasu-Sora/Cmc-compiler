#pragma once

#include "proof/proof.h"
#include "cmc_lang.h"

PROOF thm cmc_imax_le_case(void);
PROOF thm cmc_imax_gt_case(void);
PROOF extern thm cm_imax_left_bound;
PROOF extern thm cm_imax_right_bound;
PROOF extern thm cm_imax_nonnegative;
PROOF extern thm cm_expr_temps_nonnegative;
PROOF extern thm cm_args_temps_nonnegative;
PROOF extern thm cm_ltemps_nonnegative;
PROOF extern thm cm_rtemps_nonnegative;
PROOF extern thm cm_acount_nonnegative;
PROOF extern thm cm_adepth_nonnegative;
PROOF extern thm cm_args_count_matches_length;
PROOF extern thm cm_adepth_head_bound;
PROOF extern thm cm_adepth_tail_bound;
