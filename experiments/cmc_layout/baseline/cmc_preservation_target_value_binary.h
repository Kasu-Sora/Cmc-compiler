#pragma once

#include "proof/proof.h"

PROOF extern thm cm_target_v_bin_l_eval_zero_step;
PROOF extern thm cm_target_v_bin_l_eval_one_step;
PROOF extern thm cm_target_v_bin_l_short_zero_step;
PROOF extern thm cm_target_v_bin_l_short_one_step;
PROOF extern thm cm_target_v_bin_l_other_step;
PROOF extern thm cm_target_v_bin_r_zero_step;
PROOF extern thm cm_target_v_bin_r_one_step;

PROOF thm get_cm_target_v_bin_l_eval_zero_step(void);
PROOF thm get_cm_target_v_bin_l_eval_one_step(void);
PROOF thm get_cm_target_v_bin_l_short_zero_step(void);
PROOF thm get_cm_target_v_bin_l_short_one_step(void);
PROOF thm get_cm_target_v_bin_l_other_step(void);
PROOF thm get_cm_target_v_bin_r_zero_step(void);
PROOF thm get_cm_target_v_bin_r_one_step(void);
