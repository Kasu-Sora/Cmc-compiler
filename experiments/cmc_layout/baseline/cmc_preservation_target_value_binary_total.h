#pragma once

#include "proof/proof.h"

PROOF extern thm cm_referenced_type_size_fixed;
PROOF extern thm cm_target_v_bin_l_jump_valid;
PROOF extern thm cm_target_v_bin_l_total_step;
PROOF extern thm cm_target_v_bin_r_end_valid;
PROOF extern thm cm_target_v_bin_r_total_step;
PROOF extern thm cm_target_v_binary_step;

PROOF thm get_cm_referenced_type_size_fixed(void);
PROOF thm get_cm_target_v_bin_l_jump_valid(void);
PROOF thm get_cm_target_v_bin_l_total_step(void);
PROOF thm get_cm_target_v_bin_r_end_valid(void);
PROOF thm get_cm_target_v_bin_r_total_step(void);
PROOF thm get_cm_target_v_binary_step(void);
