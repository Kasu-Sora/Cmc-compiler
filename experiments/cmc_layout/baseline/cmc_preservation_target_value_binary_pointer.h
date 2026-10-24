#pragma once

#include "proof/proof.h"

PROOF extern thm cm_target_v_bin_r_add_right_pointer_step;
PROOF extern thm cm_target_v_bin_r_add_left_pointer_step;
PROOF extern thm cm_target_v_bin_r_subtract_pointers_step;
PROOF extern thm cm_target_v_bin_r_subtract_pointer_number_step;

PROOF thm get_cm_target_v_bin_r_add_right_pointer_step(void);
PROOF thm get_cm_target_v_bin_r_add_left_pointer_step(void);
PROOF thm get_cm_target_v_bin_r_subtract_pointers_step(void);
PROOF thm get_cm_target_v_bin_r_subtract_pointer_number_step(void);
