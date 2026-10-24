#pragma once

#include "proof/proof.h"
#include "cmc_preservation_target_address.h"

PROOF extern thm cm_target_r_const_step;
PROOF thm get_cm_target_r_const_step(void);
PROOF extern thm cm_target_r_string_step;
PROOF thm get_cm_target_r_string_step(void);
PROOF extern thm cm_target_r_array_step;
PROOF thm get_cm_target_r_array_step(void);
PROOF extern thm cm_target_l_var_step;
PROOF thm get_cm_target_l_var_step(void);
PROOF thm get_cm_target_r_sizeof_step(void);
PROOF thm get_cm_target_r_getc_step(void);
PROOF thm get_cm_target_r_assign_step(void);
PROOF thm get_cm_target_r_binary_start_step(void);
PROOF thm get_cm_target_r_index_start_step(void);
PROOF thm get_cm_target_r_putc_start_step(void);
PROOF thm get_cm_target_r_puti_start_step(void);
PROOF thm get_cm_target_r_exit_start_step(void);
PROOF thm get_cm_target_r_var_scalar_step(void);
PROOF thm get_cm_target_r_unary_load_start_step(void);
PROOF thm get_cm_target_r_unary_address_start_step(void);
PROOF thm get_cm_target_r_unary_value_start_step(void);
PROOF thm get_cm_target_r_member_array_start_step(void);
PROOF thm get_cm_target_r_member_scalar_start_step(void);
PROOF thm get_cm_target_r_call_args_start_step(void);
PROOF thm get_cm_target_r_empty_call_step(void);
PROOF thm get_cm_target_l_unary_address_step(void);
PROOF thm get_cm_target_l_index_start_step(void);
PROOF thm get_cm_target_l_member_start_step(void);
