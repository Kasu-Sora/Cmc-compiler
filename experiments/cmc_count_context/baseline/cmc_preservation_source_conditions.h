#pragma once

#include "proof/proof.h"

PROOF extern thm cm_r_getc_succeeds_input;
PROOF extern thm cm_r_array_succeeds_address;
PROOF extern thm cm_l_var_succeeds_address;
PROOF extern thm cm_v_init_succeeds_store;
PROOF extern thm cm_rtask_succeeds_call_ready;

PROOF thm get_cm_r_getc_succeeds_input(void);
PROOF thm get_cm_r_array_succeeds_address(void);
PROOF thm get_cm_l_var_succeeds_address(void);
PROOF thm get_cm_v_init_succeeds_store(void);
PROOF thm get_cm_rtask_succeeds_call_ready(void);
