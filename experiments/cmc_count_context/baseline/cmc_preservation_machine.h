#pragma once

#include "proof/proof.h"
#include "cmc_preservation_state.h"

PROOF extern thm cm_encode_values_length;
PROOF extern thm cm_machine_sim_parts;
PROOF extern thm cm_machine_sim_restack;
PROOF extern thm cm_machine_sim_repc;
PROOF extern thm cm_machine_sim_stack_length;
PROOF extern thm cm_machine_sim_stack_shape;
PROOF extern thm cm_machine_sim_stack_head;

PROOF thm get_cm_encode_values_length(void);
PROOF thm get_cm_machine_sim_parts(void);
PROOF thm get_cm_machine_sim_restack(void);
PROOF thm get_cm_machine_sim_repc(void);
PROOF thm get_cm_machine_sim_stack_length(void);
PROOF thm get_cm_machine_sim_stack_head(void);
PROOF thm get_cm_machine_sim_stack_shape(void);
