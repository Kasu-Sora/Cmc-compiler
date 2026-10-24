#pragma once

#include "proof/proof.h"
#include "cmc_preservation_machine_stack.h"

PROOF extern thm cm_machine_unary_operation;
PROOF extern thm cm_machine_binary_operation;
PROOF extern thm cm_machine_jump;
PROOF extern thm cm_machine_branch_pop;

PROOF thm get_cm_machine_unary_operation(void);
PROOF thm get_cm_machine_binary_operation(void);
PROOF thm get_cm_machine_jump(void);
PROOF thm get_cm_machine_branch_pop(void);
