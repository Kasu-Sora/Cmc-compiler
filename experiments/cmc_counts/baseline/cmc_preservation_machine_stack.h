#pragma once

#include "proof/proof.h"
#include "cmc_preservation_machine.h"

PROOF extern thm cm_machine_push;
PROOF extern thm cm_machine_pop;
PROOF extern thm cm_machine_dup;
PROOF extern thm cm_machine_swap;

PROOF thm get_cm_machine_push(void);
PROOF thm get_cm_machine_pop(void);
PROOF thm get_cm_machine_dup(void);
PROOF thm get_cm_machine_swap(void);
