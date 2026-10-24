#pragma once

#include "proof/proof.h"
#include "cmc_sim.h"
#include "cmc_stack.h"
#include "cmc_examples.h"

/* Terminating source executions preserve ordered output and exit status. */
PROOF thm get_cmc_preservation(void);
PROOF thm get_cmc_no_vm_error(void);
