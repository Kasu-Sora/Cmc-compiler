#pragma once

#include "proof/proof.h"
#include "cmc_preservation_target_machine.h"
#include "cmc_preservation_tagged_allocation.h"
#include "cmc_preservation_call_transport.h"

PROOF extern thm cm_target_activate_local_empty;
PROOF thm get_cm_target_activate_local_empty(void);
