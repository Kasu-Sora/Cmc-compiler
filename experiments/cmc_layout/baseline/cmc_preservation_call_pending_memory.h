#pragma once

#include "proof/proof.h"
#include "cmc_preservation_call_pending_live.h"
#include "cmc_preservation_machine_store.h"

PROOF extern thm cm_call_pending_initialized_transport;
PROOF extern thm cm_call_pending_provenance_transport;

PROOF thm get_cm_call_pending_initialized_transport(void);
PROOF thm get_cm_call_pending_provenance_transport(void);
