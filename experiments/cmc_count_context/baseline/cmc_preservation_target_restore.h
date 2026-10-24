#pragma once

#include "proof/proof.h"
#include "cmc_preservation_target_machine.h"

PROOF extern thm cm_target_restore_scope;
PROOF thm get_cm_target_restore_scope(void);
PROOF extern thm cm_target_restore_scope_halted;
PROOF thm get_cm_target_restore_scope_halted(void);
PROOF thm get_cm_region_bases_equal_below(void);
PROOF thm get_cm_restore_initialized_transport(void);
PROOF thm get_cm_restore_provenance_transport(void);
PROOF thm get_cm_restore_tagged_init_lockstep(void);
PROOF thm get_cm_restore_scope_live_source(void);
