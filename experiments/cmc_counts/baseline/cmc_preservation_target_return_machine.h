#pragma once

#include "proof/proof.h"
#include "cmc_preservation_target_machine.h"

PROOF thm get_cm_restore_call_bases_below(void);
PROOF extern thm cm_target_load_saved_fp;
PROOF thm get_cm_target_load_saved_fp(void);
PROOF extern thm cm_target_return_epilogue;
PROOF thm get_cm_target_return_epilogue(void);
