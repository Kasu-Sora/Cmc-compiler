#pragma once

#include "proof/proof.h"
#include "cmc_preservation_target_call_jump.h"
#include "cmc_preservation_machine_store.h"

PROOF extern thm cm_rebase_call_frames_def;
PROOF extern thm cm_ann_call_rebase_def;
PROOF extern thm cm_machine_call_save;
PROOF extern thm cm_target_call_save;

PROOF thm get_cm_rebase_call_frames_def(void);
PROOF thm get_cm_ann_call_rebase_def(void);
PROOF thm get_cm_machine_call_save(void);
PROOF thm get_cm_target_call_save(void);
