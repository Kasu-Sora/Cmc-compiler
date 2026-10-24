#pragma once

#include "proof/proof.h"
#include "cmc_preservation_target_call_frame.h"

PROOF extern thm cm_call_frame_save_code_def;
PROOF extern thm cm_ann_after_call_frame_save_def;
PROOF extern thm cm_target_call_frame_save;

PROOF thm get_cm_call_frame_save_code_def(void);
PROOF thm get_cm_ann_after_call_frame_save_def(void);
PROOF thm get_cm_target_call_frame_save(void);
