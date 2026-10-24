#pragma once

#include "proof/proof.h"
#include "cmc_preservation_target_call_setup.h"

PROOF extern thm cm_call_fp_prepare_code_def;
PROOF extern thm cm_ann_after_call_fp_prepare_def;
PROOF extern thm cm_target_call_fp_prepare;

PROOF thm get_cm_call_fp_prepare_code_def(void);
PROOF thm get_cm_ann_after_call_fp_prepare_def(void);
PROOF thm get_cm_target_call_fp_prepare(void);
