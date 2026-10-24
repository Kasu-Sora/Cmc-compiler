#pragma once

#include "proof/proof.h"
#include "cmc_preservation_code_value_call.h"

PROOF extern thm cm_v_phase_layout_step;
PROOF extern thm cm_v_cons_annotation_layout_step;
PROOF extern thm cm_v_nil_annotation_layout_step;
PROOF extern thm cm_v_task_layout_step;
PROOF thm get_cm_v_task_layout_step(void);
