#pragma once

#include "proof/proof.h"
#include "cmc_preservation_code_value_total.h"

PROOF extern thm cm_c_regular_ready_def;
PROOF extern thm cm_c_phase_ready_def;
PROOF extern thm cm_c_code_ready_def;
PROOF extern thm cm_c_layout_ready_def;
PROOF extern thm cm_c_phase_layout_step;
PROOF extern thm cm_c_cons_annotation_layout_step;
PROOF extern thm cm_c_nil_annotation_layout_step;
PROOF extern thm cm_c_task_layout_step;
PROOF thm get_cm_c_task_layout_step(void);
