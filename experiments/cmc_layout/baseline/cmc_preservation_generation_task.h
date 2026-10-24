#pragma once

#include "proof/proof.h"
#include "cmc_preservation_generation_state.h"

PROOF extern thm cm_expr_static_valid_def;
PROOF extern thm cm_args_static_valid_def;
PROOF extern thm cm_stmt_static_valid_def;
PROOF extern thm cm_frame_static_valid_def;
PROOF extern thm cm_frames_static_valid_def;
PROOF extern thm cm_task_static_valid_def;
PROOF extern thm cm_task_generation_limit_def;
PROOF extern thm cm_annotation_payload_generation_below_def;

PROOF extern thm cm_annotation_payload_implies_task_generation;
PROOF extern thm cm_annotation_payload_generation_below_mono;

PROOF thm get_cm_task_static_valid_def(void);
PROOF thm get_cm_task_generation_limit_def(void);
PROOF thm get_cm_annotation_payload_generation_below_def(void);
