#pragma once

#include "proof/proof.h"
#include "cmc_preservation_generation.h"

PROOF extern thm cm_frame_fid_ready_def;
PROOF extern thm cm_frames_fid_ready_def;
PROOF extern thm cm_task_fid_ready_def;
PROOF extern thm cm_cursors_fid_ready_def;
PROOF extern thm cm_task_phase_fid_ready_def;
PROOF extern thm cm_phase_frame_fid_ready;
PROOF extern thm cm_task_phase_fid_ready_from_source;

PROOF thm get_cm_frame_fid_ready_def(void);
PROOF thm get_cm_frames_fid_ready_def(void);
PROOF thm get_cm_task_fid_ready_def(void);
PROOF thm get_cm_cursors_fid_ready_def(void);
PROOF thm get_cm_task_phase_fid_ready_def(void);
PROOF thm get_cm_phase_frame_fid_ready(void);
PROOF thm get_cm_task_phase_fid_ready_from_source(void);
