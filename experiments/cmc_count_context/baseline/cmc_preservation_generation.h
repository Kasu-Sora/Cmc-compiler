#pragma once

#include "proof/proof.h"
#include "cmc_preservation_call_transport.h"
#include "cmc_preservation_spill_semantic.h"
#include "cmc_preservation_state.h"

PROOF extern thm cm_env_generation_below_def;
PROOF extern thm cm_tags_generation_below_def;
PROOF extern thm cm_control_generation_below_def;
PROOF extern thm cm_frame_generation_below_def;
PROOF extern thm cm_frame_parent_fid_def;
PROOF extern thm cm_frames_generation_below_def;
PROOF extern thm cm_state_generation_below_def;
PROOF extern thm cm_task_generation_below_def;
PROOF extern thm cm_annotation_generation_below_def;
PROOF extern thm cm_task_generation_safe_def;

PROOF extern thm cm_value_generation_below_mono;
PROOF extern thm cm_values_generation_below_mono;
PROOF extern thm cm_spills_generation_below_mono;
PROOF extern thm cm_spill_frames_generation_below_mono;
PROOF extern thm cm_values_generation_below_reverse;
PROOF extern thm cm_staged_spills_generation_below;
PROOF extern thm cm_state_tags_generation_from_all;
PROOF extern thm cm_convert_generation_below;
PROOF extern thm cm_pointer_retype_generation_below;
PROOF extern thm cm_ptr_add_generation_below;
PROOF extern thm cm_ptr_member_generation_below;

PROOF thm get_cm_task_generation_safe_def(void);
PROOF thm get_cm_value_generation_below_mono(void);
PROOF thm get_cm_values_generation_below_mono(void);
PROOF thm get_cm_spill_frames_generation_below_mono(void);
PROOF thm get_cm_values_generation_below_reverse(void);
PROOF thm get_cm_staged_spills_generation_below(void);
PROOF thm get_cm_state_tags_generation_from_all(void);
PROOF thm get_cm_convert_generation_below(void);
