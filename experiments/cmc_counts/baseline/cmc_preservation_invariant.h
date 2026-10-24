#pragma once

#include "proof/proof.h"
#include "cmc_preservation_runtime.h"
#include "cmc_preservation_code.h"

PROOF extern thm cm_static_regions_def;
PROOF extern thm cm_phase_is_halt_def;
PROOF extern thm cm_phase_is_scope_def;
PROOF extern thm cm_phase_oldfp_def;
PROOF extern thm cm_phase_oldregions_def;
PROOF extern thm cm_regions_before_def;
PROOF extern thm cm_region_frame_safe_def;
PROOF extern thm cm_region_prefix_safe_def;
PROOF extern thm cm_region_dead_prefix_def;
PROOF extern thm cm_static_regions_layout_def;
PROOF extern thm cm_frame_segment_def;
PROOF extern thm cm_spills_within_frame_def;
PROOF extern thm cm_call_frames_lower_def;
PROOF extern thm cm_spill_list_lower_def;
PROOF extern thm cm_spill_frames_lower_def;
PROOF extern thm cm_runtime_stack_def;
PROOF extern thm cm_task_runtime_invariant_def;
PROOF extern thm cm_region_prefix_member;
PROOF extern thm cm_region_dead_prefix_live_member;
PROOF extern thm cm_call_frames_lower_mono;
PROOF extern thm cm_spill_list_lower_mono;
PROOF extern thm cm_spill_frames_lower_mono;
PROOF extern thm cm_spills_within_lower;
PROOF extern thm cm_call_lower_range_safe;
PROOF extern thm cm_spill_frames_lower_range_safe;
PROOF extern thm cm_runtime_stack_lower;
PROOF extern thm cm_runtime_stack_region_bounds;
PROOF extern thm cm_runtime_stack_fp_bounds;
PROOF extern thm cm_runtime_stack_frame_ceiling;
PROOF extern thm cm_runtime_stack_current_machine_lower;
PROOF extern thm cm_runtime_stack_region_safe;
PROOF extern thm cm_runtime_stack_memory_layout;
