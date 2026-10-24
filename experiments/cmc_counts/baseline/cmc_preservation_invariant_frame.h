#pragma once

#include "proof/proof.h"
#include "cmc_preservation_invariant_step.h"

PROOF extern thm cm_slot_sizes_positive_def;
PROOF extern thm cm_slot_sizes_positive_total;
PROOF extern thm cm_slots_prefix_cell_bounds;
PROOF extern thm cm_slot_region_member_index;
PROOF extern thm cm_slot_region_base_lookup;
PROOF extern thm cm_parameter_region_frame_safe;
PROOF extern thm cm_region_prefix_safe_refl;
PROOF extern thm cm_region_prefix_safe_append;
PROOF extern thm cm_parameter_region_prefix_safe;
PROOF extern thm cm_call_frame_segment;
PROOF extern thm cm_local_region_frame_safe;
PROOF extern thm cm_slots_wf_sizes_positive;
