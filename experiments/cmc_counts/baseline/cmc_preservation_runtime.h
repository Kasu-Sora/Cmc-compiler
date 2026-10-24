#pragma once

#include "proof/proof.h"
#include "cmc_preservation_machine_store.h"

PROOF extern thm cm_call_frames_range_safe_def;
PROOF extern thm cm_spill_list_range_safe_def;
PROOF extern thm cm_spill_frames_range_safe_def;
PROOF extern thm cm_machine_range_safe_def;
PROOF extern thm cm_region_runtime_safe_def;
PROOF extern thm cm_regions_runtime_safe_def;
PROOF extern thm cm_runtime_memory_layout_def;
PROOF extern thm cm_range_disjoint_subrange;
PROOF extern thm cm_call_frames_range_subrange;
PROOF extern thm cm_spill_frames_range_subrange;
PROOF extern thm cm_pointer_region_witness;
PROOF extern thm cm_pointer_writable_number;
PROOF extern thm cm_runtime_store_safe;
PROOF extern thm cm_runtime_live_span_bounds;
PROOF extern thm cm_store_width_positive;

PROOF thm get_cm_runtime_memory_layout_def(void);
PROOF thm get_cm_runtime_store_safe(void);
PROOF thm get_cm_runtime_live_span_bounds(void);

PROOF thm get_cm_store_width_positive(void);