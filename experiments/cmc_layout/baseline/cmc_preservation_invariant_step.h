#pragma once

#include "proof/proof.h"
#include "cmc_preservation_invariant.h"
#include "cmc_preservation_code_task.h"

PROOF extern thm cm_task_runtime_initial;
PROOF extern thm cm_regions_before_mono;
PROOF extern thm cm_region_bases_equal_def;
PROOF extern thm cm_region_bases_below_equal_def;
PROOF extern thm cm_region_bases_below_equal_refl;
PROOF extern thm cm_region_bases_below_equal_trans;
PROOF extern thm cm_regions_for_slots_gen_lower;
PROOF extern thm cm_regions_for_slots_append_before;
PROOF extern thm cm_regions_for_slots_bases;
PROOF extern thm cm_runtime_stack_regions_for_slots;
PROOF extern thm cm_runtime_stack_halt_initial;
PROOF extern thm cm_region_bases_fresh_cons;
PROOF extern thm cm_runtime_stack_below_bases;
PROOF extern thm cm_runtime_stack_restore;
PROOF extern thm cm_retire_region_dead;
PROOF extern thm cm_restore_regions_dead_prefix;
PROOF extern thm cm_restore_regions_bases;
PROOF extern thm cm_static_regions_before_dynamic;
PROOF extern thm cm_regions_before_cons;
PROOF extern thm cm_restore_regions_before;
PROOF extern thm cm_static_region_base_member;
