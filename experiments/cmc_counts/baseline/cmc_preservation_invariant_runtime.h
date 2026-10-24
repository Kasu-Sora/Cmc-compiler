#pragma once

#include "proof/proof.h"
#include "cmc_preservation_invariant_frame.h"

PROOF extern thm cm_runtime_stack_plain_cons;
PROOF extern thm cm_runtime_stack_call_cons;
PROOF extern thm cm_runtime_stack_scope_cons;
PROOF extern thm cm_region_prefix_safe_cons;
PROOF extern thm cm_region_prefix_safe_old_length;
PROOF extern thm cm_runtime_stack_active_cons;
PROOF extern thm cm_runtime_stack_fresh_cons;
PROOF extern thm cm_store_params_structure;
PROOF extern thm cm_enter_call_structure;
PROOF extern thm cm_runtime_stack_enter_call;
PROOF extern thm cm_activate_local_structure;
PROOF extern thm cm_runtime_stack_activate_local;
PROOF extern thm cm_restore_scope_structure;
PROOF extern thm cm_restore_call_structure;
PROOF extern thm cm_runtime_stack_enter_scope;
PROOF extern thm cm_runtime_stack_leave_scope;
PROOF extern thm cm_runtime_stack_leave_call;
PROOF extern thm cm_runtime_stack_plain_push;
PROOF extern thm cm_runtime_stack_plain_pop;
PROOF extern thm cm_runtime_stack_plain_replace;
PROOF extern thm cm_spills_within_remove;
PROOF extern thm cm_spills_within_put;
PROOF extern thm cm_runtime_stack_spill_put;
PROOF extern thm cm_runtime_stack_spill_remove;
