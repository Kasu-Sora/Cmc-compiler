#pragma once

#include "proof/proof.h"
#include "cmc_preservation_invariant_runtime.h"
#include "cmc_preservation_source.h"
#include "cmc_preservation_code_expr.h"
#include "cmc_preservation_code_value.h"

PROOF extern thm cm_v_spill_ready_def;
PROOF extern thm cm_v_source_ready_def;
PROOF extern thm cm_runtime_step_ready_def;
PROOF extern thm cm_task_runtime_start_step;
PROOF extern thm cm_runtime_core_def;
PROOF extern thm cm_runtime_core_plain;
PROOF extern thm cm_runtime_core_linear;
PROOF extern thm cm_runtime_core_push_plain;
PROOF extern thm cm_runtime_core_pop_plain;
PROOF extern thm cm_runtime_core_replace_plain;
PROOF extern thm cm_runtime_core_spill_put;
PROOF extern thm cm_runtime_core_activate_local;
PROOF extern thm cm_runtime_core_enter_scope;
PROOF extern thm cm_runtime_core_leave_scope;
PROOF extern thm cm_runtime_core_enter_call;
PROOF extern thm cm_runtime_core_leave_call;
PROOF extern thm cm_runtime_core_io;
PROOF extern thm cm_runtime_core_store;
PROOF extern thm cm_runtime_core_replace_scope;
PROOF extern thm cm_runtime_halt_done;
PROOF extern thm cm_runtime_core_done;
PROOF extern thm cm_task_runtime_r_step;
PROOF extern thm cm_task_runtime_l_step;
PROOF extern thm cm_task_runtime_s_step;
