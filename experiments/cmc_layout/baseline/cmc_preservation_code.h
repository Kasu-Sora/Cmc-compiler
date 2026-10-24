#pragma once

#include "proof/proof.h"
#include "cmc_preservation_tvm.h"
#include "cmc_preservation_state.h"

PROOF extern thm cm_value_phase_code_def;
PROOF extern thm cm_normal_phase_code_def;
PROOF extern thm cm_cursor_code_def;
PROOF extern thm cm_normal_cont_code_def;
PROOF extern thm cm_control_phase_code_def;
PROOF extern thm cm_task_code_def;
PROOF extern thm cm_task_fid_def;
PROOF extern thm cm_phase_caller_def;
PROOF extern thm cm_phase_stops_def;
PROOF extern thm cm_phase_yields_normal_def;
PROOF extern thm cm_normal_phase_stops_def;
PROOF extern thm cm_cont_code_def;
PROOF extern thm cm_phase_is_call_def;
PROOF extern thm cm_phase_site_def;
PROOF extern thm cm_saved_layout_def;
PROOF extern thm cm_task_layout_def;
PROOF extern thm cm_task_layout_done;
PROOF thm get_cm_task_layout_done(void);

PROOF thm get_cm_task_layout_initial(void);
PROOF thm get_cm_task_layout_step(void);
