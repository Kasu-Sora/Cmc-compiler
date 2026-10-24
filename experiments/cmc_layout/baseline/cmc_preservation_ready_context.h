#pragma once

#include "proof/proof.h"
#include "cmc_annotate_model.h"
#include "cmc_lang.h"
PROOF extern thm cm_phase_control_scope_def;
PROOF extern thm cm_cursors_loop_ready_def;
PROOF extern thm cm_cursors_call_ready_def;
PROOF extern thm cm_stmt_context_ready_def;
PROOF extern thm cm_stmt_scope_ready_def;
PROOF extern thm cm_phase_scope_ready_def;
PROOF extern thm cm_cursors_scope_ready_def;
PROOF extern thm cm_control_context_ready_def;

PROOF extern thm cm_phase_accepts_statement_def;
PROOF extern thm cm_phase_requires_statement_parent_def;
PROOF extern thm cm_statement_cursors_ready_def;
PROOF extern thm cm_cursors_context_ready_def;
PROOF extern thm cm_task_context_ready_def;
PROOF extern thm cm_task_context_initial;
