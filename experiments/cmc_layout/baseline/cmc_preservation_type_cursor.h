#pragma once

#include "proof/proof.h"
#include "cmc_preservation_type_phase.h"

PROOF extern thm cm_cursor_push_type_ready;
PROOF extern thm cm_cursor_push_input_ready;
PROOF extern thm cm_cursor_push_expr_values_ready;
PROOF extern thm cm_cursor_push_lvalue_ready;
PROOF extern thm cm_lvalue_cursor_expr_values;
PROOF extern thm cm_expr_cursor_values_transport_nonzero;
PROOF extern thm cm_expr_cursor_values_lvalue;
PROOF extern thm cm_cursor_expr_result_ready;
PROOF extern thm cm_phase_result_from_expr;
PROOF extern thm cm_phase_result_from_lvalue;
PROOF extern thm cm_r_value_task_ready;
PROOF extern thm cm_l_value_task_ready;
PROOF extern thm cm_r_push_task_ready;
PROOF extern thm cm_r_push_task_ready_at;
PROOF extern thm cm_l_push_task_ready;
