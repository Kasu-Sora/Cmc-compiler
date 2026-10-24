#pragma once

#include "proof/proof.h"

PROOF extern thm cm_v_phase_ready_def;
PROOF extern thm cm_phase_child_temp_def;
PROOF extern thm cm_v_temp_ready_def;
PROOF extern thm cm_v_layout_ready_def;
PROOF extern thm cm_v_halt_layout_step;
PROOF extern thm cm_v_load_layout_step;
PROOF extern thm cm_v_assign_l_layout_step;
PROOF extern thm cm_v_assign_r_layout_step;
PROOF extern thm cm_v_unary_layout_step;
PROOF extern thm cm_v_index_l_layout_step;
PROOF extern thm cm_v_index_r_layout_step;
PROOF extern thm cm_v_member_layout_step;
PROOF extern thm cm_v_putc_layout_step;
PROOF extern thm cm_v_puti_layout_step;
PROOF extern thm cm_v_exit_layout_step;
PROOF extern thm cm_v_expr_stmt_layout_step;
PROOF extern thm cm_v_init_layout_step;
PROOF extern thm cm_v_return_layout_step;

PROOF thm_list cm_v_layout_rules(void);
PROOF thm get_cm_v_task_layout_step(void);
