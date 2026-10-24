#pragma once

#include "proof/proof.h"
#include "cmc_preservation_code.h"

PROOF extern thm cm_r_const_layout_step;
PROOF extern thm cm_r_layout_ready_def;
PROOF extern thm cm_l_layout_ready_def;
PROOF thm get_cm_r_task_layout_step(void);
PROOF thm get_cm_l_task_layout_step(void);

PROOF thm get_cm_layout_char_normalize_length(void);
PROOF thm get_cm_layout_rcode_length(void);
PROOF thm get_cm_layout_load_length(void);
PROOF thm get_cm_layout_store_length(void);
PROOF thm get_cm_layout_temp_store_length(void);
PROOF thm get_cm_layout_temp_load_length(void);
PROOF thm get_cm_layout_assign_tail_length(void);
PROOF thm get_cm_layout_index_tail_length(void);
PROOF thm get_cm_layout_member_tail_length(void);
PROOF thm get_cm_layout_binary_finish_length(void);

PROOF thm get_cm_layout_binary_phase_length(void);