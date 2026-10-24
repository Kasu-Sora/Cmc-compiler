#pragma once

#include "proof/proof.h"
#include "cmc_annotate_model.h"

PROOF extern thm cm_update_annotation_cond;
PROOF extern thm cm_annotation_erases_task_cond;
PROOF extern thm cm_annotation_erases_ann_cond;
PROOF extern thm cm_ann_cursors_cond;
PROOF extern thm cm_cursor_frames_cond;
PROOF extern thm cm_cursors_rooted_cond;
PROOF extern thm cm_annotation_rooted_cond;
PROOF extern thm cm_args_start_nonempty;
PROOF extern thm cm_update_r_erases;
PROOF extern thm cm_update_l_erases;
PROOF extern thm cm_update_s_erases;
PROOF extern thm cm_update_v_erases;
PROOF extern thm cm_update_c_erases;
PROOF thm_list cm_phase_erasure_rules(void);
