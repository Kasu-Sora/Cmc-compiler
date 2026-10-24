#pragma once

#include "proof/proof.h"
#include "cmc_annotate_erasure.h"

PROOF extern thm cm_update_r_rooted;
PROOF extern thm cm_update_l_rooted;
PROOF extern thm cm_update_s_rooted;
PROOF extern thm cm_update_v_rooted;
PROOF extern thm cm_update_c_rooted;
PROOF extern thm cm_update_v_cursor_preserves;
PROOF extern thm cm_update_c_cursor_preserves;
PROOF extern thm cm_v_step_preserves;
PROOF extern thm cm_c_step_preserves;
PROOF extern thm cm_start_step_preserves;
PROOF extern thm cm_r_step_preserves;
PROOF extern thm cm_l_step_preserves;
PROOF extern thm cm_s_step_preserves;
PROOF extern thm cm_annotation_step_preserves;
PROOF extern thm cm_annotation_step_sound;
PROOF extern thm cm_annotated_step_target;
PROOF extern thm cm_annotated_step_task;
PROOF extern thm cm_annotated_step_erasure;
PROOF extern thm cm_annotated_start_rooted;
PROOF extern thm cm_annotated_start_erases;
PROOF extern thm cm_annotated_iter_invariant;
PROOF extern thm cm_annotated_iter_task;
PROOF extern thm cm_annotated_iter_sound;
PROOF extern thm cm_annotated_iter_erasure;
