#pragma once

#include "proof/proof.h"
#include "cmc_preservation_spill_semantic.h"

PROOF extern thm cm_staged_spills_put_next;
PROOF extern thm cm_ilength_nonempty_tail;
PROOF extern thm cm_annotation_spill_plain;
PROOF extern thm cm_annotation_spill_push;
PROOF extern thm cm_annotation_spill_replace;
PROOF extern thm cm_annotation_spill_pop;
PROOF extern thm cm_annotation_spill_enter_call;
PROOF extern thm cm_annotation_spill_leave_call;
PROOF extern thm cm_annotation_spill_replace_store;
PROOF extern thm cm_annotation_spill_arg_store;
PROOF extern thm cm_annotation_spill_arg_enter_call;

PROOF thm get_cm_annotation_spill_replace_store(void);
PROOF thm get_cm_annotation_spill_arg_store(void);
PROOF thm get_cm_annotation_spill_arg_enter_call(void);
