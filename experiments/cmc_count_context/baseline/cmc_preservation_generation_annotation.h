#pragma once

#include "proof/proof.h"
#include "cmc_preservation_generation_task.h"

PROOF extern thm cm_spills_generation_remove;
PROOF extern thm cm_spills_generation_put;
PROOF extern thm cm_annotation_payload_plain;
PROOF extern thm cm_annotation_payload_linear;
PROOF extern thm cm_annotation_payload_push;
PROOF extern thm cm_annotation_payload_replace;
PROOF extern thm cm_annotation_payload_pop;
PROOF extern thm cm_annotation_payload_put_spill;
PROOF extern thm cm_annotation_payload_enter_call;
PROOF extern thm cm_annotation_payload_leave_call;
