#pragma once

#include "proof/proof.h"
#include "cmc_annotate_preservation.h"

PROOF thm get_cm_annotation_erasure(void);
PROOF thm get_cm_annotated_step_target(void);
PROOF thm get_cm_annotated_step_erasure(void);
PROOF thm get_cm_annotated_iter_erasure(void);
