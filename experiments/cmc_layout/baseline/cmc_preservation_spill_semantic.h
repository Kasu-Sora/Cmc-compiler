#pragma once

#include "proof/proof.h"
#include "cmc_annotate_model.h"
#include "cmc_preservation_code.h"
#include "cmc_preservation_code_value.h"

PROOF extern thm cm_staged_spills_def;
PROOF extern thm cm_phase_spill_consistent_def;
PROOF extern thm cm_cursors_spill_consistent_def;
PROOF extern thm cm_annotation_spill_consistent_def;

PROOF extern thm cm_spill_holds_put_same;
PROOF extern thm cm_spill_holds_put_other;
PROOF extern thm cm_staged_spills_put_above;
PROOF extern thm cm_phase_spill_consistent_put_above;
PROOF extern thm cm_cursors_spill_consistent_put_above;
PROOF extern thm cm_annotation_spill_consistent_initial;

PROOF thm get_cm_staged_spills_put_above(void);
PROOF thm get_cm_cursors_spill_consistent_put_above(void);
