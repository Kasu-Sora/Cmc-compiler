#pragma once

#include "proof/proof.h"
#include "cmc_annotate_model.h"

PROOF extern thm cm_preservation_invariant_def;
PROOF extern thm cm_preservation_initial;

PROOF thm get_cm_preservation_invariant_def(void);
PROOF thm get_cm_succeeds_step_total(void);
PROOF thm get_cm_preservation_initial(void);
PROOF thm get_cm_preservation_step(void);
PROOF thm get_cm_preservation_iter(void);
PROOF thm get_cm_annotated_iter_exec_prefix(void);
