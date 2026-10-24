#pragma once

#include "proof/proof.h"
#include "cmc_preservation_invariant_step.h"

PROOF extern thm cm_value_generation_below_def;
PROOF extern thm cm_values_generation_below_def;
PROOF extern thm cm_value_number_bases;
PROOF extern thm cm_values_number_bases;
PROOF extern thm cm_call_regions_bases;

PROOF thm get_cm_value_generation_below_def(void);
PROOF thm get_cm_values_generation_below_def(void);
PROOF thm get_cm_value_number_bases(void);
PROOF thm get_cm_values_number_bases(void);
PROOF thm get_cm_call_regions_bases(void);
