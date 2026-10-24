#pragma once

#include "proof/proof.h"
#include "cmc_preservation_type_ready.h"
#include "cmc_preservation_code.h"

PROOF extern thm cm_code_at_suffix_head_target_valid;
PROOF extern thm cm_value_cursor_code_nonempty;
PROOF extern thm cm_value_continuation_target_valid;

PROOF thm get_cm_code_at_suffix_head_target_valid(void);
PROOF thm get_cm_value_cursor_code_nonempty(void);
PROOF thm get_cm_value_continuation_target_valid(void);
