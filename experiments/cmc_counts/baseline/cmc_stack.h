#pragma once

#include "proof/proof.h"
#include "cmc_codegen.h"

PROOF thm get_cmc_stack_discipline(void);
PROOF thm get_cmc_stack_bound(void);
PROOF extern thm cm_inth_zero_cons;
PROOF extern thm cm_inth_cons_tail;
PROOF extern thm cm_inth_append_right;
