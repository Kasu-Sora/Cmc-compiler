#pragma once

#include "proof/proof.h"
#include "cmc_preservation_layout.h"

PROOF thm get_cm_tvm_code_step(void);
PROOF thm get_cm_tvm_iter_add(void);
PROOF thm get_cm_tvm_state_step(void);
PROOF thm get_cm_tvm_halt_step(void);
PROOF extern thm cm_tvm_state_iter_one;
PROOF extern thm cm_tvm_halt_iter_one;
PROOF extern thm cm_tvm_iter_compose;
