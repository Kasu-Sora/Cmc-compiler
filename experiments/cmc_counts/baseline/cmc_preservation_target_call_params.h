#pragma once

#include "proof/proof.h"
#include "cmc_preservation_call_param.h"
#include "cmc_preservation_code_stmt.h"
#include "cmc_preservation_target_address.h"
#include "cmc_preservation_target_convert.h"
#include "cmc_preservation_target_store.h"

PROOF extern thm cm_param_indices_def;
PROOF extern thm cm_param_indices_refl;
PROOF extern thm cm_param_indices_head;
PROOF extern thm cm_param_indices_tail;
PROOF extern thm cm_store_params_reverse_env;
PROOF extern thm cm_store_params_reverse_runtime;
PROOF extern thm cm_target_call_params;

PROOF thm get_cm_param_indices_def(void);
PROOF thm get_cm_param_indices_refl(void);
PROOF thm get_cm_param_indices_head(void);
PROOF thm get_cm_param_indices_tail(void);
PROOF thm get_cm_store_params_reverse_env(void);
PROOF thm get_cm_store_params_reverse_runtime(void);

PROOF thm get_cm_target_call_params(void);