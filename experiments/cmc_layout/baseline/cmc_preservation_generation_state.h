#pragma once

#include "proof/proof.h"
#include "cmc_preservation_generation.h"

PROOF extern thm cm_global_pointer_generation_below;
PROOF extern thm cm_string_pointer_generation_below;
PROOF extern thm cm_state_generation_initial;
PROOF extern thm cm_state_generation_io;
PROOF extern thm cm_state_generation_store;
PROOF extern thm cm_state_generation_activate_local;
PROOF extern thm cm_state_generation_restore_scope;
PROOF extern thm cm_state_generation_restore_call;
PROOF extern thm cm_state_generation_enter_call;
PROOF extern thm cm_load_value_generation_below;
PROOF extern thm cm_binary_value_generation_below;
PROOF extern thm cm_unary_value_generation_below;

PROOF thm get_cm_state_generation_initial(void);
PROOF thm get_cm_state_generation_store(void);
PROOF thm get_cm_state_generation_activate_local(void);
PROOF thm get_cm_state_generation_enter_call(void);
PROOF thm get_cm_load_value_generation_below(void);
PROOF thm get_cm_binary_value_generation_below(void);
PROOF thm get_cm_env_generation_below_mono(void);
