#pragma once

#include "proof/proof.h"
#include "cmc_codegen.h"

PROOF extern thm cm_global_init_bytes_static;
PROOF extern thm cm_global_bytes_static;
PROOF extern thm cm_globals_bytes_static;
PROOF extern thm cm_strings_bytes_static;
PROOF extern thm cm_model_data_bytes_static;
PROOF extern thm cm_apply_byte_patches;
PROOF extern thm cm_initial_memory_image;

PROOF thm get_cm_model_data_bytes_static(void);
PROOF thm get_cm_apply_byte_patches(void);
PROOF thm get_cm_initial_memory_image(void);
