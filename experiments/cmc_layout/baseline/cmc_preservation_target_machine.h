#pragma once

#include "proof/proof.h"
#include "cmc_preservation_runtime.h"
#include "cmc_preservation_machine_io.h"
#include "cmc_preservation_tvm.h"

PROOF extern thm cm_target_reannotate;
PROOF thm get_cm_target_reannotate(void);
PROOF extern thm cm_target_halted_reannotate;
PROOF thm get_cm_target_halted_reannotate(void);
PROOF extern thm cm_target_halted_deactivate;
PROOF thm get_cm_target_halted_deactivate(void);
PROOF extern thm cm_target_revalue;
PROOF thm get_cm_target_revalue(void);
PROOF extern thm cm_target_push;
PROOF thm get_cm_target_push(void);
PROOF extern thm cm_target_getc;
PROOF thm get_cm_target_getc(void);
PROOF extern thm cm_target_load;
PROOF thm get_cm_target_load(void);
PROOF extern thm cm_target_pop;
PROOF thm get_cm_target_pop(void);
PROOF extern thm cm_target_dup;
PROOF thm get_cm_target_dup(void);
PROOF extern thm cm_target_swap;
PROOF thm get_cm_target_swap(void);
PROOF extern thm cm_target_putc;
PROOF thm get_cm_target_putc(void);
PROOF extern thm cm_target_puti;
PROOF thm get_cm_target_puti(void);
PROOF extern thm cm_target_halt;
PROOF thm get_cm_target_halt(void);
PROOF extern thm cm_target_binary_total;
PROOF thm get_cm_target_binary_total(void);
PROOF extern thm cm_target_binary_nonzero;
PROOF thm get_cm_target_binary_nonzero(void);
PROOF extern thm cm_target_jump;
PROOF thm get_cm_target_jump(void);
PROOF extern thm cm_target_jz;
PROOF thm get_cm_target_jz(void);
PROOF extern thm cm_target_jnz;
PROOF thm get_cm_target_jnz(void);
PROOF extern thm cm_target_load_fp;
PROOF thm get_cm_target_load_fp(void);
PROOF extern thm cm_target_spill_load;
PROOF thm get_cm_target_spill_load(void);
PROOF extern thm cm_target_spill_store;
PROOF thm get_cm_target_spill_store(void);
