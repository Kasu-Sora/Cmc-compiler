#pragma once

#include "proof/proof.h"
#include "cmc_preservation_machine_ops.h"

PROOF extern thm cm_value_number_state_io;
PROOF extern thm cm_encode_values_state_io;
PROOF extern thm cm_machine_io_restack;
PROOF extern thm cm_machine_getc_empty;
PROOF extern thm cm_machine_getc_nonempty;
PROOF extern thm cm_machine_putc;
PROOF extern thm cm_machine_puti;

PROOF thm get_cm_value_number_state_io(void);
PROOF thm get_cm_encode_values_state_io(void);
PROOF thm get_cm_machine_io_restack(void);
PROOF thm get_cm_machine_getc_empty(void);
PROOF thm get_cm_machine_getc_nonempty(void);
PROOF thm get_cm_machine_putc(void);
PROOF thm get_cm_machine_puti(void);
