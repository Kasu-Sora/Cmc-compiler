#pragma once

#include "proof/proof.h"
#include "cmc_preservation_machine_load.h"

PROOF extern thm cm_range_disjoint_def;
PROOF extern thm cm_store_mem_byte_same;
PROOF extern thm cm_store_mem_byte_other;
PROOF extern thm cm_store_mem_word_other;
PROOF extern thm cm_live_address_store;
PROOF extern thm cm_initialized_store_sim;
PROOF extern thm cm_store_mem_target;

PROOF thm get_cm_range_disjoint_def(void);
PROOF thm get_cm_store_mem_byte_same(void);
PROOF thm get_cm_store_mem_byte_other(void);
PROOF thm get_cm_store_mem_word_other(void);
PROOF thm get_cm_live_address_store(void);
PROOF thm cm_store_normalized_assumption(
    const gnode leaf, const term wanted, const thm_list rules);
PROOF thm get_cm_initialized_store_sim(void);
PROOF thm get_cm_store_mem_target(void);
