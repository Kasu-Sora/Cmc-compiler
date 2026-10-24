#pragma once

#include "proof/proof.h"
#include "cmc_preservation_call_pending.h"
#include "cmc_preservation_store_semantic.h"

PROOF extern thm cm_scalar_store_shape;
PROOF extern thm cm_slot_region_index_member;
PROOF extern thm cm_region_pointer_writable;
PROOF extern thm cm_exact_region_live_span;
PROOF extern thm cm_parameter_store_ready;
PROOF extern thm cm_parameter_address_ready;

PROOF thm get_cm_scalar_store_shape(void);
PROOF thm get_cm_slot_region_index_member(void);
PROOF thm get_cm_region_pointer_writable(void);
PROOF thm get_cm_exact_region_live_span(void);
PROOF thm get_cm_parameter_store_ready(void);
PROOF thm get_cm_parameter_address_ready(void);
