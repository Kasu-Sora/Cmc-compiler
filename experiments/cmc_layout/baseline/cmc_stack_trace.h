#pragma once

#include "proof/proof.h"
#include "cmc_stack_bound.h"
#include "cmc_stack.h"

PROOF extern thm cm_stack_edges_at_offset;
PROOF extern thm cm_stack_edges_at;
PROOF extern thm cm_return_sites_def;
PROOF extern thm cm_stack_trace_inv_def;
PROOF extern thm cm_ilength_tl;
PROOF extern thm cm_ilength_tl_tl;
PROOF extern thm cm_return_sites_pop;
PROOF extern thm cm_instruction_stack_effect;
PROOF extern thm cm_tvm_inst_reconstruct;
PROOF extern thm cm_instruction_trace_effect;
PROOF extern thm cm_stack_trace_step;
PROOF extern thm cm_stack_trace_iter;
PROOF extern thm cm_direct_stack_trace_reachable;
PROOF extern thm cm_heights_le_at;
PROOF extern thm cmc_stack_bound;
