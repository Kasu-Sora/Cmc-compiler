#pragma once

#include "proof/proof.h"

PROOF conv cm_source_closed_eval_conv_count(size_t iteration_count);
PROOF conv cm_target_closed_eval_conv_count(size_t iteration_count);
PROOF conv cm_closed_wf_conv(void);

PROOF thm cm_prove_closed_example_source(
    term program, term input, term output, term expected_status,
    term iteration_count, size_t evaluation_count, thm iteration_theorem);
PROOF thm cm_prove_closed_example_target(
    term program, term input, term output, term expected_status,
    term iteration_count, thm wf_theorem, thm iteration_theorem);
