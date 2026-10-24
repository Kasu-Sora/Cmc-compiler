#pragma once

#include "proof/proof.h"
#include "cmc_stack.h"

PROOF extern thm cm_code_at_def;
PROOF extern thm cm_function_code_prefix_def;
PROOF extern thm cm_code_at_append_left;
PROOF extern thm cm_code_at_append_right;
PROOF extern thm cm_code_at_head;
PROOF extern thm cm_code_at_prepend;
PROOF extern thm cm_emit_functions_contains;
PROOF extern thm cm_function_code_prefix_length;
PROOF extern thm cm_model_function_at;
PROOF extern thm cm_model_function_body_at;
PROOF extern thm cm_model_function_body_tail_at;
PROOF extern thm cm_model_prelude_at;

PROOF thm get_cm_code_at_def(void);
PROOF thm get_cm_function_code_prefix_def(void);
PROOF thm get_cm_code_at_append_left(void);
PROOF thm get_cm_code_at_append_right(void);
PROOF thm get_cm_code_at_head(void);
PROOF thm get_cm_code_at_prepend(void);
PROOF thm get_cm_model_prelude_at(void);
PROOF thm get_cm_emit_functions_contains(void);
PROOF thm get_cm_function_code_prefix_length(void);
PROOF thm get_cm_model_function_at(void);
PROOF thm get_cm_model_function_body_at(void);
PROOF thm get_cm_model_function_body_tail_at(void);
