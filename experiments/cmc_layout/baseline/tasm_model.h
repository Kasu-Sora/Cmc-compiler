#pragma once

#include "proof/proof.h"
#include "tvm_model.h"

/* Structured post-parse TASM denotation and two-pass resolution. */
PROOF thm get_tasm_section_recursion(void);
PROOF thm get_tasm_operand_recursion(void);
PROOF thm get_tasm_item_recursion(void);
PROOF thm get_tasm_binding_recursion(void);
PROOF thm get_tasm_result_recursion(void);
PROOF thm get_tasm_item_selectors_def(void);
PROOF thm get_tasm_trace_defs(void);
PROOF thm get_tasm_labels_def(void);
PROOF thm get_tasm_label_denotes_def(void);
PROOF thm get_tasm_items_wf_def(void);
PROOF thm get_tasm_semantic_ok_def(void);
PROOF thm get_tasm_code_image_def(void);
PROOF thm get_tasm_data_patches_def(void);
PROOF thm get_tasm_object_image_def(void);
PROOF thm get_tasm_denotes_def(void);
PROOF thm get_tasm_candidates_def(void);
PROOF thm get_tasm_resolve_def(void);
PROOF thm get_tasm_resolve_deterministic(void);
PROOF thm get_tasm_resolve_sound(void);
PROOF thm get_tasm_data_fits_def(void);
PROOF thm get_tasm_denotes_object_wf(void);
PROOF thm get_tasm_code_label_inversion(void);
PROOF thm get_tasm_word_inversion(void);
PROOF thm get_tasm_patch_words_one(void);
PROOF thm get_tasm_space_inversion(void);
PROOF thm get_tasm_space_emits_none(void);
PROOF thm get_tasm_wrong_section_no_denotation(void);
PROOF thm get_tasm_example_resolution(void);
