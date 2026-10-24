#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_codegen.h"
#require "cmc_codegen.c"
#include "cmc_preservation_memory.h"

PROOF static size_t _cmc_preservation_memory_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_prove_global_init_bytes_static(void) {
  gnode root = gnode_new_with_ccl(
      `!(g:cm_global_d).
         cm_global_init_bytes g == cm_static_global_init_bytes g`);
  gnode leaf = AUTO_INTROS_TAC(root);
  CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
      get_cm_global_init_bytes_def(),
      get_cm_static_global_init_bytes_def())));
  return gnode_prove(root);
}
PROOF thm cm_global_init_bytes_static =
    cm_prove_global_init_bytes_static();

PROOF static thm cm_prove_global_bytes_static(void) {
  gnode root = gnode_new_with_ccl(
      `!(structs:(cm_struct_d)list) (g:cm_global_d).
         cm_global_bytes structs g == cm_static_global_bytes structs g`);
  gnode leaf = AUTO_INTROS_TAC(root);
  CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
      get_cm_global_bytes_def(), get_cm_static_global_bytes_def(),
      cm_global_init_bytes_static)));
  return gnode_prove(root);
}
PROOF thm cm_global_bytes_static = cm_prove_global_bytes_static();

PROOF static thm cm_prove_globals_bytes_static(void) {
  gnode root = gnode_new_with_ccl(
      `!(structs:(cm_struct_d)list) (globals:(cm_global_d)list).
         cm_globals_bytes structs globals ==
         cm_static_globals_bytes structs globals`);
  gnode_list cases = INDUCT_TAC(root, `globals:(cm_global_d)list`);
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode leaf = AUTO_INTROS_TAC(cases[i]);
    CONV_WITH_ASMP_TAC(leaf, reduce_rewrite_conv, THM_LIST(
        get_cm_globals_bytes_def(), get_cm_static_globals_bytes_def(),
        cm_global_bytes_static));
  }
  return gnode_prove(root);
}
PROOF thm cm_globals_bytes_static = cm_prove_globals_bytes_static();

PROOF static thm cm_prove_strings_bytes_static(void) {
  gnode root = gnode_new_with_ccl(
      `!(strings:(cm_string_d)list).
         cm_strings_bytes strings == cm_static_strings_bytes strings`);
  gnode_list cases = INDUCT_TAC(root, `strings:(cm_string_d)list`);
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode leaf = AUTO_INTROS_TAC(cases[i]);
    CONV_WITH_ASMP_TAC(leaf, reduce_rewrite_conv, THM_LIST(
        get_cm_strings_bytes_def(), get_cm_static_strings_bytes_def()));
  }
  return gnode_prove(root);
}
PROOF thm cm_strings_bytes_static = cm_prove_strings_bytes_static();

PROOF static thm cm_prove_model_data_bytes_static(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program).
         cm_model_data_bytes p == cm_static_data_bytes p`);
  gnode leaf = AUTO_INTROS_TAC(root);
  CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
      get_cm_model_data_bytes_def(), get_cm_static_data_bytes_def(),
      cm_globals_bytes_static, cm_strings_bytes_static)));
  return gnode_prove(root);
}
PROOF thm cm_model_data_bytes_static =
    cm_prove_model_data_bytes_static();

PROOF static thm cm_prove_apply_byte_patches(void) {
  gnode root = gnode_new_with_ccl(
      `!(bytes:(int)list) (addr:int) (mem:int->int).
         tvm_apply_patches (cm_bytes_patches bytes addr) mem ==
         cm_write_bytes mem addr bytes`);
  gnode_list cases = INDUCT_TAC(root, `bytes:(int)list`);
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode leaf = AUTO_INTROS_TAC(cases[i]);
    CONV_WITH_ASMP_TAC(leaf, reduce_rewrite_conv, THM_LIST(
        get_tvm_apply_patches_def(), get_cm_bytes_patches_def(),
        get_cm_write_bytes_def(), get_tvm_patch_addr_def(),
        get_tvm_patch_byte_def()));
  }
  return gnode_prove(root);
}
PROOF thm cm_apply_byte_patches = cm_prove_apply_byte_patches();

PROOF static thm cm_prove_initial_memory_image(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (input:(int)list).
         tvm_mem
           (tvm_initial_state (cm_compile_model p) input) ==
         cm_initial_mem p`);
  gnode leaf = AUTO_INTROS_TAC(root);
  CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
      get_tvm_initial_state_def(), get_tvm_state_selectors_def(),
      get_cm_compile_model_def(), get_tvm_object_patches_def(),
      get_cm_model_patches_def(), cm_apply_byte_patches,
      cm_model_data_bytes_static, get_cm_initial_mem_def())));
  return gnode_prove(root);
}
PROOF thm cm_initial_memory_image = cm_prove_initial_memory_image();

PROOF thm get_cm_model_data_bytes_static(void) {
  return cm_model_data_bytes_static;
}
PROOF thm get_cm_apply_byte_patches(void) {
  return cm_apply_byte_patches;
}
PROOF thm get_cm_initial_memory_image(void) {
  return cm_initial_memory_image;
}

PROOF static int cmc_preservation_memory_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_memory_axioms_before,
      "cmc_preservation_memory introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_memory_checks =
    cmc_preservation_memory_final_checks();
