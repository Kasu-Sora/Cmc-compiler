#include "cmc_concrete_compile_ready.h"
#require "cmc_concrete_function_ready.c"

PROOF static size_t _cmc_compile_ready_axioms_before =
    vector_size(get_all_axioms());

PROOF thm cm_concrete_code_ready_def = new_fun_definition(
    `cm_concrete_code_ready (p:cm_program) : bool =
       (cm_concrete_structs_ready p &&
        cm_concrete_functions_ready p 0i (cm_program_functions p))`);
PROOF static int _e_cm_concrete_code_ready =
    cst_add_const_to_header(`cm_concrete_code_ready`);

PROOF static thm cm_prove_concrete_code_ready_from_wf(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program).
         cm_wf_program p ==> cm_concrete_code_ready p`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm wf = assume_rule(`cm_wf_program (p:cm_program)`);
  thm opened = conv_rule(rewrite_conv(THM_LIST(
      get_cm_wf_program_def(), get_cm_codegen_admissible_def())), wf);
  thm typed = cm_pick_conjunct(opened,
      `cm_typed_program (p:cm_program)`);
  thm structs_ready = mp_rule(spec_rule(`p:cm_program`,
      get_cmc_structs_ready_from_typed()), typed);
  thm functions_ready = mp_rule(spec_rule(`p:cm_program`,
      cm_concrete_functions_ready_from_wf), wf);
  thm parts = conj_rule(structs_ready, functions_ready);
  thm view = apply_conversion(rewrite_conv(THM_LIST(
      cm_concrete_code_ready_def)),
      `cm_concrete_code_ready (p:cm_program)`);
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(view), parts));
  return gnode_prove(root);
}
PROOF thm cm_concrete_code_ready_from_wf =
    cm_prove_concrete_code_ready_from_wf();

PROOF thm get_cm_concrete_code_ready_def(void) {
  return cm_concrete_code_ready_def;
}

PROOF static int _cmc_compile_ready_no_axioms =
    vector_size(get_all_axioms()) == _cmc_compile_ready_axioms_before
        ? 1 : (abort(), 0);
