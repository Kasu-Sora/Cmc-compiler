#include "cmc_concrete_data_ready.h"
#require "cmc_lang.c"

PROOF static size_t _cmc_data_ready_axioms_before =
    vector_size(get_all_axioms());

PROOF thm cm_data_globals_wf_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(!structs.
       cm_data_globals_wf (structs:(cm_struct_d)list)
         ([]:(cm_global_d)list) = T) &&
     (!structs global rest.
       (cm_data_globals_wf (structs:(cm_struct_d)list)
          ((global:cm_global_d) :: (rest:(cm_global_d)list)) <=>
        cm_global_wf structs global &&
        cm_data_globals_wf structs rest))`);
PROOF static int _e_cm_data_globals_wf =
    cst_add_const_to_header(`cm_data_globals_wf`);

PROOF thm get_cm_data_globals_wf_def(void) {
  return cm_data_globals_wf_def;
}

PROOF static int _cmc_data_ready_no_axioms =
    vector_size(get_all_axioms()) == _cmc_data_ready_axioms_before
        ? 1 : (abort(), 0);
