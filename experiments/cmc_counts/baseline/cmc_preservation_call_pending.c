#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_call_pending.h"

#require "cmc_preservation_call_value.c"
#require "cmc_preservation_invariant_frame.c"

PROOF static size_t _cmc_preservation_call_pending_axioms_before =
    vector_size(get_all_axioms());

PROOF thm cm_call_param_span_def = new_fun_definition(
    `cm_call_param_span (p:cm_program) (fid:int) : int =
       cm_slots_size (cm_program_structs p)
         (cm_function_params
           (inth fid (cm_program_functions p)))`);

PROOF thm cm_call_pending_base_def = new_fun_definition(
    `cm_call_pending_base (p:cm_program) (fid:int)
       (st:cm_src_state) : cm_src_state =
       cm_state_make
         (tower_setw (cm_state_mem st)
           (cm_state_fp st -
            cm_frame_size (cm_program_structs p)
              (inth fid (cm_program_functions p)))
           (cm_state_fp st))
         (cm_clear_init (cm_state_init st)
           ((cm_state_fp st -
             cm_frame_size (cm_program_structs p)
               (inth fid (cm_program_functions p))) + 8i)
           (cm_call_param_span p fid))
         (cm_state_tags st)
         (cm_clear_tagged (cm_state_tagged st)
           ((cm_state_fp st -
             cm_frame_size (cm_program_structs p)
               (inth fid (cm_program_functions p))) + 8i)
           (cm_call_param_span p fid))
         (cm_call_env p fid (cm_state_env st)
           (cm_state_fp st -
            cm_frame_size (cm_program_structs p)
              (inth fid (cm_program_functions p)))
           (cm_state_nextgen st))
         (cm_state_input st) (cm_state_output st)
         (cm_state_fp st -
          cm_frame_size (cm_program_structs p)
            (inth fid (cm_program_functions p)))
         (cm_state_nextgen st +
          ilength (cm_function_params
            (inth fid (cm_program_functions p))))
         (cm_regions_for_slots (cm_program_structs p)
            (cm_function_params
              (inth fid (cm_program_functions p)))
            (cm_state_nextgen st)
            ((cm_state_fp st -
              cm_frame_size (cm_program_structs p)
                (inth fid (cm_program_functions p))) + 8i) ++
          cm_state_regions st)`);

PROOF thm cm_store_params_reverse_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(!p fid index st.
        cm_store_params_reverse (p:cm_program) (fid:int)
          ([]:(cm_value)list) (index:int) (st:cm_src_state) = st) &&
     (!p fid v rest index st.
        cm_store_params_reverse (p:cm_program) (fid:int)
          ((v:cm_value) :: (rest:(cm_value)list))
          (index:int) (st:cm_src_state) =
        cm_state_store
          (cm_slot_ty
            (inth index
              (cm_function_params
                (inth fid (cm_program_functions p)))))
          (cm_state_env
            (cm_store_params_reverse p fid rest (index + 1i) st)
            2i index)
          v
          (cm_store_params_reverse p fid rest (index + 1i) st))`);

PROOF static thm cm_prove_call_pending_structure(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (st:cm_src_state).
         cm_state_fp (cm_call_pending_base p fid st) ==
           cm_state_fp st -
             cm_frame_size (cm_program_structs p)
               (inth fid (cm_program_functions p)) &&
         cm_state_nextgen (cm_call_pending_base p fid st) ==
           cm_state_nextgen st +
             ilength (cm_function_params
               (inth fid (cm_program_functions p))) &&
         cm_state_regions (cm_call_pending_base p fid st) ==
           cm_regions_for_slots (cm_program_structs p)
             (cm_function_params
               (inth fid (cm_program_functions p)))
             (cm_state_nextgen st)
             ((cm_state_fp st -
               cm_frame_size (cm_program_structs p)
                 (inth fid (cm_program_functions p))) + 8i) ++
           cm_state_regions st &&
         cm_state_input (cm_call_pending_base p fid st) ==
           cm_state_input st &&
         cm_state_output (cm_call_pending_base p fid st) ==
           cm_state_output st`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm_list rules = get_cm_state_core_defs();
  vector_add(&rules, cm_call_pending_base_def);
  CONV_TAC(leaf, reduce_rewrite_conv(rules));
  return gnode_prove(root);
}
PROOF thm cm_call_pending_structure =
    cm_prove_call_pending_structure();

PROOF static thm cm_prove_store_params_reverse_structure(void) {
  gnode root = gnode_new_with_ccl(
      `!(values:(cm_value)list).
         !(p:cm_program) (fid:int) (index:int) (st:cm_src_state).
           cm_state_fp
             (cm_store_params_reverse p fid values index st) ==
             cm_state_fp st &&
           cm_state_nextgen
             (cm_store_params_reverse p fid values index st) ==
             cm_state_nextgen st &&
           cm_state_regions
             (cm_store_params_reverse p fid values index st) ==
             cm_state_regions st &&
           cm_state_input
             (cm_store_params_reverse p fid values index st) ==
             cm_state_input st &&
           cm_state_output
             (cm_store_params_reverse p fid values index st) ==
             cm_state_output st`);
  gnode_list cases = INDUCT_TAC(root, `values:(cm_value)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        cm_store_params_reverse_def)));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    term tail_state =
        `cm_store_params_reverse (p:cm_program) (fid:int)
          (a1:(cm_value)list) ((index:int) + 1i)
          (st:cm_src_state)`;
    thm ih = specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `(index:int) + 1i`,
        `st:cm_src_state`),
        assume_rule(goal_lasmps(leaf->g)[0].tm));
    thm_list rules = get_cm_state_core_defs();
    vector_add(&rules, cm_store_params_reverse_def);
    vector_add(&rules, get_cm_state_store_def());
    vector_add(&rules, ih);
    CONV_TAC(leaf, reduce_rewrite_conv(rules));
  }
  return gnode_prove(root);
}
PROOF thm cm_store_params_reverse_structure =
    cm_prove_store_params_reverse_structure();

PROOF static thm cm_prove_call_pending_regions_bases(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (st:cm_src_state).
         cm_region_bases_below_equal
           (cm_state_regions (cm_call_pending_base p fid st))
           (cm_state_regions st) (cm_state_nextgen st)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm_list rules = get_cm_state_core_defs();
  vector_add(&rules, cm_call_pending_base_def);
  vector_add(&rules, cm_regions_for_slots_bases);
  CONV_TAC(leaf, reduce_rewrite_conv(rules));
  return gnode_prove(root);
}
PROOF thm cm_call_pending_regions_bases =
    cm_prove_call_pending_regions_bases();

PROOF thm get_cm_call_param_span_def(void) {
  return cm_call_param_span_def;
}
PROOF thm get_cm_call_pending_base_def(void) {
  return cm_call_pending_base_def;
}
PROOF thm get_cm_store_params_reverse_def(void) {
  return cm_store_params_reverse_def;
}
PROOF thm get_cm_call_pending_structure(void) {
  return cm_call_pending_structure;
}
PROOF thm get_cm_store_params_reverse_structure(void) {
  return cm_store_params_reverse_structure;
}
PROOF thm get_cm_call_pending_regions_bases(void) {
  return cm_call_pending_regions_bases;
}

PROOF static int cmc_preservation_call_pending_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_call_pending_axioms_before,
      "cmc_preservation_call_pending introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_call_pending_checks =
    cmc_preservation_call_pending_final_checks();
