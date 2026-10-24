#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_call_value.h"

#require "cmc_preservation_invariant_step.c"

PROOF static size_t _cmc_preservation_call_value_axioms_before =
    vector_size(get_all_axioms());

PROOF thm cm_value_generation_below_def = new_rec_definition(
    get_cm_value_recursion(),
    `(!limit n.
        cm_value_generation_below (limit:int) (CMIntV (n:int)) = T) &&
     (!limit n.
        cm_value_generation_below (limit:int) (CMCharV (n:int)) = T) &&
     (!limit.
        cm_value_generation_below (limit:int) CMNullV = T) &&
     (!limit gen lo hi off ty.
        cm_value_generation_below (limit:int)
          (CMPtrV (gen:int) (lo:int) (hi:int) (off:int) (ty:cm_type)) =
        (gen < limit))`);

PROOF thm cm_values_generation_below_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(!limit.
        cm_values_generation_below (limit:int) ([]:(cm_value)list) = T) &&
     (!limit v rest.
        cm_values_generation_below (limit:int)
          ((v:cm_value) :: (rest:(cm_value)list)) =
        (cm_value_generation_below limit v &&
         cm_values_generation_below limit rest))`);

PROOF static thm cm_prove_value_number_bases(void) {
  gnode root = gnode_new_with_ccl(
      `!(v:cm_value).
         !(old_state:cm_src_state) (new_state:cm_src_state) (limit:int).
           cm_region_bases_below_equal
             (cm_state_regions new_state) (cm_state_regions old_state) limit ==>
           cm_value_generation_below limit v ==>
           cm_value_number new_state v ==
           cm_value_number old_state v`);
  gnode_list cases = INDUCT_TAC(root, `v:cm_value`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        cm_value_generation_below_def, get_cm_value_number_def())));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        cm_value_generation_below_def, get_cm_value_number_def())));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[2]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        cm_value_generation_below_def, get_cm_value_number_def())));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[3]);
    thm bases = conv_rule(
        rewrite_conv(THM_LIST(cm_region_bases_below_equal_def)),
        assume_rule(
          `cm_region_bases_below_equal
             (cm_state_regions (new_state:cm_src_state))
             (cm_state_regions (old_state:cm_src_state)) (limit:int)`));
    thm bound = conv_rule(
        rewrite_conv(THM_LIST(cm_value_generation_below_def)),
        assume_rule(
          `cm_value_generation_below (limit:int)
             (CMPtrV (a0:int) (a1:int) (a2:int) (a3:int)
               (a4:cm_type))`));
    thm base = mp_rule(
        ispec_rule(`a0:int`, bases), bound);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        cm_value_generation_below_def, get_cm_value_number_def(), base)));
  }
  return gnode_prove(root);
}
PROOF thm cm_value_number_bases = cm_prove_value_number_bases();

PROOF static thm cm_prove_values_number_bases(void) {
  gnode root = gnode_new_with_ccl(
      `!(values:(cm_value)list).
         !(old_state:cm_src_state) (new_state:cm_src_state) (limit:int).
           cm_region_bases_below_equal
             (cm_state_regions new_state) (cm_state_regions old_state) limit ==>
           cm_values_generation_below limit values ==>
           MAP (cm_value_number new_state) values ==
           MAP (cm_value_number old_state) values`);
  gnode_list cases = INDUCT_TAC(root, `values:(cm_value)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        cm_values_generation_below_def, get_theorem_by_name("MAP"))));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm below = conv_rule(
        rewrite_conv(THM_LIST(cm_values_generation_below_def)),
        assume_rule(
          `cm_values_generation_below (limit:int)
             ((a0:cm_value) :: (a1:(cm_value)list))`));
    thm head = mp_rule(mp_rule(
        specl_rule(TERM_LIST(
          `a0:cm_value`, `old_state:cm_src_state`,
          `new_state:cm_src_state`, `limit:int`),
          cm_value_number_bases),
        assume_rule(
          `cm_region_bases_below_equal
             (cm_state_regions (new_state:cm_src_state))
             (cm_state_regions (old_state:cm_src_state)) (limit:int)`)),
        conjunct1_rule(below));
    thm tail = mp_rule(mp_rule(
        specl_rule(TERM_LIST(
          `old_state:cm_src_state`, `new_state:cm_src_state`,
          `limit:int`), assume_rule(goal_lasmps(leaf->g)[0].tm)),
        assume_rule(
          `cm_region_bases_below_equal
             (cm_state_regions (new_state:cm_src_state))
             (cm_state_regions (old_state:cm_src_state)) (limit:int)`)),
        conjunct2_rule(below));
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        cm_values_generation_below_def, get_theorem_by_name("MAP"),
        head, tail)));
  }
  return gnode_prove(root);
}
PROOF thm cm_values_number_bases = cm_prove_values_number_bases();

PROOF static thm cm_prove_store_params_regions(void) {
  gnode root = gnode_new_with_ccl(
      `!(values:(cm_value)list).
         !(p:cm_program) (fid:int) (index:int) (state:cm_src_state).
           cm_state_regions
             (cm_store_params p fid values index state) ==
           cm_state_regions state`);
  gnode_list cases = INDUCT_TAC(root, `values:(cm_value)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        get_cm_store_params_def())));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm ih = specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `(index:int) + 1i`,
        `cm_state_store
           (cm_slot_ty
             (inth (index:int)
               (cm_function_params
                 (inth (fid:int) (cm_program_functions (p:cm_program))))))
           (cm_state_env (state:cm_src_state) 2i index)
           (a0:cm_value) state`),
        assume_rule(goal_lasmps(leaf->g)[0].tm));
    gnode recursive = CONV_TAC(
        leaf, reduce_rewrite_conv(THM_LIST(
          get_cm_store_params_def(), ih)));
    thm_list rules = get_cm_state_core_defs();
    vector_add(&rules, get_cm_state_store_def());
    CONV_TAC(recursive, reduce_rewrite_conv(rules));
  }
  return gnode_prove(root);
}
PROOF static thm cm_store_params_regions =
    cm_prove_store_params_regions();

PROOF static thm cm_prove_call_regions_bases(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (state:cm_src_state) (values:(cm_value)list).
         cm_region_bases_below_equal
           (cm_state_regions (cm_enter_call p fid values state))
           (cm_state_regions state)
           (cm_state_nextgen state)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm_list rules = get_cm_state_core_defs();
  vector_add(&rules, get_cm_enter_call_def());
  vector_add(&rules, get_cm_store_params_def());
  vector_add(&rules, get_cm_state_store_def());
  vector_add(&rules, get_cm_call_base_state_def());
  vector_add(&rules, cm_store_params_regions);
  vector_add(&rules, cm_regions_for_slots_bases);
  CONV_TAC(leaf, reduce_rewrite_conv(rules));
  return gnode_prove(root);
}
PROOF thm cm_call_regions_bases = cm_prove_call_regions_bases();

PROOF thm get_cm_value_generation_below_def(void) {
  return cm_value_generation_below_def;
}
PROOF thm get_cm_values_generation_below_def(void) {
  return cm_values_generation_below_def;
}
PROOF thm get_cm_value_number_bases(void) {
  return cm_value_number_bases;
}
PROOF thm get_cm_values_number_bases(void) {
  return cm_values_number_bases;
}
PROOF thm get_cm_call_regions_bases(void) {
  return cm_call_regions_bases;
}

PROOF static int cmc_preservation_call_value_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_call_value_axioms_before,
      "cmc_preservation_call_value introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_call_value_checks =
    cmc_preservation_call_value_final_checks();
