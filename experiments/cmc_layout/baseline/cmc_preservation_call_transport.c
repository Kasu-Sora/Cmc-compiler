#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_call_transport.h"

#require "cmc_preservation_call_pending.c"

PROOF static size_t _cmc_preservation_call_transport_axioms_before =
    vector_size(get_all_axioms());

PROOF thm cm_spills_generation_below_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(!limit.
        cm_spills_generation_below (limit:int)
          ([]:(cm_spill)list) = T) &&
     (!limit spill rest.
        cm_spills_generation_below (limit:int)
          ((spill:cm_spill) :: (rest:(cm_spill)list)) =
        (cm_value_generation_below limit (cm_spill_value spill) &&
         cm_spills_generation_below limit rest))`);

PROOF thm cm_spill_frames_generation_below_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(!limit.
        cm_spill_frames_generation_below (limit:int)
          ([]:(cm_spill_frame)list) = T) &&
     (!limit frame rest.
        cm_spill_frames_generation_below (limit:int)
          ((frame:cm_spill_frame) ::
           (rest:(cm_spill_frame)list)) =
        (cm_spills_generation_below limit
           (cm_spill_frame_spills frame) &&
         cm_spill_frames_generation_below limit rest))`);

PROOF thm cm_state_tags_generation_below_def = new_fun_definition(
    `cm_state_tags_generation_below (st:cm_src_state)
       (limit:int) : bool =
       !addr.
         cm_state_tagged st addr ==>
         cm_value_generation_below limit (cm_state_tags st addr)`);

PROOF static thm cm_prove_spill_list_sim_bases(void) {
  gnode root = gnode_new_with_ccl(
      `!(spills:(cm_spill)list).
         !(p:cm_program) (old_state:cm_src_state)
           (new_state:cm_src_state) (mem:int->int)
           (fid:int) (fp:int) (limit:int).
           cm_region_bases_below_equal
             (cm_state_regions new_state)
             (cm_state_regions old_state) limit ==>
           cm_spills_generation_below limit spills ==>
           cm_spill_list_sim p old_state mem fid fp spills ==>
           cm_spill_list_sim p new_state mem fid fp spills`);
  gnode_list cases = INDUCT_TAC(root, `spills:(cm_spill)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        cm_spills_generation_below_def, cm_spill_list_sim_def)));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm below = conv_rule(rewrite_conv(THM_LIST(
        cm_spills_generation_below_def)), assume_rule(
          `cm_spills_generation_below (limit:int)
            ((a0:cm_spill) :: (a1:(cm_spill)list))`));
    thm old_sim = conv_rule(rewrite_conv(THM_LIST(
        cm_spill_list_sim_def)), assume_rule(
          `cm_spill_list_sim (p:cm_program)
            (old_state:cm_src_state) (mem:int->int)
            (fid:int) (fp:int)
            ((a0:cm_spill) :: (a1:(cm_spill)list))`));
    thm number = match_mp_rule(match_mp_rule(
        specl_rule(TERM_LIST(
          `cm_spill_value (a0:cm_spill)`,
          `old_state:cm_src_state`, `new_state:cm_src_state`,
          `limit:int`), cm_value_number_bases),
        assume_rule(
          `cm_region_bases_below_equal
            (cm_state_regions (new_state:cm_src_state))
            (cm_state_regions (old_state:cm_src_state))
            (limit:int)`)), conjunct1_rule(below));
    thm head = conv_rule(rewrite_conv(THM_LIST(sym_rule(number))),
        conjunct1_rule(old_sim));
    thm tail = match_mp_rule(match_mp_rule(match_mp_rule(
        specl_rule(TERM_LIST(
          `p:cm_program`, `old_state:cm_src_state`,
          `new_state:cm_src_state`, `mem:int->int`,
          `fid:int`, `fp:int`, `limit:int`),
          assume_rule(goal_lasmps(leaf->g)[0].tm)),
        assume_rule(
          `cm_region_bases_below_equal
            (cm_state_regions (new_state:cm_src_state))
            (cm_state_regions (old_state:cm_src_state))
            (limit:int)`)), conjunct2_rule(below)),
        conjunct2_rule(old_sim));
    gnode opened = CONV_TAC(leaf,
        rewrite_conv(THM_LIST(cm_spill_list_sim_def)));
    ACCEPT_TAC(opened, conj_rule(head, tail));
  }
  return gnode_prove(root);
}
PROOF thm cm_spill_list_sim_bases =
    cm_prove_spill_list_sim_bases();

PROOF static thm cm_prove_spill_frames_sim_bases(void) {
  gnode root = gnode_new_with_ccl(
      `!(frames:(cm_spill_frame)list).
         !(p:cm_program) (old_state:cm_src_state)
           (new_state:cm_src_state) (mem:int->int) (limit:int).
           cm_region_bases_below_equal
             (cm_state_regions new_state)
             (cm_state_regions old_state) limit ==>
           cm_spill_frames_generation_below limit frames ==>
           cm_spill_frames_sim p old_state mem frames ==>
           cm_spill_frames_sim p new_state mem frames`);
  gnode_list cases = INDUCT_TAC(
      root, `frames:(cm_spill_frame)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        cm_spill_frames_generation_below_def,
        cm_spill_frames_sim_def)));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm below = conv_rule(rewrite_conv(THM_LIST(
        cm_spill_frames_generation_below_def)), assume_rule(
          `cm_spill_frames_generation_below (limit:int)
            ((a0:cm_spill_frame) ::
             (a1:(cm_spill_frame)list))`));
    thm old_sim = conv_rule(rewrite_conv(THM_LIST(
        cm_spill_frames_sim_def)), assume_rule(
          `cm_spill_frames_sim (p:cm_program)
            (old_state:cm_src_state) (mem:int->int)
            ((a0:cm_spill_frame) ::
             (a1:(cm_spill_frame)list))`));
    thm head = match_mp_rule(match_mp_rule(match_mp_rule(
        specl_rule(TERM_LIST(
          `cm_spill_frame_spills (a0:cm_spill_frame)`,
          `p:cm_program`, `old_state:cm_src_state`,
          `new_state:cm_src_state`, `mem:int->int`,
          `cm_spill_frame_fid (a0:cm_spill_frame)`,
          `cm_spill_frame_fp (a0:cm_spill_frame)`,
          `limit:int`), cm_spill_list_sim_bases),
        assume_rule(
          `cm_region_bases_below_equal
            (cm_state_regions (new_state:cm_src_state))
            (cm_state_regions (old_state:cm_src_state))
            (limit:int)`)), conjunct1_rule(below)),
        conjunct1_rule(old_sim));
    thm tail = match_mp_rule(match_mp_rule(match_mp_rule(
        specl_rule(TERM_LIST(
          `p:cm_program`, `old_state:cm_src_state`,
          `new_state:cm_src_state`, `mem:int->int`,
          `limit:int`), assume_rule(goal_lasmps(leaf->g)[0].tm)),
        assume_rule(
          `cm_region_bases_below_equal
            (cm_state_regions (new_state:cm_src_state))
            (cm_state_regions (old_state:cm_src_state))
            (limit:int)`)), conjunct2_rule(below)),
        conjunct2_rule(old_sim));
    gnode opened = CONV_TAC(leaf,
        rewrite_conv(THM_LIST(cm_spill_frames_sim_def)));
    ACCEPT_TAC(opened, conj_rule(head, tail));
  }
  return gnode_prove(root);
}
PROOF thm cm_spill_frames_sim_bases =
    cm_prove_spill_frames_sim_bases();

PROOF static thm cm_prove_encode_values_bases(void) {
  gnode root = gnode_new_with_ccl(
      `!(values:(cm_value)list).
         !(old_state:cm_src_state) (new_state:cm_src_state)
           (limit:int).
           cm_region_bases_below_equal
             (cm_state_regions new_state)
             (cm_state_regions old_state) limit ==>
           cm_values_generation_below limit values ==>
           cm_encode_values new_state values ==
           cm_encode_values old_state values`);
  gnode_list cases = INDUCT_TAC(root, `values:(cm_value)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        cm_values_generation_below_def, cm_encode_values_def)));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm below = conv_rule(rewrite_conv(THM_LIST(
        cm_values_generation_below_def)), assume_rule(
          `cm_values_generation_below (limit:int)
            ((a0:cm_value) :: (a1:(cm_value)list))`));
    thm head = match_mp_rule(match_mp_rule(
        specl_rule(TERM_LIST(
          `a0:cm_value`, `old_state:cm_src_state`,
          `new_state:cm_src_state`, `limit:int`),
          cm_value_number_bases),
        assume_rule(
          `cm_region_bases_below_equal
            (cm_state_regions (new_state:cm_src_state))
            (cm_state_regions (old_state:cm_src_state))
            (limit:int)`)), conjunct1_rule(below));
    thm tail = match_mp_rule(match_mp_rule(
        specl_rule(TERM_LIST(
          `old_state:cm_src_state`, `new_state:cm_src_state`,
          `limit:int`), assume_rule(goal_lasmps(leaf->g)[0].tm)),
        assume_rule(
          `cm_region_bases_below_equal
            (cm_state_regions (new_state:cm_src_state))
            (cm_state_regions (old_state:cm_src_state))
            (limit:int)`)), conjunct2_rule(below));
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        cm_encode_values_def, head, tail)));
  }
  return gnode_prove(root);
}
PROOF static thm cm_encode_values_bases =
    cm_prove_encode_values_bases();

PROOF static thm cm_prove_operand_suffix_sim_bases(void) {
  gnode root = gnode_new_with_ccl(
      `!(old_state:cm_src_state) (new_state:cm_src_state)
         (values:(cm_value)list) (suffix:(int)list)
         (stack:(int)list) (limit:int).
         cm_region_bases_below_equal
           (cm_state_regions new_state)
           (cm_state_regions old_state) limit ==>
         cm_values_generation_below limit values ==>
         cm_operand_suffix_sim old_state values suffix stack ==>
         cm_operand_suffix_sim new_state values suffix stack`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm encoded = match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(
        `values:(cm_value)list`, `old_state:cm_src_state`,
        `new_state:cm_src_state`, `limit:int`),
        cm_encode_values_bases),
      assume_rule(
        `cm_region_bases_below_equal
          (cm_state_regions (new_state:cm_src_state))
          (cm_state_regions (old_state:cm_src_state))
          (limit:int)`)), assume_rule(
        `cm_values_generation_below (limit:int)
          (values:(cm_value)list)`));
  thm old_sim = conv_rule(rewrite_conv(THM_LIST(
      cm_operand_suffix_sim_def)), assume_rule(
        `cm_operand_suffix_sim (old_state:cm_src_state)
          (values:(cm_value)list) (suffix:(int)list)
          (stack:(int)list)`));
  gnode opened = CONV_TAC(leaf,
      rewrite_conv(THM_LIST(cm_operand_suffix_sim_def)));
  ACCEPT_TAC(opened, trans_rule(old_sim, beta_norm(
      ap_term_rule(`\xs:(int)list. xs ++ (suffix:(int)list)`,
        sym_rule(encoded)))));
  return gnode_prove(root);
}
PROOF thm cm_operand_suffix_sim_bases =
    cm_prove_operand_suffix_sim_bases();

PROOF thm get_cm_spills_generation_below_def(void) {
  return cm_spills_generation_below_def;
}
PROOF thm get_cm_spill_frames_generation_below_def(void) {
  return cm_spill_frames_generation_below_def;
}
PROOF thm get_cm_state_tags_generation_below_def(void) {
  return cm_state_tags_generation_below_def;
}
PROOF thm get_cm_spill_list_sim_bases(void) {
  return cm_spill_list_sim_bases;
}
PROOF thm get_cm_spill_frames_sim_bases(void) {
  return cm_spill_frames_sim_bases;
}
PROOF thm get_cm_operand_suffix_sim_bases(void) {
  return cm_operand_suffix_sim_bases;
}

PROOF static int cmc_preservation_call_transport_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_call_transport_axioms_before,
      "cmc_preservation_call_transport introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_call_transport_checks =
    cmc_preservation_call_transport_final_checks();
