#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_target_access.h"

#require "cmc_preservation_runtime.c"

PROOF static size_t _cmc_preservation_target_access_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_prove_pointer_live_region_witness(void) {
  gnode root = gnode_new_with_ccl(
      `!(regions:(cm_region)list) (ptr:cm_value).
         cm_pointer_region_ok regions ptr F ==>
         ?region.
           MEM region regions &&
           cm_region_gen region == cm_ptr_gen ptr &&
           cm_region_live region &&
           cm_region_lo region <= cm_ptr_lo ptr &&
           cm_ptr_hi ptr <= cm_region_hi region`);
  gnode with_regions = GEN_TAC(root, "regions");
  gnode_list cases = INDUCT_TAC(with_regions, `regions:(cm_region)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm impossible = conv_rule(reduce_rewrite_conv(THM_LIST(
        get_cm_pointer_region_ok_def())), assume_rule(
          `cm_pointer_region_ok ([]:(cm_region)list)
            (ptr:cm_value) F`));
    CONTR_TAC(leaf, impossible);
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm opened = conv_rule(rewrite_conv(THM_LIST(
        get_cm_pointer_region_ok_def())), assume_rule(
          `cm_pointer_region_ok
            ((a0:cm_region) :: (a1:(cm_region)list))
            (ptr:cm_value) F`));
    thm at_head = assume_rule(
        `cm_region_gen (a0:cm_region) == cm_ptr_gen (ptr:cm_value) &&
         cm_region_live a0 && cm_region_lo a0 <= cm_ptr_lo ptr &&
         cm_ptr_hi ptr <= cm_region_hi a0`);
    thm head_mem = eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(get_theorem_by_name("MEM"))),
        `MEM (a0:cm_region)
          ((a0:cm_region) :: (a1:(cm_region)list))`));
    thm head_proof = conj_rule(head_mem, at_head);
    term goal_exists =
        `?region.
           MEM region ((a0:cm_region) :: (a1:(cm_region)list)) &&
           cm_region_gen region == cm_ptr_gen (ptr:cm_value) &&
           cm_region_live region &&
           cm_region_lo region <= cm_ptr_lo ptr &&
           cm_ptr_hi ptr <= cm_region_hi region`;
    thm head_exists = exists_rule(goal_exists, `a0:cm_region`, head_proof);

    thm tail_exists = match_mp_rule(
        spec_rule(`ptr:cm_value`, assume_rule(goal_lasmps(leaf->g)[0].tm)),
        assume_rule(
          `cm_pointer_region_ok (a1:(cm_region)list)
            (ptr:cm_value) F`));
    thm tail_body = assume_rule(
        `MEM (region:cm_region) (a1:(cm_region)list) &&
         cm_region_gen region == cm_ptr_gen (ptr:cm_value) &&
         cm_region_live region &&
         cm_region_lo region <= cm_ptr_lo ptr &&
         cm_ptr_hi ptr <= cm_region_hi region`);
    thm tail_mem = disj2_rule(
        `(region:cm_region) == (a0:cm_region)`, conjunct1_rule(tail_body));
    thm tail_cons_mem = eq_mp_rule(sym_rule(apply_conversion(
        rewrite_conv(THM_LIST(get_theorem_by_name("MEM"))),
        `MEM (region:cm_region)
          ((a0:cm_region) :: (a1:(cm_region)list))`)), tail_mem);
    thm tail_witness = exists_rule(goal_exists, `region:cm_region`,
        conj_rule(tail_cons_mem, conjunct2_rule(tail_body)));
    thm tail_case = choose_rule(`region:cm_region`, tail_exists,
        tail_witness);
    ACCEPT_TAC(leaf, disj_cases_rule(opened, head_exists, tail_case));
  }
  return gnode_prove(root);
}
PROOF thm cm_pointer_live_region_witness =
    cm_prove_pointer_live_region_witness();

PROOF static thm cm_prove_pointer_live_number(void) {
  gnode root = gnode_new_with_ccl(
      `!(st:cm_src_state) (ptr:cm_value).
         cm_pointer_live st ptr ==>
         cm_value_number st ptr ==
           tower_wrap64
             (cm_region_base (cm_state_regions st)
                (cm_ptr_gen ptr) + cm_ptr_offset ptr)`);
  gnode with_state = GEN_TAC(root, "st");
  gnode_list cases = INDUCT_TAC(with_state, `ptr:cm_value`);
  for (size_t i = 0; i < 3; ++i) {
    gnode leaf = AUTO_INTROS_TAC(cases[i]);
    thm impossible = conv_rule(reduce_rewrite_conv(THM_LIST(
        get_cm_pointer_live_def(), get_cm_ptr_gen_def())), assume_rule(
          goal_lasmps(leaf->g)[0].tm));
    CONTR_TAC(leaf, impossible);
  }
  CONV_TAC(AUTO_INTROS_TAC(cases[3]), reduce_rewrite_conv(THM_LIST(
      get_cm_value_number_def(), get_cm_ptr_gen_def(),
      get_cm_ptr_offset_def())));
  return gnode_prove(root);
}
PROOF thm cm_pointer_live_number = cm_prove_pointer_live_number();

PROOF static thm cm_prove_runtime_pointer_live_span(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (st:cm_src_state)
         (calls:(cm_call_sim_frame)list)
         (spill_frames:(cm_spill_frame)list)
         (ptr:cm_value) (width:int).
         cm_runtime_memory_layout p st calls spill_frames ==>
         cm_pointer_live st ptr ==>
         cm_ptr_lo ptr <= cm_ptr_offset ptr ==>
         cm_ptr_offset ptr + width <= cm_ptr_hi ptr ==>
         1i <= width ==>
         cm_live_span st (cm_value_number st ptr) width`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm layout = conv_rule(rewrite_conv(THM_LIST(
      cm_runtime_memory_layout_def, cm_regions_runtime_safe_def)),
      assume_rule(
        `cm_runtime_memory_layout (p:cm_program) (st:cm_src_state)
          (calls:(cm_call_sim_frame)list)
          (spill_frames:(cm_spill_frame)list)`));
  thm live = assume_rule(
      `cm_pointer_live (st:cm_src_state) (ptr:cm_value)`);
  thm live_open = conv_rule(rewrite_conv(THM_LIST(
      get_cm_pointer_live_def())), live);
  thm region_exists = match_mp_rule(specl_rule(TERM_LIST(
      `cm_state_regions (st:cm_src_state)`, `ptr:cm_value`),
      cm_pointer_live_region_witness),
      conjunct2_rule(conjunct2_rule(live_open)));
  thm witness = assume_rule(
      `MEM (region:cm_region) (cm_state_regions (st:cm_src_state)) &&
       cm_region_gen region == cm_ptr_gen (ptr:cm_value) &&
       cm_region_live region &&
       cm_region_lo region <= cm_ptr_lo ptr &&
       cm_ptr_hi ptr <= cm_region_hi region`);
  thm member = conjunct1_rule(witness);
  thm generation = conjunct1_rule(conjunct2_rule(witness));
  thm region_live = conjunct1_rule(conjunct2_rule(conjunct2_rule(witness)));
  thm region_lo_ptr = conjunct1_rule(conjunct2_rule(conjunct2_rule(
      conjunct2_rule(witness))));
  thm ptr_region_hi = conjunct2_rule(conjunct2_rule(conjunct2_rule(
      conjunct2_rule(witness))));
  thm region_safe = match_mp_rule(spec_rule(`region:cm_region`, layout),
      member);
  thm region_parts = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_region_runtime_safe_def, region_live)), region_safe);

  term base =
      `cm_region_base (cm_state_regions (st:cm_src_state))
        (cm_region_gen (region:cm_region))`;
  term raw = `${base:int} + cm_ptr_offset (ptr:cm_value)`;
  thm lower = mp_rule(mp_rule(int_arith_rule(
      `cm_region_lo (region:cm_region) <= cm_ptr_lo (ptr:cm_value) ==>
       cm_ptr_lo ptr <= cm_ptr_offset ptr ==>
       ${base:int} + cm_region_lo region <= ${raw:int}`),
      region_lo_ptr), assume_rule(
        `cm_ptr_lo (ptr:cm_value) <= cm_ptr_offset ptr`));
  thm upper = mp_rule(mp_rule(int_arith_rule(
      `cm_ptr_offset (ptr:cm_value) + (width:int) <= cm_ptr_hi ptr ==>
       cm_ptr_hi ptr <= cm_region_hi (region:cm_region) ==>
       ${raw:int} + width <= ${base:int} + cm_region_hi region`),
      assume_rule(
        `cm_ptr_offset (ptr:cm_value) + (width:int) <= cm_ptr_hi ptr`)),
      ptr_region_hi);
  thm raw_signed_bounds = int_arith_rule(
      `0i <= ${base:int} + cm_region_lo (region:cm_region) ==>
       ${base:int} + cm_region_lo region <= ${raw:int} ==>
       ${raw:int} + (width:int) <= ${base:int} + cm_region_hi region ==>
       ${base:int} + cm_region_hi region <= 1048576i ==>
       1i <= width ==>
       --9223372036854775808i <= ${raw:int} &&
       ${raw:int} <= 9223372036854775807i`);
  raw_signed_bounds = mp_rule(raw_signed_bounds,
      conjunct1_rule(conjunct2_rule(conjunct2_rule(region_parts))));
  raw_signed_bounds = mp_rule(raw_signed_bounds, lower);
  raw_signed_bounds = mp_rule(raw_signed_bounds, upper);
  raw_signed_bounds = mp_rule(raw_signed_bounds,
      conjunct1_rule(conjunct2_rule(conjunct2_rule(
        conjunct2_rule(region_parts)))));
  raw_signed_bounds = mp_rule(raw_signed_bounds,
      assume_rule(`1i <= (width:int)`));
  thm raw_signed = eq_mp_rule(sym_rule(apply_conversion(
      rewrite_conv(THM_LIST(get_tower_signed64_def())),
      `tower_signed64 ${raw:int}`)), raw_signed_bounds);
  thm raw_fixed = mp_rule(spec_rule(raw, get_tower_wrap64_fixed()),
      raw_signed);
  thm pointer_number = match_mp_rule(specl_rule(TERM_LIST(
      `st:cm_src_state`, `ptr:cm_value`), cm_pointer_live_number), live);
  pointer_number = conv_rule(rewrite_conv(THM_LIST(sym_rule(generation))),
      pointer_number);
  thm number_raw = trans_rule(pointer_number, raw_fixed);

  term interval =
      `cm_value_number (st:cm_src_state) (ptr:cm_value) <= (addr:int) &&
       addr < cm_value_number st ptr + (width:int)`;
  thm raw_interval = conv_rule(rewrite_conv(THM_LIST(number_raw)),
      assume_rule(interval));
  thm address_bounds = mp_rule(mp_rule(mp_rule(int_arith_rule(
      `${base:int} + cm_region_lo (region:cm_region) <= ${raw:int} ==>
       ${raw:int} + (width:int) <= ${base:int} + cm_region_hi region ==>
       ${raw:int} <= (addr:int) && addr < ${raw:int} + width ==>
       ${base:int} + cm_region_lo region <= addr &&
       addr < ${base:int} + cm_region_hi region`),
      lower), upper), raw_interval);
  thm live_body = conj_rule(member, conj_rule(region_live,
      address_bounds));
  thm live_exists = exists_rule(
      `?candidate.
         MEM candidate (cm_state_regions (st:cm_src_state)) &&
         cm_region_live candidate &&
         cm_region_base (cm_state_regions st)
             (cm_region_gen candidate) + cm_region_lo candidate <=
           (addr:int) &&
         addr < cm_region_base (cm_state_regions st)
             (cm_region_gen candidate) + cm_region_hi candidate`,
      `region:cm_region`, live_body);
  thm live_address = eq_mp_rule(sym_rule(apply_conversion(
      rewrite_conv(THM_LIST(cm_live_address_def)),
      `cm_live_address (st:cm_src_state) (addr:int)`)), live_exists);
  thm span_open = gen_rule(`addr:int`, disch_rule(interval, live_address));
  thm span = eq_mp_rule(sym_rule(apply_conversion(
      rewrite_conv(THM_LIST(cm_live_span_def)),
      `cm_live_span (st:cm_src_state)
        (cm_value_number st (ptr:cm_value)) (width:int)`)), span_open);
  ACCEPT_TAC(leaf, choose_rule(`region:cm_region`, region_exists, span));
  return gnode_prove(root);
}
PROOF thm cm_runtime_pointer_live_span =
    cm_prove_runtime_pointer_live_span();

PROOF thm get_cm_pointer_live_region_witness(void) {
  return cm_pointer_live_region_witness;
}
PROOF thm get_cm_pointer_live_number(void) {
  return cm_pointer_live_number;
}
PROOF thm get_cm_runtime_pointer_live_span(void) {
  return cm_runtime_pointer_live_span;
}

PROOF static int cmc_preservation_target_access_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_target_access_axioms_before,
      "cmc_preservation_target_access introduced an axiom");
  ENSURE_COND(vector_size(hyp(cm_pointer_live_region_witness)) == 0 &&
      vector_size(hyp(cm_pointer_live_number)) == 0 &&
      vector_size(hyp(cm_runtime_pointer_live_span)) == 0,
      "target access theorem has hypotheses");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_target_access_checks =
    cmc_preservation_target_access_final_checks();
