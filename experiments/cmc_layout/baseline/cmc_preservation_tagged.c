#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_tagged.h"
#include "cmc_preservation_store_semantic.h"

#require "cmc_preservation_store_semantic.c"
#require "cmc_preservation_invariant.c"

PROOF static size_t _cmc_preservation_tagged_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_prove_pointer_store_width(void) {
  gnode root_node = gnode_new_with_ccl(
      `!(ty:cm_type).
         cm_is_pointer ty ==> cm_store_width ty == 8i`);
  gnode_list cases = INDUCT_TAC(root_node, `ty:cm_type`);
  thm distinct = get_datatype_distinctness("cm_type");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    CONV_TAC(cases[i], reduce_rewrite_conv(THM_LIST(
        get_cm_is_pointer_def(), get_cm_store_width_def(), distinct)));
  }
  return gnode_prove(root_node);
}
PROOF static thm cm_pointer_store_width =
    cm_prove_pointer_store_width();

PROOF static thm cm_prove_runtime_store_live_span(void) {
  gnode root_node = gnode_new_with_ccl(
      `!(p:cm_program) (st:cm_src_state)
         (calls:(cm_call_sim_frame)list)
         (frames:(cm_spill_frame)list)
         (ty:cm_type) (ptr:cm_value).
         cm_runtime_memory_layout p st calls frames ==>
         cm_store_ok ty ptr st ==>
         cm_is_pointer ty ==>
         cm_live_span st (cm_value_number st ptr) 8i`);
  gnode leaf = AUTO_INTROS_TAC(root_node);
  thm layout = conv_rule(rewrite_conv(THM_LIST(
      cm_runtime_memory_layout_def, cm_regions_runtime_safe_def)),
      assume_rule(
        `cm_runtime_memory_layout (p:cm_program) (st:cm_src_state)
          (calls:(cm_call_sim_frame)list)
          (frames:(cm_spill_frame)list)`));
  thm store = conv_rule(rewrite_conv(THM_LIST(
      get_cm_store_ok_def())), assume_rule(
        `cm_store_ok (ty:cm_type) (ptr:cm_value)
          (st:cm_src_state)`));
  thm writable = conjunct1_rule(store);
  thm writable_parts = conv_rule(rewrite_conv(THM_LIST(
      get_cm_pointer_writable_def())), writable);
  thm region_exists = match_mp_rule(specl_rule(TERM_LIST(
      `cm_state_regions (st:cm_src_state)`, `ptr:cm_value`),
      cm_pointer_region_witness), conjunct2_rule(writable_parts));

  thm witness = assume_rule(
      `MEM (region:cm_region) (cm_state_regions (st:cm_src_state)) &&
       cm_region_gen region == cm_ptr_gen (ptr:cm_value) &&
       cm_region_live region && cm_region_writable region &&
       cm_region_lo region <= cm_ptr_lo ptr &&
       cm_ptr_hi ptr <= cm_region_hi region`);
  thm member = conjunct1_rule(witness);
  thm live = mp_rule(taut_rule(mk_imp(concl(witness),
      `cm_region_live (region:cm_region)`)), witness);
  thm can_write = mp_rule(taut_rule(mk_imp(concl(witness),
      `cm_region_writable (region:cm_region)`)), witness);
  thm region_safe = mp_rule(
      spec_rule(`region:cm_region`, layout), member);
  thm region_parts = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_region_runtime_safe_def, live, can_write)), region_safe);

  term region_base =
      `cm_region_base (cm_state_regions (st:cm_src_state))
        (cm_region_gen (region:cm_region))`;
  term raw_address =
      `${region_base:int} + cm_ptr_offset (ptr:cm_value)`;
  thm region_lo_ptr = mp_rule(taut_rule(mk_imp(concl(witness),
      `cm_region_lo (region:cm_region) <=
       cm_ptr_lo (ptr:cm_value)`)), witness);
  thm ptr_region_hi = mp_rule(taut_rule(mk_imp(concl(witness),
      `cm_ptr_hi (ptr:cm_value) <=
       cm_region_hi (region:cm_region)`)), witness);
  thm ptr_lo_offset = conjunct1_rule(conjunct2_rule(store));
  thm offset_width = conjunct1_rule(
      conjunct2_rule(conjunct2_rule(store)));
  thm width = mp_rule(spec_rule(`ty:cm_type`, cm_pointer_store_width),
      assume_rule(`cm_is_pointer (ty:cm_type)`));
  thm lower = mp_rule(mp_rule(int_arith_rule(
      `cm_region_lo (region:cm_region) <= cm_ptr_lo (ptr:cm_value) ==>
       cm_ptr_lo ptr <= cm_ptr_offset ptr ==>
       ${region_base:int} + cm_region_lo region <=
         ${raw_address:int}`), region_lo_ptr), ptr_lo_offset);
  thm upper = mp_rule(mp_rule(mp_rule(int_arith_rule(
      `cm_ptr_offset (ptr:cm_value) + cm_store_width (ty:cm_type) <=
         cm_ptr_hi ptr ==>
       cm_ptr_hi ptr <= cm_region_hi (region:cm_region) ==>
       cm_store_width ty == 8i ==>
       ${raw_address:int} + 8i <=
         ${region_base:int} + cm_region_hi region`),
      offset_width), ptr_region_hi), width);
  thm region_start_nonnegative =
      conjunct1_rule(conjunct2_rule(conjunct2_rule(region_parts)));
  thm region_finish_upper = conjunct1_rule(conjunct2_rule(
      conjunct2_rule(conjunct2_rule(region_parts))));
  thm raw_bounds = mp_rule(mp_rule(mp_rule(mp_rule(int_arith_rule(
      `0i <= ${region_base:int} + cm_region_lo (region:cm_region) ==>
       ${region_base:int} + cm_region_lo region <= ${raw_address:int} ==>
       ${raw_address:int} + 8i <=
         ${region_base:int} + cm_region_hi region ==>
       ${region_base:int} + cm_region_hi region <= 1048576i ==>
       --9223372036854775808i <= ${raw_address:int} &&
       ${raw_address:int} <= 9223372036854775807i`),
      region_start_nonnegative), lower), upper), region_finish_upper);
  thm raw_signed = eq_mp_rule(sym_rule(apply_conversion(
      rewrite_conv(THM_LIST(get_tower_signed64_def())),
      `tower_signed64 ${raw_address:int}`)), raw_bounds);
  thm raw_fixed = mp_rule(
      spec_rule(raw_address, get_tower_wrap64_fixed()), raw_signed);
  thm pointer_number = match_mp_rule(specl_rule(TERM_LIST(
      `st:cm_src_state`, `ptr:cm_value`),
      cm_pointer_writable_number), writable);
  thm generation = mp_rule(taut_rule(mk_imp(concl(witness),
      `cm_region_gen (region:cm_region) ==
       cm_ptr_gen (ptr:cm_value)`)), witness);
  pointer_number = conv_rule(rewrite_conv(
      THM_LIST(sym_rule(generation))), pointer_number);
  thm number_raw = trans_rule(pointer_number, raw_fixed);

  term target_span =
      `cm_live_span (st:cm_src_state)
        (cm_value_number st (ptr:cm_value)) 8i`;
  thm target_view = apply_conversion(rewrite_conv(THM_LIST(
      cm_live_span_def)), target_span);
  term interval_term =
      `cm_value_number (st:cm_src_state) (ptr:cm_value) <=
         (addr:int) &&
       addr < cm_value_number st ptr + 8i`;
  thm interval = assume_rule(interval_term);
  thm raw_interval = conv_rule(rewrite_conv(
      THM_LIST(number_raw)), interval);
  thm address_bounds = mp_rule(mp_rule(mp_rule(int_arith_rule(
      `${region_base:int} + cm_region_lo (region:cm_region) <=
         ${raw_address:int} ==>
       ${raw_address:int} + 8i <=
         ${region_base:int} + cm_region_hi region ==>
       ${raw_address:int} <= (addr:int) &&
         addr < ${raw_address:int} + 8i ==>
       ${region_base:int} + cm_region_lo region <= addr &&
         addr < ${region_base:int} + cm_region_hi region`),
      lower), upper), raw_interval);
  thm body_proof = conj_rule(member, conj_rule(live, address_bounds));
  thm exists = exists_rule(
      `?candidate.
         MEM candidate (cm_state_regions (st:cm_src_state)) &&
         cm_region_live candidate &&
         cm_region_base (cm_state_regions st)
             (cm_region_gen candidate) + cm_region_lo candidate <=
           (addr:int) &&
         addr < cm_region_base (cm_state_regions st)
             (cm_region_gen candidate) + cm_region_hi candidate`,
      `region:cm_region`, body_proof);
  term live_term =
      `cm_live_address (st:cm_src_state) (addr:int)`;
  thm folded_live = eq_mp_rule(sym_rule(apply_conversion(
      rewrite_conv(THM_LIST(cm_live_address_def)), live_term)), exists);
  thm normalized_proof = gen_rule(`addr:int`,
      disch_rule(interval_term, folded_live));
  thm span_proof = eq_mp_rule(sym_rule(target_view), normalized_proof);
  thm selected = choose_rule(`region:cm_region`, region_exists,
      span_proof);
  ACCEPT_TAC(leaf, selected);
  return gnode_prove(root_node);
}
PROOF thm cm_runtime_store_live_span =
    cm_prove_runtime_store_live_span();

PROOF static thm cm_prove_tagged_span_store(void) {
  gnode root_node = gnode_new_with_ccl(
      `!(p:cm_program) (st:cm_src_state)
         (calls:(cm_call_sim_frame)list)
         (frames:(cm_spill_frame)list)
         (ty:cm_type) (ptr:cm_value) (v:cm_value).
         cm_runtime_memory_layout p st calls frames ==>
         cm_store_ok ty ptr st ==>
         cm_tagged_span_valid st ==>
         cm_tagged_span_valid (cm_state_store ty ptr v st)`);
  gnode leaf = AUTO_INTROS_TAC(root_node);
  thm old_valid = conv_rule(rewrite_conv(THM_LIST(
      cm_tagged_span_valid_def)), assume_rule(
        `cm_tagged_span_valid (st:cm_src_state)`));
  gnode opened = CONV_TAC(leaf, rewrite_conv(THM_LIST(
      cm_tagged_span_valid_def)));
  gnode at_address = AUTO_INTROS_TAC(opened);
  thm new_parts = assume_rule(
      `cm_state_tagged
         (cm_state_store (ty:cm_type) (ptr:cm_value)
           (v:cm_value) (st:cm_src_state)) (addr:int) &&
       cm_live_address
         (cm_state_store (ty:cm_type) (ptr:cm_value)
           (v:cm_value) (st:cm_src_state)) addr`);
  thm new_tagged = conjunct1_rule(new_parts);
  thm new_live = conjunct2_rule(new_parts);
  thm old_live = eq_mp_rule(specl_rule(TERM_LIST(
      `ty:cm_type`, `ptr:cm_value`, `v:cm_value`,
      `st:cm_src_state`, `addr:int`), cm_live_address_store), new_live);
  thm_list store_rules = get_cm_state_core_defs();
  vector_add(&store_rules, get_cm_state_store_def());
  vector_add(&store_rules, get_cm_clear_tagged_def());
  thm raw_tagged = conv_rule(
      reduce_rewrite_conv(store_rules), new_tagged);
  gnode_list pointer_cases = BOOL_CASES_TAC(
      at_address, `cm_is_pointer (ty:cm_type)`, "Hpointer");
  {
    thm is_pointer = assume_rule(`cm_is_pointer (ty:cm_type)`);
    thm pointer_tagged = conv_rule(reduce_rewrite_conv(
        THM_LIST(is_pointer)), raw_tagged);
    struct dest_disj_results tag_cases = dest_disj(concl(pointer_tagged));
    thm at_base = assume_rule(tag_cases.tm1);
    thm old_case = assume_rule(tag_cases.tm2);
    thm base_span = match_mp_rule(match_mp_rule(match_mp_rule(
        specl_rule(TERM_LIST(
          `p:cm_program`, `st:cm_src_state`,
          `calls:(cm_call_sim_frame)list`,
          `frames:(cm_spill_frame)list`, `ty:cm_type`,
          `ptr:cm_value`), cm_runtime_store_live_span),
        assume_rule(
          `cm_runtime_memory_layout (p:cm_program) (st:cm_src_state)
            (calls:(cm_call_sim_frame)list)
            (frames:(cm_spill_frame)list)`)),
        assume_rule(
          `cm_store_ok (ty:cm_type) (ptr:cm_value)
            (st:cm_src_state)`)), is_pointer);
    thm new_base_span = specl_rule(TERM_LIST(
        `ty:cm_type`, `ptr:cm_value`, `v:cm_value`,
        `st:cm_src_state`,
        `cm_value_number (st:cm_src_state) (ptr:cm_value)`, `8i`),
        cm_store_live_span);
    new_base_span = mp_rule(new_base_span, base_span);
    thm base_result = conv_rule(rewrite_conv(THM_LIST(
        sym_rule(conjunct1_rule(at_base)))), new_base_span);
    thm old_span = mp_rule(spec_rule(`addr:int`, old_valid),
        conj_rule(conjunct1_rule(old_case), old_live));
    thm old_result = mp_rule(specl_rule(TERM_LIST(
        `ty:cm_type`, `ptr:cm_value`, `v:cm_value`,
        `st:cm_src_state`, `addr:int`, `8i`),
        cm_store_live_span), old_span);
    ACCEPT_TAC(pointer_cases[0],
        disj_cases_rule(pointer_tagged, base_result, old_result));
  }
  {
    thm not_pointer =
        assume_rule(`~cm_is_pointer (ty:cm_type)`);
    thm old_case = conv_rule(reduce_rewrite_conv(
        THM_LIST(not_pointer)), raw_tagged);
    thm old_span = mp_rule(spec_rule(`addr:int`, old_valid),
        conj_rule(conjunct1_rule(old_case), old_live));
    thm result = mp_rule(specl_rule(TERM_LIST(
        `ty:cm_type`, `ptr:cm_value`, `v:cm_value`,
        `st:cm_src_state`, `addr:int`, `8i`),
        cm_store_live_span), old_span);
    ACCEPT_TAC(pointer_cases[1], result);
  }
  return gnode_prove(root_node);
}
PROOF thm cm_tagged_span_store = cm_prove_tagged_span_store();

PROOF static thm cm_prove_tagged_span_initial(void) {
  gnode root_node = gnode_new_with_ccl(
      `!(p:cm_program) (input:(int)list).
         cm_tagged_span_valid (cm_initial_state p input)`);
  gnode leaf = AUTO_INTROS_TAC(root_node);
  thm_list rules = get_cm_state_core_defs();
  vector_add(&rules, cm_tagged_span_valid_def);
  vector_add(&rules, get_cm_initial_state_def());
  CONV_TAC(leaf, reduce_rewrite_conv(rules));
  return gnode_prove(root_node);
}
PROOF thm cm_tagged_span_initial =
    cm_prove_tagged_span_initial();

PROOF static int cmc_preservation_tagged_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_tagged_axioms_before,
      "cmc_preservation_tagged introduced an axiom");
  ENSURE_COND(vector_size(hyp(cm_runtime_store_live_span)) == 0,
      "runtime store live-span theorem is not closed");
  ENSURE_COND(vector_size(hyp(cm_tagged_span_store)) == 0,
      "tagged-span store theorem is not closed");
  ENSURE_COND(vector_size(hyp(cm_tagged_span_initial)) == 0,
      "tagged-span initial theorem is not closed");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_tagged_checks =
    cmc_preservation_tagged_final_checks();
