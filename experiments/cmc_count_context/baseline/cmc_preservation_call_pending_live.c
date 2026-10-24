#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_call_pending_live.h"

#require "cmc_preservation_call_transport.c"

PROOF static size_t _cmc_preservation_call_pending_live_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_prove_call_pending_live_old_or_param(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (st:cm_src_state) (addr:int).
         cm_function_wf p
           (inth fid (cm_program_functions p)) ==>
         cm_regions_before (cm_state_regions st)
           (cm_state_nextgen st) ==>
         cm_live_address (cm_call_pending_base p fid st) addr ==>
         cm_live_address st addr ||
         ((cm_state_fp st -
           cm_frame_size (cm_program_structs p)
             (inth fid (cm_program_functions p))) + 8i <= addr &&
          addr <
            (cm_state_fp st -
             cm_frame_size (cm_program_structs p)
               (inth fid (cm_program_functions p))) + 8i +
            cm_call_param_span p fid)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  term structs = `cm_program_structs (p:cm_program)`;
  term params =
      `cm_function_params
        (inth (fid:int) (cm_program_functions (p:cm_program)))`;
  term old_regions = `cm_state_regions (st:cm_src_state)`;
  term firstgen = `cm_state_nextgen (st:cm_src_state)`;
  term param_base =
      `(cm_state_fp (st:cm_src_state) -
        cm_frame_size (cm_program_structs (p:cm_program))
          (inth (fid:int) (cm_program_functions p))) + 8i`;
  term fresh =
      `cm_regions_for_slots ${structs:(cm_struct_d)list}
        ${params:(cm_slot_d)list} ${firstgen:int} ${param_base:int}`;
  term all_regions =
      `${fresh:(cm_region)list} ++ ${old_regions:(cm_region)list}`;

  thm function_open = conv_rule(rewrite_conv(THM_LIST(
      get_cm_function_wf_def())), assume_rule(
        `cm_function_wf (p:cm_program)
          (inth (fid:int) (cm_program_functions p))`));
  thm params_wf = conv_rule(rewrite_conv(THM_LIST(
      get_cm_params_wf_def())),
      conjunct1_rule(conjunct2_rule(function_open)));
  thm slots_wf = conjunct1_rule(params_wf);
  thm positive = match_mp_rule(ispecl_rule(TERM_LIST(
      structs, params), cm_slots_wf_sizes_positive), slots_wf);
  thm before = assume_rule(
      `cm_regions_before ${old_regions:(cm_region)list}
        ${firstgen:int}`);
  thm bases = conv_rule(rewrite_conv(THM_LIST(
      cm_region_bases_below_equal_def)),
      specl_rule(TERM_LIST(`p:cm_program`, `fid:int`,
        `st:cm_src_state`), cm_call_pending_regions_bases));

  thm_list pending_rules = get_cm_state_core_defs();
  vector_add(&pending_rules, cm_call_pending_base_def);
  thm live_exists = conv_rule(reduce_rewrite_conv(pending_rules),
      conv_rule(rewrite_conv(THM_LIST(cm_live_address_def)),
        assume_rule(
          `cm_live_address
            (cm_call_pending_base (p:cm_program) (fid:int)
              (st:cm_src_state)) (addr:int)`)));
  thm live_body = assume_rule(
      `MEM (region:cm_region) ${all_regions:(cm_region)list} &&
       cm_region_live region &&
       cm_region_base ${all_regions:(cm_region)list}
           (cm_region_gen region) + cm_region_lo region <= (addr:int) &&
       addr < cm_region_base ${all_regions:(cm_region)list}
           (cm_region_gen region) + cm_region_hi region`);
  thm member_split = conv_rule(rewrite_conv(THM_LIST(
      get_theorem_by_name("MEM_APPEND"))), conjunct1_rule(live_body));

  thm fresh_member = assume_rule(
      `MEM (region:cm_region) ${fresh:(cm_region)list}`);
  thm offset_exists = match_mp_rule(specl_rule(TERM_LIST(
      structs, params, firstgen, param_base, `region:cm_region`),
      cm_slot_region_member_index), fresh_member);
  thm offset_body = assume_rule(
      `0i <= (offset:int) &&
       offset < ilength ${params:(cm_slot_d)list} &&
       (region:cm_region) ==
         CMRegion (${firstgen:int} + offset)
           (${param_base:int} +
            cm_slots_prefix ${structs:(cm_struct_d)list}
              ${params:(cm_slot_d)list} offset)
           0i
           (cm_slot_size ${structs:(cm_struct_d)list}
             (inth offset ${params:(cm_slot_d)list})) T T`);
  thm prefix_bounds = match_mp_rule(match_mp_rule(match_mp_rule(
      ispecl_rule(TERM_LIST(structs, params),
        cm_slots_prefix_cell_bounds), positive),
      conjunct1_rule(offset_body)),
      conjunct1_rule(conjunct2_rule(offset_body)));
  thm lookup = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
      structs, params, firstgen, param_base,
      old_regions, `region:cm_region`),
      cm_slot_region_base_lookup), before), fresh_member);
  thm region_equal = conjunct2_rule(conjunct2_rule(offset_body));
  thm lookup_normal = conv_rule(reduce_rewrite_conv(THM_LIST(
      region_equal, get_cm_region_gen_def(),
      get_cm_region_base_field_def())), lookup);
  lookup_normal = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_region_gen_def(), get_cm_region_base_field_def())),
      lookup_normal);
  thm live_range = conj_rule(
      conjunct1_rule(conjunct2_rule(conjunct2_rule(live_body))),
      conjunct2_rule(conjunct2_rule(conjunct2_rule(live_body))));
  thm live_range_normal = conv_rule(reduce_rewrite_conv(THM_LIST(
      region_equal, get_cm_region_gen_def(),
      get_cm_region_lo_def(), get_cm_region_hi_def())),
      live_range);
  thm lower_bridge = beta_norm(ap_term_rule(
      `\base:int. base + 0i <= (addr:int)`, lookup_normal));
  thm upper_bridge = beta_norm(ap_term_rule(
      `\base:int.
         (addr:int) < base +
           cm_slot_size ${structs:(cm_struct_d)list}
             (inth (offset:int) ${params:(cm_slot_d)list})`,
      lookup_normal));
  thm lower = eq_mp_rule(lower_bridge,
      conjunct1_rule(live_range_normal));
  thm upper = eq_mp_rule(upper_bridge,
      conjunct2_rule(live_range_normal));
  thm fresh_facts =
      conj_rule(conj_rule(lower, upper), prefix_bounds);
  thm inside_slots = mp_rule(int_arith_rule(mk_imp(
      concl(fresh_facts),
      `${param_base:int} <= (addr:int) &&
       addr < ${param_base:int} +
         cm_slots_size ${structs:(cm_struct_d)list}
           ${params:(cm_slot_d)list}`)), fresh_facts);
  term conclusion_right =
      `${param_base:int} <= (addr:int) &&
       addr < ${param_base:int} +
         cm_call_param_span (p:cm_program) (fid:int)`;
  thm inside_view = apply_conversion(
      rewrite_conv(THM_LIST(cm_call_param_span_def)),
      conclusion_right);
  thm inside = eq_mp_rule(sym_rule(inside_view), inside_slots);
  thm fresh_result = disj2_rule(
      `cm_live_address (st:cm_src_state) (addr:int)`, inside);
  thm fresh_case = choose_rule(`offset:int`, offset_exists,
      fresh_result);

  thm old_member = assume_rule(
      `MEM (region:cm_region) ${old_regions:(cm_region)list}`);
  thm before_open = conv_rule(rewrite_conv(THM_LIST(
      cm_regions_before_def)), before);
  thm gen_bound = match_mp_rule(spec_rule(
      `region:cm_region`, before_open), old_member);
  thm base_equal = match_mp_rule(spec_rule(
      `cm_region_gen (region:cm_region)`, bases), gen_bound);
  thm base_equal_normal =
      conv_rule(reduce_rewrite_conv(pending_rules), base_equal);
  thm old_lower_bridge = beta_norm(ap_term_rule(
      `\base:int.
         base + cm_region_lo (region:cm_region) <= (addr:int)`,
      base_equal_normal));
  thm old_upper_bridge = beta_norm(ap_term_rule(
      `\base:int.
         (addr:int) < base + cm_region_hi (region:cm_region)`,
      base_equal_normal));
  thm old_lower = eq_mp_rule(old_lower_bridge,
      conjunct1_rule(conjunct2_rule(conjunct2_rule(live_body))));
  thm old_upper = eq_mp_rule(old_upper_bridge,
      conjunct2_rule(conjunct2_rule(conjunct2_rule(live_body))));
  thm old_body = conj_rule(old_member, conj_rule(
      conjunct1_rule(conjunct2_rule(live_body)),
      conj_rule(old_lower, old_upper)));
  term old_exists_term =
      `?candidate.
         MEM candidate (cm_state_regions (st:cm_src_state)) &&
         cm_region_live candidate &&
         cm_region_base (cm_state_regions st)
             (cm_region_gen candidate) + cm_region_lo candidate <=
           (addr:int) &&
         addr <
           cm_region_base (cm_state_regions st)
             (cm_region_gen candidate) + cm_region_hi candidate`;
  thm old_exists = exists_rule(old_exists_term,
      `region:cm_region`, old_body);
  thm old_live = eq_mp_rule(sym_rule(apply_conversion(
      rewrite_conv(THM_LIST(cm_live_address_def)),
      `cm_live_address (st:cm_src_state) (addr:int)`)), old_exists);
  thm old_result = disj1_rule(old_live, conclusion_right);
  thm region_result = disj_cases_rule(member_split,
      fresh_case, old_result);
  thm selected = choose_rule(`region:cm_region`,
      live_exists, region_result);
  thm selected_normal = conv_rule(rewrite_conv(THM_LIST(
      gsym_rule(get_theorem_by_name("INT_ADD_ASSOC")))), selected);
  ACCEPT_TAC(leaf, selected_normal);
  return gnode_prove(root);
}
PROOF thm cm_call_pending_live_old_or_param =
    cm_prove_call_pending_live_old_or_param();

PROOF thm get_cm_call_pending_live_old_or_param(void) {
  return cm_call_pending_live_old_or_param;
}

PROOF static int cmc_preservation_call_pending_live_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_call_pending_live_axioms_before,
      "cmc_preservation_call_pending_live introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_call_pending_live_checks =
    cmc_preservation_call_pending_live_final_checks();
