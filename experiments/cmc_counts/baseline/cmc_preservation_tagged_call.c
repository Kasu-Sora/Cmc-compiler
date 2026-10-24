#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_tagged_call.h"

#require "cmc_preservation_tagged_allocation.c"
#require "cmc_preservation_call_pending_live.c"
#require "cmc_preservation_target_call_params.c"

PROOF static size_t _cmc_preservation_tagged_call_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_prove_call_pending_live_old(void) {
  gnode root_node = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (st:cm_src_state) (addr:int).
         cm_regions_before (cm_state_regions st)
           (cm_state_nextgen st) ==>
         cm_live_address st addr ==>
         cm_live_address (cm_call_pending_base p fid st) addr`);
  gnode leaf = AUTO_INTROS_TAC(root_node);
  term old_regions = `cm_state_regions (st:cm_src_state)`;
  term nextgen = `cm_state_nextgen (st:cm_src_state)`;
  term pending =
      `cm_call_pending_base (p:cm_program) (fid:int)
        (st:cm_src_state)`;
  term pending_regions = `cm_state_regions ${pending:cm_src_state}`;
  thm before = assume_rule(
      `cm_regions_before ${old_regions:(cm_region)list} ${nextgen:int}`);
  thm before_open = conv_rule(rewrite_conv(THM_LIST(
      cm_regions_before_def)), before);
  thm bases = conv_rule(rewrite_conv(THM_LIST(
      cm_region_bases_below_equal_def)),
      specl_rule(TERM_LIST(`p:cm_program`, `fid:int`, `st:cm_src_state`),
        cm_call_pending_regions_bases));
  thm old_exists = conv_rule(rewrite_conv(THM_LIST(
      cm_live_address_def)), assume_rule(
        `cm_live_address (st:cm_src_state) (addr:int)`));
  thm old_body = assume_rule(
      `MEM (region:cm_region) ${old_regions:(cm_region)list} &&
       cm_region_live region &&
       cm_region_base ${old_regions:(cm_region)list}
           (cm_region_gen region) + cm_region_lo region <= (addr:int) &&
       addr < cm_region_base ${old_regions:(cm_region)list}
           (cm_region_gen region) + cm_region_hi region`);
  thm member = conjunct1_rule(old_body);
  thm generation_bound = match_mp_rule(spec_rule(
      `region:cm_region`, before_open), member);
  thm base_equal = match_mp_rule(spec_rule(
      `cm_region_gen (region:cm_region)`, bases), generation_bound);
  thm new_bounds = conv_rule(rewrite_conv(THM_LIST(
      sym_rule(base_equal))), conjunct2_rule(conjunct2_rule(old_body)));
  thm_list pending_rules = get_cm_state_core_defs();
  vector_add(&pending_rules, get_cm_call_pending_base_def());
  thm pending_regions_shape = apply_conversion(
      reduce_rewrite_conv(pending_rules), pending_regions);
  struct dest_eq_results region_shape =
      dest_eq(concl(pending_regions_shape));
  term concrete_regions = region_shape.tm2;
  thm old_member_concrete = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("MEM_APPEND"), member)),
      `MEM (region:cm_region) ${concrete_regions:(cm_region)list}`));
  thm old_member_pending = conv_rule(rewrite_conv(THM_LIST(
      sym_rule(pending_regions_shape))), old_member_concrete);
  thm new_body = conj_rule(old_member_pending, conj_rule(
      conjunct1_rule(conjunct2_rule(old_body)), new_bounds));
  thm pending_exists = exists_rule(
      `?candidate.
         MEM candidate ${pending_regions:(cm_region)list} &&
         cm_region_live candidate &&
         cm_region_base ${pending_regions:(cm_region)list}
             (cm_region_gen candidate) + cm_region_lo candidate <=
           (addr:int) &&
         addr < cm_region_base ${pending_regions:(cm_region)list}
             (cm_region_gen candidate) + cm_region_hi candidate`,
      `region:cm_region`, new_body);
  thm selected = choose_rule(`region:cm_region`, old_exists,
      pending_exists);
  thm target_view = apply_conversion(rewrite_conv(THM_LIST(
      cm_live_address_def)),
      `cm_live_address ${pending:cm_src_state} (addr:int)`);
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), selected));
  return gnode_prove(root_node);
}
PROOF thm cm_call_pending_live_old =
    cm_prove_call_pending_live_old();

PROOF static thm cm_prove_tagged_span_call_pending(void) {
  gnode root_node = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (st:cm_src_state).
         cm_function_wf p
           (inth fid (cm_program_functions p)) ==>
         cm_regions_before (cm_state_regions st)
           (cm_state_nextgen st) ==>
         cm_tagged_span_valid st ==>
         cm_tagged_span_valid (cm_call_pending_base p fid st)`);
  gnode leaf = AUTO_INTROS_TAC(root_node);
  term pending =
      `cm_call_pending_base (p:cm_program) (fid:int)
        (st:cm_src_state)`;
  term param_base =
      `(cm_state_fp (st:cm_src_state) -
        cm_frame_size (cm_program_structs (p:cm_program))
          (inth (fid:int) (cm_program_functions p))) + 8i`;
  term param_width = `cm_call_param_span (p:cm_program) (fid:int)`;
  thm before = assume_rule(
      `cm_regions_before (cm_state_regions (st:cm_src_state))
        (cm_state_nextgen st)`);
  thm_list tagged_rules = get_cm_state_core_defs();
  vector_add(&tagged_rules, get_cm_call_pending_base_def());
  thm tagged_equal = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(tagged_rules),
      `!addr:int.
         cm_state_tagged ${pending:cm_src_state} addr <=>
         cm_clear_tagged (cm_state_tagged st)
           ${param_base:int} ${param_width:int} addr`));
  term pending_live =
      `cm_live_address ${pending:cm_src_state} (addr:int)`;
  thm raw_classified = match_mp_rule(match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `st:cm_src_state`, `addr:int`),
        cm_call_pending_live_old_or_param), assume_rule(
          `cm_function_wf (p:cm_program)
            (inth (fid:int) (cm_program_functions p))`)), before),
      assume_rule(pending_live));
  struct dest_disj_results live_alternatives =
      dest_disj(concl(raw_classified));
  thm old_case = assume_rule(live_alternatives.tm1);
  thm param_case = assume_rule(live_alternatives.tm2);
  term desired_interval =
      `${param_base:int} <= (addr:int) &&
       addr < ${param_base:int} + ${param_width:int}`;
  thm normalized_param = mp_rule(int_arith_rule(mk_imp(
      live_alternatives.tm2, desired_interval)), param_case);
  thm desired_cases = disj_cases_rule(raw_classified,
      disj1_rule(old_case, desired_interval),
      disj2_rule(`cm_live_address (st:cm_src_state) (addr:int)`,
        normalized_param));
  thm classify = gen_rule(`addr:int`,
      disch_rule(pending_live, desired_cases));
  thm forward = gen_rule(`addr:int`, disch_rule(
      `cm_live_address (st:cm_src_state) (addr:int)`,
      match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `st:cm_src_state`, `addr:int`),
        cm_call_pending_live_old), before),
        assume_rule(
          `cm_live_address (st:cm_src_state) (addr:int)`))));
  thm result = specl_rule(TERM_LIST(
      `st:cm_src_state`, pending, param_base, param_width),
      cm_tagged_span_clear_extension);
  result = match_mp_rule(result, tagged_equal);
  result = match_mp_rule(result, classify);
  result = match_mp_rule(result, forward);
  result = match_mp_rule(result, assume_rule(
      `cm_tagged_span_valid (st:cm_src_state)`));
  ACCEPT_TAC(leaf, result);
  return gnode_prove(root_node);
}
PROOF thm cm_tagged_span_call_pending =
    cm_prove_tagged_span_call_pending();

PROOF thm cm_param_stores_ok_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(!p fid index st.
        cm_param_stores_ok (p:cm_program) (fid:int)
          ([]:(cm_value)list) (index:int) (st:cm_src_state) <=> T) &&
     (!p fid v rest index st.
        cm_param_stores_ok p fid
          ((v:cm_value) :: (rest:(cm_value)list)) index st <=>
        (cm_param_stores_ok p fid rest (index + 1i) st &&
         cm_store_ok
           (cm_slot_ty (inth index
             (cm_function_params
               (inth fid (cm_program_functions p)))))
           (cm_state_env
             (cm_store_params_reverse p fid rest (index + 1i) st)
             2i index)
           (cm_store_params_reverse p fid rest (index + 1i) st)))`);
PROOF static int _e_cm_param_stores_ok =
    cst_add_const_to_header(`cm_param_stores_ok`);

PROOF static thm cm_prove_tagged_span_store_params_reverse(void) {
  gnode root_node = gnode_new_with_ccl(
      `!(values:(cm_value)list).
         !(p:cm_program) (fid:int) (index:int) (st:cm_src_state)
           (calls:(cm_call_sim_frame)list)
           (frames:(cm_spill_frame)list).
         cm_runtime_memory_layout p st calls frames ==>
         cm_param_stores_ok p fid values index st ==>
         cm_tagged_span_valid st ==>
         cm_tagged_span_valid
           (cm_store_params_reverse p fid values index st)`);
  gnode_list cases = INDUCT_TAC(root_node, `values:(cm_value)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm old_valid = assume_rule(
        `cm_tagged_span_valid (st:cm_src_state)`);
    thm target_view = apply_conversion(rewrite_conv(THM_LIST(
        cm_store_params_reverse_def)), goal_ccl(leaf->g));
    ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), old_valid));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    term tail_state =
        `cm_store_params_reverse (p:cm_program) (fid:int)
          (a1:(cm_value)list) ((index:int) + 1i)
          (st:cm_src_state)`;
    term ty =
        `cm_slot_ty (inth (index:int)
          (cm_function_params
            (inth (fid:int) (cm_program_functions (p:cm_program)))))`;
    term pointer =
        `cm_state_env ${tail_state:cm_src_state} 2i (index:int)`;
    thm ok_parts = conv_rule(rewrite_conv(THM_LIST(
        cm_param_stores_ok_def)), assume_rule(
          `cm_param_stores_ok (p:cm_program) (fid:int)
            ((a0:cm_value) :: (a1:(cm_value)list))
            (index:int) (st:cm_src_state)`));
    thm initial_layout = assume_rule(
        `cm_runtime_memory_layout (p:cm_program) (st:cm_src_state)
          (calls:(cm_call_sim_frame)list)
          (frames:(cm_spill_frame)list)`);
    thm tail_layout = mp_rule(specl_rule(TERM_LIST(
        `a1:(cm_value)list`, `p:cm_program`, `fid:int`,
        `(index:int) + 1i`, `st:cm_src_state`,
        `calls:(cm_call_sim_frame)list`,
        `frames:(cm_spill_frame)list`),
        cm_store_params_reverse_runtime), initial_layout);
    thm ih = specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `(index:int) + 1i`,
        `st:cm_src_state`, `calls:(cm_call_sim_frame)list`,
        `frames:(cm_spill_frame)list`),
        assume_rule(goal_lasmps(leaf->g)[0].tm));
    ih = match_mp_rule(ih, initial_layout);
    ih = match_mp_rule(ih, conjunct1_rule(ok_parts));
    ih = match_mp_rule(ih, assume_rule(
        `cm_tagged_span_valid (st:cm_src_state)`));
    thm stored = specl_rule(TERM_LIST(
        `p:cm_program`, tail_state, `calls:(cm_call_sim_frame)list`,
        `frames:(cm_spill_frame)list`, ty, pointer,
        `a0:cm_value`), cm_tagged_span_store);
    stored = match_mp_rule(stored, tail_layout);
    stored = match_mp_rule(stored, conjunct2_rule(ok_parts));
    stored = match_mp_rule(stored, ih);
    thm target_view = apply_conversion(rewrite_conv(THM_LIST(
        cm_store_params_reverse_def)), goal_ccl(leaf->g));
    ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), stored));
  }
  return gnode_prove(root_node);
}
PROOF thm cm_tagged_span_store_params_reverse =
    cm_prove_tagged_span_store_params_reverse();

PROOF static int cmc_preservation_tagged_call_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_tagged_call_axioms_before,
      "cmc_preservation_tagged_call introduced an axiom");
  ENSURE_COND(vector_size(hyp(cm_call_pending_live_old)) == 0,
      "pending old-live theorem is not closed");
  ENSURE_COND(vector_size(hyp(cm_tagged_span_call_pending)) == 0,
      "pending tagged-span theorem is not closed");
  ENSURE_COND(vector_size(hyp(cm_tagged_span_store_params_reverse)) == 0,
      "reverse parameter tagged-span theorem is not closed");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_tagged_call_checks =
    cmc_preservation_tagged_call_final_checks();
