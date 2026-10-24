#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_call_pending_memory.h"

#require "cmc_preservation_call_pending_live.c"
#require "cmc_preservation_machine_store.c"

PROOF static size_t _cmc_preservation_call_pending_memory_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_prove_call_pending_initialized_transport(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (st:cm_src_state) (mem:int->int).
         cm_function_wf p
           (inth fid (cm_program_functions p)) ==>
         cm_regions_before (cm_state_regions st)
           (cm_state_nextgen st) ==>
         cm_initialized_bytes_sim st mem ==>
         tower_signed64 (cm_state_fp st) ==>
         (!addr.
            cm_live_address st addr ==>
            ~((cm_state_fp st -
               cm_frame_size (cm_program_structs p)
                 (inth fid (cm_program_functions p))) <= addr &&
              addr <
                (cm_state_fp st -
                 cm_frame_size (cm_program_structs p)
                   (inth fid (cm_program_functions p))) + 8i)) ==>
         cm_initialized_bytes_sim
           (cm_call_pending_base p fid st) mem`);
  gnode leaf = AUTO_INTROS_TAC(root);
  term base =
      `cm_state_fp (st:cm_src_state) -
       cm_frame_size (cm_program_structs (p:cm_program))
         (inth (fid:int) (cm_program_functions p))`;
  term param_base = `${base:int} + 8i`;
  term span = `cm_call_param_span (p:cm_program) (fid:int)`;
  thm_list pending_rules = get_cm_state_core_defs();
  vector_add(&pending_rules, cm_call_pending_base_def);
  vector_add(&pending_rules, get_cm_clear_init_def());

  thm old_sim = conv_rule(rewrite_conv(THM_LIST(
      cm_initialized_bytes_sim_def)), assume_rule(
        `cm_initialized_bytes_sim
          (st:cm_src_state) (mem:int->int)`));
  gnode opened = CONV_TAC(leaf, rewrite_conv(THM_LIST(
      cm_initialized_bytes_sim_def)));
  gnode at_address = AUTO_INTROS_TAC(opened);
  thm pending_raw = assume_rule(
      `cm_state_init
         (cm_call_pending_base (p:cm_program) (fid:int)
           (st:cm_src_state)) (addr:int) &&
       cm_live_address (cm_call_pending_base p fid st) addr`);
  thm pending_init = conv_rule(reduce_rewrite_conv(pending_rules),
      conjunct1_rule(pending_raw));
  thm old_init = conjunct1_rule(pending_init);
  thm outside_param = conjunct2_rule(pending_init);
  thm pending_live = conjunct2_rule(pending_raw);
  thm split = match_mp_rule(match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(`p:cm_program`, `fid:int`,
        `st:cm_src_state`, `addr:int`),
        get_cm_call_pending_live_old_or_param()),
      assume_rule(
        `cm_function_wf (p:cm_program)
          (inth (fid:int) (cm_program_functions p))`)),
      assume_rule(
        `cm_regions_before (cm_state_regions (st:cm_src_state))
          (cm_state_nextgen st)`)), pending_live);
  dest_disj_results split_parts = dest_disj(concl(split));
  term old_live_term = split_parts.tm1;
  thm old_live_case = assume_rule(old_live_term);
  thm param_case = assume_rule(split_parts.tm2);
  thm contradictory = conj_rule(outside_param, param_case);
  thm impossible = mp_rule(int_arith_rule(
      mk_imp(concl(contradictory), `F`)), contradictory);
  thm old_live = disj_cases_rule(split, old_live_case,
      false_elim_rule(impossible, old_live_term));
  thm old_byte = match_mp_rule(spec_rule(`addr:int`, old_sim),
      conj_rule(old_init, old_live));
  thm outside_frame = match_mp_rule(spec_rule(`addr:int`, assume_rule(
      `!addr.
         cm_live_address (st:cm_src_state) addr ==>
         ~(${base:int} <= addr && addr < ${base:int} + 8i)`)),
      old_live);
  thm source_rule = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_store_width_def(), get_cm_type_int_char_distinct())),
      specl_rule(TERM_LIST(
        `CMIntTy:cm_type`, base, `cm_state_fp (st:cm_src_state)`,
        `cm_state_mem (st:cm_src_state)`, `addr:int`),
        cm_store_mem_byte_other));
  thm source_same = match_mp_rule(source_rule, outside_frame);
  thm fp_fixed = mp_rule(spec_rule(`cm_state_fp (st:cm_src_state)`,
      get_tower_wrap64_fixed()), assume_rule(
        `tower_signed64 (cm_state_fp (st:cm_src_state))`));
  source_same = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_store_mem_def(), get_cm_type_int_char_distinct(), fp_fixed)),
      source_same);
  thm result = trans_rule(old_byte, sym_rule(source_same));
  gnode reduced = CONV_TAC(at_address,
      reduce_rewrite_conv(pending_rules));
  ACCEPT_TAC(reduced,
      conv_rule(reduce_rewrite_conv(pending_rules), result));
  return gnode_prove(root);
}
PROOF thm cm_call_pending_initialized_transport =
    cm_prove_call_pending_initialized_transport();

PROOF static thm cm_prove_call_pending_provenance_transport(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (st:cm_src_state) (mem:int->int).
         cm_function_wf p
           (inth fid (cm_program_functions p)) ==>
         cm_regions_before (cm_state_regions st)
           (cm_state_nextgen st) ==>
         cm_state_tags_generation_below st
           (cm_state_nextgen st) ==>
         cm_stored_provenance_sim st mem ==>
         cm_stored_provenance_sim
           (cm_call_pending_base p fid st) mem`);
  gnode leaf = AUTO_INTROS_TAC(root);
  term base =
      `cm_state_fp (st:cm_src_state) -
       cm_frame_size (cm_program_structs (p:cm_program))
         (inth (fid:int) (cm_program_functions p))`;
  term param_base = `${base:int} + 8i`;
  term span = `cm_call_param_span (p:cm_program) (fid:int)`;
  term pending =
      `cm_call_pending_base (p:cm_program) (fid:int)
        (st:cm_src_state)`;
  thm_list pending_rules = get_cm_state_core_defs();
  vector_add(&pending_rules, cm_call_pending_base_def);
  vector_add(&pending_rules, get_cm_clear_init_def());
  vector_add(&pending_rules, get_cm_clear_tagged_def());

  thm old_sim = conv_rule(rewrite_conv(THM_LIST(
      cm_stored_provenance_sim_def)), assume_rule(
        `cm_stored_provenance_sim
          (st:cm_src_state) (mem:int->int)`));
  gnode opened = CONV_TAC(leaf, rewrite_conv(THM_LIST(
      cm_stored_provenance_sim_def)));
  gnode at_address = AUTO_INTROS_TAC(opened);
  thm pending_raw = assume_rule(
      `cm_state_tagged ${pending:cm_src_state} (addr:int) &&
       cm_live_address ${pending:cm_src_state} addr`);
  thm pending_tagged = conv_rule(
      reduce_rewrite_conv(pending_rules), conjunct1_rule(pending_raw));
  thm old_tagged = conjunct1_rule(pending_tagged);
  thm no_param_overlap = conjunct2_rule(pending_tagged);
  thm pending_live = conjunct2_rule(pending_raw);
  thm split = match_mp_rule(match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(`p:cm_program`, `fid:int`,
        `st:cm_src_state`, `addr:int`),
        get_cm_call_pending_live_old_or_param()),
      assume_rule(
        `cm_function_wf (p:cm_program)
          (inth (fid:int) (cm_program_functions p))`)),
      assume_rule(
        `cm_regions_before (cm_state_regions (st:cm_src_state))
          (cm_state_nextgen st)`)), pending_live);
  dest_disj_results split_parts = dest_disj(concl(split));
  term old_live_term = split_parts.tm1;
  thm old_live_case = assume_rule(old_live_term);
  thm param_case = assume_rule(split_parts.tm2);
  thm contradictory = conj_rule(no_param_overlap, param_case);
  thm impossible = mp_rule(int_arith_rule(
      mk_imp(concl(contradictory), `F`)), contradictory);
  thm old_live = disj_cases_rule(split, old_live_case,
      false_elim_rule(impossible, old_live_term));
  thm old_point = match_mp_rule(spec_rule(`addr:int`, old_sim),
      conj_rule(old_tagged, old_live));
  thm outside_param = mp_rule(int_arith_rule(mk_imp(
      concl(no_param_overlap), mk_not(split_parts.tm2))),
      no_param_overlap);
  thm pending_init_raw = conj_rule(
      conjunct1_rule(old_point), outside_param);
  pending_init_raw = conv_rule(rewrite_conv(THM_LIST(
      get_theorem_by_name("INT_ADD_ASSOC"))), pending_init_raw);
  thm pending_init = eq_mp_rule(sym_rule(apply_conversion(
      reduce_rewrite_conv(pending_rules),
      `cm_state_init ${pending:cm_src_state} (addr:int)`)),
      pending_init_raw);
  thm below_open = conv_rule(rewrite_conv(THM_LIST(
      cm_state_tags_generation_below_def)), assume_rule(
        `cm_state_tags_generation_below (st:cm_src_state)
          (cm_state_nextgen st)`));
  thm tag_below = match_mp_rule(spec_rule(`addr:int`, below_open),
      old_tagged);
  thm number = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
      `cm_state_tags (st:cm_src_state) (addr:int)`,
      `st:cm_src_state`, pending,
      `cm_state_nextgen (st:cm_src_state)`),
      cm_value_number_bases),
      specl_rule(TERM_LIST(`p:cm_program`, `fid:int`, `st:cm_src_state`),
        cm_call_pending_regions_bases)), tag_below);
  thm target_word = trans_rule(conjunct2_rule(old_point),
      sym_rule(number));
  thm result = conj_rule(pending_init, target_word);
  gnode reduced = CONV_TAC(at_address,
      reduce_rewrite_conv(pending_rules));
  ACCEPT_TAC(reduced,
      conv_rule(reduce_rewrite_conv(pending_rules), result));
  return gnode_prove(root);
}
PROOF thm cm_call_pending_provenance_transport =
    cm_prove_call_pending_provenance_transport();

PROOF thm get_cm_call_pending_initialized_transport(void) {
  return cm_call_pending_initialized_transport;
}
PROOF thm get_cm_call_pending_provenance_transport(void) {
  return cm_call_pending_provenance_transport;
}

PROOF static int cmc_preservation_call_pending_memory_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_call_pending_memory_axioms_before,
      "cmc_preservation_call_pending_memory introduced an axiom");
  ENSURE_COND(vector_size(hyp(cm_call_pending_initialized_transport)) == 0,
      "cm_call_pending_initialized_transport has hypotheses");
  ENSURE_COND(vector_size(hyp(cm_call_pending_provenance_transport)) == 0,
      "cm_call_pending_provenance_transport has hypotheses");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_call_pending_memory_checks =
    cmc_preservation_call_pending_memory_final_checks();
