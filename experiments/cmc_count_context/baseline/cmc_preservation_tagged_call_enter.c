#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_tagged_call_enter.h"
#include "cmc_preservation_call_params_complete.h"

#require "cmc_preservation_tagged_call_ready.c"
#require "cmc_preservation_call_params_complete.c"

PROOF static size_t _cmc_preservation_tagged_call_enter_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_prove_tagged_span_enter_call(void) {
  gnode root_node = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (values:(cm_value)list)
         (st:cm_src_state) (calls:(cm_call_sim_frame)list)
         (frames:(cm_spill_frame)list).
         cm_function_wf p
           (inth fid (cm_program_functions p)) ==>
         cm_frame_segment p fid
           (cm_state_fp st -
             cm_frame_size (cm_program_structs p)
               (inth fid (cm_program_functions p)))
           (cm_state_fp st) ==>
         cm_regions_before (cm_state_regions st)
           (cm_state_nextgen st) ==>
         0i <= cm_state_nextgen st ==>
         ~(values == []) ==>
         ilength values ==
           ilength (cm_function_params
             (inth fid (cm_program_functions p))) ==>
         cm_runtime_memory_layout p
           (cm_call_pending_base p fid st) calls frames ==>
         cm_tagged_span_valid st ==>
         cm_tagged_span_valid (cm_enter_call p fid values st)`);
  gnode leaf = AUTO_INTROS_TAC(root_node);
  term params =
      `cm_function_params
        (inth (fid:int) (cm_program_functions (p:cm_program)))`;
  term newfp =
      `cm_state_fp (st:cm_src_state) -
       cm_frame_size (cm_program_structs (p:cm_program))
         (inth (fid:int) (cm_program_functions p))`;
  term pending =
      `cm_call_pending_base (p:cm_program) (fid:int)
        (st:cm_src_state)`;
  term stored =
      `cm_store_params_reverse (p:cm_program) (fid:int)
        (values:(cm_value)list) 0i ${pending:cm_src_state}`;
  thm function_wf = assume_rule(
      `cm_function_wf (p:cm_program)
        (inth (fid:int) (cm_program_functions p))`);
  thm segment = assume_rule(
      `cm_frame_segment (p:cm_program) (fid:int)
        ${newfp:int} (cm_state_fp (st:cm_src_state))`);
  thm before = assume_rule(
      `cm_regions_before (cm_state_regions (st:cm_src_state))
        (cm_state_nextgen st)`);
  thm nonempty = assume_rule(
      `~((values:(cm_value)list) == [])`);
  thm arity = assume_rule(
      `ilength (values:(cm_value)list) ==
       ilength ${params:(cm_slot_d)list}`);

  thm pending_structure = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`),
      cm_call_pending_structure);
  thm pending_fp = conjunct1_rule(pending_structure);
  thm pending_regions = conjunct1_rule(
      conjunct2_rule(conjunct2_rule(pending_structure)));
  term pending_env_function_term =
      `cm_state_env ${pending:cm_src_state} ==
       cm_call_env (p:cm_program) (fid:int)
         (cm_state_env (st:cm_src_state)) ${newfp:int}
         (cm_state_nextgen st)`;
  thm_list env_rules = get_cm_state_core_defs();
  vector_add(&env_rules, get_cm_call_pending_base_def());
  thm pending_env_function = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(env_rules), pending_env_function_term));
  thm pending_env_at = beta_norm(ap_term_rule(
      `\env:int->int->cm_value. env 2i (j:int)`,
      pending_env_function));
  pending_env_at = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_call_env_def())), pending_env_at);
  thm pending_env = gen_rule(`j:int`, disch_rule(
      `0i <= (j:int)`, disch_rule(
        `(j:int) < ilength ${params:(cm_slot_d)list}`,
        pending_env_at)));
  thm total_bound = mp_rule(int_arith_rule(
      `ilength (values:(cm_value)list) ==
         ilength ${params:(cm_slot_d)list} ==>
       0i + ilength values <= ilength ${params:(cm_slot_d)list}`),
      arity);

  thm stores_ready = specl_rule(TERM_LIST(
      `values:(cm_value)list`, `p:cm_program`, `fid:int`, pending,
      `cm_state_regions (st:cm_src_state)`,
      `cm_state_nextgen (st:cm_src_state)`, newfp,
      `cm_state_fp (st:cm_src_state)`, `0i:int`),
      cm_param_stores_ready);
  stores_ready = match_mp_rule(stores_ready, function_wf);
  stores_ready = match_mp_rule(stores_ready, segment);
  stores_ready = match_mp_rule(stores_ready, before);
  stores_ready = match_mp_rule(stores_ready, assume_rule(
      `0i <= cm_state_nextgen (st:cm_src_state)`));
  stores_ready = match_mp_rule(stores_ready, pending_fp);
  stores_ready = match_mp_rule(stores_ready, pending_regions);
  stores_ready = match_mp_rule(stores_ready, pending_env);
  stores_ready = match_mp_rule(stores_ready,
      int_arith_rule(`0i <= 0i`));
  stores_ready = match_mp_rule(stores_ready, total_bound);

  thm pending_tagged = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`),
      cm_tagged_span_call_pending);
  pending_tagged = match_mp_rule(pending_tagged, function_wf);
  pending_tagged = match_mp_rule(pending_tagged, before);
  pending_tagged = match_mp_rule(pending_tagged, assume_rule(
      `cm_tagged_span_valid (st:cm_src_state)`));
  thm stored_tagged = specl_rule(TERM_LIST(
      `values:(cm_value)list`, `p:cm_program`, `fid:int`, `0i:int`,
      pending, `calls:(cm_call_sim_frame)list`,
      `frames:(cm_spill_frame)list`),
      cm_tagged_span_store_params_reverse);
  stored_tagged = match_mp_rule(stored_tagged, assume_rule(
      `cm_runtime_memory_layout (p:cm_program)
        ${pending:cm_src_state} (calls:(cm_call_sim_frame)list)
        (frames:(cm_spill_frame)list)`));
  stored_tagged = match_mp_rule(stored_tagged, stores_ready);
  stored_tagged = match_mp_rule(stored_tagged, pending_tagged);

  thm entered_equal = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `values:(cm_value)list`,
      `st:cm_src_state`), cm_pending_params_enter_call);
  entered_equal = match_mp_rule(entered_equal, function_wf);
  entered_equal = match_mp_rule(entered_equal, segment);
  entered_equal = match_mp_rule(entered_equal, before);
  entered_equal = match_mp_rule(entered_equal, arity);
  thm lifted = beta_norm(ap_term_rule(
      `\state:cm_src_state. cm_tagged_span_valid state`,
      entered_equal));
  ACCEPT_TAC(leaf, eq_mp_rule(lifted, stored_tagged));
  return gnode_prove(root_node);
}
PROOF thm cm_tagged_span_enter_call =
    cm_prove_tagged_span_enter_call();

PROOF static thm cm_prove_tagged_span_enter_call_empty(void) {
  gnode root_node = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (st:cm_src_state).
         cm_function_params
           (inth fid (cm_program_functions p)) == [] ==>
         cm_tagged_span_valid st ==>
         cm_tagged_span_valid (cm_enter_call p fid [] st)`);
  gnode leaf = AUTO_INTROS_TAC(root_node);
  thm old_valid = assume_rule(
      `cm_tagged_span_valid (st:cm_src_state)`);
  thm params_nil = assume_rule(
      `cm_function_params
        (inth (fid:int) (cm_program_functions (p:cm_program))) ==
       ([]:(cm_slot_d)list)`);
  thm_list rules = get_cm_state_core_defs();
  vector_add(&rules, get_cm_enter_call_def());
  vector_add(&rules, get_cm_store_params_def());
  vector_add(&rules, get_cm_call_base_state_def());
  vector_add(&rules, get_cm_regions_for_slots_def());
  vector_add(&rules, cm_tagged_span_valid_def);
  vector_add(&rules, cm_live_span_def);
  vector_add(&rules, cm_live_address_def);
  vector_add(&rules, params_nil);
  vector_add(&rules, get_theorem_by_name("APPEND"));
  thm normalized = conv_rule(reduce_rewrite_conv(rules), old_valid);
  thm target_view = apply_conversion(
      reduce_rewrite_conv(rules), goal_ccl(leaf->g));
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), normalized));
  return gnode_prove(root_node);
}
PROOF thm cm_tagged_span_enter_call_empty =
    cm_prove_tagged_span_enter_call_empty();

PROOF static int cmc_preservation_tagged_call_enter_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_tagged_call_enter_axioms_before,
      "cmc_preservation_tagged_call_enter introduced an axiom");
  ENSURE_COND(vector_size(hyp(cm_tagged_span_enter_call)) == 0,
      "enter-call tagged-span theorem is not closed");
  ENSURE_COND(vector_size(hyp(cm_tagged_span_enter_call_empty)) == 0,
      "empty enter-call tagged-span theorem is not closed");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_tagged_call_enter_checks =
    cmc_preservation_tagged_call_enter_final_checks();
