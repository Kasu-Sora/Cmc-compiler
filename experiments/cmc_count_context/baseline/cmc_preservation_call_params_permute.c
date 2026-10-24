#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_call_params_permute.h"

#require "cmc_preservation_call_params_order.c"

PROOF static size_t _cmc_preservation_call_params_permute_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_param_permute_consequence(
    const thm premise, const term conclusion) {
  return mp_rule(taut_rule(mk_imp(concl(premise), conclusion)), premise);
}

PROOF static thm cm_param_permute_assumption(
    const gnode node, const term wanted) {
  labeled_term_list assumptions = goal_lasmps(node->g);
  for (size_t index = 0; index < vector_size(assumptions); ++index) {
    if (alpha_compare(assumptions[index].tm, wanted) == 0) {
      return assume_rule(assumptions[index].tm);
    }
  }
  return empty_theorem;
}

PROOF static thm cm_prove_state_store_env(void) {
  gnode root = gnode_new_with_ccl(
      `!(ty:cm_type) (ptr:cm_value) (stored_value:cm_value)
         (st:cm_src_state).
         cm_state_env (cm_state_store ty ptr stored_value st) ==
         cm_state_env st`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm_list rules = get_cm_state_core_defs();
  vector_add(&rules, get_cm_state_store_def());
  CONV_TAC(leaf, reduce_rewrite_conv(rules));
  return gnode_prove(root);
}
PROOF static thm cm_state_store_env =
    cm_prove_state_store_env();


PROOF static thm cm_prove_parameter_state_store_commute(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (st:cm_src_state)
         (old:(cm_region)list) (oldenv:int->int->cm_value)
         (gen:int) (fp:int) (oldfp:int)
         (left:int) (right:int) (left_value:cm_value)
         (right_value:cm_value).
         cm_function_wf p (inth fid (cm_program_functions p)) ==>
         cm_frame_segment p fid fp oldfp ==>
         cm_param_store_context p fid st old oldenv gen fp ==>
         0i <= left ==> left < right ==>
         right < ilength
           (cm_function_params
             (inth fid (cm_program_functions p))) ==>
         cm_parameter_state_store p fid left left_value
           (cm_parameter_state_store p fid right right_value st) ==
         cm_parameter_state_store p fid right right_value
           (cm_parameter_state_store p fid left left_value st)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  term params =
      `cm_function_params
        (inth (fid:int) (cm_program_functions (p:cm_program)))`;
  thm function_wf = assume_rule(
      `cm_function_wf (p:cm_program)
        (inth (fid:int) (cm_program_functions p))`);
  thm segment = assume_rule(
      `cm_frame_segment (p:cm_program) (fid:int)
        (fp:int) (oldfp:int)`);
  thm context = assume_rule(
      `cm_param_store_context (p:cm_program) (fid:int)
        (st:cm_src_state) (old:(cm_region)list)
        (oldenv:int->int->cm_value) (gen:int) (fp:int)`);
  thm left_lower = assume_rule(`0i <= (left:int)`);
  thm left_right = assume_rule(`(left:int) < (right:int)`);
  thm right_upper = assume_rule(
      `(right:int) < ilength ${params:(cm_slot_d)list}`);
  thm right_lower = mp_rule(mp_rule(int_arith_rule(
      `0i <= (left:int) ==> left < (right:int) ==> 0i <= right`),
      left_lower), left_right);
  thm left_upper = mp_rule(mp_rule(int_arith_rule(
      `(left:int) < (right:int) ==> right < ilength
        ${params:(cm_slot_d)list} ==>
        left < ilength ${params:(cm_slot_d)list}`),
      left_right), right_upper);
  thm left_numeric = match_mp_rule(match_mp_rule(match_mp_rule(
      match_mp_rule(specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `fp:int`, `oldfp:int`,
        `left:int`), cm_parameter_address_ready), function_wf),
      segment), left_lower), left_upper);
  thm right_numeric = match_mp_rule(match_mp_rule(match_mp_rule(
      match_mp_rule(specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `fp:int`, `oldfp:int`,
        `right:int`), cm_parameter_address_ready), function_wf),
      segment), right_lower), right_upper);
  thm left_signed = cm_param_permute_consequence(left_numeric,
      `tower_signed64
        ((fp:int) + cm_param_offset
          (p:cm_program) (fid:int) (left:int))`);
  thm right_signed = cm_param_permute_consequence(right_numeric,
      `tower_signed64
        ((fp:int) + cm_param_offset
          (p:cm_program) (fid:int) (right:int))`);
  thm left_number = match_mp_rule(match_mp_rule(match_mp_rule(
      match_mp_rule(specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `st:cm_src_state`,
        `old:(cm_region)list`, `oldenv:int->int->cm_value`,
        `gen:int`, `fp:int`, `left:int`),
        cm_parameter_pointer_number), context), left_lower),
      left_upper), left_signed);
  thm right_number = match_mp_rule(match_mp_rule(match_mp_rule(
      match_mp_rule(specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `st:cm_src_state`,
        `old:(cm_region)list`, `oldenv:int->int->cm_value`,
        `gen:int`, `fp:int`, `right:int`),
        cm_parameter_pointer_number), context), right_lower),
      right_upper), right_signed);
  thm disjoint = match_mp_rule(match_mp_rule(match_mp_rule(
      match_mp_rule(specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `left:int`, `right:int`,
        `fp:int`), cm_parameter_offsets_disjoint), function_wf),
      left_lower), left_right), right_upper);
  disjoint = conv_rule(rewrite_conv(THM_LIST(
      gsym_rule(left_number), gsym_rule(right_number))), disjoint);
  thm commute = match_mp_rule(specl_rule(TERM_LIST(
      `cm_slot_ty
        (inth (left:int) ${params:(cm_slot_d)list})`,
      `cm_state_env (st:cm_src_state) 2i (left:int)`,
      `left_value:cm_value`,
      `cm_slot_ty
        (inth (right:int) ${params:(cm_slot_d)list})`,
      `cm_state_env st 2i (right:int)`,
      `right_value:cm_value`, `st:cm_src_state`),
      cm_state_store_commute), disjoint);
  thm_list rules = THM_LIST(
      cm_parameter_state_store_def, cm_state_store_env);
  gnode reduced = CONV_WITH_ASMP_TAC(
      leaf, reduce_rewrite_conv, rules);
  ACCEPT_TAC(reduced, commute);
  return gnode_prove(root);
}
PROOF thm cm_parameter_state_store_commute =
    cm_prove_parameter_state_store_commute();

PROOF thm get_cm_parameter_state_store_commute(void) {
  return cm_parameter_state_store_commute;
}

PROOF static thm cm_prove_store_params_push_parameter(void) {
  gnode root = gnode_new_with_ccl(
      `!(values:(cm_value)list).
         !(p:cm_program) (fid:int) (st:cm_src_state)
           (old:(cm_region)list) (oldenv:int->int->cm_value)
           (gen:int) (fp:int) (oldfp:int)
           (left:int) (index:int) (held:cm_value).
           cm_function_wf p
             (inth fid (cm_program_functions p)) ==>
           cm_frame_segment p fid fp oldfp ==>
           cm_param_store_context p fid st old oldenv gen fp ==>
           0i <= left ==> left < index ==>
           index + ilength values <=
             ilength
               (cm_function_params
                 (inth fid (cm_program_functions p))) ==>
           cm_store_params p fid values index
             (cm_parameter_state_store p fid left held st) ==
           cm_parameter_state_store p fid left held
             (cm_store_params p fid values index st)`);
  gnode_list cases = INDUCT_TAC(root, `values:(cm_value)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        get_cm_store_params_def())));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    term params =
        `cm_function_params
          (inth (fid:int) (cm_program_functions (p:cm_program)))`;
    term next_state =
        `cm_parameter_state_store
          (p:cm_program) (fid:int) (index:int) (a0:cm_value)
          (st:cm_src_state)`;
    thm function_wf = assume_rule(
        `cm_function_wf (p:cm_program)
          (inth (fid:int) (cm_program_functions p))`);
    thm segment = assume_rule(
        `cm_frame_segment (p:cm_program) (fid:int)
          (fp:int) (oldfp:int)`);
    thm context = assume_rule(
        `cm_param_store_context (p:cm_program) (fid:int)
          (st:cm_src_state) (old:(cm_region)list)
          (oldenv:int->int->cm_value) (gen:int) (fp:int)`);
    thm left_lower = assume_rule(`0i <= (left:int)`);
    thm left_index = assume_rule(`(left:int) < (index:int)`);
    thm total_bound = assume_rule(
        `(index:int) + ilength
          ((a0:cm_value) :: (a1:(cm_value)list)) <=
         ilength ${params:(cm_slot_d)list}`);
    thm cons_length = apply_conversion(rewrite_conv(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF"))),
        `ilength ((a0:cm_value) :: (a1:(cm_value)list))`);
    thm rest_nonnegative = ispec_rule(
        `a1:(cm_value)list`,
        get_theorem_by_name("ILENGTH_NONNEG"));
    thm index_upper = mp_rule(mp_rule(mp_rule(int_arith_rule(
        `ilength ((a0:cm_value) :: (a1:(cm_value)list)) ==
             1i + ilength a1 ==>
         0i <= ilength a1 ==>
         (index:int) + ilength (a0 :: a1) <=
           ilength ${params:(cm_slot_d)list} ==>
         index < ilength ${params:(cm_slot_d)list}`),
        cons_length), rest_nonnegative), total_bound);
    thm tail_bound = mp_rule(mp_rule(int_arith_rule(
        `ilength ((a0:cm_value) :: (a1:(cm_value)list)) ==
             1i + ilength a1 ==>
         (index:int) + ilength (a0 :: a1) <=
           ilength ${params:(cm_slot_d)list} ==>
         (index + 1i) + ilength a1 <=
           ilength ${params:(cm_slot_d)list}`),
        cons_length), total_bound);
    thm left_next = mp_rule(int_arith_rule(
        `(left:int) < (index:int) ==> left < index + 1i`),
        left_index);
    thm next_context = match_mp_rule(specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `index:int`, `a0:cm_value`,
        `st:cm_src_state`, `old:(cm_region)list`,
        `oldenv:int->int->cm_value`, `gen:int`, `fp:int`),
        cm_param_store_context_store), context);
    thm commute = specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `st:cm_src_state`,
        `old:(cm_region)list`, `oldenv:int->int->cm_value`,
        `gen:int`, `fp:int`, `oldfp:int`,
        `left:int`, `index:int`, `held:cm_value`, `a0:cm_value`),
        cm_parameter_state_store_commute);
    commute = match_mp_rule(commute, function_wf);
    commute = match_mp_rule(commute, segment);
    commute = match_mp_rule(commute, context);
    commute = match_mp_rule(commute, left_lower);
    commute = match_mp_rule(commute, left_index);
    commute = match_mp_rule(commute, index_upper);
    thm reordered = beta_norm(ap_term_rule(
        `\base:cm_src_state.
           cm_store_params (p:cm_program) (fid:int)
             (a1:(cm_value)list) ((index:int) + 1i) base`,
        sym_rule(commute)));
    thm ih = specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, next_state,
        `old:(cm_region)list`, `oldenv:int->int->cm_value`,
        `gen:int`, `fp:int`, `oldfp:int`,
        `left:int`, `(index:int) + 1i`, `held:cm_value`),
        assume_rule(goal_lasmps(leaf->g)[0].tm));
    ih = match_mp_rule(ih, function_wf);
    ih = match_mp_rule(ih, segment);
    ih = match_mp_rule(ih, next_context);
    ih = match_mp_rule(ih, left_lower);
    ih = match_mp_rule(ih, left_next);
    ih = match_mp_rule(ih, tail_bound);
    thm result = trans_rule(reordered, ih);
    thm_list rules = THM_LIST(
        get_cm_store_params_def(), cm_parameter_state_store_def);
    thm normalized = conv_rule(
        reduce_rewrite_conv(rules), result);
    gnode reduced = CONV_TAC(
        leaf, reduce_rewrite_conv(rules));
    ACCEPT_TAC(reduced, normalized);
  }
  return gnode_prove(root);
}
PROOF thm cm_store_params_push_parameter =
    cm_prove_store_params_push_parameter();

PROOF thm get_cm_store_params_push_parameter(void) {
  return cm_store_params_push_parameter;
}

PROOF static thm cm_prove_store_params_reverse_forward(void) {
  gnode root = gnode_new_with_ccl(
      `!(values:(cm_value)list).
         !(p:cm_program) (fid:int) (st:cm_src_state)
           (old:(cm_region)list) (oldenv:int->int->cm_value)
           (gen:int) (fp:int) (oldfp:int) (index:int).
           cm_function_wf p
             (inth fid (cm_program_functions p)) ==>
           cm_frame_segment p fid fp oldfp ==>
           cm_param_store_context p fid st old oldenv gen fp ==>
           0i <= index ==>
           index + ilength values <=
             ilength
               (cm_function_params
                 (inth fid (cm_program_functions p))) ==>
           cm_store_params_reverse p fid values index st ==
           cm_store_params p fid values index st`);
  gnode_list cases = INDUCT_TAC(root, `values:(cm_value)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        cm_store_params_reverse_def, get_cm_store_params_def())));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    term params =
        `cm_function_params
          (inth (fid:int) (cm_program_functions (p:cm_program)))`;
    thm function_wf = assume_rule(
        `cm_function_wf (p:cm_program)
          (inth (fid:int) (cm_program_functions p))`);
    thm segment = assume_rule(
        `cm_frame_segment (p:cm_program) (fid:int)
          (fp:int) (oldfp:int)`);
    thm context = assume_rule(
        `cm_param_store_context (p:cm_program) (fid:int)
          (st:cm_src_state) (old:(cm_region)list)
          (oldenv:int->int->cm_value) (gen:int) (fp:int)`);
    thm index_lower = assume_rule(`0i <= (index:int)`);
    thm total_bound = assume_rule(
        `(index:int) + ilength
          ((a0:cm_value) :: (a1:(cm_value)list)) <=
         ilength ${params:(cm_slot_d)list}`);
    thm cons_length = apply_conversion(rewrite_conv(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF"))),
        `ilength ((a0:cm_value) :: (a1:(cm_value)list))`);
    thm tail_bound = mp_rule(mp_rule(int_arith_rule(
        `ilength ((a0:cm_value) :: (a1:(cm_value)list)) ==
             1i + ilength a1 ==>
         (index:int) + ilength (a0 :: a1) <=
           ilength ${params:(cm_slot_d)list} ==>
         (index + 1i) + ilength a1 <=
           ilength ${params:(cm_slot_d)list}`),
        cons_length), total_bound);
    thm next_lower = mp_rule(int_arith_rule(
        `0i <= (index:int) ==> 0i <= index + 1i`),
        index_lower);
    thm index_next = int_arith_rule(
        `(index:int) < index + 1i`);
    thm ih = specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `st:cm_src_state`,
        `old:(cm_region)list`, `oldenv:int->int->cm_value`,
        `gen:int`, `fp:int`, `oldfp:int`, `(index:int) + 1i`),
        assume_rule(goal_lasmps(leaf->g)[0].tm));
    ih = match_mp_rule(ih, function_wf);
    ih = match_mp_rule(ih, segment);
    ih = match_mp_rule(ih, context);
    ih = match_mp_rule(ih, next_lower);
    ih = match_mp_rule(ih, tail_bound);
    thm lifted = beta_norm(ap_term_rule(
        `\base:cm_src_state.
           cm_parameter_state_store
             (p:cm_program) (fid:int) (index:int)
             (a0:cm_value) base`,
        ih));
    thm pushed = specl_rule(TERM_LIST(
        `a1:(cm_value)list`, `p:cm_program`, `fid:int`,
        `st:cm_src_state`, `old:(cm_region)list`,
        `oldenv:int->int->cm_value`, `gen:int`, `fp:int`,
        `oldfp:int`, `index:int`, `(index:int) + 1i`,
        `a0:cm_value`), cm_store_params_push_parameter);
    pushed = match_mp_rule(pushed, function_wf);
    pushed = match_mp_rule(pushed, segment);
    pushed = match_mp_rule(pushed, context);
    pushed = match_mp_rule(pushed, index_lower);
    pushed = match_mp_rule(pushed, index_next);
    pushed = match_mp_rule(pushed, tail_bound);
    thm result = trans_rule(lifted, sym_rule(pushed));
    thm_list rules = THM_LIST(
        cm_store_params_reverse_def, get_cm_store_params_def(),
        cm_parameter_state_store_def);
    thm normalized = conv_rule(
        reduce_rewrite_conv(rules), result);
    gnode reduced = CONV_TAC(
        leaf, reduce_rewrite_conv(rules));
    ACCEPT_TAC(reduced, normalized);
  }
  return gnode_prove(root);
}
PROOF thm cm_store_params_reverse_forward =
    cm_prove_store_params_reverse_forward();

PROOF thm get_cm_store_params_reverse_forward(void) {
  return cm_store_params_reverse_forward;
}

PROOF static int cmc_preservation_call_params_permute_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_call_params_permute_axioms_before,
      "cmc_preservation_call_params_permute introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_call_params_permute_checks =
    cmc_preservation_call_params_permute_final_checks();
