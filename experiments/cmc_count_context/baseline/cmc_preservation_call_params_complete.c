#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_call_params_complete.h"

#require "cmc_preservation_call_clear.c"
#require "cmc_preservation_call_params_permute.c"

PROOF static size_t _cmc_preservation_call_params_complete_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_params_complete_assumption(
    const gnode node, const term wanted) {
  labeled_term_list assumptions = goal_lasmps(node->g);
  for (size_t index = 0; index < vector_size(assumptions); ++index) {
    if (alpha_compare(assumptions[index].tm, wanted) == 0) {
      return assume_rule(assumptions[index].tm);
    }
  }
  return empty_theorem;
}

PROOF static thm cm_params_complete_consequence(
    const thm premise, const term conclusion) {
  return mp_rule(taut_rule(mk_imp(concl(premise), conclusion)), premise);
}

PROOF static thm cm_prove_slots_prefix_zero_complete(void) {
  gnode root = gnode_new_with_ccl(
      `!(structs:(cm_struct_d)list) (slots:(cm_slot_d)list).
         cm_slots_prefix structs slots 0i == 0i`);
  gnode with_structs = GEN_TAC(root, "structs");
  gnode_list cases = INDUCT_TAC(
      with_structs, `slots:(cm_slot_d)list`);
  for (size_t index = 0; index < vector_size(cases); ++index) {
    gnode leaf = AUTO_INTROS_TAC(cases[index]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        get_cm_slots_prefix_def())));
  }
  return gnode_prove(root);
}
PROOF static thm cm_slots_prefix_zero_complete =
    cm_prove_slots_prefix_zero_complete();


PROOF static thm cm_prove_slots_prefix_step(void) {
  gnode root = gnode_new_with_ccl(
      `!(structs:(cm_struct_d)list) (slots:(cm_slot_d)list).
         cm_slot_sizes_positive structs slots ==>
         !(index:int).
           0i <= index ==> index < ilength slots ==>
           cm_slots_prefix structs slots (index + 1i) ==
           cm_slots_prefix structs slots index +
             cm_slot_size structs (inth index slots)`);
  gnode with_structs = GEN_TAC(root, "structs");
  gnode_list cases = INDUCT_TAC(
      with_structs, `slots:(cm_slot_d)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm upper = conv_rule(rewrite_conv(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF"))), assume_rule(
        `(index:int) < ilength ([]:(cm_slot_d)list)`));
    thm impossible = mp_rule(mp_rule(int_arith_rule(
        `0i <= (index:int) ==> index < 0i ==> F`),
        assume_rule(`0i <= (index:int)`)), upper);
    CONTR_TAC(leaf, impossible);
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm positive = conv_rule(rewrite_conv(THM_LIST(
        cm_slot_sizes_positive_def)), assume_rule(
        `cm_slot_sizes_positive (structs:(cm_struct_d)list)
          ((a0:cm_slot_d) :: (a1:(cm_slot_d)list))`));
    thm lower = assume_rule(`0i <= (index:int)`);
    thm upper = conv_rule(rewrite_conv(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF"))), assume_rule(
        `(index:int) < ilength
          ((a0:cm_slot_d) :: (a1:(cm_slot_d)list))`));
    gnode_list zero_cases = BOOL_CASES_TAC(
        leaf, `(index:int) == 0i`, "Hindex_zero");
    {
      thm zero = assume_rule(`(index:int) == 0i`);
      thm head_at = ispecl_rule(TERM_LIST(
          `a0:cm_slot_d`, `a1:(cm_slot_d)list`),
          cm_inth_zero_cons);
      gnode reduced_zero = CONV_WITH_ASMP_TAC(
          zero_cases[0], reduce_rewrite_conv,
          THM_LIST(get_cm_slots_prefix_def(), zero, head_at));
      if (IS_NULL(reduced_zero->solved)) {
        gnode normalized_zero = CONV_TAC(
            reduced_zero, reduce_rewrite_conv(THM_LIST(
              cm_slots_prefix_zero_complete)));
        if (IS_NULL(normalized_zero->solved)) {
          ACCEPT_TAC(normalized_zero,
              int_ring_rule(goal_ccl(normalized_zero->g)));
        }
      }
    }
    {
      thm nonzero = assume_rule(`~((index:int) == 0i)`);
      thm one = mp_rule(mp_rule(int_arith_rule(
          `0i <= (index:int) ==> ~(index == 0i) ==>
           1i <= index`), lower), nonzero);
      thm tail_bounds = mp_rule(mp_rule(int_arith_rule(
          `1i <= (index:int) ==>
           index < 1i + ilength (a1:(cm_slot_d)list) ==>
           0i <= index - 1i &&
           index - 1i < ilength a1`), one), upper);
      thm ih = match_mp_rule(
          cm_params_complete_assumption(zero_cases[1],
            `cm_slot_sizes_positive
               (structs:(cm_struct_d)list)
               (a1:(cm_slot_d)list) ==>
             !(index:int).
               0i <= index ==> index < ilength a1 ==>
               cm_slots_prefix structs a1 (index + 1i) ==
               cm_slots_prefix structs a1 index +
                 cm_slot_size structs (inth index a1)`),
          conjunct2_rule(positive));
      thm tail_step = match_mp_rule(match_mp_rule(
          spec_rule(`(index:int) - 1i`, ih),
          conjunct1_rule(tail_bounds)),
          conjunct2_rule(tail_bounds));
      thm current_at_tail = mp_rule(ispecl_rule(TERM_LIST(
          `a0:cm_slot_d`, `a1:(cm_slot_d)list`, `index:int`),
          cm_inth_cons_tail), one);
      thm next_one = mp_rule(int_arith_rule(
          `1i <= (index:int) ==> 1i <= index + 1i`), one);
      thm next_at_tail = mp_rule(ispecl_rule(TERM_LIST(
          `a0:cm_slot_d`, `a1:(cm_slot_d)list`,
          `(index:int) + 1i`), cm_inth_cons_tail), next_one);
      gnode reduced = CONV_WITH_ASMP_TAC(
          zero_cases[1], reduce_rewrite_conv, THM_LIST(
            get_cm_slots_prefix_def(), nonzero,
            mp_rule(int_arith_rule(
              `1i <= (index:int) ==> ~(index + 1i == 0i)`), one),
            current_at_tail, next_at_tail,
            int_ring_rule(
              `!z:int. (z - 1i) + 1i == z`),
            int_ring_rule(
              `!z:int. (z + 1i) - 1i == z`)));
      thm tail_normalized = conv_rule(rewrite_conv(THM_LIST(
          int_ring_rule(
            `!z:int. (z - 1i) + 1i == z`))), tail_step);
      gnode final_node = CONV_TAC(
          reduced, reduce_rewrite_conv(THM_LIST(tail_normalized)));
      ACCEPT_TAC(final_node,
          int_ring_rule(goal_ccl(final_node->g)));
    }
  }
  return gnode_prove(root);
}
PROOF static thm cm_slots_prefix_step =
    cm_prove_slots_prefix_step();


PROOF static thm cm_prove_slots_prefix_length_complete(void) {
  gnode root = gnode_new_with_ccl(
      `!(structs:(cm_struct_d)list) (slots:(cm_slot_d)list).
         cm_slots_prefix structs slots (ilength slots) ==
         cm_slots_size structs slots`);
  gnode with_structs = GEN_TAC(root, "structs");
  gnode_list cases = INDUCT_TAC(
      with_structs, `slots:(cm_slot_d)list`);
  for (size_t index = 0; index < vector_size(cases); ++index) {
    gnode leaf = AUTO_INTROS_TAC(cases[index]);
    if (index == 0) {
      CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
          get_cm_slots_prefix_def(), get_cm_slots_size_def())));
      continue;
    }
    thm tail_nonnegative = ispec_rule(
        `a1:(cm_slot_d)list`,
        get_theorem_by_name("ILENGTH_NONNEG"));
    thm length_positive = mp_rule(int_arith_rule(
        `0i <= ilength (a1:(cm_slot_d)list) ==>
         ~(1i + ilength a1 == 0i)`), tail_nonnegative);
    thm induction = cm_params_complete_assumption(leaf,
        `cm_slots_prefix (structs:(cm_struct_d)list)
           (a1:(cm_slot_d)list) (ilength a1) ==
         cm_slots_size structs a1`);
    thm argument = spec_rule(
        `ilength (a1:(cm_slot_d)list)`,
        int_ring_rule(`!z:int. (1i + z) - 1i == z`));
    thm prefix_argument = beta_norm(ap_term_rule(
        `\n:int.
           cm_slots_prefix (structs:(cm_struct_d)list)
             (a1:(cm_slot_d)list) n`,
        argument));
    thm normalized_induction = trans_rule(
        prefix_argument, induction);
    thm lifted = beta_norm(ap_term_rule(
        `\x:int.
           cm_slot_size (structs:(cm_struct_d)list)
             (a0:cm_slot_d) + x`,
        normalized_induction));
    thm target_view = apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          get_theorem_by_name("ILENGTH_DEF"),
          get_cm_slots_prefix_def(),
          get_cm_slots_size_def(), length_positive)),
        goal_ccl(leaf->g));
    ACCEPT_TAC(leaf, eq_mp_rule(gsym_rule(target_view), lifted));
}
  return gnode_prove(root);
}
PROOF static thm cm_slots_prefix_length_complete =
    cm_prove_slots_prefix_length_complete();


PROOF static thm cm_prove_parameter_cell_shape(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (index:int).
         cm_function_wf p
           (inth fid (cm_program_functions p)) ==>
         0i <= index ==>
         index <
           ilength
             (cm_function_params
               (inth fid (cm_program_functions p))) ==>
         0i <
           cm_slot_size (cm_program_structs p)
             (inth index
               (cm_function_params
                 (inth fid (cm_program_functions p)))) &&
         cm_slot_size (cm_program_structs p)
             (inth index
               (cm_function_params
                 (inth fid (cm_program_functions p)))) ==
           cm_store_width
             (cm_slot_ty
               (inth index
                 (cm_function_params
                   (inth fid (cm_program_functions p)))))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  term params =
      `cm_function_params
        (inth (fid:int) (cm_program_functions (p:cm_program)))`;
  thm function_open = conv_rule(rewrite_conv(THM_LIST(
      get_cm_function_wf_def())), assume_rule(
        `cm_function_wf (p:cm_program)
          (inth (fid:int) (cm_program_functions p))`));
  thm params_wf = cm_params_complete_consequence(function_open,
      `cm_params_wf (cm_program_structs (p:cm_program))
        ${params:(cm_slot_d)list}`);
  thm params_open = conv_rule(rewrite_conv(THM_LIST(
      get_cm_params_wf_def())), params_wf);
  thm slots_open = conv_rule(rewrite_conv(THM_LIST(
      get_cm_slots_wf_def())), conjunct1_rule(params_open));
  thm lower = assume_rule(`0i <= (index:int)`);
  thm upper = assume_rule(
      `(index:int) < ilength ${params:(cm_slot_d)list}`);
  thm cell_wf = match_mp_rule(match_mp_rule(
      spec_rule(`index:int`, slots_open), lower), upper);
  thm count_zero = match_mp_rule(match_mp_rule(
      spec_rule(`index:int`, conjunct2_rule(params_open)),
      lower), upper);
  thm scalar = cm_params_complete_consequence(
      conv_rule(rewrite_conv(THM_LIST(
        get_cm_slot_wf_def())), cell_wf),
      `cm_scalar_type (cm_program_structs (p:cm_program))
        (cm_slot_ty
          (inth (index:int) ${params:(cm_slot_d)list}))`);
  thm type_shape = conjunct2_rule(mp_rule(specl_rule(TERM_LIST(
      `cm_slot_ty
        (inth (index:int) ${params:(cm_slot_d)list})`,
      `cm_program_structs (p:cm_program)`),
      cm_scalar_store_shape), scalar));
  thm size_width = by_rewrite(
      `cm_slot_size (cm_program_structs (p:cm_program))
         (inth (index:int) ${params:(cm_slot_d)list}) ==
       cm_store_width
         (cm_slot_ty
           (inth index ${params:(cm_slot_d)list}))`,
      THM_LIST(get_cm_slot_size_def(), count_zero, type_shape));
  thm width_at_least_one = spec_rule(
      `cm_slot_ty
        (inth (index:int) ${params:(cm_slot_d)list})`,
      get_cm_store_width_positive());
  thm positive = mp_rule(mp_rule(int_arith_rule(
      mk_imp(concl(size_width),
        mk_imp(concl(width_at_least_one),
          `0i <
             cm_slot_size (cm_program_structs (p:cm_program))
               (inth (index:int) ${params:(cm_slot_d)list})`))),
      size_width), width_at_least_one);
  ACCEPT_TAC(leaf, conj_rule(positive, size_width));
  return gnode_prove(root);
}
PROOF static thm cm_parameter_cell_shape =
    cm_prove_parameter_cell_shape();


PROOF static thm cm_prove_param_store_context_clear(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (st:cm_src_state)
         (old:(cm_region)list)
         (oldenv:int->int->cm_value) (gen:int) (fp:int)
         (span_base:int) (span_width:int).
         cm_param_store_context p fid st old oldenv gen fp ==>
         cm_param_store_context p fid
           (cm_state_clear_range st span_base span_width)
           old oldenv gen fp`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm_list rules = get_cm_state_core_defs();
  vector_add(&rules, get_cm_state_clear_range_def());
  vector_add(&rules, get_cm_param_store_context_def());
  gnode reduced = CONV_TAC(leaf, reduce_rewrite_conv(rules));
  if (IS_NULL(reduced->solved)) {
    thm opened = conv_rule(
        rewrite_conv(THM_LIST(get_cm_param_store_context_def())),
        assume_rule(
          `cm_param_store_context (p:cm_program) (fid:int)
             (st:cm_src_state) (old:(cm_region)list)
             (oldenv:int->int->cm_value) (gen:int) (fp:int)`));
    ACCEPT_TAC(reduced, opened);
  }
  return gnode_prove(root);
}
PROOF static thm cm_param_store_context_clear =
    cm_prove_param_store_context_clear();

PROOF static thm cm_prove_parameter_slots_positive(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int).
         cm_function_wf p
           (inth fid (cm_program_functions p)) ==>
         cm_slot_sizes_positive (cm_program_structs p)
           (cm_function_params
             (inth fid (cm_program_functions p)))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  term params =
      `cm_function_params
        (inth (fid:int) (cm_program_functions (p:cm_program)))`;
  thm function_open = conv_rule(rewrite_conv(THM_LIST(
      get_cm_function_wf_def())), assume_rule(
        `cm_function_wf (p:cm_program)
          (inth (fid:int) (cm_program_functions p))`));
  thm params_wf = cm_params_complete_consequence(function_open,
      `cm_params_wf (cm_program_structs (p:cm_program))
        ${params:(cm_slot_d)list}`);
  thm slots_wf = conjunct1_rule(conv_rule(
      rewrite_conv(THM_LIST(get_cm_params_wf_def())), params_wf));
  ACCEPT_TAC(leaf, match_mp_rule(specl_rule(TERM_LIST(
      `cm_program_structs (p:cm_program)`,
      params), cm_slots_wf_sizes_positive), slots_wf));
  return gnode_prove(root);
}
PROOF static thm cm_parameter_slots_positive =
    cm_prove_parameter_slots_positive();



PROOF static thm cm_prove_parameter_clear_layout_step(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (fp:int) (index:int).
         cm_function_wf p
           (inth fid (cm_program_functions p)) ==>
         0i <= index ==>
         index + 1i <
           ilength
             (cm_function_params
               (inth fid (cm_program_functions p))) ==>
         0i <
           cm_store_width
             (cm_slot_ty
               (inth index
                 (cm_function_params
                   (inth fid (cm_program_functions p))))) &&
         0i <
           cm_slots_size (cm_program_structs p)
               (cm_function_params
                 (inth fid (cm_program_functions p))) -
             cm_slots_prefix (cm_program_structs p)
               (cm_function_params
                 (inth fid (cm_program_functions p)))
               (index + 1i) &&
         cm_slots_size (cm_program_structs p)
               (cm_function_params
                 (inth fid (cm_program_functions p))) -
             cm_slots_prefix (cm_program_structs p)
               (cm_function_params
                 (inth fid (cm_program_functions p)))
               index ==
           cm_store_width
               (cm_slot_ty
                 (inth index
                   (cm_function_params
                     (inth fid (cm_program_functions p))))) +
             (cm_slots_size (cm_program_structs p)
                 (cm_function_params
                   (inth fid (cm_program_functions p))) -
               cm_slots_prefix (cm_program_structs p)
                 (cm_function_params
                   (inth fid (cm_program_functions p)))
                 (index + 1i)) &&
         fp + cm_param_offset p fid (index + 1i) ==
           (fp + cm_param_offset p fid index) +
             cm_store_width
               (cm_slot_ty
                 (inth index
                   (cm_function_params
                     (inth fid (cm_program_functions p)))))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  term params =
      `cm_function_params
        (inth (fid:int) (cm_program_functions (p:cm_program)))`;
  term structs = `cm_program_structs (p:cm_program)`;
  term current_size =
      `cm_slot_size ${structs:(cm_struct_d)list}
        (inth (index:int) ${params:(cm_slot_d)list})`;
  term current_width =
      `cm_store_width
        (cm_slot_ty
          (inth (index:int) ${params:(cm_slot_d)list}))`;
  thm function_wf = assume_rule(
      `cm_function_wf (p:cm_program)
        (inth (fid:int) (cm_program_functions p))`);
  thm index_lower = assume_rule(`0i <= (index:int)`);
  thm next_upper = assume_rule(
      `(index:int) + 1i < ilength ${params:(cm_slot_d)list}`);
  thm index_upper = mp_rule(int_arith_rule(
      `(index:int) + 1i < ilength ${params:(cm_slot_d)list} ==>
       index < ilength ${params:(cm_slot_d)list}`),
      next_upper);
  thm next_lower = mp_rule(int_arith_rule(
      `0i <= (index:int) ==> 0i <= index + 1i`),
      index_lower);
  thm current_shape = match_mp_rule(match_mp_rule(
      match_mp_rule(specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `index:int`),
        cm_parameter_cell_shape), function_wf),
      index_lower), index_upper);
  thm next_shape = match_mp_rule(match_mp_rule(
      match_mp_rule(specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `(index:int) + 1i`),
        cm_parameter_cell_shape), function_wf),
      next_lower), next_upper);
  thm current_positive = conjunct1_rule(current_shape);
  thm current_size_width = conjunct2_rule(current_shape);
  thm width_positive = mp_rule(mp_rule(int_arith_rule(
      mk_imp(concl(current_positive),
        mk_imp(concl(current_size_width),
          `0i < ${current_width:int}`))),
      current_positive), current_size_width);
  thm positive = match_mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`),
      cm_parameter_slots_positive), function_wf);
  thm next_prefix_bounds = match_mp_rule(match_mp_rule(
      spec_rule(`(index:int) + 1i`,
        match_mp_rule(specl_rule(TERM_LIST(
          structs, params), cm_slots_prefix_cell_bounds),
          positive)),
      next_lower), next_upper);
  thm tail_positive = mp_rule(mp_rule(int_arith_rule(
      mk_imp(concl(conjunct2_rule(next_prefix_bounds)),
        mk_imp(concl(conjunct1_rule(next_shape)),
          `0i <
             cm_slots_size ${structs:(cm_struct_d)list}
               ${params:(cm_slot_d)list} -
             cm_slots_prefix ${structs:(cm_struct_d)list}
               ${params:(cm_slot_d)list} ((index:int) + 1i)`))),
      conjunct2_rule(next_prefix_bounds)),
      conjunct1_rule(next_shape));
  thm prefix_step = match_mp_rule(match_mp_rule(
      spec_rule(`index:int`,
        match_mp_rule(specl_rule(TERM_LIST(
          structs, params), cm_slots_prefix_step),
          positive)),
      index_lower), index_upper);
  term remaining_step =
      `cm_slots_size ${structs:(cm_struct_d)list}
           ${params:(cm_slot_d)list} -
         cm_slots_prefix ${structs:(cm_struct_d)list}
           ${params:(cm_slot_d)list} (index:int) ==
       ${current_width:int} +
         (cm_slots_size ${structs:(cm_struct_d)list}
            ${params:(cm_slot_d)list} -
          cm_slots_prefix ${structs:(cm_struct_d)list}
            ${params:(cm_slot_d)list} (index + 1i))`;
  thm remaining = mp_rule(mp_rule(int_arith_rule(
      mk_imp(concl(prefix_step),
        mk_imp(concl(current_size_width), remaining_step))),
      prefix_step), current_size_width);
  thm address_expanded = mp_rule(mp_rule(int_arith_rule(
      mk_imp(concl(prefix_step),
        mk_imp(concl(current_size_width),
          `((fp:int) + 8i +
               cm_slots_prefix ${structs:(cm_struct_d)list}
                 ${params:(cm_slot_d)list} ((index:int) + 1i)) ==
           (fp + 8i +
             cm_slots_prefix ${structs:(cm_struct_d)list}
               ${params:(cm_slot_d)list} index) +
             ${current_width:int}`))),
      prefix_step), current_size_width);
  thm address = conv_rule(reduce_rewrite_conv(THM_LIST(
      gsym_rule(get_cm_param_offset_def()))), address_expanded);
  ACCEPT_TAC(leaf, conj_rule(width_positive,
      conj_rule(tail_positive, conj_rule(remaining, address))));
  return gnode_prove(root);
}
PROOF static thm cm_parameter_clear_layout_step =
    cm_prove_parameter_clear_layout_step();


PROOF static thm cm_prove_parameter_clear_layout_last(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (index:int).
         cm_function_wf p
           (inth fid (cm_program_functions p)) ==>
         0i <= index ==>
         index + 1i ==
           ilength
             (cm_function_params
               (inth fid (cm_program_functions p))) ==>
         0i <
           cm_store_width
             (cm_slot_ty
               (inth index
                 (cm_function_params
                   (inth fid (cm_program_functions p))))) &&
         cm_slots_size (cm_program_structs p)
               (cm_function_params
                 (inth fid (cm_program_functions p))) -
             cm_slots_prefix (cm_program_structs p)
               (cm_function_params
                 (inth fid (cm_program_functions p)))
               index ==
           cm_store_width
             (cm_slot_ty
               (inth index
                 (cm_function_params
                   (inth fid (cm_program_functions p)))))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  term params =
      `cm_function_params
        (inth (fid:int) (cm_program_functions (p:cm_program)))`;
  term structs = `cm_program_structs (p:cm_program)`;
  term current_width =
      `cm_store_width
        (cm_slot_ty
          (inth (index:int) ${params:(cm_slot_d)list}))`;
  thm function_wf = assume_rule(
      `cm_function_wf (p:cm_program)
        (inth (fid:int) (cm_program_functions p))`);
  thm index_lower = assume_rule(`0i <= (index:int)`);
  thm reaches_end = assume_rule(
      `(index:int) + 1i == ilength ${params:(cm_slot_d)list}`);
  thm index_upper = mp_rule(int_arith_rule(
      `(index:int) + 1i == ilength ${params:(cm_slot_d)list} ==>
       index < ilength ${params:(cm_slot_d)list}`),
      reaches_end);
  thm shape = match_mp_rule(match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `index:int`),
        cm_parameter_cell_shape), function_wf),
      index_lower), index_upper);
  thm size_positive = conjunct1_rule(shape);
  thm size_width = conjunct2_rule(shape);
  thm width_positive = mp_rule(mp_rule(int_arith_rule(
      mk_imp(concl(size_positive),
        mk_imp(concl(size_width),
          `0i < ${current_width:int}`))),
      size_positive), size_width);
  thm positive = match_mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`),
      cm_parameter_slots_positive), function_wf);
  thm prefix_step = match_mp_rule(match_mp_rule(
      spec_rule(`index:int`,
        match_mp_rule(specl_rule(TERM_LIST(
          structs, params), cm_slots_prefix_step),
          positive)),
      index_lower), index_upper);
  thm prefix_reaches_end = beta_norm(ap_term_rule(
      `\n:int.
         cm_slots_prefix ${structs:(cm_struct_d)list}
           ${params:(cm_slot_d)list} n`,
      reaches_end));
  thm prefix_total = trans_rule(prefix_reaches_end,
      specl_rule(TERM_LIST(structs, params),
        cm_slots_prefix_length_complete));
  term remaining_last =
      `cm_slots_size ${structs:(cm_struct_d)list}
           ${params:(cm_slot_d)list} -
         cm_slots_prefix ${structs:(cm_struct_d)list}
           ${params:(cm_slot_d)list} (index:int) ==
       ${current_width:int}`;
  thm remaining = mp_rule(mp_rule(mp_rule(int_arith_rule(
      mk_imp(concl(prefix_step),
        mk_imp(concl(prefix_total),
          mk_imp(concl(size_width), remaining_last)))),
      prefix_step), prefix_total), size_width);
  ACCEPT_TAC(leaf, conj_rule(width_positive, remaining));
  return gnode_prove(root);
}
PROOF static thm cm_parameter_clear_layout_last =
    cm_prove_parameter_clear_layout_last();


PROOF static thm cm_prove_parameter_store_split_clear(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (stored:cm_value)
         (st:cm_src_state) (old:(cm_region)list)
         (oldenv:int->int->cm_value) (gen:int) (fp:int)
         (oldfp:int) (index:int).
         cm_function_wf p
           (inth fid (cm_program_functions p)) ==>
         cm_frame_segment p fid fp oldfp ==>
         cm_param_store_context p fid st old oldenv gen fp ==>
         0i <= index ==>
         index + 1i <
           ilength
             (cm_function_params
               (inth fid (cm_program_functions p))) ==>
         cm_parameter_state_store p fid index stored
           (cm_state_clear_range st
             (fp + cm_param_offset p fid index)
             (cm_slots_size (cm_program_structs p)
                 (cm_function_params
                   (inth fid (cm_program_functions p))) -
               cm_slots_prefix (cm_program_structs p)
                 (cm_function_params
                   (inth fid (cm_program_functions p)))
                 index)) ==
         cm_state_clear_range
           (cm_parameter_state_store p fid index stored st)
           (fp + cm_param_offset p fid (index + 1i))
           (cm_slots_size (cm_program_structs p)
               (cm_function_params
                 (inth fid (cm_program_functions p))) -
             cm_slots_prefix (cm_program_structs p)
               (cm_function_params
                 (inth fid (cm_program_functions p)))
               (index + 1i))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  term params =
      `cm_function_params
        (inth (fid:int) (cm_program_functions (p:cm_program)))`;
  term structs = `cm_program_structs (p:cm_program)`;
  term ty =
      `cm_slot_ty
        (inth (index:int) ${params:(cm_slot_d)list})`;
  term ptr =
      `cm_state_env (st:cm_src_state) 2i (index:int)`;
  term current_base =
      `(fp:int) + cm_param_offset (p:cm_program) (fid:int)
        (index:int)`;
  term next_base =
      `(fp:int) + cm_param_offset (p:cm_program) (fid:int)
        ((index:int) + 1i)`;
  term current_width = `cm_store_width ${ty:cm_type}`;
  term current_remaining =
      `cm_slots_size ${structs:(cm_struct_d)list}
          ${params:(cm_slot_d)list} -
        cm_slots_prefix ${structs:(cm_struct_d)list}
          ${params:(cm_slot_d)list} (index:int)`;
  term tail_remaining =
      `cm_slots_size ${structs:(cm_struct_d)list}
          ${params:(cm_slot_d)list} -
        cm_slots_prefix ${structs:(cm_struct_d)list}
          ${params:(cm_slot_d)list} ((index:int) + 1i)`;
  term current_cleared =
      `cm_state_clear_range (st:cm_src_state)
        ${current_base:int} ${current_width:int}`;
  term current_ptr =
      `cm_state_env ${current_cleared:cm_src_state}
        2i (index:int)`;
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
  thm next_upper = assume_rule(
      `(index:int) + 1i < ilength ${params:(cm_slot_d)list}`);
  thm index_upper = mp_rule(int_arith_rule(
      `(index:int) + 1i < ilength ${params:(cm_slot_d)list} ==>
       index < ilength ${params:(cm_slot_d)list}`),
      next_upper);
  thm layout = match_mp_rule(match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `fp:int`, `index:int`),
        cm_parameter_clear_layout_step), function_wf),
      index_lower), next_upper);
  thm width_positive = conjunct1_rule(layout);
  thm tail_positive = conjunct1_rule(conjunct2_rule(layout));
  thm remaining = conjunct1_rule(
      conjunct2_rule(conjunct2_rule(layout)));
  thm address = conjunct2_rule(
      conjunct2_rule(conjunct2_rule(layout)));
  thm joined = match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(
        `st:cm_src_state`, current_base, current_width,
        tail_remaining), get_cm_state_clear_range_join()),
      width_positive), tail_positive);
  thm current_width_lift = beta_norm(ap_term_rule(
      `\amount:int.
         cm_state_clear_range (st:cm_src_state)
           ${current_base:int} amount`,
      remaining));
  thm next_base_lift = beta_norm(ap_term_rule(
      `\base:int.
         cm_state_clear_range ${current_cleared:cm_src_state}
           base ${tail_remaining:int}`,
      gsym_rule(address)));
  thm joined_normalized = trans_rule(current_width_lift,
      trans_rule(joined, next_base_lift));
  thm store_joined = beta_norm(ap_term_rule(
      `\base:cm_src_state.
         cm_state_store ${ty:cm_type} ${current_ptr:cm_value}
           (stored:cm_value) base`,
      joined_normalized));
  thm address_ready = match_mp_rule(match_mp_rule(
      match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `fp:int`, `oldfp:int`,
        `index:int`), cm_parameter_address_ready),
        function_wf), segment), index_lower), index_upper);
  thm address_is_signed = conjunct1_rule(
      conjunct2_rule(conjunct2_rule(address_ready)));
  thm pointer_number = match_mp_rule(match_mp_rule(
      match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `st:cm_src_state`,
        `old:(cm_region)list`, `oldenv:int->int->cm_value`,
        `gen:int`, `fp:int`, `index:int`),
        cm_parameter_pointer_number), context),
      index_lower), index_upper), address_is_signed);
  thm current_context = match_mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`,
      `old:(cm_region)list`, `oldenv:int->int->cm_value`,
      `gen:int`, `fp:int`, current_base, current_width),
      cm_param_store_context_clear), context);
  thm current_pointer_number = match_mp_rule(match_mp_rule(
      match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, current_cleared,
        `old:(cm_region)list`, `oldenv:int->int->cm_value`,
        `gen:int`, `fp:int`, `index:int`),
        cm_parameter_pointer_number), current_context),
      index_lower), index_upper), address_is_signed);
  thm_list structural_rules = get_cm_state_core_defs();
  vector_add(&structural_rules, get_cm_state_clear_range_def());
  thm env_equal = by_rewrite(
      `cm_state_env ${current_cleared:cm_src_state} ==
       cm_state_env (st:cm_src_state)`,
      structural_rules);
  thm ptr_equal = beta_norm(ap_term_rule(
      `\env:int->int->cm_value. env 2i (index:int)`,
      env_equal));
  thm ptr_number_equal = beta_norm(ap_term_rule(
      `\q:cm_value.
         cm_value_number (st:cm_src_state) q`,
      ptr_equal));
  thm current_ptr_number = trans_rule(
      ptr_number_equal, pointer_number);
  thm adjacent = mp_rule(int_arith_rule(
      mk_imp(concl(address),
        `${current_base:int} + ${current_width:int} <=
         ${next_base:int}`)), address);
  term disjoint_open =
      `${current_base:int} + ${current_width:int} <=
         ${next_base:int} ||
       ${next_base:int} + ${tail_remaining:int} <=
         ${current_base:int}`;
  thm disjunction = mp_rule(
      taut_rule(mk_imp(concl(adjacent), disjoint_open)), adjacent);
  term disjoint_term =
      `cm_range_disjoint ${current_base:int}
         ${current_width:int} ${next_base:int}
         ${tail_remaining:int}`;
  thm cell_disjoint = eq_mp_rule(gsym_rule(apply_conversion(
      rewrite_conv(THM_LIST(get_cm_range_disjoint_def())),
      disjoint_term)), disjunction);
  thm commuted = specl_rule(TERM_LIST(
      ty, current_ptr, `stored:cm_value`, current_cleared,
      current_base, next_base, tail_remaining),
      get_cm_state_store_clear_commute());
  commuted = match_mp_rule(commuted, current_pointer_number);
  commuted = match_mp_rule(commuted, tail_positive);
  commuted = match_mp_rule(commuted, cell_disjoint);
  thm absorbed = match_mp_rule(specl_rule(TERM_LIST(
      ty, current_ptr, `stored:cm_value`, `st:cm_src_state`,
      current_base), get_cm_state_store_absorb_clear()),
      current_ptr_number);
  thm absorbed_lift = beta_norm(ap_term_rule(
      `\base:cm_src_state.
         cm_state_clear_range base ${next_base:int}
           ${tail_remaining:int}`,
      absorbed));
  thm result = trans_rule(store_joined,
      trans_rule(commuted, absorbed_lift));
  thm_list normalization = get_cm_state_core_defs();
  vector_add(&normalization, get_cm_state_clear_range_def());
  vector_add(&normalization, get_cm_parameter_state_store_def());
  thm normalized_result = conv_rule(
      reduce_rewrite_conv(normalization), result);
  thm target_view = apply_conversion(
      reduce_rewrite_conv(normalization), goal_ccl(leaf->g));
  ACCEPT_TAC(leaf,
      eq_mp_rule(gsym_rule(target_view), normalized_result));
  return gnode_prove(root);
}
PROOF static thm cm_parameter_store_split_clear =
    cm_prove_parameter_store_split_clear();


PROOF static thm cm_prove_parameter_store_last_clear(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (stored:cm_value)
         (st:cm_src_state) (old:(cm_region)list)
         (oldenv:int->int->cm_value) (gen:int) (fp:int)
         (oldfp:int) (index:int).
         cm_function_wf p
           (inth fid (cm_program_functions p)) ==>
         cm_frame_segment p fid fp oldfp ==>
         cm_param_store_context p fid st old oldenv gen fp ==>
         0i <= index ==>
         index + 1i ==
           ilength
             (cm_function_params
               (inth fid (cm_program_functions p))) ==>
         cm_parameter_state_store p fid index stored
           (cm_state_clear_range st
             (fp + cm_param_offset p fid index)
             (cm_slots_size (cm_program_structs p)
                 (cm_function_params
                   (inth fid (cm_program_functions p))) -
               cm_slots_prefix (cm_program_structs p)
                 (cm_function_params
                   (inth fid (cm_program_functions p)))
                 index)) ==
         cm_parameter_state_store p fid index stored st`);
  gnode leaf = AUTO_INTROS_TAC(root);
  term params =
      `cm_function_params
        (inth (fid:int) (cm_program_functions (p:cm_program)))`;
  term ty =
      `cm_slot_ty
        (inth (index:int) ${params:(cm_slot_d)list})`;
  term ptr =
      `cm_state_env (st:cm_src_state) 2i (index:int)`;
  term current_base =
      `(fp:int) + cm_param_offset (p:cm_program) (fid:int)
        (index:int)`;
  term current_width = `cm_store_width ${ty:cm_type}`;
  term current_remaining =
      `cm_slots_size (cm_program_structs (p:cm_program))
          ${params:(cm_slot_d)list} -
        cm_slots_prefix (cm_program_structs p)
          ${params:(cm_slot_d)list} (index:int)`;
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
  thm reaches_end = assume_rule(
      `(index:int) + 1i == ilength ${params:(cm_slot_d)list}`);
  thm index_upper = mp_rule(int_arith_rule(
      `(index:int) + 1i == ilength ${params:(cm_slot_d)list} ==>
       index < ilength ${params:(cm_slot_d)list}`),
      reaches_end);
  thm layout = match_mp_rule(match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `index:int`),
        cm_parameter_clear_layout_last), function_wf),
      index_lower), reaches_end);
  thm remaining = conjunct2_rule(layout);
  thm address_ready = match_mp_rule(match_mp_rule(
      match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `fp:int`, `oldfp:int`,
        `index:int`), cm_parameter_address_ready),
        function_wf), segment), index_lower), index_upper);
  thm address_is_signed = conjunct1_rule(
      conjunct2_rule(conjunct2_rule(address_ready)));
  thm pointer_number = match_mp_rule(match_mp_rule(
      match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `st:cm_src_state`,
        `old:(cm_region)list`, `oldenv:int->int->cm_value`,
        `gen:int`, `fp:int`, `index:int`),
        cm_parameter_pointer_number), context),
      index_lower), index_upper), address_is_signed);
  thm cleared_equal = beta_norm(ap_term_rule(
      `\amount:int.
         cm_state_clear_range (st:cm_src_state)
           ${current_base:int} amount`,
      remaining));
  thm stored_equal = beta_norm(ap_term_rule(
      `\base:cm_src_state.
         cm_state_store ${ty:cm_type} ${ptr:cm_value}
           (stored:cm_value) base`,
      cleared_equal));
  thm absorbed = match_mp_rule(specl_rule(TERM_LIST(
      ty, ptr, `stored:cm_value`, `st:cm_src_state`,
      current_base), get_cm_state_store_absorb_clear()),
      pointer_number);
  thm result = trans_rule(stored_equal, absorbed);
  thm_list normalization = get_cm_state_core_defs();
  vector_add(&normalization, get_cm_state_clear_range_def());
  vector_add(&normalization, get_cm_parameter_state_store_def());
  thm normalized_result = conv_rule(
      reduce_rewrite_conv(normalization), result);
  thm target_view = apply_conversion(
      reduce_rewrite_conv(normalization), goal_ccl(leaf->g));
  ACCEPT_TAC(leaf,
      eq_mp_rule(gsym_rule(target_view), normalized_result));
  return gnode_prove(root);
}
PROOF static thm cm_parameter_store_last_clear =
    cm_prove_parameter_store_last_clear();


PROOF static thm cm_prove_ilength_nonempty_positive(void) {
  gnode root = gnode_new_with_ccl(
      `!(values:(cm_value)list).
         ~(values == []) ==> 0i < ilength values`);
  gnode_list cases = INDUCT_TAC(root, `values:(cm_value)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm none = assume_rule(
        `~(([]:(cm_value)list) == [])`);
    CONTR_TAC(leaf, contra(none,
        refl_rule(`[]:(cm_value)list`)));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm tail_nonnegative = ispec_rule(
        `a1:(cm_value)list`,
        get_theorem_by_name("ILENGTH_NONNEG"));
    thm cons_length = apply_conversion(
        rewrite_conv(THM_LIST(
          get_theorem_by_name("ILENGTH_DEF"))),
        `ilength ((a0:cm_value) :: (a1:(cm_value)list))`);
    ACCEPT_TAC(leaf, mp_rule(mp_rule(int_arith_rule(
        mk_imp(concl(tail_nonnegative),
          mk_imp(concl(cons_length),
            `0i <
             ilength
               ((a0:cm_value) :: (a1:(cm_value)list))`))),
        tail_nonnegative), cons_length));
  }
  return gnode_prove(root);
}
PROOF static thm cm_ilength_nonempty_positive =
    cm_prove_ilength_nonempty_positive();


PROOF static thm cm_prove_store_params_absorb_clear(void) {
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
           ~(values == []) ==>
           index + ilength values ==
             ilength
               (cm_function_params
                 (inth fid (cm_program_functions p))) ==>
           cm_store_params p fid values index
             (cm_state_clear_range st
               (fp + cm_param_offset p fid index)
               (cm_slots_size (cm_program_structs p)
                   (cm_function_params
                     (inth fid (cm_program_functions p))) -
                 cm_slots_prefix (cm_program_structs p)
                   (cm_function_params
                     (inth fid (cm_program_functions p)))
                   index)) ==
           cm_store_params p fid values index st`);
  gnode_list cases = INDUCT_TAC(root, `values:(cm_value)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm none = assume_rule(
        `~(([]:(cm_value)list) == [])`);
    CONTR_TAC(leaf, contra(none,
        refl_rule(`[]:(cm_value)list`)));
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
    thm index_lower = assume_rule(`0i <= (index:int)`);
    thm total = assume_rule(
        `(index:int) + ilength
          ((a0:cm_value) :: (a1:(cm_value)list)) ==
         ilength ${params:(cm_slot_d)list}`);
    thm cons_length = apply_conversion(
        rewrite_conv(THM_LIST(
          get_theorem_by_name("ILENGTH_DEF"))),
        `ilength ((a0:cm_value) :: (a1:(cm_value)list))`);
    thm next_lower = mp_rule(int_arith_rule(
        `0i <= (index:int) ==> 0i <= index + 1i`),
        index_lower);
    gnode_list rest_cases = BOOL_CASES_TAC(
        leaf, `(a1:(cm_value)list) == []`, "Hrest_nil");
    {
      thm rest_nil = assume_rule(
          `(a1:(cm_value)list) == []`);
      thm rest_length = beta_norm(ap_term_rule(
          `\xs:(cm_value)list. ilength xs`, rest_nil));
      thm rest_zero = trans_rule(rest_length,
          apply_conversion(rewrite_conv(THM_LIST(
            get_theorem_by_name("ILENGTH_DEF"))),
            `ilength ([]:(cm_value)list)`));
      thm reaches_end = mp_rule(mp_rule(mp_rule(
          int_arith_rule(mk_imp(concl(total),
            mk_imp(concl(cons_length),
              mk_imp(concl(rest_zero),
                `(index:int) + 1i ==
                 ilength ${params:(cm_slot_d)list}`)))),
          total), cons_length), rest_zero);
      thm last_store = specl_rule(TERM_LIST(
          `p:cm_program`, `fid:int`, `a0:cm_value`,
          `st:cm_src_state`, `old:(cm_region)list`,
          `oldenv:int->int->cm_value`, `gen:int`, `fp:int`,
          `oldfp:int`, `index:int`),
          cm_parameter_store_last_clear);
      last_store = match_mp_rule(last_store, function_wf);
      last_store = match_mp_rule(last_store, segment);
      last_store = match_mp_rule(last_store, context);
      last_store = match_mp_rule(last_store, index_lower);
      last_store = match_mp_rule(last_store, reaches_end);
      thm_list rules = THM_LIST(
          get_cm_store_params_def(),
          get_cm_parameter_state_store_def(), rest_nil);
      thm normalized = conv_rule(
          reduce_rewrite_conv(rules), last_store);
      thm target_view = apply_conversion(
          reduce_rewrite_conv(rules),
          goal_ccl(rest_cases[0]->g));
      ACCEPT_TAC(rest_cases[0],
          eq_mp_rule(gsym_rule(target_view), normalized));
    }
    {
      thm rest_nonempty = assume_rule(
          `~((a1:(cm_value)list) == [])`);
      thm rest_positive = match_mp_rule(
          spec_rule(`a1:(cm_value)list`,
            cm_ilength_nonempty_positive),
          rest_nonempty);
      thm next_upper = mp_rule(mp_rule(mp_rule(
          int_arith_rule(mk_imp(concl(total),
            mk_imp(concl(cons_length),
              mk_imp(concl(rest_positive),
                `(index:int) + 1i <
                 ilength ${params:(cm_slot_d)list}`)))),
          total), cons_length), rest_positive);
      thm tail_total = mp_rule(mp_rule(
          int_arith_rule(mk_imp(concl(total),
            mk_imp(concl(cons_length),
              `((index:int) + 1i) +
                 ilength (a1:(cm_value)list) ==
               ilength ${params:(cm_slot_d)list}`))),
          total), cons_length);
      thm split_store = specl_rule(TERM_LIST(
          `p:cm_program`, `fid:int`, `a0:cm_value`,
          `st:cm_src_state`, `old:(cm_region)list`,
          `oldenv:int->int->cm_value`, `gen:int`, `fp:int`,
          `oldfp:int`, `index:int`),
          cm_parameter_store_split_clear);
      split_store = match_mp_rule(split_store, function_wf);
      split_store = match_mp_rule(split_store, segment);
      split_store = match_mp_rule(split_store, context);
      split_store = match_mp_rule(split_store, index_lower);
      split_store = match_mp_rule(split_store, next_upper);
      thm next_context = match_mp_rule(specl_rule(TERM_LIST(
          `p:cm_program`, `fid:int`, `index:int`,
          `a0:cm_value`, `st:cm_src_state`,
          `old:(cm_region)list`,
          `oldenv:int->int->cm_value`, `gen:int`, `fp:int`),
          cm_param_store_context_store), context);
      thm ih = specl_rule(TERM_LIST(
          `p:cm_program`, `fid:int`, next_state,
          `old:(cm_region)list`, `oldenv:int->int->cm_value`,
          `gen:int`, `fp:int`, `oldfp:int`,
          `(index:int) + 1i`),
          assume_rule(goal_lasmps(rest_cases[1]->g)[0].tm));
      ih = match_mp_rule(ih, function_wf);
      ih = match_mp_rule(ih, segment);
      ih = match_mp_rule(ih, next_context);
      ih = match_mp_rule(ih, next_lower);
      ih = match_mp_rule(ih, rest_nonempty);
      ih = match_mp_rule(ih, tail_total);
      thm lifted = beta_norm(ap_term_rule(
          `\base:cm_src_state.
             cm_store_params (p:cm_program) (fid:int)
               (a1:(cm_value)list) ((index:int) + 1i) base`,
          split_store));
      thm result = trans_rule(lifted, ih);
      thm_list rules = THM_LIST(
          get_cm_store_params_def(),
          get_cm_parameter_state_store_def());
      thm normalized = conv_rule(
          reduce_rewrite_conv(rules), result);
      thm target_view = apply_conversion(
          reduce_rewrite_conv(rules),
          goal_ccl(rest_cases[1]->g));
      ACCEPT_TAC(rest_cases[1],
          eq_mp_rule(gsym_rule(target_view), normalized));
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_store_params_absorb_clear =
    cm_prove_store_params_absorb_clear();

PROOF thm get_cm_store_params_absorb_clear(void) {
  return cm_store_params_absorb_clear;
}


PROOF static thm cm_prove_call_pending_clear_relation(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (st:cm_src_state).
         cm_call_pending_base p fid st ==
         cm_state_clear_range (cm_call_base_state p fid st)
           (cm_state_fp st -
             cm_frame_size (cm_program_structs p)
               (inth fid (cm_program_functions p)) + 8i)
           (cm_call_param_span p fid)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm_list rules = get_cm_state_core_defs();
  vector_add(&rules, get_cm_call_pending_base_def());
  vector_add(&rules, get_cm_call_base_state_def());
  vector_add(&rules, get_cm_state_clear_range_def());
  CONV_TAC(leaf, reduce_rewrite_conv(rules));
  return gnode_prove(root);
}
PROOF static thm cm_call_pending_clear_relation =
    cm_prove_call_pending_clear_relation();

PROOF static thm cm_prove_call_base_param_context(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (st:cm_src_state).
         cm_regions_before (cm_state_regions st)
           (cm_state_nextgen st) ==>
         cm_param_store_context p fid
           (cm_call_base_state p fid st)
           (cm_state_regions st) (cm_state_env st)
           (cm_state_nextgen st)
           (cm_state_fp st -
             cm_frame_size (cm_program_structs p)
               (inth fid (cm_program_functions p)))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm before = assume_rule(
      `cm_regions_before
        (cm_state_regions (st:cm_src_state))
        (cm_state_nextgen st)`);
  thm_list rules = get_cm_state_core_defs();
  vector_add(&rules, get_cm_call_base_state_def());
  vector_add(&rules, get_cm_param_store_context_def());
  gnode reduced = CONV_TAC(leaf, reduce_rewrite_conv(rules));
  if (IS_NULL(reduced->solved)) {
    ACCEPT_TAC(reduced, before);
  }
  return gnode_prove(root);
}
PROOF static thm cm_call_base_param_context =
    cm_prove_call_base_param_context();

PROOF static thm cm_prove_call_pending_param_context(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (st:cm_src_state).
         cm_regions_before (cm_state_regions st)
           (cm_state_nextgen st) ==>
         cm_param_store_context p fid
           (cm_call_pending_base p fid st)
           (cm_state_regions st) (cm_state_env st)
           (cm_state_nextgen st)
           (cm_state_fp st -
             cm_frame_size (cm_program_structs p)
               (inth fid (cm_program_functions p)))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm before = assume_rule(
      `cm_regions_before
        (cm_state_regions (st:cm_src_state))
        (cm_state_nextgen st)`);
  thm_list rules = get_cm_state_core_defs();
  vector_add(&rules, get_cm_call_pending_base_def());
  vector_add(&rules, get_cm_param_store_context_def());
  gnode reduced = CONV_TAC(leaf, reduce_rewrite_conv(rules));
  if (IS_NULL(reduced->solved)) {
    ACCEPT_TAC(reduced, before);
  }
  return gnode_prove(root);
}
PROOF static thm cm_call_pending_param_context =
    cm_prove_call_pending_param_context();


PROOF static thm cm_prove_clear_init_zero(void) {
  gnode root_node = gnode_new_with_ccl(
      `!(old:int->bool) (base:int).
         cm_clear_init old base 0i == old`);
  gnode leaf = CONV_TAC(root_node, rewrite_conv(THM_LIST(
      get_cm_clear_init_def(), get_theorem_by_name("FUN_EQ_THM"))));
  gnode point = AUTO_INTROS_TAC(leaf);
  thm no_empty = int_arith_rule(
      `!x (base:int). ~(base <= x && x < base + 0i)`);
  CONV_TAC(point, reduce_rewrite_conv(THM_LIST(no_empty)));
  return gnode_prove(root_node);
}
PROOF static thm cm_clear_init_zero =
    cm_prove_clear_init_zero();

PROOF static thm cm_prove_clear_tagged_zero(void) {
  gnode root_node = gnode_new_with_ccl(
      `!(old:int->bool) (base:int).
         cm_clear_tagged old base 0i == old`);
  gnode leaf = CONV_TAC(root_node, rewrite_conv(THM_LIST(
      get_cm_clear_tagged_def(), get_theorem_by_name("FUN_EQ_THM"))));
  gnode point = AUTO_INTROS_TAC(leaf);
  CONV_TAC(point, reduce_rewrite_conv(THM_LIST()));
  return gnode_prove(root_node);
}
PROOF static thm cm_clear_tagged_zero =
    cm_prove_clear_tagged_zero();

PROOF static thm cm_prove_slot_list_ilength_zero(void) {
  gnode root_node = gnode_new_with_ccl(
      `!(slots:(cm_slot_d)list).
         ilength slots == 0i ==> slots == []`);
  gnode_list cases =
      INDUCT_TAC(root_node, `slots:(cm_slot_d)list`);
  CONV_TAC(AUTO_INTROS_TAC(cases[0]),
      reduce_rewrite_conv(THM_LIST()));
  gnode cons = AUTO_INTROS_TAC(cases[1]);
  thm length_step = conv_rule(rewrite_conv(THM_LIST(
      get_theorem_by_name("ILENGTH_DEF"))), assume_rule(
        `ilength ((a0:cm_slot_d) :: (a1:(cm_slot_d)list)) == 0i`));
  thm tail_nonnegative = ispec_rule(
      `a1:(cm_slot_d)list`,
      get_theorem_by_name("ILENGTH_NONNEG"));
  CONTR_TAC(cons, mp_rule(mp_rule(int_arith_rule(
      `1i + ilength (a1:(cm_slot_d)list) == 0i ==>
       0i <= ilength a1 ==> F`),
      length_step), tail_nonnegative));
  return gnode_prove(root_node);
}
PROOF static thm cm_slot_list_ilength_zero =
    cm_prove_slot_list_ilength_zero();

PROOF static thm cm_prove_pending_params_enter_call_nil(void) {
  gnode root_node = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (st:cm_src_state).
         cm_function_params
           (inth fid (cm_program_functions p)) == [] ==>
         cm_store_params_reverse p fid [] 0i
           (cm_call_pending_base p fid st) ==
         cm_enter_call p fid [] st`);
  gnode leaf = AUTO_INTROS_TAC(root_node);
  thm_list rules = get_cm_state_core_defs();
  vector_add(&rules, get_cm_store_params_reverse_def());
  vector_add(&rules, get_cm_enter_call_def());
  vector_add(&rules, get_cm_store_params_def());
  vector_add(&rules, get_cm_call_pending_base_def());
  vector_add(&rules, get_cm_call_param_span_def());
  vector_add(&rules, get_cm_call_base_state_def());
  vector_add(&rules, get_cm_regions_for_slots_def());
  vector_add(&rules, cm_clear_init_zero);
  vector_add(&rules, cm_clear_tagged_zero);
  vector_add(&rules, get_theorem_by_name("ILENGTH_DEF"));
  vector_add(&rules, get_theorem_by_name("APPEND"));
  vector_add(&rules, get_cm_slots_size_def());
  vector_add(&rules, assume_rule(
      `cm_function_params
        (inth (fid:int) (cm_program_functions (p:cm_program))) == []`));
  thm normalized = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(rules), goal_ccl(leaf->g)));
  ACCEPT_TAC(leaf, normalized);
  return gnode_prove(root_node);
}
PROOF static thm cm_pending_params_enter_call_nil =
    cm_prove_pending_params_enter_call_nil();

PROOF static thm cm_prove_pending_params_enter_call(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (values:(cm_value)list)
         (st:cm_src_state).
         cm_function_wf p
           (inth fid (cm_program_functions p)) ==>
         cm_frame_segment p fid
           (cm_state_fp st -
             cm_frame_size (cm_program_structs p)
               (inth fid (cm_program_functions p)))
           (cm_state_fp st) ==>
         cm_regions_before (cm_state_regions st)
           (cm_state_nextgen st) ==>
         ~(values == []) ==>
         ilength values ==
           ilength
             (cm_function_params
               (inth fid (cm_program_functions p))) ==>
         cm_store_params_reverse p fid values 0i
           (cm_call_pending_base p fid st) ==
         cm_enter_call p fid values st`);
  gnode leaf = AUTO_INTROS_TAC(root);
  term params =
      `cm_function_params
        (inth (fid:int) (cm_program_functions (p:cm_program)))`;
  term newfp =
      `cm_state_fp (st:cm_src_state) -
       cm_frame_size (cm_program_structs (p:cm_program))
         (inth (fid:int) (cm_program_functions p))`;
  term base_state =
      `cm_call_base_state
        (p:cm_program) (fid:int) (st:cm_src_state)`;
  term pending_state =
      `cm_call_pending_base
        (p:cm_program) (fid:int) (st:cm_src_state)`;
  thm function_wf = assume_rule(
      `cm_function_wf (p:cm_program)
        (inth (fid:int) (cm_program_functions p))`);
  thm segment = assume_rule(
      `cm_frame_segment (p:cm_program) (fid:int)
        ${newfp:int} (cm_state_fp (st:cm_src_state))`);
  thm before = assume_rule(
      `cm_regions_before
        (cm_state_regions (st:cm_src_state))
        (cm_state_nextgen st)`);
  thm nonempty = assume_rule(
      `~((values:(cm_value)list) == [])`);
  thm arity = assume_rule(
      `ilength (values:(cm_value)list) ==
       ilength ${params:(cm_slot_d)list}`);
  thm base_context = match_mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`),
      cm_call_base_param_context), before);
  thm pending_context = match_mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`),
      cm_call_pending_param_context), before);
  thm total_bound = mp_rule(int_arith_rule(
      `ilength (values:(cm_value)list) ==
         ilength ${params:(cm_slot_d)list} ==>
       0i + ilength values <= ilength ${params:(cm_slot_d)list}`),
      arity);
  thm total_exact = mp_rule(int_arith_rule(
      `ilength (values:(cm_value)list) ==
         ilength ${params:(cm_slot_d)list} ==>
       0i + ilength values == ilength ${params:(cm_slot_d)list}`),
      arity);
  thm reverse_forward = specl_rule(TERM_LIST(
      `values:(cm_value)list`, `p:cm_program`, `fid:int`,
      pending_state, `cm_state_regions (st:cm_src_state)`,
      `cm_state_env (st:cm_src_state)`,
      `cm_state_nextgen (st:cm_src_state)`, newfp,
      `cm_state_fp (st:cm_src_state)`, `0i:int`),
      cm_store_params_reverse_forward);
  reverse_forward = match_mp_rule(reverse_forward, function_wf);
  reverse_forward = match_mp_rule(reverse_forward, segment);
  reverse_forward = match_mp_rule(
      reverse_forward, pending_context);
  reverse_forward = match_mp_rule(reverse_forward,
      int_arith_rule(`0i <= 0i`));
  reverse_forward = match_mp_rule(
      reverse_forward, total_bound);
  thm pending_relation = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `st:cm_src_state`),
      cm_call_pending_clear_relation);
  term pending_exact =
      `${pending_state:cm_src_state} ==
       cm_state_clear_range ${base_state:cm_src_state}
         (${newfp:int} + cm_param_offset
           (p:cm_program) (fid:int) 0i)
         (cm_slots_size (cm_program_structs (p:cm_program))
             ${params:(cm_slot_d)list} -
           cm_slots_prefix (cm_program_structs p)
             ${params:(cm_slot_d)list} 0i)`;
  thm_list bridge_rules = THM_LIST(
      get_cm_call_param_span_def(), get_cm_param_offset_def(),
      cm_slots_prefix_zero_complete,
      int_ring_rule(`!z:int. z + 0i == z`),
      int_ring_rule(`!z:int. z - 0i == z`));
  thm normalized_pending = conv_rule(
      reduce_rewrite_conv(bridge_rules), pending_relation);
  thm pending_view = apply_conversion(
      reduce_rewrite_conv(bridge_rules), pending_exact);
  thm pending_exact_proof = eq_mp_rule(
      gsym_rule(pending_view), normalized_pending);
  thm pending_lift = beta_norm(ap_term_rule(
      `\base:cm_src_state.
         cm_store_params (p:cm_program) (fid:int)
           (values:(cm_value)list) 0i base`,
      pending_exact_proof));
  thm absorbed = specl_rule(TERM_LIST(
      `values:(cm_value)list`, `p:cm_program`, `fid:int`,
      base_state, `cm_state_regions (st:cm_src_state)`,
      `cm_state_env (st:cm_src_state)`,
      `cm_state_nextgen (st:cm_src_state)`, newfp,
      `cm_state_fp (st:cm_src_state)`, `0i:int`),
      cm_store_params_absorb_clear);
  absorbed = match_mp_rule(absorbed, function_wf);
  absorbed = match_mp_rule(absorbed, segment);
  absorbed = match_mp_rule(absorbed, base_context);
  absorbed = match_mp_rule(absorbed,
      int_arith_rule(`0i <= 0i`));
  absorbed = match_mp_rule(absorbed, nonempty);
  absorbed = match_mp_rule(absorbed, total_exact);
  thm enter = get_cm_enter_call_def();
  ACCEPT_TAC(leaf, trans_rule(reverse_forward,
      trans_rule(pending_lift,
        trans_rule(absorbed, gsym_rule(enter)))));
  return gnode_prove(root);
}
PROOF static thm cm_pending_params_enter_call_nonempty =
    cm_prove_pending_params_enter_call();

PROOF static thm cm_prove_pending_params_enter_call_total(void) {
  term params =
      `cm_function_params
        (inth (fid:int) (cm_program_functions (p:cm_program)))`;
  term frame_base =
      `cm_state_fp (st:cm_src_state) -
       cm_frame_size (cm_program_structs (p:cm_program))
         (inth (fid:int) (cm_program_functions p))`;
  term body = imp_chain(TERM_LIST(
      `cm_function_wf (p:cm_program)
        (inth (fid:int) (cm_program_functions p))`,
      `cm_frame_segment (p:cm_program) (fid:int)
        ${frame_base:int} (cm_state_fp (st:cm_src_state))`,
      `cm_regions_before (cm_state_regions (st:cm_src_state))
        (cm_state_nextgen st)`,
      `ilength (values:(cm_value)list) ==
       ilength ${params:(cm_slot_d)list}`),
      `cm_store_params_reverse (p:cm_program) (fid:int)
         (values:(cm_value)list) 0i
         (cm_call_pending_base p fid (st:cm_src_state)) ==
       cm_enter_call p fid values st`);
  gnode root_node = gnode_new_with_ccl(
      list_mk_forall(free_vars(body), body));
  gnode leaf = AUTO_INTROS_TAC(root_node);
  gnode_list cases = BOOL_CASES_TAC(
      leaf, `(values:(cm_value)list) == []`, "Hvalues_nil");
  {
    thm values_nil =
        assume_rule(`(values:(cm_value)list) == []`);
    thm arity = assume_rule(
        `ilength (values:(cm_value)list) ==
         ilength ${params:(cm_slot_d)list}`);
    thm params_zero = sym_rule(conv_rule(reduce_rewrite_conv(
        THM_LIST(values_nil, get_theorem_by_name("ILENGTH_DEF"))),
        arity));
    thm params_nil = match_mp_rule(
        spec_rule(params, cm_slot_list_ilength_zero), params_zero);
    thm result = match_mp_rule(specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `st:cm_src_state`),
        cm_pending_params_enter_call_nil), params_nil);
    thm target_view = apply_conversion(
        rewrite_conv(THM_LIST(values_nil)), goal_ccl(cases[0]->g));
    ACCEPT_TAC(cases[0], eq_mp_rule(sym_rule(target_view), result));
  }
  {
    thm result = specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `values:(cm_value)list`,
        `st:cm_src_state`), cm_pending_params_enter_call_nonempty);
    result = match_mp_rule(result, assume_rule(
        `cm_function_wf (p:cm_program)
          (inth (fid:int) (cm_program_functions p))`));
    result = match_mp_rule(result, assume_rule(
        `cm_frame_segment (p:cm_program) (fid:int)
          ${frame_base:int} (cm_state_fp (st:cm_src_state))`));
    result = match_mp_rule(result, assume_rule(
        `cm_regions_before (cm_state_regions (st:cm_src_state))
          (cm_state_nextgen st)`));
    result = match_mp_rule(result, assume_rule(
        `~((values:(cm_value)list) == [])`));
    result = match_mp_rule(result, assume_rule(
        `ilength (values:(cm_value)list) ==
         ilength ${params:(cm_slot_d)list}`));
    ACCEPT_TAC(cases[1], result);
  }
  return gnode_prove(root_node);
}
PROOF thm cm_pending_params_enter_call =
    cm_prove_pending_params_enter_call_total();

PROOF thm get_cm_pending_params_enter_call(void) {
  return cm_pending_params_enter_call;
}

PROOF static int cmc_preservation_call_params_complete_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_call_params_complete_axioms_before,
      "cmc_preservation_call_params_complete introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_call_params_complete_checks =
    cmc_preservation_call_params_complete_final_checks();
