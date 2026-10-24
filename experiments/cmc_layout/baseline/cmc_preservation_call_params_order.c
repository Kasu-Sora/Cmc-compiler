#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_call_params_order.h"

#require "cmc_preservation_call_finish.c"
PROOF extern thm cm_call_env_def;


PROOF static size_t _cmc_preservation_call_params_order_axioms_before =
    vector_size(get_all_axioms());

PROOF thm cm_param_store_context_def = new_fun_definition(
    `cm_param_store_context (p:cm_program) (fid:int)
       (st:cm_src_state) (old:(cm_region)list)
       (oldenv:int->int->cm_value) (gen:int) (fp:int) : bool =
       (cm_regions_before old gen &&
        cm_state_env st == cm_call_env p fid oldenv fp gen &&
        cm_state_regions st ==
          cm_regions_for_slots (cm_program_structs p)
            (cm_function_params
              (inth fid (cm_program_functions p)))
            gen (fp + 8i) ++ old)`);
PROOF static int _e_cm_param_store_context =
    cst_add_const_to_header(`cm_param_store_context`);

PROOF thm cm_parameter_state_store_def = new_fun_definition(
    `cm_parameter_state_store (p:cm_program) (fid:int)
       (index:int) (stored:cm_value) (st:cm_src_state) : cm_src_state =
       cm_state_store
         (cm_slot_ty
           (inth index
             (cm_function_params
               (inth fid (cm_program_functions p)))))
         (cm_state_env st 2i index) stored st`);
PROOF static int _e_cm_parameter_state_store =
    cst_add_const_to_header(`cm_parameter_state_store`);

PROOF static thm cm_param_order_consequence(
    const thm premise, const term conclusion) {
  return mp_rule(taut_rule(mk_imp(concl(premise), conclusion)), premise);
}

PROOF static thm cm_prove_parameter_offsets_disjoint(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (left:int) right fp.
         cm_function_wf p (inth fid (cm_program_functions p)) ==>
         0i <= left ==> left < right ==>
         right < ilength
           (cm_function_params
             (inth fid (cm_program_functions p))) ==>
         cm_range_disjoint
           (fp + cm_param_offset p fid left)
           (cm_store_width
             (cm_slot_ty
               (inth left
                 (cm_function_params
                   (inth fid (cm_program_functions p))))))
           (fp + cm_param_offset p fid right)
           (cm_store_width
             (cm_slot_ty
               (inth right
                 (cm_function_params
                   (inth fid (cm_program_functions p))))))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  term params =
      `cm_function_params
        (inth (fid:int) (cm_program_functions (p:cm_program)))`;
  thm function_open = conv_rule(rewrite_conv(THM_LIST(
      get_cm_function_wf_def())), assume_rule(
        `cm_function_wf (p:cm_program)
          (inth (fid:int) (cm_program_functions p))`));
  thm params_wf = cm_param_order_consequence(function_open,
      `cm_params_wf (cm_program_structs (p:cm_program))
        ${params:(cm_slot_d)list}`);
  thm params_open = conv_rule(rewrite_conv(THM_LIST(
      get_cm_params_wf_def())), params_wf);
  thm slots_wf = conjunct1_rule(params_open);
  thm positive = match_mp_rule(specl_rule(TERM_LIST(
      `cm_program_structs (p:cm_program)`, params),
      cm_slots_wf_sizes_positive), slots_wf);
  thm left_lower = assume_rule(`0i <= (left:int)`);
  thm left_right = assume_rule(`(left:int) < (right:int)`);
  thm right_upper = assume_rule(
      `(right:int) < ilength ${params:(cm_slot_d)list}`);
  thm right_lower = mp_rule(mp_rule(int_arith_rule(
      `0i <= (left:int) ==> left < (right:int) ==> 0i <= right`),
      left_lower), left_right);
  thm slots_open = conv_rule(rewrite_conv(THM_LIST(
      get_cm_slots_wf_def())), slots_wf);
  thm left_upper = mp_rule(mp_rule(int_arith_rule(
      `(left:int) < (right:int) ==> right < ilength
        ${params:(cm_slot_d)list} ==>
        left < ilength ${params:(cm_slot_d)list}`),
      left_right), right_upper);
  thm left_wf = match_mp_rule(match_mp_rule(
      spec_rule(`left:int`, slots_open), left_lower), left_upper);
  thm right_wf = match_mp_rule(match_mp_rule(
      spec_rule(`right:int`, slots_open), right_lower), right_upper);
  thm counts = conjunct2_rule(params_open);
  thm left_count = match_mp_rule(match_mp_rule(
      spec_rule(`left:int`, counts), left_lower), left_upper);
  thm right_count = match_mp_rule(match_mp_rule(
      spec_rule(`right:int`, counts), right_lower), right_upper);
  thm left_scalar = cm_param_order_consequence(
      conv_rule(rewrite_conv(THM_LIST(get_cm_slot_wf_def())), left_wf),
      `cm_scalar_type (cm_program_structs (p:cm_program))
        (cm_slot_ty (inth (left:int) ${params:(cm_slot_d)list}))`);
  thm right_scalar = cm_param_order_consequence(
      conv_rule(rewrite_conv(THM_LIST(get_cm_slot_wf_def())), right_wf),
      `cm_scalar_type (cm_program_structs (p:cm_program))
        (cm_slot_ty (inth (right:int) ${params:(cm_slot_d)list}))`);
  thm left_shape = conjunct2_rule(mp_rule(specl_rule(TERM_LIST(
      `cm_slot_ty (inth (left:int) ${params:(cm_slot_d)list})`,
      `cm_program_structs (p:cm_program)`), cm_scalar_store_shape),
      left_scalar));
  thm right_shape = conjunct2_rule(mp_rule(specl_rule(TERM_LIST(
      `cm_slot_ty (inth (right:int) ${params:(cm_slot_d)list})`,
      `cm_program_structs (p:cm_program)`), cm_scalar_store_shape),
      right_scalar));
  thm left_size_width = by_rewrite(
      `cm_slot_size (cm_program_structs (p:cm_program))
         (inth (left:int) ${params:(cm_slot_d)list}) ==
       cm_store_width
         (cm_slot_ty (inth left ${params:(cm_slot_d)list}))`,
      THM_LIST(get_cm_slot_size_def(), left_count, left_shape));
  thm right_size_width = by_rewrite(
      `cm_slot_size (cm_program_structs (p:cm_program))
         (inth (right:int) ${params:(cm_slot_d)list}) ==
       cm_store_width
         (cm_slot_ty (inth right ${params:(cm_slot_d)list}))`,
      THM_LIST(get_cm_slot_size_def(), right_count, right_shape));
  thm cells = match_mp_rule(match_mp_rule(match_mp_rule(
      match_mp_rule(specl_rule(TERM_LIST(
        `cm_program_structs (p:cm_program)`, params),
        cm_slot_cells_disjoint), positive), left_lower), left_right),
      right_upper);
  cells = spec_rule(`(fp:int) + 8i`, cells);
  thm reassociate = int_ring_rule(
      `!(base:int) prefix. base + (8i + prefix) ==
         (base + 8i) + prefix`);
  thm normalized = conv_rule(reduce_rewrite_conv(THM_LIST(
      left_size_width, right_size_width, gsym_rule(reassociate),
      gsym_rule(get_cm_param_offset_def()))), cells);
  ACCEPT_TAC(leaf, normalized);
  return gnode_prove(root);
}
PROOF thm cm_parameter_offsets_disjoint =
    cm_prove_parameter_offsets_disjoint();

PROOF static thm cm_prove_parameter_pointer_number(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (st:cm_src_state)
         (old:(cm_region)list) (oldenv:int->int->cm_value)
         (gen:int) (fp:int) (index:int).
         cm_param_store_context p fid st old oldenv gen fp ==>
         0i <= index ==>
         index < ilength
           (cm_function_params
             (inth fid (cm_program_functions p))) ==>
         tower_signed64 (fp + cm_param_offset p fid index) ==>
         cm_value_number st (cm_state_env st 2i index) ==
         fp + cm_param_offset p fid index`);
  gnode leaf = AUTO_INTROS_TAC(root);
  term params =
      `cm_function_params
        (inth (fid:int) (cm_program_functions (p:cm_program)))`;
  term fresh =
      `cm_regions_for_slots (cm_program_structs (p:cm_program))
        ${params:(cm_slot_d)list} (gen:int) ((fp:int) + 8i)`;
  term region =
      `CMRegion ((gen:int) + (index:int))
        (((fp:int) + 8i) +
          cm_slots_prefix (cm_program_structs (p:cm_program))
            ${params:(cm_slot_d)list} (index:int))
        0i
        (cm_slot_size (cm_program_structs p)
          (inth index ${params:(cm_slot_d)list})) T T`;
  thm context = conv_rule(rewrite_conv(THM_LIST(
      cm_param_store_context_def)), assume_rule(
        `cm_param_store_context (p:cm_program) (fid:int)
          (st:cm_src_state) (old:(cm_region)list)
          (oldenv:int->int->cm_value) (gen:int) (fp:int)`));
  thm old_before = conjunct1_rule(context);
  thm env = conjunct1_rule(conjunct2_rule(context));
  thm regions = conjunct2_rule(conjunct2_rule(context));
  thm lower = assume_rule(`0i <= (index:int)`);
  thm upper = assume_rule(
      `(index:int) < ilength ${params:(cm_slot_d)list}`);
  thm member = mp_rule(mp_rule(specl_rule(TERM_LIST(
      params, `cm_program_structs (p:cm_program)`, `gen:int`,
      `(fp:int) + 8i`, `index:int`), cm_slot_region_index_member),
      lower), upper);
  thm lookup = mp_rule(mp_rule(specl_rule(TERM_LIST(
      `cm_program_structs (p:cm_program)`, params, `gen:int`,
      `(fp:int) + 8i`, `old:(cm_region)list`, region),
      cm_slot_region_base_lookup), old_before), member);
  lookup = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_region_gen_def(), get_cm_region_base_field_def())),
      lookup);
  thm wrap_fixed = mp_rule(
      spec_rule(`(fp:int) + cm_param_offset
        (p:cm_program) (fid:int) (index:int)`,
        get_tower_wrap64_fixed()),
      assume_rule(`tower_signed64
        ((fp:int) + cm_param_offset
          (p:cm_program) (fid:int) (index:int))`));
  thm address_eq = by_rewrite(
      `(((fp:int) + 8i) +
          cm_slots_prefix (cm_program_structs (p:cm_program))
            ${params:(cm_slot_d)list} (index:int)) + 0i ==
       fp + cm_param_offset p fid index`,
      THM_LIST(get_cm_param_offset_def(),
        int_ring_rule(
          `!(base:int) prefix. ((base + 8i) + prefix) + 0i ==
             base + (8i + prefix)`)));
  thm wrap_address = trans_rule(
      beta_norm(ap_term_rule(`tower_wrap64:int->int`, address_eq)),
      wrap_fixed);
  thm_list rules = THM_LIST(
      cm_param_store_context_def, env, regions,
      cm_call_env_def, get_cm_value_number_def(), lookup,
      get_cm_ptr_offset_def(), wrap_address,
      get_cm_param_offset_def(),
      int_ring_rule(
        `!(base:int) prefix. (base + 8i) + prefix + 0i ==
           base + (8i + prefix)`));
  gnode reduced =
      CONV_WITH_ASMP_TAC(leaf, reduce_rewrite_conv, rules);
  if (IS_NULL(reduced->solved)) {
    reduced = CONV_WITH_ASMP_TAC(
        reduced, reduce_rewrite_conv, rules);
  }
  if (IS_NULL(reduced->solved)) {
    ACCEPT_TAC(reduced, taut_rule(goal_ccl(reduced->g)));
  }
  return gnode_prove(root);
}
PROOF thm cm_parameter_pointer_number =
    cm_prove_parameter_pointer_number();

PROOF static thm cm_prove_param_store_context_store(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) index (stored:cm_value) st old oldenv gen fp.
         cm_param_store_context p fid st old oldenv gen fp ==>
         cm_param_store_context p fid
           (cm_parameter_state_store p fid index stored st)
           old oldenv gen fp`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm context = conv_rule(rewrite_conv(THM_LIST(
      cm_param_store_context_def)), assume_rule(
        `cm_param_store_context (p:cm_program) (fid:int)
          (st:cm_src_state) (old:(cm_region)list)
          (oldenv:int->int->cm_value) (gen:int) (fp:int)`));
  thm_list rules = get_cm_state_core_defs();
  vector_add(&rules, cm_param_store_context_def);
  vector_add(&rules, cm_parameter_state_store_def);
  vector_add(&rules, get_cm_state_store_def());
  gnode reduced =
      CONV_WITH_ASMP_TAC(leaf, reduce_rewrite_conv, rules);
  if (IS_NULL(reduced->solved)) {
    ACCEPT_TAC(reduced, context);
  }
  return gnode_prove(root);
}
PROOF thm cm_param_store_context_store =
    cm_prove_param_store_context_store();

PROOF thm get_cm_param_store_context_def(void) {
  return cm_param_store_context_def;
}
PROOF thm get_cm_parameter_state_store_def(void) {
  return cm_parameter_state_store_def;
}
PROOF thm get_cm_parameter_offsets_disjoint(void) {
  return cm_parameter_offsets_disjoint;
}
PROOF thm get_cm_parameter_pointer_number(void) {
  return cm_parameter_pointer_number;
}
PROOF thm get_cm_param_store_context_store(void) {
  return cm_param_store_context_store;
}

PROOF static int cmc_preservation_call_params_order_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_call_params_order_axioms_before,
      "cmc_preservation_call_params_order introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_call_params_order_checks =
    cmc_preservation_call_params_order_final_checks();
