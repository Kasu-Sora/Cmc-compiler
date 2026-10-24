#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_target_call_params.h"

#require "cmc_preservation_call_param.c"
#require "cmc_preservation_code_stmt.c"
#require "cmc_preservation_target_address.c"
#require "cmc_preservation_target_convert.c"
#require "cmc_preservation_target_store.c"

PROOF static size_t _cmc_preservation_target_call_params_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_call_params_consequence(
    const thm premise, const term conclusion) {
  return mp_rule(taut_rule(mk_imp(concl(premise), conclusion)), premise);
}

PROOF thm cm_param_indices_def = new_fun_definition(
    `cm_param_indices (full:(cm_slot_d)list) (index:int)
       (params:(cm_slot_d)list) : bool =
       (0i <= index &&
        index + ilength params <= ilength full &&
        (!j. 0i <= j ==> j < ilength params ==>
             inth j params == inth (index + j) full))`);
PROOF static int _e_cm_param_indices =
    cst_add_const_to_header(`cm_param_indices`);

PROOF static thm cm_prove_param_indices_refl(void) {
  gnode root = gnode_new_with_ccl(
      `!(slots:(cm_slot_d)list). cm_param_indices slots 0i slots`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm lower = int_arith_rule(`0i <= 0i`);
  thm upper = int_arith_rule(
      `0i + ilength (slots:(cm_slot_d)list) <= ilength slots`);
  thm jlower = assume_rule(`0i <= (j:int)`);
  thm jupper = assume_rule(
      `(j:int) < ilength (slots:(cm_slot_d)list)`);
  thm cell = by_rewrite(
      `inth (j:int) (slots:(cm_slot_d)list) ==
       inth (0i + j) slots`,
      THM_LIST(int_arith_rule(`!(x:int). 0i + x == x`)));
  thm cells = gen_rule(`j:int`, disch_rule(`0i <= (j:int)`,
      disch_rule(`(j:int) < ilength (slots:(cm_slot_d)list)`, cell)));
  thm body = conj_rule(lower, conj_rule(upper, cells));
  thm view = apply_conversion(rewrite_conv(THM_LIST(
      cm_param_indices_def)), goal_ccl(leaf->g));
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(view), body));
  return gnode_prove(root);
}
PROOF thm cm_param_indices_refl = cm_prove_param_indices_refl();

PROOF static thm cm_prove_param_indices_head(void) {
  gnode root = gnode_new_with_ccl(
      `!(full:(cm_slot_d)list) (index:int) (param:cm_slot_d)
         (rest:(cm_slot_d)list).
         cm_param_indices full index (param :: rest) ==>
         (0i <= index && index < ilength full &&
          param == inth index full)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm opened = conv_rule(rewrite_conv(THM_LIST(
      cm_param_indices_def)), assume_rule(
        `cm_param_indices (full:(cm_slot_d)list) (index:int)
          ((param:cm_slot_d) :: (rest:(cm_slot_d)list))`));
  thm lower = conjunct1_rule(opened);
  thm upper_sum = conjunct1_rule(conjunct2_rule(opened));
  thm cells = conjunct2_rule(conjunct2_rule(opened));
  thm rest_length_nonnegative = ispec_rule(
      `rest:(cm_slot_d)list`, get_theorem_by_name("ILENGTH_NONNEG"));
  thm upper_sum_normal = conv_rule(rewrite_conv(THM_LIST(
      get_theorem_by_name("ILENGTH_DEF"))), upper_sum);
  thm upper = mp_rule(mp_rule(int_arith_rule(
      `(index:int) + (1i + ilength (rest:(cm_slot_d)list)) <=
         ilength (full:(cm_slot_d)list) ==>
       0i <= ilength rest ==> index < ilength full`),
      upper_sum_normal), rest_length_nonnegative);
  thm zero_lower = int_arith_rule(`0i <= 0i`);
  thm zero_upper_raw = mp_rule(int_arith_rule(
      `0i <= ilength (rest:(cm_slot_d)list) ==>
       0i < 1i + ilength rest`), rest_length_nonnegative);
  thm zero_upper = eq_mp_rule(sym_rule(apply_conversion(
      rewrite_conv(THM_LIST(get_theorem_by_name("ILENGTH_DEF"))),
      `0i < ilength ((param:cm_slot_d) ::
        (rest:(cm_slot_d)list))`)), zero_upper_raw);
  thm cell = match_mp_rule(match_mp_rule(
      spec_rule(`0i`, cells), zero_lower), zero_upper);
  thm head_value = apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("INTH_DEF"),
        get_theorem_by_name("NUM_OF_INT_OF_NUM"),
        get_theorem_by_name("NTH_DEF"))),
      `inth 0i ((param:cm_slot_d) :: (rest:(cm_slot_d)list))`);
  thm index_zero = int_arith_rule(`(index:int) + 0i == index`);
  thm indexed_value = beta_norm(ap_term_rule(
      `\i:int. inth i (full:(cm_slot_d)list)`, index_zero));
  cell = trans_rule(sym_rule(head_value),
      trans_rule(cell, indexed_value));
  ACCEPT_TAC(leaf, conj_rule(lower, conj_rule(upper, cell)));
  return gnode_prove(root);
}
PROOF thm cm_param_indices_head = cm_prove_param_indices_head();

PROOF static thm cm_prove_param_indices_tail(void) {
  gnode root = gnode_new_with_ccl(
      `!(full:(cm_slot_d)list) (index:int) (param:cm_slot_d)
         (rest:(cm_slot_d)list).
         cm_param_indices full index (param :: rest) ==>
         cm_param_indices full (index + 1i) rest`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm opened = conv_rule(rewrite_conv(THM_LIST(
      cm_param_indices_def)), assume_rule(
        `cm_param_indices (full:(cm_slot_d)list) (index:int)
          ((param:cm_slot_d) :: (rest:(cm_slot_d)list))`));
  thm lower = conjunct1_rule(opened);
  thm upper_sum = conjunct1_rule(conjunct2_rule(opened));
  thm cells = conjunct2_rule(conjunct2_rule(opened));
  thm next_lower = mp_rule(int_arith_rule(
      `0i <= (index:int) ==> 0i <= index + 1i`), lower);
  thm upper_sum_normal = conv_rule(rewrite_conv(THM_LIST(
      get_theorem_by_name("ILENGTH_DEF"))), upper_sum);
  thm next_upper = mp_rule(int_arith_rule(
      `(index:int) + (1i + ilength (rest:(cm_slot_d)list)) <=
         ilength (full:(cm_slot_d)list) ==>
       (index + 1i) + ilength rest <= ilength full`),
      upper_sum_normal);

  thm jlower = assume_rule(`0i <= (j:int)`);
  thm jupper = assume_rule(
      `(j:int) < ilength (rest:(cm_slot_d)list)`);
  thm succ_lower = mp_rule(int_arith_rule(
      `0i <= (j:int) ==> 0i <= j + 1i`), jlower);
  thm succ_upper_raw = mp_rule(int_arith_rule(
      `(j:int) < ilength (rest:(cm_slot_d)list) ==>
       j + 1i < 1i + ilength rest`), jupper);
  thm succ_upper = eq_mp_rule(sym_rule(apply_conversion(
      rewrite_conv(THM_LIST(get_theorem_by_name("ILENGTH_DEF"))),
      `(j:int) + 1i <
       ilength ((param:cm_slot_d) :: (rest:(cm_slot_d)list))`)),
      succ_upper_raw);
  thm cell = match_mp_rule(match_mp_rule(
      spec_rule(`(j:int) + 1i`, cells), succ_lower), succ_upper);
  thm one_nonnegative = int_arith_rule(`0i <= 1i`);
  thm num_add = mp_rule(specl_rule(TERM_LIST(
      `j:int`, `1i:int`), get_theorem_by_name("NUM_OF_INT_ADD")),
      conj_rule(jlower, one_nonnegative));
  thm shift = by_rewrite(
      `inth ((j:int) + 1i)
         ((param:cm_slot_d) :: (rest:(cm_slot_d)list)) ==
       inth j rest`,
      THM_LIST(get_theorem_by_name("INTH_DEF"), num_add,
        get_theorem_by_name("NUM_OF_INT_OF_NUM"),
        sym_rule(spec_rule(`num_of_int (j:int)`,
          get_theorem_by_name("ADD1"))),
        get_theorem_by_name("NTH_DEF")));
  thm ordered = int_ring_rule(
      `(index:int) + (j + 1i) == (index + 1i) + j`);
  cell = conv_rule(rewrite_conv(THM_LIST(shift, ordered)), cell);
  thm tail_cells = gen_rule(`j:int`, disch_rule(`0i <= (j:int)`,
      disch_rule(`(j:int) < ilength (rest:(cm_slot_d)list)`, cell)));
  thm body = conj_rule(next_lower, conj_rule(next_upper, tail_cells));
  thm view = apply_conversion(rewrite_conv(THM_LIST(
      cm_param_indices_def)), goal_ccl(leaf->g));
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(view), body));
  return gnode_prove(root);
}
PROOF thm cm_param_indices_tail = cm_prove_param_indices_tail();

PROOF static thm cm_prove_store_params_reverse_env(void) {
  gnode root = gnode_new_with_ccl(
      `!(values:(cm_value)list).
         !(p:cm_program) (fid:int) (index:int) (st:cm_src_state).
        cm_state_env (cm_store_params_reverse p fid values index st) ==
         cm_state_env st`);
  gnode_list cases = INDUCT_TAC(root, `values:(cm_value)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
      cm_store_params_reverse_def)));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm ih = specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `(index:int) + 1i`,
        `st:cm_src_state`), assume_rule(goal_lasmps(leaf->g)[0].tm));
    term tail_state =
        `cm_store_params_reverse (p:cm_program) (fid:int)
          (a1:(cm_value)list) ((index:int) + 1i)
          (st:cm_src_state)`;
    term stored_state =
        `cm_state_store
          (cm_slot_ty (inth (index:int)
            (cm_function_params
              (inth (fid:int) (cm_program_functions p)))))
          (cm_state_env ${tail_state:cm_src_state} 2i (index:int))
          (a0:cm_value) ${tail_state:cm_src_state}`;
    thm_list state_rules = get_cm_state_core_defs();
    vector_add(&state_rules, get_cm_state_store_def());
    thm stored_env = apply_conversion(
        reduce_rewrite_conv(state_rules),
        `cm_state_env ${stored_state:cm_src_state}`);
    thm normalized = trans_rule(stored_env, ih);
    thm view = apply_conversion(rewrite_conv(THM_LIST(
        cm_store_params_reverse_def)), goal_ccl(leaf->g));
    ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(view), normalized));
  }
  return gnode_prove(root);
}
PROOF thm cm_store_params_reverse_env =
    cm_prove_store_params_reverse_env();

PROOF static thm cm_prove_store_params_reverse_runtime(void) {
  gnode root = gnode_new_with_ccl(
      `!(values:(cm_value)list).
         !(p:cm_program) (fid:int) (index:int) (st:cm_src_state)
           (calls:(cm_call_sim_frame)list)
           (frames:(cm_spill_frame)list).
         cm_runtime_memory_layout p st calls frames ==>
         cm_runtime_memory_layout p
           (cm_store_params_reverse p fid values index st)
           calls frames`);
  gnode_list cases = INDUCT_TAC(root, `values:(cm_value)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm layout = assume_rule(
        `cm_runtime_memory_layout (p:cm_program) (st:cm_src_state)
          (calls:(cm_call_sim_frame)list)
          (frames:(cm_spill_frame)list)`);
    thm view = apply_conversion(rewrite_conv(THM_LIST(
        cm_store_params_reverse_def)), goal_ccl(leaf->g));
    ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(view), layout));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    term tail_state =
        `cm_store_params_reverse (p:cm_program) (fid:int)
          (a1:(cm_value)list) ((index:int) + 1i)
          (st:cm_src_state)`;
    thm tail_layout = mp_rule(specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `(index:int) + 1i`,
        `st:cm_src_state`, `calls:(cm_call_sim_frame)list`,
        `frames:(cm_spill_frame)list`),
        assume_rule(goal_lasmps(leaf->g)[0].tm)), assume_rule(
          `cm_runtime_memory_layout (p:cm_program) (st:cm_src_state)
            (calls:(cm_call_sim_frame)list)
            (frames:(cm_spill_frame)list)`));
    thm stored = mp_rule(specl_rule(TERM_LIST(
        `p:cm_program`,
        `cm_slot_ty (inth (index:int)
          (cm_function_params
            (inth (fid:int) (cm_program_functions p))))`,
        `cm_state_env ${tail_state:cm_src_state} 2i (index:int)`,
        `a0:cm_value`, tail_state,
        `calls:(cm_call_sim_frame)list`,
        `frames:(cm_spill_frame)list`), cm_store_runtime_layout),
        tail_layout);
    thm view = apply_conversion(rewrite_conv(THM_LIST(
        cm_store_params_reverse_def)), goal_ccl(leaf->g));
    ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(view), stored));
  }
  return gnode_prove(root);
}
PROOF thm cm_store_params_reverse_runtime =
    cm_prove_store_params_reverse_runtime();

PROOF static thm cm_prove_call_params_code_steps_append(void) {
  gnode root = gnode_new_with_ccl(
      `!(left:(tvm_inst)list) (right:(tvm_inst)list).
         cm_code_steps (left ++ right) ==
         cm_code_steps left + cm_code_steps right`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm left_nonnegative = ispec_rule(
      `left:(tvm_inst)list`, get_theorem_by_name("ILENGTH_NONNEG"));
  thm right_nonnegative = ispec_rule(
      `right:(tvm_inst)list`, get_theorem_by_name("ILENGTH_NONNEG"));
  thm sum = mp_rule(specl_rule(TERM_LIST(
      `ilength (left:(tvm_inst)list)`,
      `ilength (right:(tvm_inst)list)`),
      get_theorem_by_name("NUM_OF_INT_ADD")),
      conj_rule(left_nonnegative, right_nonnegative));
  CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
      cm_code_steps_def, get_theorem_by_name("ILENGTH_APPEND"), sum)));
  return gnode_prove(root);
}
PROOF static thm cm_call_params_code_steps_append =
    cm_prove_call_params_code_steps_append();

PROOF static thm cm_prove_call_params_ann_linear_append(void) {
  gnode root = gnode_new_with_ccl(
      `!(left:(tvm_inst)list) (right:(tvm_inst)list)
         (ann:cm_annotation).
         cm_ann_linear (left ++ right) ann ==
         cm_ann_linear right (cm_ann_linear left ann)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode reduced = CONV_WITH_ASMP_TAC(
      leaf, reduce_rewrite_conv, THM_LIST(
        cm_ann_linear_def, cm_ann_plain_def,
        cm_ann_pc_def, cm_ann_temp_def, cm_ann_break_def,
        cm_ann_continue_def, cm_ann_cursors_def,
        cm_ann_spills_def, cm_ann_saved_def, cm_ann_calls_def,
        get_theorem_by_name("ILENGTH_APPEND")));
  thm pc_order = int_ring_rule(
      `(cm_ann_pc (ann:cm_annotation) +
          (ilength (left:(tvm_inst)list) +
           ilength (right:(tvm_inst)list))) ==
       (cm_ann_pc ann + ilength left) + ilength right`);
  gnode ordered = CONV_WITH_ASMP_TAC(
      reduced, once_rewrite_conv, THM_LIST(pc_order));
  if (IS_NULL(ordered->solved)) {
    ACCEPT_TAC(ordered, refl_rule(dest_eq(goal_ccl(ordered->g)).tm1));
  }
  return gnode_prove(root);
}
PROOF static thm cm_call_params_ann_linear_append =
    cm_prove_call_params_ann_linear_append();

PROOF static thm cm_call_params_code_suffix(
    const thm current_code, const term code,
    const term current_ann, const term prefix,
    const term suffix, const term next_ann,
    const thm_list rules) {
  thm current_normal =
      conv_rule(reduce_rewrite_conv(rules), current_code);
  thm tail_rule = ispecl_rule(TERM_LIST(
      code, `cm_ann_pc ${current_ann:cm_annotation}`,
      prefix, suffix), get_cm_code_at_append_right());
  thm tail_raw = mp_rule(
      conv_rule(reduce_rewrite_conv(rules), tail_rule),
      current_normal);
  thm tail_normal =
      conv_rule(reduce_rewrite_conv(rules), tail_raw);
  thm tail_view = apply_conversion(
      reduce_rewrite_conv(rules),
      `cm_code_at ${code:(tvm_inst)list}
        (cm_ann_pc ${next_ann:cm_annotation})
        ${suffix:(tvm_inst)list}`);
  return eq_mp_rule(sym_rule(tail_view), tail_normal);
}
PROOF static thm cm_prove_call_params_ilength_zero(void) {
  gnode root = gnode_new_with_ccl(
      `!(values:(cm_value)list).
         ilength values == 0i ==> values == []`);
  gnode_list cases = INDUCT_TAC(root, `values:(cm_value)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF"))));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm rest_nonnegative = ispec_rule(
        `a1:(cm_value)list`, get_theorem_by_name("ILENGTH_NONNEG"));
    thm length = conv_rule(rewrite_conv(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF"))), assume_rule(
          `ilength ((a0:cm_value) :: (a1:(cm_value)list)) == 0i`));
    CONTR_TAC(leaf, mp_rule(mp_rule(int_arith_rule(
        `0i <= ilength (a1:(cm_value)list) ==>
         1i + ilength a1 == 0i ==> F`),
        rest_nonnegative), length));
  }
  return gnode_prove(root);
}
PROOF static thm cm_call_params_ilength_zero =
    cm_prove_call_params_ilength_zero();


PROOF static thm cm_prove_call_params_ann_linear_nil(void) {
  gnode root = gnode_new_with_ccl(
      `!(ann:cm_annotation).
         cm_ann_linear ([]:(tvm_inst)list) ann == ann`);
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list cases =
      CASES_TAC(introduced, `ann:cm_annotation`, "Hann");
  thm ann_case = assume_rule(
      `(ann:cm_annotation) ==
       CMAnnotation (a0:int) (a1:int) (a2:int) (a3:int)
         (a4:(cm_acursor)list) (a5:(cm_spill)list)
         (a6:(cm_spill_frame)list)
         (a7:(cm_call_sim_frame)list)`);
  CONV_WITH_ASMP_TAC(cases[0], reduce_rewrite_conv, THM_LIST(
      ann_case, cm_ann_linear_def, cm_ann_plain_def,
      cm_ann_pc_def, cm_ann_temp_def, cm_ann_break_def,
      cm_ann_continue_def, cm_ann_cursors_def,
      cm_ann_spills_def, cm_ann_saved_def, cm_ann_calls_def,
      get_theorem_by_name("ILENGTH_DEF"),
      int_ring_rule(`(pc:int) + 0i == pc`)));
  return gnode_prove(root);
}
PROOF static thm cm_call_params_ann_linear_nil =
    cm_prove_call_params_ann_linear_nil();

PROOF static thm cm_prove_target_call_params(void) {
  gnode root = gnode_new_with_ccl(
      `!(params:(cm_slot_d)list).
         !(values:(cm_value)list) (p:cm_program) (fid:int)
           (st:cm_src_state) (old:(cm_region)list)
           (gen:int) (fp:int) (oldfp:int) (index:int)
           (stack_values:(cm_value)list) (ann:cm_annotation)
           (target:tvm_task) (rest:(tvm_inst)list).
         ilength params == ilength values ==>
         cm_param_indices
           (cm_function_params
             (inth fid (cm_program_functions p)))
           index params ==>
         cm_function_wf p
           (inth fid (cm_program_functions p)) ==>
         cm_frame_segment p fid fp oldfp ==>
         cm_regions_before old gen ==>
         0i <= gen ==>
         cm_state_fp st == fp ==>
         cm_state_regions st ==
           (cm_regions_for_slots (cm_program_structs p)
             (cm_function_params
               (inth fid (cm_program_functions p)))
             gen (fp + 8i) ++ old) ==>
         (!j. 0i <= j ==>
              j < ilength
                (cm_function_params
                  (inth fid (cm_program_functions p))) ==>
              cm_state_env st 2i j ==
                CMPtrV (gen + j) 0i
                  (cm_slot_size (cm_program_structs p)
                    (inth j (cm_function_params
                      (inth fid (cm_program_functions p)))))
                  0i
                  (cm_slot_ty
                    (inth j (cm_function_params
                      (inth fid (cm_program_functions p)))))) ==>
         cm_runtime_memory_layout p st (cm_ann_calls ann)
           (cm_active_spill_frames fid st ann) ==>
         cm_code_at (cm_model_code p) (cm_ann_pc ann)
           (cm_emit_param_stores p fid index params ++ rest) ==>
         cm_running_target_sim p fid st
           (REVERSE values ++ stack_values) ann target ==>
         ilength values + ilength stack_values < 65534i ==>
         cm_running_target_sim p fid
           (cm_store_params_reverse p fid values index st)
           stack_values
           (cm_ann_linear
             (cm_emit_param_stores p fid index params) ann)
           (tvm_iter
             (cm_code_steps
               (cm_emit_param_stores p fid index params))
             target)`);
  gnode_list cases = INDUCT_TAC(root, `params:(cm_slot_d)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm length = conv_rule(rewrite_conv(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF"))), assume_rule(
          `ilength ([]:(cm_slot_d)list) ==
           ilength (values:(cm_value)list)`));
    thm values_nil = mp_rule(spec_rule(
        `values:(cm_value)list`, cm_call_params_ilength_zero),
        sym_rule(length));
    thm running = assume_rule(
        `cm_running_target_sim (p:cm_program) (fid:int)
          (st:cm_src_state)
          (REVERSE (values:(cm_value)list) ++
           (stack_values:(cm_value)list))
          (ann:cm_annotation) (target:tvm_task)`);
    thm_list rules = THM_LIST(
        values_nil, get_cm_emit_param_stores_def(),
        cm_store_params_reverse_def,
        get_theorem_by_name("REVERSE"),
        get_theorem_by_name("APPEND"),
        cm_call_params_ann_linear_nil,
        cm_code_steps_def, get_theorem_by_name("ILENGTH_DEF"),
        get_theorem_by_name("NUM_OF_INT_OF_NUM"),
        conjunct1_rule(get_tvm_iter_def()));
    thm normalized = conv_rule(reduce_rewrite_conv(rules), running);
    thm view = apply_conversion(
        reduce_rewrite_conv(rules), goal_ccl(leaf->g));
    ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(view), normalized));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    term full =
        `cm_function_params
          (inth (fid:int) (cm_program_functions (p:cm_program)))`;
    term param = `a0:cm_slot_d`;
    term param_rest = `a1:(cm_slot_d)list`;
    term value = `HD (values:(cm_value)list)`;
    term value_rest = `TL (values:(cm_value)list)`;
    term indexed_slot = `inth (index:int) ${full:(cm_slot_d)list}`;
    term ty = `cm_slot_ty ${indexed_slot:cm_slot_d}`;
    term slot_size =
        `cm_slot_size (cm_program_structs (p:cm_program))
          ${indexed_slot:cm_slot_d}`;
    term pointer =
        `CMPtrV ((gen:int) + (index:int)) 0i ${slot_size:int}
          0i ${ty:cm_type}`;
    term offset =
        `cm_param_offset (p:cm_program) (fid:int) (index:int)`;
    term address = `(fp:int) + ${offset:int}`;
    term tail_state =
        `cm_store_params_reverse (p:cm_program) (fid:int)
          ${value_rest:(cm_value)list} ((index:int) + 1i)
          (st:cm_src_state)`;
    term tail_code =
        `cm_emit_param_stores (p:cm_program) (fid:int)
          ((index:int) + 1i) ${param_rest:(cm_slot_d)list}`;
    term char_code = `cm_char_normalize_code ${ty:cm_type}`;
    term address_code =
        `cm_fp_relative_address_code ${offset:int}`;
    term store_code = `cm_store_code ${ty:cm_type}`;
    term after_address =
        `${store_code:(tvm_inst)list} ++ (rest:(tvm_inst)list)`;
    term after_char =
        `${address_code:(tvm_inst)list} ++
         ${after_address:(tvm_inst)list}`;
    term tail_suffix =
        `${char_code:(tvm_inst)list} ++
         ${after_char:(tvm_inst)list}`;
    term tail_ann =
        `cm_ann_linear ${tail_code:(tvm_inst)list}
          (ann:cm_annotation)`;
    term char_ann =
        `cm_ann_linear ${char_code:(tvm_inst)list}
          ${tail_ann:cm_annotation}`;
    term address_ann =
        `cm_ann_linear ${address_code:(tvm_inst)list}
          ${char_ann:cm_annotation}`;
    term tail_target =
        `tvm_iter (cm_code_steps ${tail_code:(tvm_inst)list})
          (target:tvm_task)`;
    term char_target =
        `tvm_iter (cm_code_steps ${char_code:(tvm_inst)list})
          ${tail_target:tvm_task}`;
    term address_target =
        `tvm_iter 4 ${char_target:tvm_task}`;
    term converted =
        `cm_convert_value ${tail_state:cm_src_state}
          ${ty:cm_type} ${value:cm_value}`;

    thm length_equal = assume_rule(
        `ilength ((a0:cm_slot_d) :: (a1:(cm_slot_d)list)) ==
         ilength (values:(cm_value)list)`);
    thm param_rest_nonnegative = ispec_rule(
        param_rest, get_theorem_by_name("ILENGTH_NONNEG"));
    thm values_nil_assumption =
        assume_rule(`(values:(cm_value)list) == []`);
    thm nil_length = conv_rule(reduce_rewrite_conv(THM_LIST(
        values_nil_assumption, get_theorem_by_name("ILENGTH_DEF"))),
        length_equal);
    thm values_nonempty = not_intro(
        `(values:(cm_value)list) == []`,
        mp_rule(mp_rule(int_arith_rule(
          `0i <= ilength ${param_rest:(cm_slot_d)list} ==>
           1i + ilength ${param_rest:(cm_slot_d)list} == 0i ==> F`),
          param_rest_nonnegative), nil_length));
    thm values_shape = mp_rule(ispec_rule(
        `values:(cm_value)list`,
        get_theorem_by_name("CONS_HD_TL")), values_nonempty);
    thm values_length = beta_norm(ap_term_rule(
        `\xs:(cm_value)list. ilength xs`, values_shape));
    thm length_shaped = trans_rule(length_equal, values_length);
    thm tail_length_raw = conv_rule(rewrite_conv(THM_LIST(
        get_theorem_by_name("ILENGTH_DEF"))), length_shaped);
    thm tail_length = mp_rule(int_arith_rule(
        `(1i + ilength ${param_rest:(cm_slot_d)list}) ==
         1i + ilength ${value_rest:(cm_value)list} ==>
         ilength ${param_rest:(cm_slot_d)list} ==
         ilength ${value_rest:(cm_value)list}`), tail_length_raw);

    thm total = assume_rule(
        `ilength (values:(cm_value)list) +
           ilength (stack_values:(cm_value)list) < 65534i`);
    thm values_length_normal = conv_rule(
        rewrite_conv(THM_LIST(get_theorem_by_name("ILENGTH_DEF"))),
        values_length);
    thm total_normal = mp_rule(mp_rule(int_arith_rule(
        `ilength (values:(cm_value)list) ==
           1i + ilength ${value_rest:(cm_value)list} ==>
         ilength values +
           ilength (stack_values:(cm_value)list) < 65534i ==>
         (1i + ilength ${value_rest:(cm_value)list}) +
           ilength stack_values < 65534i`),
        values_length_normal), total);
    thm tail_total_raw = mp_rule(int_arith_rule(
        `(1i + ilength ${value_rest:(cm_value)list}) +
           ilength (stack_values:(cm_value)list) < 65534i ==>
         ilength ${value_rest:(cm_value)list} +
           (1i + ilength (stack_values:(cm_value)list)) < 65534i`),
        total_normal);
    thm tail_total = eq_mp_rule(sym_rule(apply_conversion(
        rewrite_conv(THM_LIST(get_theorem_by_name("ILENGTH_DEF"))),
        `ilength ${value_rest:(cm_value)list} +
           ilength (${value:cm_value} ::
             (stack_values:(cm_value)list)) < 65534i`)),
        tail_total_raw);

    thm indices = assume_rule(
        `cm_param_indices ${full:(cm_slot_d)list} (index:int)
          (${param:cm_slot_d} :: ${param_rest:(cm_slot_d)list})`);
    thm head_info = mp_rule(specl_rule(TERM_LIST(
        full, `index:int`, param, param_rest),
        cm_param_indices_head), indices);
    thm index_lower = conjunct1_rule(head_info);
    thm index_upper = conjunct1_rule(conjunct2_rule(head_info));
    thm param_equal = conjunct2_rule(conjunct2_rule(head_info));
    thm tail_indices = mp_rule(specl_rule(TERM_LIST(
        full, `index:int`, param, param_rest),
        cm_param_indices_tail), indices);

    thm_list code_rules = THM_LIST(
        get_cm_emit_param_stores_def(), param_equal,
        get_theorem_by_name("APPEND"),
        gsym_rule(get_theorem_by_name("APPEND_ASSOC")),
        cm_ann_linear_def, cm_ann_plain_def,
        cm_ann_pc_def, cm_ann_temp_def, cm_ann_break_def,
        cm_ann_continue_def, cm_ann_cursors_def,
        cm_ann_spills_def, cm_ann_saved_def, cm_ann_calls_def,
        get_theorem_by_name("ILENGTH_APPEND"),
        get_theorem_by_name("ILENGTH_DEF"));
    thm old_code = assume_rule(
        `cm_code_at (cm_model_code (p:cm_program))
          (cm_ann_pc (ann:cm_annotation))
          (cm_emit_param_stores p fid index
             (${param:cm_slot_d} :: ${param_rest:(cm_slot_d)list}) ++
           (rest:(tvm_inst)list))`);
    thm old_code_normal =
        conv_rule(reduce_rewrite_conv(code_rules), old_code);
    term tail_code_term =
        `cm_code_at (cm_model_code (p:cm_program))
          (cm_ann_pc (ann:cm_annotation))
          (${tail_code:(tvm_inst)list} ++
           ${tail_suffix:(tvm_inst)list})`;
    thm tail_code_view = apply_conversion(
        reduce_rewrite_conv(code_rules), tail_code_term);
    thm tail_code_at =
        eq_mp_rule(sym_rule(tail_code_view), old_code_normal);

    thm running = assume_rule(
        `cm_running_target_sim (p:cm_program) (fid:int)
          (st:cm_src_state)
          (REVERSE (values:(cm_value)list) ++
           (stack_values:(cm_value)list))
          (ann:cm_annotation) (target:tvm_task)`);
    thm running_stack = beta_norm(ap_term_rule(
        `\xs:(cm_value)list.
           REVERSE xs ++ (stack_values:(cm_value)list)`,
        values_shape));
    running_stack = conv_rule(reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("REVERSE"),
        get_theorem_by_name("APPEND"),
        gsym_rule(get_theorem_by_name("APPEND_ASSOC")))),
        running_stack);
    thm running_view = beta_norm(ap_term_rule(
        `\xs:(cm_value)list.
           cm_running_target_sim (p:cm_program) (fid:int)
             (st:cm_src_state) xs (ann:cm_annotation)
             (target:tvm_task)`,
        running_stack));
    thm running_tail = eq_mp_rule(running_view, running);

    thm ih = specl_rule(TERM_LIST(
        value_rest, `p:cm_program`, `fid:int`, `st:cm_src_state`,
        `old:(cm_region)list`, `gen:int`, `fp:int`, `oldfp:int`,
        `(index:int) + 1i`,
        `${value:cm_value} :: (stack_values:(cm_value)list)`,
        `ann:cm_annotation`, `target:tvm_task`, tail_suffix),
        assume_rule(goal_lasmps(leaf->g)[0].tm));
    ih = match_mp_rule(ih, tail_length);
    ih = match_mp_rule(ih, tail_indices);
    ih = match_mp_rule(ih, assume_rule(
        `cm_function_wf (p:cm_program)
          (inth (fid:int) (cm_program_functions p))`));
    ih = match_mp_rule(ih, assume_rule(
        `cm_frame_segment (p:cm_program) (fid:int)
          (fp:int) (oldfp:int)`));
    ih = match_mp_rule(ih, assume_rule(
        `cm_regions_before (old:(cm_region)list) (gen:int)`));
    ih = match_mp_rule(ih, assume_rule(`0i <= (gen:int)`));
    ih = match_mp_rule(ih, assume_rule(
        `cm_state_fp (st:cm_src_state) == (fp:int)`));
    ih = match_mp_rule(ih, assume_rule(
        `cm_state_regions (st:cm_src_state) ==
         (cm_regions_for_slots (cm_program_structs p)
           ${full:(cm_slot_d)list} (gen:int) ((fp:int) + 8i) ++
          (old:(cm_region)list))`));
    ih = match_mp_rule(ih, assume_rule(
        `!j. 0i <= j ==> j < ilength ${full:(cm_slot_d)list} ==>
             cm_state_env (st:cm_src_state) 2i j ==
               CMPtrV ((gen:int) + j) 0i
                 (cm_slot_size (cm_program_structs p)
                   (inth j ${full:(cm_slot_d)list}))
                 0i (cm_slot_ty
                   (inth j ${full:(cm_slot_d)list}))`));
    thm initial_layout = assume_rule(
        `cm_runtime_memory_layout (p:cm_program) (st:cm_src_state)
          (cm_ann_calls (ann:cm_annotation))
          (cm_active_spill_frames (fid:int) st ann)`);
    ih = match_mp_rule(ih, initial_layout);
    ih = match_mp_rule(ih, tail_code_at);
    ih = match_mp_rule(ih, running_tail);
    ih = match_mp_rule(ih, tail_total);

    thm tail_structure = specl_rule(TERM_LIST(
        value_rest, `p:cm_program`, `fid:int`,
        `(index:int) + 1i`, `st:cm_src_state`),
        cm_store_params_reverse_structure);
    thm tail_fp = trans_rule(
        cm_call_params_consequence(tail_structure,
          `cm_state_fp ${tail_state:cm_src_state} ==
           cm_state_fp (st:cm_src_state)`),
        assume_rule(`cm_state_fp (st:cm_src_state) == (fp:int)`));
    thm tail_regions = trans_rule(
        cm_call_params_consequence(tail_structure,
          `cm_state_regions ${tail_state:cm_src_state} ==
           cm_state_regions (st:cm_src_state)`),
        assume_rule(
          `cm_state_regions (st:cm_src_state) ==
           (cm_regions_for_slots (cm_program_structs p)
             ${full:(cm_slot_d)list} (gen:int) ((fp:int) + 8i) ++
            (old:(cm_region)list))`));
    thm tail_env = specl_rule(TERM_LIST(
        value_rest, `p:cm_program`, `fid:int`,
        `(index:int) + 1i`, `st:cm_src_state`),
        cm_store_params_reverse_env);
    thm tail_layout_base = mp_rule(specl_rule(TERM_LIST(
        value_rest, `p:cm_program`, `fid:int`,
        `(index:int) + 1i`, `st:cm_src_state`,
        `cm_ann_calls (ann:cm_annotation)`,
        `cm_active_spill_frames (fid:int) st ann`),
        cm_store_params_reverse_runtime), initial_layout);
    thm tail_fp_original = trans_rule(tail_fp, sym_rule(
        assume_rule(`cm_state_fp (st:cm_src_state) == (fp:int)`)));
    thm_list layout_rules = THM_LIST(
        cm_ann_linear_def, cm_ann_plain_def,
        cm_ann_calls_def, cm_ann_spills_def, cm_ann_saved_def,
        cm_active_spill_frames_def, tail_fp_original);
    thm tail_layout_normal =
        conv_rule(reduce_rewrite_conv(layout_rules), tail_layout_base);
    thm layout_view = apply_conversion(
        reduce_rewrite_conv(layout_rules),
        `cm_runtime_memory_layout (p:cm_program)
          ${tail_state:cm_src_state}
          (cm_ann_calls ${address_ann:cm_annotation})
          (cm_active_spill_frames (fid:int)
            ${tail_state:cm_src_state} ${address_ann:cm_annotation})`);
    thm tail_layout =
        eq_mp_rule(sym_rule(layout_view), tail_layout_normal);

    thm numeric = specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `fp:int`, `oldfp:int`,
        `index:int`), cm_parameter_address_ready);
    numeric = match_mp_rule(numeric, assume_rule(
        `cm_function_wf (p:cm_program)
          (inth (fid:int) (cm_program_functions p))`));
    numeric = match_mp_rule(numeric, assume_rule(
        `cm_frame_segment (p:cm_program) (fid:int)
          (fp:int) (oldfp:int)`));
    numeric = match_mp_rule(numeric, index_lower);
    numeric = match_mp_rule(numeric, index_upper);
    thm fp_signed = cm_call_params_consequence(
        numeric, `tower_signed64 (fp:int)`);
    thm offset_signed = cm_call_params_consequence(
        numeric, `tower_signed64 ${offset:int}`);
    thm address_signed = cm_call_params_consequence(
        numeric, `tower_signed64 ${address:int}`);
    thm validity = cm_call_params_consequence(numeric,
        `if ${ty:cm_type} == CMCharTy
         then tower_addr_valid ${address:int}
         else tower_word_valid ${address:int}`);

    thm ready = specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, tail_state,
        `old:(cm_region)list`, `gen:int`, `fp:int`, `index:int`),
        cm_parameter_store_ready);
    ready = match_mp_rule(ready, assume_rule(
        `cm_function_wf (p:cm_program)
          (inth (fid:int) (cm_program_functions p))`));
    ready = match_mp_rule(ready, assume_rule(
        `cm_regions_before (old:(cm_region)list) (gen:int)`));
    ready = match_mp_rule(ready, assume_rule(`0i <= (gen:int)`));
    ready = match_mp_rule(ready, tail_fp);
    ready = match_mp_rule(ready, tail_regions);
    ready = match_mp_rule(ready, index_lower);
    ready = match_mp_rule(ready, index_upper);
    ready = match_mp_rule(ready, offset_signed);
    ready = match_mp_rule(ready, address_signed);
    ready = match_mp_rule(ready, validity);
    thm address_fp = cm_call_params_consequence(ready,
        `${address:int} ==
         cm_state_fp ${tail_state:cm_src_state} + ${offset:int}`);
    thm pointer_number = cm_call_params_consequence(ready,
        `tower_wrap64 ${address:int} ==
         cm_value_number ${tail_state:cm_src_state}
           ${pointer:cm_value}`);
    thm store_ok = cm_call_params_consequence(ready,
        `cm_store_ok ${ty:cm_type} ${pointer:cm_value}
          ${tail_state:cm_src_state}`);
    thm kinds = cm_call_params_consequence(ready,
        `${ty:cm_type} == CMCharTy ||
         ${ty:cm_type} == CMIntTy ||
         cm_is_pointer ${ty:cm_type}`);
    thm live = cm_call_params_consequence(ready,
        `cm_live_span ${tail_state:cm_src_state} ${address:int}
          (cm_store_width ${ty:cm_type})`);

    thm env_cell = match_mp_rule(match_mp_rule(
        spec_rule(`index:int`, assume_rule(
          `!j. 0i <= j ==> j < ilength ${full:(cm_slot_d)list} ==>
               cm_state_env (st:cm_src_state) 2i j ==
                 CMPtrV ((gen:int) + j) 0i
                   (cm_slot_size (cm_program_structs p)
                     (inth j ${full:(cm_slot_d)list}))
                   0i (cm_slot_ty
                     (inth j ${full:(cm_slot_d)list}))`)),
        index_lower), index_upper);
    thm tail_env_cell = beta_norm(ap_term_rule(
        `\env:int->int->cm_value. env 2i (index:int)`, tail_env));
    thm env_pointer = trans_rule(tail_env_cell, env_cell);

    thm value_rest_nonnegative = ispec_rule(
        value_rest, get_theorem_by_name("ILENGTH_NONNEG"));
    thm char_bound = mp_rule(mp_rule(int_arith_rule(
        `ilength ${value_rest:(cm_value)list} +
           (1i + ilength (stack_values:(cm_value)list)) < 65534i ==>
         0i <= ilength ${value_rest:(cm_value)list} ==>
         ilength (stack_values:(cm_value)list) < 65535i`),
        tail_total_raw), value_rest_nonnegative);
    thm address_bound_raw = mp_rule(mp_rule(int_arith_rule(
        `ilength ${value_rest:(cm_value)list} +
           (1i + ilength (stack_values:(cm_value)list)) < 65534i ==>
         0i <= ilength ${value_rest:(cm_value)list} ==>
         1i + ilength (stack_values:(cm_value)list) < 65535i`),
        tail_total_raw), value_rest_nonnegative);
    thm address_bound = eq_mp_rule(sym_rule(apply_conversion(
        rewrite_conv(THM_LIST(get_theorem_by_name("ILENGTH_DEF"))),
        `ilength (${converted:cm_value} ::
           (stack_values:(cm_value)list)) < 65535i`)),
        address_bound_raw);

    thm char_code_at = cm_call_params_code_suffix(
        old_code, `cm_model_code (p:cm_program)`,
        `ann:cm_annotation`, tail_code, tail_suffix,
        tail_ann, code_rules);
    thm value_signed = specl_rule(TERM_LIST(
        tail_state, value), get_cm_value_number_signed_bridge());
    thm char_result = specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, tail_state, ty, value,
        `stack_values:(cm_value)list`, tail_ann, tail_target,
        after_char), cm_target_char_normalize);
    char_result = match_mp_rule(char_result, char_code_at);
    char_result = match_mp_rule(char_result, ih);
    char_result = match_mp_rule(char_result, char_bound);
    char_result = match_mp_rule(char_result, value_signed);

    thm address_code_at = cm_call_params_code_suffix(
        char_code_at, `cm_model_code (p:cm_program)`,
        tail_ann, char_code, after_char,
        char_ann, code_rules);
    thm tail_fp_signed = conv_rule(rewrite_conv(THM_LIST(
        sym_rule(tail_fp))), fp_signed);
    thm address_result = specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, tail_state, offset, address,
        pointer, `${converted:cm_value} ::
          (stack_values:(cm_value)list)`,
        char_ann, char_target, after_address),
        cm_target_fp_relative_address);
    address_result = match_mp_rule(address_result, address_code_at);
    address_result = match_mp_rule(address_result, char_result);
    address_result = match_mp_rule(address_result, address_bound);
    address_result = match_mp_rule(address_result, tail_fp_signed);
    address_result = match_mp_rule(address_result, offset_signed);
    address_result = match_mp_rule(address_result, address_fp);
    address_result = match_mp_rule(address_result, address_signed);
    address_result = match_mp_rule(address_result, pointer_number);

    thm store_code_at = cm_call_params_code_suffix(
        address_code_at, `cm_model_code (p:cm_program)`,
        char_ann, address_code, after_address,
        address_ann, code_rules);
    store_code_at = conv_rule(reduce_rewrite_conv(THM_LIST(
        get_cm_store_code_def(), get_theorem_by_name("APPEND"))),
        store_code_at);
    thm wrap_fixed = mp_rule(spec_rule(
        address, get_tower_wrap64_fixed()), address_signed);
    thm number_address =
        trans_rule(sym_rule(pointer_number), wrap_fixed);
    thm live_number = conv_rule(rewrite_conv(THM_LIST(
        sym_rule(number_address))), live);
    thm store_result = specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, tail_state, pointer, converted,
        `stack_values:(cm_value)list`, address_ann, address_target,
        ty, `rest:(tvm_inst)list`), cm_target_store);
    store_result = match_mp_rule(store_result, store_code_at);
    store_result = match_mp_rule(store_result, address_result);
    store_result = match_mp_rule(store_result, tail_layout);
    store_result = match_mp_rule(store_result, store_ok);
    store_result = match_mp_rule(store_result, kinds);
    store_result = match_mp_rule(store_result, live_number);

    thm converted_store = specl_rule(TERM_LIST(
        ty, pointer, value, tail_state), cm_state_store_converted);
    thm pointer_store = beta_norm(ap_term_rule(
        `\ptr:cm_value.
           cm_state_store ${ty:cm_type} ptr ${value:cm_value}
             ${tail_state:cm_src_state}`,
        sym_rule(env_pointer)));
    term reverse_cons =
        `cm_store_params_reverse (p:cm_program) (fid:int)
          (${value:cm_value} :: ${value_rest:(cm_value)list})
          (index:int) (st:cm_src_state)`;
    thm reverse_view = apply_conversion(once_rewrite_conv(THM_LIST(
        cm_store_params_reverse_def)), reverse_cons);
    thm values_state = beta_norm(ap_term_rule(
        `\xs:(cm_value)list.
           cm_store_params_reverse (p:cm_program) (fid:int) xs
             (index:int) (st:cm_src_state)`,
        values_shape));
    thm final_state = trans_rule(converted_store,
        trans_rule(pointer_store,
          trans_rule(sym_rule(reverse_view), sym_rule(values_state))));
    store_result = conv_rule(rewrite_conv(THM_LIST(final_state)),
        store_result);

    thm address_steps = eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          cm_code_steps_def, get_cm_stmt_fp_relative_length(),
          get_theorem_by_name("NUM_OF_INT_OF_NUM"))),
        `cm_code_steps ${address_code:(tvm_inst)list} == 4`));
    thm store_steps = eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          cm_code_steps_def, get_cm_layout_store_length(),
          get_theorem_by_name("NUM_OF_INT_OF_NUM"))),
        `cm_code_steps ${store_code:(tvm_inst)list} == 1`));
    thm_list finish_rules = THM_LIST(
        get_cm_emit_param_stores_def(), param_equal,
        cm_call_params_ann_linear_append,
        cm_call_params_code_steps_append,
        address_steps, store_steps, get_cm_tvm_iter_add(),
        get_theorem_by_name("APPEND"),
        get_theorem_by_name("APPEND_ASSOC"));
    thm normalized =
        conv_rule(reduce_rewrite_conv(finish_rules), store_result);
    thm result_view = apply_conversion(
        reduce_rewrite_conv(finish_rules), goal_ccl(leaf->g));
    ACCEPT_TAC(leaf,
        eq_mp_rule(sym_rule(result_view), normalized));
  }
  return gnode_prove(root);
}
PROOF thm cm_target_call_params = cm_prove_target_call_params();

PROOF thm get_cm_param_indices_def(void) { return cm_param_indices_def; }
PROOF thm get_cm_param_indices_refl(void) { return cm_param_indices_refl; }
PROOF thm get_cm_param_indices_head(void) { return cm_param_indices_head; }
PROOF thm get_cm_param_indices_tail(void) { return cm_param_indices_tail; }
PROOF thm get_cm_store_params_reverse_env(void) {
  return cm_store_params_reverse_env;
}
PROOF thm get_cm_store_params_reverse_runtime(void) {
  return cm_store_params_reverse_runtime;
}
PROOF thm get_cm_target_call_params(void) {
  return cm_target_call_params;
}

PROOF static int cmc_preservation_target_call_params_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_target_call_params_axioms_before,
      "cmc_preservation_target_call_params introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _e_cmc_preservation_target_call_params_final_checks =
    cmc_preservation_target_call_params_final_checks();
