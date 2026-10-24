#include "cmc_concrete_emit_expr.h"
#include "cmc_concrete_emit_plan.h"
#include "cmc_concrete_emit_binary_finish.h"
#include "cmc_concrete_emit_expr_call.h"
#include "userlib/proof.h"
#include "userlib/operational.h"
#require "cmc_concrete_emit_expr_simple.c"
#require "cmc_concrete_count_context.c"
#require "cmc_concrete_emit_plan.c"
#require "cmc_concrete_emit_binary_finish.c"
#require "cmc_concrete_emit_expr_call.c"

PROOF static thm cm_selected_expr_code_shape(const thm shape,
                                         const thm lvalue_case,
                                         const term code) {
  thm selected = by_rewrite(
      `cm_expr_code_for (p:cm_program) (fid__pre:int) (pc__pre:int)
         (temp__pre:int) (e:cm_expr) (lvalue__pre:int) ==
       (if lvalue__pre == 0i
        then cm_rcode_of
          (cm_emit_expr_pair p fid__pre pc__pre temp__pre e)
        else cm_lcode_of
          (cm_emit_expr_pair p fid__pre pc__pre temp__pre e))`,
      THM_LIST(cm_expr_code_for_def, lvalue_case,
        get_cm_emit_rvalue_def(), get_cm_emit_lvalue_def()));
  return trans_rule(selected, by_rewrite(
      mk_eq(rhs_of(selected), code), THM_LIST(
        shape, get_cm_emit_expr_pair_def(), get_cm_rcode_of_def(),
        get_cm_lcode_of_def(), cm_expr_code_for_def,
        get_cm_emit_rvalue_def(), get_cm_emit_lvalue_def(), lvalue_case,
        eqf_intro_rule(int_arith_rule(`~(1i == 0i)`)),
        get_theorem_by_name("APPEND_NIL"))));
}


PROOF static void cm_add_rvalue_child_facts(
    const thm code_shape, const thm temp_shape,
    const term suffix) {
  thm child_temp = conv_rule(rewrite_conv(THM_LIST(temp_shape)),
      assume_rule(
        `(temp__pre:int) +
           cm_expr_temps_for (e:cm_expr) (lvalue__pre:int) <=
         (temp_limit__pre:int)`));
  add_fact_st(child_temp);
  thm parent_pc = conv_rule(
      rewrite_conv(THM_LIST(get_cm_i32_code_count_def())),
      eqt_elim_rule(assume_rule(
        `cm_i32_code_count (pc__pre:int) <=> true`)));
  thm parent_end = conv_rule(
      rewrite_conv(THM_LIST(get_cm_i32_code_count_def(), code_shape,
        get_theorem_by_name("ILENGTH_APPEND"))),
      eqt_elim_rule(assume_rule(
        `cm_i32_code_count
          ((pc__pre:int) + ilength
            (cm_expr_code_for (p:cm_program) (fid__pre:int)
              pc__pre (temp__pre:int) (e:cm_expr) (lvalue__pre:int)))
         <=> true`)));
  thm child_nonnegative = ispec_rule(
      `cm_expr_code_for (p:cm_program) (fid__pre:int)
         (pc__pre:int) (temp__pre:int) (arg_:cm_expr) 0i`,
      get_theorem_by_name("ILENGTH_NONNEG"));
  thm suffix_nonnegative = conv_rule(
      rewrite_conv(THM_LIST(get_theorem_by_name("ILENGTH_APPEND"))),
      ispec_rule(suffix, get_theorem_by_name("ILENGTH_NONNEG")));
  thm child_i32 = by_defs_arith(
      `cm_i32_code_count
        ((pc__pre:int) + ilength
          (cm_expr_code_for (p:cm_program) (fid__pre:int)
            pc__pre (temp__pre:int) (arg_:cm_expr) 0i))`,
      THM_LIST(get_cm_i32_code_count_def(), code_shape,
        get_theorem_by_name("ILENGTH_APPEND")),
      THM_LIST(parent_pc, parent_end, child_nonnegative,
        suffix_nonnegative));
  add_fact_st(eqt_intro_rule(child_i32));
}

PROOF static void cm_add_lvalue_child_facts(
    const thm code_shape, const thm temp_shape,
    const term suffix) {
  thm child_temp = conv_rule(rewrite_conv(THM_LIST(temp_shape)),
      assume_rule(
        `(temp__pre:int) +
           cm_expr_temps_for (e:cm_expr) (lvalue__pre:int) <=
         (temp_limit__pre:int)`));
  add_fact_st(child_temp);
  thm parent_pc = conv_rule(
      rewrite_conv(THM_LIST(get_cm_i32_code_count_def())),
      eqt_elim_rule(assume_rule(
        `cm_i32_code_count (pc__pre:int) <=> true`)));
  thm parent_end = conv_rule(
      rewrite_conv(THM_LIST(get_cm_i32_code_count_def(), code_shape,
        get_theorem_by_name("ILENGTH_APPEND"))),
      eqt_elim_rule(assume_rule(
        `cm_i32_code_count
          ((pc__pre:int) + ilength
            (cm_expr_code_for (p:cm_program) (fid__pre:int)
              pc__pre (temp__pre:int) (e:cm_expr) (lvalue__pre:int)))
         <=> true`)));
  thm child_nonnegative = ispec_rule(
      `cm_expr_code_for (p:cm_program) (fid__pre:int)
         (pc__pre:int) (temp__pre:int) (arg_:cm_expr) 1i`,
      get_theorem_by_name("ILENGTH_NONNEG"));
  thm suffix_nonnegative = conv_rule(
      rewrite_conv(THM_LIST(get_theorem_by_name("ILENGTH_APPEND"))),
      ispec_rule(suffix, get_theorem_by_name("ILENGTH_NONNEG")));
  thm child_i32 = by_defs_arith(
      `cm_i32_code_count
        ((pc__pre:int) + ilength
          (cm_expr_code_for (p:cm_program) (fid__pre:int)
            pc__pre (temp__pre:int) (arg_:cm_expr) 1i))`,
      THM_LIST(get_cm_i32_code_count_def(), code_shape,
        get_theorem_by_name("ILENGTH_APPEND")),
      THM_LIST(parent_pc, parent_end, child_nonnegative,
        suffix_nonnegative));
  add_fact_st(eqt_intro_rule(child_i32));
}

PROOF static thm cm_unary_code_shape(const thm shape,
                                     const thm lvalue_case,
                                     const thm_list op_cases,
                                     const term code) {
  thm selected = by_rewrite(
      `cm_expr_code_for (p:cm_program) (fid__pre:int) (pc__pre:int)
         (temp__pre:int) (e:cm_expr) (lvalue__pre:int) ==
       (if lvalue__pre == 0i
        then cm_rcode_of
          (cm_emit_expr_pair p fid__pre pc__pre temp__pre e)
        else cm_lcode_of
          (cm_emit_expr_pair p fid__pre pc__pre temp__pre e))`,
      THM_LIST(cm_expr_code_for_def, lvalue_case,
        get_cm_emit_rvalue_def(), get_cm_emit_lvalue_def()));
  thm_list rules = THM_LIST(
      shape, get_cm_emit_expr_pair_def(), get_cm_rcode_of_def(),
      get_cm_lcode_of_def(), cm_expr_code_for_def,
      get_cm_emit_rvalue_def(), get_cm_emit_lvalue_def(), lvalue_case,
      eqf_intro_rule(int_arith_rule(`~(1i == 0i)`)),
      get_theorem_by_name("APPEND_NIL"));
  for (size_t i = 0; i < vector_size(op_cases); ++i) {
    vector_add(&rules, op_cases[i]);
  }
  return trans_rule(selected,
      by_rewrite(mk_eq(rhs_of(selected), code), rules));
}


PROOF static thm cm_index_code_shape(const thm shape) {
  term target =
      `cm_expr_code_for (p:cm_program) (fid__pre:int) (pc__pre:int)
         (temp__pre:int) (e:cm_expr) (lvalue__pre:int) ==
       cm_expr_code_for p fid__pre pc__pre temp__pre
         (left_:cm_expr) 0i ++
       cm_temp_store_code p fid__pre temp__pre ++
       cm_expr_code_for p fid__pre
         (pc__pre + cm_rvalue_code_count p fid__pre left_ + 5i)
         (temp__pre + 1i) (right_:cm_expr) 0i ++
       [TVMInst TVMPushOp
          (cm_type_size (cm_program_structs p) (ty_:cm_type));
        TVMInst TVMMulOp 0i] ++
       cm_temp_load_code p fid__pre temp__pre ++
       [TVMInst TVMAddOp 0i] ++
       cm_expr_load_suffix ty_ lvalue__pre`;
  gnode root = gnode_new_with_ccl(mk_imp(concl(shape), target));
  gnode leaf = DISCH_TAC(root, "Hshape");
  gnode_list cases = BOOL_CASES_TAC(
      leaf, `(lvalue__pre:int) == 0i`, "Hlvalue");
  thm_list rules = THM_LIST(
      cm_expr_code_for_def, shape, get_cm_emit_expr_pair_def(),
      get_cm_rcode_of_def(), get_cm_lcode_of_def(),
      get_cm_emit_rvalue_def(), get_cm_emit_lvalue_def(),
      cm_expr_load_suffix_def, get_theorem_by_name("APPEND_NIL"));
  for (size_t i = 0; i < vector_size(cases); ++i) {
    CONV_WITH_ASMP_TAC(cases[i], reduce_rewrite_conv, rules);
  }
  return mp_rule(gnode_prove(root), shape);
}

PROOF static thm cm_rvalue_code_length_at(
    const term expr, const term pc, const term temp) {
  thm lengths = conjunct2_rule(
      spec_rule(expr, get_cm_expr_code_lengths()));
  thm result = specl_rule(TERM_LIST(
      `p:cm_program`, `fid__pre:int`, pc, temp), lengths);
  term selection_target = subst(TERM_PAIR_LIST(
      (term_pair){expr, `expr_:cm_expr`},
      (term_pair){pc, `pc_:int`},
      (term_pair){temp, `temp_:int`}),
      `cm_expr_code_for (p:cm_program) (fid__pre:int)
         (pc_:int) (temp_:int) (expr_:cm_expr) 0i ==
       cm_emit_rvalue p fid__pre pc_ temp_ expr_`);
  thm selection = by_rewrite(selection_target, THM_LIST(
      cm_expr_code_for_def,
      eqt_intro_rule(int_arith_rule(`0i == 0i`))));
  return conv_rule(rewrite_conv(THM_LIST(gsym_rule(selection))),
      result);
}

PROOF static void cm_add_expr_result_refs_st(void) {
  thm result = specl_rule(TERM_LIST(
      `e:cm_expr`, `p:cm_program`, `f:cm_function_d`),
      cm_expr_result_refs);
  result = mp_rule(result, eqt_elim_rule(assume_rule(
      `cm_typed_program (p:cm_program) <=> true`)));
  result = mp_rule(result, eqt_elim_rule(assume_rule(
      `cm_slots_wf (cm_program_structs (p:cm_program))
        (cm_function_params (f:cm_function_d)) <=> true`)));
  result = mp_rule(result, eqt_elim_rule(assume_rule(
      `cm_slots_wf (cm_program_structs (p:cm_program))
        (cm_function_locals (f:cm_function_d)) <=> true`)));
  result = mp_rule(result, eqt_elim_rule(assume_rule(
      `cm_expr_wf (p:cm_program) (f:cm_function_d)
        (e:cm_expr) <=> true`)));
  add_fact_st(eqt_intro_rule(result));
}
PROOF static void cm_add_child_expr_facts_st(const term child) {
  term child_count_fact = subst(TERM_PAIR_LIST(
      (term_pair){child, `child_:cm_expr`}),
      `cm_expr_counts_representable (p:cm_program)
         (fid__pre:int) child_`);
  thm node = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `fid__pre:int`, child), cm_expr_counts_node),
      from_state_bool(child_count_fact));
  thm node_facts = conv_rule(rewrite_conv(THM_LIST(
      get_cm_expr_count_node_representable_def(),
      get_cm_code_counts_representable_def())), node);
  cm_add_count_facts(node_facts);

  term child_wf_fact = subst(TERM_PAIR_LIST(
      (term_pair){child, `child_:cm_expr`}),
      `cm_expr_wf (p:cm_program) (f:cm_function_d) child_`);
  thm refs = specl_rule(TERM_LIST(
      child, `p:cm_program`, `f:cm_function_d`),
      cm_expr_result_refs);
  refs = mp_rule(refs, from_state_bool(
      `cm_typed_program (p:cm_program)`));
  refs = mp_rule(refs, from_state_bool(
      `cm_slots_wf (cm_program_structs (p:cm_program))
        (cm_function_params (f:cm_function_d))`));
  refs = mp_rule(refs, from_state_bool(
      `cm_slots_wf (cm_program_structs (p:cm_program))
        (cm_function_locals (f:cm_function_d))`));
  refs = mp_rule(refs, from_state_bool(child_wf_fact));
  add_fact_st(eqt_intro_rule(refs));
}
PROOF static thm cm_prove_rep_members_size_nonnegative(void) {
  gnode root = gnode_new_with_ccl(
      `!(members:(cm_slot_d)list).
         cm_rep_members_safe members ==>
         0i <= cm_rep_members_size members`);
  gnode_list cases = INDUCT_TAC(root, `members:(cm_slot_d)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        get_cm_rep_members_size_def())));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm safe = conv_rule(rewrite_conv(THM_LIST(
        get_cm_rep_members_safe_def())),
        assume_rule(
          `cm_rep_members_safe
            ((a0:cm_slot_d) :: (a1:(cm_slot_d)list))`));
    gnode reduced = CONV_TAC(leaf, rewrite_conv(THM_LIST(
        get_cm_rep_members_size_def())));
    thm inputs = conj_rule(conjunct1_rule(safe),
        conjunct1_rule(conjunct2_rule(safe)));
    ACCEPT_TAC(reduced, mp_rule(int_arith_rule(mk_imp(
        concl(inputs), goal_ccl(reduced->g))), inputs));
  }
  return gnode_prove(root);
}
PROOF static thm cm_rep_members_size_nonnegative =
    cm_prove_rep_members_size_nonnegative();


PROOF static void cm_add_index_temp_facts(const thm shape) {
  thm parent_shape = by_rewrite(
      `cm_expr_temps_for (e:cm_expr) (lvalue__pre:int) ==
       cm_imax (cm_rtemps (left_:cm_expr))
         (1i + cm_rtemps (right_:cm_expr))`,
      THM_LIST(cm_expr_temps_for_def, shape,
        get_cm_ltemps_def(), get_cm_rtemps_def(),
        get_cm_expr_tpair_def(), get_cm_tleft_def(),
        get_cm_tright_def(), get_theorem_by_name("COND_ID")));
  thm parent_bound = conv_rule(rewrite_conv(THM_LIST(
      parent_shape)), assume_rule(
        `(temp__pre:int) +
           cm_expr_temps_for (e:cm_expr) (lvalue__pre:int) <=
         (temp_limit__pre:int)`));
  thm left_nonnegative = conjunct2_rule(spec_rule(
      `left_:cm_expr`, cm_expr_temps_nonnegative));
  thm right_nonnegative = conjunct2_rule(spec_rule(
      `right_:cm_expr`, cm_expr_temps_nonnegative));
  thm left_max = specl_rule(TERM_LIST(
      `cm_rtemps (left_:cm_expr)`,
      `1i + cm_rtemps (right_:cm_expr)`),
      cm_imax_left_bound);
  thm right_max = specl_rule(TERM_LIST(
      `cm_rtemps (left_:cm_expr)`,
      `1i + cm_rtemps (right_:cm_expr)`),
      cm_imax_right_bound);
  thm left_bound = by_defs_arith(
      `(temp__pre:int) +
         cm_expr_temps_for (left_:cm_expr) 0i <=
       (temp_limit__pre:int)`,
      THM_LIST(cm_expr_temps_for_def),
      THM_LIST(parent_bound, left_max));
  thm right_bound = by_defs_arith(
      `(temp__pre:int) + 1i +
         cm_expr_temps_for (right_:cm_expr) 0i <=
       (temp_limit__pre:int)`,
      THM_LIST(cm_expr_temps_for_def),
      THM_LIST(parent_bound, right_max));
  add_fact_st(left_bound);
  add_fact_st(right_bound);
  add_fact_st(mp_rule(int_arith_rule(
      `0i <= (temp__pre:int) ==> 0i <= temp__pre + 1i`),
      assume_rule(`0i <= (temp__pre:int)`)));
  add_fact_st(mp_rule(mp_rule(int_arith_rule(
      `(temp__pre:int) + 1i +
         cm_rtemps (right_:cm_expr) <=
           (temp_limit__pre:int) ==>
       0i <= cm_rtemps right_ ==>
       temp__pre + 1i <= temp_limit__pre`),
      conv_rule(rewrite_conv(THM_LIST(cm_expr_temps_for_def)),
        right_bound)), right_nonnegative));
  cm_add_temp_offset_bound_st(`temp__pre:int`);
  cm_add_temp_offset_bound_st(`(temp__pre:int) + 1i`);
  {
    term params =
        `cm_function_params (f:cm_function_d)`;
    term locals =
        `cm_function_locals (f:cm_function_d)`;
    thm params_safe = from_state_bool(
        `cm_rep_members_safe
          (cm_function_params (f:cm_function_d))`);
    thm locals_safe = from_state_bool(
        `cm_rep_members_safe
          (cm_function_locals (f:cm_function_d))`);
    thm params_rep_nonnegative = mp_rule(
        spec_rule(params, cm_rep_members_size_nonnegative),
        params_safe);
    thm locals_rep_nonnegative = mp_rule(
        spec_rule(locals, cm_rep_members_size_nonnegative),
        locals_safe);
    thm params_match = mp_rule(specl_rule(TERM_LIST(
        `cm_program_structs (p:cm_program)`, params),
        cm_rep_members_size_matches), from_state_bool(
          `cm_slots_wf (cm_program_structs (p:cm_program))
            (cm_function_params (f:cm_function_d))`));
    thm locals_match = mp_rule(specl_rule(TERM_LIST(
        `cm_program_structs (p:cm_program)`, locals),
        cm_rep_members_size_matches), from_state_bool(
          `cm_slots_wf (cm_program_structs (p:cm_program))
            (cm_function_locals (f:cm_function_d))`));
    thm params_nonnegative = by_rewrite(
        `0i <= cm_slots_size (cm_program_structs (p:cm_program))
          (cm_function_params (f:cm_function_d))`,
        THM_LIST(sym_rule(params_match), params_rep_nonnegative));
    thm locals_nonnegative = by_rewrite(
        `0i <= cm_slots_size (cm_program_structs (p:cm_program))
          (cm_function_locals (f:cm_function_d))`,
        THM_LIST(sym_rule(locals_match), locals_rep_nonnegative));
    thm params_at_fid = conv_rule(rewrite_conv(THM_LIST(
        assume_rule(
          `(f:cm_function_d) ==
           inth (fid__pre:int) (cm_program_functions (p:cm_program))`))),
        params_nonnegative);
    thm locals_at_fid = conv_rule(rewrite_conv(THM_LIST(
        assume_rule(
          `(f:cm_function_d) ==
           inth (fid__pre:int) (cm_program_functions (p:cm_program))`))),
        locals_nonnegative);
    thm offset_bound = conv_rule(rewrite_conv(THM_LIST(
        get_cm_temp_offset_def())), assume_rule(
          `cm_temp_offset (p:cm_program) (fid__pre:int)
            ((temp__pre:int) + 1i) <= 2147483647i`));
    thm temp_upper = by_defs_arith(
        `(temp__pre:int) + 1i <= 2147483647i`,
        THM_LIST(get_cm_temp_offset_def()),
        THM_LIST(params_at_fid, locals_at_fid, offset_bound));
    thm temp_cast = mp_rule(mp_rule(spec_rule(
        `(temp__pre:int) + 1i`, cm_nonnegative_i32_cast),
        assume_rule(`0i <= (temp__pre:int) + 1i`)), temp_upper);
    add_fact_st(temp_upper);
    add_fact_st(temp_cast);
  }
  add_fact_st(left_nonnegative);
}

PROOF static void cm_add_index_pc_facts(
    const thm code_shape, const term fixed_suffix) {
  term base_code =
      `cm_expr_code_for (p:cm_program) (fid__pre:int)
         (pc__pre:int) (temp__pre:int) (left_:cm_expr) 0i`;
  term right_code =
      `cm_expr_code_for (p:cm_program) (fid__pre:int)
         ((pc__pre:int) +
           cm_rvalue_code_count p fid__pre left_ + 5i)
         ((temp__pre:int) + 1i) (right_:cm_expr) 0i`;
  term after_base = subst(TERM_PAIR_LIST(
      (term_pair){right_code, `right_code_:(tvm_inst)list`},
      (term_pair){fixed_suffix, `fixed_:(tvm_inst)list`}),
      `cm_temp_store_code (p:cm_program) (fid__pre:int)
         (temp__pre:int) ++ right_code_ ++ fixed_`);
  term after_store = subst(TERM_PAIR_LIST(
      (term_pair){right_code, `right_code_:(tvm_inst)list`},
      (term_pair){fixed_suffix, `fixed_:(tvm_inst)list`}),
      `(right_code_:(tvm_inst)list) ++
       (fixed_:(tvm_inst)list)`);
  thm parent_pc = conv_rule(
      rewrite_conv(THM_LIST(get_cm_i32_code_count_def())),
      eqt_elim_rule(assume_rule(
        `cm_i32_code_count (pc__pre:int) <=> true`)));
  thm parent_end = conv_rule(
      rewrite_conv(THM_LIST(get_cm_i32_code_count_def())),
      eqt_elim_rule(assume_rule(
        `cm_i32_code_count
          ((pc__pre:int) + ilength
            (cm_expr_code_for (p:cm_program) (fid__pre:int)
              pc__pre (temp__pre:int) (e:cm_expr) (lvalue__pre:int)))
         <=> true`)));
  thm base_length = cm_rvalue_code_length_at(
      `left_:cm_expr`, `pc__pre:int`, `temp__pre:int`);
  thm right_length = cm_rvalue_code_length_at(
      `right_:cm_expr`,
      `(pc__pre:int) +
        cm_rvalue_code_count (p:cm_program)
          (fid__pre:int) (left_:cm_expr) + 5i`,
      `(temp__pre:int) + 1i`);
  thm after_base_nonnegative = ispec_rule(
      after_base, get_theorem_by_name("ILENGTH_NONNEG"));
  thm fixed_nonnegative = ispec_rule(
      fixed_suffix, get_theorem_by_name("ILENGTH_NONNEG"));
  thm after_store_nonnegative = ispec_rule(
      after_store, get_theorem_by_name("ILENGTH_NONNEG"));
  thm base_nonnegative = ispec_rule(
      base_code, get_theorem_by_name("ILENGTH_NONNEG"));
  thm right_nonnegative = ispec_rule(
      right_code, get_theorem_by_name("ILENGTH_NONNEG"));
  thm_list rules = THM_LIST(
      get_cm_i32_code_count_def(), code_shape,
      get_theorem_by_name("ILENGTH_APPEND"),
      get_theorem_by_name("ILENGTH_DEF"),
      get_cm_temp_store_code_def(),
      get_cm_fp_relative_address_code_def(), base_length,
      right_length);
  thm parent_end_shape = conv_rule(rewrite_conv(rules), parent_end);
  thm after_base_nonnegative_shape =
      conv_rule(rewrite_conv(rules), after_base_nonnegative);
  thm fixed_nonnegative_shape =
      conv_rule(rewrite_conv(rules), fixed_nonnegative);
  thm after_store_nonnegative_shape =
      conv_rule(rewrite_conv(rules), after_store_nonnegative);
  thm right_nonnegative_shape =
      conv_rule(rewrite_conv(rules), right_nonnegative);
  thm base_end = by_defs_arith(
      `cm_i32_code_count
        ((pc__pre:int) + ilength
          (cm_expr_code_for (p:cm_program) (fid__pre:int)
            pc__pre (temp__pre:int) (left_:cm_expr) 0i))`,
      rules, THM_LIST(parent_pc, parent_end_shape,
        after_base_nonnegative_shape, base_nonnegative,
        base_length));
  thm right_start = by_defs_arith(
      `cm_i32_code_count
        ((pc__pre:int) +
          cm_rvalue_code_count (p:cm_program)
            (fid__pre:int) (left_:cm_expr) + 5i)`,
      rules, THM_LIST(parent_pc, parent_end_shape,
        after_store_nonnegative_shape, base_nonnegative,
        base_length));
  thm right_start_bounds = conv_rule(
      rewrite_conv(THM_LIST(get_cm_i32_code_count_def())),
      right_start);
  thm right_partial_bounds;
  thm right_partial_cast;
  thm right_start_cast;
  thm base_increment_bounds;
  thm base_increment_cast;
  thm right_partial = by_defs_arith(
      `cm_i32_code_count
        ((pc__pre:int) +
          cm_rvalue_code_count (p:cm_program)
            (fid__pre:int) (left_:cm_expr))`,
      rules, THM_LIST(parent_pc, right_start_bounds,
        base_nonnegative, base_length));
  right_partial_bounds = conv_rule(
      rewrite_conv(THM_LIST(get_cm_i32_code_count_def())),
      right_partial);
  right_partial_cast = mp_rule(mp_rule(spec_rule(
      `(pc__pre:int) +
        cm_rvalue_code_count (p:cm_program)
          (fid__pre:int) (left_:cm_expr)`,
      cm_nonnegative_i32_cast), conjunct1_rule(right_partial_bounds)),
      conjunct2_rule(right_partial_bounds));
  right_start_cast = mp_rule(mp_rule(spec_rule(
      `(pc__pre:int) +
        cm_rvalue_code_count (p:cm_program)
          (fid__pre:int) (left_:cm_expr) + 5i`,
      cm_nonnegative_i32_cast), conjunct1_rule(right_start_bounds)),
      conjunct2_rule(right_start_bounds));
  base_increment_bounds = by_defs_arith(
      `0i <=
         cm_rvalue_code_count (p:cm_program)
           (fid__pre:int) (left_:cm_expr) + 5i &&
       cm_rvalue_code_count p fid__pre left_ + 5i <= 2147483647i`,
      rules, THM_LIST(parent_pc, right_start_bounds,
        base_nonnegative, base_length));
  base_increment_cast = mp_rule(mp_rule(spec_rule(
      `cm_rvalue_code_count (p:cm_program)
         (fid__pre:int) (left_:cm_expr) + 5i`,
      cm_nonnegative_i32_cast),
      conjunct1_rule(base_increment_bounds)),
      conjunct2_rule(base_increment_bounds));
  thm right_end = by_defs_arith(
      `cm_i32_code_count
        (((pc__pre:int) +
           cm_rvalue_code_count (p:cm_program)
             (fid__pre:int) (left_:cm_expr) + 5i) +
         ilength
           (cm_expr_code_for p fid__pre
             (pc__pre +
               cm_rvalue_code_count p fid__pre left_ + 5i)
             (temp__pre + 1i) (right_:cm_expr) 0i))`,
      rules, THM_LIST(parent_pc, right_start_bounds,
        parent_end_shape, fixed_nonnegative_shape,
        right_nonnegative_shape, base_length, right_length));
  add_fact_st(eqt_intro_rule(base_end));
  add_fact_st(eqt_intro_rule(right_start));
  add_fact_st(eqt_intro_rule(right_partial));
  add_fact_st(eqt_intro_rule(right_end));
  add_fact_st(conjunct1_rule(right_partial_bounds));
  add_fact_st(conjunct2_rule(right_partial_bounds));
  add_fact_st(conjunct1_rule(right_start_bounds));
  add_fact_st(conjunct2_rule(right_start_bounds));
  add_fact_st(conjunct1_rule(base_increment_bounds));
  add_fact_st(conjunct2_rule(base_increment_bounds));
  add_fact_st(right_partial_cast);
  add_fact_st(right_start_cast);
  add_fact_st(base_increment_cast);
}

static void cm_emit_intrinsic_expr(struct cm_program *program, int fid,
                            struct cm_function *fn, int pc, int temp,
                            int temp_limit, struct cm_expr *expr,
                            int lvalue, struct cm_emitter *emitter)
    [[cst::param(`p:cm_program`, `f:cm_function_d`, `e:cm_expr`,
                 `body:int`, `next:int`, `functions_ptr:int`,
                 `done:(tvm_inst)list`, `tail:(tvm_inst)list`,
                 `out:int`, `capacity:int`)]]
    [[cst::require(
      `fact(cm_intrinsic_expr e <=> true) **
       fact(0i <= lvalue) ** fact(lvalue <= 1i) **
       fact(cm_wf_program p <=> true) **
       fact(cm_typed_program p <=> true) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(cm_expr_wf p f e <=> true) **
       fact(cm_expr_counts_representable p fid e <=> true) **
       fact(cm_slots_wf (cm_program_structs p) (cm_function_params f) <=> true) **
       fact(cm_slots_wf (cm_program_structs p) (cm_function_locals f) <=> true) **
       fact(cm_rep_structs_safe (cm_program_structs p) <=> true) **
       fact(cm_rep_globals_safe (cm_program_globals p) <=> true) **
       fact(cm_rep_strings_safe (cm_program_strings p) <=> true) **
       fact(cm_rep_members_safe (cm_function_params f) <=> true) **
       fact(cm_rep_members_safe (cm_function_locals f) <=> true) **
       fact(cm_rep_globals_size (cm_program_globals p) +
              cm_rep_strings_size (cm_program_strings p) <= 1048560i) **
       fact(0i <= temp) ** fact(temp <= temp_limit) **
       fact(temp + cm_expr_temps_for e lvalue <= temp_limit) **
       fact(cm_temp_offset p fid temp_limit <= 2147483647i) **
       fact(cm_i32_code_count pc <=> true) **
       fact(cm_i32_code_count
              (pc + ilength (cm_expr_code_for p fid pc temp e lvalue))
              <=> true) **
       cm_program_context_rep program p functions_ptr **
       cm_function_context_rep fn f body next **
       cm_expr_rep expr e **
       cm_resolved_emitter_plan_rep p emitter out capacity done
         (cm_expr_code_for p fid pc temp e lvalue ++ tail)`)]]
    [[cst::ensure(
      `fact(cm_intrinsic_expr e <=> true) **
       fact(0i <= lvalue) ** fact(lvalue <= 1i) **
       fact(cm_wf_program p <=> true) **
       fact(cm_typed_program p <=> true) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(cm_expr_wf p f e <=> true) **
       fact(cm_expr_counts_representable p fid e <=> true) **
       fact(cm_slots_wf (cm_program_structs p) (cm_function_params f) <=> true) **
       fact(cm_slots_wf (cm_program_structs p) (cm_function_locals f) <=> true) **
       fact(cm_rep_structs_safe (cm_program_structs p) <=> true) **
       fact(cm_rep_globals_safe (cm_program_globals p) <=> true) **
       fact(cm_rep_strings_safe (cm_program_strings p) <=> true) **
       fact(cm_rep_members_safe (cm_function_params f) <=> true) **
       fact(cm_rep_members_safe (cm_function_locals f) <=> true) **
       fact(cm_rep_globals_size (cm_program_globals p) +
              cm_rep_strings_size (cm_program_strings p) <= 1048560i) **
       fact(0i <= temp) ** fact(temp <= temp_limit) **
       fact(temp + cm_expr_temps_for e lvalue <= temp_limit) **
       fact(cm_temp_offset p fid temp_limit <= 2147483647i) **
       fact(cm_i32_code_count pc <=> true) **
       fact(cm_i32_code_count
              (pc + ilength (cm_expr_code_for p fid pc temp e lvalue))
              <=> true) **
       cm_program_context_rep program p functions_ptr **
       cm_function_context_rep fn f body next **
       cm_expr_rep expr e **
       cm_resolved_emitter_plan_rep p emitter out capacity
         (done ++ cm_expr_code_for p fid pc temp e lvalue) tail`)]]
{
  [[cst::proof]] { cm_open_expr_rep_st(); }
  if (expr->kind == CMC_EXPR_PUTC) {
    [[cst::proof]] {
      thm shape_ent = mp_rule(spec_rule(`e:cm_expr`,
          get_cm_expr_putc_shape_ent()),
          assume_rule(`cm_rep_expr_kind (e:cm_expr) == 11i`));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          rename_exists_hconv(shape_ent,
            TERM_LIST(`arg_:cm_expr`, `ty_:cm_type`))));
      thm shape = assume_rule(
          `e == CMPutcE (arg_:cm_expr) (ty_:cm_type)`);
      cm_open_expr_count_facts(shape);
    }
    if (!lvalue) {
      [[cst::proof]] {
        thm shape = assume_rule(
            `e == CMPutcE (arg_:cm_expr) (ty_:cm_type)`);
        cm_open_single_child_count_payload(shape);
        thm code_shape = cm_selected_expr_code_shape(shape,
            eqt_intro_rule(assume_rule(`lvalue__pre == 0i`)),
            `cm_expr_code_for p fid__pre pc__pre temp__pre arg_ 0i ++
             [TVMInst TVMDupOp 0i; TVMInst TVMPutcOp 0i]`);
        thm temp_shape = by_rewrite(
            `cm_expr_temps_for (e:cm_expr) (lvalue__pre:int) ==
             cm_expr_temps_for (arg_:cm_expr) 0i`,
            THM_LIST(cm_expr_temps_for_def, shape, get_cm_rtemps_def(),
              get_cm_expr_tpair_def(), get_cm_tright_def(),
              eqt_intro_rule(assume_rule(`lvalue__pre == 0i`))));
        cm_add_rvalue_child_facts(code_shape, temp_shape,
            `[TVMInst TVMDupOp 0i; TVMInst TVMPutcOp 0i]`);
        cm_select_code_plan_st(code_shape);
      }
      [[cst::where(`p`, `(p:cm_program)`)]][[cst::where(`f`, `(f:cm_function_d)`)]]
      [[cst::where(`fid`, `(fid__pre:int)`)]]
      cm_emit_expr(program, fid, fn, pc, temp, temp_limit,
                   expr->a, 0, emitter);
      [[cst::proof]] {
        rewrite_st(THM_LIST(get_theorem_by_name("APPEND")));
      }
      [[cst::proof]] { cm_add_opcode_facts_st(`2i`, `TVMDupOp`); }
      [[cst::where(`p`, `(p:cm_program)`)]][[cst::where(`opcode`, `TVMDupOp`)]]
      cm_emit_plan(emitter, CMC_OP_DUP, 0);
      [[cst::proof]] { cm_add_opcode_facts_st(`25i`, `TVMPutcOp`); }
      [[cst::where(`p`, `(p:cm_program)`)]][[cst::where(`opcode`, `TVMPutcOp`)]]
      cm_emit_plan(emitter, CMC_OP_PUTC, 0);
      [[cst::proof]] {
        thm shape = assume_rule(
            `e == CMPutcE (arg_:cm_expr) (ty_:cm_type)`);
        thm code_shape = cm_selected_expr_code_shape(shape,
            eqt_intro_rule(assume_rule(`lvalue__pre == 0i`)),
            `cm_expr_code_for p fid__pre pc__pre temp__pre arg_ 0i ++
             [TVMInst TVMDupOp 0i; TVMInst TVMPutcOp 0i]`);
        cm_restore_code_plan_end_st(code_shape);
        cm_close_single_child_count_payload(shape);
      }
    } else {
      [[cst::proof]] {
        thm code_shape = cm_selected_expr_code_shape(
            assume_rule(`e == CMPutcE (arg_:cm_expr) (ty_:cm_type)`),
            eqf_intro_rule(assume_rule(`~(lvalue__pre == 0i)`)),
            `[]:(tvm_inst)list`);
        cm_empty_code_plan_end_st(code_shape);
      }
    }
  } else if (expr->kind == CMC_EXPR_PUTI) {
    [[cst::proof]] {
      thm shape_ent = mp_rule(spec_rule(`e:cm_expr`,
          get_cm_expr_puti_shape_ent()),
          assume_rule(`cm_rep_expr_kind (e:cm_expr) == 12i`));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          rename_exists_hconv(shape_ent,
            TERM_LIST(`arg_:cm_expr`, `ty_:cm_type`))));
      thm shape = assume_rule(
          `e == CMPutiE (arg_:cm_expr) (ty_:cm_type)`);
      cm_open_expr_count_facts(shape);
    }
    if (!lvalue) {
      [[cst::proof]] {
        thm shape = assume_rule(
            `e == CMPutiE (arg_:cm_expr) (ty_:cm_type)`);
        cm_open_single_child_count_payload(shape);
        thm code_shape = cm_selected_expr_code_shape(shape,
            eqt_intro_rule(assume_rule(`lvalue__pre == 0i`)),
            `cm_expr_code_for p fid__pre pc__pre temp__pre arg_ 0i ++
             [TVMInst TVMDupOp 0i; TVMInst TVMPutiOp 0i]`);
        thm temp_shape = by_rewrite(
            `cm_expr_temps_for (e:cm_expr) (lvalue__pre:int) ==
             cm_expr_temps_for (arg_:cm_expr) 0i`,
            THM_LIST(cm_expr_temps_for_def, shape, get_cm_rtemps_def(),
              get_cm_expr_tpair_def(), get_cm_tright_def(),
              eqt_intro_rule(assume_rule(`lvalue__pre == 0i`))));
        cm_add_rvalue_child_facts(code_shape, temp_shape,
            `[TVMInst TVMDupOp 0i; TVMInst TVMPutiOp 0i]`);
        cm_select_code_plan_st(code_shape);
      }
      [[cst::where(`p`, `(p:cm_program)`)]][[cst::where(`f`, `(f:cm_function_d)`)]]
      [[cst::where(`fid`, `(fid__pre:int)`)]]
      cm_emit_expr(program, fid, fn, pc, temp, temp_limit,
                   expr->a, 0, emitter);
      [[cst::proof]] {
        rewrite_st(THM_LIST(get_theorem_by_name("APPEND")));
      }
      [[cst::proof]] { cm_add_opcode_facts_st(`2i`, `TVMDupOp`); }
      [[cst::where(`p`, `(p:cm_program)`)]][[cst::where(`opcode`, `TVMDupOp`)]]
      cm_emit_plan(emitter, CMC_OP_DUP, 0);
      [[cst::proof]] { cm_add_opcode_facts_st(`26i`, `TVMPutiOp`); }
      [[cst::where(`p`, `(p:cm_program)`)]][[cst::where(`opcode`, `TVMPutiOp`)]]
      cm_emit_plan(emitter, CMC_OP_PUTI, 0);
      [[cst::proof]] {
        thm shape = assume_rule(
            `e == CMPutiE (arg_:cm_expr) (ty_:cm_type)`);
        thm code_shape = cm_selected_expr_code_shape(shape,
            eqt_intro_rule(assume_rule(`lvalue__pre == 0i`)),
            `cm_expr_code_for p fid__pre pc__pre temp__pre arg_ 0i ++
             [TVMInst TVMDupOp 0i; TVMInst TVMPutiOp 0i]`);
        cm_restore_code_plan_end_st(code_shape);
        cm_close_single_child_count_payload(shape);
      }
    } else {
      [[cst::proof]] {
        thm code_shape = cm_selected_expr_code_shape(
            assume_rule(`e == CMPutiE (arg_:cm_expr) (ty_:cm_type)`),
            eqf_intro_rule(assume_rule(`~(lvalue__pre == 0i)`)),
            `[]:(tvm_inst)list`);
        cm_empty_code_plan_end_st(code_shape);
      }
    }
  } else {
    [[cst::proof]] {
      thm intrinsic = eqt_elim_rule(assume_rule(
          `cm_intrinsic_expr (e:cm_expr) <=> true`));
      thm is_exit = conv_rule(rewrite_conv(THM_LIST(
          cm_intrinsic_expr_def,
          eqf_intro_rule(assume_rule(
            `~(cm_rep_expr_kind (e:cm_expr) == 11i)`)),
          eqf_intro_rule(assume_rule(
            `~(cm_rep_expr_kind (e:cm_expr) == 12i)`)))), intrinsic);
      add_fact_st(is_exit);
      thm shape_ent = mp_rule(spec_rule(`e:cm_expr`,
          get_cm_expr_exit_shape_ent()), is_exit);
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          rename_exists_hconv(shape_ent,
            TERM_LIST(`arg_:cm_expr`, `ty_:cm_type`))));
      thm shape = assume_rule(
          `e == CMExitE (arg_:cm_expr) (ty_:cm_type)`);
      cm_open_expr_count_facts(shape);
    }
    if (!lvalue) {
      [[cst::proof]] {
        thm shape = assume_rule(
            `e == CMExitE (arg_:cm_expr) (ty_:cm_type)`);
        cm_open_single_child_count_payload(shape);
        thm code_shape = cm_selected_expr_code_shape(shape,
            eqt_intro_rule(assume_rule(`lvalue__pre == 0i`)),
            `cm_expr_code_for p fid__pre pc__pre temp__pre arg_ 0i ++
             cm_char_normalize_code CMCharTy ++
             [TVMInst TVMHaltOp 0i]`);
        thm temp_shape = by_rewrite(
            `cm_expr_temps_for (e:cm_expr) (lvalue__pre:int) ==
             cm_expr_temps_for (arg_:cm_expr) 0i`,
            THM_LIST(cm_expr_temps_for_def, shape, get_cm_rtemps_def(),
              get_cm_expr_tpair_def(), get_cm_tright_def(),
              eqt_intro_rule(assume_rule(`lvalue__pre == 0i`))));
        cm_add_rvalue_child_facts(code_shape, temp_shape,
            `cm_char_normalize_code CMCharTy ++
             [TVMInst TVMHaltOp 0i]`);
        cm_select_code_plan_st(code_shape);
      }
      [[cst::where(`p`, `(p:cm_program)`)]][[cst::where(`f`, `(f:cm_function_d)`)]]
      [[cst::where(`fid`, `(fid__pre:int)`)]]
      cm_emit_expr(program, fid, fn, pc, temp, temp_limit,
                   expr->a, 0, emitter);
      [[cst::proof]] {
        add_fact_st(by_rewrite(
            `cm_type_code_wf CMCharTy <=> true`,
            THM_LIST(get_cm_type_code_wf_def())));
        thm char_encoded = eqt_elim_rule(apply_conversion(
            reduce_rewrite_conv(THM_LIST(get_cm_type_encode_def(),
              get_cm_type_depth_def(), get_cm_type_base_code_def())),
            `cm_type_encode CMCharTy == 1i`));
        add_fact_st(sym_rule(char_encoded));
      }
      [[cst::where(`p`, `(p:cm_program)`)]]
      [[cst::where(`model_ty`, `CMCharTy`)]]
      cm_emit_normalize_plan(emitter, CMC_TYPE_CHAR);
      [[cst::proof]] {
        rewrite_st(THM_LIST(get_theorem_by_name("APPEND")));
      }
      [[cst::proof]] { cm_add_opcode_facts_st(`27i`, `TVMHaltOp`); }
      [[cst::where(`p`, `(p:cm_program)`)]][[cst::where(`opcode`, `TVMHaltOp`)]]
      cm_emit_plan(emitter, CMC_OP_HALT, 0);
      [[cst::proof]] {
        thm shape = assume_rule(
            `e == CMExitE (arg_:cm_expr) (ty_:cm_type)`);
        thm code_shape = cm_selected_expr_code_shape(shape,
            eqt_intro_rule(assume_rule(`lvalue__pre == 0i`)),
            `cm_expr_code_for p fid__pre pc__pre temp__pre arg_ 0i ++
             cm_char_normalize_code CMCharTy ++
             [TVMInst TVMHaltOp 0i]`);
        cm_restore_code_plan_end_st(code_shape);
        cm_close_single_child_count_payload(shape);
      }
    } else {
      [[cst::proof]] {
        thm code_shape = cm_selected_expr_code_shape(
            assume_rule(`e == CMExitE (arg_:cm_expr) (ty_:cm_type)`),
            eqf_intro_rule(assume_rule(`~(lvalue__pre == 0i)`)),
            `[]:(tvm_inst)list`);
        cm_empty_code_plan_end_st(code_shape);
      }
    }
  }
  [[cst::proof]] { cm_close_expr_rep_st(); }
}

static void cm_emit_unary_expr(struct cm_program *program, int fid,
                               struct cm_function *fn, int pc, int temp,
                               int temp_limit, struct cm_expr *expr,
                               int lvalue, struct cm_emitter *emitter)
    [[cst::param(`p:cm_program`, `f:cm_function_d`, `e:cm_expr`,
                 `op_:int`, `arg_:cm_expr`, `ty_:cm_type`,
                 `body:int`, `next:int`, `functions_ptr:int`,
                 `done:(tvm_inst)list`, `tail:(tvm_inst)list`,
                 `out:int`, `capacity:int`)]]
    [[cst::require(
      `fact(e == CMUnaryE op_ arg_ ty_) **
       fact(0i <= lvalue) ** fact(lvalue <= 1i) **
       fact(cm_wf_program p <=> true) **
       fact(cm_typed_program p <=> true) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(cm_expr_wf p f e <=> true) **
       fact(cm_expr_counts_representable p fid e <=> true) **
       fact(cm_slots_wf (cm_program_structs p)
              (cm_function_params f) <=> true) **
       fact(cm_slots_wf (cm_program_structs p)
              (cm_function_locals f) <=> true) **
       fact(cm_rep_structs_safe (cm_program_structs p) <=> true) **
       fact(cm_rep_globals_safe (cm_program_globals p) <=> true) **
       fact(cm_rep_strings_safe (cm_program_strings p) <=> true) **
       fact(cm_rep_members_safe (cm_function_params f) <=> true) **
       fact(cm_rep_members_safe (cm_function_locals f) <=> true) **
       fact(cm_rep_globals_size (cm_program_globals p) +
              cm_rep_strings_size (cm_program_strings p) <= 1048560i) **
       fact(0i <= temp) ** fact(temp <= temp_limit) **
       fact(temp + cm_expr_temps_for e lvalue <= temp_limit) **
       fact(cm_temp_offset p fid temp_limit <= 2147483647i) **
       fact(cm_i32_code_count pc <=> true) **
       fact(cm_i32_code_count
              (pc + ilength (cm_expr_code_for p fid pc temp e lvalue))
              <=> true) **
       cm_program_context_rep program p functions_ptr **
       cm_function_context_rep fn f body next **
       cm_expr_rep expr e **
       cm_resolved_emitter_plan_rep p emitter out capacity done
         (cm_expr_code_for p fid pc temp e lvalue ++ tail)`)]]
    [[cst::ensure(
      `fact(e == CMUnaryE op_ arg_ ty_) **
       fact(0i <= lvalue) ** fact(lvalue <= 1i) **
       fact(cm_wf_program p <=> true) **
       fact(cm_typed_program p <=> true) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(cm_expr_wf p f e <=> true) **
       fact(cm_expr_counts_representable p fid e <=> true) **
       fact(cm_slots_wf (cm_program_structs p)
              (cm_function_params f) <=> true) **
       fact(cm_slots_wf (cm_program_structs p)
              (cm_function_locals f) <=> true) **
       fact(cm_rep_structs_safe (cm_program_structs p) <=> true) **
       fact(cm_rep_globals_safe (cm_program_globals p) <=> true) **
       fact(cm_rep_strings_safe (cm_program_strings p) <=> true) **
       fact(cm_rep_members_safe (cm_function_params f) <=> true) **
       fact(cm_rep_members_safe (cm_function_locals f) <=> true) **
       fact(cm_rep_globals_size (cm_program_globals p) +
              cm_rep_strings_size (cm_program_strings p) <= 1048560i) **
       fact(0i <= temp) ** fact(temp <= temp_limit) **
       fact(temp + cm_expr_temps_for e lvalue <= temp_limit) **
       fact(cm_temp_offset p fid temp_limit <= 2147483647i) **
       fact(cm_i32_code_count pc <=> true) **
       fact(cm_i32_code_count
              (pc + ilength (cm_expr_code_for p fid pc temp e lvalue))
              <=> true) **
       cm_program_context_rep program p functions_ptr **
       cm_function_context_rep fn f body next **
       cm_expr_rep expr e **
       cm_resolved_emitter_plan_rep p emitter out capacity
         (done ++ cm_expr_code_for p fid pc temp e lvalue) tail`)]]
{
  [[cst::proof]] {
    cm_open_expr_rep_st();
    thm shape = assume_rule(
        `e == CMUnaryE (op_:int) (arg_:cm_expr) (ty_:cm_type)`);
    thm op_model = by_rewrite(
        `cm_rep_expr_op (e:cm_expr) == (op_:int)`,
        THM_LIST(shape, get_cm_rep_expr_op_def()));
    substitute_st(op_model);
    add_fact_st(by_rewrite(
        `cm_type_encode (cm_expr_type (e:cm_expr)) ==
         cm_type_encode (ty_:cm_type)`,
        THM_LIST(shape, get_cm_expr_type_def())));
    cm_open_expr_count_facts(shape);
    cm_open_single_child_count_payload(shape);
  }
  if (expr->op == CMC_UN_DEREF) {
    if (!lvalue) {
      [[cst::proof]] {
        thm shape = assume_rule(
            `e == CMUnaryE (op_:int) (arg_:cm_expr) (ty_:cm_type)`);
        thm op_case = eqt_intro_rule(
            assume_rule(`(op_:int) == 2i`));
        thm lvalue_case = eqt_intro_rule(
            assume_rule(`lvalue__pre == 0i`));
        thm code_shape = cm_unary_code_shape(shape, lvalue_case,
            THM_LIST(op_case),
            `cm_expr_code_for p fid__pre pc__pre temp__pre arg_ 0i ++
             cm_load_code (ty_:cm_type)`);
        thm temp_shape = by_rewrite(
            `cm_expr_temps_for (e:cm_expr) (lvalue__pre:int) ==
             cm_expr_temps_for (arg_:cm_expr) 0i`,
            THM_LIST(cm_expr_temps_for_def, shape,
              get_cm_ltemps_def(), get_cm_rtemps_def(),
              get_cm_expr_tpair_def(), get_cm_tleft_def(),
              get_cm_tright_def(), op_case, lvalue_case));
        cm_add_rvalue_child_facts(code_shape, temp_shape,
            `cm_load_code (ty_:cm_type)`);
        cm_select_code_plan_st(code_shape);
      }
      [[cst::where(`p`, `(p:cm_program)`)]]
      [[cst::where(`f`, `(f:cm_function_d)`)]]
      [[cst::where(`fid`, `(fid__pre:int)`)]]
      cm_emit_expr(program, fid, fn, pc, temp, temp_limit,
                   expr->a, 0, emitter);
      [[cst::where(`p`, `(p:cm_program)`)]]
      [[cst::where(`model_ty`, `(ty_:cm_type)`)]]
      cm_emit_load_plan(emitter, expr->ty);
      [[cst::proof]] {
        thm shape = assume_rule(
            `e == CMUnaryE (op_:int) (arg_:cm_expr) (ty_:cm_type)`);
        thm code_shape = cm_unary_code_shape(shape,
            eqt_intro_rule(assume_rule(`lvalue__pre == 0i`)),
            THM_LIST(eqt_intro_rule(
              assume_rule(`(op_:int) == 2i`))),
            `cm_expr_code_for p fid__pre pc__pre temp__pre arg_ 0i ++
             cm_load_code (ty_:cm_type)`);
        cm_restore_code_plan_end_st(code_shape);
      }
    } else {
      [[cst::proof]] {
        thm shape = assume_rule(
            `e == CMUnaryE (op_:int) (arg_:cm_expr) (ty_:cm_type)`);
        thm op_case = eqt_intro_rule(
            assume_rule(`(op_:int) == 2i`));
        thm lvalue_case = eqf_intro_rule(
            assume_rule(`~(lvalue__pre == 0i)`));
        thm code_shape = cm_unary_code_shape(shape, lvalue_case,
            THM_LIST(op_case),
            `cm_expr_code_for p fid__pre pc__pre temp__pre arg_ 0i`);
        thm temp_shape = by_rewrite(
            `cm_expr_temps_for (e:cm_expr) (lvalue__pre:int) ==
             cm_expr_temps_for (arg_:cm_expr) 0i`,
            THM_LIST(cm_expr_temps_for_def, shape,
              get_cm_ltemps_def(), get_cm_rtemps_def(),
              get_cm_expr_tpair_def(), get_cm_tleft_def(),
              get_cm_tright_def(), op_case, lvalue_case));
        cm_add_rvalue_child_facts(code_shape, temp_shape,
            `[]:(tvm_inst)list`);
        cm_select_code_plan_st(code_shape);
      }
      [[cst::where(`p`, `(p:cm_program)`)]]
      [[cst::where(`f`, `(f:cm_function_d)`)]]
      [[cst::where(`fid`, `(fid__pre:int)`)]]
      cm_emit_expr(program, fid, fn, pc, temp, temp_limit,
                   expr->a, 0, emitter);
      [[cst::proof]] {
        thm shape = assume_rule(
            `e == CMUnaryE (op_:int) (arg_:cm_expr) (ty_:cm_type)`);
        thm code_shape = cm_unary_code_shape(shape,
            eqf_intro_rule(assume_rule(`~(lvalue__pre == 0i)`)),
            THM_LIST(eqt_intro_rule(
              assume_rule(`(op_:int) == 2i`))),
            `cm_expr_code_for p fid__pre pc__pre temp__pre arg_ 0i`);
        cm_restore_code_plan_end_st(code_shape);
      }
    }
  } else if (expr->op == CMC_UN_ADDR) {
    if (!lvalue) {
      [[cst::proof]] {
        thm shape = assume_rule(
            `e == CMUnaryE (op_:int) (arg_:cm_expr) (ty_:cm_type)`);
        thm not_deref = eqf_intro_rule(
            assume_rule(`~((op_:int) == 2i)`));
        thm is_addr = eqt_intro_rule(
            assume_rule(`(op_:int) == 3i`));
        thm lvalue_case = eqt_intro_rule(
            assume_rule(`lvalue__pre == 0i`));
        thm code_shape = cm_unary_code_shape(shape, lvalue_case,
            THM_LIST(not_deref, is_addr),
            `cm_expr_code_for p fid__pre pc__pre temp__pre arg_ 1i`);
        thm temp_shape = by_rewrite(
            `cm_expr_temps_for (e:cm_expr) (lvalue__pre:int) ==
             cm_expr_temps_for (arg_:cm_expr) 1i`,
            THM_LIST(cm_expr_temps_for_def, shape,
              get_cm_ltemps_def(), get_cm_rtemps_def(),
              get_cm_expr_tpair_def(), get_cm_tleft_def(),
              get_cm_tright_def(), not_deref, is_addr, lvalue_case,
              eqf_intro_rule(int_arith_rule(`~(1i == 0i)`))));
        cm_add_lvalue_child_facts(code_shape, temp_shape,
            `[]:(tvm_inst)list`);
        cm_select_code_plan_st(code_shape);
      }
      [[cst::where(`p`, `(p:cm_program)`)]]
      [[cst::where(`f`, `(f:cm_function_d)`)]]
      [[cst::where(`fid`, `(fid__pre:int)`)]]
      cm_emit_expr(program, fid, fn, pc, temp, temp_limit,
                   expr->a, 1, emitter);
      [[cst::proof]] {
        thm shape = assume_rule(
            `e == CMUnaryE (op_:int) (arg_:cm_expr) (ty_:cm_type)`);
        thm code_shape = cm_unary_code_shape(shape,
            eqt_intro_rule(assume_rule(`lvalue__pre == 0i`)),
            THM_LIST(
              eqf_intro_rule(assume_rule(`~((op_:int) == 2i)`)),
              eqt_intro_rule(assume_rule(`(op_:int) == 3i`))),
            `cm_expr_code_for p fid__pre pc__pre temp__pre arg_ 1i`);
        cm_restore_code_plan_end_st(code_shape);
      }
    } else {
      [[cst::proof]] {
        thm shape = assume_rule(
            `e == CMUnaryE (op_:int) (arg_:cm_expr) (ty_:cm_type)`);
        thm code_shape = cm_unary_code_shape(shape,
            eqf_intro_rule(assume_rule(`~(lvalue__pre == 0i)`)),
            THM_LIST(
              eqf_intro_rule(assume_rule(`~((op_:int) == 2i)`)),
              eqt_intro_rule(assume_rule(`(op_:int) == 3i`))),
            `[]:(tvm_inst)list`);
        cm_empty_code_plan_end_st(code_shape);
      }
    }
  } else {
    if (!lvalue) {
      if (expr->op == CMC_UN_NEG) {
        [[cst::proof]] {
          thm shape = assume_rule(
              `e == CMUnaryE (op_:int) (arg_:cm_expr) (ty_:cm_type)`);
          thm not_deref = eqf_intro_rule(
              assume_rule(`~((op_:int) == 2i)`));
          thm not_addr = eqf_intro_rule(
              assume_rule(`~((op_:int) == 3i)`));
          thm is_neg = eqt_intro_rule(
              assume_rule(`(op_:int) == 0i`));
          thm lvalue_case = eqt_intro_rule(
              assume_rule(`lvalue__pre == 0i`));
          thm code_shape = cm_unary_code_shape(shape, lvalue_case,
              THM_LIST(not_deref, not_addr, is_neg),
              `cm_expr_code_for p fid__pre pc__pre temp__pre arg_ 0i ++
               [TVMInst TVMPushOp (--1i); TVMInst TVMMulOp 0i]`);
          thm temp_shape = by_rewrite(
              `cm_expr_temps_for (e:cm_expr) (lvalue__pre:int) ==
               cm_expr_temps_for (arg_:cm_expr) 0i`,
              THM_LIST(cm_expr_temps_for_def, shape,
                get_cm_ltemps_def(), get_cm_rtemps_def(),
                get_cm_expr_tpair_def(), get_cm_tleft_def(),
                get_cm_tright_def(), not_deref, not_addr,
                lvalue_case));
          cm_add_rvalue_child_facts(code_shape, temp_shape,
              `[TVMInst TVMPushOp (--1i); TVMInst TVMMulOp 0i]`);
          cm_select_code_plan_st(code_shape);
        }
        [[cst::where(`p`, `(p:cm_program)`)]]
        [[cst::where(`f`, `(f:cm_function_d)`)]]
        [[cst::where(`fid`, `(fid__pre:int)`)]]
        cm_emit_expr(program, fid, fn, pc, temp, temp_limit,
                     expr->a, 0, emitter);
        [[cst::proof]] {
          rewrite_st(THM_LIST(get_theorem_by_name("APPEND")));
          cm_add_opcode_facts_st(`0i`, `TVMPushOp`);
        }
        [[cst::where(`p`, `(p:cm_program)`)]]
        [[cst::where(`opcode`, `TVMPushOp`)]]
        cm_emit_plan(emitter, CMC_OP_PUSH, -1);
        [[cst::proof]] {
          cm_add_opcode_facts_st(`10i`, `TVMMulOp`);
        }
        [[cst::where(`p`, `(p:cm_program)`)]]
        [[cst::where(`opcode`, `TVMMulOp`)]]
        cm_emit_plan(emitter, CMC_OP_MUL, 0);
        [[cst::proof]] {
          thm shape = assume_rule(
              `e == CMUnaryE (op_:int) (arg_:cm_expr) (ty_:cm_type)`);
          thm code_shape = cm_unary_code_shape(shape,
              eqt_intro_rule(assume_rule(`lvalue__pre == 0i`)),
              THM_LIST(
                eqf_intro_rule(assume_rule(`~((op_:int) == 2i)`)),
                eqf_intro_rule(assume_rule(`~((op_:int) == 3i)`)),
                eqt_intro_rule(assume_rule(`(op_:int) == 0i`))),
              `cm_expr_code_for p fid__pre pc__pre temp__pre arg_ 0i ++
               [TVMInst TVMPushOp (--1i); TVMInst TVMMulOp 0i]`);
          cm_restore_code_plan_end_st(code_shape);
        }
      } else {
        [[cst::proof]] {
          thm shape = assume_rule(
              `e == CMUnaryE (op_:int) (arg_:cm_expr) (ty_:cm_type)`);
          thm not_deref = eqf_intro_rule(
              assume_rule(`~((op_:int) == 2i)`));
          thm not_addr = eqf_intro_rule(
              assume_rule(`~((op_:int) == 3i)`));
          thm not_neg = eqf_intro_rule(
              assume_rule(`~((op_:int) == 0i)`));
          thm lvalue_case = eqt_intro_rule(
              assume_rule(`lvalue__pre == 0i`));
          thm code_shape = cm_unary_code_shape(shape, lvalue_case,
              THM_LIST(not_deref, not_addr, not_neg),
              `cm_expr_code_for p fid__pre pc__pre temp__pre arg_ 0i ++
               [TVMInst TVMPushOp 0i; TVMInst TVMEqOp 0i]`);
          thm temp_shape = by_rewrite(
              `cm_expr_temps_for (e:cm_expr) (lvalue__pre:int) ==
               cm_expr_temps_for (arg_:cm_expr) 0i`,
              THM_LIST(cm_expr_temps_for_def, shape,
                get_cm_ltemps_def(), get_cm_rtemps_def(),
                get_cm_expr_tpair_def(), get_cm_tleft_def(),
                get_cm_tright_def(), not_deref, not_addr,
                lvalue_case));
          cm_add_rvalue_child_facts(code_shape, temp_shape,
              `[TVMInst TVMPushOp 0i; TVMInst TVMEqOp 0i]`);
          cm_select_code_plan_st(code_shape);
        }
        [[cst::where(`p`, `(p:cm_program)`)]]
        [[cst::where(`f`, `(f:cm_function_d)`)]]
        [[cst::where(`fid`, `(fid__pre:int)`)]]
        cm_emit_expr(program, fid, fn, pc, temp, temp_limit,
                     expr->a, 0, emitter);
        [[cst::proof]] {
          rewrite_st(THM_LIST(get_theorem_by_name("APPEND")));
          cm_add_opcode_facts_st(`0i`, `TVMPushOp`);
        }
        [[cst::where(`p`, `(p:cm_program)`)]]
        [[cst::where(`opcode`, `TVMPushOp`)]]
        cm_emit_plan(emitter, CMC_OP_PUSH, 0);
        [[cst::proof]] {
          cm_add_opcode_facts_st(`13i`, `TVMEqOp`);
        }
        [[cst::where(`p`, `(p:cm_program)`)]]
        [[cst::where(`opcode`, `TVMEqOp`)]]
        cm_emit_plan(emitter, CMC_OP_EQ, 0);
        [[cst::proof]] {
          thm shape = assume_rule(
              `e == CMUnaryE (op_:int) (arg_:cm_expr) (ty_:cm_type)`);
          thm code_shape = cm_unary_code_shape(shape,
              eqt_intro_rule(assume_rule(`lvalue__pre == 0i`)),
              THM_LIST(
                eqf_intro_rule(assume_rule(`~((op_:int) == 2i)`)),
                eqf_intro_rule(assume_rule(`~((op_:int) == 3i)`)),
                eqf_intro_rule(assume_rule(`~((op_:int) == 0i)`))),
              `cm_expr_code_for p fid__pre pc__pre temp__pre arg_ 0i ++
               [TVMInst TVMPushOp 0i; TVMInst TVMEqOp 0i]`);
          cm_restore_code_plan_end_st(code_shape);
        }
      }
    } else {
      [[cst::proof]] {
        thm shape = assume_rule(
            `e == CMUnaryE (op_:int) (arg_:cm_expr) (ty_:cm_type)`);
        thm code_shape = cm_unary_code_shape(shape,
            eqf_intro_rule(assume_rule(`~(lvalue__pre == 0i)`)),
            THM_LIST(
              eqf_intro_rule(assume_rule(`~((op_:int) == 2i)`)),
              eqf_intro_rule(assume_rule(`~((op_:int) == 3i)`))),
            `[]:(tvm_inst)list`);
        cm_empty_code_plan_end_st(code_shape);
      }
    }
  }
  [[cst::proof]] {
    thm shape = assume_rule(
        `e == CMUnaryE (op_:int) (arg_:cm_expr) (ty_:cm_type)`);
    cm_close_single_child_count_payload(shape);
    thm op_model = by_rewrite(
        `cm_rep_expr_op (e:cm_expr) == (op_:int)`,
        THM_LIST(shape, get_cm_rep_expr_op_def()));
    substitute_st(sym_rule(op_model));
    cm_close_expr_rep_st();
  }
}

static void cm_emit_index_expr(struct cm_program *program, int fid,
                               struct cm_function *fn, int pc, int temp,
                               int temp_limit, struct cm_expr *expr,
                               int lvalue, struct cm_emitter *emitter)
    [[cst::param(`p:cm_program`, `f:cm_function_d`, `e:cm_expr`,
                 `left_:cm_expr`, `right_:cm_expr`, `ty_:cm_type`,
                 `body:int`, `next:int`, `functions_ptr:int`,
                 `done:(tvm_inst)list`, `tail:(tvm_inst)list`,
                 `out:int`, `capacity:int`)]]
    [[cst::require(
      `fact(e == CMIndexE left_ right_ ty_) **
       fact(0i <= lvalue) ** fact(lvalue <= 1i) **
       fact(cm_wf_program p <=> true) **
       fact(cm_typed_program p <=> true) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(cm_expr_wf p f e <=> true) **
       fact(cm_expr_counts_representable p fid e <=> true) **
       fact(cm_slots_wf (cm_program_structs p)
              (cm_function_params f) <=> true) **
       fact(cm_slots_wf (cm_program_structs p)
              (cm_function_locals f) <=> true) **
       fact(cm_rep_structs_safe (cm_program_structs p) <=> true) **
       fact(cm_rep_globals_safe (cm_program_globals p) <=> true) **
       fact(cm_rep_strings_safe (cm_program_strings p) <=> true) **
       fact(cm_rep_members_safe (cm_function_params f) <=> true) **
       fact(cm_rep_members_safe (cm_function_locals f) <=> true) **
       fact(cm_rep_globals_size (cm_program_globals p) +
              cm_rep_strings_size (cm_program_strings p) <= 1048560i) **
       fact(0i <= temp) ** fact(temp <= temp_limit) **
       fact(temp + cm_expr_temps_for e lvalue <= temp_limit) **
       fact(cm_temp_offset p fid temp_limit <= 2147483647i) **
       fact(cm_i32_code_count pc <=> true) **
       fact(cm_i32_code_count
              (pc + ilength (cm_expr_code_for p fid pc temp e lvalue))
              <=> true) **
       cm_program_context_rep program p functions_ptr **
       cm_function_context_rep fn f body next **
       cm_expr_rep expr e **
       cm_resolved_emitter_plan_rep p emitter out capacity done
         (cm_expr_code_for p fid pc temp e lvalue ++ tail)`)]]
    [[cst::ensure(
      `fact(e == CMIndexE left_ right_ ty_) **
       fact(0i <= lvalue) ** fact(lvalue <= 1i) **
       fact(cm_wf_program p <=> true) **
       fact(cm_typed_program p <=> true) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(cm_expr_wf p f e <=> true) **
       fact(cm_expr_counts_representable p fid e <=> true) **
       fact(cm_slots_wf (cm_program_structs p)
              (cm_function_params f) <=> true) **
       fact(cm_slots_wf (cm_program_structs p)
              (cm_function_locals f) <=> true) **
       fact(cm_rep_structs_safe (cm_program_structs p) <=> true) **
       fact(cm_rep_globals_safe (cm_program_globals p) <=> true) **
       fact(cm_rep_strings_safe (cm_program_strings p) <=> true) **
       fact(cm_rep_members_safe (cm_function_params f) <=> true) **
       fact(cm_rep_members_safe (cm_function_locals f) <=> true) **
       fact(cm_rep_globals_size (cm_program_globals p) +
              cm_rep_strings_size (cm_program_strings p) <= 1048560i) **
       fact(0i <= temp) ** fact(temp <= temp_limit) **
       fact(temp + cm_expr_temps_for e lvalue <= temp_limit) **
       fact(cm_temp_offset p fid temp_limit <= 2147483647i) **
       fact(cm_i32_code_count pc <=> true) **
       fact(cm_i32_code_count
              (pc + ilength (cm_expr_code_for p fid pc temp e lvalue))
              <=> true) **
       cm_program_context_rep program p functions_ptr **
       cm_function_context_rep fn f body next **
       cm_expr_rep expr e **
       cm_resolved_emitter_plan_rep p emitter out capacity
         (done ++ cm_expr_code_for p fid pc temp e lvalue) tail`)]]
{
  [[cst::proof]] {
    cm_open_expr_rep_st();
    thm shape = assume_rule(
        `e == CMIndexE (left_:cm_expr) (right_:cm_expr)
          (ty_:cm_type)`);
    add_fact_st(by_rewrite(
        `cm_type_encode (cm_expr_type (e:cm_expr)) ==
         cm_type_encode (ty_:cm_type)`,
        THM_LIST(shape, get_cm_expr_type_def())));
    cm_open_expr_count_facts(shape);
    cm_open_two_child_count_payload(shape);
    cm_add_expr_result_refs_st();
    thm model_refs = conv_rule(
        rewrite_conv(THM_LIST(shape, get_cm_expr_type_def())),
        from_state_bool(
          `cm_type_refs (cm_program_structs (p:cm_program))
             (cm_expr_type (e:cm_expr))`));
    add_fact_st(eqt_intro_rule(model_refs));
    cm_add_index_temp_facts(shape);
  }
  [[cst::where(`p`, `(p:cm_program)`)]]
  [[cst::where(`f`, `(f:cm_function_d)`)]]
  [[cst::where(`e`, `(left_:cm_expr)`)]]
  [[cst::where(`fid`, `(fid__pre:int)`)]]
  int base_count = cm_expr_rvalue_count_context(
      program, fid, fn, expr->a);
  [[cst::proof]] {
    thm returned = assume_rule(
        `(retval:int) ==
         cm_rcount_of
           (cm_expr_code_counts (p:cm_program)
             (fid__pre:int) (left_:cm_expr))`);
    thm model = conv_rule(rewrite_conv(THM_LIST(
        gsym_rule(get_cm_rvalue_code_count_def()))), returned);
    add_fact_st(model);
    cst_set_symbolic_state(retarget_cell_st(
        cst_get_symbolic_state(), `base_count__addr:addr`,
        `retval:int`,
        `cm_rvalue_code_count (p:cm_program)
          (fid__pre:int) (left_:cm_expr)`));
  }
  [[cst::where(`p`, `(p:cm_program)`)]]
  [[cst::where(`asked`, `(ty_:cm_type)`)]]
  [[cst::where(`functions_ptr`, `(functions_ptr:int)`)]]
  long long element_size = cm_type_size_value(program, expr->ty);
  [[cst::proof]] {
    cst_set_symbolic_state(retarget_cell64_st(
        cst_get_symbolic_state(), `element_size__addr:addr`,
        `retval_1:int`,
        `cm_type_size (cm_program_structs (p:cm_program))
          (ty_:cm_type)`));
  }
  [[cst::proof]] {
    thm shape = assume_rule(
        `e == CMIndexE (left_:cm_expr) (right_:cm_expr)
          (ty_:cm_type)`);
    thm code_shape = cm_index_code_shape(shape);
    cm_add_index_pc_facts(code_shape,
        `[TVMInst TVMPushOp
            (cm_type_size (cm_program_structs p) ty_);
          TVMInst TVMMulOp 0i] ++
         cm_temp_load_code p fid__pre temp__pre ++
         [TVMInst TVMAddOp 0i] ++
         cm_expr_load_suffix ty_ lvalue__pre`);
    cm_select_code_plan_st(code_shape);
  }
  [[cst::where(`p`, `(p:cm_program)`)]]
  [[cst::where(`f`, `(f:cm_function_d)`)]]
  [[cst::where(`fid`, `(fid__pre:int)`)]]
  cm_emit_expr(program, fid, fn, pc, temp, temp_limit,
               expr->a, 0, emitter);
  [[cst::proof]] {
    rewrite_st(THM_LIST(get_theorem_by_name("APPEND")));
  }
  [[cst::where(`p`, `(p:cm_program)`)]]
  [[cst::where(`f`, `(f:cm_function_d)`)]]
  [[cst::where(`fid`, `(fid__pre:int)`)]]
  [[cst::where(`structs`, `cm_program_structs (p:cm_program)`)]]
  cm_emit_temp_store_plan(fn, temp, emitter);
  [[cst::proof]] {
    rewrite_st(THM_LIST(get_theorem_by_name("APPEND")));
  }
  int right_pc = pc + (base_count + 5);
  int right_temp = temp + 1;
  struct cm_expr *right_expr = expr->b;
  [[cst::proof]] {
    term child_tail =
        `TVMInst TVMPushOp
            (cm_type_size (cm_program_structs (p:cm_program))
              (ty_:cm_type)) ::
         TVMInst TVMMulOp 0i ::
         (cm_temp_load_code p (fid__pre:int) (temp__pre:int) ++
          TVMInst TVMAddOp 0i ::
          (cm_expr_load_suffix ty_ (lvalue__pre:int) ++
           (tail:(tvm_inst)list)))`;
    term child_done =
        `((done:(tvm_inst)list) ++
            cm_expr_code_for (p:cm_program) (fid__pre:int)
              (pc__pre:int) (temp__pre:int) (left_:cm_expr) 0i) ++
          cm_temp_store_code p fid__pre temp__pre`;
    term child_resources =
        `cm_program_context_rep (program__pre:int) (p:cm_program)
           (functions_ptr:int) **
         cm_function_context_rep (fn__pre:int) (f:cm_function_d)
           (body:int) (next:int) **
         cm_expr_rep (zb:int) (right_:cm_expr) **
         cm_resolved_emitter_plan_rep p (emitter__pre:int)
           (out:int) (capacity:int) child_done_
           (cm_expr_code_for p (fid__pre:int)
              (pc__pre +
                cm_rvalue_code_count p fid__pre (left_:cm_expr) + 5i)
              ((temp__pre:int) + 1i) right_ 0i ++ child_tail_)`;
    child_resources = subst(TERM_PAIR_LIST(
        (term_pair){child_done, `child_done_:(tvm_inst)list`},
        (term_pair){child_tail, `child_tail_:(tvm_inst)list`}),
        child_resources);
    cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
        refl_slrule(child_resources)));
  }
  [[cst::proof]] {
    term child_facts =
        `fact(0i <= 0i) **
         fact(0i <= 1i) **
         fact(cm_wf_program (p:cm_program) <=> true) **
         fact(cm_typed_program p <=> true) **
         fact((f:cm_function_d) ==
           inth (fid__pre:int) (cm_program_functions p)) **
         fact(cm_expr_wf p f (right_:cm_expr) <=> true) **
         fact(cm_expr_counts_representable p fid__pre right_
           <=> true) **
         fact(cm_slots_wf (cm_program_structs p)
           (cm_function_params f) <=> true) **
         fact(cm_slots_wf (cm_program_structs p)
           (cm_function_locals f) <=> true) **
         fact(cm_rep_structs_safe (cm_program_structs p) <=> true) **
         fact(cm_rep_globals_safe (cm_program_globals p) <=> true) **
         fact(cm_rep_strings_safe (cm_program_strings p) <=> true) **
         fact(cm_rep_members_safe (cm_function_params f) <=> true) **
         fact(cm_rep_members_safe (cm_function_locals f) <=> true) **
         fact(cm_rep_globals_size (cm_program_globals p) +
           cm_rep_strings_size (cm_program_strings p) <= 1048560i) **
         fact(0i <= (temp__pre:int) + 1i) **
         fact(temp__pre + 1i <= (temp_limit__pre:int)) **
         fact(temp__pre + 1i +
           cm_expr_temps_for (right_:cm_expr) 0i <= temp_limit__pre) **
         fact(cm_temp_offset p (fid__pre:int) (temp_limit__pre:int)
           <= 2147483647i) **
         fact(cm_i32_code_count
           ((pc__pre:int) +
            cm_rvalue_code_count p fid__pre (left_:cm_expr) + 5i)
           <=> true) **
         fact(cm_i32_code_count
           ((pc__pre +
             cm_rvalue_code_count p fid__pre left_ + 5i) +
            ilength
              (cm_expr_code_for p fid__pre
                (pc__pre +
                  cm_rvalue_code_count p fid__pre left_ + 5i)
                (temp__pre + 1i) right_ 0i))
           <=> true)`;
    cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
        refl_slrule(child_facts)));
  }
  [[cst::where(`p`, `(p:cm_program)`)]]
  [[cst::where(`f`, `(f:cm_function_d)`)]]
  [[cst::where(`fid`, `(fid__pre:int)`)]]
  [[cst::where(`e`, `(right_:cm_expr)`)]]
  [[cst::where(`body`, `(body:int)`)]]
  [[cst::where(`next`, `(next:int)`)]]
  [[cst::where(`functions_ptr`, `(functions_ptr:int)`)]]
  [[cst::where(`out`, `(out:int)`)]]
  [[cst::where(`capacity`, `(capacity:int)`)]]
  [[cst::where(`done`,
      `((done:(tvm_inst)list) ++
          cm_expr_code_for (p:cm_program) (fid__pre:int)
            (pc__pre:int) (temp__pre:int) (left_:cm_expr) 0i) ++
        cm_temp_store_code p fid__pre temp__pre`)]]
  [[cst::where(`tail`,
      `TVMInst TVMPushOp
          (cm_type_size (cm_program_structs (p:cm_program))
            (ty_:cm_type)) ::
       TVMInst TVMMulOp 0i ::
       (cm_temp_load_code p (fid__pre:int) (temp__pre:int) ++
        TVMInst TVMAddOp 0i ::
        (cm_expr_load_suffix ty_ (lvalue__pre:int) ++
         (tail:(tvm_inst)list)))`)]]
  cm_emit_expr(program, fid, fn, right_pc, right_temp, temp_limit,
               right_expr, 0, emitter);
  [[cst::proof]] {
    rewrite_st(THM_LIST(get_theorem_by_name("APPEND")));
    cm_add_opcode_facts_st(`0i`, `TVMPushOp`);
  }
  [[cst::where(`p`, `(p:cm_program)`)]]
  [[cst::where(`opcode`, `TVMPushOp`)]]
  cm_emit_plan(emitter, CMC_OP_PUSH, element_size);
  [[cst::proof]] {
    cm_add_opcode_facts_st(`10i`, `TVMMulOp`);
  }
  [[cst::where(`p`, `(p:cm_program)`)]]
  [[cst::where(`opcode`, `TVMMulOp`)]]
  cm_emit_plan(emitter, CMC_OP_MUL, 0);
  [[cst::proof]] {
    rewrite_st(THM_LIST(get_theorem_by_name("APPEND")));
  }
  [[cst::where(`p`, `(p:cm_program)`)]]
  [[cst::where(`f`, `(f:cm_function_d)`)]]
  [[cst::where(`fid`, `(fid__pre:int)`)]]
  [[cst::where(`structs`, `cm_program_structs (p:cm_program)`)]]
  cm_emit_temp_load_plan(fn, temp, emitter);
  [[cst::proof]] {
    rewrite_st(THM_LIST(get_theorem_by_name("APPEND")));
    cm_add_opcode_facts_st(`8i`, `TVMAddOp`);
  }
  [[cst::where(`p`, `(p:cm_program)`)]]
  [[cst::where(`opcode`, `TVMAddOp`)]]
  cm_emit_plan(emitter, CMC_OP_ADD, 0);
  if (!lvalue) {
    [[cst::proof]] {
      thm lvalue_case =
          eqt_intro_rule(assume_rule(`lvalue__pre == 0i`));
      thm suffix = by_rewrite(
          `cm_expr_load_suffix (ty_:cm_type) (lvalue__pre:int) ==
           cm_load_code ty_`,
          THM_LIST(cm_expr_load_suffix_def, lvalue_case));
      rewrite_st(THM_LIST(suffix, get_theorem_by_name("APPEND")));
    }
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`model_ty`, `(ty_:cm_type)`)]]
    cm_emit_load_plan(emitter, expr->ty);
    [[cst::proof]] {
      thm shape = assume_rule(
          `e == CMIndexE (left_:cm_expr) (right_:cm_expr)
            (ty_:cm_type)`);
      thm lvalue_case =
          eqt_intro_rule(assume_rule(`lvalue__pre == 0i`));
      thm suffix = by_rewrite(
          `cm_expr_load_suffix (ty_:cm_type) (lvalue__pre:int) ==
           cm_load_code ty_`,
          THM_LIST(cm_expr_load_suffix_def, lvalue_case));
      thm code_shape = conv_rule(rewrite_conv(THM_LIST(suffix)),
          cm_index_code_shape(shape));
      code_shape = conv_rule(rewrite_conv(THM_LIST(
          gsym_rule(get_theorem_by_name("APPEND_ASSOC")),
          get_theorem_by_name("APPEND"),
          get_theorem_by_name("APPEND_NIL"))), code_shape);
      cm_restore_code_plan_end_st(code_shape);
    }
  } else {
    [[cst::proof]] {
      thm shape = assume_rule(
          `e == CMIndexE (left_:cm_expr) (right_:cm_expr)
            (ty_:cm_type)`);
      thm lvalue_case =
          eqf_intro_rule(assume_rule(`~(lvalue__pre == 0i)`));
      thm suffix = by_rewrite(
          `cm_expr_load_suffix (ty_:cm_type) (lvalue__pre:int) ==
           ([]:(tvm_inst)list)`,
          THM_LIST(cm_expr_load_suffix_def, lvalue_case));
      rewrite_st(THM_LIST(suffix, get_theorem_by_name("APPEND")));
      thm code_shape = conv_rule(rewrite_conv(THM_LIST(suffix)),
          cm_index_code_shape(shape));
      code_shape = conv_rule(rewrite_conv(THM_LIST(
          gsym_rule(get_theorem_by_name("APPEND_ASSOC")),
          get_theorem_by_name("APPEND"),
          get_theorem_by_name("APPEND_NIL"))), code_shape);
      cm_restore_code_plan_end_st(code_shape);
    }
  }
  [[cst::proof]] {
    thm shape = assume_rule(
        `e == CMIndexE (left_:cm_expr) (right_:cm_expr)
          (ty_:cm_type)`);
    cm_close_two_child_count_payload(shape);
    cm_close_expr_rep_st();
  }
}

PROOF static thm cm_lvalue_code_length_at(
    const term expr, const term pc, const term temp) {
  thm lengths = conjunct1_rule(
      spec_rule(expr, get_cm_expr_code_lengths()));
  thm result = specl_rule(TERM_LIST(
      `p:cm_program`, `fid__pre:int`, pc, temp), lengths);
  thm selection = by_rewrite(
      subst(TERM_PAIR_LIST(
        (term_pair){expr, `expr_:cm_expr`},
        (term_pair){pc, `pc_:int`},
        (term_pair){temp, `temp_:int`}),
        `cm_expr_code_for (p:cm_program) (fid__pre:int)
           (pc_:int) (temp_:int) (expr_:cm_expr) 1i ==
         cm_emit_lvalue p fid__pre pc_ temp_ expr_`),
      THM_LIST(cm_expr_code_for_def,
        eqf_intro_rule(int_arith_rule(`~(1i == 0i)`))));
  return conv_rule(rewrite_conv(THM_LIST(gsym_rule(selection))),
      result);
}

PROOF static void cm_add_assignment_temp_facts(
    const thm shape, const thm lvalue_case) {
  thm parent_shape = by_rewrite(
      `cm_expr_temps_for (e:cm_expr) (lvalue__pre:int) ==
       cm_imax (cm_ltemps (left_:cm_expr))
         (1i + cm_rtemps (right_:cm_expr))`,
      THM_LIST(cm_expr_temps_for_def, shape,
        get_cm_ltemps_def(), get_cm_rtemps_def(),
        get_cm_expr_tpair_def(), get_cm_tleft_def(),
        get_cm_tright_def(), lvalue_case));
  thm parent_bound = conv_rule(rewrite_conv(THM_LIST(
      parent_shape)), assume_rule(
        `(temp__pre:int) +
           cm_expr_temps_for (e:cm_expr) (lvalue__pre:int) <=
         (temp_limit__pre:int)`));
  thm left_nonnegative = conjunct1_rule(spec_rule(
      `left_:cm_expr`, cm_expr_temps_nonnegative));
  thm right_nonnegative = conjunct2_rule(spec_rule(
      `right_:cm_expr`, cm_expr_temps_nonnegative));
  thm left_max = specl_rule(TERM_LIST(
      `cm_ltemps (left_:cm_expr)`,
      `1i + cm_rtemps (right_:cm_expr)`),
      cm_imax_left_bound);
  thm right_max = specl_rule(TERM_LIST(
      `cm_ltemps (left_:cm_expr)`,
      `1i + cm_rtemps (right_:cm_expr)`),
      cm_imax_right_bound);
  thm left_bound = by_defs_arith(
      `(temp__pre:int) +
         cm_expr_temps_for (left_:cm_expr) 1i <=
       (temp_limit__pre:int)`,
      THM_LIST(cm_expr_temps_for_def),
      THM_LIST(parent_bound, left_max));
  thm right_bound = by_defs_arith(
      `(temp__pre:int) + 1i +
         cm_expr_temps_for (right_:cm_expr) 0i <=
       (temp_limit__pre:int)`,
      THM_LIST(cm_expr_temps_for_def),
      THM_LIST(parent_bound, right_max));
  add_fact_st(left_bound);
  add_fact_st(right_bound);
  add_fact_st(mp_rule(int_arith_rule(
      `0i <= (temp__pre:int) ==> 0i <= temp__pre + 1i`),
      assume_rule(`0i <= (temp__pre:int)`)));
  add_fact_st(mp_rule(mp_rule(int_arith_rule(
      `(temp__pre:int) + 1i +
         cm_rtemps (right_:cm_expr) <=
           (temp_limit__pre:int) ==>
       0i <= cm_rtemps right_ ==>
       temp__pre + 1i <= temp_limit__pre`),
      conv_rule(rewrite_conv(THM_LIST(cm_expr_temps_for_def)),
        right_bound)), right_nonnegative));
  cm_add_temp_offset_bound_st(`temp__pre:int`);
  cm_add_temp_offset_bound_st(`(temp__pre:int) + 1i`);
  {
    term params =
        `cm_function_params (f:cm_function_d)`;
    term locals =
        `cm_function_locals (f:cm_function_d)`;
    thm params_safe = from_state_bool(
        `cm_rep_members_safe
          (cm_function_params (f:cm_function_d))`);
    thm locals_safe = from_state_bool(
        `cm_rep_members_safe
          (cm_function_locals (f:cm_function_d))`);
    thm params_rep_nonnegative = mp_rule(
        spec_rule(params, cm_rep_members_size_nonnegative),
        params_safe);
    thm locals_rep_nonnegative = mp_rule(
        spec_rule(locals, cm_rep_members_size_nonnegative),
        locals_safe);
    thm params_match = mp_rule(specl_rule(TERM_LIST(
        `cm_program_structs (p:cm_program)`, params),
        cm_rep_members_size_matches), from_state_bool(
          `cm_slots_wf (cm_program_structs (p:cm_program))
            (cm_function_params (f:cm_function_d))`));
    thm locals_match = mp_rule(specl_rule(TERM_LIST(
        `cm_program_structs (p:cm_program)`, locals),
        cm_rep_members_size_matches), from_state_bool(
          `cm_slots_wf (cm_program_structs (p:cm_program))
            (cm_function_locals (f:cm_function_d))`));
    thm params_nonnegative = by_rewrite(
        `0i <= cm_slots_size (cm_program_structs (p:cm_program))
          (cm_function_params (f:cm_function_d))`,
        THM_LIST(sym_rule(params_match), params_rep_nonnegative));
    thm locals_nonnegative = by_rewrite(
        `0i <= cm_slots_size (cm_program_structs (p:cm_program))
          (cm_function_locals (f:cm_function_d))`,
        THM_LIST(sym_rule(locals_match), locals_rep_nonnegative));
    thm params_at_fid = conv_rule(rewrite_conv(THM_LIST(
        assume_rule(
          `(f:cm_function_d) ==
           inth (fid__pre:int) (cm_program_functions (p:cm_program))`))),
        params_nonnegative);
    thm locals_at_fid = conv_rule(rewrite_conv(THM_LIST(
        assume_rule(
          `(f:cm_function_d) ==
           inth (fid__pre:int) (cm_program_functions (p:cm_program))`))),
        locals_nonnegative);
    thm offset_bound = conv_rule(rewrite_conv(THM_LIST(
        get_cm_temp_offset_def())), assume_rule(
          `cm_temp_offset (p:cm_program) (fid__pre:int)
            ((temp__pre:int) + 1i) <= 2147483647i`));
    thm temp_upper = by_defs_arith(
        `(temp__pre:int) + 1i <= 2147483647i`,
        THM_LIST(get_cm_temp_offset_def()),
        THM_LIST(params_at_fid, locals_at_fid, offset_bound));
    thm temp_cast = mp_rule(mp_rule(spec_rule(
        `(temp__pre:int) + 1i`, cm_nonnegative_i32_cast),
        assume_rule(`0i <= (temp__pre:int) + 1i`)), temp_upper);
    add_fact_st(temp_upper);
    add_fact_st(temp_cast);
  }
  add_fact_st(left_nonnegative);
}

PROOF static void cm_add_assignment_pc_facts(
    const thm code_shape, const term fixed_suffix) {
  term left_code =
      `cm_expr_code_for (p:cm_program) (fid__pre:int)
         (pc__pre:int) (temp__pre:int) (left_:cm_expr) 1i`;
  term right_code =
      `cm_expr_code_for (p:cm_program) (fid__pre:int)
         ((pc__pre:int) +
           cm_lvalue_code_count p fid__pre left_ + 5i)
         ((temp__pre:int) + 1i) (right_:cm_expr) 0i`;
  term after_left = subst(TERM_PAIR_LIST(
      (term_pair){right_code, `right_code_:(tvm_inst)list`},
      (term_pair){fixed_suffix, `fixed_:(tvm_inst)list`}),
      `cm_temp_store_code (p:cm_program) (fid__pre:int)
         (temp__pre:int) ++ right_code_ ++ fixed_`);
  term after_store = subst(TERM_PAIR_LIST(
      (term_pair){right_code, `right_code_:(tvm_inst)list`},
      (term_pair){fixed_suffix, `fixed_:(tvm_inst)list`}),
      `(right_code_:(tvm_inst)list) ++
       (fixed_:(tvm_inst)list)`);
  thm parent_pc = conv_rule(
      rewrite_conv(THM_LIST(get_cm_i32_code_count_def())),
      eqt_elim_rule(assume_rule(
        `cm_i32_code_count (pc__pre:int) <=> true`)));
  thm parent_end = conv_rule(
      rewrite_conv(THM_LIST(get_cm_i32_code_count_def())),
      eqt_elim_rule(assume_rule(
        `cm_i32_code_count
          ((pc__pre:int) + ilength
            (cm_expr_code_for (p:cm_program) (fid__pre:int)
              pc__pre (temp__pre:int) (e:cm_expr) (lvalue__pre:int)))
         <=> true`)));
  thm left_length = cm_lvalue_code_length_at(
      `left_:cm_expr`, `pc__pre:int`, `temp__pre:int`);
  thm right_length = cm_rvalue_code_length_at(
      `right_:cm_expr`,
      `(pc__pre:int) +
        cm_lvalue_code_count (p:cm_program)
          (fid__pre:int) (left_:cm_expr) + 5i`,
      `(temp__pre:int) + 1i`);
  thm after_left_nonnegative = ispec_rule(
      after_left, get_theorem_by_name("ILENGTH_NONNEG"));
  thm fixed_nonnegative = ispec_rule(
      fixed_suffix, get_theorem_by_name("ILENGTH_NONNEG"));
  thm after_store_nonnegative = ispec_rule(
      after_store, get_theorem_by_name("ILENGTH_NONNEG"));
  thm left_nonnegative = ispec_rule(
      left_code, get_theorem_by_name("ILENGTH_NONNEG"));
  thm right_nonnegative = ispec_rule(
      right_code, get_theorem_by_name("ILENGTH_NONNEG"));
  thm_list rules = THM_LIST(
      get_cm_i32_code_count_def(), code_shape,
      get_theorem_by_name("ILENGTH_APPEND"),
      get_theorem_by_name("ILENGTH_DEF"),
      get_cm_temp_store_code_def(),
      get_cm_fp_relative_address_code_def(), left_length,
      right_length);
  thm parent_end_shape = conv_rule(rewrite_conv(rules), parent_end);
  thm after_left_nonnegative_shape =
      conv_rule(rewrite_conv(rules), after_left_nonnegative);
  thm fixed_nonnegative_shape =
      conv_rule(rewrite_conv(rules), fixed_nonnegative);
  thm after_store_nonnegative_shape =
      conv_rule(rewrite_conv(rules), after_store_nonnegative);
  thm right_nonnegative_shape =
      conv_rule(rewrite_conv(rules), right_nonnegative);
  thm left_end = by_defs_arith(
      `cm_i32_code_count
        ((pc__pre:int) + ilength
          (cm_expr_code_for (p:cm_program) (fid__pre:int)
            pc__pre (temp__pre:int) (left_:cm_expr) 1i))`,
      rules, THM_LIST(parent_pc, parent_end_shape,
        after_left_nonnegative_shape, left_nonnegative,
        left_length));
  thm right_start = by_defs_arith(
      `cm_i32_code_count
        ((pc__pre:int) +
          cm_lvalue_code_count (p:cm_program)
            (fid__pre:int) (left_:cm_expr) + 5i)`,
      rules, THM_LIST(parent_pc, parent_end_shape,
        after_store_nonnegative_shape, left_nonnegative,
        left_length));
  thm right_start_bounds = conv_rule(
      rewrite_conv(THM_LIST(get_cm_i32_code_count_def())),
      right_start);
  thm right_partial = by_defs_arith(
      `cm_i32_code_count
        ((pc__pre:int) +
          cm_lvalue_code_count (p:cm_program)
            (fid__pre:int) (left_:cm_expr))`,
      rules, THM_LIST(parent_pc, right_start_bounds,
        left_nonnegative, left_length));
  thm right_partial_bounds = conv_rule(
      rewrite_conv(THM_LIST(get_cm_i32_code_count_def())),
      right_partial);
  thm right_partial_cast = mp_rule(mp_rule(spec_rule(
      `(pc__pre:int) +
        cm_lvalue_code_count (p:cm_program)
          (fid__pre:int) (left_:cm_expr)`,
      cm_nonnegative_i32_cast), conjunct1_rule(right_partial_bounds)),
      conjunct2_rule(right_partial_bounds));
  thm right_start_cast = mp_rule(mp_rule(spec_rule(
      `(pc__pre:int) +
        cm_lvalue_code_count (p:cm_program)
          (fid__pre:int) (left_:cm_expr) + 5i`,
      cm_nonnegative_i32_cast), conjunct1_rule(right_start_bounds)),
      conjunct2_rule(right_start_bounds));
  thm left_increment_bounds = by_defs_arith(
      `0i <=
         cm_lvalue_code_count (p:cm_program)
           (fid__pre:int) (left_:cm_expr) + 5i &&
       cm_lvalue_code_count p fid__pre left_ + 5i <= 2147483647i`,
      rules, THM_LIST(parent_pc, right_start_bounds,
        left_nonnegative, left_length));
  thm left_increment_cast = mp_rule(mp_rule(spec_rule(
      `cm_lvalue_code_count (p:cm_program)
         (fid__pre:int) (left_:cm_expr) + 5i`,
      cm_nonnegative_i32_cast),
      conjunct1_rule(left_increment_bounds)),
      conjunct2_rule(left_increment_bounds));
  thm right_end = by_defs_arith(
      `cm_i32_code_count
        (((pc__pre:int) +
           cm_lvalue_code_count (p:cm_program)
             (fid__pre:int) (left_:cm_expr) + 5i) +
         ilength
           (cm_expr_code_for p fid__pre
             (pc__pre +
               cm_lvalue_code_count p fid__pre left_ + 5i)
             (temp__pre + 1i) (right_:cm_expr) 0i))`,
      rules, THM_LIST(parent_pc, right_start_bounds,
        parent_end_shape, fixed_nonnegative_shape,
        right_nonnegative_shape, left_length, right_length));
  add_fact_st(eqt_intro_rule(left_end));
  add_fact_st(eqt_intro_rule(right_start));
  add_fact_st(eqt_intro_rule(right_partial));
  add_fact_st(eqt_intro_rule(right_end));
  add_fact_st(conjunct1_rule(right_partial_bounds));
  add_fact_st(conjunct2_rule(right_partial_bounds));
  add_fact_st(conjunct1_rule(right_start_bounds));
  add_fact_st(conjunct2_rule(right_start_bounds));
  add_fact_st(conjunct1_rule(left_increment_bounds));
  add_fact_st(conjunct2_rule(left_increment_bounds));
  add_fact_st(right_partial_cast);
  add_fact_st(right_start_cast);
  add_fact_st(left_increment_cast);
}

static void cm_emit_assignment_expr(struct cm_program *program, int fid,
                                    struct cm_function *fn, int pc, int temp,
                                    int temp_limit, struct cm_expr *expr,
                                    int lvalue, struct cm_emitter *emitter)
    [[cst::param(`p:cm_program`, `f:cm_function_d`, `e:cm_expr`,
                 `left_:cm_expr`, `right_:cm_expr`, `ty_:cm_type`,
                 `body:int`, `next:int`, `functions_ptr:int`,
                 `done:(tvm_inst)list`, `tail:(tvm_inst)list`,
                 `out:int`, `capacity:int`)]]
    [[cst::require(
      `fact(e == CMAssignE left_ right_ ty_) **
       fact(0i <= lvalue) ** fact(lvalue <= 1i) **
       fact(cm_wf_program p <=> true) **
       fact(cm_typed_program p <=> true) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(cm_expr_wf p f e <=> true) **
       fact(cm_expr_counts_representable p fid e <=> true) **
       fact(cm_slots_wf (cm_program_structs p)
              (cm_function_params f) <=> true) **
       fact(cm_slots_wf (cm_program_structs p)
              (cm_function_locals f) <=> true) **
       fact(cm_rep_structs_safe (cm_program_structs p) <=> true) **
       fact(cm_rep_globals_safe (cm_program_globals p) <=> true) **
       fact(cm_rep_strings_safe (cm_program_strings p) <=> true) **
       fact(cm_rep_members_safe (cm_function_params f) <=> true) **
       fact(cm_rep_members_safe (cm_function_locals f) <=> true) **
       fact(cm_rep_globals_size (cm_program_globals p) +
              cm_rep_strings_size (cm_program_strings p) <= 1048560i) **
       fact(0i <= temp) ** fact(temp <= temp_limit) **
       fact(temp + cm_expr_temps_for e lvalue <= temp_limit) **
       fact(cm_temp_offset p fid temp_limit <= 2147483647i) **
       fact(cm_i32_code_count pc <=> true) **
       fact(cm_i32_code_count
              (pc + ilength (cm_expr_code_for p fid pc temp e lvalue))
              <=> true) **
       cm_program_context_rep program p functions_ptr **
       cm_function_context_rep fn f body next **
       cm_expr_rep expr e **
       cm_resolved_emitter_plan_rep p emitter out capacity done
         (cm_expr_code_for p fid pc temp e lvalue ++ tail)`)]]
    [[cst::ensure(
      `fact(e == CMAssignE left_ right_ ty_) **
       fact(0i <= lvalue) ** fact(lvalue <= 1i) **
       fact(cm_wf_program p <=> true) **
       fact(cm_typed_program p <=> true) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(cm_expr_wf p f e <=> true) **
       fact(cm_expr_counts_representable p fid e <=> true) **
       fact(cm_slots_wf (cm_program_structs p)
              (cm_function_params f) <=> true) **
       fact(cm_slots_wf (cm_program_structs p)
              (cm_function_locals f) <=> true) **
       fact(cm_rep_structs_safe (cm_program_structs p) <=> true) **
       fact(cm_rep_globals_safe (cm_program_globals p) <=> true) **
       fact(cm_rep_strings_safe (cm_program_strings p) <=> true) **
       fact(cm_rep_members_safe (cm_function_params f) <=> true) **
       fact(cm_rep_members_safe (cm_function_locals f) <=> true) **
       fact(cm_rep_globals_size (cm_program_globals p) +
              cm_rep_strings_size (cm_program_strings p) <= 1048560i) **
       fact(0i <= temp) ** fact(temp <= temp_limit) **
       fact(temp + cm_expr_temps_for e lvalue <= temp_limit) **
       fact(cm_temp_offset p fid temp_limit <= 2147483647i) **
       fact(cm_i32_code_count pc <=> true) **
       fact(cm_i32_code_count
              (pc + ilength (cm_expr_code_for p fid pc temp e lvalue))
              <=> true) **
       cm_program_context_rep program p functions_ptr **
       cm_function_context_rep fn f body next **
       cm_expr_rep expr e **
       cm_resolved_emitter_plan_rep p emitter out capacity
         (done ++ cm_expr_code_for p fid pc temp e lvalue) tail`)]]
{
  [[cst::proof]] {
    cm_open_expr_rep_st();
    thm shape = assume_rule(
        `e == CMAssignE (left_:cm_expr) (right_:cm_expr)
          (ty_:cm_type)`);
    add_fact_st(by_rewrite(
        `cm_type_encode (cm_expr_type (e:cm_expr)) ==
         cm_type_encode (ty_:cm_type)`,
        THM_LIST(shape, get_cm_expr_type_def())));
    cm_open_expr_count_facts(shape);
    cm_open_two_child_count_payload(shape);
    cm_add_expr_result_refs_st();
  }
  if (!lvalue) {
    [[cst::proof]] {
      thm shape = assume_rule(
          `e == CMAssignE (left_:cm_expr) (right_:cm_expr)
            (ty_:cm_type)`);
      thm lvalue_case =
          eqt_intro_rule(assume_rule(`lvalue__pre == 0i`));
      cm_add_assignment_temp_facts(shape, lvalue_case);
    }
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`f`, `(f:cm_function_d)`)]]
    [[cst::where(`e`, `(left_:cm_expr)`)]]
    [[cst::where(`fid`, `(fid__pre:int)`)]]
    int left_count = cm_expr_lvalue_count_context(
        program, fid, fn, expr->a);
    [[cst::proof]] {
      thm returned = assume_rule(
          `(retval:int) ==
           cm_lcount_of
             (cm_expr_code_counts (p:cm_program)
               (fid__pre:int) (left_:cm_expr))`);
      thm model = conv_rule(rewrite_conv(THM_LIST(
          gsym_rule(get_cm_lvalue_code_count_def()))), returned);
      add_fact_st(model);
      cst_set_symbolic_state(retarget_cell_st(
          cst_get_symbolic_state(), `left_count__addr:addr`,
          `retval:int`,
          `cm_lvalue_code_count (p:cm_program)
            (fid__pre:int) (left_:cm_expr)`));
    }
    [[cst::proof]] {
      thm shape = assume_rule(
          `e == CMAssignE (left_:cm_expr) (right_:cm_expr)
            (ty_:cm_type)`);
      thm lvalue_case =
          eqt_intro_rule(assume_rule(`lvalue__pre == 0i`));
      thm code_shape = cm_selected_expr_code_shape(
          shape, lvalue_case,
          `cm_expr_code_for (p:cm_program) (fid__pre:int)
             (pc__pre:int) (temp__pre:int) (left_:cm_expr) 1i ++
           cm_temp_store_code p fid__pre temp__pre ++
           cm_expr_code_for p fid__pre
             (pc__pre +
               cm_lvalue_code_count p fid__pre left_ + 5i)
             (temp__pre + 1i) (right_:cm_expr) 0i ++
           cm_char_normalize_code (ty_:cm_type) ++
           cm_temp_load_code p fid__pre temp__pre ++
           cm_store_code ty_ ++
           cm_temp_load_code p fid__pre temp__pre ++
           cm_load_code ty_`);
      cm_add_assignment_pc_facts(code_shape,
          `cm_char_normalize_code (ty_:cm_type) ++
           cm_temp_load_code (p:cm_program) (fid__pre:int)
             (temp__pre:int) ++
           cm_store_code ty_ ++
           cm_temp_load_code p fid__pre temp__pre ++
           cm_load_code ty_`);
      cm_select_code_plan_st(code_shape);
    }
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`f`, `(f:cm_function_d)`)]]
    [[cst::where(`fid`, `(fid__pre:int)`)]]
    cm_emit_expr(program, fid, fn, pc, temp, temp_limit,
                 expr->a, 1, emitter);
    [[cst::proof]] {
      rewrite_st(THM_LIST(get_theorem_by_name("APPEND")));
    }
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`f`, `(f:cm_function_d)`)]]
    [[cst::where(`fid`, `(fid__pre:int)`)]]
    [[cst::where(`structs`, `cm_program_structs (p:cm_program)`)]]
    cm_emit_temp_store_plan(fn, temp, emitter);
    [[cst::proof]] {
      rewrite_st(THM_LIST(get_theorem_by_name("APPEND")));
    }
    int right_pc = pc + (left_count + 5);
    int right_temp = temp + 1;
    struct cm_expr *right_expr = expr->b;
    [[cst::proof]] {
      term child_tail =
          `cm_char_normalize_code (ty_:cm_type) ++
           cm_temp_load_code (p:cm_program) (fid__pre:int)
             (temp__pre:int) ++
           cm_store_code ty_ ++
           cm_temp_load_code p fid__pre temp__pre ++
           cm_load_code ty_ ++ (tail:(tvm_inst)list)`;
      term child_done =
          `((done:(tvm_inst)list) ++
              cm_expr_code_for (p:cm_program) (fid__pre:int)
                (pc__pre:int) (temp__pre:int)
                (left_:cm_expr) 1i) ++
            cm_temp_store_code p fid__pre temp__pre`;
      term child_resources =
          `cm_program_context_rep (program__pre:int) (p:cm_program)
             (functions_ptr:int) **
           cm_function_context_rep (fn__pre:int) (f:cm_function_d)
             (body:int) (next:int) **
           cm_expr_rep (zb:int) (right_:cm_expr) **
           cm_resolved_emitter_plan_rep p (emitter__pre:int)
             (out:int) (capacity:int) child_done_
             (cm_expr_code_for p (fid__pre:int)
                (pc__pre +
                  cm_lvalue_code_count p fid__pre
                    (left_:cm_expr) + 5i)
                ((temp__pre:int) + 1i) right_ 0i ++ child_tail_)`;
      child_resources = subst(TERM_PAIR_LIST(
          (term_pair){child_done, `child_done_:(tvm_inst)list`},
          (term_pair){child_tail, `child_tail_:(tvm_inst)list`}),
          child_resources);
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          refl_slrule(child_resources)));
    }
    [[cst::proof]] {
      add_fact_st(int_arith_rule(`0i <= (0i:int)`));
      term child_facts =
          `fact(0i <= 0i) **
           fact(0i <= 1i) **
           fact(cm_wf_program (p:cm_program) <=> true) **
           fact(cm_typed_program p <=> true) **
           fact((f:cm_function_d) ==
             inth (fid__pre:int) (cm_program_functions p)) **
           fact(cm_expr_wf p f (right_:cm_expr) <=> true) **
           fact(cm_expr_counts_representable p fid__pre right_
             <=> true) **
           fact(cm_slots_wf (cm_program_structs p)
             (cm_function_params f) <=> true) **
           fact(cm_slots_wf (cm_program_structs p)
             (cm_function_locals f) <=> true) **
           fact(cm_rep_structs_safe (cm_program_structs p) <=> true) **
           fact(cm_rep_globals_safe (cm_program_globals p) <=> true) **
           fact(cm_rep_strings_safe (cm_program_strings p) <=> true) **
           fact(cm_rep_members_safe (cm_function_params f) <=> true) **
           fact(cm_rep_members_safe (cm_function_locals f) <=> true) **
           fact(cm_rep_globals_size (cm_program_globals p) +
             cm_rep_strings_size (cm_program_strings p) <= 1048560i) **
           fact(0i <= (temp__pre:int) + 1i) **
           fact(temp__pre + 1i <= (temp_limit__pre:int)) **
           fact(temp__pre + 1i +
             cm_expr_temps_for (right_:cm_expr) 0i <= temp_limit__pre) **
           fact(cm_temp_offset p (fid__pre:int) (temp_limit__pre:int)
             <= 2147483647i) **
           fact(cm_i32_code_count
             ((pc__pre:int) +
              cm_lvalue_code_count p fid__pre
                (left_:cm_expr) + 5i)
             <=> true) **
           fact(cm_i32_code_count
             ((pc__pre +
               cm_lvalue_code_count p fid__pre left_ + 5i) +
              ilength
                (cm_expr_code_for p fid__pre
                  (pc__pre +
                    cm_lvalue_code_count p fid__pre left_ + 5i)
                  (temp__pre + 1i) right_ 0i))
             <=> true)`;
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          refl_slrule(child_facts)));
    }
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`f`, `(f:cm_function_d)`)]]
    [[cst::where(`fid`, `(fid__pre:int)`)]]
    [[cst::where(`e`, `(right_:cm_expr)`)]]
    [[cst::where(`body`, `(body:int)`)]]
    [[cst::where(`next`, `(next:int)`)]]
    [[cst::where(`functions_ptr`, `(functions_ptr:int)`)]]
    [[cst::where(`out`, `(out:int)`)]]
    [[cst::where(`capacity`, `(capacity:int)`)]]
    [[cst::where(`done`,
        `((done:(tvm_inst)list) ++
            cm_expr_code_for (p:cm_program) (fid__pre:int)
              (pc__pre:int) (temp__pre:int) (left_:cm_expr) 1i) ++
          cm_temp_store_code p fid__pre temp__pre`)]]
    [[cst::where(`tail`,
        `cm_char_normalize_code (ty_:cm_type) ++
         cm_temp_load_code (p:cm_program) (fid__pre:int)
           (temp__pre:int) ++
         cm_store_code ty_ ++
         cm_temp_load_code p fid__pre temp__pre ++
         cm_load_code ty_ ++ (tail:(tvm_inst)list)`)]]
    cm_emit_expr(program, fid, fn, right_pc, right_temp, temp_limit,
                 right_expr, 0, emitter);
    [[cst::proof]] {
      rewrite_st(THM_LIST(get_theorem_by_name("APPEND")));
    }
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`model_ty`, `(ty_:cm_type)`)]]
    cm_emit_normalize_plan(emitter, expr->ty);
    [[cst::proof]] {
      rewrite_st(THM_LIST(get_theorem_by_name("APPEND")));
    }
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`f`, `(f:cm_function_d)`)]]
    [[cst::where(`fid`, `(fid__pre:int)`)]]
    [[cst::where(`structs`, `cm_program_structs (p:cm_program)`)]]
    cm_emit_temp_load_plan(fn, temp, emitter);
    [[cst::proof]] {
      rewrite_st(THM_LIST(get_theorem_by_name("APPEND")));
    }
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`model_ty`, `(ty_:cm_type)`)]]
    cm_emit_store_plan(emitter, expr->ty);
    [[cst::proof]] {
      rewrite_st(THM_LIST(get_theorem_by_name("APPEND")));
    }
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`f`, `(f:cm_function_d)`)]]
    [[cst::where(`fid`, `(fid__pre:int)`)]]
    [[cst::where(`structs`, `cm_program_structs (p:cm_program)`)]]
    cm_emit_temp_load_plan(fn, temp, emitter);
    [[cst::proof]] {
      rewrite_st(THM_LIST(get_theorem_by_name("APPEND")));
    }
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`model_ty`, `(ty_:cm_type)`)]]
    cm_emit_load_plan(emitter, expr->ty);
    [[cst::proof]] {
      thm shape = assume_rule(
          `e == CMAssignE (left_:cm_expr) (right_:cm_expr)
            (ty_:cm_type)`);
      thm lvalue_case =
          eqt_intro_rule(assume_rule(`lvalue__pre == 0i`));
      thm code_shape = cm_selected_expr_code_shape(
          shape, lvalue_case,
          `cm_expr_code_for (p:cm_program) (fid__pre:int)
             (pc__pre:int) (temp__pre:int) (left_:cm_expr) 1i ++
           cm_temp_store_code p fid__pre temp__pre ++
           cm_expr_code_for p fid__pre
             (pc__pre +
               cm_lvalue_code_count p fid__pre left_ + 5i)
             (temp__pre + 1i) (right_:cm_expr) 0i ++
           cm_char_normalize_code (ty_:cm_type) ++
           cm_temp_load_code p fid__pre temp__pre ++
           cm_store_code ty_ ++
           cm_temp_load_code p fid__pre temp__pre ++
           cm_load_code ty_`);
      code_shape = conv_rule(rewrite_conv(THM_LIST(
          gsym_rule(get_theorem_by_name("APPEND_ASSOC")),
          get_theorem_by_name("APPEND"),
          get_theorem_by_name("APPEND_NIL"))), code_shape);
      cm_restore_code_plan_end_st(code_shape);
    }
  } else {
    [[cst::proof]] {
      thm shape = assume_rule(
          `e == CMAssignE (left_:cm_expr) (right_:cm_expr)
            (ty_:cm_type)`);
      thm lvalue_case =
          eqf_intro_rule(assume_rule(`~(lvalue__pre == 0i)`));
      thm code_shape = cm_selected_expr_code_shape(
          shape, lvalue_case, `[]:(tvm_inst)list`);
      cm_empty_code_plan_end_st(code_shape);
    }
  }
  [[cst::proof]] {
    thm shape = assume_rule(
        `e == CMAssignE (left_:cm_expr) (right_:cm_expr)
          (ty_:cm_type)`);
    cm_close_two_child_count_payload(shape);
    cm_close_expr_rep_st();
  }
}

PROOF static thm cm_binary_code_shape(const thm shape,
                                      const thm lvalue_case,
                                      const thm short_case,
                                      const term code) {
  return cm_unary_code_shape(shape, lvalue_case,
      THM_LIST(short_case), code);
}

PROOF static void cm_add_binary_ordinary_temp_facts(const thm shape,
                                                     const thm short_case,
                                                     const thm lvalue_case) {
  thm parent_shape = by_rewrite(
      `cm_expr_temps_for (e:cm_expr) (lvalue__pre:int) ==
       cm_imax (cm_rtemps (left_:cm_expr))
         (1i + cm_rtemps (right_:cm_expr))`,
      THM_LIST(cm_expr_temps_for_def, shape,
        get_cm_ltemps_def(), get_cm_rtemps_def(),
        get_cm_expr_tpair_def(), get_cm_tleft_def(),
        get_cm_tright_def(), short_case, lvalue_case));
  thm parent_bound = conv_rule(rewrite_conv(THM_LIST(parent_shape)),
      assume_rule(
        `(temp__pre:int) +
           cm_expr_temps_for (e:cm_expr) (lvalue__pre:int) <=
         (temp_limit__pre:int)`));
  thm left_nonnegative = conjunct2_rule(spec_rule(
      `left_:cm_expr`, cm_expr_temps_nonnegative));
  thm right_nonnegative = conjunct2_rule(spec_rule(
      `right_:cm_expr`, cm_expr_temps_nonnegative));
  thm left_max = specl_rule(TERM_LIST(
      `cm_rtemps (left_:cm_expr)`,
      `1i + cm_rtemps (right_:cm_expr)`), cm_imax_left_bound);
  thm right_max = specl_rule(TERM_LIST(
      `cm_rtemps (left_:cm_expr)`,
      `1i + cm_rtemps (right_:cm_expr)`), cm_imax_right_bound);
  thm left_bound = by_defs_arith(
      `(temp__pre:int) +
         cm_expr_temps_for (left_:cm_expr) 0i <=
       (temp_limit__pre:int)`,
      THM_LIST(cm_expr_temps_for_def),
      THM_LIST(parent_bound, left_max));
  thm right_bound = by_defs_arith(
      `(temp__pre:int) + 1i +
         cm_expr_temps_for (right_:cm_expr) 0i <=
       (temp_limit__pre:int)`,
      THM_LIST(cm_expr_temps_for_def),
      THM_LIST(parent_bound, right_max));
  add_fact_st(left_bound);
  add_fact_st(right_bound);
  add_fact_st(mp_rule(int_arith_rule(
      `0i <= (temp__pre:int) ==> 0i <= temp__pre + 1i`),
      assume_rule(`0i <= (temp__pre:int)`)));
  add_fact_st(mp_rule(mp_rule(int_arith_rule(
      `(temp__pre:int) + 1i +
         cm_rtemps (right_:cm_expr) <=
           (temp_limit__pre:int) ==>
       0i <= cm_rtemps right_ ==>
       temp__pre + 1i <= temp_limit__pre`),
      conv_rule(rewrite_conv(THM_LIST(cm_expr_temps_for_def)),
        right_bound)), right_nonnegative));
  cm_add_temp_offset_bound_st(`temp__pre:int`);
  cm_add_temp_offset_bound_st(`(temp__pre:int) + 1i`);
  {
    term params = `cm_function_params (f:cm_function_d)`;
    term locals = `cm_function_locals (f:cm_function_d)`;
    thm params_safe = from_state_bool(
        `cm_rep_members_safe (cm_function_params (f:cm_function_d))`);
    thm locals_safe = from_state_bool(
        `cm_rep_members_safe (cm_function_locals (f:cm_function_d))`);
    thm params_rep_nonnegative = mp_rule(
        spec_rule(params, cm_rep_members_size_nonnegative), params_safe);
    thm locals_rep_nonnegative = mp_rule(
        spec_rule(locals, cm_rep_members_size_nonnegative), locals_safe);
    thm params_match = mp_rule(specl_rule(TERM_LIST(
        `cm_program_structs (p:cm_program)`, params),
        cm_rep_members_size_matches), from_state_bool(
          `cm_slots_wf (cm_program_structs (p:cm_program))
            (cm_function_params (f:cm_function_d))`));
    thm locals_match = mp_rule(specl_rule(TERM_LIST(
        `cm_program_structs (p:cm_program)`, locals),
        cm_rep_members_size_matches), from_state_bool(
          `cm_slots_wf (cm_program_structs (p:cm_program))
            (cm_function_locals (f:cm_function_d))`));
    thm params_nonnegative = by_rewrite(
        `0i <= cm_slots_size (cm_program_structs (p:cm_program))
          (cm_function_params (f:cm_function_d))`,
        THM_LIST(sym_rule(params_match), params_rep_nonnegative));
    thm locals_nonnegative = by_rewrite(
        `0i <= cm_slots_size (cm_program_structs (p:cm_program))
          (cm_function_locals (f:cm_function_d))`,
        THM_LIST(sym_rule(locals_match), locals_rep_nonnegative));
    thm params_at_fid = conv_rule(rewrite_conv(THM_LIST(assume_rule(
        `(f:cm_function_d) ==
         inth (fid__pre:int) (cm_program_functions (p:cm_program))`))),
        params_nonnegative);
    thm locals_at_fid = conv_rule(rewrite_conv(THM_LIST(assume_rule(
        `(f:cm_function_d) ==
         inth (fid__pre:int) (cm_program_functions (p:cm_program))`))),
        locals_nonnegative);
    thm offset_bound = conv_rule(rewrite_conv(THM_LIST(
        get_cm_temp_offset_def())), assume_rule(
          `cm_temp_offset (p:cm_program) (fid__pre:int)
            ((temp__pre:int) + 1i) <= 2147483647i`));
    thm temp_upper = by_defs_arith(
        `(temp__pre:int) + 1i <= 2147483647i`,
        THM_LIST(get_cm_temp_offset_def()),
        THM_LIST(params_at_fid, locals_at_fid, offset_bound));
    thm temp_cast = mp_rule(mp_rule(spec_rule(
        `(temp__pre:int) + 1i`, cm_nonnegative_i32_cast),
        assume_rule(`0i <= (temp__pre:int) + 1i`)), temp_upper);
    add_fact_st(temp_upper);
    add_fact_st(temp_cast);
  }
  add_fact_st(left_nonnegative);
}

PROOF static void cm_add_binary_short_temp_facts(const thm shape,
                                                  const thm short_case,
                                                  const thm lvalue_case) {
  thm parent_shape = by_rewrite(
      `cm_expr_temps_for (e:cm_expr) (lvalue__pre:int) ==
       cm_imax (cm_rtemps (left_:cm_expr))
         (cm_rtemps (right_:cm_expr))`,
      THM_LIST(cm_expr_temps_for_def, shape,
        get_cm_ltemps_def(), get_cm_rtemps_def(),
        get_cm_expr_tpair_def(), get_cm_tleft_def(),
        get_cm_tright_def(), short_case, lvalue_case));
  thm parent_bound = conv_rule(rewrite_conv(THM_LIST(parent_shape)),
      assume_rule(
        `(temp__pre:int) +
           cm_expr_temps_for (e:cm_expr) (lvalue__pre:int) <=
         (temp_limit__pre:int)`));
  thm left_max = specl_rule(TERM_LIST(
      `cm_rtemps (left_:cm_expr)`, `cm_rtemps (right_:cm_expr)`),
      cm_imax_left_bound);
  thm right_max = specl_rule(TERM_LIST(
      `cm_rtemps (left_:cm_expr)`, `cm_rtemps (right_:cm_expr)`),
      cm_imax_right_bound);
  add_fact_st(by_defs_arith(
      `(temp__pre:int) +
         cm_expr_temps_for (left_:cm_expr) 0i <=
       (temp_limit__pre:int)`,
      THM_LIST(cm_expr_temps_for_def),
      THM_LIST(parent_bound, left_max)));
  add_fact_st(by_defs_arith(
      `(temp__pre:int) +
         cm_expr_temps_for (right_:cm_expr) 0i <=
       (temp_limit__pre:int)`,
      THM_LIST(cm_expr_temps_for_def),
      THM_LIST(parent_bound, right_max)));
}

PROOF static void cm_add_binary_short_pc_facts(const thm code_shape) {
  term left_code =
      `cm_expr_code_for (p:cm_program) (fid__pre:int)
         (pc__pre:int) (temp__pre:int) (left_:cm_expr) 0i`;
  term right_code =
      `cm_expr_code_for (p:cm_program) (fid__pre:int)
         ((pc__pre:int) +
           (cm_rvalue_code_count p fid__pre (left_:cm_expr) + 1i))
         (temp__pre:int) (right_:cm_expr) 0i`;
  thm parent_pc = conv_rule(
      rewrite_conv(THM_LIST(get_cm_i32_code_count_def())),
      eqt_elim_rule(assume_rule(
        `cm_i32_code_count (pc__pre:int) <=> true`)));
  thm parent_end = conv_rule(
      rewrite_conv(THM_LIST(get_cm_i32_code_count_def())),
      eqt_elim_rule(assume_rule(
        `cm_i32_code_count
          ((pc__pre:int) + ilength
            (cm_expr_code_for (p:cm_program) (fid__pre:int)
              pc__pre (temp__pre:int) (e:cm_expr) (lvalue__pre:int)))
         <=> true`)));
  thm left_length = cm_rvalue_code_length_at(
      `left_:cm_expr`, `pc__pre:int`, `temp__pre:int`);
  thm right_length = cm_rvalue_code_length_at(
      `right_:cm_expr`,
      `(pc__pre:int) +
        (cm_rvalue_code_count (p:cm_program)
          (fid__pre:int) (left_:cm_expr) + 1i)`,
      `temp__pre:int`);
  thm left_nonnegative = ispec_rule(
      left_code, get_theorem_by_name("ILENGTH_NONNEG"));
  thm right_nonnegative = ispec_rule(
      right_code, get_theorem_by_name("ILENGTH_NONNEG"));
  thm_list rules = THM_LIST(
      get_cm_i32_code_count_def(), code_shape,
      get_theorem_by_name("ILENGTH_APPEND"),
      get_theorem_by_name("ILENGTH_DEF"),
      left_length, right_length);
  thm parent_end_shape = conv_rule(rewrite_conv(rules), parent_end);
  thm left_nonnegative_shape = conv_rule(
      rewrite_conv(rules), left_nonnegative);
  thm right_nonnegative_shape = conv_rule(
      rewrite_conv(rules), right_nonnegative);
  thm left_end = by_defs_arith(
      `cm_i32_code_count
        ((pc__pre:int) + ilength
          (cm_expr_code_for (p:cm_program) (fid__pre:int)
            pc__pre (temp__pre:int) (left_:cm_expr) 0i))`,
      rules, THM_LIST(parent_pc, parent_end_shape,
        left_nonnegative_shape, right_nonnegative_shape,
        left_length, right_length));
  thm right_start = by_defs_arith(
      `cm_i32_code_count
        ((pc__pre:int) +
         (cm_rvalue_code_count (p:cm_program)
           (fid__pre:int) (left_:cm_expr) + 1i))`,
      rules, THM_LIST(parent_pc, parent_end_shape,
        left_nonnegative_shape, right_nonnegative_shape,
        left_length, right_length));
  thm right_end = by_defs_arith(
      `cm_i32_code_count
        (((pc__pre:int) +
          (cm_rvalue_code_count (p:cm_program)
            (fid__pre:int) (left_:cm_expr) + 1i)) +
         ilength
           (cm_expr_code_for p fid__pre
             (pc__pre +
              (cm_rvalue_code_count p fid__pre left_ + 1i))
             (temp__pre:int) (right_:cm_expr) 0i))`,
      rules, THM_LIST(parent_pc, parent_end_shape,
        left_nonnegative_shape, right_nonnegative_shape,
        left_length, right_length));
  thm first_target = by_defs_arith(
      `cm_i32_code_count
        ((pc__pre:int) +
         (cm_rvalue_code_count (p:cm_program) fid__pre left_ +
          (cm_rvalue_code_count p fid__pre (right_:cm_expr) + 4i)))`,
      rules, THM_LIST(parent_pc, parent_end_shape,
        left_nonnegative_shape, right_nonnegative_shape,
        left_length, right_length));
  thm final_target = by_defs_arith(
      `cm_i32_code_count
        ((pc__pre:int) +
         (cm_rvalue_code_count (p:cm_program) fid__pre left_ +
          (cm_rvalue_code_count p fid__pre (right_:cm_expr) + 5i)))`,
      rules, THM_LIST(parent_pc, parent_end_shape,
        left_nonnegative_shape, right_nonnegative_shape,
        left_length, right_length));
  thm first_target_bounds = conv_rule(
      rewrite_conv(THM_LIST(get_cm_i32_code_count_def())),
      first_target);
  thm final_target_bounds = conv_rule(
      rewrite_conv(THM_LIST(get_cm_i32_code_count_def())),
      final_target);
  thm first_right_bounds = by_defs_arith(
      `0i <=
         cm_rvalue_code_count (p:cm_program) (fid__pre:int)
           (right_:cm_expr) + 4i &&
       cm_rvalue_code_count p fid__pre right_ + 4i <= 2147483647i`,
      rules, THM_LIST(first_target_bounds, parent_pc,
        left_nonnegative_shape, right_nonnegative_shape,
        left_length, right_length));
  thm first_middle_bounds = by_defs_arith(
      `0i <=
         cm_rvalue_code_count (p:cm_program) (fid__pre:int)
           (left_:cm_expr) +
         (cm_rvalue_code_count p fid__pre (right_:cm_expr) + 4i) &&
       cm_rvalue_code_count p fid__pre left_ +
         (cm_rvalue_code_count p fid__pre right_ + 4i) <=
         2147483647i`,
      rules, THM_LIST(first_target_bounds, parent_pc,
        left_nonnegative_shape, right_nonnegative_shape,
        left_length, right_length));
  thm final_right_bounds = by_defs_arith(
      `0i <=
         cm_rvalue_code_count (p:cm_program) (fid__pre:int)
           (right_:cm_expr) + 5i &&
       cm_rvalue_code_count p fid__pre right_ + 5i <= 2147483647i`,
      rules, THM_LIST(final_target_bounds, parent_pc,
        left_nonnegative_shape, right_nonnegative_shape,
        left_length, right_length));
  thm final_middle_bounds = by_defs_arith(
      `0i <=
         cm_rvalue_code_count (p:cm_program) (fid__pre:int)
           (left_:cm_expr) +
         (cm_rvalue_code_count p fid__pre (right_:cm_expr) + 5i) &&
       cm_rvalue_code_count p fid__pre left_ +
         (cm_rvalue_code_count p fid__pre right_ + 5i) <=
         2147483647i`,
      rules, THM_LIST(final_target_bounds, parent_pc,
        left_nonnegative_shape, right_nonnegative_shape,
        left_length, right_length));
  add_fact_st(eqt_intro_rule(left_end));
  add_fact_st(eqt_intro_rule(right_start));
  add_fact_st(eqt_intro_rule(right_end));
  add_fact_st(eqt_intro_rule(first_target));
  add_fact_st(eqt_intro_rule(final_target));
  add_fact_st(conjunct1_rule(first_target_bounds));
  add_fact_st(conjunct2_rule(first_target_bounds));
  add_fact_st(conjunct1_rule(first_right_bounds));
  add_fact_st(conjunct2_rule(first_right_bounds));
  add_fact_st(conjunct1_rule(first_middle_bounds));
  add_fact_st(conjunct2_rule(first_middle_bounds));
  add_fact_st(conjunct1_rule(final_target_bounds));
  add_fact_st(conjunct2_rule(final_target_bounds));
  add_fact_st(conjunct1_rule(final_right_bounds));
  add_fact_st(conjunct2_rule(final_right_bounds));
  add_fact_st(conjunct1_rule(final_middle_bounds));
  add_fact_st(conjunct2_rule(final_middle_bounds));
  {
    thm right_start_bounds = conv_rule(
        rewrite_conv(THM_LIST(get_cm_i32_code_count_def())), right_start);
    thm right_start_cast = mp_rule(mp_rule(spec_rule(
        `(pc__pre:int) +
         (cm_rvalue_code_count (p:cm_program) fid__pre left_ + 1i)`,
        cm_nonnegative_i32_cast), conjunct1_rule(right_start_bounds)),
        conjunct2_rule(right_start_bounds));
    thm increment_bounds = by_defs_arith(
        `0i <= cm_rvalue_code_count (p:cm_program)
                   (fid__pre:int) (left_:cm_expr) + 1i &&
         cm_rvalue_code_count p fid__pre left_ + 1i <= 2147483647i`,
        rules, THM_LIST(parent_pc, right_start_bounds,
          left_nonnegative_shape, left_length));
    thm increment_cast = mp_rule(mp_rule(spec_rule(
        `cm_rvalue_code_count (p:cm_program)
           (fid__pre:int) (left_:cm_expr) + 1i`,
        cm_nonnegative_i32_cast), conjunct1_rule(increment_bounds)),
        conjunct2_rule(increment_bounds));
    add_fact_st(conjunct1_rule(right_start_bounds));
    add_fact_st(conjunct2_rule(right_start_bounds));
    add_fact_st(conjunct1_rule(increment_bounds));
    add_fact_st(conjunct2_rule(increment_bounds));
    add_fact_st(right_start_cast);
    add_fact_st(increment_cast);
  }
}

PROOF static thm cm_binary_short_code_shape(const thm shape,
                                             const thm lvalue_case,
                                             const thm short_case) {
  return cm_binary_code_shape(
      shape, lvalue_case, short_case,
      `cm_expr_code_for (p:cm_program) (fid__pre:int)
         (pc__pre:int) (temp__pre:int) (left_:cm_expr) 0i ++
       [TVMInst
          (if (op_:int) == 0i then TVMJnzOp else TVMJzOp)
          (pc__pre +
            (cm_rvalue_code_count p fid__pre left_ +
             (cm_rvalue_code_count p fid__pre
               (right_:cm_expr) + 4i)))] ++
       cm_expr_code_for p fid__pre
         (pc__pre +
          (cm_rvalue_code_count p fid__pre left_ + 1i))
         temp__pre right_ 0i ++
       [TVMInst TVMPushOp 0i;
        TVMInst TVMNeOp 0i;
        TVMInst TVMJmpOp
          (pc__pre +
            (cm_rvalue_code_count p fid__pre left_ +
             (cm_rvalue_code_count p fid__pre right_ + 5i)));
        TVMInst TVMPushOp
          (if op_ == 0i then 1i else 0i)]`);
}

PROOF static void cm_prepare_binary_short_st(const thm shape,
                                              const thm lvalue_case,
                                              const thm short_case,
                                              const thm or_case) {
  thm code_shape =
      cm_binary_short_code_shape(shape, lvalue_case, short_case);
  code_shape = conv_rule(
      reduce_rewrite_conv(THM_LIST(or_case)), code_shape);
  cm_add_binary_short_temp_facts(shape, short_case, lvalue_case);
  cm_add_binary_short_pc_facts(code_shape);
  cm_select_code_plan_st(code_shape);
}

PROOF static void cm_restore_binary_short_st(const thm shape,
                                              const thm lvalue_case,
                                              const thm short_case,
                                              const thm or_case) {
  thm code_shape =
      cm_binary_short_code_shape(shape, lvalue_case, short_case);
  code_shape = conv_rule(
      reduce_rewrite_conv(THM_LIST(or_case)), code_shape);
  code_shape = conv_rule(rewrite_conv(THM_LIST(
      gsym_rule(get_theorem_by_name("APPEND_ASSOC")),
      get_theorem_by_name("APPEND"),
      get_theorem_by_name("APPEND_NIL"))), code_shape);
  cm_restore_code_plan_end_st(code_shape);
}

PROOF static void cm_select_binary_short_right_st(
    const term branch_opcode, const term short_value) {
  term child_tail =
      `TVMInst TVMPushOp 0i ::
       TVMInst TVMNeOp 0i ::
       TVMInst TVMJmpOp
         ((pc__pre:int) +
           (cm_rvalue_code_count (p:cm_program)
              (fid__pre:int) (left_:cm_expr) +
            (cm_rvalue_code_count p fid__pre
              (right_:cm_expr) + 5i))) ::
       TVMInst TVMPushOp short_value_ ::
       (tail:(tvm_inst)list)`;
  term child_done =
      `((done:(tvm_inst)list) ++
          cm_expr_code_for (p:cm_program) (fid__pre:int)
            (pc__pre:int) (temp__pre:int)
            (left_:cm_expr) 0i) ++
        [TVMInst branch_opcode_
           (pc__pre +
             (cm_rvalue_code_count p fid__pre left_ +
              (cm_rvalue_code_count p fid__pre
                (right_:cm_expr) + 4i)))]`;
  child_tail = subst(TERM_PAIR_LIST(
      (term_pair){branch_opcode, `branch_opcode_:tvm_opcode`},
      (term_pair){short_value, `short_value_:int`}), child_tail);
  child_done = subst(TERM_PAIR_LIST(
      (term_pair){branch_opcode, `branch_opcode_:tvm_opcode`}),
      child_done);
  term child_resources =
      `cm_program_context_rep (program__pre:int) (p:cm_program)
         (functions_ptr:int) **
       cm_function_context_rep (fn__pre:int) (f:cm_function_d)
         (body:int) (next:int) **
       cm_expr_rep (zb:int) (right_:cm_expr) **
       cm_resolved_emitter_plan_rep p (emitter__pre:int)
         (out:int) (capacity:int) child_done_
         (cm_expr_code_for p (fid__pre:int)
            ((pc__pre:int) +
              (cm_rvalue_code_count p fid__pre
                (left_:cm_expr) + 1i))
            (temp__pre:int) right_ 0i ++ child_tail_)`;
  child_resources = subst(TERM_PAIR_LIST(
      (term_pair){child_done, `child_done_:(tvm_inst)list`},
      (term_pair){child_tail, `child_tail_:(tvm_inst)list`}),
      child_resources);
  cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
      refl_slrule(child_resources)));

  term child_facts =
      `fact(0i <= 0i) ** fact(0i <= 1i) **
       fact(cm_wf_program (p:cm_program) <=> true) **
       fact(cm_typed_program p <=> true) **
       fact((f:cm_function_d) ==
         inth (fid__pre:int) (cm_program_functions p)) **
       fact(cm_expr_wf p f (right_:cm_expr) <=> true) **
       fact(cm_expr_counts_representable p fid__pre right_
         <=> true) **
       fact(cm_slots_wf (cm_program_structs p)
         (cm_function_params f) <=> true) **
       fact(cm_slots_wf (cm_program_structs p)
         (cm_function_locals f) <=> true) **
       fact(cm_rep_structs_safe (cm_program_structs p)
         <=> true) **
       fact(cm_rep_globals_safe (cm_program_globals p)
         <=> true) **
       fact(cm_rep_strings_safe (cm_program_strings p)
         <=> true) **
       fact(cm_rep_members_safe (cm_function_params f)
         <=> true) **
       fact(cm_rep_members_safe (cm_function_locals f)
         <=> true) **
       fact(cm_rep_globals_size (cm_program_globals p) +
         cm_rep_strings_size (cm_program_strings p) <= 1048560i) **
       fact(0i <= (temp__pre:int)) **
       fact(temp__pre <= (temp_limit__pre:int)) **
       fact(temp__pre +
         cm_expr_temps_for (right_:cm_expr) 0i <=
           temp_limit__pre) **
       fact(cm_temp_offset p (fid__pre:int)
         (temp_limit__pre:int) <= 2147483647i) **
       fact(cm_i32_code_count
         ((pc__pre:int) +
          (cm_rvalue_code_count p fid__pre
            (left_:cm_expr) + 1i)) <=> true) **
       fact(cm_i32_code_count
         (((pc__pre:int) +
           (cm_rvalue_code_count p fid__pre left_ + 1i)) +
          ilength
            (cm_expr_code_for p fid__pre
              (pc__pre +
                (cm_rvalue_code_count p fid__pre left_ + 1i))
              temp__pre right_ 0i)) <=> true)`;
  cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
      refl_slrule(child_facts)));
}

static void cm_emit_binary_expr(struct cm_program *program, int fid,
                                struct cm_function *fn, int pc, int temp,
                                int temp_limit, struct cm_expr *expr,
                                int lvalue, struct cm_emitter *emitter)
    [[cst::param(`p:cm_program`, `f:cm_function_d`, `e:cm_expr`,
                 `op_:int`, `left_:cm_expr`, `right_:cm_expr`,
                 `ty_:cm_type`, `body:int`, `next:int`,
                 `functions_ptr:int`, `done:(tvm_inst)list`,
                 `tail:(tvm_inst)list`, `out:int`, `capacity:int`)]]
    [[cst::require(
      `fact(e == CMBinaryE op_ left_ right_ ty_) **
       fact(0i <= lvalue) ** fact(lvalue <= 1i) **
       fact(cm_wf_program p <=> true) **
       fact(cm_typed_program p <=> true) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(cm_expr_wf p f e <=> true) **
       fact(cm_expr_counts_representable p fid e <=> true) **
       fact(cm_slots_wf (cm_program_structs p)
              (cm_function_params f) <=> true) **
       fact(cm_slots_wf (cm_program_structs p)
              (cm_function_locals f) <=> true) **
       fact(cm_rep_structs_safe (cm_program_structs p) <=> true) **
       fact(cm_rep_globals_safe (cm_program_globals p) <=> true) **
       fact(cm_rep_strings_safe (cm_program_strings p) <=> true) **
       fact(cm_rep_members_safe (cm_function_params f) <=> true) **
       fact(cm_rep_members_safe (cm_function_locals f) <=> true) **
       fact(cm_rep_globals_size (cm_program_globals p) +
              cm_rep_strings_size (cm_program_strings p) <= 1048560i) **
       fact(0i <= temp) ** fact(temp <= temp_limit) **
       fact(temp + cm_expr_temps_for e lvalue <= temp_limit) **
       fact(cm_temp_offset p fid temp_limit <= 2147483647i) **
       fact(cm_i32_code_count pc <=> true) **
       fact(cm_i32_code_count
              (pc + ilength (cm_expr_code_for p fid pc temp e lvalue))
              <=> true) **
       cm_program_context_rep program p functions_ptr **
       cm_function_context_rep fn f body next **
       cm_expr_rep expr e **
       cm_resolved_emitter_plan_rep p emitter out capacity done
         (cm_expr_code_for p fid pc temp e lvalue ++ tail)`)]]
    [[cst::ensure(
      `fact(e == CMBinaryE op_ left_ right_ ty_) **
       fact(0i <= lvalue) ** fact(lvalue <= 1i) **
       fact(cm_wf_program p <=> true) **
       fact(cm_typed_program p <=> true) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(cm_expr_wf p f e <=> true) **
       fact(cm_expr_counts_representable p fid e <=> true) **
       fact(cm_slots_wf (cm_program_structs p)
              (cm_function_params f) <=> true) **
       fact(cm_slots_wf (cm_program_structs p)
              (cm_function_locals f) <=> true) **
       fact(cm_rep_structs_safe (cm_program_structs p) <=> true) **
       fact(cm_rep_globals_safe (cm_program_globals p) <=> true) **
       fact(cm_rep_strings_safe (cm_program_strings p) <=> true) **
       fact(cm_rep_members_safe (cm_function_params f) <=> true) **
       fact(cm_rep_members_safe (cm_function_locals f) <=> true) **
       fact(cm_rep_globals_size (cm_program_globals p) +
              cm_rep_strings_size (cm_program_strings p) <= 1048560i) **
       fact(0i <= temp) ** fact(temp <= temp_limit) **
       fact(temp + cm_expr_temps_for e lvalue <= temp_limit) **
       fact(cm_temp_offset p fid temp_limit <= 2147483647i) **
       fact(cm_i32_code_count pc <=> true) **
       fact(cm_i32_code_count
              (pc + ilength (cm_expr_code_for p fid pc temp e lvalue))
              <=> true) **
       cm_program_context_rep program p functions_ptr **
       cm_function_context_rep fn f body next **
       cm_expr_rep expr e **
       cm_resolved_emitter_plan_rep p emitter out capacity
         (done ++ cm_expr_code_for p fid pc temp e lvalue) tail`)]]
{
  [[cst::proof]] {
    cm_open_expr_rep_st();
    thm shape = assume_rule(
        `e == CMBinaryE (op_:int) (left_:cm_expr)
          (right_:cm_expr) (ty_:cm_type)`);
    thm op_model = by_rewrite(
        `cm_rep_expr_op (e:cm_expr) == (op_:int)`,
        THM_LIST(shape, get_cm_rep_expr_op_def()));
    substitute_st(op_model);
    add_fact_st(by_rewrite(
        `cm_type_encode (cm_expr_type (e:cm_expr)) ==
         cm_type_encode (ty_:cm_type)`,
        THM_LIST(shape, get_cm_expr_type_def())));
    cm_open_expr_count_facts(shape);
    cm_open_two_child_count_payload(shape);
    cm_add_child_expr_facts_st(`left_:cm_expr`);
    cm_add_child_expr_facts_st(`right_:cm_expr`);
    cm_add_expr_result_refs_st();
  }
  if (!lvalue) {
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`f`, `(f:cm_function_d)`)]]
    [[cst::where(`e`, `(left_:cm_expr)`)]]
    [[cst::where(`fid`, `(fid__pre:int)`)]]
    int left_count = cm_expr_rvalue_count_context(
        program, fid, fn, expr->a);
    [[cst::proof]] {
      thm returned = assume_rule(
          `(retval:int) ==
           cm_rcount_of
             (cm_expr_code_counts (p:cm_program)
               (fid__pre:int) (left_:cm_expr))`);
      thm model = conv_rule(rewrite_conv(THM_LIST(
          gsym_rule(get_cm_rvalue_code_count_def()))), returned);
      add_fact_st(model);
      cst_set_symbolic_state(retarget_cell_st(
          cst_get_symbolic_state(), `left_count__addr:addr`,
          `retval:int`,
          `cm_rvalue_code_count (p:cm_program)
            (fid__pre:int) (left_:cm_expr)`));
    }
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`f`, `(f:cm_function_d)`)]]
    [[cst::where(`e`, `(right_:cm_expr)`)]]
    [[cst::where(`fid`, `(fid__pre:int)`)]]
    int right_count = cm_expr_rvalue_count_context(
        program, fid, fn, expr->b);
    [[cst::proof]] {
      thm returned = assume_rule(
          `(retval_1:int) ==
           cm_rcount_of
             (cm_expr_code_counts (p:cm_program)
               (fid__pre:int) (right_:cm_expr))`);
      thm model = conv_rule(rewrite_conv(THM_LIST(
          gsym_rule(get_cm_rvalue_code_count_def()))), returned);
      add_fact_st(model);
      cst_set_symbolic_state(retarget_cell_st(
          cst_get_symbolic_state(), `right_count__addr:addr`,
          `retval_1:int`,
          `cm_rvalue_code_count (p:cm_program)
            (fid__pre:int) (right_:cm_expr)`));
    }
    if (expr->op == CMC_BIN_OR || expr->op == CMC_BIN_AND) {
      if (expr->op == CMC_BIN_OR) {
        [[cst::proof]] {
          thm shape = assume_rule(
              `e == CMBinaryE (op_:int) (left_:cm_expr)
                (right_:cm_expr) (ty_:cm_type)`);
          thm lvalue_case =
              eqt_intro_rule(assume_rule(`lvalue__pre == 0i`));
          thm or_case =
              eqt_intro_rule(assume_rule(`(op_:int) == 0i`));
          thm short_case = apply_conversion(
              reduce_rewrite_conv(THM_LIST(or_case)),
              `(op_:int) == 0i || op_ == 1i`);
          cm_prepare_binary_short_st(
              shape, lvalue_case, short_case, or_case);
        }
      } else {
        [[cst::proof]] {
          thm shape = assume_rule(
              `e == CMBinaryE (op_:int) (left_:cm_expr)
                (right_:cm_expr) (ty_:cm_type)`);
          thm lvalue_case =
              eqt_intro_rule(assume_rule(`lvalue__pre == 0i`));
          thm op_case =
              assume_rule(`(op_:int) == 1i`);
          thm op_one_case = eqt_intro_rule(op_case);
          thm or_case = eqf_intro_rule(mp_rule(
              int_arith_rule(
                `(op_:int) == 1i ==> ~(op_ == 0i)`),
              op_case));
          thm short_case = apply_conversion(
              reduce_rewrite_conv(THM_LIST(or_case, op_one_case)),
              `(op_:int) == 0i || op_ == 1i`);
          cm_prepare_binary_short_st(
              shape, lvalue_case, short_case, or_case);
        }
      }
      [[cst::where(`p`, `(p:cm_program)`)]]
      [[cst::where(`f`, `(f:cm_function_d)`)]]
      [[cst::where(`fid`, `(fid__pre:int)`)]]
      cm_emit_expr(program, fid, fn, pc, temp, temp_limit,
                   expr->a, 0, emitter);
      [[cst::proof]] {
        rewrite_st(THM_LIST(get_theorem_by_name("APPEND")));
      }
      long long first_target =
          (long long)pc +
          ((long long)left_count + ((long long)right_count + 4LL));
      if (expr->op == CMC_BIN_OR) {
        [[cst::proof]] {
          cm_add_opcode_facts_st(`21i`, `TVMJnzOp`);
        }
        [[cst::where(`p`, `(p:cm_program)`)]]
        [[cst::where(`opcode`, `TVMJnzOp`)]]
        cm_emit_plan(emitter, CMC_OP_JNZ, first_target);
      } else {
        [[cst::proof]] {
          cm_add_opcode_facts_st(`20i`, `TVMJzOp`);
        }
        [[cst::where(`p`, `(p:cm_program)`)]]
        [[cst::where(`opcode`, `TVMJzOp`)]]
        cm_emit_plan(emitter, CMC_OP_JZ, first_target);
      }
      int right_pc = pc + (left_count + 1);
      struct cm_expr *right_expr = expr->b;
      if (expr->op == CMC_BIN_OR) {
        [[cst::proof]] {
          cm_select_binary_short_right_st(`TVMJnzOp`, `1i`);
        }
        [[cst::where(`p`, `(p:cm_program)`)]]
        [[cst::where(`f`, `(f:cm_function_d)`)]]
        [[cst::where(`fid`, `(fid__pre:int)`)]]
        [[cst::where(`e`, `(right_:cm_expr)`)]]
        [[cst::where(`body`, `(body:int)`)]]
        [[cst::where(`next`, `(next:int)`)]]
        [[cst::where(`functions_ptr`, `(functions_ptr:int)`)]]
        [[cst::where(`out`, `(out:int)`)]]
        [[cst::where(`capacity`, `(capacity:int)`)]]
        [[cst::where(`done`,
            `((done:(tvm_inst)list) ++
                cm_expr_code_for (p:cm_program) (fid__pre:int)
                  (pc__pre:int) (temp__pre:int)
                  (left_:cm_expr) 0i) ++
              [TVMInst TVMJnzOp
                 (pc__pre +
                   (cm_rvalue_code_count p fid__pre left_ +
                    (cm_rvalue_code_count p fid__pre
                      (right_:cm_expr) + 4i)))]`)]]
        [[cst::where(`tail`,
            `TVMInst TVMPushOp 0i ::
             TVMInst TVMNeOp 0i ::
             TVMInst TVMJmpOp
               ((pc__pre:int) +
                 (cm_rvalue_code_count (p:cm_program)
                    (fid__pre:int) (left_:cm_expr) +
                  (cm_rvalue_code_count p fid__pre
                    (right_:cm_expr) + 5i))) ::
             TVMInst TVMPushOp 1i ::
             (tail:(tvm_inst)list)`)]]
        cm_emit_expr(program, fid, fn, right_pc, temp,
                     temp_limit, right_expr, 0, emitter);
      } else {
        [[cst::proof]] {
          cm_select_binary_short_right_st(`TVMJzOp`, `0i`);
        }
        [[cst::where(`p`, `(p:cm_program)`)]]
        [[cst::where(`f`, `(f:cm_function_d)`)]]
        [[cst::where(`fid`, `(fid__pre:int)`)]]
        [[cst::where(`e`, `(right_:cm_expr)`)]]
        [[cst::where(`body`, `(body:int)`)]]
        [[cst::where(`next`, `(next:int)`)]]
        [[cst::where(`functions_ptr`, `(functions_ptr:int)`)]]
        [[cst::where(`out`, `(out:int)`)]]
        [[cst::where(`capacity`, `(capacity:int)`)]]
        [[cst::where(`done`,
            `((done:(tvm_inst)list) ++
                cm_expr_code_for (p:cm_program) (fid__pre:int)
                  (pc__pre:int) (temp__pre:int)
                  (left_:cm_expr) 0i) ++
              [TVMInst TVMJzOp
                 (pc__pre +
                   (cm_rvalue_code_count p fid__pre left_ +
                    (cm_rvalue_code_count p fid__pre
                      (right_:cm_expr) + 4i)))]`)]]
        [[cst::where(`tail`,
            `TVMInst TVMPushOp 0i ::
             TVMInst TVMNeOp 0i ::
             TVMInst TVMJmpOp
               ((pc__pre:int) +
                 (cm_rvalue_code_count (p:cm_program)
                    (fid__pre:int) (left_:cm_expr) +
                  (cm_rvalue_code_count p fid__pre
                    (right_:cm_expr) + 5i))) ::
             TVMInst TVMPushOp 0i ::
             (tail:(tvm_inst)list)`)]]
        cm_emit_expr(program, fid, fn, right_pc, temp,
                     temp_limit, right_expr, 0, emitter);
      }
      [[cst::proof]] {
        rewrite_st(THM_LIST(get_theorem_by_name("APPEND")));
        cm_add_opcode_facts_st(`0i`, `TVMPushOp`);
      }
      [[cst::where(`p`, `(p:cm_program)`)]]
      [[cst::where(`opcode`, `TVMPushOp`)]]
      cm_emit_plan(emitter, CMC_OP_PUSH, 0);
      [[cst::proof]] {
        cm_add_opcode_facts_st(`14i`, `TVMNeOp`);
      }
      [[cst::where(`p`, `(p:cm_program)`)]]
      [[cst::where(`opcode`, `TVMNeOp`)]]
      cm_emit_plan(emitter, CMC_OP_NE, 0);
      long long final_target =
          (long long)pc +
          ((long long)left_count + ((long long)right_count + 5LL));
      [[cst::proof]] {
        cm_add_opcode_facts_st(`19i`, `TVMJmpOp`);
      }
      [[cst::where(`p`, `(p:cm_program)`)]]
      [[cst::where(`opcode`, `TVMJmpOp`)]]
      cm_emit_plan(emitter, CMC_OP_JMP, final_target);
      long long short_value =
          expr->op == CMC_BIN_OR ? 1LL : 0LL;
      [[cst::proof]] {
        cm_add_opcode_facts_st(`0i`, `TVMPushOp`);
      }
      [[cst::where(`p`, `(p:cm_program)`)]]
      [[cst::where(`opcode`, `TVMPushOp`)]]
      cm_emit_plan(emitter, CMC_OP_PUSH, short_value);
      if (expr->op == CMC_BIN_OR) {
        [[cst::proof]] {
          thm shape = assume_rule(
              `e == CMBinaryE (op_:int) (left_:cm_expr)
                (right_:cm_expr) (ty_:cm_type)`);
          thm lvalue_case =
              eqt_intro_rule(assume_rule(`lvalue__pre == 0i`));
          thm or_case =
              eqt_intro_rule(assume_rule(`(op_:int) == 0i`));
          thm short_case = apply_conversion(
              reduce_rewrite_conv(THM_LIST(or_case)),
              `(op_:int) == 0i || op_ == 1i`);
          cm_restore_binary_short_st(
              shape, lvalue_case, short_case, or_case);
        }
      } else {
        [[cst::proof]] {
          thm shape = assume_rule(
              `e == CMBinaryE (op_:int) (left_:cm_expr)
                (right_:cm_expr) (ty_:cm_type)`);
          thm lvalue_case =
              eqt_intro_rule(assume_rule(`lvalue__pre == 0i`));
          thm op_case =
              assume_rule(`(op_:int) == 1i`);
          thm op_one_case = eqt_intro_rule(op_case);
          thm or_case = eqf_intro_rule(mp_rule(
              int_arith_rule(
                `(op_:int) == 1i ==> ~(op_ == 0i)`),
              op_case));
          thm short_case = apply_conversion(
              reduce_rewrite_conv(THM_LIST(or_case, op_one_case)),
              `(op_:int) == 0i || op_ == 1i`);
          cm_restore_binary_short_st(
              shape, lvalue_case, short_case, or_case);
        }
      }
    } else {
      [[cst::proof]] {
        thm shape = assume_rule(
            `e == CMBinaryE (op_:int) (left_:cm_expr)
              (right_:cm_expr) (ty_:cm_type)`);
        thm lvalue_case =
            eqt_intro_rule(assume_rule(`lvalue__pre == 0i`));
        thm op_zero_case = eqf_intro_rule(
            assume_rule(`~((op_:int) == 0i)`));
        thm op_one_case = eqf_intro_rule(
            assume_rule(`~((op_:int) == 1i)`));
        thm short_case = apply_conversion(
            rewrite_conv(THM_LIST(op_zero_case, op_one_case)),
            `(op_:int) == 0i || op_ == 1i`);
        thm code_shape = cm_binary_code_shape(
            shape, lvalue_case, short_case,
            `cm_expr_code_for (p:cm_program) (fid__pre:int)
               (pc__pre:int) (temp__pre:int) (left_:cm_expr) 0i ++
             cm_temp_store_code p fid__pre temp__pre ++
             cm_expr_code_for p fid__pre
               (pc__pre +
                cm_rvalue_code_count p fid__pre left_ + 5i)
               (temp__pre + 1i) (right_:cm_expr) 0i ++
             cm_binary_finish_code p fid__pre op_ left_ right_
               temp__pre`);
        cm_add_binary_ordinary_temp_facts(
            shape, short_case, lvalue_case);
        cm_add_index_pc_facts(code_shape,
            `cm_binary_finish_code (p:cm_program)
              (fid__pre:int) (op_:int) (left_:cm_expr)
              (right_:cm_expr) (temp__pre:int)`);
        cm_select_code_plan_st(code_shape);
      }
      [[cst::where(`p`, `(p:cm_program)`)]]
      [[cst::where(`f`, `(f:cm_function_d)`)]]
      [[cst::where(`fid`, `(fid__pre:int)`)]]
      cm_emit_expr(program, fid, fn, pc, temp, temp_limit,
                   expr->a, 0, emitter);
      [[cst::proof]] {
        rewrite_st(THM_LIST(get_theorem_by_name("APPEND")));
      }
      [[cst::where(`p`, `(p:cm_program)`)]]
      [[cst::where(`f`, `(f:cm_function_d)`)]]
      [[cst::where(`fid`, `(fid__pre:int)`)]]
      [[cst::where(`structs`, `cm_program_structs (p:cm_program)`)]]
      cm_emit_temp_store_plan(fn, temp, emitter);
      [[cst::proof]] {
        rewrite_st(THM_LIST(get_theorem_by_name("APPEND")));
      }
      int right_pc = pc + (left_count + 5);
      int right_temp = temp + 1;
      struct cm_expr *right_expr = expr->b;
      [[cst::proof]] {
        term child_tail =
            `cm_binary_finish_code (p:cm_program) (fid__pre:int)
               (op_:int) (left_:cm_expr) (right_:cm_expr)
               (temp__pre:int) ++ (tail:(tvm_inst)list)`;
        term child_done =
            `((done:(tvm_inst)list) ++
                cm_expr_code_for (p:cm_program) (fid__pre:int)
                  (pc__pre:int) (temp__pre:int)
                  (left_:cm_expr) 0i) ++
              cm_temp_store_code p fid__pre temp__pre`;
        term child_resources =
            `cm_program_context_rep (program__pre:int) (p:cm_program)
               (functions_ptr:int) **
             cm_function_context_rep (fn__pre:int) (f:cm_function_d)
               (body:int) (next:int) **
             cm_expr_rep (zb:int) (right_:cm_expr) **
             cm_resolved_emitter_plan_rep p (emitter__pre:int)
               (out:int) (capacity:int) child_done_
               (cm_expr_code_for p (fid__pre:int)
                  (pc__pre +
                    cm_rvalue_code_count p fid__pre
                      (left_:cm_expr) + 5i)
                  ((temp__pre:int) + 1i) right_ 0i ++ child_tail_)`;
        child_resources = subst(TERM_PAIR_LIST(
            (term_pair){child_done, `child_done_:(tvm_inst)list`},
            (term_pair){child_tail, `child_tail_:(tvm_inst)list`}),
            child_resources);
        cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
            refl_slrule(child_resources)));
      }
      [[cst::proof]] {
        term child_facts =
            `fact(0i <= 0i) ** fact(0i <= 1i) **
             fact(cm_wf_program (p:cm_program) <=> true) **
             fact(cm_typed_program p <=> true) **
             fact((f:cm_function_d) ==
               inth (fid__pre:int) (cm_program_functions p)) **
             fact(cm_expr_wf p f (right_:cm_expr) <=> true) **
             fact(cm_expr_counts_representable p fid__pre right_
               <=> true) **
             fact(cm_slots_wf (cm_program_structs p)
               (cm_function_params f) <=> true) **
             fact(cm_slots_wf (cm_program_structs p)
               (cm_function_locals f) <=> true) **
             fact(cm_rep_structs_safe (cm_program_structs p)
               <=> true) **
             fact(cm_rep_globals_safe (cm_program_globals p)
               <=> true) **
             fact(cm_rep_strings_safe (cm_program_strings p)
               <=> true) **
             fact(cm_rep_members_safe (cm_function_params f)
               <=> true) **
             fact(cm_rep_members_safe (cm_function_locals f)
               <=> true) **
             fact(cm_rep_globals_size (cm_program_globals p) +
               cm_rep_strings_size (cm_program_strings p) <= 1048560i) **
             fact(0i <= (temp__pre:int) + 1i) **
             fact(temp__pre + 1i <= (temp_limit__pre:int)) **
             fact(temp__pre + 1i +
               cm_expr_temps_for (right_:cm_expr) 0i <=
                 temp_limit__pre) **
             fact(cm_temp_offset p (fid__pre:int)
               (temp_limit__pre:int) <= 2147483647i) **
             fact(cm_i32_code_count
               ((pc__pre:int) +
                cm_rvalue_code_count p fid__pre
                  (left_:cm_expr) + 5i) <=> true) **
             fact(cm_i32_code_count
               ((pc__pre +
                 cm_rvalue_code_count p fid__pre left_ + 5i) +
                ilength
                  (cm_expr_code_for p fid__pre
                    (pc__pre +
                      cm_rvalue_code_count p fid__pre left_ + 5i)
                    (temp__pre + 1i) right_ 0i)) <=> true)`;
        cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
            refl_slrule(child_facts)));
      }
      [[cst::where(`p`, `(p:cm_program)`)]]
      [[cst::where(`f`, `(f:cm_function_d)`)]]
      [[cst::where(`fid`, `(fid__pre:int)`)]]
      [[cst::where(`e`, `(right_:cm_expr)`)]]
      [[cst::where(`body`, `(body:int)`)]]
      [[cst::where(`next`, `(next:int)`)]]
      [[cst::where(`functions_ptr`, `(functions_ptr:int)`)]]
      [[cst::where(`out`, `(out:int)`)]]
      [[cst::where(`capacity`, `(capacity:int)`)]]
      [[cst::where(`done`,
          `((done:(tvm_inst)list) ++
              cm_expr_code_for (p:cm_program) (fid__pre:int)
                (pc__pre:int) (temp__pre:int)
                (left_:cm_expr) 0i) ++
            cm_temp_store_code p fid__pre temp__pre`)]]
      [[cst::where(`tail`,
          `cm_binary_finish_code (p:cm_program) (fid__pre:int)
             (op_:int) (left_:cm_expr) (right_:cm_expr)
             (temp__pre:int) ++ (tail:(tvm_inst)list)`)]]
      cm_emit_expr(program, fid, fn, right_pc, right_temp,
                   temp_limit, right_expr, 0, emitter);
      [[cst::proof]] {
        rewrite_st(THM_LIST(get_theorem_by_name("APPEND")));
      }
      [[cst::where(`p`, `(p:cm_program)`)]]
      [[cst::where(`f`, `(f:cm_function_d)`)]]
      [[cst::where(`left_e`, `(left_:cm_expr)`)]]
      [[cst::where(`right_e`, `(right_:cm_expr)`)]]
      [[cst::where(`body`, `(body:int)`)]]
      [[cst::where(`next`, `(next:int)`)]]
      [[cst::where(`functions_ptr`, `(functions_ptr:int)`)]]
      cm_emit_binary_finish_plan(program, fid, fn, temp, expr->op,
                                 expr->a, expr->b, emitter);
      [[cst::proof]] {
        thm shape = assume_rule(
            `e == CMBinaryE (op_:int) (left_:cm_expr)
              (right_:cm_expr) (ty_:cm_type)`);
        thm lvalue_case =
            eqt_intro_rule(assume_rule(`lvalue__pre == 0i`));
        thm op_zero_case = eqf_intro_rule(
            assume_rule(`~((op_:int) == 0i)`));
        thm op_one_case = eqf_intro_rule(
            assume_rule(`~((op_:int) == 1i)`));
        thm short_case = apply_conversion(
            rewrite_conv(THM_LIST(op_zero_case, op_one_case)),
            `(op_:int) == 0i || op_ == 1i`);
        thm code_shape = cm_binary_code_shape(
            shape, lvalue_case, short_case,
            `cm_expr_code_for (p:cm_program) (fid__pre:int)
               (pc__pre:int) (temp__pre:int) (left_:cm_expr) 0i ++
             cm_temp_store_code p fid__pre temp__pre ++
             cm_expr_code_for p fid__pre
               (pc__pre +
                cm_rvalue_code_count p fid__pre left_ + 5i)
               (temp__pre + 1i) (right_:cm_expr) 0i ++
             cm_binary_finish_code p fid__pre op_ left_ right_
               temp__pre`);
        code_shape = conv_rule(rewrite_conv(THM_LIST(
            gsym_rule(get_theorem_by_name("APPEND_ASSOC")),
            get_theorem_by_name("APPEND"),
            get_theorem_by_name("APPEND_NIL"))), code_shape);
        cm_restore_code_plan_end_st(code_shape);
      }
    }
  } else {
    [[cst::proof]] {
      thm shape = assume_rule(
          `e == CMBinaryE (op_:int) (left_:cm_expr)
            (right_:cm_expr) (ty_:cm_type)`);
      thm code_shape = cm_binary_code_shape(
          shape,
          eqf_intro_rule(assume_rule(`~(lvalue__pre == 0i)`)),
          refl_rule(`(op_:int) == 0i || op_ == 1i`),
          `[]:(tvm_inst)list`);
      cm_empty_code_plan_end_st(code_shape);
    }
  }
  [[cst::proof]] {
    thm shape = assume_rule(
        `e == CMBinaryE (op_:int) (left_:cm_expr)
          (right_:cm_expr) (ty_:cm_type)`);
    cm_close_two_child_count_payload(shape);
    thm op_model = by_rewrite(
        `cm_rep_expr_op (e:cm_expr) == (op_:int)`,
        THM_LIST(shape, get_cm_rep_expr_op_def()));
    substitute_st(sym_rule(op_model));
    cm_close_expr_rep_st();
  }
}
PROOF static thm cm_member_code_shape(const thm shape) {
  term target =
      `cm_expr_code_for (p:cm_program) (fid__pre:int) (pc__pre:int)
         (temp__pre:int) (e:cm_expr) (lvalue__pre:int) ==
       cm_expr_code_for p fid__pre pc__pre temp__pre
         (arg_:cm_expr) 0i ++
       [TVMInst TVMPushOp
          (cm_member_offset (cm_program_structs p)
            (cm_struct_id (cm_pointee (cm_expr_type arg_)))
            (mid_:int));
        TVMInst TVMAddOp 0i] ++
       cm_member_load_suffix p (cm_expr_type arg_) mid_
         (ty_:cm_type) lvalue__pre`;
  gnode root = gnode_new_with_ccl(mk_imp(concl(shape), target));
  gnode leaf = DISCH_TAC(root, "Hshape");
  gnode_list cases = BOOL_CASES_TAC(
      leaf, `(lvalue__pre:int) == 0i`, "Hlvalue");
  thm_list rules = THM_LIST(
      cm_expr_code_for_def, shape, get_cm_emit_expr_pair_def(),
      get_cm_rcode_of_def(), get_cm_lcode_of_def(),
      get_cm_emit_rvalue_def(), get_cm_emit_lvalue_def(),
      cm_member_load_suffix_def,
      get_theorem_by_name("APPEND_NIL"));
  for (size_t i = 0; i < vector_size(cases); ++i) {
    CONV_WITH_ASMP_TAC(cases[i], reduce_rewrite_conv, rules);
  }
  return mp_rule(gnode_prove(root), shape);
}

static void cm_emit_member_expr(struct cm_program *program, int fid,
                                struct cm_function *fn, int pc, int temp,
                                int temp_limit, struct cm_expr *expr,
                                int lvalue, struct cm_emitter *emitter)
    [[cst::param(`p:cm_program`, `f:cm_function_d`, `e:cm_expr`,
                 `arg_:cm_expr`, `mid_:int`, `ty_:cm_type`,
                 `body:int`, `next:int`, `functions_ptr:int`,
                 `done:(tvm_inst)list`, `tail:(tvm_inst)list`,
                 `out:int`, `capacity:int`)]]
    [[cst::require(
      `fact(e == CMMemberE arg_ mid_ ty_) **
       fact(0i <= lvalue) ** fact(lvalue <= 1i) **
       fact(cm_wf_program p <=> true) **
       fact(cm_typed_program p <=> true) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(cm_expr_wf p f e <=> true) **
       fact(cm_expr_counts_representable p fid e <=> true) **
       fact(cm_slots_wf (cm_program_structs p)
              (cm_function_params f) <=> true) **
       fact(cm_slots_wf (cm_program_structs p)
              (cm_function_locals f) <=> true) **
       fact(cm_rep_structs_safe (cm_program_structs p) <=> true) **
       fact(cm_rep_globals_safe (cm_program_globals p) <=> true) **
       fact(cm_rep_strings_safe (cm_program_strings p) <=> true) **
       fact(cm_rep_members_safe (cm_function_params f) <=> true) **
       fact(cm_rep_members_safe (cm_function_locals f) <=> true) **
       fact(cm_rep_globals_size (cm_program_globals p) +
              cm_rep_strings_size (cm_program_strings p) <= 1048560i) **
       fact(0i <= temp) ** fact(temp <= temp_limit) **
       fact(temp + cm_expr_temps_for e lvalue <= temp_limit) **
       fact(cm_temp_offset p fid temp_limit <= 2147483647i) **
       fact(cm_i32_code_count pc <=> true) **
       fact(cm_i32_code_count
              (pc + ilength (cm_expr_code_for p fid pc temp e lvalue))
              <=> true) **
       cm_program_context_rep program p functions_ptr **
       cm_function_context_rep fn f body next **
       cm_expr_rep expr e **
       cm_resolved_emitter_plan_rep p emitter out capacity done
         (cm_expr_code_for p fid pc temp e lvalue ++ tail)`)]]
    [[cst::ensure(
      `fact(e == CMMemberE arg_ mid_ ty_) **
       fact(0i <= lvalue) ** fact(lvalue <= 1i) **
       fact(cm_wf_program p <=> true) **
       fact(cm_typed_program p <=> true) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(cm_expr_wf p f e <=> true) **
       fact(cm_expr_counts_representable p fid e <=> true) **
       fact(cm_slots_wf (cm_program_structs p)
              (cm_function_params f) <=> true) **
       fact(cm_slots_wf (cm_program_structs p)
              (cm_function_locals f) <=> true) **
       fact(cm_rep_structs_safe (cm_program_structs p) <=> true) **
       fact(cm_rep_globals_safe (cm_program_globals p) <=> true) **
       fact(cm_rep_strings_safe (cm_program_strings p) <=> true) **
       fact(cm_rep_members_safe (cm_function_params f) <=> true) **
       fact(cm_rep_members_safe (cm_function_locals f) <=> true) **
       fact(cm_rep_globals_size (cm_program_globals p) +
              cm_rep_strings_size (cm_program_strings p) <= 1048560i) **
       fact(0i <= temp) ** fact(temp <= temp_limit) **
       fact(temp + cm_expr_temps_for e lvalue <= temp_limit) **
       fact(cm_temp_offset p fid temp_limit <= 2147483647i) **
       fact(cm_i32_code_count pc <=> true) **
       fact(cm_i32_code_count
              (pc + ilength (cm_expr_code_for p fid pc temp e lvalue))
              <=> true) **
       cm_program_context_rep program p functions_ptr **
       cm_function_context_rep fn f body next **
       cm_expr_rep expr e **
       cm_resolved_emitter_plan_rep p emitter out capacity
         (done ++ cm_expr_code_for p fid pc temp e lvalue) tail`)]]
{
  [[cst::proof]] {
    cm_open_expr_rep_st();
    thm shape = assume_rule(
        `e == CMMemberE (arg_:cm_expr) (mid_:int)
          (ty_:cm_type)`);
    add_fact_st(by_rewrite(
        `cm_type_encode (cm_expr_type (e:cm_expr)) ==
         cm_type_encode (ty_:cm_type)`,
        THM_LIST(shape, get_cm_expr_type_def())));
    cm_open_expr_count_facts(shape);
    cm_open_single_child_count_payload(shape);
    cm_add_expr_result_refs_st();
    thm value_model = by_rewrite(
        `cm_rep_expr_value (e:cm_expr) == (mid_:int)`,
        THM_LIST(shape, get_cm_rep_expr_value_def()));
    thm member_cast = mp_rule(mp_rule(
        spec_rule(`mid_:int`, cm_nonnegative_i32_cast),
        assume_rule(`0i <= (mid_:int)`)),
        assume_rule(`(mid_:int) <= 2147483647i`));
    substitute_st(trans_rule(beta_norm(ap_term_rule(
        `\n:int. signed_last_nbits n 32i`, value_model)),
        member_cast));
  }
  int member_id = (int)expr->value;
  [[cst::proof]] {
    thm shape = assume_rule(
        `e == CMMemberE (arg_:cm_expr) (mid_:int)
          (ty_:cm_type)`);
    thm value_model = by_rewrite(
        `cm_rep_expr_value (e:cm_expr) == (mid_:int)`,
        THM_LIST(shape, get_cm_rep_expr_value_def()));
    thm member_cast = mp_rule(mp_rule(
        spec_rule(`mid_:int`, cm_nonnegative_i32_cast),
        assume_rule(`0i <= (mid_:int)`)),
        assume_rule(`(mid_:int) <= 2147483647i`));
    thm cast_model = trans_rule(beta_norm(ap_term_rule(
        `\n:int. signed_last_nbits n 32i`, value_model)),
        member_cast);
    add_fact_st(cast_model);
    cst_set_symbolic_state(retarget_cell_st(
        cst_get_symbolic_state(), `member_id__addr:addr`,
        `signed_last_nbits (cm_rep_expr_value (e:cm_expr)) 32i`,
        `mid_:int`));
  }
  int base_type;
  [[cst::where(`e`, `(arg_:cm_expr)`)]]
  cm_expr_type_code_context(expr->a, &base_type);
  [[cst::proof]] {
    thm node = mp_rule(specl_rule(TERM_LIST(
        `p:cm_program`, `fid__pre:int`, `arg_:cm_expr`),
        cm_expr_counts_node), from_state_bool(
          `cm_expr_counts_representable (p:cm_program)
            (fid__pre:int) (arg_:cm_expr)`));
    thm node_facts = conv_rule(rewrite_conv(THM_LIST(
        get_cm_expr_count_node_representable_def(),
        get_cm_code_counts_representable_def())), node);
    cm_add_count_facts(node_facts);
  }
  [[cst::where(`p`, `(p:cm_program)`)]]
  [[cst::where(`base`, `cm_expr_type (arg_:cm_expr)`)]]
  [[cst::where(`functions_ptr`, `(functions_ptr:int)`)]]
  int array_value = cm_member_array_value_context(
      program, base_type, member_id);
  [[cst::proof]] {
    cst_set_symbolic_state(retarget_cell_st(
        cst_get_symbolic_state(), `array_value__addr:addr`,
        `retval:int`,
        `cm_member_array_code (p:cm_program)
          (cm_expr_type (arg_:cm_expr)) (mid_:int)`));
  }
  [[cst::where(`p`, `(p:cm_program)`)]]
  [[cst::where(`base`, `cm_expr_type (arg_:cm_expr)`)]]
  [[cst::where(`functions_ptr`, `(functions_ptr:int)`)]]
  long long offset = cm_member_offset_value_context(
      program, base_type, member_id);
  [[cst::proof]] {
    cm_retarget_i64_st(`offset__addr:addr`,
        assume_rule(
          `(retval_1:int) ==
           cm_member_offset (cm_program_structs (p:cm_program))
             (cm_struct_id
               (cm_pointee (cm_expr_type (arg_:cm_expr))))
             (mid_:int)`));
  }
  [[cst::proof]] {
    thm shape = assume_rule(
        `e == CMMemberE (arg_:cm_expr) (mid_:int)
          (ty_:cm_type)`);
    thm code_shape = cm_member_code_shape(shape);
    thm temp_shape = by_rewrite(
        `cm_expr_temps_for (e:cm_expr) (lvalue__pre:int) ==
         cm_expr_temps_for (arg_:cm_expr) 0i`,
        THM_LIST(cm_expr_temps_for_def, shape,
          get_cm_ltemps_def(), get_cm_rtemps_def(),
          get_cm_expr_tpair_def(), get_cm_tleft_def(),
          get_cm_tright_def(), get_theorem_by_name("COND_ID")));
    cm_add_rvalue_child_facts(code_shape, temp_shape,
        `[TVMInst TVMPushOp
            (cm_member_offset (cm_program_structs (p:cm_program))
              (cm_struct_id
                (cm_pointee (cm_expr_type (arg_:cm_expr))))
              (mid_:int));
          TVMInst TVMAddOp 0i] ++
         cm_member_load_suffix p (cm_expr_type arg_) mid_
           (ty_:cm_type) (lvalue__pre:int)`);
    cm_select_code_plan_st(code_shape);
  }
  [[cst::where(`p`, `(p:cm_program)`)]]
  [[cst::where(`f`, `(f:cm_function_d)`)]]
  [[cst::where(`fid`, `(fid__pre:int)`)]]
  cm_emit_expr(program, fid, fn, pc, temp, temp_limit,
               expr->a, 0, emitter);
  [[cst::proof]] {
    rewrite_st(THM_LIST(get_theorem_by_name("APPEND")));
    cm_add_opcode_facts_st(`0i`, `TVMPushOp`);
  }
  [[cst::where(`p`, `(p:cm_program)`)]]
  [[cst::where(`opcode`, `TVMPushOp`)]]
  cm_emit_plan(emitter, CMC_OP_PUSH, offset);
  [[cst::proof]] {
    cm_add_opcode_facts_st(`8i`, `TVMAddOp`);
  }
  [[cst::where(`p`, `(p:cm_program)`)]]
  [[cst::where(`opcode`, `TVMAddOp`)]]
  cm_emit_plan(emitter, CMC_OP_ADD, 0);
  if (!lvalue) {
    if (!array_value) {
      [[cst::proof]] {
        thm cases = specl_rule(TERM_LIST(
            `p:cm_program`, `cm_expr_type (arg_:cm_expr)`,
            `mid_:int`), cm_member_array_code_cases);
        thm not_array = eq_mp_rule(conjunct1_rule(cases),
            assume_rule(
              `cm_member_array_code (p:cm_program)
                (cm_expr_type (arg_:cm_expr)) (mid_:int) == 0i`));
        thm suffix = by_rewrite(
            `cm_member_load_suffix (p:cm_program)
               (cm_expr_type (arg_:cm_expr)) (mid_:int)
               (ty_:cm_type) (lvalue__pre:int) ==
             cm_load_code ty_`,
            THM_LIST(cm_member_load_suffix_def,
              eqt_intro_rule(assume_rule(`lvalue__pre == 0i`)),
              eqf_intro_rule(not_array)));
        rewrite_st(THM_LIST(suffix, get_theorem_by_name("APPEND")));
      }
      [[cst::where(`p`, `(p:cm_program)`)]]
      [[cst::where(`model_ty`, `(ty_:cm_type)`)]]
      cm_emit_load_plan(emitter, expr->ty);
      [[cst::proof]] {
        thm shape = assume_rule(
            `e == CMMemberE (arg_:cm_expr) (mid_:int)
              (ty_:cm_type)`);
        thm cases = specl_rule(TERM_LIST(
            `p:cm_program`, `cm_expr_type (arg_:cm_expr)`,
            `mid_:int`), cm_member_array_code_cases);
        thm not_array = eq_mp_rule(conjunct1_rule(cases),
            assume_rule(
              `cm_member_array_code (p:cm_program)
                (cm_expr_type (arg_:cm_expr)) (mid_:int) == 0i`));
        thm suffix = by_rewrite(
            `cm_member_load_suffix (p:cm_program)
               (cm_expr_type (arg_:cm_expr)) (mid_:int)
               (ty_:cm_type) (lvalue__pre:int) ==
             cm_load_code ty_`,
            THM_LIST(cm_member_load_suffix_def,
              eqt_intro_rule(assume_rule(`lvalue__pre == 0i`)),
              eqf_intro_rule(not_array)));
        thm code_shape = conv_rule(rewrite_conv(THM_LIST(suffix)),
            cm_member_code_shape(shape));
        code_shape = conv_rule(rewrite_conv(THM_LIST(
            gsym_rule(get_theorem_by_name("APPEND_ASSOC")),
            get_theorem_by_name("APPEND"),
            get_theorem_by_name("APPEND_NIL"))), code_shape);
        cm_restore_code_plan_end_st(code_shape);
      }
    } else {
      [[cst::proof]] {
        thm shape = assume_rule(
            `e == CMMemberE (arg_:cm_expr) (mid_:int)
              (ty_:cm_type)`);
        thm cases = specl_rule(TERM_LIST(
            `p:cm_program`, `cm_expr_type (arg_:cm_expr)`,
            `mid_:int`), cm_member_array_code_cases);
        thm is_array = eq_mp_rule(conjunct2_rule(cases),
            assume_rule(
              `~(cm_member_array_code (p:cm_program)
                  (cm_expr_type (arg_:cm_expr)) (mid_:int) == 0i)`));
        thm suffix = by_rewrite(
            `cm_member_load_suffix (p:cm_program)
               (cm_expr_type (arg_:cm_expr)) (mid_:int)
               (ty_:cm_type) (lvalue__pre:int) ==
             ([]:(tvm_inst)list)`,
            THM_LIST(cm_member_load_suffix_def,
              eqt_intro_rule(assume_rule(`lvalue__pre == 0i`)),
              eqt_intro_rule(is_array)));
        rewrite_st(THM_LIST(suffix, get_theorem_by_name("APPEND")));
        thm code_shape = conv_rule(rewrite_conv(THM_LIST(suffix)),
            cm_member_code_shape(shape));
        code_shape = conv_rule(rewrite_conv(THM_LIST(
            gsym_rule(get_theorem_by_name("APPEND_ASSOC")),
            get_theorem_by_name("APPEND"),
            get_theorem_by_name("APPEND_NIL"))), code_shape);
        cm_restore_code_plan_end_st(code_shape);
      }
    }
  } else {
    [[cst::proof]] {
      thm shape = assume_rule(
          `e == CMMemberE (arg_:cm_expr) (mid_:int)
            (ty_:cm_type)`);
      thm suffix = by_rewrite(
          `cm_member_load_suffix (p:cm_program)
             (cm_expr_type (arg_:cm_expr)) (mid_:int)
             (ty_:cm_type) (lvalue__pre:int) ==
           ([]:(tvm_inst)list)`,
          THM_LIST(cm_member_load_suffix_def,
            eqf_intro_rule(assume_rule(
              `~(lvalue__pre == 0i)`))));
      rewrite_st(THM_LIST(suffix, get_theorem_by_name("APPEND")));
      thm code_shape = conv_rule(rewrite_conv(THM_LIST(suffix)),
          cm_member_code_shape(shape));
      code_shape = conv_rule(rewrite_conv(THM_LIST(
          gsym_rule(get_theorem_by_name("APPEND_ASSOC")),
          get_theorem_by_name("APPEND"),
          get_theorem_by_name("APPEND_NIL"))), code_shape);
      cm_restore_code_plan_end_st(code_shape);
    }
  }
  [[cst::proof]] {
    thm shape = assume_rule(
        `e == CMMemberE (arg_:cm_expr) (mid_:int)
          (ty_:cm_type)`);
    cm_close_single_child_count_payload(shape);
    cm_close_expr_rep_st();
  }
}

PROOF static void cm_dispatch_add_simple_st(const thm kind) {
  term expanded =
      `(cm_rep_expr_kind (e:cm_expr) == 0i ||
        cm_rep_expr_kind e == 1i ||
        cm_rep_expr_kind e == 9i ||
        cm_rep_expr_kind e == 10i) ||
       cm_rep_expr_kind e == 2i`;
  thm expanded_fact = mp_rule(
      int_arith_rule(mk_imp(concl(kind), expanded)), kind);
  thm shape = by_rewrite(
      mk_eq(`cm_simple_expr (e:cm_expr)`, expanded),
      THM_LIST(cm_simple_expr_def, cm_leaf_expr_def));
  add_fact_st(eqt_intro_rule(
      eq_mp_rule(sym_rule(shape), expanded_fact)));
}

PROOF static void cm_dispatch_add_intrinsic_st(const thm kind) {
  term expanded =
      `cm_rep_expr_kind (e:cm_expr) == 11i ||
       cm_rep_expr_kind e == 12i ||
       cm_rep_expr_kind e == 13i`;
  thm expanded_fact = mp_rule(
      int_arith_rule(mk_imp(concl(kind), expanded)), kind);
  thm shape = by_rewrite(
      mk_eq(`cm_intrinsic_expr (e:cm_expr)`, expanded),
      THM_LIST(cm_intrinsic_expr_def));
  add_fact_st(eqt_intro_rule(
      eq_mp_rule(sym_rule(shape), expanded_fact)));
}

void cm_emit_expr(struct cm_program *program, int fid,
                  struct cm_function *fn, int pc, int temp,
                  int temp_limit, struct cm_expr *expr, int lvalue,
                  struct cm_emitter *emitter)
    [[cst::param(`p:cm_program`, `f:cm_function_d`, `e:cm_expr`,
                 `body:int`, `next:int`, `functions_ptr:int`,
                 `done:(tvm_inst)list`, `tail:(tvm_inst)list`,
                 `out:int`, `capacity:int`)]]
    [[cst::require(
      `fact(0i <= lvalue) ** fact(lvalue <= 1i) **
       fact(cm_wf_program p <=> true) **
       fact(cm_typed_program p <=> true) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(cm_expr_wf p f e <=> true) **
       fact(cm_expr_counts_representable p fid e <=> true) **
       fact(cm_slots_wf (cm_program_structs p)
              (cm_function_params f) <=> true) **
       fact(cm_slots_wf (cm_program_structs p)
              (cm_function_locals f) <=> true) **
       fact(cm_rep_structs_safe (cm_program_structs p) <=> true) **
       fact(cm_rep_globals_safe (cm_program_globals p) <=> true) **
       fact(cm_rep_strings_safe (cm_program_strings p) <=> true) **
       fact(cm_rep_members_safe (cm_function_params f) <=> true) **
       fact(cm_rep_members_safe (cm_function_locals f) <=> true) **
       fact(cm_rep_globals_size (cm_program_globals p) +
              cm_rep_strings_size (cm_program_strings p) <= 1048560i) **
       fact(0i <= temp) ** fact(temp <= temp_limit) **
       fact(temp + cm_expr_temps_for e lvalue <= temp_limit) **
       fact(cm_temp_offset p fid temp_limit <= 2147483647i) **
       fact(cm_i32_code_count pc <=> true) **
       fact(cm_i32_code_count
              (pc + ilength (cm_expr_code_for p fid pc temp e lvalue))
              <=> true) **
       cm_program_context_rep program p functions_ptr **
       cm_function_context_rep fn f body next **
       cm_expr_rep expr e **
       cm_resolved_emitter_plan_rep p emitter out capacity done
         (cm_expr_code_for p fid pc temp e lvalue ++ tail)`)]]
    [[cst::ensure(
      `fact(0i <= lvalue) ** fact(lvalue <= 1i) **
       fact(cm_wf_program p <=> true) **
       fact(cm_typed_program p <=> true) **
       fact(f == inth fid (cm_program_functions p)) **
       fact(cm_expr_wf p f e <=> true) **
       fact(cm_expr_counts_representable p fid e <=> true) **
       fact(cm_slots_wf (cm_program_structs p)
              (cm_function_params f) <=> true) **
       fact(cm_slots_wf (cm_program_structs p)
              (cm_function_locals f) <=> true) **
       fact(cm_rep_structs_safe (cm_program_structs p) <=> true) **
       fact(cm_rep_globals_safe (cm_program_globals p) <=> true) **
       fact(cm_rep_strings_safe (cm_program_strings p) <=> true) **
       fact(cm_rep_members_safe (cm_function_params f) <=> true) **
       fact(cm_rep_members_safe (cm_function_locals f) <=> true) **
       fact(cm_rep_globals_size (cm_program_globals p) +
              cm_rep_strings_size (cm_program_strings p) <= 1048560i) **
       fact(0i <= temp) ** fact(temp <= temp_limit) **
       fact(temp + cm_expr_temps_for e lvalue <= temp_limit) **
       fact(cm_temp_offset p fid temp_limit <= 2147483647i) **
       fact(cm_i32_code_count pc <=> true) **
       fact(cm_i32_code_count
              (pc + ilength (cm_expr_code_for p fid pc temp e lvalue))
              <=> true) **
       cm_program_context_rep program p functions_ptr **
       cm_function_context_rep fn f body next **
       cm_expr_rep expr e **
       cm_resolved_emitter_plan_rep p emitter out capacity
         (done ++ cm_expr_code_for p fid pc temp e lvalue) tail`)]]
{
  [[cst::proof]] { cm_open_expr_rep_st(); }
  if (expr->kind == CMC_EXPR_CONST) {
    [[cst::proof]] {
      cm_dispatch_add_simple_st(assume_rule(
          `cm_rep_expr_kind (e:cm_expr) == 0i`));
      cm_close_expr_rep_st();
    }
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`f`, `(f:cm_function_d)`)]]
    [[cst::where(`e`, `(e:cm_expr)`)]]
    cm_emit_simple_expr(program, fid, fn, pc, temp,
        expr, lvalue, emitter);
  } else if (expr->kind == CMC_EXPR_STRING) {
    [[cst::proof]] {
      cm_dispatch_add_simple_st(assume_rule(
          `cm_rep_expr_kind (e:cm_expr) == 1i`));
      cm_close_expr_rep_st();
    }
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`f`, `(f:cm_function_d)`)]]
    [[cst::where(`e`, `(e:cm_expr)`)]]
    cm_emit_simple_expr(program, fid, fn, pc, temp,
        expr, lvalue, emitter);
  } else if (expr->kind == CMC_EXPR_VAR) {
    [[cst::proof]] {
      cm_dispatch_add_simple_st(assume_rule(
          `cm_rep_expr_kind (e:cm_expr) == 2i`));
      cm_close_expr_rep_st();
    }
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`f`, `(f:cm_function_d)`)]]
    [[cst::where(`e`, `(e:cm_expr)`)]]
    cm_emit_simple_expr(program, fid, fn, pc, temp,
        expr, lvalue, emitter);
  } else if (expr->kind == CMC_EXPR_ASSIGN) {
    [[cst::proof]] {
      thm shape_ent = mp_rule(spec_rule(`e:cm_expr`,
          get_cm_expr_assign_shape_ent()),
          assume_rule(`cm_rep_expr_kind (e:cm_expr) == 3i`));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          rename_exists_hconv(shape_ent,
            TERM_LIST(`left_:cm_expr`, `right_:cm_expr`,
                      `ty_:cm_type`))));
      cm_close_expr_rep_st();
    }
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`f`, `(f:cm_function_d)`)]]
    [[cst::where(`e`, `(e:cm_expr)`)]]
    [[cst::where(`fid`, `(fid__pre:int)`)]]
    cm_emit_assignment_expr(program, fid, fn, pc, temp,
        temp_limit, expr, lvalue, emitter);
  } else if (expr->kind == CMC_EXPR_BINARY) {
    [[cst::proof]] {
      thm shape_ent = mp_rule(spec_rule(`e:cm_expr`,
          get_cm_expr_binary_shape_ent()),
          assume_rule(`cm_rep_expr_kind (e:cm_expr) == 4i`));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          rename_exists_hconv(shape_ent,
            TERM_LIST(`op_:int`, `left_:cm_expr`,
                      `right_:cm_expr`, `ty_:cm_type`))));
      cm_close_expr_rep_st();
    }
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`f`, `(f:cm_function_d)`)]]
    [[cst::where(`e`, `(e:cm_expr)`)]]
    [[cst::where(`fid`, `(fid__pre:int)`)]]
    cm_emit_binary_expr(program, fid, fn, pc, temp,
        temp_limit, expr, lvalue, emitter);
  } else if (expr->kind == CMC_EXPR_UNARY) {
    [[cst::proof]] {
      thm shape_ent = mp_rule(spec_rule(`e:cm_expr`,
          get_cm_expr_unary_shape_ent()),
          assume_rule(`cm_rep_expr_kind (e:cm_expr) == 5i`));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          rename_exists_hconv(shape_ent,
            TERM_LIST(`op_:int`, `arg_:cm_expr`,
                      `ty_:cm_type`))));
      cm_close_expr_rep_st();
    }
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`f`, `(f:cm_function_d)`)]]
    [[cst::where(`e`, `(e:cm_expr)`)]]
    [[cst::where(`fid`, `(fid__pre:int)`)]]
    cm_emit_unary_expr(program, fid, fn, pc, temp,
        temp_limit, expr, lvalue, emitter);
  } else if (expr->kind == CMC_EXPR_INDEX) {
    [[cst::proof]] {
      thm shape_ent = mp_rule(spec_rule(`e:cm_expr`,
          get_cm_expr_index_shape_ent()),
          assume_rule(`cm_rep_expr_kind (e:cm_expr) == 6i`));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          rename_exists_hconv(shape_ent,
            TERM_LIST(`left_:cm_expr`, `right_:cm_expr`,
                      `ty_:cm_type`))));
      cm_close_expr_rep_st();
    }
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`f`, `(f:cm_function_d)`)]]
    [[cst::where(`e`, `(e:cm_expr)`)]]
    [[cst::where(`fid`, `(fid__pre:int)`)]]
    cm_emit_index_expr(program, fid, fn, pc, temp,
        temp_limit, expr, lvalue, emitter);
  } else if (expr->kind == CMC_EXPR_MEMBER) {
    [[cst::proof]] {
      thm shape_ent = mp_rule(spec_rule(`e:cm_expr`,
          get_cm_expr_member_shape_ent()),
          assume_rule(`cm_rep_expr_kind (e:cm_expr) == 7i`));
      cst_set_symbolic_state(local_apply(cst_get_symbolic_state(),
          rename_exists_hconv(shape_ent,
            TERM_LIST(`arg_:cm_expr`, `mid_:int`,
                      `ty_:cm_type`))));
      cm_close_expr_rep_st();
    }
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`f`, `(f:cm_function_d)`)]]
    [[cst::where(`e`, `(e:cm_expr)`)]]
    [[cst::where(`fid`, `(fid__pre:int)`)]]
    cm_emit_member_expr(program, fid, fn, pc, temp,
        temp_limit, expr, lvalue, emitter);
  } else if (expr->kind == CMC_EXPR_CALL) {
    [[cst::proof]] { cm_close_expr_rep_st(); }
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`f`, `(f:cm_function_d)`)]]
    [[cst::where(`e`, `(e:cm_expr)`)]]
    [[cst::where(`fid`, `(fid__pre:int)`)]]
    cm_emit_call_expr(program, fid, fn, pc, temp,
        temp_limit, expr, lvalue, emitter);
  } else if (expr->kind == CMC_EXPR_SIZEOF) {
    [[cst::proof]] {
      cm_dispatch_add_simple_st(assume_rule(
          `cm_rep_expr_kind (e:cm_expr) == 9i`));
      cm_close_expr_rep_st();
    }
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`f`, `(f:cm_function_d)`)]]
    [[cst::where(`e`, `(e:cm_expr)`)]]
    cm_emit_simple_expr(program, fid, fn, pc, temp,
        expr, lvalue, emitter);
  } else if (expr->kind == CMC_EXPR_GETC) {
    [[cst::proof]] {
      cm_dispatch_add_simple_st(assume_rule(
          `cm_rep_expr_kind (e:cm_expr) == 10i`));
      cm_close_expr_rep_st();
    }
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`f`, `(f:cm_function_d)`)]]
    [[cst::where(`e`, `(e:cm_expr)`)]]
    cm_emit_simple_expr(program, fid, fn, pc, temp,
        expr, lvalue, emitter);
  } else if (expr->kind == CMC_EXPR_PUTC) {
    [[cst::proof]] {
      cm_dispatch_add_intrinsic_st(assume_rule(
          `cm_rep_expr_kind (e:cm_expr) == 11i`));
      cm_close_expr_rep_st();
    }
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`f`, `(f:cm_function_d)`)]]
    [[cst::where(`e`, `(e:cm_expr)`)]]
    [[cst::where(`fid`, `(fid__pre:int)`)]]
    cm_emit_intrinsic_expr(program, fid, fn, pc, temp,
        temp_limit, expr, lvalue, emitter);
  } else if (expr->kind == CMC_EXPR_PUTI) {
    [[cst::proof]] {
      cm_dispatch_add_intrinsic_st(assume_rule(
          `cm_rep_expr_kind (e:cm_expr) == 12i`));
      cm_close_expr_rep_st();
    }
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`f`, `(f:cm_function_d)`)]]
    [[cst::where(`e`, `(e:cm_expr)`)]]
    [[cst::where(`fid`, `(fid__pre:int)`)]]
    cm_emit_intrinsic_expr(program, fid, fn, pc, temp,
        temp_limit, expr, lvalue, emitter);
  } else {
    [[cst::proof]] {
      thm kind = mp_rule(int_arith_rule(
          `(0i <= cm_rep_expr_kind (e:cm_expr) &&
            cm_rep_expr_kind e <= 13i) ==>
           ~(cm_rep_expr_kind e == 0i) ==>
           ~(cm_rep_expr_kind e == 1i) ==>
           ~(cm_rep_expr_kind e == 2i) ==>
           ~(cm_rep_expr_kind e == 3i) ==>
           ~(cm_rep_expr_kind e == 4i) ==>
           ~(cm_rep_expr_kind e == 5i) ==>
           ~(cm_rep_expr_kind e == 6i) ==>
           ~(cm_rep_expr_kind e == 7i) ==>
           ~(cm_rep_expr_kind e == 8i) ==>
           ~(cm_rep_expr_kind e == 9i) ==>
           ~(cm_rep_expr_kind e == 10i) ==>
           ~(cm_rep_expr_kind e == 11i) ==>
           ~(cm_rep_expr_kind e == 12i) ==>
           cm_rep_expr_kind e == 13i`),
          spec_rule(`e:cm_expr`, get_cm_rep_expr_kind_bounds()));
      kind = mp_rule(kind, assume_rule(
          `~(cm_rep_expr_kind (e:cm_expr) == 0i)`));
      kind = mp_rule(kind, assume_rule(
          `~(cm_rep_expr_kind (e:cm_expr) == 1i)`));
      kind = mp_rule(kind, assume_rule(
          `~(cm_rep_expr_kind (e:cm_expr) == 2i)`));
      kind = mp_rule(kind, assume_rule(
          `~(cm_rep_expr_kind (e:cm_expr) == 3i)`));
      kind = mp_rule(kind, assume_rule(
          `~(cm_rep_expr_kind (e:cm_expr) == 4i)`));
      kind = mp_rule(kind, assume_rule(
          `~(cm_rep_expr_kind (e:cm_expr) == 5i)`));
      kind = mp_rule(kind, assume_rule(
          `~(cm_rep_expr_kind (e:cm_expr) == 6i)`));
      kind = mp_rule(kind, assume_rule(
          `~(cm_rep_expr_kind (e:cm_expr) == 7i)`));
      kind = mp_rule(kind, assume_rule(
          `~(cm_rep_expr_kind (e:cm_expr) == 8i)`));
      kind = mp_rule(kind, assume_rule(
          `~(cm_rep_expr_kind (e:cm_expr) == 9i)`));
      kind = mp_rule(kind, assume_rule(
          `~(cm_rep_expr_kind (e:cm_expr) == 10i)`));
      kind = mp_rule(kind, assume_rule(
          `~(cm_rep_expr_kind (e:cm_expr) == 11i)`));
      kind = mp_rule(kind, assume_rule(
          `~(cm_rep_expr_kind (e:cm_expr) == 12i)`));
      add_fact_st(kind);
      cm_dispatch_add_intrinsic_st(kind);
      cm_close_expr_rep_st();
    }
    [[cst::where(`p`, `(p:cm_program)`)]]
    [[cst::where(`f`, `(f:cm_function_d)`)]]
    [[cst::where(`e`, `(e:cm_expr)`)]]
    [[cst::where(`fid`, `(fid__pre:int)`)]]
    cm_emit_intrinsic_expr(program, fid, fn, pc, temp,
        temp_limit, expr, lvalue, emitter);
  }
}
