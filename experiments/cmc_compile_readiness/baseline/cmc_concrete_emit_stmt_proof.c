#include "cmc_concrete_emit_stmt_proof.h"
#include "userlib/proof.h"
#include "userlib/operational.h"
#require "cmc_concrete_counts.c"

PROOF void cm_open_stmt_rep_st(void) {
  apply_hconv_st(specl_rule(TERM_LIST(
      `stmt__pre:int`, `s:cm_stmt`), get_cm_stmt_open()));
}

PROOF void cm_close_stmt_rep_st(void) {
  apply_hconv_st(specl_rule(TERM_LIST(
      `stmt__pre:int`, `s:cm_stmt`, `ze:int`, `za:int`, `zb:int`),
      get_cm_stmt_close_witness()));
}

PROOF thm cm_stmt_case_wf(const thm shape) {
  return conv_rule(rewrite_conv(THM_LIST(
      shape, get_cm_stmt_wf_def())), from_state_bool(
        `cm_stmt_wf (p:cm_program) (f:cm_function_d)
          (loop_:bool) (s:cm_stmt)`));
}
PROOF static thm cm_find_stmt_conjunct_rec(
    const thm conjunction, const term expected) {
  if (alpha_compare(concl(conjunction), expected) == 0) {
    return conjunction;
  }
  if (!is_conj(concl(conjunction))) return empty_theorem;
  thm found = cm_find_stmt_conjunct_rec(
      conjunct1_rule(conjunction), expected);
  if (!IS_NULL(found)) return found;
  return cm_find_stmt_conjunct_rec(
      conjunct2_rule(conjunction), expected);
}

PROOF thm cm_find_stmt_conjunct_rule(
    const thm conjunction, const term expected) {
  thm found = cm_find_stmt_conjunct_rec(conjunction, expected);
  ENSURE_COND(!IS_NULL(found), "Missing statement conjunct");
  return found;
err:
  ERR_FUN_PUTS("cm_find_stmt_conjunct_rule",
               cstr_thm(conjunction), cstr_term(expected));
  return empty_theorem;
}


PROOF thm cm_stmt_code_shape(const thm shape, const term code) {
  return by_rewrite(mk_eq(
      `cm_emit_stmt (p:cm_program) (fid__pre:int) (pc__pre:int)
         (temp__pre:int) (break_pc__pre:int)
         (continue_pc__pre:int) (s:cm_stmt)`, code),
      THM_LIST(shape, get_cm_emit_stmt_def(), cm_expr_code_for_def,
        eqt_intro_rule(int_arith_rule(`0i == 0i`)),
        get_theorem_by_name("APPEND_NIL")));
}

PROOF thm cm_rvalue_code_length_at(
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

PROOF thm cm_stmt_code_length_at(
    const term stmt, const term pc, const term temp,
    const term break_pc, const term continue_pc) {
  return specl_rule(TERM_LIST(
      stmt, `p:cm_program`, `fid__pre:int`, pc, temp,
      break_pc, continue_pc), get_cm_stmt_code_length());
}

PROOF void cm_retarget_stmt_call_result_st(
    const term cell, const thm result) {
  struct dest_eq_results sides = dest_eq(concl(result));
  add_fact_st(result);
  cst_set_symbolic_state(retarget_cell_st(
      cst_get_symbolic_state(), cell, sides.tm1, sides.tm2));
}

PROOF void cm_add_i32_term_st(const thm predicate) {
  term value = dest_comb(concl(predicate)).tm2;
  thm bounds = conv_rule(rewrite_conv(THM_LIST(
      get_cm_i32_code_count_def())), predicate);
  thm lower = conjunct1_rule(bounds);
  thm upper = conjunct2_rule(bounds);
  add_fact_st(eqt_intro_rule(predicate));
  add_fact_st(lower);
  add_fact_st(upper);
  add_fact_st(mp_rule(mp_rule(spec_rule(
      value, cm_nonnegative_i32_cast), lower), upper));
}

PROOF void cm_add_stmt_fragment_i32_st(
    const thm code_shape, const term prefix,
    const term fragment, const term suffix) {
  thm parent_pc = from_state_bool(
      `cm_i32_code_count (pc__pre:int)`);
  thm parent_end = from_state_bool(
      `cm_i32_code_count
        ((pc__pre:int) + ilength
          (cm_emit_stmt (p:cm_program) (fid__pre:int) pc__pre
            (temp__pre:int) (break_pc__pre:int)
            (continue_pc__pre:int) (s:cm_stmt)))`);
  thm parent_pc_bounds = conv_rule(rewrite_conv(THM_LIST(
      get_cm_i32_code_count_def())), parent_pc);
  thm parent_end_bounds = conv_rule(rewrite_conv(THM_LIST(
      get_cm_i32_code_count_def(), code_shape,
      get_theorem_by_name("ILENGTH_APPEND"),
      get_theorem_by_name("ILENGTH_DEF"))), parent_end);
  thm prefix_nonnegative = conv_rule(rewrite_conv(THM_LIST(
      get_theorem_by_name("ILENGTH_APPEND"),
      get_theorem_by_name("ILENGTH_DEF"))), ispec_rule(
        prefix, get_theorem_by_name("ILENGTH_NONNEG")));
  thm fragment_nonnegative = conv_rule(rewrite_conv(THM_LIST(
      get_theorem_by_name("ILENGTH_APPEND"),
      get_theorem_by_name("ILENGTH_DEF"))), ispec_rule(
        fragment, get_theorem_by_name("ILENGTH_NONNEG")));
  thm suffix_nonnegative = conv_rule(rewrite_conv(THM_LIST(
      get_theorem_by_name("ILENGTH_APPEND"),
      get_theorem_by_name("ILENGTH_DEF"))), ispec_rule(
        suffix, get_theorem_by_name("ILENGTH_NONNEG")));
  term start_value = subst(TERM_PAIR_LIST(
      (term_pair){prefix, `prefix_:(tvm_inst)list`}),
      `(pc__pre:int) + ilength (prefix_:(tvm_inst)list)`);
  term end_value = subst(TERM_PAIR_LIST(
      (term_pair){prefix, `prefix_:(tvm_inst)list`},
      (term_pair){fragment, `fragment_:(tvm_inst)list`}),
      `(pc__pre:int) + ilength (prefix_:(tvm_inst)list) +
       ilength (fragment_:(tvm_inst)list)`);
  thm start = by_defs_arith(
      mk_comb(`cm_i32_code_count`, start_value),
      THM_LIST(get_cm_i32_code_count_def(), code_shape,
        get_theorem_by_name("ILENGTH_APPEND"),
        get_theorem_by_name("ILENGTH_DEF")),
      THM_LIST(parent_pc_bounds, parent_end_bounds,
        prefix_nonnegative, fragment_nonnegative,
        suffix_nonnegative));
  thm end = by_defs_arith(
      mk_comb(`cm_i32_code_count`, end_value),
      THM_LIST(get_cm_i32_code_count_def(), code_shape,
        get_theorem_by_name("ILENGTH_APPEND"),
        get_theorem_by_name("ILENGTH_DEF")),
      THM_LIST(parent_pc_bounds, parent_end_bounds,
        prefix_nonnegative, fragment_nonnegative,
        suffix_nonnegative));
  start = conv_rule(rewrite_conv(THM_LIST(
      get_theorem_by_name("ILENGTH_DEF"))), start);
  end = conv_rule(rewrite_conv(THM_LIST(
      get_theorem_by_name("ILENGTH_DEF"))), end);
  start = conv_rule(rewrite_conv(THM_LIST(
      get_theorem_by_name("INT_ADD_RID"),
      get_theorem_by_name("INT_ADD_LID"))), start);
  end = conv_rule(rewrite_conv(THM_LIST(
      get_theorem_by_name("INT_ADD_RID"),
      get_theorem_by_name("INT_ADD_LID"))), end);
  cm_add_i32_term_st(start);
  cm_add_i32_term_st(end);
  thm pc_cast = mp_rule(mp_rule(spec_rule(
      `pc__pre:int`, cm_nonnegative_i32_cast),
      conjunct1_rule(parent_pc_bounds)), conjunct2_rule(parent_pc_bounds));
  // Recursive calls also need the bound after the C int argument conversion.
  add_fact_st(eqt_intro_rule(conv_rule(
      subs_conv(THM_LIST(sym_rule(pc_cast))), end)));
}
