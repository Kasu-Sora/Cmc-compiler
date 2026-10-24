#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_type_source_r_var.h"
#include "cmc_preservation_ready_coordinate.h"

#require "cmc_preservation_type_cursor.c"
#require "cmc_preservation_type_lvalue.c"
#require "cmc_preservation_source_conditions.c"

PROOF static size_t _cmc_preservation_type_source_r_var_axioms_before =
    vector_size(get_all_axioms());

PROOF static bool cm_tsrvar_has_conjunct(term fact, term wanted) {
  if (alpha_compare(fact, wanted) == 0) return true;
  if (!is_conj(fact)) return false;
  struct dest_conj_results parts = dest_conj(fact);
  return cm_tsrvar_has_conjunct(parts.tm1, wanted) ||
      cm_tsrvar_has_conjunct(parts.tm2, wanted);
}

PROOF static thm cm_tsrvar_pick_conjunct(thm fact, term wanted) {
  if (alpha_compare(concl(fact), wanted) == 0) return fact;
  struct dest_conj_results parts = dest_conj(concl(fact));
  return cm_tsrvar_has_conjunct(parts.tm1, wanted)
      ? cm_tsrvar_pick_conjunct(conjunct1_rule(fact), wanted)
      : cm_tsrvar_pick_conjunct(conjunct2_rule(fact), wanted);
}

PROOF static void cm_tsrvar_add_facts(thm_list *rules, thm fact) {
  if (is_conj(concl(fact))) {
    cm_tsrvar_add_facts(rules, conjunct1_rule(fact));
    cm_tsrvar_add_facts(rules, conjunct2_rule(fact));
    return;
  }
  vector_add(rules, fact);
}

PROOF static void cm_tsrvar_close_reduced(
    gnode node, thm_list rules) {
  labeled_term_list assumptions = goal_lasmps(node->g);
  for (size_t i = 0; i < vector_size(assumptions); ++i) {
    cm_tsrvar_add_facts(&rules, assume_rule(assumptions[i].tm));
  }
  thm view = apply_conversion(reduce_rewrite_conv(rules),
      goal_ccl(node->g));
  ACCEPT_TAC(node, eqt_elim_rule(view));
}

PROOF static void cm_tsrvar_close_nonarray_branch(
    gnode branch, thm expression_open, thm binding_case,
    thm scope_fact, thm count_zero) {
  thm type_equal = conjunct2_rule(expression_open);
  thm nonarray = assume_rule(
      `~cm_binding_array (p:cm_program) (fid:int)
        (scope:int) (slot:int)`);
  thm normalized_type = conv_rule(reduce_rewrite_conv(THM_LIST(
      scope_fact, count_zero, get_cm_binding_type_def(),
      get_cm_global_expr_type_def(), get_cm_slot_expr_type_def(),
      get_theorem_by_name("COND_CLAUSES"))), type_equal);
  thm_list rules = THM_LIST(
      normalized_type, nonarray, get_cm_binding_array_def(),
      get_cm_lvalue_output_type_def(), get_cm_binding_type_def(),
      get_cm_global_expr_type_def(), get_cm_slot_expr_type_def(),
      get_theorem_by_name("COND_CLAUSES"));
  cm_tsrvar_add_facts(&rules, binding_case);
  vector_add(&rules, count_zero);
  cm_tsrvar_close_reduced(branch, rules);
}

PROOF static thm cm_prove_array_var_output_type(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (scope:int) (slot:int)
         (ty:cm_type).
         cm_expr_wf p (inth fid (cm_program_functions p))
           (CMVarE scope slot ty) ==>
         cm_binding_array p fid scope slot ==>
         cm_lvalue_output_type p
           (inth fid (cm_program_functions p))
           (CMVarE scope slot ty) == ty`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm expression_open = conv_rule(rewrite_conv(THM_LIST(
      get_cm_expr_wf_def())), assume_rule(
      `cm_expr_wf (p:cm_program)
        (inth (fid:int) (cm_program_functions p))
        (CMVarE (scope:int) (slot:int) (ty:cm_type))`));
  thm type_equal = conjunct2_rule(expression_open);
  thm array_ready = assume_rule(
      `cm_binding_array (p:cm_program) (fid:int)
        (scope:int) (slot:int)`);
  gnode_list global_cases = BOOL_CASES_TAC(
      leaf, `(scope:int) == 0i`, "Hglobal");
  {
    thm global = assume_rule(`(scope:int) == 0i`);
    thm array_open = conv_rule(reduce_rewrite_conv(THM_LIST(
        global, get_cm_binding_array_def())), array_ready);
    thm normalized_type = conv_rule(reduce_rewrite_conv(THM_LIST(
        global, array_open, get_cm_binding_type_def(),
        get_cm_global_expr_type_def(), get_cm_slot_expr_type_def(),
        get_theorem_by_name("COND_CLAUSES"))), type_equal);
    thm view = apply_conversion(reduce_rewrite_conv(THM_LIST(
        global, normalized_type, get_cm_lvalue_output_type_def())),
        goal_ccl(global_cases[0]->g));
    ACCEPT_TAC(global_cases[0], eqt_elim_rule(view));
  }
  gnode_list local_cases = BOOL_CASES_TAC(
      global_cases[1], `(scope:int) == 1i`, "Hlocal");
  {
    thm not_global = assume_rule(`~((scope:int) == 0i)`);
    thm local = assume_rule(`(scope:int) == 1i`);
    thm array_open = conv_rule(reduce_rewrite_conv(THM_LIST(
        not_global, local, get_cm_binding_array_def())), array_ready);
    thm normalized_type = conv_rule(reduce_rewrite_conv(THM_LIST(
        not_global, local, array_open, get_cm_binding_type_def(),
        get_cm_global_expr_type_def(), get_cm_slot_expr_type_def(),
        get_theorem_by_name("COND_CLAUSES"))), type_equal);
    thm view = apply_conversion(reduce_rewrite_conv(THM_LIST(
        not_global, local, normalized_type,
        get_cm_lvalue_output_type_def())),
        goal_ccl(local_cases[0]->g));
    ACCEPT_TAC(local_cases[0], eqt_elim_rule(view));
  }
  {
    thm impossible = conv_rule(reduce_rewrite_conv(THM_LIST(
        assume_rule(`~((scope:int) == 0i)`),
        assume_rule(`~((scope:int) == 1i)`),
        get_cm_binding_array_def())), array_ready);
    CONTR_TAC(local_cases[1], impossible);
  }
  return gnode_prove(root);
}
PROOF static thm cm_array_var_output_type =
    cm_prove_array_var_output_type();

PROOF static thm cm_prove_nonarray_var_output_type(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (scope:int) (slot:int)
         (ty:cm_type).
         cm_typed_program p ==>
         0i <= fid ==>
         fid < ilength (cm_program_functions p) ==>
         cm_expr_wf p (inth fid (cm_program_functions p))
           (CMVarE scope slot ty) ==>
         ~cm_binding_array p fid scope slot ==>
         cm_lvalue_output_type p
           (inth fid (cm_program_functions p))
           (CMVarE scope slot ty) == CMPtrTy ty`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm function_wf = mp_rule(mp_rule(mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`), cm_typed_function_at), assume_rule(
      `cm_typed_program (p:cm_program)`)),
      assume_rule(`0i <= (fid:int)`)), assume_rule(
      `(fid:int) < ilength (cm_program_functions (p:cm_program))`));
  thm function_open = conv_rule(rewrite_conv(THM_LIST(
      get_cm_function_wf_def())), function_wf);
  thm params_wf = conjunct1_rule(conjunct2_rule(function_open));
  thm params_open = conv_rule(rewrite_conv(THM_LIST(
      get_cm_params_wf_def())), params_wf);
  thm params_zero = conjunct2_rule(params_open);
  thm expression_open = conv_rule(rewrite_conv(THM_LIST(
      get_cm_expr_wf_def())), assume_rule(
      `cm_expr_wf (p:cm_program)
        (inth (fid:int) (cm_program_functions p))
        (CMVarE (scope:int) (slot:int) (ty:cm_type))`));
  thm binding_valid = conv_rule(rewrite_conv(THM_LIST(
      get_cm_binding_valid_def())), conjunct1_rule(expression_open));
  gnode_list cases = DISJ_CASES_TAC(
      leaf, binding_valid, "Hbinding");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    labeled_term_list assumptions = goal_lasmps(cases[i]->g);
    thm binding_case = assume_rule(assumptions[
        labeled_term_list_index(assumptions, "Hbinding")].tm);
    thm nonarray = assume_rule(
        `~cm_binding_array (p:cm_program) (fid:int)
          (scope:int) (slot:int)`);
    if (i == 0) {
      thm scope_zero = cm_tsrvar_pick_conjunct(
          binding_case, `(scope:int) == 0i`);
      thm count_zero = conv_rule(reduce_rewrite_conv(THM_LIST(
          scope_zero, get_cm_binding_array_def())), nonarray);
      cm_tsrvar_close_nonarray_branch(cases[i], expression_open,
          binding_case, scope_zero, count_zero);
    } else if (i == 1) {
      thm scope_one = cm_tsrvar_pick_conjunct(
          binding_case, `(scope:int) == 1i`);
      thm count_zero = conv_rule(reduce_rewrite_conv(THM_LIST(
          scope_one, get_cm_binding_array_def())), nonarray);
      cm_tsrvar_close_nonarray_branch(cases[i], expression_open,
          binding_case, scope_one, count_zero);
    } else {
      thm scope_two = cm_tsrvar_pick_conjunct(
          binding_case, `(scope:int) == 2i`);
      thm count_zero = mp_rule(mp_rule(spec_rule(
          `slot:int`, params_zero), cm_tsrvar_pick_conjunct(
            binding_case, `0i <= (slot:int)`)),
          cm_tsrvar_pick_conjunct(binding_case,
            `(slot:int) < ilength (cm_function_params
              (inth (fid:int) (cm_program_functions (p:cm_program))))`));
      cm_tsrvar_close_nonarray_branch(cases[i], expression_open,
          binding_case, scope_two, count_zero);
    }
  }
  return gnode_prove(root);
}
PROOF static thm cm_nonarray_var_output_type =
    cm_prove_nonarray_var_output_type();

PROOF static thm cm_prove_array_var_expr_value_ready(void) {
  term expression =
      `CMVarE (scope:int) (slot:int) (ty:cm_type)`;
  term value =
      `(if (scope:int) == 0i
       then cm_global_pointer (p:cm_program) (slot:int)
       else cm_state_env (st:cm_src_state) scope slot)`;
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (scope:int) (slot:int)
         (ty:cm_type) (st:cm_src_state).
         cm_expr_wf p (inth fid (cm_program_functions p))
           (CMVarE scope slot ty) ==>
         cm_binding_array p fid scope slot ==>
         cm_binding_address_ok p fid scope slot st ==>
         cm_expr_value_type_ready
           (CMVarE scope slot ty)
           (if scope == 0i then cm_global_pointer p slot
            else cm_state_env st scope slot)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm expression_wf = assume_rule(
      `cm_expr_wf (p:cm_program)
        (inth (fid:int) (cm_program_functions p))
        ${expression:cm_expr}`);
  thm output_equal = mp_rule(mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `scope:int`, `slot:int`,
      `ty:cm_type`), cm_array_var_output_type), expression_wf),
      assume_rule(`cm_binding_array (p:cm_program) (fid:int)
        (scope:int) (slot:int)`));
  thm compatible = mp_rule(mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `scope:int`, `slot:int`,
      `ty:cm_type`, `st:cm_src_state`),
      cm_binding_lvalue_type_ready), expression_wf), assume_rule(
        `cm_binding_address_ok (p:cm_program) (fid:int)
          (scope:int) (slot:int) (st:cm_src_state)`));
  compatible = conv_rule(rewrite_conv(THM_LIST(output_equal)),
      compatible);
  thm zero_clause = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(get_cm_zero_literal_def(),
        get_datatype_distinctness("cm_expr"))),
      `cm_zero_literal ${expression:cm_expr} ==>
       ${value:cm_value} == CMIntV 0i`));
  thm opened = conj_rule(compatible, zero_clause);
  thm target_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
      get_cm_expr_value_type_ready_def(), get_cm_expr_type_def())),
      goal_ccl(leaf->g));
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), opened));
  return gnode_prove(root);
}
PROOF static thm cm_array_var_expr_value_ready =
    cm_prove_array_var_expr_value_ready();

PROOF static thm cm_prove_nonarray_lvalue_output_type(void) {
  term function =
      `inth (fid:int) (cm_program_functions (p:cm_program))`;
  gnode root = gnode_new_with_ccl(
      `!(expr:cm_expr) (p:cm_program) (fid:int).
         cm_typed_program p ==>
         0i <= fid ==>
         fid < ilength (cm_program_functions p) ==>
         cm_expr_wf p (inth fid (cm_program_functions p)) expr ==>
         cm_lvalue expr ==>
         ~cm_expr_array p (inth fid (cm_program_functions p)) expr ==>
         cm_lvalue_output_type p
           (inth fid (cm_program_functions p)) expr ==
         CMPtrTy (cm_expr_type expr)`);
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list cases = DISJ_CASES_TAC(introduced,
      ispec_rule(`expr:cm_expr`, get_cm_expr_cases()), "Hex");
  term constructors[14] = {
    `CMConstE (a0:int) (a1:cm_type)`,
    `CMStringE (a0:int) (a1:cm_type)`,
    `CMVarE (a0:int) (a1:int) (a2:cm_type)`,
    `CMAssignE (a0:cm_expr) (a1:cm_expr) (a2:cm_type)`,
    `CMBinaryE (a0:int) (a1:cm_expr) (a2:cm_expr) (a3:cm_type)`,
    `CMUnaryE (a0:int) (a1:cm_expr) (a2:cm_type)`,
    `CMIndexE (a0:cm_expr) (a1:cm_expr) (a2:cm_type)`,
    `CMMemberE (a0:cm_expr) (a1:int) (a2:cm_type)`,
    `CMCallE (a0:int) (a1:(cm_expr)list) (a2:cm_type)`,
    `CMSizeofE (a0:cm_type) (a1:cm_type)`,
    `CMGetcE (a:cm_type)`,
    `CMPutcE (a0:cm_expr) (a1:cm_type)`,
    `CMPutiE (a0:cm_expr) (a1:cm_type)`,
    `CMExitE (a0:cm_expr) (a1:cm_type)`
  };
  for (size_t i = 0; i < vector_size(cases); ++i) {
    while (true) {
      labeled_term_list assumptions = goal_lasmps(cases[i]->g);
      int shape_index = labeled_term_list_index(assumptions, "Hex");
      if (!is_exists(assumptions[shape_index].tm)) break;
      cases[i] = ASMP_EXISTS_TAC(cases[i], "Hex", NULL);
    }
    gnode branch = cases[i];
    labeled_term_list assumptions = goal_lasmps(branch->g);
    thm shape = assume_rule(assumptions[
        labeled_term_list_index(assumptions, "Hex")].tm);
    thm shaped_wf = conv_rule(rewrite_conv(THM_LIST(shape)),
        assume_rule(
          `cm_expr_wf (p:cm_program) ${function:cm_function_d}
            (expr:cm_expr)`));
    thm shaped_lvalue = conv_rule(rewrite_conv(THM_LIST(shape)),
        assume_rule(`cm_lvalue (expr:cm_expr)`));
    thm shaped_nonarray = conv_rule(rewrite_conv(THM_LIST(shape)),
        assume_rule(
          `~cm_expr_array (p:cm_program) ${function:cm_function_d}
            (expr:cm_expr)`));
    thm target_view = apply_conversion(rewrite_conv(THM_LIST(shape)),
        goal_ccl(branch->g));
    if (i == 2) {
      thm normalized_nonarray = conv_rule(
          reduce_rewrite_conv(THM_LIST(get_cm_expr_array_def())),
          shaped_nonarray);
      thm binding_view = apply_conversion(
          reduce_rewrite_conv(THM_LIST(get_cm_binding_array_def())),
          `~cm_binding_array (p:cm_program) (fid:int)
            (a0:int) (a1:int)`);
      thm binding_nonarray =
          eq_mp_rule(sym_rule(binding_view), normalized_nonarray);
      thm result = mp_rule(mp_rule(mp_rule(mp_rule(mp_rule(
          specl_rule(TERM_LIST(
            `p:cm_program`, `fid:int`, `a0:int`, `a1:int`,
            `a2:cm_type`), cm_nonarray_var_output_type),
          assume_rule(`cm_typed_program (p:cm_program)`)),
          assume_rule(`0i <= (fid:int)`)), assume_rule(
            `(fid:int) <
             ilength (cm_program_functions (p:cm_program))`)),
          shaped_wf), binding_nonarray);
      thm result_view = apply_conversion(
          reduce_rewrite_conv(THM_LIST(get_cm_expr_type_def())),
          rhs_of(target_view));
      result = eq_mp_rule(sym_rule(result_view), result);
      ACCEPT_TAC(branch,
          eq_mp_rule(sym_rule(target_view), result));
    } else if (i == 5 || i == 6) {
      thm result = eqt_elim_rule(apply_conversion(
          reduce_rewrite_conv(THM_LIST(
            get_cm_lvalue_output_type_def(), get_cm_expr_type_def())),
          rhs_of(target_view)));
      ACCEPT_TAC(branch,
          eq_mp_rule(sym_rule(target_view), result));
    } else if (i == 7) {
      thm wf_open = conv_rule(reduce_rewrite_conv(THM_LIST(
          get_cm_expr_wf_def())), shaped_wf);
      thm result_type = cm_tsrvar_pick_conjunct(wf_open,
          `(a2:cm_type) ==
           cm_member_type (p:cm_program)
             (cm_expr_type (a0:cm_expr)) (a1:int)`);
      thm count_zero = conv_rule(reduce_rewrite_conv(THM_LIST(
          get_cm_expr_array_def())), shaped_nonarray);
      thm result = eqt_elim_rule(apply_conversion(
          reduce_rewrite_conv(THM_LIST(
            result_type, count_zero, get_cm_lvalue_output_type_def(),
            get_cm_member_lvalue_type_def(), get_cm_member_type_def(),
            get_cm_slot_expr_type_def(), get_cm_expr_type_def(),
            get_theorem_by_name("COND_CLAUSES"))),
          rhs_of(target_view)));
      ACCEPT_TAC(branch,
          eq_mp_rule(sym_rule(target_view), result));
    } else {
      thm impossible = conv_rule(reduce_rewrite_conv(THM_LIST(
          get_cm_lvalue_def())), shaped_lvalue);
      CONTR_TAC(branch, impossible);
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_nonarray_lvalue_output_type =
    cm_prove_nonarray_lvalue_output_type();

PROOF static thm cm_prove_r_var_type_ready_step(void) {
  term expression =
      `CMVarE (scope:int) (slot:int) (ty:cm_type)`;
  term task =
      `CMRTask (q:cm_program) (fid:int) ${expression:cm_expr}
        (st:cm_src_state) (ks:(cm_frame)list)`;
  term value =
      `(if (scope:int) == 0i
       then cm_global_pointer (p:cm_program) (slot:int)
       else cm_state_env (st:cm_src_state) scope slot)`;
  term linear_ann =
      `cm_ann_linear
        (cm_binding_address_code (p:cm_program) (fid:int)
          (scope:int) (slot:int))
        (ann:cm_annotation)`;
  term phase = `CALoadP (ty:cm_type)`;
  term old_cursors =
      `cm_ann_cursors (ann:cm_annotation)`;
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (q:cm_program) (fid:int) (scope:int)
         (slot:int) (ty:cm_type) (st:cm_src_state)
         (ks:(cm_frame)list) (ann:cm_annotation).
         cm_typed_program p ==>
         cm_task_succeeds
           (CMRTask q fid (CMVarE scope slot ty) st ks) ==>
         cm_task_type_ready p
           (CMRTask q fid (CMVarE scope slot ty) st ks) ann ==>
         cm_task_type_ready p
           (cm_step (CMRTask q fid (CMVarE scope slot ty) st ks))
           (cm_update_annotation
             (cm_annotation_step
               (CMRTask q fid (CMVarE scope slot ty) st ks) ann))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm task_ready = assume_rule(
      `cm_task_type_ready (p:cm_program) ${task:cm_task}
        (ann:cm_annotation)`);
  thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_task_type_ready_def())), task_ready);
  thm same_program = cm_tsrvar_pick_conjunct(
      opened, `(q:cm_program) == (p:cm_program)`);
  thm fid_low = cm_tsrvar_pick_conjunct(
      opened, `0i <= (fid:int)`);
  thm fid_high = cm_tsrvar_pick_conjunct(opened,
      `(fid:int) < ilength (cm_program_functions (p:cm_program))`);
  thm expression_wf = cm_tsrvar_pick_conjunct(opened,
      `cm_expr_wf (p:cm_program)
        (inth (fid:int) (cm_program_functions p))
        ${expression:cm_expr}`);
  thm expression_scalar = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_expr_type_def())), cm_tsrvar_pick_conjunct(opened,
        `cm_scalar_expr_type (cm_expr_type ${expression:cm_expr})`));
  thm cursors_ready = cm_tsrvar_pick_conjunct(opened,
      `cm_cursors_type_ready (p:cm_program) (fid:int)
        ${old_cursors:(cm_acursor)list}`);
  thm parent_input = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_expr_type_def())), cm_tsrvar_pick_conjunct(opened,
        `cm_cursor_head_input_type_ready (p:cm_program) (fid:int)
          (cm_expr_type ${expression:cm_expr})
          ${old_cursors:(cm_acursor)list}`));
  thm parent_values = cm_tsrvar_pick_conjunct(opened,
      `cm_cursor_expr_values_type_ready (p:cm_program) (fid:int)
        ${expression:cm_expr} ${old_cursors:(cm_acursor)list}`);
  gnode_list array_cases = BOOL_CASES_TAC(leaf,
      `cm_binding_array (p:cm_program) (fid:int)
        (scope:int) (slot:int)`, "Harray");
  {
    thm array_ready = assume_rule(
        `cm_binding_array (p:cm_program) (fid:int)
          (scope:int) (slot:int)`);
    thm succeeds = conv_rule(rewrite_conv(THM_LIST(same_program)),
        assume_rule(`cm_task_succeeds ${task:cm_task}`));
    thm address_ok = mp_rule(mp_rule(specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `scope:int`, `slot:int`,
        `ty:cm_type`, `st:cm_src_state`, `ks:(cm_frame)list`),
        cm_r_array_succeeds_address), succeeds), array_ready);
    thm value_ready = mp_rule(mp_rule(mp_rule(specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `scope:int`, `slot:int`,
        `ty:cm_type`, `st:cm_src_state`),
        cm_array_var_expr_value_ready), expression_wf), array_ready),
        address_ok);
    thm cursor_equal = eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          cm_ann_linear_def, cm_ann_plain_def, cm_ann_cursors_def)),
        `cm_ann_cursors ${linear_ann:cm_annotation} ==
         ${old_cursors:(cm_acursor)list}`));
    thm result = mp_rule(mp_rule(mp_rule(specl_rule(TERM_LIST(
        `p:cm_program`, `q:cm_program`, `fid:int`, expression,
        `st:cm_src_state`, `ks:(cm_frame)list`, `ann:cm_annotation`,
        value, `st:cm_src_state`, linear_ann),
        cm_r_value_task_ready), task_ready), value_ready), cursor_equal);
    result = conv_rule(rewrite_conv(THM_LIST(same_program)), result);
    thm target_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
        same_program, array_ready, address_ok,
        get_cm_step_def(), get_cm_rstart_def(), cm_annotation_step_def,
        cm_update_r_def, cm_update_annotation_def)),
        goal_ccl(array_cases[0]->g));
    ACCEPT_TAC(array_cases[0],
        eq_mp_rule(sym_rule(target_view), result));
  }
  {
    thm not_array = assume_rule(
        `~cm_binding_array (p:cm_program) (fid:int)
          (scope:int) (slot:int)`);
    thm output_equal = mp_rule(mp_rule(mp_rule(mp_rule(
        specl_rule(TERM_LIST(
          `p:cm_program`, `fid:int`, `scope:int`, `slot:int`,
          `ty:cm_type`), cm_nonarray_var_output_type),
        assume_rule(`cm_typed_program (p:cm_program)`)), fid_low),
        fid_high), expression_wf);
    output_equal = mp_rule(output_equal, not_array);
    thm phase_static = eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          get_cm_phase_static_type_ready_def(), expression_scalar)),
        `cm_phase_static_type_ready (p:cm_program) (fid:int)
          ${phase:cm_aphase}`));
    thm phase_parent = eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          get_cm_phase_parent_type_ready_def(), parent_input)),
        `cm_phase_parent_type_ready (p:cm_program) (fid:int)
          ${phase:cm_aphase} ${old_cursors:(cm_acursor)list}`));
    thm parent_nonzero = eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          get_cm_zero_literal_def(),
          get_datatype_distinctness("cm_expr"))),
        `~cm_zero_literal ${expression:cm_expr}`));
    thm phase_results = eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          get_cm_phase_result_type_def(), get_cm_expr_type_def())),
        `!(result:cm_type).
           cm_phase_result_type (p:cm_program) (fid:int)
             ${phase:cm_aphase} result ==>
           result == cm_expr_type ${expression:cm_expr}`));
    thm next_fid = eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(cm_phase_next_fid_def)),
        `cm_phase_next_fid (fid:int) ${phase:cm_aphase} == fid`));
    thm phase_result = mp_rule(mp_rule(mp_rule(mp_rule(
        specl_rule(TERM_LIST(
          `p:cm_program`, `fid:int`, phase, expression, old_cursors),
          cm_phase_result_from_expr), parent_values), parent_nonzero),
        phase_results), next_fid);
    term next_rest_term =
        `cm_cursors_type_ready (p:cm_program)
          (cm_phase_next_fid (fid:int) ${phase:cm_aphase})
          ${old_cursors:(cm_acursor)list}`;
    thm next_rest_view = apply_conversion(
        reduce_rewrite_conv(THM_LIST(cm_phase_next_fid_def)),
        next_rest_term);
    thm next_rest = eq_mp_rule(
        sym_rule(next_rest_view), cursors_ready);
    thm new_ready = specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, phase,
        `cm_ann_temp (ann:cm_annotation)`, `cm_ann_break ann`,
        `cm_ann_continue ann`, old_cursors),
        cm_cursor_push_type_ready);
    new_ready = mp_rule(new_ready, phase_static);
    new_ready = mp_rule(new_ready, phase_parent);
    new_ready = mp_rule(new_ready, phase_result);
    new_ready = mp_rule(new_ready, next_rest);
    thm phase_input = eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          get_cm_phase_input_type_ready_def())),
        `cm_phase_input_type_ready (p:cm_program) (fid:int)
          ${phase:cm_aphase} (CMPtrTy (ty:cm_type))`));
    thm new_input = mp_rule(specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, phase, `CMPtrTy (ty:cm_type)`,
        `cm_ann_temp (ann:cm_annotation)`, `cm_ann_break ann`,
        `cm_ann_continue ann`, old_cursors),
        cm_cursor_push_input_ready), phase_input);
    thm phase_lvalue = eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          get_cm_phase_lvalue_type_ready_def(),
          get_cm_phase_value_type_ready_def())),
        `cm_phase_lvalue_type_ready (p:cm_program) (fid:int)
          ${phase:cm_aphase} (CMPtrTy (ty:cm_type))`));
    thm new_lvalue = mp_rule(specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, phase, `CMPtrTy (ty:cm_type)`,
        `cm_ann_temp (ann:cm_annotation)`, `cm_ann_break ann`,
        `cm_ann_continue ann`, old_cursors),
        cm_cursor_push_lvalue_ready), phase_lvalue);
    thm target_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
        same_program, fid_low, fid_high, expression_wf, output_equal,
        new_ready, new_input, new_lvalue, not_array,
        get_cm_lvalue_def(), get_cm_task_type_ready_def(),
        get_cm_step_def(), get_cm_rstart_def(), cm_annotation_step_def,
        cm_update_r_def, cm_update_annotation_def, cm_ann_push_def,
        cm_ann_cursors_def)), goal_ccl(array_cases[1]->g));
    ACCEPT_TAC(array_cases[1], eqt_elim_rule(target_view));
  }
  return gnode_prove(root);
}
PROOF thm cm_r_var_type_ready_step =
    cm_prove_r_var_type_ready_step();

PROOF static int cmc_preservation_type_source_r_var_final_checks(void) {
  ENSURE_COND(vector_size(hyp(cm_array_var_output_type)) == 0 &&
      vector_size(hyp(cm_nonarray_var_output_type)) == 0 &&
      vector_size(hyp(cm_array_var_expr_value_ready)) == 0 &&
      vector_size(hyp(cm_nonarray_lvalue_output_type)) == 0 &&
      vector_size(hyp(cm_r_var_type_ready_step)) == 0,
      "variable type theorem has assumptions");
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_type_source_r_var_axioms_before,
      "cmc_preservation_type_source_r_var introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_type_source_r_var_checks =
    cmc_preservation_type_source_r_var_final_checks();
