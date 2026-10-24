#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_annotate_erasure.h"
#include "cmc_preservation_spill_update.h"
#include "cmc_preservation_ready_coordinate.h"

#require "cmc_annotate_erasure.c"
#require "cmc_preservation_spill_transition.c"
#require "cmc_preservation_ready_coordinate.c"

PROOF static size_t _cmc_preservation_spill_update_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_prove_annotation_spill_cond(void) {
  gnode root = gnode_new_with_ccl(
      `!(condition:bool) (yes:cm_annotation) (no:cm_annotation).
         cm_annotation_spill_consistent
          (if condition then yes else no) <=>
         (if condition
          then cm_annotation_spill_consistent yes
          else cm_annotation_spill_consistent no)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list cases = BOOL_CASES_TAC(
      leaf, `condition:bool`, "Hcondition");
  for (size_t index = 0; index < vector_size(cases); ++index) {
    CONV_WITH_ASMP_TAC(cases[index], reduce_rewrite_conv, THM_LIST());
  }
  return gnode_prove(root);
}

PROOF thm cm_annotation_spill_cond =
    cm_prove_annotation_spill_cond();

PROOF static thm cm_prove_temp_plus_length_bound(void) {
  gnode root = gnode_new_with_ccl(
      `!(temp:int) (items:(A)list).
         temp <= temp + ilength items`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm nonnegative = ispec_rule(
      `items:(A)list`, get_theorem_by_name("ILENGTH_NONNEG"));
  ACCEPT_TAC(leaf, mp_rule(int_arith_rule(
      `0i <= ilength (items:(A)list) ==>
       (temp:int) <= temp + ilength items`), nonnegative));
  return gnode_prove(root);
}

PROOF static thm cm_temp_plus_length_bound =
    cm_prove_temp_plus_length_bound();

PROOF static thm cm_prove_annotation_spill_linear(void) {
  gnode root = gnode_new_with_ccl(
      `!(code:(tvm_inst)list) (ann:cm_annotation).
         cm_annotation_spill_consistent ann ==>
         cm_annotation_spill_consistent (cm_ann_linear code ann)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm result = mp_rule(specl_rule(TERM_LIST(
      `ann:cm_annotation`,
      `cm_ann_pc (ann:cm_annotation) +
        ilength (code:(tvm_inst)list)`,
      `cm_ann_break ann`, `cm_ann_continue ann`),
      cm_annotation_spill_plain), assume_rule(
        `cm_annotation_spill_consistent (ann:cm_annotation)`));
  gnode reduced = CONV_TAC(leaf,
      rewrite_conv(THM_LIST(cm_ann_linear_def)));
  ACCEPT_TAC(reduced, result);
  return gnode_prove(root);
}

PROOF static thm cm_annotation_spill_linear =
    cm_prove_annotation_spill_linear();

PROOF static thm cm_prove_annotation_spill_enter_call_same(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (caller:int) (callee:int) (st:cm_src_state)
         (ret:cm_type) (returnpc:int) (ann:cm_annotation).
         cm_annotation_spill_consistent ann ==>
         cm_annotation_spill_consistent
           (cm_ann_enter_call p caller callee st ret returnpc
             (cm_ann_temp ann) (cm_ann_break ann)
             (cm_ann_continue ann) (cm_ann_cursors ann)
             (cm_ann_spills ann) (cm_ann_saved ann)
             (cm_ann_calls ann))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm old_consistent = assume_rule(
      `cm_annotation_spill_consistent (ann:cm_annotation)`);
  thm cursors = conv_rule(rewrite_conv(THM_LIST(
      cm_annotation_spill_consistent_def)), old_consistent);
  thm result = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `caller:int`, `callee:int`, `st:cm_src_state`,
      `ret:cm_type`, `returnpc:int`, `cm_ann_temp (ann:cm_annotation)`,
      `cm_ann_break ann`, `cm_ann_continue ann`, `cm_ann_cursors ann`,
      `cm_ann_spills ann`, `cm_ann_saved ann`, `cm_ann_calls ann`),
      cm_annotation_spill_enter_call), cursors);
  ACCEPT_TAC(leaf, result);
  return gnode_prove(root);
}

PROOF static thm cm_annotation_spill_enter_call_same =
    cm_prove_annotation_spill_enter_call_same();

PROOF static thm_list cm_spill_update_rules(void) {
  return THM_LIST(
      cm_update_annotation_cond, cm_annotation_spill_cond,
      cm_annotation_spill_plain, cm_annotation_spill_linear,
      cm_annotation_spill_push,
      cm_annotation_spill_enter_call_same,
      cm_phase_spill_consistent_def, cm_staged_spills_def,
      cm_phase_is_call_def,
      cm_update_annotation_def,
      cm_ann_pc_def, cm_ann_temp_def, cm_ann_break_def,
      cm_ann_continue_def, cm_ann_cursors_def, cm_ann_spills_def,
      cm_ann_saved_def, cm_ann_calls_def,
      cm_cursor_temp_def, cm_cursor_phase_def,
      cm_spill_frame_spills_def,
      cm_temp_plus_length_bound,
      get_theorem_by_name("ILENGTH_DEF"),
      get_theorem_by_name("HD"), get_theorem_by_name("TL"),
      get_theorem_by_name("NOT_CONS_NIL"));
}

PROOF static term cm_spill_update_annotation_term(void) {
  return `CMAnnotation (pc:int) (temp:int) (breakpc:int)
      (continuepc:int) (cursors:(cm_acursor)list)
      (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
      (calls:(cm_call_sim_frame)list)`;
}

PROOF static thm cm_spill_update_old_fact(void) {
  return assume_rule(mk_comb(
      `cm_annotation_spill_consistent`,
      cm_spill_update_annotation_term()));
}

PROOF static thm cm_spill_update_linear_fact(const term code) {
  return mp_rule(specl_rule(TERM_LIST(
      code, cm_spill_update_annotation_term()),
      cm_annotation_spill_linear), cm_spill_update_old_fact());
}

PROOF static thm cm_spill_update_plain_fact(const term next_pc) {
  thm result = mp_rule(specl_rule(TERM_LIST(
      cm_spill_update_annotation_term(), next_pc,
      `breakpc:int`, `continuepc:int`),
      cm_annotation_spill_plain), cm_spill_update_old_fact());
  return conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_ann_temp_def)), result);
}

PROOF static thm cm_spill_update_push_fact(
    const term phase, const term new_temp) {
  term call_proposition = mk_comb(`cm_phase_is_call`, phase);
  thm not_call = eqf_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(cm_phase_is_call_def)),
      call_proposition));
  term phase_proposition = mk_comb(mk_comb(mk_comb(mk_comb(
      `cm_phase_spill_consistent`, new_temp), `temp:int`),
      phase), `spills:(cm_spill)list`);
  thm phase_view = apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        cm_phase_spill_consistent_def, cm_staged_spills_def,
        cm_temp_plus_length_bound,
        get_theorem_by_name("ILENGTH_DEF"))),
      phase_proposition);
  struct dest_eq_results phase_sides = dest_eq(concl(phase_view));
  thm phase_consistent = eq_mp_rule(sym_rule(phase_view),
      int_arith_rule(phase_sides.tm2));
  thm pending = mp_rule(mp_rule(specl_rule(TERM_LIST(
      cm_spill_update_annotation_term(), phase, `pc:int`,
      new_temp, `breakpc:int`, `continuepc:int`),
      cm_annotation_spill_push), cm_spill_update_old_fact()),
      not_call);
  pending = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_ann_pc_def, cm_ann_temp_def, cm_ann_break_def,
      cm_ann_continue_def, cm_ann_spills_def)), pending);
  return mp_rule(pending, phase_consistent);
}

PROOF static thm cm_spill_update_arg_push_fact(void) {
  term phase =
      `CAArgP (a0:int) (TL (a1:(cm_expr)list))
        ([]:(cm_value)list) (a2:cm_type)
        (a1:(cm_expr)list) (temp:int) (temp:int)
        (temp + ilength a1)`;
  term new_temp = `(temp:int) + ilength (a1:(cm_expr)list)`;
  thm not_call = eqf_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(cm_phase_is_call_def)),
      mk_comb(`cm_phase_is_call`, phase)));
  thm args_length = mp_rule(ispec_rule(
      `a1:(cm_expr)list`, cm_ilength_nonempty_tail),
      assume_rule(`~((a1:(cm_expr)list) == [])`));
  term phase_proposition = mk_comb(mk_comb(mk_comb(mk_comb(
      `cm_phase_spill_consistent`, new_temp), `temp:int`),
      phase), `spills:(cm_spill)list`);
  thm phase_view = apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        cm_phase_spill_consistent_def, cm_staged_spills_def,
        cm_temp_plus_length_bound, args_length,
        get_theorem_by_name("ILENGTH_DEF"))),
      phase_proposition);
  struct dest_eq_results phase_sides = dest_eq(concl(phase_view));
  thm phase_consistent = eq_mp_rule(sym_rule(phase_view),
      int_arith_rule(phase_sides.tm2));
  thm pending = mp_rule(mp_rule(specl_rule(TERM_LIST(
      cm_spill_update_annotation_term(), phase, `pc:int`,
      new_temp, `breakpc:int`, `continuepc:int`),
      cm_annotation_spill_push), cm_spill_update_old_fact()),
      not_call);
  pending = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_ann_pc_def, cm_ann_temp_def, cm_ann_break_def,
      cm_ann_continue_def, cm_ann_spills_def)), pending);
  return mp_rule(pending, phase_consistent);
}

PROOF static thm cm_spill_update_enter_call_fact(
    const term callee, const term ret) {
  thm result = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, callee, `st:cm_src_state`, ret,
      `(pc:int) + 1i`, cm_spill_update_annotation_term()),
      cm_annotation_spill_enter_call_same),
      cm_spill_update_old_fact());
  return conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_ann_temp_def, cm_ann_break_def, cm_ann_continue_def,
      cm_ann_cursors_def, cm_ann_spills_def, cm_ann_saved_def,
      cm_ann_calls_def)), result);
}

PROOF static void cm_spill_update_accept_result(
    gnode branch, const thm result, const thm_list rules) {
  thm_list proof_rules = THM_LIST();
  for (size_t rule_index = 0;
       rule_index < vector_size(rules); ++rule_index) {
    vector_add(&proof_rules, rules[rule_index]);
  }
  labeled_term_list assumptions = goal_lasmps(branch->g);
  for (size_t assumption_index = 0;
       assumption_index < vector_size(assumptions);
       ++assumption_index) {
    vector_add(&proof_rules,
        assume_rule(assumptions[assumption_index].tm));
  }
  thm normalized_result = result;
  for (size_t pass = 0; pass < 3; ++pass) {
    normalized_result = conv_rule(
        reduce_rewrite_conv(proof_rules), normalized_result);
  }
  vector_add(&proof_rules, normalized_result);
  thm target_view = apply_conversion(
      reduce_rewrite_conv(proof_rules), goal_ccl(branch->g));
  for (size_t pass = 0; pass < 3; ++pass) {
    struct dest_eq_results sides = dest_eq(concl(target_view));
    thm next_view = apply_conversion(
        reduce_rewrite_conv(proof_rules), sides.tm2);
    target_view = trans_rule(target_view, next_view);
  }
  struct dest_eq_results final_sides = dest_eq(concl(target_view));
  if (alpha_compare(concl(normalized_result),
        final_sides.tm2) == 0) {
    ACCEPT_TAC(branch,
        eq_mp_rule(sym_rule(target_view), normalized_result));
    return;
  }
  ACCEPT_TAC(branch, eqt_elim_rule(target_view));
}

PROOF static void cm_spill_update_close(
    gnode branch, const thm_list rules) {
  gnode reduced = CONV_WITH_ASMP_TAC(
      branch, reduce_rewrite_conv, rules);
  if (IS_NULL(reduced->solved)) {
    reduced = CONV_WITH_ASMP_TAC(
        reduced, reduce_rewrite_conv, rules);
  }
  if (!IS_NULL(reduced->solved)) return;
  gnode_list decomposed = AUTO_ASMP_DESTRUCT_TAC(reduced);
  for (size_t branch_index = 0;
       branch_index < vector_size(decomposed); ++branch_index) {
    labeled_term_list branch_assumptions =
        goal_lasmps(decomposed[branch_index]->g);
    thm_list assumption_rules = THM_LIST();
    for (size_t assumption_index = 0;
         assumption_index < vector_size(branch_assumptions);
         ++assumption_index) {
      vector_add(&assumption_rules,
          assume_rule(branch_assumptions[assumption_index].tm));
    }
    thm_list leaf_rules = THM_LIST();
    for (size_t rule_index = 0;
         rule_index < vector_size(rules); ++rule_index) {
      vector_add(&leaf_rules, rules[rule_index]);
      vector_add(&leaf_rules, conv_rule(
          reduce_rewrite_conv(assumption_rules), rules[rule_index]));
    }
    gnode closed = CONV_WITH_ASMP_TAC(
        decomposed[branch_index], reduce_rewrite_conv, leaf_rules);
    if (IS_NULL(closed->solved)) {
      labeled_term_list assumptions = goal_lasmps(closed->g);
      for (size_t fact_index = 0;
           fact_index < vector_size(assumptions); ++fact_index) {
        thm normalized = conv_rule(
            reduce_rewrite_conv(leaf_rules),
            assume_rule(assumptions[fact_index].tm));
        if (alpha_compare(concl(normalized),
              goal_ccl(closed->g)) == 0) {
          ACCEPT_TAC(closed, normalized);
          break;
        }
      }
    }
    if (IS_NULL(closed->solved)) {
      thm arithmetic = int_arith_rule(goal_ccl(closed->g));
      ACCEPT_TAC(closed, arithmetic);
    }
  }
}

PROOF static thm cm_prove_update_r_spill_consistent(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (expr:cm_expr) (st:cm_src_state)
         (pc:int) (temp:int) (breakpc:int) (continuepc:int)
         (cursors:(cm_acursor)list) (spills:(cm_spill)list)
         (saved:(cm_spill_frame)list)
         (calls:(cm_call_sim_frame)list).
         cm_annotation_spill_consistent
          (CMAnnotation pc temp breakpc continuepc
            cursors spills saved calls) ==>
         cm_annotation_spill_consistent
          (cm_update_annotation
            (cm_update_r p fid st
              (CMAnnotation pc temp breakpc continuepc
                cursors spills saved calls)
              expr))`);
  gnode introduced = AUTO_INTROS_TAC(root);
  thm cases_theorem = ispec_rule(`expr:cm_expr`, get_cm_expr_cases());
  gnode_list cases = DISJ_CASES_TAC(
      introduced, cases_theorem, "Hex");
  thm_list base_rules = cm_spill_update_rules();
  vector_add(&base_rules, cm_update_r_def);
  for (size_t index = 0; index < vector_size(cases); ++index) {
    while (true) {
      labeled_term_list assumptions = goal_lasmps(cases[index]->g);
      int shape_index = labeled_term_list_index(assumptions, "Hex");
      if (!is_exists(assumptions[shape_index].tm)) break;
      cases[index] = ASMP_EXISTS_TAC(cases[index], "Hex", NULL);
    }
    thm_list branch_rules = THM_LIST();
    for (size_t rule_index = 0;
         rule_index < vector_size(base_rules); ++rule_index) {
      vector_add(&branch_rules, base_rules[rule_index]);
    }
    if (index == 0) {
      vector_add(&branch_rules, cm_spill_update_linear_fact(
          `cm_push_code
            (cm_const_immediate (a1:cm_type) (a0:int))`));
    } else if (index == 1) {
      vector_add(&branch_rules, cm_spill_update_linear_fact(
          `cm_push_code
            (cm_string_address (p:cm_program) (a0:int))`));
    } else if (index == 2) {
      vector_add(&branch_rules, cm_spill_update_linear_fact(
          `cm_binding_address_code (p:cm_program) (fid:int)
            (a0:int) (a1:int)`));
      vector_add(&branch_rules, cm_spill_update_push_fact(
          `CALoadP (a2:cm_type)`, `temp:int`));
    } else if (index == 3) {
      vector_add(&branch_rules, cm_spill_update_push_fact(
          `CAAssignLP (a1:cm_expr) (a2:cm_type)`, `temp:int`));
    } else if (index == 4) {
      vector_add(&branch_rules, cm_spill_update_push_fact(
          `CABinLP (a0:int) (a1:cm_expr) (a2:cm_expr)
            (a3:cm_type)`, `temp:int`));
    } else if (index == 5) {
      vector_add(&branch_rules, cm_spill_update_push_fact(
          `CALoadP (a2:cm_type)`, `temp:int`));
      vector_add(&branch_rules, cm_spill_update_push_fact(
          `CAUnaryP (a0:int)`, `temp:int`));
    } else if (index == 6) {
      vector_add(&branch_rules, cm_spill_update_push_fact(
          `CALoadP (a2:cm_type)`, `temp:int`));
    } else if (index == 7) {
      vector_add(&branch_rules, cm_spill_update_push_fact(
          `CALoadP (a2:cm_type)`, `temp:int`));
    } else if (index == 8) {
      vector_add(&branch_rules, cm_spill_update_enter_call_fact(
          `a0:int`, `a2:cm_type`));
      gnode_list args_cases = BOOL_CASES_TAC(
          cases[index], `(a1:(cm_expr)list) == []`, "Hargs");
      cm_spill_update_close(args_cases[0], branch_rules);
      thm_list nonempty_rules = THM_LIST();
      for (size_t rule_index = 0;
           rule_index < vector_size(branch_rules); ++rule_index) {
        vector_add(&nonempty_rules, branch_rules[rule_index]);
      }
      vector_add(&nonempty_rules, cm_spill_update_arg_push_fact());
      cm_spill_update_close(args_cases[1], nonempty_rules);
      continue;
    } else if (index == 9) {
      vector_add(&branch_rules, cm_spill_update_linear_fact(
          `cm_push_code
            (cm_type_size (cm_program_structs (p:cm_program))
              (a0:cm_type))`));
    } else if (index == 10) {
      vector_add(&branch_rules, cm_spill_update_plain_fact(
          `(pc:int) + 1i`));
    } else if (index == 11) {
      vector_add(&branch_rules, cm_spill_update_push_fact(
          `CAPutcP`, `temp:int`));
    } else if (index == 12) {
      vector_add(&branch_rules, cm_spill_update_push_fact(
          `CAPutiP`, `temp:int`));
    } else if (index == 13) {
      vector_add(&branch_rules, cm_spill_update_push_fact(
          `CAExitP`, `temp:int`));
    }
    cm_spill_update_close(cases[index], branch_rules);
  }
  return gnode_prove(root);
}

PROOF thm cm_update_r_spill_consistent =
    cm_prove_update_r_spill_consistent();
PROOF static thm cm_prove_update_l_spill_consistent(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (expr:cm_expr) (st:cm_src_state)
         (pc:int) (temp:int) (breakpc:int) (continuepc:int)
         (cursors:(cm_acursor)list) (spills:(cm_spill)list)
         (saved:(cm_spill_frame)list)
         (calls:(cm_call_sim_frame)list).
         cm_annotation_spill_consistent
          (CMAnnotation pc temp breakpc continuepc
            cursors spills saved calls) ==>
         cm_annotation_spill_consistent
          (cm_update_annotation
            (cm_update_l p fid st
              (CMAnnotation pc temp breakpc continuepc
                cursors spills saved calls)
              expr))`);
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list cases = DISJ_CASES_TAC(
      introduced,
      ispec_rule(`expr:cm_expr`, get_cm_expr_cases()), "Hex");
  thm_list base_rules = cm_spill_update_rules();
  vector_add(&base_rules, cm_update_l_def);
  for (size_t index = 0; index < vector_size(cases); ++index) {
    while (true) {
      labeled_term_list assumptions = goal_lasmps(cases[index]->g);
      int shape_index = labeled_term_list_index(assumptions, "Hex");
      if (!is_exists(assumptions[shape_index].tm)) break;
      cases[index] = ASMP_EXISTS_TAC(cases[index], "Hex", NULL);
    }
    thm_list branch_rules = THM_LIST();
    for (size_t rule_index = 0;
         rule_index < vector_size(base_rules); ++rule_index) {
      vector_add(&branch_rules, base_rules[rule_index]);
    }
    if (index == 2) {
      vector_add(&branch_rules, cm_spill_update_linear_fact(
          `cm_binding_address_code (p:cm_program) (fid:int)
            (a0:int) (a1:int)`));
    } else if (index == 6) {
      vector_add(&branch_rules, cm_spill_update_push_fact(
          `CAIndexLP (a1:cm_expr) (a2:cm_type)`, `temp:int`));
    } else if (index == 7) {
      vector_add(&branch_rules, cm_spill_update_push_fact(
          `CAMemberP (a1:int) (cm_expr_type (a0:cm_expr))`,
          `temp:int`));
    }
    cm_spill_update_close(cases[index], branch_rules);
  }
  return gnode_prove(root);
}

PROOF thm cm_update_l_spill_consistent =
    cm_prove_update_l_spill_consistent();
PROOF static thm cm_prove_update_s_spill_consistent(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (stmt:cm_stmt) (st:cm_src_state)
         (pc:int) (temp:int) (breakpc:int) (continuepc:int)
         (cursors:(cm_acursor)list) (spills:(cm_spill)list)
         (saved:(cm_spill_frame)list)
         (calls:(cm_call_sim_frame)list).
         cm_annotation_spill_consistent
          (CMAnnotation pc temp breakpc continuepc
            cursors spills saved calls) ==>
         cm_annotation_spill_consistent
          (cm_update_annotation
            (cm_update_s p fid st
              (CMAnnotation pc temp breakpc continuepc
                cursors spills saved calls)
              stmt))`);
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list cases = DISJ_CASES_TAC(
      introduced,
      ispec_rule(`stmt:cm_stmt`, get_cm_stmt_cases()), "Hstmt");
  thm_list base_rules = cm_spill_update_rules();
  vector_add(&base_rules, cm_update_s_def);
  for (size_t index = 0; index < vector_size(cases); ++index) {
    while (true) {
      labeled_term_list assumptions = goal_lasmps(cases[index]->g);
      int shape_index = labeled_term_list_index(assumptions, "Hstmt");
      if (!is_exists(assumptions[shape_index].tm)) break;
      cases[index] = ASMP_EXISTS_TAC(cases[index], "Hstmt", NULL);
    }
    thm_list branch_rules = THM_LIST();
    for (size_t rule_index = 0;
         rule_index < vector_size(base_rules); ++rule_index) {
      vector_add(&branch_rules, base_rules[rule_index]);
    }
    if (index == 1) {
      vector_add(&branch_rules, cm_spill_update_push_fact(
          `CAExprStmtP`, `temp:int`));
    } else if (index == 3) {
      vector_add(&branch_rules, cm_spill_update_push_fact(
          `CAInitP (a0:int)`, `temp:int`));
    } else if (index == 4) {
      vector_add(&branch_rules, cm_spill_update_push_fact(
          `CASeqP (a1:cm_stmt)`, `temp:int`));
    } else if (index == 5) {
      vector_add(&branch_rules, cm_spill_update_push_fact(
          `CABlockP (cm_state_env (st:cm_src_state))
            (cm_state_regions st) F 0i`, `temp:int`));
    } else if (index == 6) {
      vector_add(&branch_rules, cm_spill_update_push_fact(
          `CAIfP (a1:cm_stmt) (a2:cm_stmt)`, `temp:int`));
    } else if (index == 7) {
      vector_add(&branch_rules, cm_spill_update_push_fact(
          `CAWhileGuardP (a0:cm_expr) (a1:cm_stmt) (pc:int)
            (pc + cm_stmt_code_count (p:cm_program) (fid:int)
              (CMWhileS a0 a1))`, `temp:int`));
    } else if (index == 10) {
      vector_add(&branch_rules, cm_spill_update_push_fact(
          `CAReturnP`, `temp:int`));
    }
    cm_spill_update_close(cases[index], branch_rules);
  }
  return gnode_prove(root);
}

PROOF thm cm_update_s_spill_consistent =
    cm_prove_update_s_spill_consistent();
PROOF static term cm_spill_update_cursor_annotation(const term phase) {
  return `CMAnnotation (pc:int) (temp:int) (breakpc:int)
      (continuepc:int)
      (CMACursor ${phase:cm_aphase} (owner:int)
        (owner_break:int) (owner_continue:int) ::
        (cursor_rest:(cm_acursor)list))
      (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
      (calls:(cm_call_sim_frame)list)`;
}

PROOF static thm cm_spill_update_cursor_old_fact(const term phase) {
  thm phase_shape = assume_rule(mk_eq(`phase:cm_aphase`, phase));
  thm old_consistent = assume_rule(
      `cm_annotation_spill_consistent
        (CMAnnotation (pc:int) (temp:int) (breakpc:int)
          (continuepc:int)
          (CMACursor (phase:cm_aphase) (owner:int)
            (owner_break:int) (owner_continue:int) ::
            (cursor_rest:(cm_acursor)list))
          (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
          (calls:(cm_call_sim_frame)list))`);
  return conv_rule(rewrite_conv(THM_LIST(phase_shape)),
      old_consistent);
}

PROOF static thm cm_spill_update_coordinate_fact(const term phase) {
  thm phase_shape = assume_rule(mk_eq(`phase:cm_aphase`, phase));
  return conv_rule(reduce_rewrite_conv(THM_LIST(
      phase_shape, cm_phase_child_temp_def)), assume_rule(
        `temp == cm_phase_child_temp
          (phase:cm_aphase) (owner:int)`));
}

PROOF static thm cm_spill_update_pop_raw_fact(
    const term phase, const term next_pc) {
  thm not_call = eqf_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(cm_phase_is_call_def)),
      mk_comb(`cm_phase_is_call`, phase)));
  thm result = mp_rule(mp_rule(specl_rule(TERM_LIST(
      phase, `pc:int`, `temp:int`, `breakpc:int`, `continuepc:int`,
      `owner:int`, `owner_break:int`, `owner_continue:int`,
      `cursor_rest:(cm_acursor)list`, `spills:(cm_spill)list`,
      `saved:(cm_spill_frame)list`,
      `calls:(cm_call_sim_frame)list`, next_pc),
      cm_annotation_spill_pop),
      cm_spill_update_cursor_old_fact(phase)), not_call);
  return result;
}
PROOF static thm cm_spill_update_pop_fact(
    const term phase, const term next_pc) {
  thm result = cm_spill_update_pop_raw_fact(phase, next_pc);
  return conv_rule(rewrite_conv(THM_LIST(
      cm_spill_update_coordinate_fact(phase))), result);
}


PROOF static thm cm_spill_update_replace_raw_fact(
    const term old_phase, const term new_phase,
    const term next_pc, const term next_temp,
    const term next_break, const term next_continue,
    const thm_list extra_rules) {
  thm old_not_call = eqf_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(cm_phase_is_call_def)),
      mk_comb(`cm_phase_is_call`, old_phase)));
  thm new_not_call = eqf_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(cm_phase_is_call_def)),
      mk_comb(`cm_phase_is_call`, new_phase)));
  term phase_proposition = mk_comb(mk_comb(mk_comb(mk_comb(
      `cm_phase_spill_consistent`, next_temp), `owner:int`),
      new_phase), `spills:(cm_spill)list`);
  thm_list phase_rules = THM_LIST(
      cm_phase_spill_consistent_def, cm_staged_spills_def,
      cm_spill_holds_put_same);
  for (size_t index = 0;
       index < vector_size(extra_rules); ++index) {
    vector_add(&phase_rules, extra_rules[index]);
  }
  thm phase_view = apply_conversion(
      reduce_rewrite_conv(phase_rules), phase_proposition);
  struct dest_eq_results phase_sides = dest_eq(concl(phase_view));
  thm phase_consistent = eq_mp_rule(sym_rule(phase_view),
      int_arith_rule(phase_sides.tm2));
  thm pending = mp_rule(mp_rule(mp_rule(specl_rule(TERM_LIST(
      old_phase, new_phase,
      `pc:int`, `temp:int`, `breakpc:int`, `continuepc:int`,
      `owner:int`, `owner_break:int`, `owner_continue:int`,
      `cursor_rest:(cm_acursor)list`, `spills:(cm_spill)list`,
      `saved:(cm_spill_frame)list`,
      `calls:(cm_call_sim_frame)list`,
      next_pc, next_temp, next_break, next_continue),
      cm_annotation_spill_replace),
      cm_spill_update_cursor_old_fact(old_phase)), old_not_call),
      new_not_call);
  return mp_rule(pending, phase_consistent);
}
PROOF static thm cm_spill_update_replace_fact(
    const term old_phase, const term new_phase,
    const term next_pc, const term next_temp,
    const term next_break, const term next_continue,
    const thm_list extra_rules) {
  thm result = cm_spill_update_replace_raw_fact(
      old_phase, new_phase, next_pc, next_temp,
      next_break, next_continue, extra_rules);
  return conv_rule(rewrite_conv(THM_LIST(
      cm_spill_update_coordinate_fact(old_phase))), result);
}


PROOF static thm cm_spill_update_replace_store_fact(
    const term old_phase, const term new_phase,
    const term next_pc) {
  thm old_not_call = eqf_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(cm_phase_is_call_def)),
      mk_comb(`cm_phase_is_call`, old_phase)));
  thm new_not_call = eqf_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(cm_phase_is_call_def)),
      mk_comb(`cm_phase_is_call`, new_phase)));
  term phase_proposition = mk_comb(mk_comb(mk_comb(mk_comb(
      `cm_phase_spill_consistent`, `(owner:int) + 1i`),
      `owner:int`), new_phase),
      `cm_spill_put (owner:int) (v:cm_value)
        (spills:(cm_spill)list)`);
  thm phase_view = apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        cm_phase_spill_consistent_def, cm_spill_holds_put_same)),
      phase_proposition);
  struct dest_eq_results phase_sides = dest_eq(concl(phase_view));
  thm phase_consistent = eq_mp_rule(sym_rule(phase_view),
      int_arith_rule(phase_sides.tm2));
  thm pending = mp_rule(mp_rule(mp_rule(specl_rule(TERM_LIST(
      old_phase, new_phase,
      `pc:int`, `temp:int`, `breakpc:int`, `continuepc:int`,
      `owner:int`, `owner_break:int`, `owner_continue:int`,
      `cursor_rest:(cm_acursor)list`, `spills:(cm_spill)list`,
      `saved:(cm_spill_frame)list`,
      `calls:(cm_call_sim_frame)list`, `v:cm_value`,
      next_pc, `breakpc:int`, `continuepc:int`),
      cm_annotation_spill_replace_store),
      cm_spill_update_cursor_old_fact(old_phase)), old_not_call),
      new_not_call);
  thm result = mp_rule(pending, phase_consistent);
  return conv_rule(rewrite_conv(THM_LIST(
      cm_spill_update_coordinate_fact(old_phase))), result);
}

PROOF static thm cm_spill_update_arg_store_fact(
    const term phase, const term next_pc) {
  thm coordinate = cm_spill_update_coordinate_fact(phase);
  thm result = mp_rule(mp_rule(mp_rule(specl_rule(TERM_LIST(
      `a0:int`, `a1:(cm_expr)list`, `a2:(cm_value)list`,
      `a3:cm_type`, `a4:(cm_expr)list`, `a5:int`, `a6:int`, `a7:int`,
      `pc:int`, `temp:int`, `breakpc:int`, `continuepc:int`,
      `owner:int`, `owner_break:int`, `owner_continue:int`,
      `cursor_rest:(cm_acursor)list`, `spills:(cm_spill)list`,
      `saved:(cm_spill_frame)list`,
      `calls:(cm_call_sim_frame)list`, `v:cm_value`, next_pc),
      cm_annotation_spill_arg_store),
      cm_spill_update_cursor_old_fact(phase)), coordinate),
      assume_rule(`~((a1:(cm_expr)list) == [])`));
  return conv_rule(rewrite_conv(THM_LIST(coordinate)), result);
}

PROOF static thm cm_spill_update_arg_enter_fact(
    const term phase, const term return_pc) {
  return mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `a0:int`, `st:cm_src_state`,
      `a3:cm_type`, return_pc,
      `a1:(cm_expr)list`, `a2:(cm_value)list`,
      `a4:(cm_expr)list`, `a5:int`, `a6:int`, `a7:int`,
      `pc:int`, `temp:int`, `breakpc:int`, `continuepc:int`,
      `owner:int`, `owner_break:int`, `owner_continue:int`,
      `cursor_rest:(cm_acursor)list`, `spills:(cm_spill)list`,
      `saved:(cm_spill_frame)list`,
      `calls:(cm_call_sim_frame)list`, `v:cm_value`),
      cm_annotation_spill_arg_enter_call),
      cm_spill_update_cursor_old_fact(phase));
}




PROOF static thm cm_prove_update_v_spill_consistent(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (v:cm_value) (st:cm_src_state)
         (phase:cm_aphase)
         (pc:int) (temp:int) (breakpc:int) (continuepc:int)
         (owner:int) (owner_break:int) (owner_continue:int)
         (cursor_rest:(cm_acursor)list) (spills:(cm_spill)list)
         (saved:(cm_spill_frame)list)
         (calls:(cm_call_sim_frame)list).
         cm_annotation_spill_consistent
           (CMAnnotation pc temp breakpc continuepc
             (CMACursor phase owner owner_break owner_continue ::
               cursor_rest)
             spills saved calls) ==>
         temp == cm_phase_child_temp phase owner ==>
         cm_v_phase_ready p v st
           (CMAnnotation pc temp breakpc continuepc
             (CMACursor phase owner owner_break owner_continue ::
               cursor_rest)
             spills saved calls)
           phase ==>
         cm_annotation_spill_consistent
           (cm_update_annotation
             (cm_update_v p fid v st
               (CMAnnotation pc temp breakpc continuepc
                 (CMACursor phase owner owner_break owner_continue ::
                   cursor_rest)
                 spills saved calls)
               phase))`);
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list cases = DISJ_CASES_TAC(
      introduced,
      ispec_rule(`phase:cm_aphase`,
        get_datatype_cases("cm_aphase")),
      "Hphase");
  for (size_t index = 0; index < vector_size(cases); ++index) {
    while (true) {
      labeled_term_list assumptions = goal_lasmps(cases[index]->g);
      int shape_index = labeled_term_list_index(assumptions, "Hphase");
      if (!is_exists(assumptions[shape_index].tm)) break;
      cases[index] = ASMP_EXISTS_TAC(cases[index], "Hphase", NULL);
    }
    labeled_term_list assumptions = goal_lasmps(cases[index]->g);
    thm shape = assume_rule(
        assumptions[labeled_term_list_index(
          assumptions, "Hphase")].tm);
    thm_list branch_rules = THM_LIST(
        shape, cm_update_annotation_def, cm_update_v_def,
        cm_v_phase_ready_def, cm_phase_child_temp_def,
        cm_ann_pc_def, cm_ann_temp_def, cm_ann_break_def,
        cm_ann_continue_def, cm_ann_cursors_def, cm_ann_spills_def,
        cm_ann_saved_def, cm_ann_calls_def,
        cm_cursor_temp_def, cm_cursor_break_def,
        cm_cursor_continue_def, cm_cursor_phase_def,
        get_theorem_by_name("HD"), get_theorem_by_name("TL"));
    term concrete_phase = empty_term;
    if (index == 0) {
      concrete_phase = `CAHaltP`;
      vector_add(&branch_rules, cm_spill_update_pop_fact(
          concrete_phase,
          `(pc:int) + ilength (cm_char_normalize_code CMCharTy)`));
    } else if (index == 1) {
      concrete_phase = `CALoadP (a:cm_type)`;
      vector_add(&branch_rules, cm_spill_update_pop_fact(
          concrete_phase,
          `(pc:int) + ilength (cm_load_code (a:cm_type))`));
    } else if (index == 2) {
      concrete_phase = `CAAssignLP (a0:cm_expr) (a1:cm_type)`;
      vector_add(&branch_rules, cm_spill_update_coordinate_fact(
          concrete_phase));
      vector_add(&branch_rules, cm_spill_update_replace_store_fact(
          concrete_phase, `CAAssignRP (v:cm_value) (a1:cm_type)`,
          `(pc:int) + ilength
            (cm_temp_store_code (p:cm_program) (fid:int) (temp:int))`));
    } else if (index == 3) {
      concrete_phase = `CAAssignRP (a0:cm_value) (a1:cm_type)`;
      vector_add(&branch_rules, cm_spill_update_pop_fact(
          concrete_phase,
          `(pc:int) + ilength
            (cm_assign_tail_code (p:cm_program) (fid:int)
              (a1:cm_type) (owner:int))`));
    } else if (index == 4) {
      concrete_phase =
          `CABinLP (a0:int) (a1:cm_expr) (a2:cm_expr) (a3:cm_type)`;
      vector_add(&branch_rules, cm_spill_update_coordinate_fact(
          concrete_phase));
      gnode_list zero_cases = BOOL_CASES_TAC(
          cases[index], `(a0:int) == 0i`, "Hop_zero");
      gnode_list zero_truth_cases = BOOL_CASES_TAC(
          zero_cases[0], `cm_truth (st:cm_src_state) (v:cm_value)`,
          "Hzero_truth");
      {
        thm_list short_rules = THM_LIST();
        for (size_t rule_index = 0;
             rule_index < vector_size(branch_rules); ++rule_index) {
          vector_add(&short_rules, branch_rules[rule_index]);
        }
        vector_add(&short_rules, cm_spill_update_pop_fact(
            concrete_phase,
            `(pc:int) +
              cm_rvalue_code_count (p:cm_program) (fid:int)
                (a2:cm_expr) + 5i`));
        cm_spill_update_close(zero_truth_cases[0], short_rules);
      }
      {
        thm_list logical_rules = THM_LIST();
        for (size_t rule_index = 0;
             rule_index < vector_size(branch_rules); ++rule_index) {
          vector_add(&logical_rules, branch_rules[rule_index]);
        }
        thm op_zero = assume_rule(`(a0:int) == 0i`);
        vector_add(&logical_rules, op_zero);
        vector_add(&logical_rules, cm_spill_update_replace_fact(
            concrete_phase,
            `CABinRP (a0:int) (a1:cm_expr) (a2:cm_expr)
              (v:cm_value) (a3:cm_type)`,
            `(pc:int) + 1i`, `owner:int`,
            `breakpc:int`, `continuepc:int`, THM_LIST(op_zero)));
        cm_spill_update_close(zero_truth_cases[1], logical_rules);
      }
      gnode_list one_cases = BOOL_CASES_TAC(
          zero_cases[1], `(a0:int) == 1i`, "Hop_one");
      gnode_list one_truth_cases = BOOL_CASES_TAC(
          one_cases[0], `cm_truth (st:cm_src_state) (v:cm_value)`,
          "Hone_truth");
      {
        thm_list logical_rules = THM_LIST();
        for (size_t rule_index = 0;
             rule_index < vector_size(branch_rules); ++rule_index) {
          vector_add(&logical_rules, branch_rules[rule_index]);
        }
        thm op_one = assume_rule(`(a0:int) == 1i`);
        vector_add(&logical_rules, op_one);
        vector_add(&logical_rules, cm_spill_update_replace_fact(
            concrete_phase,
            `CABinRP (a0:int) (a1:cm_expr) (a2:cm_expr)
              (v:cm_value) (a3:cm_type)`,
            `(pc:int) + 1i`, `owner:int`,
            `breakpc:int`, `continuepc:int`, THM_LIST(op_one)));
        cm_spill_update_close(one_truth_cases[0], logical_rules);
      }
      {
        thm_list short_rules = THM_LIST();
        for (size_t rule_index = 0;
             rule_index < vector_size(branch_rules); ++rule_index) {
          vector_add(&short_rules, branch_rules[rule_index]);
        }
        vector_add(&short_rules, cm_spill_update_pop_fact(
            concrete_phase,
            `(pc:int) +
              cm_rvalue_code_count (p:cm_program) (fid:int)
                (a2:cm_expr) + 5i`));
        cm_spill_update_close(one_truth_cases[1], short_rules);
      }
      {
        thm_list stored_rules = THM_LIST();
        for (size_t rule_index = 0;
             rule_index < vector_size(branch_rules); ++rule_index) {
          vector_add(&stored_rules, branch_rules[rule_index]);
        }
        vector_add(&stored_rules, cm_spill_update_replace_store_fact(
            concrete_phase,
            `CABinRP (a0:int) (a1:cm_expr) (a2:cm_expr)
              (v:cm_value) (a3:cm_type)`,
            `(pc:int) + ilength
              (cm_temp_store_code (p:cm_program) (fid:int)
                (temp:int))`));
        cm_spill_update_close(one_cases[1], stored_rules);
      }
      continue;
    } else if (index == 5) {
      concrete_phase =
          `CABinRP (a0:int) (a1:cm_expr) (a2:cm_expr)
            (a3:cm_value) (a4:cm_type)`;
      gnode_list zero_cases = BOOL_CASES_TAC(
          cases[index], `(a0:int) == 0i`, "Hop_zero");
      {
        thm_list zero_rules = THM_LIST();
        for (size_t rule_index = 0;
             rule_index < vector_size(branch_rules); ++rule_index) {
          vector_add(&zero_rules, branch_rules[rule_index]);
        }
        vector_add(&zero_rules, cm_spill_update_pop_fact(
            concrete_phase, `(pc:int) + 4i`));
        cm_spill_update_close(zero_cases[0], zero_rules);
      }
      gnode_list one_cases = BOOL_CASES_TAC(
          zero_cases[1], `(a0:int) == 1i`, "Hop_one");
      {
        thm_list one_rules = THM_LIST();
        for (size_t rule_index = 0;
             rule_index < vector_size(branch_rules); ++rule_index) {
          vector_add(&one_rules, branch_rules[rule_index]);
        }
        vector_add(&one_rules, cm_spill_update_pop_fact(
            concrete_phase, `(pc:int) + 4i`));
        cm_spill_update_close(one_cases[0], one_rules);
      }
      {
        thm_list finish_rules = THM_LIST();
        for (size_t rule_index = 0;
             rule_index < vector_size(branch_rules); ++rule_index) {
          vector_add(&finish_rules, branch_rules[rule_index]);
        }
        vector_add(&finish_rules, cm_spill_update_pop_fact(
            concrete_phase,
            `(pc:int) + ilength
              (cm_binary_finish_code (p:cm_program) (fid:int)
                (a0:int) (a1:cm_expr) (a2:cm_expr) (owner:int))`));
        cm_spill_update_close(one_cases[1], finish_rules);
      }
      continue;
    } else if (index == 6) {
      concrete_phase = `CAUnaryP (a:int)`;
      vector_add(&branch_rules, cm_spill_update_pop_fact(
          concrete_phase, `(pc:int) + 2i`));
    } else if (index == 7) {
      concrete_phase = `CAIndexLP (a0:cm_expr) (a1:cm_type)`;
      vector_add(&branch_rules, cm_spill_update_coordinate_fact(
          concrete_phase));
      vector_add(&branch_rules, cm_spill_update_replace_store_fact(
          concrete_phase, `CAIndexRP (v:cm_value) (a1:cm_type)`,
          `(pc:int) + ilength
            (cm_temp_store_code (p:cm_program) (fid:int) (temp:int))`));
    } else if (index == 8) {
      concrete_phase = `CAIndexRP (a0:cm_value) (a1:cm_type)`;
      vector_add(&branch_rules, cm_spill_update_pop_fact(
          concrete_phase,
          `(pc:int) + ilength
            (cm_index_tail_code (p:cm_program) (fid:int)
              (a1:cm_type) (owner:int))`));
    } else if (index == 9) {
      concrete_phase = `CAMemberP (a0:int) (a1:cm_type)`;
      vector_add(&branch_rules, cm_spill_update_pop_fact(
          concrete_phase,
          `(pc:int) + ilength
            (cm_member_tail_code (p:cm_program)
              (a1:cm_type) (a0:int))`));
    } else if (index == 10) {
      concrete_phase = `CAPutcP`;
      vector_add(&branch_rules, cm_spill_update_pop_fact(
          concrete_phase, `(pc:int) + 2i`));
    } else if (index == 11) {
      concrete_phase = `CAPutiP`;
      vector_add(&branch_rules, cm_spill_update_pop_fact(
          concrete_phase, `(pc:int) + 2i`));
    } else if (index == 12) {
      concrete_phase = `CAExitP`;
      vector_add(&branch_rules, cm_spill_update_pop_fact(
          concrete_phase,
          `(pc:int) + ilength (cm_char_normalize_code CMCharTy)`));
    } else if (index == 13) {
      concrete_phase = `CAExprStmtP`;
      vector_add(&branch_rules, cm_spill_update_pop_fact(
          concrete_phase, `(pc:int) + 1i`));
    } else if (index == 14) {
      concrete_phase = `CAInitP (a:int)`;
      vector_add(&branch_rules, cm_spill_update_pop_fact(
          concrete_phase,
          `(pc:int) + ilength
            (cm_init_tail_code (p:cm_program) (fid:int) (a:int))`));
    } else if (index == 15) {
      concrete_phase =
          `CABlockP (a0:int->int->cm_value) (a1:(cm_region)list)
            (a2:bool) (a3:int)`;
      vector_add(&branch_rules, cm_spill_update_pop_fact(
          concrete_phase, `pc:int`));
    } else if (index == 16) {
      concrete_phase = `CASeqP (a:cm_stmt)`;
      vector_add(&branch_rules, cm_spill_update_pop_fact(
          concrete_phase, `pc:int`));
    } else if (index == 17) {
      concrete_phase = `CAIfP (a0:cm_stmt) (a1:cm_stmt)`;
      gnode_list truth_cases = BOOL_CASES_TAC(
          cases[index], `cm_truth (st:cm_src_state) (v:cm_value)`,
          "Htruth");
      {
        thm_list true_rules = THM_LIST();
        for (size_t rule_index = 0;
             rule_index < vector_size(branch_rules); ++rule_index) {
          vector_add(&true_rules, branch_rules[rule_index]);
        }
        vector_add(&true_rules, cm_spill_update_replace_fact(
            concrete_phase,
            `CABlockP (cm_state_env (st:cm_src_state))
              (cm_state_regions st) T
              ((pc:int) + 2i +
                cm_stmt_code_count (p:cm_program) (fid:int)
                  (a0:cm_stmt) +
                cm_stmt_code_count p fid (a1:cm_stmt))`,
            `(pc:int) + 1i`, `owner:int`,
            `owner_break:int`, `owner_continue:int`, THM_LIST()));
        cm_spill_update_close(truth_cases[0], true_rules);
      }
      {
        thm_list false_rules = THM_LIST();
        for (size_t rule_index = 0;
             rule_index < vector_size(branch_rules); ++rule_index) {
          vector_add(&false_rules, branch_rules[rule_index]);
        }
        vector_add(&false_rules, cm_spill_update_replace_fact(
            concrete_phase,
            `CABlockP (cm_state_env (st:cm_src_state))
              (cm_state_regions st) F
              ((pc:int) + 2i +
                cm_stmt_code_count (p:cm_program) (fid:int)
                  (a0:cm_stmt) +
                cm_stmt_code_count p fid (a1:cm_stmt))`,
            `(pc:int) + 2i +
              cm_stmt_code_count (p:cm_program) (fid:int)
                (a0:cm_stmt)`,
            `owner:int`, `owner_break:int`, `owner_continue:int`,
            THM_LIST()));
        cm_spill_update_close(truth_cases[1], false_rules);
      }
      continue;
    } else if (index == 18) {
      concrete_phase =
          `CAWhileGuardP (a0:cm_expr) (a1:cm_stmt) (a2:int) (a3:int)`;
      gnode_list truth_cases = BOOL_CASES_TAC(
          cases[index], `cm_truth (st:cm_src_state) (v:cm_value)`,
          "Htruth");
      {
        thm_list true_rules = THM_LIST();
        for (size_t rule_index = 0;
             rule_index < vector_size(branch_rules); ++rule_index) {
          vector_add(&true_rules, branch_rules[rule_index]);
        }
        vector_add(&true_rules, cm_spill_update_replace_fact(
            concrete_phase,
            `CAWhileBodyP (a0:cm_expr) (a1:cm_stmt)
              (cm_state_env (st:cm_src_state)) (cm_state_regions st)
              (a2:int) (a3:int)`,
            `(pc:int) + 1i`, `owner:int`, `a3:int`, `a2:int`,
            THM_LIST()));
        cm_spill_update_close(truth_cases[0], true_rules);
      }
      {
        thm_list false_rules = THM_LIST();
        for (size_t rule_index = 0;
             rule_index < vector_size(branch_rules); ++rule_index) {
          vector_add(&false_rules, branch_rules[rule_index]);
        }
        vector_add(&false_rules, cm_spill_update_pop_fact(
            concrete_phase, `a3:int`));
        cm_spill_update_close(truth_cases[1], false_rules);
      }
      continue;
    } else if (index == 19) {
      concrete_phase =
          `CAWhileBodyP (a0:cm_expr) (a1:cm_stmt)
            (a2:int->int->cm_value) (a3:(cm_region)list)
            (a4:int) (a5:int)`;
      vector_add(&branch_rules, cm_spill_update_pop_fact(
          concrete_phase, `pc:int`));
    } else if (index == 20) {
      concrete_phase = `CAReturnP`;
      vector_add(&branch_rules, cm_spill_update_pop_fact(
          concrete_phase, `pc:int`));
    } else if (index == 21) {
      concrete_phase =
          `CAArgP (a0:int) (a1:(cm_expr)list)
            (a2:(cm_value)list) (a3:cm_type)
            (a4:(cm_expr)list) (a5:int) (a6:int) (a7:int)`;
      vector_add(&branch_rules, cm_spill_update_coordinate_fact(
          concrete_phase));
      gnode_list rest_cases = BOOL_CASES_TAC(
          cases[index], `(a1:(cm_expr)list) == []`, "Hrest");
      {
        term call_ok =
            `cm_call_ok (p:cm_program) (a0:int)
              (REVERSE ((v:cm_value) :: (a2:(cm_value)list)))
              (st:cm_src_state)`;
        gnode_list call_ok_cases = BOOL_CASES_TAC(
            rest_cases[0], call_ok, "Hcall_ok");
        gnode_list depth_cases = BOOL_CASES_TAC(
            call_ok_cases[0],
            `cm_call_depth
              (cm_cursor_frames (cursor_rest:(cm_acursor)list)) <
              65536i`,
            "Hdepth");
        {
          thm_list entered_rules = THM_LIST();
          for (size_t rule_index = 0;
               rule_index < vector_size(branch_rules); ++rule_index) {
            vector_add(&entered_rules, branch_rules[rule_index]);
          }
          vector_add(&entered_rules, cm_spill_update_arg_enter_fact(
              concrete_phase,
              `(pc:int) +
                ilength
                  (cm_temp_store_code (p:cm_program) (fid:int) (a6:int)) +
                ilength
                  (cm_emit_args_reload p fid (a5:int)
                    (a4:(cm_expr)list)) + 1i`));
          cm_spill_update_close(depth_cases[0], entered_rules);
        }
        {
          thm_list failed_rules = THM_LIST();
          for (size_t rule_index = 0;
               rule_index < vector_size(branch_rules); ++rule_index) {
            vector_add(&failed_rules, branch_rules[rule_index]);
          }
          vector_add(&failed_rules, cm_spill_update_pop_fact(
              concrete_phase, `pc:int`));
          cm_spill_update_close(depth_cases[1], failed_rules);
        }
        {
          thm_list failed_rules = THM_LIST();
          for (size_t rule_index = 0;
               rule_index < vector_size(branch_rules); ++rule_index) {
            vector_add(&failed_rules, branch_rules[rule_index]);
          }
          vector_add(&failed_rules, cm_spill_update_pop_fact(
              concrete_phase, `pc:int`));
          cm_spill_update_close(call_ok_cases[1], failed_rules);
        }
      }
      {
        thm_list stored_rules = THM_LIST();
        for (size_t rule_index = 0;
             rule_index < vector_size(branch_rules); ++rule_index) {
          vector_add(&stored_rules, branch_rules[rule_index]);
        }
        thm stored_result = cm_spill_update_arg_store_fact(
            concrete_phase,
            `(pc:int) + ilength
              (cm_temp_store_code (p:cm_program) (fid:int) (a6:int))`);
        vector_add(&stored_rules, stored_result);
        cm_spill_update_accept_result(
            rest_cases[1], stored_result, stored_rules);
      }
      continue;
    } else {
      concrete_phase =
          `CACallP (a0:int) (a1:int->int->cm_value) (a2:int)
            (a3:(cm_region)list) (a4:cm_type)`;
      thm impossible = conv_rule(reduce_rewrite_conv(THM_LIST(
          shape, cm_v_phase_ready_def)),
          assume_rule(
            `cm_v_phase_ready (p:cm_program) (v:cm_value)
              (st:cm_src_state)
              (CMAnnotation (pc:int) (temp:int) (breakpc:int)
                (continuepc:int)
                (CMACursor (phase:cm_aphase) (owner:int)
                  (owner_break:int) (owner_continue:int) ::
                  (cursor_rest:(cm_acursor)list))
                (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
                (calls:(cm_call_sim_frame)list))
              phase`));
      CONTR_TAC(cases[index], impossible);
      continue;
    }
    cm_spill_update_close(cases[index], branch_rules);
  }
  return gnode_prove(root);
}

PROOF static thm cm_prove_annotation_spill_leave_call_generic(void) {
  gnode root = gnode_new_with_ccl(
      `!(caller:int) (env:int->int->cm_value) (fp:int)
         (regions:(cm_region)list) (ret:cm_type)
         (pc:int) (temp:int) (breakpc:int) (continuepc:int)
         (owner:int) (owner_break:int) (owner_continue:int)
         (cursor_rest:(cm_acursor)list) (spills:(cm_spill)list)
         (saved:(cm_spill_frame)list)
         (calls:(cm_call_sim_frame)list) (return_pc:int).
         cm_annotation_spill_consistent
           (CMAnnotation pc temp breakpc continuepc
             (CMACursor (CACallP caller env fp regions ret)
               owner owner_break owner_continue :: cursor_rest)
             spills saved calls) ==>
         cm_annotation_spill_consistent
           (cm_ann_leave_call return_pc
             (CMAnnotation pc temp breakpc continuepc
               (CMACursor (CACallP caller env fp regions ret)
                 owner owner_break owner_continue :: cursor_rest)
               spills saved calls))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm old_consistent = assume_rule(
      `cm_annotation_spill_consistent
        (CMAnnotation (pc:int) (temp:int) (breakpc:int)
          (continuepc:int)
          (CMACursor
            (CACallP (caller:int) (env:int->int->cm_value) (fp:int)
              (regions:(cm_region)list) (ret:cm_type))
            (owner:int) (owner_break:int) (owner_continue:int) ::
            (cursor_rest:(cm_acursor)list))
          (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
          (calls:(cm_call_sim_frame)list))`);
  thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_annotation_spill_consistent_def,
      cm_ann_temp_def, cm_ann_cursors_def, cm_ann_spills_def,
      cm_ann_saved_def, cm_cursor_temp_def, cm_cursor_phase_def,
      cm_cursors_spill_consistent_def, cm_phase_spill_consistent_def,
      cm_phase_is_call_def,
      get_theorem_by_name("HD"), get_theorem_by_name("TL"),
      get_theorem_by_name("NOT_CONS_NIL"))), old_consistent);
  thm tail = conjunct2_rule(opened);
  term target = goal_ccl(leaf->g);
  thm target_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
      cm_annotation_spill_consistent_def, cm_ann_leave_call_def,
      cm_ann_temp_def, cm_ann_cursors_def, cm_ann_spills_def,
      cm_ann_saved_def, cm_cursor_temp_def, cm_cursor_break_def,
      cm_cursor_continue_def, cm_spill_frame_spills_def,
      get_theorem_by_name("HD"), get_theorem_by_name("TL"))), target);
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), tail));
  return gnode_prove(root);
}

PROOF static thm cm_annotation_spill_leave_call_generic =
    cm_prove_annotation_spill_leave_call_generic();

PROOF static thm cm_spill_update_leave_call_raw_fact(
    const term phase, const term return_pc) {
  thm result = mp_rule(specl_rule(TERM_LIST(
      `a0:int`, `a1:int->int->cm_value`, `a2:int`,
      `a3:(cm_region)list`, `a4:cm_type`,
      `pc:int`, `temp:int`, `breakpc:int`, `continuepc:int`,
      `owner:int`, `owner_break:int`, `owner_continue:int`,
      `cursor_rest:(cm_acursor)list`, `spills:(cm_spill)list`,
      `saved:(cm_spill_frame)list`,
      `calls:(cm_call_sim_frame)list`, return_pc),
      cm_annotation_spill_leave_call_generic),
      cm_spill_update_cursor_old_fact(phase));
  return result;
}
PROOF static thm cm_spill_update_leave_call_fact(
    const term phase, const term return_pc) {
  thm result =
      cm_spill_update_leave_call_raw_fact(phase, return_pc);
  return conv_rule(rewrite_conv(THM_LIST(
      cm_spill_update_coordinate_fact(phase))), result);
}


PROOF thm cm_update_v_spill_consistent =
    cm_prove_update_v_spill_consistent();

PROOF static thm cm_prove_update_c_spill_consistent(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (ctl:cm_control) (st:cm_src_state)
         (phase:cm_aphase)
         (pc:int) (temp:int) (breakpc:int) (continuepc:int)
         (owner:int) (owner_break:int) (owner_continue:int)
         (cursor_rest:(cm_acursor)list) (spills:(cm_spill)list)
         (saved:(cm_spill_frame)list)
         (calls:(cm_call_sim_frame)list).
         cm_annotation_spill_consistent
           (CMAnnotation pc temp breakpc continuepc
             (CMACursor phase owner owner_break owner_continue ::
               cursor_rest)
             spills saved calls) ==>
         cm_annotation_spill_consistent
           (cm_update_annotation
             (cm_update_c p fid ctl st
               (CMAnnotation pc temp breakpc continuepc
                 (CMACursor phase owner owner_break owner_continue ::
                   cursor_rest)
                 spills saved calls)
               phase))`);
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list cases = DISJ_CASES_TAC(
      introduced,
      ispec_rule(`phase:cm_aphase`,
        get_datatype_cases("cm_aphase")),
      "Hphase");
  for (size_t index = 0; index < vector_size(cases); ++index) {
    while (true) {
      labeled_term_list assumptions = goal_lasmps(cases[index]->g);
      int shape_index = labeled_term_list_index(assumptions, "Hphase");
      if (!is_exists(assumptions[shape_index].tm)) break;
      cases[index] = ASMP_EXISTS_TAC(cases[index], "Hphase", NULL);
    }
    labeled_term_list assumptions = goal_lasmps(cases[index]->g);
    thm shape = assume_rule(
        assumptions[labeled_term_list_index(
          assumptions, "Hphase")].tm);
    thm_list branch_rules = THM_LIST(
        shape, cm_update_annotation_def, cm_update_c_def,
        cm_phase_child_temp_def,
        cm_ann_pc_def, cm_ann_temp_def, cm_ann_break_def,
        cm_ann_continue_def, cm_ann_cursors_def, cm_ann_spills_def,
        cm_ann_saved_def, cm_ann_calls_def,
        cm_cursor_temp_def, cm_cursor_break_def,
        cm_cursor_continue_def, cm_cursor_phase_def,
        get_theorem_by_name("HD"), get_theorem_by_name("TL"));
    term concrete_phase = empty_term;
    if (index == 0) {
      concrete_phase = `CAHaltP`;
    } else if (index == 1) {
      concrete_phase = `CALoadP (a:cm_type)`;
    } else if (index == 2) {
      concrete_phase = `CAAssignLP (a0:cm_expr) (a1:cm_type)`;
    } else if (index == 3) {
      concrete_phase = `CAAssignRP (a0:cm_value) (a1:cm_type)`;
    } else if (index == 4) {
      concrete_phase =
          `CABinLP (a0:int) (a1:cm_expr) (a2:cm_expr) (a3:cm_type)`;
    } else if (index == 5) {
      concrete_phase =
          `CABinRP (a0:int) (a1:cm_expr) (a2:cm_expr)
            (a3:cm_value) (a4:cm_type)`;
    } else if (index == 6) {
      concrete_phase = `CAUnaryP (a:int)`;
    } else if (index == 7) {
      concrete_phase = `CAIndexLP (a0:cm_expr) (a1:cm_type)`;
    } else if (index == 8) {
      concrete_phase = `CAIndexRP (a0:cm_value) (a1:cm_type)`;
    } else if (index == 9) {
      concrete_phase = `CAMemberP (a0:int) (a1:cm_type)`;
    } else if (index == 10) {
      concrete_phase = `CAPutcP`;
    } else if (index == 11) {
      concrete_phase = `CAPutiP`;
    } else if (index == 12) {
      concrete_phase = `CAExitP`;
    } else if (index == 13) {
      concrete_phase = `CAExprStmtP`;
    } else if (index == 14) {
      concrete_phase = `CAInitP (a:int)`;
    }
    if (index <= 14) {
      vector_add(&branch_rules, cm_spill_update_pop_raw_fact(
          concrete_phase, `pc:int`));
      cm_spill_update_close(cases[index], branch_rules);
      continue;
    }
    if (index == 15) {
      concrete_phase =
          `CABlockP (a0:int->int->cm_value) (a1:(cm_region)list)
            (a2:bool) (a3:int)`;
      gnode_list normal_cases = BOOL_CASES_TAC(
          cases[index],
          `cm_control_kind (ctl:cm_control) == 0i`, "Hnormal");
      gnode_list jump_cases = BOOL_CASES_TAC(
          normal_cases[0], `a2:bool`, "Hjump");
      {
        thm_list jump_rules = THM_LIST();
        for (size_t rule_index = 0;
             rule_index < vector_size(branch_rules); ++rule_index) {
          vector_add(&jump_rules, branch_rules[rule_index]);
        }
        vector_add(&jump_rules, cm_spill_update_pop_raw_fact(
            concrete_phase, `a3:int`));
        cm_spill_update_close(jump_cases[0], jump_rules);
      }
      {
        thm_list plain_rules = THM_LIST();
        for (size_t rule_index = 0;
             rule_index < vector_size(branch_rules); ++rule_index) {
          vector_add(&plain_rules, branch_rules[rule_index]);
        }
        vector_add(&plain_rules, cm_spill_update_pop_raw_fact(
            concrete_phase, `pc:int`));
        cm_spill_update_close(jump_cases[1], plain_rules);
      }
      {
        thm_list plain_rules = THM_LIST();
        for (size_t rule_index = 0;
             rule_index < vector_size(branch_rules); ++rule_index) {
          vector_add(&plain_rules, branch_rules[rule_index]);
        }
        vector_add(&plain_rules, cm_spill_update_pop_raw_fact(
            concrete_phase, `pc:int`));
        cm_spill_update_close(normal_cases[1], plain_rules);
      }
      continue;
    }
    if (index == 16) {
      concrete_phase = `CASeqP (a:cm_stmt)`;
      vector_add(&branch_rules, cm_spill_update_pop_raw_fact(
          concrete_phase, `pc:int`));
    } else if (index == 17) {
      concrete_phase = `CAIfP (a0:cm_stmt) (a1:cm_stmt)`;
      vector_add(&branch_rules, cm_spill_update_pop_raw_fact(
          concrete_phase, `pc:int`));
    } else if (index == 18) {
      concrete_phase =
          `CAWhileGuardP (a0:cm_expr) (a1:cm_stmt) (a2:int) (a3:int)`;
      vector_add(&branch_rules, cm_spill_update_pop_raw_fact(
          concrete_phase, `pc:int`));
    } else if (index == 19) {
      concrete_phase =
          `CAWhileBodyP (a0:cm_expr) (a1:cm_stmt)
            (a2:int->int->cm_value) (a3:(cm_region)list)
            (a4:int) (a5:int)`;
      gnode_list zero_cases = BOOL_CASES_TAC(
          cases[index],
          `cm_control_kind (ctl:cm_control) == 0i`, "Hkind_zero");
      {
        thm_list replace_rules = THM_LIST();
        for (size_t rule_index = 0;
             rule_index < vector_size(branch_rules); ++rule_index) {
          vector_add(&replace_rules, branch_rules[rule_index]);
        }
        vector_add(&replace_rules, cm_spill_update_replace_raw_fact(
            concrete_phase,
            `CAWhileGuardP (a0:cm_expr) (a1:cm_stmt)
              (a4:int) (a5:int)`,
            `a4:int`, `owner:int`, `a5:int`, `a4:int`, THM_LIST()));
        cm_spill_update_close(zero_cases[0], replace_rules);
      }
      gnode_list two_cases = BOOL_CASES_TAC(
          zero_cases[1],
          `cm_control_kind (ctl:cm_control) == 2i`, "Hkind_two");
      {
        thm_list replace_rules = THM_LIST();
        for (size_t rule_index = 0;
             rule_index < vector_size(branch_rules); ++rule_index) {
          vector_add(&replace_rules, branch_rules[rule_index]);
        }
        vector_add(&replace_rules, cm_spill_update_replace_raw_fact(
            concrete_phase,
            `CAWhileGuardP (a0:cm_expr) (a1:cm_stmt)
              (a4:int) (a5:int)`,
            `a4:int`, `owner:int`, `a5:int`, `a4:int`, THM_LIST()));
        cm_spill_update_close(two_cases[0], replace_rules);
      }
      gnode_list one_cases = BOOL_CASES_TAC(
          two_cases[1],
          `cm_control_kind (ctl:cm_control) == 1i`, "Hkind_one");
      {
        thm_list break_rules = THM_LIST();
        for (size_t rule_index = 0;
             rule_index < vector_size(branch_rules); ++rule_index) {
          vector_add(&break_rules, branch_rules[rule_index]);
        }
        vector_add(&break_rules, cm_spill_update_pop_raw_fact(
            concrete_phase, `a5:int`));
        cm_spill_update_close(one_cases[0], break_rules);
      }
      {
        thm_list other_rules = THM_LIST();
        for (size_t rule_index = 0;
             rule_index < vector_size(branch_rules); ++rule_index) {
          vector_add(&other_rules, branch_rules[rule_index]);
        }
        vector_add(&other_rules, cm_spill_update_pop_raw_fact(
            concrete_phase, `pc:int`));
        cm_spill_update_close(one_cases[1], other_rules);
      }
      continue;
    } else if (index == 20) {
      concrete_phase = `CAReturnP`;
      vector_add(&branch_rules, cm_spill_update_pop_raw_fact(
          concrete_phase, `pc:int`));
    } else if (index == 21) {
      concrete_phase =
          `CAArgP (a0:int) (a1:(cm_expr)list)
            (a2:(cm_value)list) (a3:cm_type)
            (a4:(cm_expr)list) (a5:int) (a6:int) (a7:int)`;
      vector_add(&branch_rules, cm_spill_update_pop_raw_fact(
          concrete_phase, `pc:int`));
    } else {
      concrete_phase =
          `CACallP (a0:int) (a1:int->int->cm_value) (a2:int)
            (a3:(cm_region)list) (a4:cm_type)`;
      gnode_list return_cases = BOOL_CASES_TAC(
          cases[index],
          `cm_control_kind (ctl:cm_control) == 3i`, "Hreturn");
      {
        thm_list return_rules = THM_LIST();
        for (size_t rule_index = 0;
             rule_index < vector_size(branch_rules); ++rule_index) {
          vector_add(&return_rules, branch_rules[rule_index]);
        }
        vector_add(&return_rules, cm_spill_update_leave_call_raw_fact(
            concrete_phase,
            `cm_call_sim_return
              (HD (calls:(cm_call_sim_frame)list))`));
        cm_spill_update_close(return_cases[0], return_rules);
      }
      gnode_list normal_cases = BOOL_CASES_TAC(
          return_cases[1],
          `cm_control_kind (ctl:cm_control) == 0i`, "Hnormal");
      {
        thm_list normal_rules = THM_LIST();
        for (size_t rule_index = 0;
             rule_index < vector_size(branch_rules); ++rule_index) {
          vector_add(&normal_rules, branch_rules[rule_index]);
        }
        vector_add(&normal_rules, cm_spill_update_leave_call_raw_fact(
            concrete_phase,
            `cm_call_sim_return
              (HD (calls:(cm_call_sim_frame)list))`));
        cm_spill_update_close(normal_cases[0], normal_rules);
      }
      {
        thm_list other_rules = THM_LIST();
        for (size_t rule_index = 0;
             rule_index < vector_size(branch_rules); ++rule_index) {
          vector_add(&other_rules, branch_rules[rule_index]);
        }
        vector_add(&other_rules, cm_spill_update_leave_call_raw_fact(
            concrete_phase, `pc:int`));
        cm_spill_update_close(normal_cases[1], other_rules);
      }
      continue;
    }
    cm_spill_update_close(cases[index], branch_rules);
  }
  return gnode_prove(root);
}

PROOF thm cm_update_c_spill_consistent =
    cm_prove_update_c_spill_consistent();
PROOF static term cm_spill_app_arg_from_right(
    term application, size_t offset) {
  for (size_t index = 0; index < offset; ++index) {
    application = dest_comb(application).tm1;
  }
  return dest_comb(application).tm2;
}

PROOF static term cm_spill_constructor_arg(
    term constructor, size_t arity, size_t index) {
  return cm_spill_app_arg_from_right(
      constructor, arity - index - 1);
}

PROOF static thm cm_prove_annotation_v_spill_consistent(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (v:cm_value)
         (st:cm_src_state) (ks:(cm_frame)list)
         (ann:cm_annotation).
         cm_annotation_spill_consistent ann ==>
         cm_v_layout_ready p v st ann ==>
         cm_annotation_spill_consistent
           (cm_update_annotation
             (cm_annotation_step
               (CMVTask p fid v st ks) ann))`);
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list ann_cases = DISJ_CASES_TAC(
      introduced,
      ispec_rule(`ann:cm_annotation`,
        get_datatype_cases("cm_annotation")),
      "Hann");
  gnode branch = ann_cases[0];
  while (true) {
    labeled_term_list assumptions = goal_lasmps(branch->g);
    int shape_index = labeled_term_list_index(assumptions, "Hann");
    if (!is_exists(assumptions[shape_index].tm)) break;
    branch = ASMP_EXISTS_TAC(branch, "Hann", NULL);
  }
  thm ann_shape = assume_rule(
      goal_lasmps(branch->g)[labeled_term_list_index(
        goal_lasmps(branch->g), "Hann")].tm);
  term shaped_ann = rhs_of(ann_shape);
  term cursors = cm_spill_constructor_arg(shaped_ann, 8, 4);
  gnode_list cursor_cases = DISJ_CASES_TAC(
      branch,
      ispec_rule(cursors, get_theorem_by_name("list_CASES")),
      "Hcursors");
  {
    thm cursors_nil = assume_rule(
        goal_lasmps(cursor_cases[0]->g)[
          labeled_term_list_index(
            goal_lasmps(cursor_cases[0]->g), "Hcursors")].tm);
    thm old_consistent = conv_rule(rewrite_conv(THM_LIST(
        ann_shape, cursors_nil)), assume_rule(
          `cm_annotation_spill_consistent (ann:cm_annotation)`));
    term target = goal_ccl(cursor_cases[0]->g);
    thm target_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
        ann_shape, cursors_nil, cm_annotation_step_def,
        cm_update_annotation_def, cm_ann_cursors_def)),
        target);
    ACCEPT_TAC(cursor_cases[0],
        eq_mp_rule(sym_rule(target_view), old_consistent));
  }
  gnode cons = ASMP_EXISTS_TAC(
      cursor_cases[1], "Hcursors", NULL);
  cons = ASMP_EXISTS_TAC(cons, "Hcursors", NULL);
  thm cursors_cons = assume_rule(
      goal_lasmps(cons->g)[labeled_term_list_index(
        goal_lasmps(cons->g), "Hcursors")].tm);
  term cursor = cm_spill_app_arg_from_right(
      rhs_of(cursors_cons), 1);
  gnode_list cursor_shapes = DISJ_CASES_TAC(
      cons,
      ispec_rule(cursor, get_datatype_cases("cm_acursor")),
      "Hcursor");
  gnode cursor_branch = cursor_shapes[0];
  while (true) {
    labeled_term_list assumptions = goal_lasmps(cursor_branch->g);
    int shape_index = labeled_term_list_index(assumptions, "Hcursor");
    if (!is_exists(assumptions[shape_index].tm)) break;
    cursor_branch = ASMP_EXISTS_TAC(
        cursor_branch, "Hcursor", NULL);
  }
  thm cursor_shape = assume_rule(
      goal_lasmps(cursor_branch->g)[labeled_term_list_index(
        goal_lasmps(cursor_branch->g), "Hcursor")].tm);
  thm full_shape = conv_rule(rewrite_conv(THM_LIST(
      cursors_cons, cursor_shape)), ann_shape);
  shaped_ann = rhs_of(full_shape);
  term pc_value = cm_spill_constructor_arg(shaped_ann, 8, 0);
  term temp_value = cm_spill_constructor_arg(shaped_ann, 8, 1);
  term break_value = cm_spill_constructor_arg(shaped_ann, 8, 2);
  term continue_value = cm_spill_constructor_arg(shaped_ann, 8, 3);
  term spills_value = cm_spill_constructor_arg(shaped_ann, 8, 5);
  term saved_value = cm_spill_constructor_arg(shaped_ann, 8, 6);
  term calls_value = cm_spill_constructor_arg(shaped_ann, 8, 7);
  term shaped_cursor = rhs_of(cursor_shape);
  term phase_value = cm_spill_constructor_arg(shaped_cursor, 4, 0);
  term owner_value = cm_spill_constructor_arg(shaped_cursor, 4, 1);
  term owner_break_value =
      cm_spill_constructor_arg(shaped_cursor, 4, 2);
  term owner_continue_value =
      cm_spill_constructor_arg(shaped_cursor, 4, 3);
  term rest_value =
      cm_spill_app_arg_from_right(rhs_of(cursors_cons), 0);
  thm old_consistent = conv_rule(rewrite_conv(THM_LIST(
      full_shape)), assume_rule(
        `cm_annotation_spill_consistent (ann:cm_annotation)`));
  thm layout = conv_rule(reduce_rewrite_conv(THM_LIST(
      full_shape, cm_v_layout_ready_def, cm_v_temp_ready_def,
      cm_ann_temp_def, cm_ann_cursors_def,
      cm_cursor_temp_def, cm_cursor_phase_def,
      get_theorem_by_name("HD"),
      get_theorem_by_name("NOT_CONS_NIL"))), assume_rule(
        `cm_v_layout_ready (p:cm_program) (v:cm_value)
          (st:cm_src_state) (ann:cm_annotation)`));
  thm coordinate = conjunct1_rule(layout);
  thm ready = conjunct2_rule(layout);
  thm result = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `v:cm_value`, `st:cm_src_state`,
      phase_value, pc_value, temp_value, break_value, continue_value,
      owner_value, owner_break_value, owner_continue_value,
      rest_value, spills_value, saved_value, calls_value),
      cm_update_v_spill_consistent);
  result = mp_rule(mp_rule(mp_rule(
      result, old_consistent), coordinate), ready);
  term target = goal_ccl(cursor_branch->g);
  thm target_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
      full_shape, cm_annotation_step_def, cm_update_annotation_def,
      cm_ann_cursors_def, cm_cursor_phase_def,
      get_theorem_by_name("HD"),
      get_theorem_by_name("NOT_CONS_NIL"))), target);
  ACCEPT_TAC(cursor_branch,
      eq_mp_rule(sym_rule(target_view), result));
  return gnode_prove(root);
}

PROOF static thm cm_annotation_v_spill_consistent =
    cm_prove_annotation_v_spill_consistent();

PROOF static thm cm_prove_annotation_c_spill_consistent(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (ctl:cm_control)
         (st:cm_src_state) (ks:(cm_frame)list)
         (ann:cm_annotation).
         cm_annotation_spill_consistent ann ==>
         cm_annotation_spill_consistent
           (cm_update_annotation
             (cm_annotation_step
               (CMCTask p fid ctl st ks) ann))`);
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list exit_cases = BOOL_CASES_TAC(introduced,
      `cm_control_kind (ctl:cm_control) == 4i`, "Hspill_control_exit");
  CONV_TAC(exit_cases[0], reduce_rewrite_conv(THM_LIST(
      assume_rule(`cm_control_kind (ctl:cm_control) == 4i`),
      cm_annotation_step_def, cm_update_annotation_def,
      cm_ann_done_def, cm_annotation_spill_consistent_def,
      cm_cursors_spill_consistent_def, cm_ann_temp_def,
      cm_ann_cursors_def, cm_ann_spills_def, cm_ann_saved_def)));
  introduced = exit_cases[1];
  thm nonexit = assume_rule(
      `~(cm_control_kind (ctl:cm_control) == 4i)`);
  gnode_list ann_cases = DISJ_CASES_TAC(
      introduced,
      ispec_rule(`ann:cm_annotation`,
        get_datatype_cases("cm_annotation")),
      "Hann");
  gnode branch = ann_cases[0];
  while (true) {
    labeled_term_list assumptions = goal_lasmps(branch->g);
    int shape_index = labeled_term_list_index(assumptions, "Hann");
    if (!is_exists(assumptions[shape_index].tm)) break;
    branch = ASMP_EXISTS_TAC(branch, "Hann", NULL);
  }
  thm ann_shape = assume_rule(
      goal_lasmps(branch->g)[labeled_term_list_index(
        goal_lasmps(branch->g), "Hann")].tm);
  term shaped_ann = rhs_of(ann_shape);
  term cursors = cm_spill_constructor_arg(shaped_ann, 8, 4);
  gnode_list cursor_cases = DISJ_CASES_TAC(
      branch,
      ispec_rule(cursors, get_theorem_by_name("list_CASES")),
      "Hcursors");
  {
    thm cursors_nil = assume_rule(
        goal_lasmps(cursor_cases[0]->g)[
          labeled_term_list_index(
            goal_lasmps(cursor_cases[0]->g), "Hcursors")].tm);
    thm old_consistent = conv_rule(rewrite_conv(THM_LIST(
        ann_shape, cursors_nil)), assume_rule(
          `cm_annotation_spill_consistent (ann:cm_annotation)`));
    term target = goal_ccl(cursor_cases[0]->g);
    thm target_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
        nonexit, ann_shape, cursors_nil, cm_annotation_step_def,
        cm_update_annotation_def, cm_ann_cursors_def)),
        target);
    ACCEPT_TAC(cursor_cases[0],
        eq_mp_rule(sym_rule(target_view), old_consistent));
  }
  gnode cons = ASMP_EXISTS_TAC(
      cursor_cases[1], "Hcursors", NULL);
  cons = ASMP_EXISTS_TAC(cons, "Hcursors", NULL);
  thm cursors_cons = assume_rule(
      goal_lasmps(cons->g)[labeled_term_list_index(
        goal_lasmps(cons->g), "Hcursors")].tm);
  term cursor = cm_spill_app_arg_from_right(
      rhs_of(cursors_cons), 1);
  gnode_list cursor_shapes = DISJ_CASES_TAC(
      cons,
      ispec_rule(cursor, get_datatype_cases("cm_acursor")),
      "Hcursor");
  gnode cursor_branch = cursor_shapes[0];
  while (true) {
    labeled_term_list assumptions = goal_lasmps(cursor_branch->g);
    int shape_index = labeled_term_list_index(assumptions, "Hcursor");
    if (!is_exists(assumptions[shape_index].tm)) break;
    cursor_branch = ASMP_EXISTS_TAC(
        cursor_branch, "Hcursor", NULL);
  }
  thm cursor_shape = assume_rule(
      goal_lasmps(cursor_branch->g)[labeled_term_list_index(
        goal_lasmps(cursor_branch->g), "Hcursor")].tm);
  thm full_shape = conv_rule(rewrite_conv(THM_LIST(
      cursors_cons, cursor_shape)), ann_shape);
  shaped_ann = rhs_of(full_shape);
  term pc_value = cm_spill_constructor_arg(shaped_ann, 8, 0);
  term temp_value = cm_spill_constructor_arg(shaped_ann, 8, 1);
  term break_value = cm_spill_constructor_arg(shaped_ann, 8, 2);
  term continue_value = cm_spill_constructor_arg(shaped_ann, 8, 3);
  term spills_value = cm_spill_constructor_arg(shaped_ann, 8, 5);
  term saved_value = cm_spill_constructor_arg(shaped_ann, 8, 6);
  term calls_value = cm_spill_constructor_arg(shaped_ann, 8, 7);
  term shaped_cursor = rhs_of(cursor_shape);
  term phase_value = cm_spill_constructor_arg(shaped_cursor, 4, 0);
  term owner_value = cm_spill_constructor_arg(shaped_cursor, 4, 1);
  term owner_break_value =
      cm_spill_constructor_arg(shaped_cursor, 4, 2);
  term owner_continue_value =
      cm_spill_constructor_arg(shaped_cursor, 4, 3);
  term rest_value =
      cm_spill_app_arg_from_right(rhs_of(cursors_cons), 0);
  thm old_consistent = conv_rule(rewrite_conv(THM_LIST(
      full_shape)), assume_rule(
        `cm_annotation_spill_consistent (ann:cm_annotation)`));
  thm result = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `ctl:cm_control`, `st:cm_src_state`,
      phase_value, pc_value, temp_value, break_value, continue_value,
      owner_value, owner_break_value, owner_continue_value,
      rest_value, spills_value, saved_value, calls_value),
      cm_update_c_spill_consistent);
  result = mp_rule(result, old_consistent);
  term target = goal_ccl(cursor_branch->g);
  thm target_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
      nonexit, full_shape, cm_annotation_step_def, cm_update_annotation_def,
      cm_ann_cursors_def, cm_cursor_phase_def,
      get_theorem_by_name("HD"),
      get_theorem_by_name("NOT_CONS_NIL"))), target);
  ACCEPT_TAC(cursor_branch,
      eq_mp_rule(sym_rule(target_view), result));
  return gnode_prove(root);
}

PROOF static thm cm_annotation_c_spill_consistent =
    cm_prove_annotation_c_spill_consistent();

PROOF static thm cm_prove_annotation_start_spill_consistent(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (input:(int)list) (ann:cm_annotation).
         ann == cm_initial_annotation ==>
         cm_call_ok p (cm_program_main p) []
           (cm_initial_state p input) ==>
         cm_annotation_spill_consistent
           (cm_update_annotation
             (cm_annotation_step (CMStartTask p input) ann))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm ann_shape = assume_rule(
      `(ann:cm_annotation) == cm_initial_annotation`);
  thm call_ok = assume_rule(
      `cm_call_ok (p:cm_program) (cm_program_main p) []
        (cm_initial_state p (input:(int)list))`);
  thm depth = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_call_depth_def(), get_cm_is_call_frame_def(),
        get_theorem_by_name("ILENGTH_DEF"))),
      `cm_call_depth ([CMHaltK]:(cm_frame)list) < 65536i`));
  thm tail_consistent = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        cm_cursors_spill_consistent_def,
        cm_phase_spill_consistent_def, cm_phase_is_call_def,
        cm_cursor_temp_def, cm_cursor_phase_def)),
      `cm_cursors_spill_consistent 0i
        ([CMACursor CAHaltP 0i 0i 0i]:(cm_acursor)list)
        ([]:(cm_spill)list) ([]:(cm_spill_frame)list)`));
  thm result = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `--1i`, `cm_program_main (p:cm_program)`,
      `cm_initial_state p (input:(int)list)`, `CMIntTy`, `4i`,
      `0i`, `0i`, `0i`,
      `[CMACursor CAHaltP 0i 0i 0i]:(cm_acursor)list`,
      `[]:(cm_spill)list`, `[]:(cm_spill_frame)list`,
      `[]:(cm_call_sim_frame)list`),
      cm_annotation_spill_enter_call), tail_consistent);
  term target = goal_ccl(leaf->g);
  thm target_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
      ann_shape, call_ok, depth, cm_annotation_step_def,
      cm_update_annotation_def)), target);
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), result));
  return gnode_prove(root);
}

PROOF static thm cm_annotation_start_spill_consistent =
    cm_prove_annotation_start_spill_consistent();

PROOF static thm cm_prove_annotation_step_spill_consistent(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (task:cm_task) (ann:cm_annotation).
         cm_annotation_spill_consistent ann ==>
         cm_task_layout_ready p task ann ==>
         cm_annotation_spill_consistent
           (cm_update_annotation (cm_annotation_step task ann))`);
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list ann_cases = DISJ_CASES_TAC(
      introduced,
      ispec_rule(`ann:cm_annotation`,
        get_datatype_cases("cm_annotation")),
      "Hann");
  gnode ann_branch = ann_cases[0];
  while (true) {
    labeled_term_list assumptions = goal_lasmps(ann_branch->g);
    int shape_index = labeled_term_list_index(assumptions, "Hann");
    if (!is_exists(assumptions[shape_index].tm)) break;
    ann_branch = ASMP_EXISTS_TAC(ann_branch, "Hann", NULL);
  }
  thm ann_shape = assume_rule(
      goal_lasmps(ann_branch->g)[labeled_term_list_index(
        goal_lasmps(ann_branch->g), "Hann")].tm);
  term shaped_ann = rhs_of(ann_shape);
  term pc_value = cm_spill_constructor_arg(shaped_ann, 8, 0);
  term temp_value = cm_spill_constructor_arg(shaped_ann, 8, 1);
  term break_value = cm_spill_constructor_arg(shaped_ann, 8, 2);
  term continue_value = cm_spill_constructor_arg(shaped_ann, 8, 3);
  term cursors_value = cm_spill_constructor_arg(shaped_ann, 8, 4);
  term spills_value = cm_spill_constructor_arg(shaped_ann, 8, 5);
  term saved_value = cm_spill_constructor_arg(shaped_ann, 8, 6);
  term calls_value = cm_spill_constructor_arg(shaped_ann, 8, 7);
  thm old_consistent = conv_rule(rewrite_conv(THM_LIST(ann_shape)),
      assume_rule(
        `cm_annotation_spill_consistent (ann:cm_annotation)`));
  gnode_list task_cases = DISJ_CASES_TAC(
      ann_branch,
      ispec_rule(`task:cm_task`, get_datatype_cases("cm_task")),
      "Htask");
  for (size_t index = 0;
       index < vector_size(task_cases); ++index) {
    gnode branch = task_cases[index];
    while (true) {
      labeled_term_list assumptions = goal_lasmps(branch->g);
      int shape_index = labeled_term_list_index(
          assumptions, "Htask");
      if (!is_exists(assumptions[shape_index].tm)) break;
      branch = ASMP_EXISTS_TAC(branch, "Htask", NULL);
    }
    thm task_shape = assume_rule(
        goal_lasmps(branch->g)[labeled_term_list_index(
          goal_lasmps(branch->g), "Htask")].tm);
    term concrete_task = rhs_of(task_shape);
    thm opened_layout = conv_rule(
        reduce_rewrite_conv(THM_LIST(
          task_shape, ann_shape, cm_task_layout_ready_def)),
        assume_rule(
          `cm_task_layout_ready (p:cm_program)
            (task:cm_task) (ann:cm_annotation)`));
    thm_list target_rules = THM_LIST(task_shape, ann_shape);
    thm result = empty_theorem;
    if (index == 0) {
      term input_value =
          cm_spill_constructor_arg(concrete_task, 2, 1);
      thm program_eq = conjunct1_rule(opened_layout);
      thm annotation_eq =
          conjunct1_rule(conjunct2_rule(opened_layout));
      thm call_ok = conjunct2_rule(conjunct2_rule(opened_layout));
      result = specl_rule(TERM_LIST(
          `p:cm_program`, input_value, shaped_ann),
          cm_annotation_start_spill_consistent);
      result = mp_rule(mp_rule(result, annotation_eq), call_ok);
      vector_add(&target_rules, program_eq);
    } else if (index >= 1 && index <= 4) {
      term task_program =
          cm_spill_constructor_arg(concrete_task, 5, 0);
      term fid_value =
          cm_spill_constructor_arg(concrete_task, 5, 1);
      term payload_value =
          cm_spill_constructor_arg(concrete_task, 5, 2);
      term state_value =
          cm_spill_constructor_arg(concrete_task, 5, 3);
      if (index == 1) {
        result = specl_rule(TERM_LIST(
            task_program, fid_value, payload_value, state_value,
            pc_value, temp_value, break_value, continue_value,
            cursors_value, spills_value, saved_value, calls_value),
            cm_update_r_spill_consistent);
        result = mp_rule(result, old_consistent);
        vector_add(&target_rules, cm_annotation_step_def);
        vector_add(&target_rules, cm_update_annotation_def);
      } else if (index == 2) {
        result = specl_rule(TERM_LIST(
            task_program, fid_value, payload_value, state_value,
            pc_value, temp_value, break_value, continue_value,
            cursors_value, spills_value, saved_value, calls_value),
            cm_update_l_spill_consistent);
        result = mp_rule(result, old_consistent);
        vector_add(&target_rules, cm_annotation_step_def);
        vector_add(&target_rules, cm_update_annotation_def);
      } else if (index == 3) {
        result = specl_rule(TERM_LIST(
            task_program, fid_value, payload_value, state_value,
            pc_value, temp_value, break_value, continue_value,
            cursors_value, spills_value, saved_value, calls_value),
            cm_update_s_spill_consistent);
        result = mp_rule(result, old_consistent);
        vector_add(&target_rules, cm_annotation_step_def);
        vector_add(&target_rules, cm_update_annotation_def);
      } else {
        term stack_value =
            cm_spill_constructor_arg(concrete_task, 5, 4);
        thm program_eq = conjunct1_rule(opened_layout);
        thm value_ready = conjunct2_rule(opened_layout);
        result = specl_rule(TERM_LIST(
            `p:cm_program`, fid_value, payload_value,
            state_value, stack_value, shaped_ann),
            cm_annotation_v_spill_consistent);
        result = mp_rule(mp_rule(
            result, old_consistent), value_ready);
        vector_add(&target_rules, program_eq);
      }
    } else if (index == 5) {
      term task_program =
          cm_spill_constructor_arg(concrete_task, 5, 0);
      term fid_value =
          cm_spill_constructor_arg(concrete_task, 5, 1);
      term control_value =
          cm_spill_constructor_arg(concrete_task, 5, 2);
      term state_value =
          cm_spill_constructor_arg(concrete_task, 5, 3);
      term stack_value =
          cm_spill_constructor_arg(concrete_task, 5, 4);
      result = specl_rule(TERM_LIST(
          task_program, fid_value, control_value,
          state_value, stack_value, shaped_ann),
          cm_annotation_c_spill_consistent);
      result = mp_rule(result, old_consistent);
    } else {
      result = old_consistent;
      vector_add(&target_rules, cm_annotation_step_def);
      vector_add(&target_rules, cm_update_annotation_def);
    }
    term target = goal_ccl(branch->g);
    thm target_view = apply_conversion(
        reduce_rewrite_conv(target_rules), target);
    ACCEPT_TAC(branch,
        eq_mp_rule(sym_rule(target_view), result));
  }
  return gnode_prove(root);
}

PROOF thm cm_annotation_step_spill_consistent =
    cm_prove_annotation_step_spill_consistent();




PROOF static int cmc_preservation_spill_update_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_spill_update_axioms_before,
      "cmc_preservation_spill_update introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_spill_update_checks =
    cmc_preservation_spill_update_final_checks();
