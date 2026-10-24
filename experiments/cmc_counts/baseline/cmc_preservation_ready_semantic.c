#include "proof/proof.h"
#include "userlib/proof.h"
#include "cmc_preservation_ready_semantic.h"
#include "cmc_preservation_source.h"
#include "cmc_preservation_source_conditions.h"
#include "cmc_preservation_code_task.h"
#include "cmc_preservation_invariant_task.h"
#include "cmc_annotate_preservation.h"

#require "cmc_preservation_ready_coordinate.c"
#require "cmc_preservation_ready_context.c"
#require "cmc_preservation_source_conditions.c"

PROOF static size_t _cmc_preservation_ready_semantic_axioms_before =
    vector_size(get_all_axioms());
PROOF static thm cm_semantic_ann_pc_cond = ispecl_rule(
    TERM_LIST(`condition:bool`, `cm_ann_pc`,
      `yes_annotation:cm_annotation`,
      `no_annotation:cm_annotation`),
    get_theorem_by_name("COND_RAND"));
PROOF static thm cm_semantic_ann_temp_cond = ispecl_rule(
    TERM_LIST(`condition:bool`, `cm_ann_temp`,
      `yes_annotation:cm_annotation`,
      `no_annotation:cm_annotation`),
    get_theorem_by_name("COND_RAND"));
PROOF static thm cm_semantic_ann_break_cond = ispecl_rule(
    TERM_LIST(`condition:bool`, `cm_ann_break`,
      `yes_annotation:cm_annotation`,
      `no_annotation:cm_annotation`),
    get_theorem_by_name("COND_RAND"));
PROOF static thm cm_semantic_ann_continue_cond = ispecl_rule(
    TERM_LIST(`condition:bool`, `cm_ann_continue`,
      `yes_annotation:cm_annotation`,
      `no_annotation:cm_annotation`),
    get_theorem_by_name("COND_RAND"));
PROOF static thm cm_semantic_ann_spills_cond = ispecl_rule(
    TERM_LIST(`condition:bool`, `cm_ann_spills`,
      `yes_annotation:cm_annotation`,
      `no_annotation:cm_annotation`),
    get_theorem_by_name("COND_RAND"));
PROOF static thm cm_semantic_ann_saved_cond = ispecl_rule(
    TERM_LIST(`condition:bool`, `cm_ann_saved`,
      `yes_annotation:cm_annotation`,
      `no_annotation:cm_annotation`),
    get_theorem_by_name("COND_RAND"));
PROOF static thm cm_semantic_ann_calls_cond = ispecl_rule(
    TERM_LIST(`condition:bool`, `cm_ann_calls`,
      `yes_annotation:cm_annotation`,
      `no_annotation:cm_annotation`),
    get_theorem_by_name("COND_RAND"));


PROOF static term cm_sr_app_arg_from_right(
    term application, size_t offset) {
  for (size_t i = 0; i < offset; ++i) {
    application = dest_comb(application).tm1;
  }
  return dest_comb(application).tm2;
}

PROOF static term cm_sr_constructor_arg(
    term constructor, size_t arity, size_t index) {
  return cm_sr_app_arg_from_right(
      constructor, arity - index - 1);
}

PROOF static thm cm_prove_typed_body_start_safe(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int).
         cm_typed_program p ==>
         0i <= fid ==>
         fid < ilength (cm_program_functions p) ==>
         cm_stmt_start_safe p fid
           (cm_function_body
             (inth fid (cm_program_functions p)))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm typed = conv_rule(
      rewrite_conv(THM_LIST(get_cm_typed_program_def())),
      assume_rule(`cm_typed_program (p:cm_program)`));
  thm functions_wf = conjunct1_rule(conjunct2_rule(
      conjunct2_rule(conjunct2_rule(typed))));
  thm function_wf = match_mp_rule(match_mp_rule(
      spec_rule(`fid:int`, functions_wf),
      assume_rule(`0i <= (fid:int)`)),
      assume_rule(
        `(fid:int) < ilength
           (cm_program_functions (p:cm_program))`));
  thm opened_function = conv_rule(
      rewrite_conv(THM_LIST(get_cm_function_wf_def())),
      function_wf);
  thm statement_wf = conjunct1_rule(conjunct2_rule(
      conjunct2_rule(conjunct2_rule(opened_function))));
  term statement =
      `cm_function_body
         (inth (fid:int) (cm_program_functions (p:cm_program)))`;
  gnode_list cases = DISJ_CASES_TAC(leaf,
      ispec_rule(statement, get_cm_stmt_cases()), "Hbody");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode branch = cases[i];
    while (true) {
      labeled_term_list assumptions = goal_lasmps(branch->g);
      int index = labeled_term_list_index(assumptions, "Hbody");
      if (!is_exists(assumptions[index].tm)) break;
      branch = ASMP_EXISTS_TAC(branch, "Hbody", NULL);
    }
    thm shape = assume_rule(
        goal_lasmps(branch->g)[labeled_term_list_index(
          goal_lasmps(branch->g), "Hbody")].tm);
    thm shaped_wf = conv_rule(
        reduce_rewrite_conv(THM_LIST(
          shape, get_cm_stmt_wf_def())),
        statement_wf);
    gnode reduced = CONV_WITH_ASMP_TAC(
        branch, reduce_rewrite_conv, THM_LIST(
          shape, shaped_wf, get_cm_stmt_start_safe_def(),
          get_cm_local_slot_ok_def()));
    if (IS_NULL(reduced->solved)) {
      labeled_term_list assumptions = goal_lasmps(reduced->g);
      thm facts = shaped_wf;
      for (size_t j = 0; j < vector_size(assumptions); ++j) {
        facts = conj_rule(facts, assume_rule(assumptions[j].tm));
      }
      ACCEPT_TAC(reduced, mp_rule(
          taut_rule(mk_imp(concl(facts), goal_ccl(reduced->g))),
          facts));
    }
  }
  return gnode_prove(root);
}
PROOF static thm cm_typed_body_start_safe =
    cm_prove_typed_body_start_safe();

PROOF static thm cm_prove_typed_body_context_ready(void) {
  term statement =
      `cm_function_body
         (inth (fid:int) (cm_program_functions (p:cm_program)))`;
  term cursors =
      `CMACursor
         (CACallP (caller:int) (oldenv:int->int->cm_value)
           (oldfp:int) (oldregions:(cm_region)list) (ret:cm_type))
         (owner:int) (owner_break:int) (owner_continue:int) ::
       (rest:(cm_acursor)list)`;
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int).
         cm_typed_program p ==>
         0i <= fid ==>
         fid < ilength (cm_program_functions p) ==>
         !(caller:int) (oldenv:int->int->cm_value) (oldfp:int)
           (oldregions:(cm_region)list) (ret:cm_type)
           (owner:int) (owner_break:int) (owner_continue:int)
           (rest:(cm_acursor)list).
           cm_stmt_context_ready
             (cm_function_body
               (inth fid (cm_program_functions p)))
             (CMACursor
                (CACallP caller oldenv oldfp oldregions ret)
                owner owner_break owner_continue :: rest)`);
  gnode introduced = AUTO_INTROS_TAC(root);
  thm typed = conv_rule(
      rewrite_conv(THM_LIST(get_cm_typed_program_def())),
      assume_rule(`cm_typed_program (p:cm_program)`));
  thm functions_wf = conjunct1_rule(conjunct2_rule(
      conjunct2_rule(conjunct2_rule(typed))));
  thm function_wf = match_mp_rule(match_mp_rule(
      spec_rule(`fid:int`, functions_wf),
      assume_rule(`0i <= (fid:int)`)),
      assume_rule(`(fid:int) <
        ilength (cm_program_functions (p:cm_program))`));
  thm opened_function = conv_rule(
      rewrite_conv(THM_LIST(get_cm_function_wf_def())),
      function_wf);
  thm statement_wf = conjunct1_rule(conjunct2_rule(
      conjunct2_rule(conjunct2_rule(opened_function))));
  gnode_list cases = DISJ_CASES_TAC(introduced,
      ispec_rule(statement, get_cm_stmt_cases()), "Hcontext_body");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode branch = cases[i];
    while (is_exists(goal_lasmps(branch->g)[
        labeled_term_list_index(
          goal_lasmps(branch->g), "Hcontext_body")].tm)) {
      branch = ASMP_EXISTS_TAC(branch, "Hcontext_body", NULL);
    }
    thm shape = assume_rule(goal_lasmps(branch->g)[
        labeled_term_list_index(
          goal_lasmps(branch->g), "Hcontext_body")].tm);
    thm shaped_wf = conv_rule(reduce_rewrite_conv(THM_LIST(
        shape, get_cm_stmt_wf_def())), statement_wf);
    gnode reduced = CONV_WITH_ASMP_TAC(branch,
        reduce_rewrite_conv, THM_LIST(
          shape, shaped_wf, cm_stmt_context_ready_def,
          cm_cursors_call_ready_def, cm_phase_control_scope_def,
          cm_cursor_phase_def));
    if (IS_NULL(reduced->solved)) {
      if (is_false(concl(shaped_wf))) {
        CONTR_TAC(reduced, shaped_wf);
      } else {
        thm implication = taut_rule(
            mk_imp(concl(shaped_wf), goal_ccl(reduced->g)));
        ACCEPT_TAC(reduced, mp_rule(implication, shaped_wf));
      }
    }
  }
  (void)cursors;
  return gnode_prove(root);
}
PROOF static thm cm_typed_body_context_ready =
    cm_prove_typed_body_context_ready();
PROOF static thm cm_prove_stmt_wf_context_ready(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fn:cm_function_d) (stmt:cm_stmt)
          (cursors:(cm_acursor)list).
         cm_stmt_wf p fn (cm_cursors_loop_ready cursors) stmt ==>
         cm_cursors_call_ready cursors ==>
         cm_stmt_context_ready stmt cursors`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list cases = DISJ_CASES_TAC(
      leaf, ispec_rule(`stmt:cm_stmt`, get_cm_stmt_cases()),
      "Hstmt_context");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode branch = cases[i];
    while (is_exists(goal_lasmps(branch->g)[
        labeled_term_list_index(
          goal_lasmps(branch->g), "Hstmt_context")].tm)) {
      branch = ASMP_EXISTS_TAC(branch, "Hstmt_context", NULL);
    }
    thm shape = assume_rule(goal_lasmps(branch->g)[
        labeled_term_list_index(
          goal_lasmps(branch->g), "Hstmt_context")].tm);
    thm_list rules = THM_LIST(
        shape, get_cm_stmt_wf_def(), cm_stmt_context_ready_def);
    gnode reduced = CONV_TAC(branch, reduce_rewrite_conv(rules));
    if (IS_NULL(reduced->solved)) {
      labeled_term_list assumptions = goal_lasmps(reduced->g);
      for (size_t j = 0; j < vector_size(assumptions); ++j) {
        thm normalized = conv_rule(
            reduce_rewrite_conv(rules),
            assume_rule(assumptions[j].tm));
        if (alpha_compare(
              concl(normalized), goal_ccl(reduced->g)) == 0) {
          ACCEPT_TAC(reduced, normalized);
          break;
        }
      }
    }
  }
  return gnode_prove(root);
}
PROOF static thm cm_stmt_wf_context_ready =
    cm_prove_stmt_wf_context_ready();
PROOF static thm cm_prove_stmt_scope_context_ready(void) {
  gnode root = gnode_new_with_ccl(
      `!(stmt:cm_stmt) (cursors:(cm_acursor)list).
         cm_stmt_scope_ready
           (cm_cursors_loop_ready cursors)
           (cm_cursors_call_ready cursors)
           stmt ==>
         cm_stmt_context_ready stmt cursors`);
  gnode leaf = AUTO_INTROS_TAC(root);
  gnode_list cases = DISJ_CASES_TAC(
      leaf, ispec_rule(`stmt:cm_stmt`, get_cm_stmt_cases()),
      "Hstmt_scope_context");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode branch = cases[i];
    while (is_exists(goal_lasmps(branch->g)[
        labeled_term_list_index(
          goal_lasmps(branch->g), "Hstmt_scope_context")].tm)) {
      branch = ASMP_EXISTS_TAC(
          branch, "Hstmt_scope_context", NULL);
    }
    thm shape = assume_rule(goal_lasmps(branch->g)[
        labeled_term_list_index(
          goal_lasmps(branch->g), "Hstmt_scope_context")].tm);
    thm shaped_scope = conv_rule(
        reduce_rewrite_conv(THM_LIST(
          shape, cm_stmt_scope_ready_def)),
        assume_rule(
          `cm_stmt_scope_ready
             (cm_cursors_loop_ready
               (cursors:(cm_acursor)list))
             (cm_cursors_call_ready cursors)
             (stmt:cm_stmt)`));
    gnode reduced = CONV_TAC(
        branch, reduce_rewrite_conv(THM_LIST(
          shape, cm_stmt_context_ready_def)));
    if (IS_NULL(reduced->solved)) {
      thm normalized_scope = conv_rule(
          reduce_rewrite_conv(THM_LIST(
            shape, cm_stmt_scope_ready_def,
            cm_stmt_context_ready_def)),
          shaped_scope);
      ACCEPT_TAC(reduced, normalized_scope);
    }
  }
  return gnode_prove(root);
}
PROOF static thm cm_stmt_scope_context_ready =
    cm_prove_stmt_scope_context_ready();

PROOF static thm cm_scope_taut_from_assumptions(const gnode node) {
  labeled_term_list assumptions = goal_lasmps(node->g);
  thm_list facts = (thm_list)vector_create();
  term_list premises = (term_list)vector_create();
  thm target_view = apply_conversion(
      reduce_rewrite_conv(THM_LIST(cm_stmt_scope_ready_def)),
      goal_ccl(node->g));
  for (size_t i = 0; i < vector_size(assumptions); ++i) {
    thm raw = assume_rule(assumptions[i].tm);
    if (is_forall(concl(raw))) {
      thm true_case = specl_rule(TERM_LIST(
          `p:cm_program`, `fn:cm_function_d`, `T:bool`), raw);
      true_case = conv_rule(reduce_rewrite_conv(THM_LIST(
          get_cm_stmt_wf_def(), cm_stmt_scope_ready_def)), true_case);
      vector_add(&facts, true_case);
      vector_add(&premises, concl(true_case));
      raw = specl_rule(TERM_LIST(
          `p:cm_program`, `fn:cm_function_d`, `loop_ok:bool`), raw);
    }
    thm fact = conv_rule(reduce_rewrite_conv(THM_LIST(
        get_cm_stmt_wf_def(), cm_stmt_scope_ready_def)), raw);
    vector_add(&facts, fact);
    vector_add(&premises, concl(fact));
  }
  thm result = taut_rule(imp_chain(premises, rhs_of(target_view)));
  for (size_t i = 0; i < vector_size(facts); ++i) {
    result = mp_rule(result, facts[i]);
  }
  return eq_mp_rule(sym_rule(target_view), result);
}

PROOF static thm cm_prove_stmt_wf_scope_ready(void) {
  gnode root = gnode_new_with_ccl(
      `!(stmt:cm_stmt). !(p:cm_program) (fn:cm_function_d)
          (loop_ok:bool).
         cm_stmt_wf p fn loop_ok stmt ==>
         cm_stmt_scope_ready loop_ok T stmt`);
  gnode_list cases = INDUCT_TAC(root, `stmt:cm_stmt`);
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode constructor = AUTO_INTROS_TAC(cases[i]);
    gnode_list frontier = AUTO_ASMP_DESTRUCT_TAC(constructor);
    gnode leaf = AUTO_INTROS_TAC(frontier[0]);
    ACCEPT_TAC(leaf, cm_scope_taut_from_assumptions(leaf));
  }
  return gnode_prove(root);
}
PROOF static thm cm_stmt_wf_scope_ready =
    cm_prove_stmt_wf_scope_ready();



PROOF static thm cm_prove_typed_body_wf(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int).
         cm_typed_program p ==>
         0i <= fid ==>
         fid < ilength (cm_program_functions p) ==>
         cm_stmt_wf p (inth fid (cm_program_functions p)) F
           (cm_function_body
             (inth fid (cm_program_functions p)))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm typed = conv_rule(
      rewrite_conv(THM_LIST(get_cm_typed_program_def())),
      assume_rule(`cm_typed_program (p:cm_program)`));
  thm functions_wf = conjunct1_rule(conjunct2_rule(
      conjunct2_rule(conjunct2_rule(typed))));
  thm function_wf = match_mp_rule(match_mp_rule(
      spec_rule(`fid:int`, functions_wf),
      assume_rule(`0i <= (fid:int)`)),
      assume_rule(`(fid:int) <
        ilength (cm_program_functions (p:cm_program))`));
  thm opened_function = conv_rule(
      rewrite_conv(THM_LIST(get_cm_function_wf_def())),
      function_wf);
  thm statement_wf = conjunct1_rule(conjunct2_rule(
      conjunct2_rule(conjunct2_rule(opened_function))));
  ACCEPT_TAC(leaf, statement_wf);
  return gnode_prove(root);
}
PROOF static thm cm_typed_body_wf = cm_prove_typed_body_wf();
PROOF static thm cm_prove_typed_body_scope_ready(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int).
         cm_typed_program p ==>
         0i <= fid ==>
         fid < ilength (cm_program_functions p) ==>
         cm_stmt_scope_ready F T
           (cm_function_body
             (inth fid (cm_program_functions p)))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm body_wf = specl_rule(
      TERM_LIST(`p:cm_program`, `fid:int`), cm_typed_body_wf);
  body_wf = match_mp_rule(
      body_wf, assume_rule(`cm_typed_program (p:cm_program)`));
  body_wf = match_mp_rule(
      body_wf, assume_rule(`0i <= (fid:int)`));
  body_wf = match_mp_rule(body_wf, assume_rule(
      `(fid:int) < ilength (cm_program_functions (p:cm_program))`));
  thm scope_ready = specl_rule(TERM_LIST(
      `cm_function_body
        (inth (fid:int) (cm_program_functions (p:cm_program)))`,
      `p:cm_program`,
      `inth (fid:int) (cm_program_functions (p:cm_program))`,
      `F:bool`), cm_stmt_wf_scope_ready);
  ACCEPT_TAC(leaf, match_mp_rule(scope_ready, body_wf));
  return gnode_prove(root);
}
PROOF static thm cm_typed_body_scope_ready =
    cm_prove_typed_body_scope_ready();
PROOF static thm cm_prove_typed_call_body_wf(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (args:(cm_value)list)
          (st:cm_src_state).
         cm_typed_program p ==>
         cm_call_ok p fid args st ==>
         cm_stmt_wf p (inth fid (cm_program_functions p)) F
           (cm_function_body
             (inth fid (cm_program_functions p)))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm opened_call = conv_rule(
      rewrite_conv(THM_LIST(get_cm_call_ok_def())),
      assume_rule(
        `cm_call_ok (p:cm_program) (fid:int)
          (args:(cm_value)list) (st:cm_src_state)`));
  thm body_wf = specl_rule(
      TERM_LIST(`p:cm_program`, `fid:int`), cm_typed_body_wf);
  body_wf = match_mp_rule(
      body_wf, assume_rule(`cm_typed_program (p:cm_program)`));
  body_wf = match_mp_rule(body_wf, conjunct1_rule(opened_call));
  body_wf = match_mp_rule(
      body_wf, conjunct1_rule(conjunct2_rule(opened_call)));
  ACCEPT_TAC(leaf, body_wf);
  return gnode_prove(root);
}
PROOF static thm cm_typed_call_body_wf =
    cm_prove_typed_call_body_wf();

PROOF static thm cm_prove_typed_main_body_wf(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program).
         cm_typed_program p ==>
         cm_stmt_wf p
           (inth (cm_program_main p) (cm_program_functions p)) F
           (cm_function_body
             (inth (cm_program_main p)
               (cm_program_functions p)))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm typed_fact = assume_rule(`cm_typed_program (p:cm_program)`);
  thm typed = conv_rule(
      rewrite_conv(THM_LIST(get_cm_typed_program_def())), typed_fact);
  thm typed_main = conjunct2_rule(conjunct2_rule(
      conjunct2_rule(conjunct2_rule(typed))));
  thm body_wf = specl_rule(TERM_LIST(
      `p:cm_program`, `cm_program_main (p:cm_program)`),
      cm_typed_body_wf);
  body_wf = match_mp_rule(body_wf, typed_fact);
  body_wf = match_mp_rule(
      body_wf, conjunct1_rule(typed_main));
  body_wf = match_mp_rule(
      body_wf, conjunct1_rule(conjunct2_rule(typed_main)));
  ACCEPT_TAC(leaf, body_wf);
  return gnode_prove(root);
}
PROOF static thm cm_typed_main_body_wf =
    cm_prove_typed_main_body_wf();


PROOF static thm cm_prove_ltask_succeeds_lvalue(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (expr:cm_expr)
         (st:cm_src_state) (ks:(cm_frame)list).
         cm_task_succeeds (CMLTask p fid expr st ks) ==>
         cm_lvalue expr`);
  gnode leaf = AUTO_INTROS_TAC(root);
  term source_task =
      `CMLTask (p:cm_program) (fid:int) (expr:cm_expr)
         (st:cm_src_state) (ks:(cm_frame)list)`;
  thm source_succeeds = assume_rule(
      `cm_task_succeeds
         (CMLTask (p:cm_program) (fid:int) (expr:cm_expr)
           (st:cm_src_state) (ks:(cm_frame)list))`);
  thm source_not_done = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(get_cm_task_done_def())),
      mk_not(mk_comb(`cm_task_done`, source_task))));
  thm next_succeeds = match_mp_rule(
      match_mp_rule(cm_task_succeeds_step, source_not_done),
      source_succeeds);
  thm next_not_error = match_mp_rule(
      specl_rule(TERM_LIST(
        `1i:int`, mk_comb(`cm_step`, source_task)),
        cm_task_succeeds_not_error),
      next_succeeds);
  gnode_list cases = DISJ_CASES_TAC(leaf,
      ispec_rule(`expr:cm_expr`, get_cm_expr_cases()), "Hex");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode branch = cases[i];
    while (true) {
      labeled_term_list assumptions = goal_lasmps(branch->g);
      int index = labeled_term_list_index(assumptions, "Hex");
      if (!is_exists(assumptions[index].tm)) break;
      branch = ASMP_EXISTS_TAC(branch, "Hex", NULL);
    }
    thm shape = assume_rule(
        goal_lasmps(branch->g)[labeled_term_list_index(
          goal_lasmps(branch->g), "Hex")].tm);
    gnode_list branches = (gnode_list)vector_create();
    if (i == 5) {
      term concrete_expr = rhs_of(shape);
      term op = cm_sr_constructor_arg(concrete_expr, 3, 0);
      branches = BOOL_CASES_TAC(
          branch, `${op:int} == 2i`, "Hop");
    } else {
      vector_add(&branches, branch);
    }
    for (size_t j = 0; j < vector_size(branches); ++j) {
      labeled_term_list assumptions = goal_lasmps(branches[j]->g);
      thm_list rules = THM_LIST(
          shape, get_cm_step_def(), get_cm_lstart_def(),
          cm_error_task_def, get_cm_lvalue_def(),
          get_datatype_distinctness("cm_control"),
          get_datatype_injectivity("cm_control"));
      for (size_t k = 0; k < vector_size(assumptions); ++k) {
        vector_add(&rules, assume_rule(assumptions[k].tm));
      }
      thm normalized_not_error = conv_rule(
          reduce_rewrite_conv(rules), next_not_error);
      if (is_false(concl(normalized_not_error))) {
        CONTR_TAC(branches[j], normalized_not_error);
      } else {
        CONV_WITH_ASMP_TAC(
            branches[j], reduce_rewrite_conv, rules);
      }
    }
  }
  return gnode_prove(root);
}
PROOF static thm cm_ltask_succeeds_lvalue =
    cm_prove_ltask_succeeds_lvalue();
PROOF static thm cm_prove_rtask_succeeds_getc_ready(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (expr:cm_expr)
         (st:cm_src_state) (ks:(cm_frame)list).
         cm_task_succeeds (CMRTask p fid expr st ks) ==>
         !ty.
           expr == CMGetcE (ty:cm_type) ==>
           cm_state_input st == [] ||
           tower_byte_value (HD (cm_state_input st))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm shape = assume_rule(
      `(expr:cm_expr) == CMGetcE (ty:cm_type)`);
  thm shaped_succeeds = conv_rule(rewrite_conv(THM_LIST(shape)),
      assume_rule(
        `cm_task_succeeds
          (CMRTask (p:cm_program) (fid:int) (expr:cm_expr)
            (st:cm_src_state) (ks:(cm_frame)list))`));
  thm result = match_mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `ty:cm_type`,
      `st:cm_src_state`, `ks:(cm_frame)list`),
      cm_r_getc_succeeds_input), shaped_succeeds);
  ACCEPT_TAC(leaf, result);
  return gnode_prove(root);
}
PROOF static thm cm_rtask_succeeds_getc_ready =
    cm_prove_rtask_succeeds_getc_ready();

PROOF static thm cm_prove_rtask_succeeds_array_ready(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (expr:cm_expr)
         (st:cm_src_state) (ks:(cm_frame)list).
         cm_task_succeeds (CMRTask p fid expr st ks) ==>
         !scope slot ty.
           expr == CMVarE (scope:int) (slot:int) (ty:cm_type) ==>
           cm_binding_array p fid scope slot ==>
           cm_binding_address_ok p fid scope slot st`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm shape = assume_rule(
      `(expr:cm_expr) ==
       CMVarE (scope:int) (slot:int) (ty:cm_type)`);
  thm shaped_succeeds = conv_rule(rewrite_conv(THM_LIST(shape)),
      assume_rule(
        `cm_task_succeeds
          (CMRTask (p:cm_program) (fid:int) (expr:cm_expr)
            (st:cm_src_state) (ks:(cm_frame)list))`));
  thm result = match_mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `scope:int`, `slot:int`,
      `ty:cm_type`, `st:cm_src_state`, `ks:(cm_frame)list`),
      cm_r_array_succeeds_address), shaped_succeeds);
  result = match_mp_rule(result, assume_rule(
      `cm_binding_array (p:cm_program) (fid:int)
        (scope:int) (slot:int)`));
  ACCEPT_TAC(leaf, result);
  return gnode_prove(root);
}
PROOF static thm cm_rtask_succeeds_array_ready =
    cm_prove_rtask_succeeds_array_ready();

PROOF static thm cm_prove_ltask_succeeds_address_ready(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (expr:cm_expr)
         (st:cm_src_state) (ks:(cm_frame)list).
         cm_task_succeeds (CMLTask p fid expr st ks) ==>
         !scope slot ty.
           expr == CMVarE (scope:int) (slot:int) (ty:cm_type) ==>
           cm_binding_address_ok p fid scope slot st`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm shape = assume_rule(
      `(expr:cm_expr) ==
       CMVarE (scope:int) (slot:int) (ty:cm_type)`);
  thm shaped_succeeds = conv_rule(rewrite_conv(THM_LIST(shape)),
      assume_rule(
        `cm_task_succeeds
          (CMLTask (p:cm_program) (fid:int) (expr:cm_expr)
            (st:cm_src_state) (ks:(cm_frame)list))`));
  thm result = match_mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `scope:int`, `slot:int`,
      `ty:cm_type`, `st:cm_src_state`, `ks:(cm_frame)list`),
      cm_l_var_succeeds_address), shaped_succeeds);
  ACCEPT_TAC(leaf, result);
  return gnode_prove(root);
}
PROOF static thm cm_ltask_succeeds_address_ready =
    cm_prove_ltask_succeeds_address_ready();

PROOF static thm cm_prove_ltask_succeeds_layout_ready(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (expr:cm_expr)
         (st:cm_src_state) (ks:(cm_frame)list).
         cm_task_succeeds (CMLTask p fid expr st ks) ==>
         cm_l_layout_ready p fid expr st`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm succeeds = assume_rule(
      `cm_task_succeeds
        (CMLTask (p:cm_program) (fid:int) (expr:cm_expr)
          (st:cm_src_state) (ks:(cm_frame)list))`);
  thm lvalue = match_mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `expr:cm_expr`,
      `st:cm_src_state`, `ks:(cm_frame)list`),
      cm_ltask_succeeds_lvalue), succeeds);
  thm address_ready = match_mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `expr:cm_expr`,
      `st:cm_src_state`, `ks:(cm_frame)list`),
      cm_ltask_succeeds_address_ready), succeeds);
  gnode opened = CONV_TAC(
      leaf, rewrite_conv(THM_LIST(cm_l_layout_ready_def)));
  ACCEPT_TAC(opened, conj_rule(lvalue, address_ready));
  return gnode_prove(root);
}
PROOF static thm cm_ltask_succeeds_layout_ready =
    cm_prove_ltask_succeeds_layout_ready();


PROOF static thm cm_prove_r_source_ready_layout(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (expr:cm_expr) (st:cm_src_state)
         (ks:(cm_frame)list) (ann:cm_annotation).
         cm_task_succeeds (CMRTask p fid expr st ks) ==>
         (!callee ty.
            expr == CMCallE (callee:int) [] (ty:cm_type) ==>
            cm_call_ok p callee [] st &&
            cm_call_depth ks < 65536i) ==>
         cm_cursor_frames (cm_ann_cursors ann) == ks ==>
         cm_r_layout_ready p fid expr st ks ann`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm succeeds = assume_rule(
      `cm_task_succeeds
        (CMRTask (p:cm_program) (fid:int) (expr:cm_expr)
          (st:cm_src_state) (ks:(cm_frame)list))`);
  thm source_ready = assume_rule(
      `!callee ty.
         (expr:cm_expr) == CMCallE (callee:int) [] (ty:cm_type) ==>
         cm_call_ok (p:cm_program) callee [] (st:cm_src_state) &&
         cm_call_depth (ks:(cm_frame)list) < 65536i`);
  thm frames = assume_rule(
      `cm_cursor_frames (cm_ann_cursors (ann:cm_annotation)) ==
       (ks:(cm_frame)list)`);
  thm getc_ready = match_mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `expr:cm_expr`,
      `st:cm_src_state`, `ks:(cm_frame)list`),
      cm_rtask_succeeds_getc_ready), succeeds);
  thm array_ready = match_mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `expr:cm_expr`,
      `st:cm_src_state`, `ks:(cm_frame)list`),
      cm_rtask_succeeds_array_ready), succeeds);
  gnode opened = CONV_TAC(
      leaf, rewrite_conv(THM_LIST(cm_r_layout_ready_def, frames)));
  thm joined = conj_rule(source_ready,
      conj_rule(getc_ready, array_ready));
  ACCEPT_TAC(opened, mp_rule(
      taut_rule(mk_imp(concl(joined), goal_ccl(opened->g))),
      joined));
  return gnode_prove(root);
}
PROOF static thm cm_r_source_ready_layout =
    cm_prove_r_source_ready_layout();
PROOF static thm cm_prove_stask_succeeds_start_safe(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (stmt:cm_stmt)
         (st:cm_src_state) (ks:(cm_frame)list).
         cm_task_succeeds (CMSTask p fid stmt st ks) ==>
         cm_stmt_start_safe p fid stmt`);
  gnode leaf = AUTO_INTROS_TAC(root);
  term source_task =
      `CMSTask (p:cm_program) (fid:int) (stmt:cm_stmt)
         (st:cm_src_state) (ks:(cm_frame)list)`;
  thm source_succeeds = assume_rule(
      `cm_task_succeeds
         (CMSTask (p:cm_program) (fid:int) (stmt:cm_stmt)
           (st:cm_src_state) (ks:(cm_frame)list))`);
  thm source_not_done = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(get_cm_task_done_def())),
      mk_not(mk_comb(`cm_task_done`, source_task))));
  thm next_succeeds = match_mp_rule(
      match_mp_rule(cm_task_succeeds_step, source_not_done),
      source_succeeds);
  thm next_not_error = match_mp_rule(
      specl_rule(TERM_LIST(
        `1i:int`, mk_comb(`cm_step`, source_task)),
        cm_task_succeeds_not_error),
      next_succeeds);
  gnode_list cases = DISJ_CASES_TAC(leaf,
      ispec_rule(`stmt:cm_stmt`, get_cm_stmt_cases()), "Hstmt");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode branch = cases[i];
    while (true) {
      labeled_term_list assumptions = goal_lasmps(branch->g);
      int index = labeled_term_list_index(assumptions, "Hstmt");
      if (!is_exists(assumptions[index].tm)) break;
      branch = ASMP_EXISTS_TAC(branch, "Hstmt", NULL);
    }
    thm shape = assume_rule(
        goal_lasmps(branch->g)[labeled_term_list_index(
          goal_lasmps(branch->g), "Hstmt")].tm);
    gnode_list branches = (gnode_list)vector_create();
    if (i == 2 || i == 3) {
      term concrete_stmt = rhs_of(shape);
      term slot = cm_sr_constructor_arg(
          concrete_stmt, i == 2 ? 1 : 2, 0);
      branches = BOOL_CASES_TAC(
          branch,
          `cm_local_slot_ok (p:cm_program) (fid:int) ${slot:int}`,
          "Hslot");
    } else {
      vector_add(&branches, branch);
    }
    for (size_t j = 0; j < vector_size(branches); ++j) {
      labeled_term_list assumptions = goal_lasmps(branches[j]->g);
      thm_list rules = THM_LIST(
          shape, get_cm_step_def(), get_cm_sstart_def(),
          cm_error_task_def, get_cm_stmt_start_safe_def(),
          get_cm_local_slot_ok_def(),
          get_datatype_distinctness("cm_control"),
          get_datatype_injectivity("cm_control"));
      for (size_t k = 0; k < vector_size(assumptions); ++k) {
        vector_add(&rules, assume_rule(assumptions[k].tm));
      }
      thm normalized_not_error = conv_rule(
          reduce_rewrite_conv(rules), next_not_error);
      if (is_false(concl(normalized_not_error))) {
        CONTR_TAC(branches[j], normalized_not_error);
      } else {
        CONV_WITH_ASMP_TAC(
            branches[j], reduce_rewrite_conv, rules);
      }
    }
  }
  return gnode_prove(root);
}
PROOF static thm cm_stask_succeeds_start_safe =
    cm_prove_stask_succeeds_start_safe();




PROOF static thm_list cm_semantic_step_rules(void) {
  return THM_LIST(
      cm_error_task_def, get_cm_step_def(),
      get_cm_begin_call_def(), get_cm_rstart_def(),
      get_cm_lstart_def(), get_cm_sstart_def(),
      get_cm_vapply_def(), get_cm_capply_def(),
      get_cm_lvalue_def(), get_cm_stmt_start_safe_def(),
      get_cm_stmt_wf_def(),
      get_cm_local_slot_ok_def(),
      get_cm_control_kind_def(), get_cm_control_status_def(),
      get_cm_call_depth_def(), get_cm_is_call_frame_def(),
      cm_args_start_nonempty,
      get_cm_success_control_def(),
      get_cm_outcome_control_def(),
      get_theorem_by_name("HD"), get_theorem_by_name("TL"),
      get_theorem_by_name("NOT_CONS_NIL"),
      get_datatype_distinctness("cm_aphase"),
      get_datatype_injectivity("cm_aphase"),
      get_datatype_distinctness("cm_control"),
      get_datatype_injectivity("cm_control"));
}
PROOF static thm_list cm_semantic_annotation_rules(void) {
  return THM_LIST(
      cm_update_annotation_cond, cm_ann_cursors_cond,
      cm_semantic_ann_pc_cond, cm_semantic_ann_temp_cond,
      cm_semantic_ann_break_cond, cm_semantic_ann_continue_cond,
      cm_semantic_ann_spills_cond, cm_semantic_ann_saved_cond,
      cm_semantic_ann_calls_cond, get_theorem_by_name("COND_ID"),
      cm_annotation_step_def, cm_update_annotation_def,
      cm_update_r_def, cm_update_l_def, cm_update_s_def,
      cm_update_v_def, cm_update_c_def,
      cm_ann_plain_def, cm_ann_linear_def, cm_ann_done_def,
      cm_ann_push_def, cm_ann_replace_def, cm_ann_pop_def,
      cm_ann_enter_call_def,
      cm_ann_leave_call_def, cm_ann_spills_set_def,
      cm_ann_put_spill_def,
      cm_ann_pc_def, cm_ann_temp_def, cm_ann_break_def,
      cm_ann_continue_def, cm_ann_cursors_def, cm_ann_spills_def,
      cm_ann_saved_def, cm_ann_calls_def);
}


PROOF static void cm_semantic_add_unique_rule(
    thm_list *rules, const thm rule) {
  for (size_t i = 0; i < vector_size(*rules); ++i) {
    if (alpha_compare(concl((*rules)[i]), concl(rule)) == 0) {
      return;
    }
  }
  vector_add(rules, rule);
}

PROOF static void cm_semantic_add_fact_rules(
    thm_list *rules, const thm fact) {
  if (is_conj(concl(fact))) {
    cm_semantic_add_fact_rules(rules, conjunct1_rule(fact));
    cm_semantic_add_fact_rules(rules, conjunct2_rule(fact));
  } else {
    cm_semantic_add_unique_rule(rules, fact);
  }
}
PROOF static void cm_semantic_add_equality_rules(
    thm_list *rules, const thm fact) {
  if (is_conj(concl(fact))) {
    cm_semantic_add_equality_rules(rules, conjunct1_rule(fact));
    cm_semantic_add_equality_rules(rules, conjunct2_rule(fact));
  } else if (is_eq(concl(fact))) {
    cm_semantic_add_unique_rule(rules, fact);
  }
}
PROOF static void cm_semantic_add_variable_equalities(
    thm_list *rules, const thm fact) {
  if (is_conj(concl(fact))) {
    cm_semantic_add_variable_equalities(
        rules, conjunct1_rule(fact));
    cm_semantic_add_variable_equalities(
        rules, conjunct2_rule(fact));
  } else if (is_eq(concl(fact))) {
    struct dest_eq_results sides = dest_eq(concl(fact));
    if (is_var(sides.tm1) &&
        !var_free_in(sides.tm1, sides.tm2)) {
      cm_semantic_add_unique_rule(rules, fact);
    }
  }
}
PROOF static bool cm_semantic_has_conjunct(
    const thm fact, term wanted) {
  if (alpha_compare(concl(fact), wanted) == 0) return true;
  if (!is_conj(concl(fact))) return false;
  return cm_semantic_has_conjunct(conjunct1_rule(fact), wanted) ||
      cm_semantic_has_conjunct(conjunct2_rule(fact), wanted);
}



PROOF static bool cm_semantic_contains_const(
    term subject, const char *name) {
  if (is_const(subject)) {
    return strcmp(dest_const(subject).s, name) == 0;
  }
  if (is_comb(subject)) {
    struct dest_comb_results application = dest_comb(subject);
    return cm_semantic_contains_const(application.tm1, name) ||
        cm_semantic_contains_const(application.tm2, name);
  }
  return false;
}

PROOF static bool cm_semantic_has_head_const(
    term subject, const char *name) {
  while (is_comb(subject)) {
    subject = dest_comb(subject).tm1;
  }
  return is_const(subject) &&
      strcmp(dest_const(subject).s, name) == 0;
}

PROOF static bool cm_semantic_find_head_conjunct(
    const thm fact, const char *name, thm *found) {
  if (cm_semantic_has_head_const(concl(fact), name)) {
    *found = fact;
    return true;
  }
  if (!is_conj(concl(fact))) return false;
  if (cm_semantic_find_head_conjunct(
        conjunct1_rule(fact), name, found)) {
    return true;
  }
  return cm_semantic_find_head_conjunct(
      conjunct2_rule(fact), name, found);
}
PROOF static bool cm_semantic_find_stmt_wf_conjunct(
    const thm fact, term statement_term, thm *found) {
  if (cm_semantic_has_head_const(concl(fact), "cm_stmt_wf") &&
      alpha_compare(
        cm_sr_app_arg_from_right(concl(fact), 0),
        statement_term) == 0) {
    *found = fact;
    return true;
  }
  if (!is_conj(concl(fact))) return false;
  if (cm_semantic_find_stmt_wf_conjunct(
        conjunct1_rule(fact), statement_term, found)) {
    return true;
  }
  return cm_semantic_find_stmt_wf_conjunct(
      conjunct2_rule(fact), statement_term, found);
}
PROOF static bool cm_semantic_find_stmt_scope_conjunct(
    const thm fact, term statement_term, thm *found) {
  if (cm_semantic_has_head_const(
        concl(fact), "cm_stmt_scope_ready") &&
      alpha_compare(
        cm_sr_app_arg_from_right(concl(fact), 0),
        statement_term) == 0) {
    *found = fact;
    return true;
  }
  if (!is_conj(concl(fact))) return false;
  if (cm_semantic_find_stmt_scope_conjunct(
        conjunct1_rule(fact), statement_term, found)) {
    return true;
  }
  return cm_semantic_find_stmt_scope_conjunct(
      conjunct2_rule(fact), statement_term, found);
}



PROOF static thm cm_prove_semantic_cursors_context_cond(void) {
  gnode root = gnode_new_with_ccl(
      `!(condition:bool) (yes:(cm_acursor)list)
          (no:(cm_acursor)list).
         cm_cursors_context_ready
           (if condition then yes else no) <=>
         (if condition
          then cm_cursors_context_ready yes
          else cm_cursors_context_ready no)`);
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list cases = BOOL_CASES_TAC(
      introduced, `condition:bool`, "Hcontext_cond");
  CONV_WITH_ASMP_TAC(
      cases[0], reduce_rewrite_conv, THM_LIST());
  CONV_WITH_ASMP_TAC(
      cases[1], reduce_rewrite_conv, THM_LIST());
  return gnode_prove(root);
}
PROOF static thm cm_semantic_cursors_context_cond =
    cm_prove_semantic_cursors_context_cond();
PROOF static thm cm_prove_semantic_cursors_scope_cond(void) {
  gnode root = gnode_new_with_ccl(
      `!(condition:bool) (yes:(cm_acursor)list)
          (no:(cm_acursor)list).
         cm_cursors_scope_ready
           (if condition then yes else no) <=>
         (if condition
          then cm_cursors_scope_ready yes
          else cm_cursors_scope_ready no)`);
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list cases = BOOL_CASES_TAC(
      introduced, `condition:bool`, "Hscope_cond");
  CONV_WITH_ASMP_TAC(
      cases[0], reduce_rewrite_conv, THM_LIST());
  CONV_WITH_ASMP_TAC(
      cases[1], reduce_rewrite_conv, THM_LIST());
  return gnode_prove(root);
}
PROOF static thm cm_semantic_cursors_scope_cond =
    cm_prove_semantic_cursors_scope_cond();



PROOF static bool cm_semantic_contains_coordinate(term subject) {
  return cm_semantic_contains_const(
      subject, "cm_cursors_coordinate");
}







PROOF static thm cm_semantic_substitute_occurrences(
    term subject, thm equality) {
  struct dest_eq_results sides = dest_eq(concl(equality));
  if (alpha_compare(subject, sides.tm1) == 0) {
    return equality;
  }
  if (is_comb(subject)) {
    struct dest_comb_results application = dest_comb(subject);
    return mk_comb_rule(
        cm_semantic_substitute_occurrences(
          application.tm1, equality),
        cm_semantic_substitute_occurrences(
          application.tm2, equality));
  }
  return refl_rule(subject);
}
PROOF static thm cm_semantic_apply_substitutions(
    thm fact, const thm_list equalities) {
  for (size_t i = 0; i < vector_size(equalities); ++i) {
    fact = eq_mp_rule(
        cm_semantic_substitute_occurrences(
          concl(fact), equalities[i]),
        fact);
  }
  return fact;
}
PROOF static void cm_semantic_prepare_targets(
    gnode node, const thm_list rules, gnode_list *targets) {
  node = CONV_WITH_ASMP_TAC(
      node, reduce_rewrite_conv, rules);
  if (!IS_NULL(node->solved)) return;
  if (is_conj(goal_ccl(node->g))) {
    gnode_list parts = CONJ_TAC(node);
    cm_semantic_prepare_targets(parts[0], rules, targets);
    cm_semantic_prepare_targets(parts[1], rules, targets);
    return;
  }
  if (is_forall(goal_ccl(node->g)) ||
      is_imp(goal_ccl(node->g))) {
    cm_semantic_prepare_targets(
        AUTO_INTROS_TAC(node), rules, targets);
    return;
  }
  vector_add(targets, node);
}


PROOF static void cm_semantic_close(
    gnode branch, const thm_list extra_rules) {
  for (size_t i = 0; i < vector_size(extra_rules); ++i) {
    if (is_false(concl(extra_rules[i]))) {
      CONTR_TAC(branch, extra_rules[i]);
      return;
    }
  }
  thm_list rules = (thm_list)vector_create();
  for (size_t i = 0; i < vector_size(extra_rules); ++i) {
    if (cm_semantic_has_head_const(
          concl(extra_rules[i]), "cm_stmt_scope_ready")) {
      continue;
    }
    cm_semantic_add_fact_rules(&rules, extra_rules[i]);
  }
  thm_list definitions = THM_LIST(
      cm_task_layout_ready_def, cm_r_layout_ready_def,
      cm_v_layout_ready_def, cm_v_temp_ready_def,
      cm_v_phase_ready_def, cm_c_layout_ready_def,
      cm_c_phase_ready_def, cm_c_regular_ready_def,
      cm_c_code_ready_def, cm_task_context_ready_def,
      cm_cursors_context_ready_def, cm_statement_cursors_ready_def,
      cm_cursors_scope_ready_def, cm_phase_scope_ready_def,
      cm_stmt_scope_ready_def,
      cm_stmt_context_ready_def, cm_control_context_ready_def,
      get_cm_stmt_wf_def(),
      cm_cursors_loop_ready_def, cm_cursors_call_ready_def,
      cm_phase_accepts_statement_def,
      cm_phase_requires_statement_parent_def,
      cm_phase_control_scope_def, get_cm_step_def(),
      cm_error_task_def, get_cm_control_kind_def(),
      cm_phase_child_temp_def, cm_phase_control_regular_def,
      get_cm_call_depth_def(), get_cm_is_call_frame_def(),
      get_theorem_by_name("ILENGTH_DEF"),
      get_cm_call_ok_def(), cm_typed_body_context_ready,
      cm_typed_call_body_wf, cm_typed_main_body_wf,
      cm_semantic_cursors_context_cond,
      cm_semantic_cursors_scope_cond,
      cm_phase_code_ready_at_def, cm_phase_next_fid_def,
      cm_cursors_coordinate_def,
      cm_cursor_frames_def, cm_cursor_phase_def, cm_cursor_temp_def,
      get_theorem_by_name("HD"), get_theorem_by_name("TL"),
      get_theorem_by_name("NOT_CONS_NIL"),
      get_datatype_distinctness("cm_aphase"),
      get_datatype_injectivity("cm_aphase"),
      get_datatype_distinctness("cm_control"),
      get_datatype_injectivity("cm_control"),
      get_datatype_distinctness("cm_task"),
      get_datatype_injectivity("cm_task"));
  for (size_t i = 0; i < vector_size(definitions); ++i) {
    vector_add(&rules, definitions[i]);
  }
  thm_list annotation_definitions =
      cm_semantic_annotation_rules();
  for (size_t i = 0;
       i < vector_size(annotation_definitions); ++i) {
    vector_add(&rules, annotation_definitions[i]);
  }
  labeled_term_list assumptions = goal_lasmps(branch->g);
  for (size_t i = 0; i < vector_size(assumptions); ++i) {
    vector_add(&rules, assume_rule(assumptions[i].tm));
  }

  gnode_list targets = (gnode_list)vector_create();
  cm_semantic_prepare_targets(branch, rules, &targets);
  gnode_list leaves = (gnode_list)vector_create();
  for (size_t i = 0; i < vector_size(targets); ++i) {
    vector_add(&leaves, targets[i]);
  }
  for (size_t i = 0; i < vector_size(leaves); ++i) {
    gnode leaf = CONV_WITH_ASMP_TAC(
        leaves[i], reduce_rewrite_conv, rules);
    if (!IS_NULL(leaf->solved)) continue;
    labeled_term_list leaf_assumptions = goal_lasmps(leaf->g);
    if (cm_semantic_has_head_const(
          goal_ccl(leaf->g), "cm_stmt_wf")) {
      thm typed_local = empty_theorem;
      thm call_local = empty_theorem;
      bool has_typed = false;
      bool has_call = false;
      for (size_t j = 0;
           j < vector_size(leaf_assumptions); ++j) {
        term assumption_term = leaf_assumptions[j].tm;
        if (!has_typed && cm_semantic_has_head_const(
              assumption_term, "cm_typed_program")) {
          typed_local = assume_rule(assumption_term);
          has_typed = true;
        }
        thm assumption = assume_rule(assumption_term);
        if (!has_call &&
            cm_semantic_find_head_conjunct(
              assumption, "cm_call_ok", &call_local)) {
          has_call = true;
        }
      }
      if (has_typed) {
        term typed_program =
            cm_sr_app_arg_from_right(concl(typed_local), 0);
        if (has_call) {
          term call_program =
              cm_sr_app_arg_from_right(concl(call_local), 3);
          if (alpha_compare(typed_program, call_program) == 0) {
            thm body_wf = specl_rule(TERM_LIST(
                call_program,
                cm_sr_app_arg_from_right(concl(call_local), 2),
                cm_sr_app_arg_from_right(concl(call_local), 1),
                cm_sr_app_arg_from_right(concl(call_local), 0)),
                cm_typed_call_body_wf);
            body_wf = match_mp_rule(body_wf, typed_local);
            body_wf = match_mp_rule(body_wf, call_local);
            if (alpha_compare(
                  concl(body_wf), goal_ccl(leaf->g)) == 0) {
              ACCEPT_TAC(leaf, body_wf);
            }
          }
        }
        if (IS_NULL(leaf->solved)) {
          thm main_wf = match_mp_rule(
              spec_rule(typed_program, cm_typed_main_body_wf),
              typed_local);
          if (alpha_compare(
                concl(main_wf), goal_ccl(leaf->g)) == 0) {
            ACCEPT_TAC(leaf, main_wf);
          }
        }
      }
      if (!IS_NULL(leaf->solved)) continue;
    }
    thm_list substitution_rules = (thm_list)vector_create();
    thm_list leaf_substitutions = (thm_list)vector_create();
    thm_list leaf_variable_substitutions =
        (thm_list)vector_create();
    thm_list transport_rules = (thm_list)vector_create();
    for (size_t j = 0; j < vector_size(extra_rules); ++j) {
      cm_semantic_add_equality_rules(
          &substitution_rules, extra_rules[j]);
      cm_semantic_add_variable_equalities(
          &transport_rules, extra_rules[j]);
    }
    vector_add(&substitution_rules, cm_cursor_break_def);
    vector_add(&substitution_rules, cm_cursor_continue_def);
    vector_add(&transport_rules, cm_cursor_break_def);
    vector_add(&transport_rules, cm_cursor_continue_def);
    for (size_t j = 0; j < vector_size(leaf_assumptions); ++j) {
      thm assumption = assume_rule(leaf_assumptions[j].tm);
      cm_semantic_add_equality_rules(
          &substitution_rules, assumption);
      cm_semantic_add_equality_rules(
          &leaf_substitutions, assumption);
      cm_semantic_add_variable_equalities(
          &leaf_variable_substitutions, assumption);
      cm_semantic_add_variable_equalities(
          &transport_rules, assumption);
    }
    size_t variable_substitution_count =
        vector_size(leaf_variable_substitutions);
    thm_list normalized_leaf_substitutions =
        (thm_list)vector_copy(leaf_variable_substitutions);
    for (size_t j = 0;
         j < vector_size(leaf_substitutions); ++j) {
      thm equality = leaf_substitutions[j];
      for (size_t k = 0;
           k < vector_size(leaf_variable_substitutions); ++k) {
        thm variable_equality = leaf_variable_substitutions[k];
        if (alpha_compare(
              concl(equality), concl(variable_equality)) != 0) {
          equality = eq_mp_rule(
              cm_semantic_substitute_occurrences(
                concl(equality), variable_equality),
              equality);
        }
      }
      vector_add(&normalized_leaf_substitutions, equality);
    }
    leaf = CONV_WITH_ASMP_TAC(
        leaf, reduce_rewrite_conv, substitution_rules);
    if (!IS_NULL(leaf->solved)) continue;
    leaf_assumptions = goal_lasmps(leaf->g);
    if (cm_semantic_has_head_const(
          goal_ccl(leaf->g), "cm_stmt_scope_ready")) {
      thm typed_local = empty_theorem;
      thm call_local = empty_theorem;
      bool has_typed = false;
      bool has_call = false;
      for (size_t j = 0;
           j < vector_size(leaf_assumptions); ++j) {
        term assumption_term = leaf_assumptions[j].tm;
        if (!has_typed && cm_semantic_has_head_const(
              assumption_term, "cm_typed_program")) {
          typed_local = assume_rule(assumption_term);
          has_typed = true;
        }
        thm assumption = assume_rule(assumption_term);
        if (!has_call &&
            cm_semantic_find_head_conjunct(
              assumption, "cm_call_ok", &call_local)) {
          has_call = true;
        }
      }
      if (has_typed && has_call) {
        term typed_program =
            cm_sr_app_arg_from_right(concl(typed_local), 0);
        term call_program =
            cm_sr_app_arg_from_right(concl(call_local), 3);
        if (alpha_compare(typed_program, call_program) == 0) {
          thm opened_call = conv_rule(
              rewrite_conv(THM_LIST(get_cm_call_ok_def())),
              call_local);
          thm body_scope = specl_rule(
              TERM_LIST(
                call_program,
                cm_sr_app_arg_from_right(concl(call_local), 2)),
              cm_typed_body_scope_ready);
          body_scope = match_mp_rule(body_scope, typed_local);
          body_scope = match_mp_rule(
              body_scope, conjunct1_rule(opened_call));
          body_scope = match_mp_rule(
              body_scope,
              conjunct1_rule(conjunct2_rule(opened_call)));
          if (alpha_compare(
                concl(body_scope), goal_ccl(leaf->g)) == 0) {
            ACCEPT_TAC(leaf, body_scope);
          }
        }
      }
      if (!IS_NULL(leaf->solved)) continue;
    }
    if (cm_semantic_has_head_const(
          goal_ccl(leaf->g), "cm_stmt_context_ready")) {
      term statement_term =
          cm_sr_app_arg_from_right(goal_ccl(leaf->g), 1);
      term cursor_term =
          cm_sr_app_arg_from_right(goal_ccl(leaf->g), 0);
      thm local_scope = empty_theorem;
      bool has_local_scope = false;
      thm_list scope_normalization =
          (thm_list)vector_copy(substitution_rules);
      for (size_t j = 0; j < vector_size(definitions); ++j) {
        vector_add(&scope_normalization, definitions[j]);
      }
      for (size_t j = 0;
           j < vector_size(annotation_definitions); ++j) {
        vector_add(&scope_normalization, annotation_definitions[j]);
      }
      for (size_t j = 0;
           j < vector_size(extra_rules); ++j) {
        thm normalized_extra = conv_rule(
            reduce_rewrite_conv(scope_normalization),
            extra_rules[j]);
        if (cm_semantic_find_stmt_scope_conjunct(
              normalized_extra, statement_term, &local_scope)) {
          has_local_scope = true;
          break;
        }
      }
      if (!has_local_scope) {
        for (size_t j = 0;
             j < vector_size(leaf_assumptions); ++j) {
          thm assumption = conv_rule(
              reduce_rewrite_conv(scope_normalization),
              assume_rule(leaf_assumptions[j].tm));
          if (cm_semantic_find_stmt_scope_conjunct(
                assumption, statement_term, &local_scope)) {
            has_local_scope = true;
            break;
          }
        }
      }
      if (has_local_scope) {
        thm context_ready = specl_rule(
            TERM_LIST(statement_term, cursor_term),
            cm_stmt_scope_context_ready);
        thm_list local_rules = (thm_list)vector_copy(rules);
        vector_add(&local_rules, local_scope);
        for (size_t j = 0;
             j < vector_size(leaf_assumptions); ++j) {
          vector_add(
              &local_rules, assume_rule(leaf_assumptions[j].tm));
        }
        thm premise_view = apply_conversion(
            reduce_rewrite_conv(local_rules),
            dest_imp(concl(context_ready)).tm1);
        thm normalized_premise = eqt_elim_rule(apply_conversion(
            reduce_rewrite_conv(local_rules),
            rhs_of(premise_view)));
        thm premise = eq_mp_rule(
            sym_rule(premise_view), normalized_premise);
        context_ready = match_mp_rule(context_ready, premise);
        if (alpha_compare(
              concl(context_ready), goal_ccl(leaf->g)) == 0) {
          ACCEPT_TAC(leaf, context_ready);
        }
      }
      if (!IS_NULL(leaf->solved)) continue;
      thm local_wf = empty_theorem;
      bool has_local_wf = false;
      thm_list wf_normalization =
          (thm_list)vector_copy(substitution_rules);
      for (size_t j = 0; j < vector_size(definitions); ++j) {
        vector_add(&wf_normalization, definitions[j]);
      }
      for (size_t j = 0;
           j < vector_size(annotation_definitions); ++j) {
        vector_add(&wf_normalization, annotation_definitions[j]);
      }
      for (size_t j = 0;
           j < vector_size(extra_rules); ++j) {
        thm normalized_extra = conv_rule(
            reduce_rewrite_conv(wf_normalization), extra_rules[j]);
        if (cm_semantic_find_stmt_wf_conjunct(
              normalized_extra, statement_term, &local_wf)) {
          has_local_wf = true;
          break;
        }
      }
      if (!has_local_wf) {
        for (size_t j = 0;
             j < vector_size(leaf_assumptions); ++j) {
          thm assumption = conv_rule(
              reduce_rewrite_conv(wf_normalization),
              assume_rule(leaf_assumptions[j].tm));
          if (cm_semantic_find_stmt_wf_conjunct(
                assumption, statement_term, &local_wf)) {
            has_local_wf = true;
            break;
          }
        }
      }
      if (has_local_wf) {
        thm context_ready = specl_rule(TERM_LIST(
            cm_sr_app_arg_from_right(concl(local_wf), 3),
            cm_sr_app_arg_from_right(concl(local_wf), 2),
            statement_term, cursor_term),
            cm_stmt_wf_context_ready);
        thm_list local_rules = (thm_list)vector_copy(rules);
        vector_add(&local_rules, local_wf);
        for (size_t j = 0;
             j < vector_size(leaf_assumptions); ++j) {
          vector_add(
              &local_rules, assume_rule(leaf_assumptions[j].tm));
        }
        while (is_imp(concl(context_ready))) {
          thm premise_view = apply_conversion(
              reduce_rewrite_conv(local_rules),
              dest_imp(concl(context_ready)).tm1);
          thm normalized_premise = eqt_elim_rule(apply_conversion(
              reduce_rewrite_conv(local_rules),
              rhs_of(premise_view)));
          thm premise = eq_mp_rule(
              sym_rule(premise_view), normalized_premise);
          context_ready = match_mp_rule(context_ready, premise);
        }
        if (alpha_compare(
              concl(context_ready), goal_ccl(leaf->g)) == 0) {
          ACCEPT_TAC(leaf, context_ready);
        }
      }
      if (!IS_NULL(leaf->solved)) continue;
    }
    if (is_conj(goal_ccl(leaf->g)) ||
        is_forall(goal_ccl(leaf->g)) ||
        is_imp(goal_ccl(leaf->g))) {
      cm_semantic_close(leaf, extra_rules);
      continue;
    }
    size_t joined_start =
        vector_size(extra_rules) > 12
          ? vector_size(extra_rules) - 12 : 0;
    thm_list joined_rules =
        (thm_list)vector_copy(substitution_rules);
    for (size_t j = 0; j < vector_size(definitions); ++j) {
      vector_add(&joined_rules, definitions[j]);
    }
    for (size_t j = 0;
         j < vector_size(annotation_definitions); ++j) {
      vector_add(&joined_rules, annotation_definitions[j]);
    }
    thm joined = conv_rule(
        reduce_rewrite_conv(joined_rules),
        extra_rules[joined_start]);
    for (size_t j = joined_start + 1;
         j < vector_size(extra_rules); ++j) {
      thm normalized_extra = conv_rule(
          reduce_rewrite_conv(joined_rules), extra_rules[j]);
      joined = conj_rule(joined, normalized_extra);
    }
    for (size_t j = 0; j < vector_size(extra_rules); ++j) {
      if (cm_semantic_contains_coordinate(
            concl(extra_rules[j]))) {
        thm inherited_coordinate = conv_rule(
            reduce_rewrite_conv(joined_rules), extra_rules[j]);
        inherited_coordinate = cm_semantic_apply_substitutions(
            inherited_coordinate, normalized_leaf_substitutions);
        joined = conj_rule(joined, inherited_coordinate);
        break;
      }
    }
    thm transported = conv_rule(
        reduce_rewrite_conv(transport_rules),
        extra_rules[vector_size(extra_rules) - 1]);
    transported = cm_semantic_apply_substitutions(
        transported, normalized_leaf_substitutions);
    joined = conj_rule(joined, transported);
    for (size_t j = variable_substitution_count;
         j < vector_size(normalized_leaf_substitutions); ++j) {
      joined = conj_rule(
          joined, normalized_leaf_substitutions[j]);
      joined = conj_rule(
          joined, sym_rule(normalized_leaf_substitutions[j]));
    }
    for (size_t j = 0; j < vector_size(leaf_assumptions); ++j) {
      bool inherited = false;
      for (size_t k = 0; k < vector_size(extra_rules); ++k) {
        if (cm_semantic_has_conjunct(
              extra_rules[k], leaf_assumptions[j].tm)) {
          inherited = true;
          break;
        }
      }
      if (!inherited) {
        joined = conj_rule(
            joined, assume_rule(leaf_assumptions[j].tm));
      }
    }
    ACCEPT_TAC(leaf, mp_rule(
        taut_rule(mk_imp(concl(joined), goal_ccl(leaf->g))),
        joined));
  }
}

PROOF static thm_list cm_semantic_copy_rules(
    const thm_list source, const thm extra) {
  thm_list copied = (thm_list)vector_create();
  for (size_t i = 0; i < vector_size(source); ++i) {
    vector_add(&copied, source[i]);
  }
  vector_add(&copied, extra);
  return copied;
}

PROOF static thm_list cm_semantic_branch_fact_rules(
    gnode branch, const thm_list base_rules, thm fact) {
  thm_list normalization_rules = (thm_list)vector_create();
  for (size_t i = 0; i < vector_size(base_rules); ++i) {
    if (alpha_compare(concl(base_rules[i]), concl(fact)) != 0) {
      cm_semantic_add_fact_rules(
          &normalization_rules, base_rules[i]);
    }
  }
  vector_add(&normalization_rules, cm_error_task_def);
  vector_add(&normalization_rules,
      get_datatype_distinctness("cm_control"));
  vector_add(&normalization_rules,
      get_datatype_injectivity("cm_control"));
  thm_list result = (thm_list)vector_copy(base_rules);
  labeled_term_list assumptions = goal_lasmps(branch->g);
  for (size_t i = 0; i < vector_size(assumptions); ++i) {
    thm normalized_assumption = conv_rule(
        reduce_rewrite_conv(normalization_rules),
        assume_rule(assumptions[i].tm));
    cm_semantic_add_fact_rules(&result, normalized_assumption);
    cm_semantic_add_fact_rules(
        &normalization_rules, normalized_assumption);
  }
  thm normalized = conv_rule(
      reduce_rewrite_conv(normalization_rules), fact);
  cm_semantic_add_fact_rules(&result, normalized);
  return result;
}

PROOF static void cm_semantic_value_control(
    gnode branch, bool control_task, bool advance_before_ready,
    term annotation, const thm task_shape,
    const thm task_coordinate, const thm task_erases,
    const thm rooted, const thm task_succeeds,
    const thm source_context, const thm_list base_rules);
PROOF static void cm_semantic_finish_next_ready(
    gnode branch, const thm_list rules,
    const thm_list base_rules);

PROOF static void cm_semantic_resolve_ready_branch(
    gnode branch, const thm_list rules,
    const thm_list base_rules, bool advance_before_ready) {
  if (advance_before_ready) {
    cm_semantic_finish_next_ready(branch, rules, base_rules);
  } else {
    cm_semantic_close(branch, rules);
  }
}

PROOF static void cm_semantic_expression_cases(
    gnode branch, term subject, const thm cases_theorem,
    const char *label, const thm_list base_rules) {
  gnode_list cases = DISJ_CASES_TAC(branch,
      ispec_rule(subject, cases_theorem), label);
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode leaf = cases[i];
    while (true) {
      labeled_term_list assumptions = goal_lasmps(leaf->g);
      int index = labeled_term_list_index(assumptions, label);
      if (!is_exists(assumptions[index].tm)) break;
      leaf = ASMP_EXISTS_TAC(leaf, label, NULL);
    }
    thm shape = assume_rule(
        goal_lasmps(leaf->g)[labeled_term_list_index(
          goal_lasmps(leaf->g), label)].tm);
    thm_list rules = cm_semantic_copy_rules(base_rules, shape);
    if ((strcmp(label, "Hr_expr") == 0 ||
        strcmp(label, "Hl_expr") == 0) && i == 2) {
      term concrete_task = rhs_of(base_rules[0]);
      term fid = cm_sr_constructor_arg(concrete_task, 5, 1);
      term state = cm_sr_constructor_arg(concrete_task, 5, 3);
      term concrete_expr = rhs_of(shape);
      term scope = cm_sr_constructor_arg(concrete_expr, 3, 0);
      term slot = cm_sr_constructor_arg(concrete_expr, 3, 1);
      if (strcmp(label, "Hr_expr") == 0) {
        gnode_list binding_cases = BOOL_CASES_TAC(leaf,
            `cm_binding_array (p:cm_program) ${fid:int}
               ${scope:int} ${slot:int}`,
            "Hbinding");
        for (size_t j = 0; j < vector_size(binding_cases); ++j) {
          gnode_list address_cases = BOOL_CASES_TAC(binding_cases[j],
              `cm_binding_address_ok (p:cm_program) ${fid:int}
                 ${scope:int} ${slot:int} ${state:cm_src_state}`,
              "Hbinding_address");
          for (size_t k = 0; k < vector_size(address_cases); ++k) {
            cm_semantic_finish_next_ready(
                address_cases[k], rules, base_rules);
          }
        }
      } else {
        gnode_list address_cases = BOOL_CASES_TAC(leaf,
            `cm_binding_address_ok (p:cm_program) ${fid:int}
               ${scope:int} ${slot:int} ${state:cm_src_state}`,
            "Hlvalue_address");
        for (size_t j = 0; j < vector_size(address_cases); ++j) {
          cm_semantic_finish_next_ready(
              address_cases[j], rules, base_rules);
        }
      }
    } else if ((strcmp(label, "Hr_expr") == 0 ||
        strcmp(label, "Hl_expr") == 0) && i == 5) {
      term concrete_expr = rhs_of(shape);
      term op = cm_sr_constructor_arg(concrete_expr, 3, 0);
      gnode_list load_cases = BOOL_CASES_TAC(
          leaf, `${op:int} == 2i`, "Hunary_load");
      if (strcmp(label, "Hl_expr") == 0) {
        for (size_t j = 0; j < vector_size(load_cases); ++j) {
          cm_semantic_finish_next_ready(
              load_cases[j], rules, base_rules);
        }
      } else {
        cm_semantic_finish_next_ready(
            load_cases[0], rules, base_rules);
        gnode_list address_cases = BOOL_CASES_TAC(
            load_cases[1], `${op:int} == 3i`, "Hunary_address");
        for (size_t j = 0; j < vector_size(address_cases); ++j) {
          cm_semantic_finish_next_ready(
              address_cases[j], rules, base_rules);
        }
      }
    } else if (strcmp(label, "Hr_expr") == 0 && i == 7) {
      term concrete_expr = rhs_of(shape);
      term base = cm_sr_constructor_arg(concrete_expr, 3, 0);
      term mid = cm_sr_constructor_arg(concrete_expr, 3, 1);
      gnode_list member_cases = BOOL_CASES_TAC(leaf,
          `cm_member_array (p:cm_program)
             (cm_expr_type ${base:cm_expr}) ${mid:int}`,
          "Hmember_array");
      for (size_t j = 0; j < vector_size(member_cases); ++j) {
        cm_semantic_finish_next_ready(
            member_cases[j], rules, base_rules);
      }
    } else if (strcmp(label, "Hr_expr") == 0 && i == 8) {
      term concrete_task = rhs_of(base_rules[0]);
      term state = cm_sr_constructor_arg(concrete_task, 5, 3);
      term frames = cm_sr_constructor_arg(concrete_task, 5, 4);
      term concrete_expr = rhs_of(shape);
      term callee = cm_sr_constructor_arg(concrete_expr, 3, 0);
      term args = cm_sr_constructor_arg(concrete_expr, 3, 1);
      gnode_list args_cases = BOOL_CASES_TAC(
          leaf, `${args:(cm_expr)list} == []`, "Hargs_nil");
      gnode_list call_cases = BOOL_CASES_TAC(args_cases[0],
          `cm_call_ok (p:cm_program) ${callee:int}
               ([]:(cm_value)list) ${state:cm_src_state} &&
             cm_call_depth ${frames:(cm_frame)list} < 65536i`,
          "Hcall_ready");
      for (size_t j = 0; j < vector_size(call_cases); ++j) {
        cm_semantic_finish_next_ready(
            call_cases[j], rules, base_rules);
      }
      gnode_list list_cases = DISJ_CASES_TAC(
          args_cases[1],
          ispec_rule(args, get_theorem_by_name("list_CASES")),
          "Hargs_list");
      cm_semantic_close(list_cases[0], rules);
      gnode cons_args = ASMP_EXISTS_TAC(
          list_cases[1], "Hargs_list", NULL);
      cons_args = ASMP_EXISTS_TAC(
          cons_args, "Hargs_list", NULL);
      cm_semantic_finish_next_ready(
          cons_args, rules, base_rules);
    } else if (strcmp(label, "Hr_expr") == 0 && i == 10) {
      term concrete_task = rhs_of(base_rules[0]);
      term state = cm_sr_constructor_arg(concrete_task, 5, 3);
      gnode_list input_cases = BOOL_CASES_TAC(leaf,
          `cm_state_input ${state:cm_src_state} == []`,
          "Hinput_nil");
      cm_semantic_finish_next_ready(
          input_cases[0], rules, base_rules);
      gnode_list byte_cases = BOOL_CASES_TAC(input_cases[1],
          `tower_byte_value
             (HD (cm_state_input ${state:cm_src_state}))`,
          "Hinput_byte");
      for (size_t j = 0; j < vector_size(byte_cases); ++j) {
        cm_semantic_finish_next_ready(
            byte_cases[j], rules, base_rules);
      }
    } else if (strcmp(label, "Hs_stmt") == 0 &&
        (i == 2 || i == 3)) {
      term concrete_task = rhs_of(base_rules[0]);
      term fid = cm_sr_constructor_arg(concrete_task, 5, 1);
      term concrete_stmt = rhs_of(shape);
      term slot = cm_sr_constructor_arg(
          concrete_stmt, i == 2 ? 1 : 2, 0);
      gnode_list slot_cases = BOOL_CASES_TAC(leaf,
          `cm_local_slot_ok (p:cm_program) ${fid:int} ${slot:int}`,
          "Hlocal_slot");
      for (size_t j = 0; j < vector_size(slot_cases); ++j) {
        cm_semantic_finish_next_ready(
            slot_cases[j], rules, base_rules);
      }
    } else {
      cm_semantic_finish_next_ready(leaf, rules, base_rules);
    }
  }
}

PROOF static void cm_semantic_control_cases(
    gnode branch, term control, const thm task_shape,
    const thm_list base_rules, const thm task_coordinate,
    const thm task_succeeds,
    const thm cursors_shape, const thm cursor_shape,
    const thm phase_shape, bool advance_before_ready) {
  const char *control_label = advance_before_ready
      ? "Hcontrol_current" : "Hcontrol_next";
  gnode_list cases = DISJ_CASES_TAC(branch,
      ispec_rule(control, get_datatype_cases("cm_control")),
      control_label);
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode leaf = cases[i];
    while (true) {
      labeled_term_list assumptions = goal_lasmps(leaf->g);
      int index = labeled_term_list_index(
          assumptions, control_label);
      if (!is_exists(assumptions[index].tm)) break;
      leaf = ASMP_EXISTS_TAC(leaf, control_label, NULL);
    }
    thm control_shape = assume_rule(
        goal_lasmps(leaf->g)[labeled_term_list_index(
          goal_lasmps(leaf->g), control_label)].tm);
    thm_list control_compatibility =
        (thm_list)vector_copy(base_rules);
    vector_add(&control_compatibility,
        get_datatype_distinctness("cm_control"));
    vector_add(&control_compatibility,
        get_datatype_injectivity("cm_control"));
    thm normalized_control_shape = conv_rule(
        reduce_rewrite_conv(control_compatibility),
        control_shape);
    if (is_false(concl(normalized_control_shape))) {
      CONTR_TAC(leaf, normalized_control_shape);
      continue;
    }
    thm_list rules = cm_semantic_copy_rules(
        base_rules, control_shape);
    if (advance_before_ready) {
      thm current_ready = conv_rule(
          reduce_rewrite_conv(THM_LIST(
            task_shape, cursors_shape, cursor_shape, phase_shape,
            control_shape, cm_task_layout_ready_def,
            cm_c_layout_ready_def, cm_c_phase_ready_def,
            cm_c_regular_ready_def, cm_c_code_ready_def,
            get_cm_control_kind_def(), cm_cursor_phase_def,
            cm_cursor_break_def, cm_cursor_continue_def,
            get_theorem_by_name("HD"),
            get_theorem_by_name("TL"),
            get_theorem_by_name("NOT_CONS_NIL"))),
          base_rules[5]);
      if (is_false(concl(current_ready))) {
        CONTR_TAC(leaf, current_ready);
        continue;
      }
      vector_add(&rules, current_ready);
    }
    thm child_coordinate = conv_rule(
        reduce_rewrite_conv(THM_LIST(
          control_shape, get_cm_control_kind_def())),
        task_coordinate);
    vector_add(&rules, child_coordinate);
    thm control_cons = conv_rule(
        reduce_rewrite_conv(THM_LIST(
          cursors_shape, cursor_shape, phase_shape,
          cm_cursors_coordinate_def, cm_phase_child_temp_def,
          cm_phase_control_regular_def, cm_phase_code_ready_at_def,
          cm_phase_next_fid_def,
          cm_cursor_phase_def, cm_cursor_temp_def,
          cm_cursor_break_def, cm_cursor_continue_def)),
        child_coordinate);
    vector_add(&rules, control_cons);
    if (i == 5) {
      term concrete_control = rhs_of(control_shape);
      term code = cm_sr_constructor_arg(concrete_control, 1, 0);
      thm current_not_error = match_mp_rule(
          specl_rule(TERM_LIST(code, rhs_of(task_shape)),
            cm_task_succeeds_not_error),
          task_succeeds);
      thm impossible_error = conv_rule(
          reduce_rewrite_conv(THM_LIST(
            control_shape, cm_error_task_def,
            get_datatype_injectivity("cm_control"))),
          current_not_error);
      CONTR_TAC(leaf, impossible_error);
      continue;
    }
    cm_semantic_resolve_ready_branch(
        leaf, rules, base_rules, advance_before_ready);
  }
}

PROOF static void cm_semantic_value_control(
    gnode branch, bool control_task, bool advance_before_ready,
    term annotation, const thm task_shape,
    const thm task_coordinate, const thm task_erases,
    const thm rooted, const thm task_succeeds,
    const thm source_context, const thm_list base_rules) {
  term ann_cursors = mk_comb(`cm_ann_cursors`, annotation);
  term current_task = dest_eq(concl(task_shape)).tm1;
  thm concrete_succeeds = eq_mp_rule(
      ap_term_rule(`cm_task_succeeds`, task_shape),
      task_succeeds);
  thm current_not_done = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        task_shape, get_cm_task_done_def())),
      mk_not(mk_comb(`cm_task_done`, current_task))));
  thm following_succeeds = match_mp_rule(
      match_mp_rule(cm_task_succeeds_step, current_not_done),
      task_succeeds);
  thm following_not_error = match_mp_rule(
      specl_rule(TERM_LIST(
        `1i:int`, mk_comb(`cm_step`, current_task)),
        cm_task_succeeds_not_error),
      following_succeeds);
  const char *cursor_label = advance_before_ready
      ? "Hcursors_current" : "Hcursors_next";
  const char *cursor_shape_label = advance_before_ready
      ? "Hcursor_current" : "Hcursor_next";
  const char *phase_shape_label = advance_before_ready
      ? "Hphase_current" : "Hphase_next";
  gnode_list cursor_cases = DISJ_CASES_TAC(branch,
      ispec_rule(ann_cursors, get_theorem_by_name("list_CASES")),
      cursor_label);
  {
    thm nil_shape = assume_rule(
        goal_lasmps(cursor_cases[0]->g)[labeled_term_list_index(
          goal_lasmps(cursor_cases[0]->g), cursor_label)].tm);
    thm_list normalization_rules = (thm_list)vector_create();
    for (size_t i = 0; i < vector_size(base_rules); ++i) {
      vector_add(&normalization_rules, base_rules[i]);
    }
    thm_list definitions = cm_semantic_step_rules();
    for (size_t i = 0; i < vector_size(definitions); ++i) {
      vector_add(&normalization_rules, definitions[i]);
    }
    thm_list annotation_rules = cm_semantic_annotation_rules();
    for (size_t i = 0; i < vector_size(annotation_rules); ++i) {
      vector_add(&normalization_rules, annotation_rules[i]);
    }
    vector_add(&normalization_rules, cm_cursor_phase_def);
    vector_add(&normalization_rules, cm_cursor_temp_def);
    thm normalized_nil = conv_rule(
        reduce_rewrite_conv(normalization_rules), nil_shape);
    thm_list nil_shape_rules = (thm_list)vector_create();
    for (size_t i = 0; i < vector_size(base_rules); ++i) {
      cm_semantic_add_equality_rules(
          &nil_shape_rules, base_rules[i]);
    }
    thm concrete_nil = conv_rule(
        reduce_rewrite_conv(nil_shape_rules), nil_shape);
    thm_list nil_context_rules =
        (thm_list)vector_copy(nil_shape_rules);
    vector_add(&nil_context_rules, normalized_nil);
    vector_add(
        &nil_context_rules, cm_cursors_context_ready_def);
    vector_add(
        &nil_context_rules, cm_cursors_scope_ready_def);
    vector_add(&nil_context_rules, cm_phase_scope_ready_def);
    vector_add(&nil_context_rules, cm_stmt_scope_ready_def);
    vector_add(
        &nil_context_rules, cm_statement_cursors_ready_def);
    vector_add(&nil_context_rules, cm_stmt_context_ready_def);
    vector_add(&nil_context_rules, get_cm_stmt_wf_def());
    vector_add(&nil_context_rules, cm_cursors_loop_ready_def);
    vector_add(&nil_context_rules, cm_cursors_call_ready_def);
    vector_add(
        &nil_context_rules, cm_phase_accepts_statement_def);
    vector_add(&nil_context_rules,
        cm_phase_requires_statement_parent_def);
    vector_add(&nil_context_rules, cm_phase_control_scope_def);
    vector_add(&nil_context_rules, cm_control_context_ready_def);
    vector_add(&nil_context_rules, cm_cursor_phase_def);
    thm normalized_nil_context = conv_rule(
        reduce_rewrite_conv(nil_context_rules), source_context);
    thm nil_frames = conv_rule(
        reduce_rewrite_conv(THM_LIST(
          nil_shape, cm_cursor_frames_def)),
        task_erases);
    if (is_false(concl(normalized_nil_context))) {
      CONTR_TAC(cursor_cases[0], normalized_nil_context);
    } else {
    thm_list rules = cm_semantic_copy_rules(
        base_rules, normalized_nil);
    vector_add(&rules, nil_shape);
    vector_add(&rules, concrete_nil);
    vector_add(&rules, normalized_nil_context);
    vector_add(&rules, sym_rule(nil_frames));
    if (control_task) {
      term control = cm_sr_constructor_arg(
          rhs_of(task_shape), 5, 2);
      gnode_list exit_cases = BOOL_CASES_TAC(
          cursor_cases[0],
          `cm_control_kind ${control:cm_control} == 4i`,
          "Hnil_control_exit");
      thm_list exit_rules = cm_semantic_branch_fact_rules(
          exit_cases[0], rules, following_not_error);
      cm_semantic_resolve_ready_branch(
          exit_cases[0], exit_rules, base_rules,
          advance_before_ready);
      gnode_list error_cases = BOOL_CASES_TAC(
          exit_cases[1],
          `cm_control_kind ${control:cm_control} == 5i`,
          "Hnil_control_error");
      for (size_t i = 0; i < vector_size(error_cases); ++i) {
        thm_list branch_rules = cm_semantic_branch_fact_rules(
            error_cases[i], rules, following_not_error);
        cm_semantic_resolve_ready_branch(
            error_cases[i], branch_rules, base_rules,
            advance_before_ready);
      }
    } else {
      cm_semantic_resolve_ready_branch(
          cursor_cases[0], rules, base_rules,
          advance_before_ready);
    }
  }
  }
  gnode cons = ASMP_EXISTS_TAC(
      cursor_cases[1], cursor_label, NULL);
  cons = ASMP_EXISTS_TAC(cons, cursor_label, NULL);
  thm cursors_shape = assume_rule(
      goal_lasmps(cons->g)[labeled_term_list_index(
        goal_lasmps(cons->g), cursor_label)].tm);
  thm_list cons_normalization_rules = (thm_list)vector_create();
  for (size_t i = 0; i < vector_size(base_rules); ++i) {
    vector_add(&cons_normalization_rules, base_rules[i]);
  }
  thm_list cons_definitions = cm_semantic_step_rules();
  for (size_t i = 0; i < vector_size(cons_definitions); ++i) {
    vector_add(&cons_normalization_rules, cons_definitions[i]);
  }
  thm_list cons_annotation_rules = cm_semantic_annotation_rules();
  for (size_t i = 0;
       i < vector_size(cons_annotation_rules); ++i) {
    vector_add(
        &cons_normalization_rules, cons_annotation_rules[i]);
  }
  vector_add(&cons_normalization_rules, cm_cursor_phase_def);
  vector_add(&cons_normalization_rules, cm_cursor_temp_def);
  thm normalized_cursors = conv_rule(
      reduce_rewrite_conv(cons_normalization_rules), cursors_shape);
  thm_list cursors_shape_rules = (thm_list)vector_create();
  for (size_t i = 0; i < vector_size(base_rules); ++i) {
    cm_semantic_add_equality_rules(
        &cursors_shape_rules, base_rules[i]);
  }
  thm concrete_cursors = conv_rule(
      reduce_rewrite_conv(cursors_shape_rules), cursors_shape);
  term cursor = cm_sr_app_arg_from_right(rhs_of(cursors_shape), 1);
  term cursor_tail = cm_sr_app_arg_from_right(rhs_of(cursors_shape), 0);
  gnode_list cursor_cases2 = DISJ_CASES_TAC(cons,
      ispec_rule(cursor, get_datatype_cases("cm_acursor")),
      cursor_shape_label);
  gnode cursor_branch = cursor_cases2[0];
  while (true) {
    labeled_term_list assumptions = goal_lasmps(cursor_branch->g);
    int index = labeled_term_list_index(
        assumptions, cursor_shape_label);
    if (!is_exists(assumptions[index].tm)) break;
    cursor_branch = ASMP_EXISTS_TAC(
        cursor_branch, cursor_shape_label, NULL);
  }
  thm cursor_shape = assume_rule(
      goal_lasmps(cursor_branch->g)[labeled_term_list_index(
        goal_lasmps(cursor_branch->g), cursor_shape_label)].tm);
  term concrete_cursor = rhs_of(cursor_shape);
  term phase = cm_sr_constructor_arg(concrete_cursor, 4, 0);
  gnode_list phase_cases = DISJ_CASES_TAC(cursor_branch,
      ispec_rule(phase, get_datatype_cases("cm_aphase")),
      phase_shape_label);
  for (size_t i = 0; i < vector_size(phase_cases); ++i) {
    gnode phase_branch = phase_cases[i];
    while (true) {
      labeled_term_list assumptions = goal_lasmps(phase_branch->g);
      int index = labeled_term_list_index(
          assumptions, phase_shape_label);
      if (!is_exists(assumptions[index].tm)) break;
      phase_branch = ASMP_EXISTS_TAC(
          phase_branch, phase_shape_label, NULL);
    }
    thm phase_shape = assume_rule(
        goal_lasmps(phase_branch->g)[labeled_term_list_index(
          goal_lasmps(phase_branch->g), phase_shape_label)].tm);
    thm coordinate_cons = conv_rule(
        reduce_rewrite_conv(THM_LIST(
          cursors_shape, cursor_shape, phase_shape,
          cm_cursors_coordinate_def, cm_phase_child_temp_def,
          cm_phase_control_regular_def, cm_phase_code_ready_at_def,
          cm_phase_next_fid_def,
          cm_cursor_phase_def, cm_cursor_temp_def,
          cm_cursor_break_def, cm_cursor_continue_def)),
        task_coordinate);
    thm frames_cons = conv_rule(
        reduce_rewrite_conv(THM_LIST(
          cursors_shape, cursor_shape, phase_shape,
          cm_cursor_frames_def, cm_cursor_phase_def,
          cm_phase_frame_def)),
        task_erases);
    struct dest_eq_results frame_sides =
        dest_eq(concl(frames_cons));
    thm frames_nonempty = eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          sym_rule(frames_cons),
          get_theorem_by_name("NOT_CONS_NIL"))),
        mk_not(mk_eq(
          frame_sides.tm2, `[]:(cm_frame)list`))));
    thm rooted_cons = conv_rule(
        reduce_rewrite_conv(THM_LIST(
          cursors_shape, cursor_shape, phase_shape,
          cm_annotation_rooted_def, cm_cursors_rooted_def,
          cm_cursor_phase_def)),
        rooted);
    thm concrete_coordinate = conv_rule(
        reduce_rewrite_conv(cursors_shape_rules), coordinate_cons);
    thm concrete_frames = conv_rule(
        reduce_rewrite_conv(cursors_shape_rules), frames_cons);
    thm concrete_rooted = conv_rule(
        reduce_rewrite_conv(cursors_shape_rules), rooted_cons);
    thm normalized_coordinate = conv_rule(
        reduce_rewrite_conv(cons_normalization_rules), coordinate_cons);
    thm normalized_frames = conv_rule(
        reduce_rewrite_conv(cons_normalization_rules), frames_cons);
    thm normalized_rooted = conv_rule(
        reduce_rewrite_conv(cons_normalization_rules), rooted_cons);
    thm_list rules = (thm_list)vector_create();
    for (size_t j = 0; j < vector_size(base_rules); ++j) {
      vector_add(&rules, base_rules[j]);
    }
    vector_add(&rules, normalized_coordinate);
    vector_add(&rules, sym_rule(concrete_frames));
    vector_add(&rules, normalized_rooted);
    vector_add(&rules, frames_nonempty);
    vector_add(&rules, normalized_cursors);
    vector_add(&rules, concrete_cursors);
    vector_add(&rules, coordinate_cons);
    vector_add(&rules, rooted_cons);
    vector_add(&rules, concrete_coordinate);
    vector_add(&rules, concrete_rooted);
    vector_add(&rules, cursors_shape);
    vector_add(&rules, cursor_shape);
    vector_add(&rules, phase_shape);
    thm_list context_rules = (thm_list)vector_create();
    for (size_t j = 0; j < vector_size(base_rules); ++j) {
      cm_semantic_add_equality_rules(
          &context_rules, base_rules[j]);
    }
    vector_add(&context_rules, normalized_cursors);
    vector_add(&context_rules, cursors_shape);
    vector_add(&context_rules, cursor_shape);
    vector_add(&context_rules, phase_shape);
    vector_add(&context_rules, cm_task_context_ready_def);
    vector_add(&context_rules, cm_cursors_context_ready_def);
    vector_add(&context_rules, cm_cursors_scope_ready_def);
    vector_add(&context_rules, cm_phase_scope_ready_def);
    vector_add(&context_rules, cm_stmt_scope_ready_def);
    vector_add(&context_rules, cm_statement_cursors_ready_def);
    vector_add(&context_rules, cm_phase_accepts_statement_def);
    vector_add(&context_rules,
        cm_phase_requires_statement_parent_def);
    vector_add(&context_rules, cm_phase_control_scope_def);
    vector_add(&context_rules, cm_cursors_loop_ready_def);
    vector_add(&context_rules, cm_cursors_call_ready_def);
    vector_add(&context_rules, cm_stmt_context_ready_def);
    vector_add(&context_rules, get_cm_stmt_wf_def());
    vector_add(&context_rules, cm_control_context_ready_def);
    vector_add(&context_rules, cm_cursor_phase_def);
    vector_add(&context_rules, get_theorem_by_name("HD"));
    vector_add(&context_rules, get_theorem_by_name("TL"));
    vector_add(&context_rules,
        get_theorem_by_name("NOT_CONS_NIL"));
    thm normalized_context = conv_rule(
        reduce_rewrite_conv(context_rules),
        source_context);
    if (is_false(concl(normalized_context))) {
      CONTR_TAC(phase_branch, normalized_context);
      continue;
    }
    cm_semantic_add_fact_rules(&rules, normalized_context);
    thm_list safety_rules = THM_LIST(
        task_shape, sym_rule(normalized_frames),
        cursor_shape, phase_shape);
    thm_list safety_definitions = cm_semantic_step_rules();
    for (size_t j = 0; j < vector_size(safety_definitions); ++j) {
      vector_add(&safety_rules, safety_definitions[j]);
    }
    thm noerror_task_transport = cm_semantic_substitute_occurrences(
        concl(following_not_error), task_shape);
    thm noerror_frame_transport = cm_semantic_substitute_occurrences(
        rhs_of(noerror_task_transport), sym_rule(frames_cons));
    thm concrete_following_not_error = eq_mp_rule(
        noerror_frame_transport,
        eq_mp_rule(noerror_task_transport, following_not_error));
    thm normalized_following_not_error = conv_rule(
        reduce_rewrite_conv(safety_rules),
        concrete_following_not_error);
    vector_add(&rules, normalized_following_not_error);


    if (control_task) {
      term concrete_task = rhs_of(task_shape);
      term control = cm_sr_constructor_arg(concrete_task, 5, 2);
      cm_semantic_control_cases(
          phase_branch, control, task_shape, rules,
          task_coordinate, concrete_succeeds,
          cursors_shape, cursor_shape, phase_shape,
          advance_before_ready);
    } else if (i == 1) {
      term concrete_task = rhs_of(task_shape);
      term value = cm_sr_constructor_arg(concrete_task, 5, 2);
      term state = cm_sr_constructor_arg(concrete_task, 5, 3);
      term concrete_phase = rhs_of(phase_shape);
      term ty = cm_sr_constructor_arg(concrete_phase, 1, 0);
      gnode_list ready_cases = BOOL_CASES_TAC(phase_branch,
          `cm_load_ok ${ty:cm_type} ${value:cm_value}
             ${state:cm_src_state}`,
          advance_before_ready
            ? "Hload_ok_current" : "Hload_ok_next");
      for (size_t j = 0; j < vector_size(ready_cases); ++j) {
        thm_list branch_rules = cm_semantic_branch_fact_rules(
            ready_cases[j], rules, normalized_following_not_error);
        cm_semantic_resolve_ready_branch(
            ready_cases[j], branch_rules, base_rules,
            advance_before_ready);
      }
    } else if (i == 3) {
      term concrete_task = rhs_of(task_shape);
      term state = cm_sr_constructor_arg(concrete_task, 5, 3);
      term concrete_phase = rhs_of(phase_shape);
      term pointer = cm_sr_constructor_arg(concrete_phase, 2, 0);
      term ty = cm_sr_constructor_arg(concrete_phase, 2, 1);
      gnode_list ready_cases = BOOL_CASES_TAC(phase_branch,
          `cm_store_ok ${ty:cm_type} ${pointer:cm_value}
             ${state:cm_src_state}`,
          advance_before_ready
            ? "Hstore_ok_current" : "Hstore_ok_next");
      for (size_t j = 0; j < vector_size(ready_cases); ++j) {
        thm_list branch_rules = cm_semantic_branch_fact_rules(
            ready_cases[j], rules, normalized_following_not_error);
        cm_semantic_resolve_ready_branch(
            ready_cases[j], branch_rules, base_rules,
            advance_before_ready);
      }
    } else if (i == 4) {
      term concrete_task = rhs_of(task_shape);
      term value = cm_sr_constructor_arg(concrete_task, 5, 2);
      term state = cm_sr_constructor_arg(concrete_task, 5, 3);
      term concrete_phase = rhs_of(phase_shape);
      term op = cm_sr_constructor_arg(concrete_phase, 4, 0);
      gnode_list or_cases = BOOL_CASES_TAC(
          phase_branch, `${op:int} == 0i`,
          advance_before_ready
            ? "Hor_op_current" : "Hor_op_next");
      gnode_list or_truth = BOOL_CASES_TAC(or_cases[0],
          `cm_truth ${state:cm_src_state} ${value:cm_value}`,
          advance_before_ready
            ? "Hor_truth_current" : "Hor_truth_next");
      for (size_t j = 0; j < vector_size(or_truth); ++j) {
        cm_semantic_resolve_ready_branch(
            or_truth[j], rules, base_rules, advance_before_ready);
      }
      gnode_list and_cases = BOOL_CASES_TAC(
          or_cases[1], `${op:int} == 1i`,
          advance_before_ready
            ? "Hand_op_current" : "Hand_op_next");
      gnode_list and_truth = BOOL_CASES_TAC(and_cases[0],
          `cm_truth ${state:cm_src_state} ${value:cm_value}`,
          advance_before_ready
            ? "Hand_truth_current" : "Hand_truth_next");
      for (size_t j = 0; j < vector_size(and_truth); ++j) {
        cm_semantic_resolve_ready_branch(
            and_truth[j], rules, base_rules, advance_before_ready);
      }
      cm_semantic_resolve_ready_branch(
          and_cases[1], rules, base_rules, advance_before_ready);
    } else if (i == 5) {
      term concrete_task = rhs_of(task_shape);
      term value = cm_sr_constructor_arg(concrete_task, 5, 2);
      term state = cm_sr_constructor_arg(concrete_task, 5, 3);
      term concrete_phase = rhs_of(phase_shape);
      term op = cm_sr_constructor_arg(concrete_phase, 5, 0);
      term left_value = cm_sr_constructor_arg(concrete_phase, 5, 3);
      gnode_list ready_cases = BOOL_CASES_TAC(phase_branch,
          `cm_binary_ok (p:cm_program) ${op:int}
             ${left_value:cm_value} ${value:cm_value}
             ${state:cm_src_state}`,
          advance_before_ready
            ? "Hbinary_ok_current" : "Hbinary_ok_next");
      for (size_t j = 0; j < vector_size(ready_cases); ++j) {
        thm_list branch_rules = cm_semantic_branch_fact_rules(
            ready_cases[j], rules, normalized_following_not_error);
        cm_semantic_resolve_ready_branch(
            ready_cases[j], branch_rules, base_rules,
            advance_before_ready);
      }
    } else if (i == 8) {
      term concrete_task = rhs_of(task_shape);
      term value = cm_sr_constructor_arg(concrete_task, 5, 2);
      term state = cm_sr_constructor_arg(concrete_task, 5, 3);
      term concrete_phase = rhs_of(phase_shape);
      term base = cm_sr_constructor_arg(concrete_phase, 2, 0);
      gnode_list ready_cases = BOOL_CASES_TAC(phase_branch,
          `cm_ptr_shift_ok (cm_program_structs (p:cm_program))
             ${base:cm_value}
             (cm_value_number ${state:cm_src_state} ${value:cm_value})
             ${state:cm_src_state}`,
          advance_before_ready
            ? "Hshift_ok_current" : "Hshift_ok_next");
      for (size_t j = 0; j < vector_size(ready_cases); ++j) {
        thm_list branch_rules = cm_semantic_branch_fact_rules(
            ready_cases[j], rules, normalized_following_not_error);
        cm_semantic_resolve_ready_branch(
            ready_cases[j], branch_rules, base_rules,
            advance_before_ready);
      }
    } else if (i == 9) {
      term concrete_task = rhs_of(task_shape);
      term value = cm_sr_constructor_arg(concrete_task, 5, 2);
      term state = cm_sr_constructor_arg(concrete_task, 5, 3);
      term concrete_phase = rhs_of(phase_shape);
      term mid = cm_sr_constructor_arg(concrete_phase, 2, 0);
      gnode_list ready_cases = BOOL_CASES_TAC(phase_branch,
          `cm_ptr_member_ok (p:cm_program) ${value:cm_value}
             ${mid:int} ${state:cm_src_state}`,
          advance_before_ready
            ? "Hmember_ok_current" : "Hmember_ok_next");
      for (size_t j = 0; j < vector_size(ready_cases); ++j) {
        thm_list branch_rules = cm_semantic_branch_fact_rules(
            ready_cases[j], rules, normalized_following_not_error);
        cm_semantic_resolve_ready_branch(
            ready_cases[j], branch_rules, base_rules,
            advance_before_ready);
      }
    } else if (i == 14) {
      term concrete_task = rhs_of(task_shape);
      term fid = cm_sr_constructor_arg(concrete_task, 5, 1);
      term state = cm_sr_constructor_arg(concrete_task, 5, 3);
      term concrete_phase = rhs_of(phase_shape);
      term slot = cm_sr_constructor_arg(concrete_phase, 1, 0);
      gnode_list ready_cases = BOOL_CASES_TAC(phase_branch,
          `cm_store_ok
             (cm_slot_ty (inth ${slot:int}
               (cm_function_locals
                 (inth ${fid:int}
                   (cm_program_functions (p:cm_program))))))
             (cm_state_env ${state:cm_src_state} 1i ${slot:int})
             ${state:cm_src_state}`,
          advance_before_ready
            ? "Hinit_store_ok_current" : "Hinit_store_ok_next");
      for (size_t j = 0; j < vector_size(ready_cases); ++j) {
        gnode_list address_cases = BOOL_CASES_TAC(ready_cases[j],
            `cm_binding_address_ok (p:cm_program) ${fid:int}
               1i ${slot:int} ${state:cm_src_state}`,
            advance_before_ready
              ? "Hinit_address_current" : "Hinit_address_next");
        for (size_t k = 0; k < vector_size(address_cases); ++k) {
          thm_list branch_rules = cm_semantic_branch_fact_rules(
              address_cases[k], rules, normalized_following_not_error);
          cm_semantic_resolve_ready_branch(
              address_cases[k], branch_rules, base_rules,
              advance_before_ready);
        }
      }
    } else if (i == 17 || i == 18) {
      term concrete_task = rhs_of(task_shape);
      term value = cm_sr_constructor_arg(concrete_task, 5, 2);
      term state = cm_sr_constructor_arg(concrete_task, 5, 3);
      gnode_list truth_cases = BOOL_CASES_TAC(phase_branch,
          `cm_truth ${state:cm_src_state} ${value:cm_value}`,
          advance_before_ready
            ? "Hcondition_truth_current"
            : "Hcondition_truth_next");
      for (size_t j = 0; j < vector_size(truth_cases); ++j) {
        cm_semantic_resolve_ready_branch(
            truth_cases[j], rules, base_rules, advance_before_ready);
      }
    } else if (i == 21) {
      term concrete_task = rhs_of(task_shape);
      term value = cm_sr_constructor_arg(concrete_task, 5, 2);
      term state = cm_sr_constructor_arg(concrete_task, 5, 3);
      term concrete_phase = rhs_of(phase_shape);
      term callee = cm_sr_constructor_arg(concrete_phase, 8, 0);
      term rest = cm_sr_constructor_arg(concrete_phase, 8, 1);
      term values = cm_sr_constructor_arg(concrete_phase, 8, 2);
      gnode_list rest_cases = BOOL_CASES_TAC(
          phase_branch, `${rest:(cm_expr)list} == []`,
          advance_before_ready
            ? "Harg_rest_nil_current" : "Harg_rest_nil_next");
      gnode_list call_cases = BOOL_CASES_TAC(rest_cases[0],
          `cm_call_ok (p:cm_program) ${callee:int}
               (REVERSE (${value:cm_value} ::
                 ${values:(cm_value)list}))
               ${state:cm_src_state} &&
             cm_call_depth
               (cm_cursor_frames ${cursor_tail:(cm_acursor)list}) <
               65536i`,
          advance_before_ready
            ? "Harg_call_ready_current"
            : "Harg_call_ready_next");
      for (size_t j = 0; j < vector_size(call_cases); ++j) {
        thm_list branch_rules = cm_semantic_branch_fact_rules(
            call_cases[j], rules, normalized_following_not_error);
        cm_semantic_resolve_ready_branch(
            call_cases[j], branch_rules, base_rules,
            advance_before_ready);
      }
      cm_semantic_resolve_ready_branch(
          rest_cases[1], rules, base_rules, advance_before_ready);
    } else {
      cm_semantic_resolve_ready_branch(
          phase_branch, rules, base_rules, advance_before_ready);
    }
  }
}
PROOF static void cm_semantic_finish_next_ready(
    gnode branch, const thm_list rules,
    const thm_list base_rules) {
  term next_task = `cm_step (task:cm_task)`;
  term next_annotation = `cm_update_annotation
      (cm_annotation_step (task:cm_task) (ann:cm_annotation))`;
  thm next_source_context =
      base_rules[vector_size(base_rules) - 1];
  bool found_next_source_context = false;
  for (size_t i = 0; i < vector_size(base_rules); ++i) {
    term conclusion = concl(base_rules[i]);
    if (is_conj(conclusion) &&
        cm_semantic_contains_const(
          conclusion, "cm_cursors_context_ready") &&
        (cm_semantic_contains_const(
           conclusion, "cm_control_context_ready") ||
         cm_semantic_contains_const(
           conclusion, "cm_cursors_scope_ready") ||
         cm_semantic_contains_const(
           conclusion, "cm_statement_cursors_ready") ||
         cm_semantic_contains_const(
           conclusion, "cm_stmt_context_ready"))) {
      next_source_context = base_rules[i];
      found_next_source_context = true;
      break;
    }
  }
  if (!found_next_source_context) {
    for (size_t i = 0; i < vector_size(base_rules); ++i) {
      if (cm_semantic_has_head_const(
            concl(base_rules[i]), "cm_cursors_context_ready")) {
        next_source_context = base_rules[i];
        break;
      }
    }
  }
  thm_list step_rules = (thm_list)vector_create();
  for (size_t i = 0; i < vector_size(rules); ++i) {
    vector_add(&step_rules, rules[i]);
  }
  thm_list definitions = cm_semantic_step_rules();
  for (size_t i = 0; i < vector_size(definitions); ++i) {
    vector_add(&step_rules, definitions[i]);
  }
  labeled_term_list step_assumptions = goal_lasmps(branch->g);
  for (size_t i = 0; i < vector_size(step_assumptions); ++i) {
    vector_add(&step_rules, assume_rule(step_assumptions[i].tm));
  }
  thm computed_next = apply_conversion(
      reduce_rewrite_conv(step_rules), next_task);
  gnode_list cases = DISJ_CASES_TAC(branch,
      ispec_rule(next_task, get_datatype_cases("cm_task")),
      "Hnext");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode leaf = cases[i];
    while (true) {
      labeled_term_list assumptions = goal_lasmps(leaf->g);
      int index = labeled_term_list_index(assumptions, "Hnext");
      if (!is_exists(assumptions[index].tm)) break;
      leaf = ASMP_EXISTS_TAC(leaf, "Hnext", NULL);
    }
    thm next_shape = assume_rule(
        goal_lasmps(leaf->g)[labeled_term_list_index(
          goal_lasmps(leaf->g), "Hnext")].tm);
    thm agreement = trans_rule(sym_rule(next_shape), computed_next);
    thm normalized_agreement = conv_rule(
        reduce_rewrite_conv(THM_LIST(
          get_datatype_distinctness("cm_task"),
          get_datatype_injectivity("cm_task"))),
        agreement);
    if (is_false(concl(normalized_agreement))) {
      CONTR_TAC(leaf, normalized_agreement);
      continue;
    }
    thm_list next_rules = (thm_list)vector_create();
    cm_semantic_add_fact_rules(
        &next_rules, normalized_agreement);
    for (size_t j = 0; j < vector_size(rules); ++j) {
      vector_add(&next_rules, rules[j]);
    }
    for (size_t j = 0; j < vector_size(step_assumptions); ++j) {
      vector_add(&next_rules, assume_rule(step_assumptions[j].tm));
    }
    if (i == 4 || i == 5) {
      thm shaped_next_coordinate = conv_rule(
          reduce_rewrite_conv(THM_LIST(
            next_shape, cm_task_coordinate_ready_def,
            cm_annotation_child_ready_def)),
          base_rules[10]);
      thm shaped_next_erases = conv_rule(
          reduce_rewrite_conv(THM_LIST(
            next_shape, cm_annotation_erases_def)),
          base_rules[8]);
      cm_semantic_value_control(
          leaf, i == 5, false, next_annotation, next_shape,
          shaped_next_coordinate, shaped_next_erases, base_rules[9],
          base_rules[11],
          next_source_context, next_rules);
    } else if (i == 1) {
      term concrete_task = rhs_of(next_shape);
      term concrete_program =
          cm_sr_constructor_arg(concrete_task, 5, 0);
      term concrete_fid =
          cm_sr_constructor_arg(concrete_task, 5, 1);
      term concrete_expr =
          cm_sr_constructor_arg(concrete_task, 5, 2);
      term concrete_state =
          cm_sr_constructor_arg(concrete_task, 5, 3);
      term concrete_frames =
          cm_sr_constructor_arg(concrete_task, 5, 4);
      thm shaped_succeeds = eq_mp_rule(
          ap_term_rule(`cm_task_succeeds`, next_shape),
          base_rules[11]);
      thm source_ready = match_mp_rule(
          specl_rule(TERM_LIST(
            concrete_program, concrete_fid, concrete_expr,
            concrete_state, concrete_frames),
            cm_rtask_succeeds_call_ready),
          shaped_succeeds);
      thm shaped_erases = conv_rule(
          reduce_rewrite_conv(THM_LIST(
            next_shape, cm_annotation_erases_def)),
          base_rules[8]);
      thm layout_ready = match_mp_rule(match_mp_rule(
          match_mp_rule(specl_rule(TERM_LIST(
            concrete_program, concrete_fid, concrete_expr,
            concrete_state, concrete_frames, next_annotation),
            cm_r_source_ready_layout),
          shaped_succeeds), source_ready), shaped_erases);
      thm shaped_next_coordinate = conv_rule(
          reduce_rewrite_conv(THM_LIST(
            next_shape, cm_task_coordinate_ready_def,
            cm_annotation_child_ready_def)),
          base_rules[10]);
      thm program_equality = conjunct1_rule(
          shaped_next_coordinate);
      thm layout_program_transport =
          cm_semantic_substitute_occurrences(
            concl(layout_ready), program_equality);
      thm program_layout_ready = eq_mp_rule(
          layout_program_transport, layout_ready);
      thm ready_pair = conj_rule(
          program_equality, program_layout_ready);
      thm target_reduction = apply_conversion(
          reduce_rewrite_conv(THM_LIST(
            next_shape, cm_task_layout_ready_def)),
          `cm_task_layout_ready (p:cm_program)
             ${next_task:cm_task} ${next_annotation:cm_annotation}`);
      thm layout_result = eq_mp_rule(
          sym_rule(target_reduction), ready_pair);
      gnode_list properties = CONJ_TAC(leaf);
      ACCEPT_TAC(properties[0], layout_result);
      thm_list context_rules = (thm_list)vector_copy(next_rules);
      vector_add(&context_rules, next_source_context);
      cm_semantic_close(properties[1], context_rules);
    } else if (i == 2) {
      term concrete_task = rhs_of(next_shape);
      term concrete_program =
          cm_sr_constructor_arg(concrete_task, 5, 0);
      term concrete_fid =
          cm_sr_constructor_arg(concrete_task, 5, 1);
      term concrete_expr =
          cm_sr_constructor_arg(concrete_task, 5, 2);
      term concrete_state =
          cm_sr_constructor_arg(concrete_task, 5, 3);
      term concrete_frames =
          cm_sr_constructor_arg(concrete_task, 5, 4);
      thm shaped_succeeds = eq_mp_rule(
          ap_term_rule(`cm_task_succeeds`, next_shape),
          base_rules[11]);
      thm lvalue = match_mp_rule(
          specl_rule(TERM_LIST(
            concrete_program, concrete_fid, concrete_expr,
            concrete_state, concrete_frames),
            cm_ltask_succeeds_layout_ready),
          shaped_succeeds);
      thm shaped_next_coordinate = conv_rule(
          reduce_rewrite_conv(THM_LIST(
            next_shape, cm_task_coordinate_ready_def,
            cm_annotation_child_ready_def)),
          base_rules[10]);
      thm program_equality = conjunct1_rule(
          shaped_next_coordinate);
      thm layout_program_transport =
          cm_semantic_substitute_occurrences(
            concl(lvalue), program_equality);
      thm program_layout_ready = eq_mp_rule(
          layout_program_transport, lvalue);
      thm ready_pair = conj_rule(
          program_equality, program_layout_ready);
      thm target_reduction = apply_conversion(
          reduce_rewrite_conv(THM_LIST(
            next_shape, cm_task_layout_ready_def)),
          `cm_task_layout_ready (p:cm_program)
             ${next_task:cm_task} ${next_annotation:cm_annotation}`);
      thm layout_result = eq_mp_rule(
          sym_rule(target_reduction), ready_pair);
      gnode_list properties = CONJ_TAC(leaf);
      ACCEPT_TAC(properties[0], layout_result);
      thm_list context_rules = (thm_list)vector_copy(next_rules);
      vector_add(&context_rules, next_source_context);
      cm_semantic_close(properties[1], context_rules);
    } else if (i == 3) {
      term concrete_task = rhs_of(next_shape);
      term concrete_program =
          cm_sr_constructor_arg(concrete_task, 5, 0);
      term concrete_fid =
          cm_sr_constructor_arg(concrete_task, 5, 1);
      term concrete_stmt =
          cm_sr_constructor_arg(concrete_task, 5, 2);
      term concrete_state =
          cm_sr_constructor_arg(concrete_task, 5, 3);
      term concrete_frames =
          cm_sr_constructor_arg(concrete_task, 5, 4);
      thm shaped_succeeds = eq_mp_rule(
          ap_term_rule(`cm_task_succeeds`, next_shape),
          base_rules[11]);
      thm start_safe = match_mp_rule(
          specl_rule(TERM_LIST(
            concrete_program, concrete_fid, concrete_stmt,
            concrete_state, concrete_frames),
            cm_stask_succeeds_start_safe),
          shaped_succeeds);
      thm shaped_next_coordinate = conv_rule(
          reduce_rewrite_conv(THM_LIST(
            next_shape, cm_task_coordinate_ready_def,
            cm_annotation_child_ready_def)),
          base_rules[10]);
      thm program_equality = conjunct1_rule(
          shaped_next_coordinate);
      thm safe_program_transport =
          cm_semantic_substitute_occurrences(
            concl(start_safe), program_equality);
      thm program_start_safe = eq_mp_rule(
          safe_program_transport, start_safe);
      thm ready_pair = conj_rule(
          program_equality, program_start_safe);
      thm target_reduction = apply_conversion(
          reduce_rewrite_conv(THM_LIST(
            next_shape, cm_task_layout_ready_def)),
          `cm_task_layout_ready (p:cm_program)
             ${next_task:cm_task} ${next_annotation:cm_annotation}`);
      thm layout_result = eq_mp_rule(
          sym_rule(target_reduction), ready_pair);
      gnode_list properties = CONJ_TAC(leaf);
      ACCEPT_TAC(properties[0], layout_result);
      thm_list context_rules = (thm_list)vector_copy(next_rules);
      vector_add(&context_rules, next_source_context);
      for (size_t j = 0; j < vector_size(base_rules); ++j) {
        if (cm_semantic_has_head_const(
              concl(base_rules[j]), "cm_stmt_scope_ready")) {
          vector_add(&context_rules, base_rules[j]);
          break;
        }
      }
      size_t context_rule_count = vector_size(context_rules);
      for (size_t j = 0; j < context_rule_count; ++j) {
        thm call_fact = empty_theorem;
        if (!cm_semantic_find_head_conjunct(
              context_rules[j], "cm_call_ok", &call_fact)) {
          continue;
        }
        thm opened_call = conv_rule(
            rewrite_conv(THM_LIST(get_cm_call_ok_def())), call_fact);
        term call_program =
            cm_sr_app_arg_from_right(concl(call_fact), 3);
        term call_fid =
            cm_sr_app_arg_from_right(concl(call_fact), 2);
        thm body_context = specl_rule(
            TERM_LIST(call_program, call_fid),
            cm_typed_body_context_ready);
        body_context = match_mp_rule(
            body_context, base_rules[1]);
        body_context = match_mp_rule(
            body_context, conjunct1_rule(opened_call));
        body_context = match_mp_rule(
            body_context,
            conjunct1_rule(conjunct2_rule(opened_call)));
        vector_add(&context_rules, body_context);
        break;
      }
      cm_semantic_close(properties[1], context_rules);
    } else {
      cm_semantic_close(leaf, next_rules);
    }
  }
}
PROOF static thm cm_semantic_task_case_def = new_rec_definition(
    get_cm_task_recursion(),
    `(!q input. cm_semantic_task_case
        (CMStartTask (q:cm_program) (input:(int)list)) = 0i) &&
     (!q fid expr st frames. cm_semantic_task_case
        (CMRTask (q:cm_program) (fid:int) (expr:cm_expr)
          (st:cm_src_state) (frames:(cm_frame)list)) = 1i) &&
     (!q fid expr st frames. cm_semantic_task_case
        (CMLTask (q:cm_program) (fid:int) (expr:cm_expr)
          (st:cm_src_state) (frames:(cm_frame)list)) = 2i) &&
     (!q fid stmt st frames. cm_semantic_task_case
        (CMSTask (q:cm_program) (fid:int) (stmt:cm_stmt)
          (st:cm_src_state) (frames:(cm_frame)list)) = 3i) &&
     (!q fid value st frames. cm_semantic_task_case
        (CMVTask (q:cm_program) (fid:int) (value:cm_value)
          (st:cm_src_state) (frames:(cm_frame)list)) = 4i) &&
     (!q fid control st frames. cm_semantic_task_case
        (CMCTask (q:cm_program) (fid:int) (control:cm_control)
          (st:cm_src_state) (frames:(cm_frame)list)) = 5i) &&
     (!st control status. cm_semantic_task_case
        (CMDoneTask (st:cm_src_state) (control:cm_control)
          (status:int)) = 6i)`);


PROOF static thm cm_prove_task_ready_case(term selected_case) {
  term typed = `cm_typed_program (p:cm_program)`;
  term erases = `cm_annotation_erases
      (task:cm_task) (ann:cm_annotation)`;
  term rooted = `cm_annotation_rooted (ann:cm_annotation)`;
  term coordinate = `cm_task_coordinate_ready
      (p:cm_program) (task:cm_task) (ann:cm_annotation)`;
  term runtime = `cm_task_runtime_invariant
      (p:cm_program) (task:cm_task) (ann:cm_annotation)`;
  term ready = `cm_task_layout_ready
      (p:cm_program) (task:cm_task) (ann:cm_annotation)`;
  term context = `cm_task_context_ready
      (task:cm_task) (ann:cm_annotation)`;
  term succeeds = `cm_task_succeeds (task:cm_task)`;
  term selected = mk_eq(
      mk_comb(`cm_semantic_task_case`, `task:cm_task`),
      selected_case);
  term next_ready = `cm_task_layout_ready (p:cm_program)
      (cm_step (task:cm_task))
      (cm_update_annotation
        (cm_annotation_step task (ann:cm_annotation)))`;
  term next_context = `cm_task_context_ready
      (cm_step (task:cm_task))
      (cm_update_annotation
        (cm_annotation_step task (ann:cm_annotation)))`;
  term target = mk_conj(next_ready, next_context);
  term body = imp_chain(TERM_LIST(
      typed, erases, rooted, coordinate, runtime, ready,
      context, succeeds, selected), target);
  gnode root = gnode_new_with_ccl(
      list_mk_forall(free_vars(body), body));
  gnode introduced = AUTO_INTROS_TAC(root);
  thm typed_fact = assume_rule(typed);
  thm typed_open = conv_rule(
      rewrite_conv(THM_LIST(get_cm_typed_program_def())),
      typed_fact);
  thm typed_main = conjunct2_rule(conjunct2_rule(
      conjunct2_rule(conjunct2_rule(typed_open))));
  thm main_safe = match_mp_rule(match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(
        `p:cm_program`, `cm_program_main (p:cm_program)`),
        cm_typed_body_start_safe),
      typed_fact),
      conjunct1_rule(typed_main)),
      conjunct1_rule(conjunct2_rule(typed_main)));
  term initial_state =
      `cm_initial_state (p:cm_program) (input:(int)list)`;
  thm main_context = specl_rule(TERM_LIST(
      `p:cm_program`, `cm_program_main (p:cm_program)`),
      cm_typed_body_context_ready);
  main_context = match_mp_rule(main_context, typed_fact);
  main_context = match_mp_rule(
      main_context, conjunct1_rule(typed_main));
  main_context = match_mp_rule(
      main_context, conjunct1_rule(conjunct2_rule(typed_main)));
  main_context = specl_rule(TERM_LIST(
      `-- 1i:int`, `cm_state_env ${initial_state:cm_src_state}`,
      `cm_state_fp ${initial_state:cm_src_state}`,
      `cm_state_regions ${initial_state:cm_src_state}`,
      `CMIntTy:cm_type`, `0i:int`, `0i:int`, `0i:int`,
      `[CMACursor CAHaltP 0i 0i 0i]:(cm_acursor)list`),
      main_context);
  thm main_wf = match_mp_rule(
      spec_rule(`p:cm_program`, cm_typed_main_body_wf), typed_fact);
  thm main_scope = specl_rule(TERM_LIST(
      `p:cm_program`, `cm_program_main (p:cm_program)`),
      cm_typed_body_scope_ready);
  main_scope = match_mp_rule(main_scope, typed_fact);
  main_scope = match_mp_rule(
      main_scope, conjunct1_rule(typed_main));
  main_scope = match_mp_rule(
      main_scope, conjunct1_rule(conjunct2_rule(typed_main)));
  thm erases_fact = assume_rule(erases);
  thm rooted_fact = assume_rule(rooted);
  thm coordinate_fact = assume_rule(coordinate);
  thm runtime_fact = assume_rule(runtime);
  thm ready_fact = assume_rule(ready);
  thm context_fact = assume_rule(context);
  thm succeeds_fact = assume_rule(succeeds);
  thm selected_fact = assume_rule(selected);
  thm annotation_sound = match_mp_rule(
      cm_annotation_step_sound,
      conj_rule(rooted_fact, erases_fact));
  thm next_erases = conjunct1_rule(annotation_sound);
  thm next_rooted = conjunct2_rule(annotation_sound);
  thm next_coordinate = match_mp_rule(
      match_mp_rule(cm_task_coordinate_step, erases_fact),
      coordinate_fact);

  gnode_list cases = DISJ_CASES_TAC(introduced,
      ispec_rule(`task:cm_task`, get_datatype_cases("cm_task")),
      "Htask");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode branch = cases[i];
    while (true) {
      labeled_term_list assumptions = goal_lasmps(branch->g);
      int index = labeled_term_list_index(assumptions, "Htask");
      if (!is_exists(assumptions[index].tm)) break;
      branch = ASMP_EXISTS_TAC(branch, "Htask", NULL);
    }
    thm task_shape = assume_rule(
        goal_lasmps(branch->g)[labeled_term_list_index(
          goal_lasmps(branch->g), "Htask")].tm);
    thm selected_branch = conv_rule(
        reduce_rewrite_conv(THM_LIST(
          task_shape, cm_semantic_task_case_def)),
        selected_fact);
    if (is_false(concl(selected_branch))) {
      CONTR_TAC(branch, selected_branch);
      continue;
    }
    thm task_coordinate = conv_rule(
        reduce_rewrite_conv(THM_LIST(
          task_shape, cm_task_coordinate_ready_def,
          cm_annotation_child_ready_def)),
        coordinate_fact);
    thm task_erases = conv_rule(
        reduce_rewrite_conv(THM_LIST(
          task_shape, cm_annotation_erases_def)),
        erases_fact);
    thm task_runtime = conv_rule(
        reduce_rewrite_conv(THM_LIST(
          task_shape, cm_task_runtime_invariant_def)),
        runtime_fact);
    thm task_ready = conv_rule(
        reduce_rewrite_conv(THM_LIST(
          task_shape, cm_task_layout_ready_def)),
        ready_fact);
    thm task_context = conv_rule(
        reduce_rewrite_conv(THM_LIST(
          task_shape, cm_task_context_ready_def)),
        context_fact);
    thm_list base_rules = THM_LIST(
        task_shape, typed_fact, task_coordinate, task_erases,
        task_runtime, task_ready, succeeds_fact, main_safe,
        next_erases, next_rooted, next_coordinate);
    if (i < 6) {
      thm not_done = eqt_elim_rule(apply_conversion(
          reduce_rewrite_conv(THM_LIST(
            task_shape, get_cm_task_done_def())),
          `~cm_task_done (task:cm_task)`));
      thm next_succeeds = match_mp_rule(
          match_mp_rule(cm_task_succeeds_step, not_done),
          succeeds_fact);
      thm next_not_error = match_mp_rule(
          specl_rule(TERM_LIST(`1i:int`, `cm_step (task:cm_task)`),
            cm_task_succeeds_not_error),
          next_succeeds);
      vector_add(&base_rules, next_succeeds);
      vector_add(&base_rules, next_not_error);
    }
    vector_add(&base_rules, task_context);
    vector_add(&base_rules, main_context);
    vector_add(&base_rules, main_wf);
    vector_add(&base_rules, main_scope);

    term concrete_task = rhs_of(task_shape);
    if (i == 0) {
      cm_semantic_finish_next_ready(
          branch, base_rules, base_rules);
    } else if (i == 1 || i == 2) {
      term expression = cm_sr_constructor_arg(concrete_task, 5, 2);
      cm_semantic_expression_cases(branch, expression,
          get_cm_expr_cases(), i == 1 ? "Hr_expr" : "Hl_expr",
          base_rules);
    } else if (i == 3) {
      term statement = cm_sr_constructor_arg(concrete_task, 5, 2);
      cm_semantic_expression_cases(branch, statement,
          get_cm_stmt_cases(), "Hs_stmt", base_rules);
    } else if (i == 4) {
      cm_semantic_value_control(
          branch, false, true, `ann:cm_annotation`, task_shape,
          conjunct2_rule(task_coordinate), task_erases, rooted_fact,
          succeeds_fact, task_context, base_rules);
    } else if (i == 5) {
      cm_semantic_value_control(
          branch, true, true, `ann:cm_annotation`, task_shape,
          conjunct2_rule(task_coordinate), task_erases, rooted_fact,
          succeeds_fact, task_context, base_rules);
    } else {
      cm_semantic_close(branch, base_rules);
    }
  }
  return gnode_prove(root);
}
PROOF static thm cm_task_ready_step_case_0 =
    cm_prove_task_ready_case(`0i:int`);
PROOF static thm cm_task_ready_step_case_1 =
    cm_prove_task_ready_case(`1i:int`);
PROOF static thm cm_task_ready_step_case_2 =
    cm_prove_task_ready_case(`2i:int`);
PROOF static thm cm_task_ready_step_case_3 =
    cm_prove_task_ready_case(`3i:int`);
PROOF static thm cm_task_ready_step_case_4 =
    cm_prove_task_ready_case(`4i:int`);
PROOF static thm cm_task_ready_step_case_5 =
    cm_prove_task_ready_case(`5i:int`);
PROOF static thm cm_task_ready_step_case_6 =
    cm_prove_task_ready_case(`6i:int`);
PROOF static thm cm_prove_task_ready_step(
    const bool layout_property) {
  term typed = `cm_typed_program (p:cm_program)`;
  term erases = `cm_annotation_erases
      (task:cm_task) (ann:cm_annotation)`;
  term rooted = `cm_annotation_rooted (ann:cm_annotation)`;
  term coordinate = `cm_task_coordinate_ready
      (p:cm_program) (task:cm_task) (ann:cm_annotation)`;
  term runtime = `cm_task_runtime_invariant
      (p:cm_program) (task:cm_task) (ann:cm_annotation)`;
  term ready = `cm_task_layout_ready
      (p:cm_program) (task:cm_task) (ann:cm_annotation)`;
  term context = `cm_task_context_ready
      (task:cm_task) (ann:cm_annotation)`;
  term succeeds = `cm_task_succeeds (task:cm_task)`;
  term target = layout_property
      ? `cm_task_layout_ready (p:cm_program)
          (cm_step (task:cm_task))
          (cm_update_annotation
            (cm_annotation_step task (ann:cm_annotation)))`
      : `cm_task_context_ready
          (cm_step (task:cm_task))
          (cm_update_annotation
            (cm_annotation_step task (ann:cm_annotation)))`;
  term body = imp_chain(TERM_LIST(
      typed, erases, rooted, coordinate, runtime, ready,
      context, succeeds), target);
  gnode root = gnode_new_with_ccl(
      list_mk_forall(free_vars(body), body));
  gnode introduced = AUTO_INTROS_TAC(root);
  thm_list case_theorems = THM_LIST(
      cm_task_ready_step_case_0, cm_task_ready_step_case_1,
      cm_task_ready_step_case_2, cm_task_ready_step_case_3,
      cm_task_ready_step_case_4, cm_task_ready_step_case_5,
      cm_task_ready_step_case_6);
  term_list case_values = TERM_LIST(
      `0i:int`, `1i:int`, `2i:int`, `3i:int`,
      `4i:int`, `5i:int`, `6i:int`);
  gnode_list cases = DISJ_CASES_TAC(introduced,
      ispec_rule(`task:cm_task`, get_datatype_cases("cm_task")),
      "Htask_final");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode branch = cases[i];
    while (true) {
      labeled_term_list assumptions = goal_lasmps(branch->g);
      int index = labeled_term_list_index(
          assumptions, "Htask_final");
      if (!is_exists(assumptions[index].tm)) break;
      branch = ASMP_EXISTS_TAC(branch, "Htask_final", NULL);
    }
    thm task_shape = assume_rule(
        goal_lasmps(branch->g)[labeled_term_list_index(
          goal_lasmps(branch->g), "Htask_final")].tm);
    term selected = mk_eq(
        mk_comb(`cm_semantic_task_case`, `task:cm_task`),
        case_values[i]);
    thm selected_fact = eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          task_shape, cm_semantic_task_case_def)),
        selected));
    thm result = case_theorems[i];
    result = match_mp_rule(result, assume_rule(typed));
    result = match_mp_rule(result, assume_rule(erases));
    result = match_mp_rule(result, assume_rule(rooted));
    result = match_mp_rule(result, assume_rule(coordinate));
    result = match_mp_rule(result, assume_rule(runtime));
    result = match_mp_rule(result, assume_rule(ready));
    result = match_mp_rule(result, assume_rule(context));
    result = match_mp_rule(result, assume_rule(succeeds));
    result = match_mp_rule(result, selected_fact);
    result = layout_property
        ? conjunct1_rule(result)
        : conjunct2_rule(result);
    ACCEPT_TAC(branch, result);
  }
  return gnode_prove(root);
}
PROOF thm cm_task_ready_step = cm_prove_task_ready_step(true);
PROOF thm cm_task_context_step = cm_prove_task_ready_step(false);

PROOF static int cmc_preservation_ready_semantic_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_ready_semantic_axioms_before,
      "cmc_preservation_ready_semantic introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_ready_semantic_checks =
    cmc_preservation_ready_semantic_final_checks();
