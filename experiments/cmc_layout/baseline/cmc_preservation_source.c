#include "proof/proof.h"
#include "userlib/proof.h"
#include "cmc_preservation_source.h"
#include "cmc_preservation_code_task.h"
#include "cmc_lang.h"
#include "cmc_preservation_state.h"

#require "cmc_preservation_code_task.c"
#require "cmc_preservation_state.c"

PROOF size_t _cmc_preservation_source_axioms_before =
    vector_size(get_all_axioms());

PROOF thm cm_error_task_def = new_rec_definition(
    get_cm_task_recursion(),
    `(!code p input. cm_error_task (code:int)
        (CMStartTask (p:cm_program) (input:(int)list)) = F) &&
     (!code p fid expr st ks. cm_error_task code
        (CMRTask (p:cm_program) (fid:int) (expr:cm_expr)
          (st:cm_src_state) (ks:(cm_frame)list)) = F) &&
     (!code p fid expr st ks. cm_error_task code
        (CMLTask (p:cm_program) (fid:int) (expr:cm_expr)
          (st:cm_src_state) (ks:(cm_frame)list)) = F) &&
     (!code p fid stmt st ks. cm_error_task code
        (CMSTask (p:cm_program) (fid:int) (stmt:cm_stmt)
          (st:cm_src_state) (ks:(cm_frame)list)) = F) &&
     (!code p fid value st ks. cm_error_task code
        (CMVTask (p:cm_program) (fid:int) (value:cm_value)
          (st:cm_src_state) (ks:(cm_frame)list)) = F) &&
     (!code p fid ctl st ks. cm_error_task code
        (CMCTask (p:cm_program) (fid:int) (ctl:cm_control)
          (st:cm_src_state) (ks:(cm_frame)list)) =
        (ctl == CMError code)) &&
     (!code st ctl status. cm_error_task code
        (CMDoneTask (st:cm_src_state) (ctl:cm_control)
          (status:int)) = (ctl == CMError code))`);
PROOF static int _c_cm_error_task =
    cst_add_const_to_header(`cm_error_task`);

PROOF static thm_list cm_error_step_rules(void) {
  return THM_LIST(
      cm_error_task_def, get_cm_step_def(), get_cm_capply_def(),
      get_cm_control_kind_def(), get_cm_control_status_def(),
      get_theorem_by_name("HD"), get_theorem_by_name("TL"),
      get_theorem_by_name("NOT_CONS_NIL"),
      get_datatype_distinctness("cm_control"),
      get_datatype_injectivity("cm_control"));
}
PROOF static term cm_source_app_arg_from_right(
    term application, size_t offset) {
  for (size_t i = 0; i < offset; ++i) {
    application = dest_comb(application).tm1;
  }
  return dest_comb(application).tm2;
}
PROOF static void cm_source_close_trivial(const gnode leaf) {
  gnode current = CONV_TAC(leaf,
      reduce_rewrite_conv(THM_LIST(
        cm_error_task_def,
        get_datatype_injectivity("cm_control"),
        get_datatype_distinctness("cm_control"))));
  if (!IS_NULL(current->solved)) return;
  term wanted = goal_ccl(current->g);
  labeled_term_list assumptions = goal_lasmps(current->g);
  for (size_t i = 0; i < vector_size(assumptions); ++i) {
    thm direct = assume_rule(assumptions[i].tm);
    if (alpha_compare(concl(direct), wanted) == 0) {
      ACCEPT_TAC(current, direct);
      return;
    }
    thm normalized = conv_rule(
        reduce_rewrite_conv(THM_LIST(
          cm_error_task_def,
          get_datatype_injectivity("cm_control"),
          get_datatype_distinctness("cm_control"))),
        direct);
    if (alpha_compare(concl(normalized), wanted) == 0) {
      ACCEPT_TAC(current, normalized);
      return;
    }
    if (is_eq(concl(normalized)) &&
        alpha_compare(concl(sym_rule(normalized)), wanted) == 0) {
      ACCEPT_TAC(current, sym_rule(normalized));
      return;
    }
  }
  ACCEPT_TAC(current, taut_rule(wanted));
}



PROOF static thm cm_prove_error_task_step(void) {
  gnode root = gnode_new_with_ccl(
      `!(code:int) (task:cm_task).
         cm_error_task code task ==>
         cm_error_task code (cm_step task)`);
  gnode with_code = GEN_TAC(root, "code");
  gnode_list task_cases = INDUCT_TAC(with_code, `task:cm_task`);
  for (size_t i = 0; i < 5; ++i) {
    gnode leaf = AUTO_INTROS_TAC(task_cases[i]);
    thm impossible = conv_rule(
        reduce_rewrite_conv(THM_LIST(cm_error_task_def)),
        assume_rule(goal_lasmps(leaf->g)[0].tm));
    CONTR_TAC(leaf, impossible);
  }
  {
    gnode control_case = task_cases[5];
    gnode_list control_cases = INDUCT_TAC(
        control_case, `a2:cm_control`);
    for (size_t i = 0; i < vector_size(control_cases); ++i) {
      gnode branch = AUTO_INTROS_TAC(control_cases[i]);
      if (i != 5) {
        thm control_equal = conv_rule(
            rewrite_conv(THM_LIST(cm_error_task_def)),
            assume_rule(goal_lasmps(branch->g)[0].tm));
        thm kinds = ap_term_rule(`cm_control_kind`, control_equal);
        thm impossible = conv_rule(
            reduce_rewrite_conv(THM_LIST(
              get_cm_control_kind_def())), kinds);
        CONTR_TAC(branch, impossible);
        continue;
      }
      gnode_list stack_cases = DISJ_CASES_TAC(
          branch,
          ispec_rule(`a4:(cm_frame)list`,
            get_theorem_by_name("list_CASES")),
          "Hframes");
      gnode nil_reduced = CONV_WITH_ASMP_TAC(
          stack_cases[0], reduce_rewrite_conv,
          cm_error_step_rules());
      if (IS_NULL(nil_reduced->solved)) {
        cm_source_close_trivial(nil_reduced);
      }
      gnode cons = ASMP_EXISTS_TAC(
          stack_cases[1], "Hframes", NULL);
      cons = ASMP_EXISTS_TAC(cons, "Hframes", NULL);
      thm frames_cons = assume_rule(
          goal_lasmps(cons->g)[labeled_term_list_index(
            goal_lasmps(cons->g), "Hframes")].tm);
      term frame_head = cm_source_app_arg_from_right(
          rhs_of(frames_cons), 1);
      gnode_list frame_cases = INDUCT_TAC(cons, frame_head);
      for (size_t j = 0; j < vector_size(frame_cases); ++j) {
        gnode frame = AUTO_INTROS_TAC(frame_cases[j]);
        gnode reduced = CONV_WITH_ASMP_TAC(
            frame, reduce_rewrite_conv,
            cm_error_step_rules());
        if (IS_NULL(reduced->solved)) {
          cm_source_close_trivial(reduced);
        }
      }
    }
  }
  {
    gnode leaf = AUTO_INTROS_TAC(task_cases[6]);
    gnode reduced = CONV_WITH_ASMP_TAC(
        leaf, reduce_rewrite_conv, cm_error_step_rules());
    if (IS_NULL(reduced->solved)) {
      cm_source_close_trivial(reduced);
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_error_task_step = cm_prove_error_task_step();

PROOF thm cm_error_outcome_def = new_fun_definition(
    `cm_error_outcome (code:int) (out:cm_outcome) : bool =
       (cm_outcome_control out == CMError code)`);
PROOF static int _c_cm_error_outcome =
    cst_add_const_to_header(`cm_error_outcome`);

PROOF static thm cm_prove_error_exec(void) {
  term relation =
      `\task:cm_task out:cm_outcome.
         cm_error_task (code:int) task ==>
         cm_error_outcome code out`;
  gnode closed_root = gnode_new_with_ccl(
      mk_comb(`cm_exec_closed`, relation));
  gnode closed_open = CONV_TAC(closed_root,
      rewrite_conv(THM_LIST(get_cm_exec_closed_def())));
  gnode_list clauses = CONJ_TAC(closed_open);
  {
    gnode leaf = AUTO_INTROS_TAC(clauses[0]);
    gnode reduced = CONV_WITH_ASMP_TAC(
        leaf, reduce_rewrite_conv, THM_LIST(
          cm_error_task_def, cm_error_outcome_def,
          get_cm_outcome_control_def(),
          get_datatype_injectivity("cm_control")));
    if (IS_NULL(reduced->solved)) {
      cm_source_close_trivial(reduced);
    }
  }
  {
    gnode leaf = AUTO_INTROS_TAC(clauses[1]);
    thm premise = assume_rule(
        `cm_error_task (code:int) (cm_step (task:cm_task)) ==>
         cm_error_outcome code (out:cm_outcome)`);
    thm current = assume_rule(
        `cm_error_task (code:int) (task:cm_task)`);
    thm stepped = match_mp_rule(
        cm_error_task_step, current);
    ACCEPT_TAC(leaf, mp_rule(premise, stepped));
  }
  thm closed = gnode_prove(closed_root);

  term exec =
      `cm_exec (task:cm_task) (out:cm_outcome)`;
  term error =
      `cm_error_task (code:int) (task:cm_task)`;
  term target =
      `cm_error_outcome (code:int) (out:cm_outcome)`;
  term body = imp_chain(TERM_LIST(error, exec), target);
  gnode root = gnode_new_with_ccl(
      list_mk_forall(free_vars(body), body));
  gnode leaf = AUTO_INTROS_TAC(root);
  thm use = beta_norm(mp_rule(spec_rule(relation,
      conv_rule(rewrite_conv(THM_LIST(get_cm_exec_def())),
        assume_rule(exec))), closed));
  ACCEPT_TAC(leaf, mp_rule(use, assume_rule(error)));
  return gnode_prove(root);
}
PROOF thm cm_error_exec = cm_prove_error_exec();

PROOF static thm cm_prove_task_succeeds_step(void) {
  gnode root = gnode_new_with_ccl(
      `!(task:cm_task).
         ~(cm_task_done task) ==>
         cm_task_succeeds task ==>
         cm_task_succeeds (cm_step task)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm not_done = assume_rule(
      `~cm_task_done (task:cm_task)`);
  thm succeeds = conv_rule(
      rewrite_conv(THM_LIST(cm_task_succeeds_def)),
      assume_rule(`cm_task_succeeds (task:cm_task)`));
  thm body = assume_rule(
      `cm_exec (task:cm_task)
         (CMOutcome (st:cm_src_state) (ctl:cm_control)
           (status:int)) &&
       cm_success_control ctl`);
  thm tail = match_mp_rule(
      match_mp_rule(specl_rule(TERM_LIST(
        `task:cm_task`,
        `CMOutcome (st:cm_src_state) (ctl:cm_control)
          (status:int)`), get_cm_exec_step_inv()), not_done),
      conjunct1_rule(body));
  thm witness_body = conj_rule(tail, conjunct2_rule(body));
  thm witness = exists_rule(
      `?st0 ctl0 status0.
         cm_exec (cm_step (task:cm_task))
           (CMOutcome (st0:cm_src_state) (ctl0:cm_control)
             (status0:int)) &&
         cm_success_control ctl0`,
      `st:cm_src_state`, exists_rule(
        `?ctl0 status0.
           cm_exec (cm_step (task:cm_task))
             (CMOutcome (st:cm_src_state) (ctl0:cm_control)
               (status0:int)) &&
           cm_success_control ctl0`,
        `ctl:cm_control`, exists_rule(
          `?status0.
             cm_exec (cm_step (task:cm_task))
               (CMOutcome (st:cm_src_state) (ctl:cm_control)
                 (status0:int)) &&
             cm_success_control ctl`,
          `status:int`, witness_body)));
  thm no_status = choose_rule(`status:int`,
      assume_rule(
        `?status.
           cm_exec (task:cm_task)
             (CMOutcome (st:cm_src_state) (ctl:cm_control)
               (status:int)) &&
           cm_success_control ctl`),
      witness);
  thm no_control = choose_rule(`ctl:cm_control`,
      assume_rule(
        `?ctl status.
           cm_exec (task:cm_task)
             (CMOutcome (st:cm_src_state) (ctl:cm_control)
               (status:int)) &&
           cm_success_control ctl`),
      no_status);
  thm result = choose_rule(`st:cm_src_state`, succeeds, no_control);
  gnode reduced = CONV_TAC(leaf,
      rewrite_conv(THM_LIST(cm_task_succeeds_def)));
  ACCEPT_TAC(reduced, result);
  return gnode_prove(root);
}
PROOF thm cm_task_succeeds_step =
    cm_prove_task_succeeds_step();

PROOF static thm cm_prove_task_succeeds_not_error(void) {
  gnode root = gnode_new_with_ccl(
      `!(code:int) (task:cm_task).
         cm_task_succeeds task ==>
         ~cm_error_task code task`);
  gnode leaf = AUTO_INTROS_TAC(root);
  term error =
      `cm_error_task (code:int) (task:cm_task)`;
  thm succeeds = conv_rule(
      rewrite_conv(THM_LIST(cm_task_succeeds_def)),
      assume_rule(`cm_task_succeeds (task:cm_task)`));
  thm body = assume_rule(
      `cm_exec (task:cm_task)
         (CMOutcome (st:cm_src_state) (ctl:cm_control)
           (status:int)) &&
       cm_success_control ctl`);
  thm outcome_error = match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(
        `task:cm_task`, `code:int`,
        `CMOutcome (st:cm_src_state) (ctl:cm_control)
          (status:int)`), cm_error_exec),
      assume_rule(error)), conjunct1_rule(body));
  thm control_error = conv_rule(
      reduce_rewrite_conv(THM_LIST(
        cm_error_outcome_def, get_cm_outcome_control_def())),
      outcome_error);
  thm impossible = conv_rule(
      reduce_rewrite_conv(THM_LIST(
        get_cm_success_control_def(), get_cm_control_kind_def(),
        control_error)),
      conjunct2_rule(body));
  thm no_status = choose_rule(`status:int`,
      assume_rule(
        `?status.
           cm_exec (task:cm_task)
             (CMOutcome (st:cm_src_state) (ctl:cm_control)
               (status:int)) &&
           cm_success_control ctl`),
      impossible);
  thm no_control = choose_rule(`ctl:cm_control`,
      assume_rule(
        `?ctl status.
           cm_exec (task:cm_task)
             (CMOutcome (st:cm_src_state) (ctl:cm_control)
               (status:int)) &&
           cm_success_control ctl`),
      no_status);
  thm no_state = choose_rule(`st:cm_src_state`,
      succeeds, no_control);
  ACCEPT_TAC(leaf, no_state);
  return gnode_prove(root);
}
PROOF thm cm_task_succeeds_not_error =
    cm_prove_task_succeeds_not_error();
PROOF static thm cm_prove_done_succeeds(void) {
  gnode root = gnode_new_with_ccl(
      `!(st:cm_src_state) (ctl:cm_control) (status:int).
         cm_task_succeeds (CMDoneTask st ctl status) =
         cm_success_control ctl`);
  gnode_list opened = EQ_TAC(AUTO_INTROS_TAC(root));
  {
    gnode leaf = AUTO_INTROS_TAC(opened[0]);
    thm succeeds = conv_rule(
        rewrite_conv(THM_LIST(cm_task_succeeds_def)),
        assume_rule(
          `cm_task_succeeds
             (CMDoneTask (st:cm_src_state) (ctl:cm_control)
               (status:int))`));
    thm body = assume_rule(
        `cm_exec
           (CMDoneTask (st:cm_src_state) (ctl:cm_control)
             (status:int))
           (CMOutcome (st0:cm_src_state) (ctl0:cm_control)
             (status0:int)) &&
         cm_success_control ctl0`);
    thm same = match_mp_rule(match_mp_rule(
        specl_rule(TERM_LIST(
          `CMDoneTask (st:cm_src_state) (ctl:cm_control)
             (status:int)`,
          `CMOutcome (st0:cm_src_state) (ctl0:cm_control)
             (status0:int)`,
          `CMOutcome (st:cm_src_state) (ctl:cm_control)
             (status:int)`), get_cm_exec_deterministic()),
        conjunct1_rule(body)),
        specl_rule(TERM_LIST(
          `st:cm_src_state`, `ctl:cm_control`, `status:int`),
          get_cm_exec_done()));
    thm control_eq = conv_rule(
        reduce_rewrite_conv(THM_LIST(
          get_cm_outcome_control_def())),
        ap_term_rule(`cm_outcome_control`, same));
    thm result = conv_rule(
        rewrite_conv(THM_LIST(control_eq)),
        conjunct2_rule(body));
    thm no_status = choose_rule(`status0:int`,
        assume_rule(
          `?status0.
             cm_exec
               (CMDoneTask (st:cm_src_state) (ctl:cm_control)
                 (status:int))
               (CMOutcome (st0:cm_src_state) (ctl0:cm_control)
                 (status0:int)) &&
             cm_success_control ctl0`),
        result);
    thm no_control = choose_rule(`ctl0:cm_control`,
        assume_rule(
          `?ctl0 status0.
             cm_exec
               (CMDoneTask (st:cm_src_state) (ctl:cm_control)
                 (status:int))
               (CMOutcome (st0:cm_src_state) (ctl0:cm_control)
                 (status0:int)) &&
             cm_success_control ctl0`),
        no_status);
    ACCEPT_TAC(leaf,
        choose_rule(`st0:cm_src_state`, succeeds, no_control));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(opened[1]);
    thm body = conj_rule(
        specl_rule(TERM_LIST(
          `st:cm_src_state`, `ctl:cm_control`, `status:int`),
          get_cm_exec_done()),
        assume_rule(`cm_success_control (ctl:cm_control)`));
    thm witness = exists_rule(
        `?st0 ctl0 status0.
           cm_exec
             (CMDoneTask (st:cm_src_state) (ctl:cm_control)
               (status:int))
             (CMOutcome (st0:cm_src_state) (ctl0:cm_control)
               (status0:int)) &&
           cm_success_control ctl0`,
        `st:cm_src_state`, exists_rule(
          `?ctl0 status0.
             cm_exec
               (CMDoneTask (st:cm_src_state) (ctl:cm_control)
                 (status:int))
               (CMOutcome (st:cm_src_state) (ctl0:cm_control)
                 (status0:int)) &&
             cm_success_control ctl0`,
          `ctl:cm_control`, exists_rule(
            `?status0.
               cm_exec
                 (CMDoneTask (st:cm_src_state) (ctl:cm_control)
                   (status:int))
                 (CMOutcome (st:cm_src_state) (ctl:cm_control)
                   (status0:int)) &&
               cm_success_control ctl`,
            `status:int`, body)));
    gnode reduced = CONV_TAC(leaf,
        rewrite_conv(THM_LIST(cm_task_succeeds_def)));
    ACCEPT_TAC(reduced, witness);
  }
  return gnode_prove(root);
}
PROOF thm cm_done_succeeds = cm_prove_done_succeeds();

PROOF thm get_cm_error_exec(void) {
  return cm_error_exec;
}
PROOF thm get_cm_task_succeeds_step(void) {
  return cm_task_succeeds_step;
}
PROOF thm get_cm_done_succeeds(void) {
  return cm_done_succeeds;
}


PROOF static int cmc_preservation_source_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_source_axioms_before,
      "cmc_preservation_source introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_source_checks =
    cmc_preservation_source_final_checks();
