#include "proof/proof.h"
#include "userlib/proof.h"
#include "cmc_preservation_code_control.h"
#include "cmc_codegen.h"
#include "cmc_annotate_model.h"
#include "cmc_lang.h"
#include "cmc_sim.h"
#include "cmc_preservation_layout.h"
#include "cmc_preservation_code_expr.h"
#include "cmc_preservation_code_stmt.h"

#require "cmc_preservation_code_control.c"

PROOF size_t _cmc_preservation_code_task_axioms_before =
    vector_size(get_all_axioms());

PROOF thm cm_task_layout_ready_def = new_rec_definition(
    get_cm_task_recursion(),
    `(!p q input ann.
        cm_task_layout_ready (p:cm_program)
          (CMStartTask (q:cm_program) (input:(int)list))
          (ann:cm_annotation) =
        (q == p && ann == cm_initial_annotation &&
         cm_call_ok p (cm_program_main p) []
           (cm_initial_state p input))) &&
     (!p q fid expr st ks ann.
        cm_task_layout_ready p
          (CMRTask (q:cm_program) (fid:int) (expr:cm_expr)
            (st:cm_src_state) (ks:(cm_frame)list)) ann =
        (q == p && cm_r_layout_ready p fid expr st ks ann)) &&
     (!p q fid expr st ks ann.
        cm_task_layout_ready p
          (CMLTask (q:cm_program) (fid:int) (expr:cm_expr)
            (st:cm_src_state) (ks:(cm_frame)list)) ann =
        (q == p && cm_l_layout_ready p fid expr st)) &&
     (!p q fid stmt st ks ann.
        cm_task_layout_ready p
          (CMSTask (q:cm_program) (fid:int) (stmt:cm_stmt)
            (st:cm_src_state) (ks:(cm_frame)list)) ann =
        (q == p && cm_stmt_start_safe p fid stmt)) &&
     (!p q fid value st ks ann.
        cm_task_layout_ready p
          (CMVTask (q:cm_program) (fid:int) (value:cm_value)
            (st:cm_src_state) (ks:(cm_frame)list)) ann =
        (q == p && cm_v_layout_ready p value st ann)) &&
     (!p q fid ctl st ks ann.
        cm_task_layout_ready p
          (CMCTask (q:cm_program) (fid:int) (ctl:cm_control)
            (st:cm_src_state) (ks:(cm_frame)list)) ann =
        (q == p && cm_c_layout_ready p fid ctl ann)) &&
     (!p st ctl status ann.
        cm_task_layout_ready (p:cm_program)
          (CMDoneTask (st:cm_src_state) (ctl:cm_control)
            (status:int)) (ann:cm_annotation) = T)`);
PROOF static int _c_cm_task_layout_ready =
    cst_add_const_to_header(`cm_task_layout_ready`);

PROOF static thm_list cm_task_start_layout_rules(void) {
  thm_list rules = cm_v_layout_rules();
  vector_add(&rules, get_cm_begin_call_def());
  vector_add(&rules, cm_call_body_pc_def);
  vector_add(&rules, cm_ann_enter_call_def);
  vector_add(&rules, cm_call_sim_base_def);
  vector_add(&rules, cm_call_sim_saved_def);
  vector_add(&rules, cm_call_sim_return_def);
  vector_add(&rules, cm_initial_annotation_def);
  vector_add(&rules, cm_entry_steps_def);
  vector_add(&rules, get_cm_emit_prelude_def());
  vector_add(&rules, cm_status_tail_code_def);
  vector_add(&rules, cm_fallthrough_tail_code_def);
  vector_add(&rules, get_cm_char_normalize_code_def());
  vector_add(&rules, get_theorem_by_name("APPEND"));
  vector_add(&rules, get_cm_call_depth_def());
  vector_add(&rules, get_cm_is_call_frame_def());
  vector_add(&rules, get_theorem_by_name("ILENGTH_DEF"));
  return rules;
}

PROOF static thm cm_prove_start_task_layout_step(void) {
  term call_ok =
      `cm_call_ok (p:cm_program) (cm_program_main p)
        ([]:(cm_value)list) (cm_initial_state p (input:(int)list))`;
  term task =
      `CMStartTask (p:cm_program) (input:(int)list)`;
  term target =
      `cm_task_layout (p:cm_program) (cm_step ${task:cm_task})
        (cm_update_annotation
          (cm_annotation_step ${task:cm_task}
            cm_initial_annotation))`;
  term body = mk_imp(call_ok, target);
  gnode root = gnode_new_with_ccl(
      list_mk_forall(free_vars(body), body));
  gnode leaf = AUTO_INTROS_TAC(root);
  thm call_ok_fact = assume_rule(call_ok);
  thm opened_ok = conv_rule(
      reduce_rewrite_conv(THM_LIST(get_cm_call_ok_def())),
      call_ok_fact);
  thm bounds = conj_rule(
      conjunct1_rule(opened_ok),
      conjunct1_rule(conjunct2_rule(opened_ok)));
  thm body_at = mp_rule(specl_rule(TERM_LIST(
      `p:cm_program`, `cm_program_main (p:cm_program)`),
      cm_model_function_body_tail_at), bounds);

  term prefix =
      `[TVMInst TVMPushOp 1048576i;
        TVMInst TVMPushOp 8i; TVMInst TVMStoreOp 0i;
        TVMInst TVMCallOp
          (cm_function_pc (p:cm_program) (cm_program_main p))]:
       (tvm_inst)list`;
  thm return_rule = ispecl_rule(TERM_LIST(
      `cm_model_code (p:cm_program)`, `0i:int`, prefix,
      `cm_status_tail_code:(tvm_inst)list`),
      cm_code_at_append_right);
  thm_list prelude_rules = cm_task_start_layout_rules();
  thm normalized_prelude = conv_rule(
      reduce_rewrite_conv(prelude_rules),
      spec_rule(`p:cm_program`, cm_model_prelude_at));
  thm return_at = mp_rule(
      conv_rule(reduce_rewrite_conv(prelude_rules), return_rule),
      normalized_prelude);

  thm_list rules = cm_task_start_layout_rules();
  vector_add(&rules, call_ok_fact);
  thm normalized_body = conv_rule(
      reduce_rewrite_conv(rules), body_at);
  thm normalized_return = conv_rule(
      reduce_rewrite_conv(rules), return_at);
  gnode reduced = CONV_TAC(leaf, reduce_rewrite_conv(rules));
  reduced = CONV_TAC(reduced, reduce_rewrite_conv(rules));
  thm facts = conj_rule(normalized_body, normalized_return);
  thm implication = taut_rule(
      mk_imp(concl(facts), goal_ccl(reduced->g)));
  ACCEPT_TAC(reduced, mp_rule(implication, facts));
  return gnode_prove(root);
}
PROOF thm cm_start_task_layout_step =
    cm_prove_start_task_layout_step();

PROOF static thm cm_prove_done_task_layout_step(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (st:cm_src_state) (ctl:cm_control)
         (status:int) (ann:cm_annotation).
         cm_task_layout p (CMDoneTask st ctl status) ann ==>
         cm_task_layout p
           (cm_step (CMDoneTask st ctl status))
           (cm_update_annotation
             (cm_annotation_step
               (CMDoneTask st ctl status) ann))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm_list rules = cm_v_layout_rules();
  term next_task =
      `cm_step (CMDoneTask (st:cm_src_state)
        (ctl:cm_control) (status:int))`;
  term next_annotation =
      `cm_update_annotation
        (cm_annotation_step
          (CMDoneTask (st:cm_src_state)
            (ctl:cm_control) (status:int))
          (ann:cm_annotation))`;
  thm task_shape = apply_conversion(
      reduce_rewrite_conv(rules), next_task);
  thm annotation_shape = apply_conversion(
      reduce_rewrite_conv(rules), next_annotation);
  gnode reduced = CONV_TAC(leaf, rewrite_conv(THM_LIST(
      task_shape, annotation_shape)));
  ACCEPT_TAC(reduced, specl_rule(TERM_LIST(
      `p:cm_program`, `st:cm_src_state`, `ctl:cm_control`,
      `status:int`, rhs_of(annotation_shape)),
      get_cm_task_layout_done()));
  return gnode_prove(root);
}
PROOF thm cm_done_task_layout_step =
    cm_prove_done_task_layout_step();

PROOF static thm cm_prove_task_layout_step(void) {
  term erases =
      `cm_annotation_erases (task:cm_task)
        (ann:cm_annotation)`;
  term ready =
      `cm_task_layout_ready (p:cm_program)
        (task:cm_task) (ann:cm_annotation)`;
  term old_layout =
      `cm_task_layout (p:cm_program)
        (task:cm_task) (ann:cm_annotation)`;
  term target =
      `cm_task_layout (p:cm_program) (cm_step (task:cm_task))
        (cm_update_annotation
          (cm_annotation_step (task:cm_task)
            (ann:cm_annotation)))`;
  term body = imp_chain(
      TERM_LIST(erases, ready, old_layout), target);
  gnode root = gnode_new_with_ccl(
      list_mk_forall(free_vars(body), body));
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list cases = DISJ_CASES_TAC(
      introduced,
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
        goal_lasmps(branch->g)[
          labeled_term_list_index(
            goal_lasmps(branch->g), "Htask")].tm);
    thm opened_ready = conv_rule(
        reduce_rewrite_conv(
          THM_LIST(task_shape, cm_task_layout_ready_def)),
        assume_rule(ready));
    thm shaped_layout = conv_rule(
        rewrite_conv(THM_LIST(task_shape)),
        assume_rule(old_layout));
    thm shaped_erases = conv_rule(
        rewrite_conv(THM_LIST(task_shape)),
        assume_rule(erases));
    thm_list shapes = THM_LIST(task_shape);
    thm result = empty_theorem;

    if (i == 0) {
      thm program_eq = conjunct1_rule(opened_ready);
      thm annotation_eq =
          conjunct1_rule(conjunct2_rule(opened_ready));
      thm call_ok =
          conjunct2_rule(conjunct2_rule(opened_ready));
      result = match_mp_rule(cm_start_task_layout_step, call_ok);
      vector_add(&shapes, program_eq);
      vector_add(&shapes, annotation_eq);
    } else if (i == 1) {
      thm program_eq = conjunct1_rule(opened_ready);
      thm r_ready = conjunct2_rule(opened_ready);
      shaped_layout = conv_rule(
          rewrite_conv(THM_LIST(program_eq)), shaped_layout);
      result = match_mp_rule(
          get_cm_r_task_layout_step(), r_ready);
      result = match_mp_rule(result, shaped_layout);
      vector_add(&shapes, program_eq);
    } else if (i == 2) {
      thm program_eq = conjunct1_rule(opened_ready);
      thm lvalue = conjunct2_rule(opened_ready);
      shaped_layout = conv_rule(
          rewrite_conv(THM_LIST(program_eq)), shaped_layout);
      result = match_mp_rule(
          get_cm_l_task_layout_step(), lvalue);
      result = match_mp_rule(result, shaped_layout);
      vector_add(&shapes, program_eq);
    } else if (i == 3) {
      thm program_eq = conjunct1_rule(opened_ready);
      thm stmt_ready = conjunct2_rule(opened_ready);
      shaped_layout = conv_rule(
          rewrite_conv(THM_LIST(program_eq)), shaped_layout);
      result = match_mp_rule(
          get_cm_s_task_layout_step(), stmt_ready);
      result = match_mp_rule(result, shaped_layout);
      vector_add(&shapes, program_eq);
    } else if (i == 4) {
      thm program_eq = conjunct1_rule(opened_ready);
      thm v_ready = conjunct2_rule(opened_ready);
      shaped_layout = conv_rule(
          rewrite_conv(THM_LIST(program_eq)), shaped_layout);
      shaped_erases = conv_rule(
          rewrite_conv(THM_LIST(program_eq)), shaped_erases);
      result = match_mp_rule(
          get_cm_v_task_layout_step(), shaped_erases);
      result = match_mp_rule(result, v_ready);
      result = match_mp_rule(result, shaped_layout);
      vector_add(&shapes, program_eq);
    } else if (i == 5) {
      thm program_eq = conjunct1_rule(opened_ready);
      thm c_ready = conjunct2_rule(opened_ready);
      shaped_layout = conv_rule(
          rewrite_conv(THM_LIST(program_eq)), shaped_layout);
      shaped_erases = conv_rule(
          rewrite_conv(THM_LIST(program_eq)), shaped_erases);
      result = match_mp_rule(
          get_cm_c_task_layout_step(), shaped_erases);
      result = match_mp_rule(result, c_ready);
      result = match_mp_rule(result, shaped_layout);
      vector_add(&shapes, program_eq);
    } else {
      result = match_mp_rule(
          cm_done_task_layout_step, shaped_layout);
    }
    result = conv_rule(rewrite_conv(shapes), result);
    gnode reduced = CONV_TAC(branch, rewrite_conv(shapes));
    ACCEPT_TAC(reduced, result);
  }
  return gnode_prove(root);
}
PROOF thm cm_task_layout_step =
    cm_prove_task_layout_step();

PROOF thm get_cm_task_layout_step(void) {
  return cm_task_layout_step;
}

PROOF static int cmc_preservation_code_task_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_code_task_axioms_before,
      "cmc_preservation_code_task introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_code_task_checks =
    cmc_preservation_code_task_final_checks();
