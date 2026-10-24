#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_type_source_v_control.h"
#include "cmc_preservation_type_source_v_helpers.h"

#require "cmc_preservation_type_source_v_pointer.c"

PROOF static size_t _cmc_preservation_type_source_v_control_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_tvctl_replace_statement(
    term old_phase, term new_phase, term child, term next_frame,
    thm ready, thm components, thm bounds, thm child_wf,
    thm new_static, thm_list extra) {
  thm new_parent = cm_tvs_trivial(
      `cm_phase_parent_type_ready (p:cm_program) (fid:int)
        ${new_phase:cm_aphase} (rest:(cm_acursor)list)`,
      THM_LIST(get_cm_phase_parent_type_ready_def()));
  thm new_result = cm_tvs_trivial(
      `cm_phase_result_type_ready (p:cm_program) (fid:int)
        ${new_phase:cm_aphase} (rest:(cm_acursor)list)`,
      THM_LIST(get_cm_phase_result_type_ready_def(),
        get_cm_phase_result_type_def()));
  thm old_next = cm_tvs_trivial(
      `cm_phase_next_fid (fid:int) ${old_phase:cm_aphase} == fid`,
      THM_LIST(cm_phase_next_fid_def));
  thm new_next = cm_tvs_trivial(
      `cm_phase_next_fid (fid:int) ${new_phase:cm_aphase} == fid`,
      THM_LIST(cm_phase_next_fid_def));
  term next_ann = cm_tvs_next_annotation(old_phase);
  thm cursor_equal = cm_tvs_cursor_fact(old_phase,
      `CMACursor ${new_phase:cm_aphase} (parent_temp:int)
         (parent_break:int) (parent_continue:int) ::
       (rest:(cm_acursor)list)`, extra);
  thm proved = specl_rule(TERM_LIST(
      `p:cm_program`, `q:cm_program`, `fid:int`,
      `incoming:cm_value`, `st:cm_src_state`, `st:cm_src_state`,
      `cm_phase_frame ${old_phase:cm_aphase} :: (ks:(cm_frame)list)`,
      `${next_frame:cm_frame} :: (ks:(cm_frame)list)`,
      old_phase, new_phase, child, `pc:int`, `temp:int`,
      `breakpc:int`, `continuepc:int`, `parent_temp:int`,
      `parent_break:int`, `parent_continue:int`,
      `rest:(cm_acursor)list`, `spills:(cm_spill)list`,
      `saved:(cm_spill_frame)list`, `calls:(cm_call_sim_frame)list`,
      next_ann), cm_v_replace_s_task_ready);
  thm_list premises = THM_LIST(ready, conjunct1_rule(bounds),
      conjunct2_rule(bounds), old_next, child_wf, new_static,
      new_parent, new_result, new_next, cursor_equal);
  for (size_t i = 0; i < vector_size(premises); ++i) {
    proved = mp_rule(proved, premises[i]);
  }
  return proved;
}

PROOF static thm cm_prove_v_control_type_ready_step(void) {
  term phase = `phase:cm_aphase`;
  term ann = cm_tvs_annotation(phase);
  term task = cm_tvs_task(phase);
  term body = imp_chain(TERM_LIST(
      `cm_phase_is_halt (phase:cm_aphase) ||
       (0i <= (fid:int) &&
        fid < ilength (cm_program_functions (p:cm_program)))`,
      `cm_task_type_ready (p:cm_program) ${task:cm_task}
        ${ann:cm_annotation}`,
      `cm_v_phase_family (phase:cm_aphase) == 3i`),
      `cm_task_type_ready (p:cm_program)
        (cm_step ${task:cm_task})
        (cm_update_annotation
          (cm_annotation_step ${task:cm_task}
            ${ann:cm_annotation}))`);
  gnode root = gnode_new_with_ccl(list_mk_forall(free_vars(body), body));
  gnode introduced = AUTO_INTROS_TAC(root);
  thm generic_ready = assume_rule(
      `cm_task_type_ready (p:cm_program) ${task:cm_task}
        ${ann:cm_annotation}`);
  thm family = assume_rule(
      `cm_v_phase_family (phase:cm_aphase) == 3i`);
  gnode_list cases = DISJ_CASES_TAC(introduced,
      ispec_rule(phase, get_datatype_cases("cm_aphase")), "Hphase");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    while (true) {
      labeled_term_list assumptions = goal_lasmps(cases[i]->g);
      int shape_index = labeled_term_list_index(assumptions, "Hphase");
      if (!is_exists(assumptions[shape_index].tm)) break;
      cases[i] = ASMP_EXISTS_TAC(cases[i], "Hphase", NULL);
    }
    thm shape = assume_rule(goal_lasmps(cases[i]->g)[
        labeled_term_list_index(goal_lasmps(cases[i]->g), "Hphase")].tm);
    term concrete_phase = rhs_of(shape);
    thm ready = conv_rule(rewrite_conv(THM_LIST(shape)), generic_ready);
    thm components = cm_tvs_components(concrete_phase, ready);
    thm same_program = cm_tvs_pick_conjunct(components,
        `(q:cm_program) == (p:cm_program)`);
    if (i != 17 && i != 18) {
      thm impossible = conv_rule(reduce_rewrite_conv(THM_LIST(
          shape, get_cm_v_phase_family_def())), family);
      CONTR_TAC(cases[i], impossible);
      continue;
    }
    thm bounds = conv_rule(reduce_rewrite_conv(THM_LIST(
        shape, cm_phase_is_halt_def)), assume_rule(
        `cm_phase_is_halt (phase:cm_aphase) ||
         (0i <= (fid:int) &&
          fid < ilength (cm_program_functions (p:cm_program)))`));
    thm old_static = cm_tvs_pick_conjunct(components,
        `cm_phase_static_type_ready (p:cm_program) (fid:int)
          ${concrete_phase:cm_aphase}`);
    thm static_open = conv_rule(reduce_rewrite_conv(THM_LIST(
        get_cm_phase_static_type_ready_def())), old_static);
    term condition = `cm_truth (st:cm_src_state) (incoming:cm_value)`;
    gnode_list condition_cases = BOOL_CASES_TAC(
        cases[i], condition, "Htruth");
    if (i == 17) {
      term yes = cm_tvs_phase_arg(concrete_phase, 2, 0);
      term no = cm_tvs_phase_arg(concrete_phase, 2, 1);
      thm yes_wf = cm_tvs_pick_conjunct(static_open,
          `cm_stmt_wf (p:cm_program)
            (inth (fid:int) (cm_program_functions p)) T ${yes:cm_stmt}`);
      thm no_wf = cm_tvs_pick_conjunct(static_open,
          `cm_stmt_wf (p:cm_program)
            (inth (fid:int) (cm_program_functions p)) T ${no:cm_stmt}`);
      {
        thm truth = assume_rule(condition);
        term new_phase =
            `CABlockP (cm_state_env (st:cm_src_state))
              (cm_state_regions st) T
              ((pc:int) + 2i +
               cm_stmt_code_count (p:cm_program) (fid:int) ${yes:cm_stmt} +
               cm_stmt_code_count p fid ${no:cm_stmt})`;
        thm new_static = cm_tvs_trivial(
            `cm_phase_static_type_ready (p:cm_program) (fid:int)
              ${new_phase:cm_aphase}`,
            THM_LIST(get_cm_phase_static_type_ready_def()));
        thm proved = cm_tvctl_replace_statement(concrete_phase,
            new_phase, yes,
            `CMBlockK (cm_state_env (st:cm_src_state))
              (cm_state_regions st)`,
            ready, components, bounds, yes_wf, new_static,
            THM_LIST(same_program, truth));
        cm_tvs_accept(condition_cases[0], proved, shape,
            THM_LIST(same_program, truth));
      }
      {
        thm not_truth = assume_rule(mk_not(condition));
        term new_phase =
            `CABlockP (cm_state_env (st:cm_src_state))
              (cm_state_regions st) F
              ((pc:int) + 2i +
               cm_stmt_code_count (p:cm_program) (fid:int) ${yes:cm_stmt} +
               cm_stmt_code_count p fid ${no:cm_stmt})`;
        thm new_static = cm_tvs_trivial(
            `cm_phase_static_type_ready (p:cm_program) (fid:int)
              ${new_phase:cm_aphase}`,
            THM_LIST(get_cm_phase_static_type_ready_def()));
        thm proved = cm_tvctl_replace_statement(concrete_phase,
            new_phase, no,
            `CMBlockK (cm_state_env (st:cm_src_state))
              (cm_state_regions st)`,
            ready, components, bounds, no_wf, new_static,
            THM_LIST(same_program, not_truth));
        cm_tvs_accept(condition_cases[1], proved, shape,
            THM_LIST(same_program, not_truth));
      }
      continue;
    }
    term guard = cm_tvs_phase_arg(concrete_phase, 4, 0);
    term loop_body = cm_tvs_phase_arg(concrete_phase, 4, 1);
    term loop_start = cm_tvs_phase_arg(concrete_phase, 4, 2);
    term loop_end = cm_tvs_phase_arg(concrete_phase, 4, 3);
    thm body_wf = cm_tvs_pick_conjunct(static_open,
        `cm_stmt_wf (p:cm_program)
          (inth (fid:int) (cm_program_functions p)) T ${loop_body:cm_stmt}`);
    {
      thm truth = assume_rule(condition);
      term new_phase =
          `CAWhileBodyP ${guard:cm_expr} ${loop_body:cm_stmt}
            (cm_state_env (st:cm_src_state)) (cm_state_regions st)
            ${loop_start:int} ${loop_end:int}`;
      thm new_static = cm_tvs_trivial(
          `cm_phase_static_type_ready (p:cm_program) (fid:int)
            ${new_phase:cm_aphase}`,
          THM_LIST(get_cm_phase_static_type_ready_def(), static_open));
      thm proved = cm_tvctl_replace_statement(concrete_phase,
          new_phase, loop_body,
          `CMWhileBodyK ${guard:cm_expr} ${loop_body:cm_stmt}
            (cm_state_env (st:cm_src_state)) (cm_state_regions st)`,
          ready, components, bounds, body_wf, new_static,
          THM_LIST(same_program, truth));
      cm_tvs_accept(condition_cases[0], proved, shape,
          THM_LIST(same_program, truth));
    }
    {
      thm not_truth = assume_rule(mk_not(condition));
      thm control_ready = cm_tvs_trivial(
          `cm_control_type_ready (p:cm_program)
            (cm_phase_next_fid (fid:int) ${concrete_phase:cm_aphase})
            CMNormal`,
          THM_LIST(get_cm_control_type_ready_def(), cm_phase_next_fid_def));
      thm proved = cm_tvs_pop_control(concrete_phase, `CMNormal`,
          `st:cm_src_state`, ready, control_ready,
          THM_LIST(same_program, not_truth));
      cm_tvs_accept(condition_cases[1], proved, shape,
          THM_LIST(same_program, not_truth));
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_v_control_type_ready_step =
    cm_prove_v_control_type_ready_step();

PROOF static int cmc_preservation_type_source_v_control_final_checks(void) {
  ENSURE_COND(vector_size(hyp(cm_v_control_type_ready_step)) == 0,
      "control value type theorem has assumptions");
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_type_source_v_control_axioms_before,
      "control value type proof introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_type_source_v_control_checks =
    cmc_preservation_type_source_v_control_final_checks();
