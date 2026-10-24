#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_type_source_c_struct.h"
#include "cmc_preservation_type_source_c_helpers.h"

#require "cmc_preservation_type_source_c_regular.c"

PROOF static size_t _cmc_preservation_type_source_c_struct_axioms_before =
    vector_size(get_all_axioms());

PROOF static thm cm_tcstruct_seq_normal(
    term old_phase, term second, thm ready, thm components,
    thm bounds, thm same_program, thm normal) {
  thm old_static = cm_tvs_pick_conjunct(components,
      `cm_phase_static_type_ready (p:cm_program) (fid:int)
        ${old_phase:cm_aphase}`);
  thm child_wf = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_phase_static_type_ready_def())), old_static);
  thm old_next = cm_tvs_trivial(
      `cm_phase_next_fid (fid:int) ${old_phase:cm_aphase} == fid`,
      THM_LIST(cm_phase_next_fid_def));
  term next_ann = cm_tcs_next_annotation(old_phase);
  thm cursor_equal = cm_tcs_cursor_fact(old_phase,
      `rest:(cm_acursor)list`, THM_LIST(same_program, normal));
  thm proved = specl_rule(TERM_LIST(
      `p:cm_program`, `q:cm_program`, `fid:int`, `control:cm_control`,
      second, `st:cm_src_state`, `st:cm_src_state`,
      `cm_phase_frame ${old_phase:cm_aphase} :: (ks:(cm_frame)list)`,
      `ks:(cm_frame)list`, old_phase, `pc:int`, `temp:int`,
      `breakpc:int`, `continuepc:int`, `parent_temp:int`,
      `parent_break:int`, `parent_continue:int`,
      `rest:(cm_acursor)list`, `spills:(cm_spill)list`,
      `saved:(cm_spill_frame)list`, `calls:(cm_call_sim_frame)list`,
      next_ann), cm_c_pop_s_task_ready);
  proved = conv_rule(rewrite_conv(THM_LIST(old_next)), proved);
  proved = mp_rule(proved, ready);
  proved = mp_rule(proved, conjunct1_rule(bounds));
  proved = mp_rule(proved, conjunct2_rule(bounds));
  proved = mp_rule(proved, child_wf);
  return mp_rule(proved, cursor_equal);
}

PROOF static thm cm_tcstruct_while_repeat(
    term old_phase, term guard, term loop_body, term env,
    term regions, term loop_start, term loop_end,
    thm ready, thm components, thm bounds, thm same_program,
    thm repeat) {
  term new_phase =
      `CAWhileGuardP ${guard:cm_expr} ${loop_body:cm_stmt}
        ${loop_start:int} ${loop_end:int}`;
  thm old_static = cm_tvs_pick_conjunct(components,
      `cm_phase_static_type_ready (p:cm_program) (fid:int)
        ${old_phase:cm_aphase}`);
  thm static_open = conv_rule(reduce_rewrite_conv(THM_LIST(
      get_cm_phase_static_type_ready_def())), old_static);
  thm guard_wf = cm_tvs_pick_conjunct(static_open,
      `cm_expr_wf (p:cm_program)
        (inth (fid:int) (cm_program_functions p)) ${guard:cm_expr}`);
  thm guard_scalar = cm_tvs_pick_conjunct(static_open,
      `cm_scalar_expr_type (cm_expr_type ${guard:cm_expr})`);
  thm body_wf = cm_tvs_pick_conjunct(static_open,
      `cm_stmt_wf (p:cm_program)
        (inth (fid:int) (cm_program_functions p)) T ${loop_body:cm_stmt}`);
  thm new_static = cm_tvs_trivial(
      `cm_phase_static_type_ready (p:cm_program) (fid:int)
        ${new_phase:cm_aphase}`,
      THM_LIST(get_cm_phase_static_type_ready_def(), guard_wf,
        guard_scalar, body_wf));
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
  thm new_input = cm_tvs_trivial(
      `cm_phase_input_type_ready (p:cm_program) (fid:int)
        ${new_phase:cm_aphase} (cm_expr_type ${guard:cm_expr})`,
      THM_LIST(get_cm_phase_input_type_ready_def(), guard_scalar));
  thm new_expr = cm_tvs_trivial(
      `cm_phase_expr_type_ready (p:cm_program) (fid:int)
        ${new_phase:cm_aphase} ${guard:cm_expr}`,
      THM_LIST(get_cm_phase_expr_type_ready_def(), guard_scalar));
  term next_ann = cm_tcs_next_annotation(old_phase);
  thm cursor_equal = cm_tcs_cursor_fact(old_phase,
      `CMACursor ${new_phase:cm_aphase} (parent_temp:int)
         (parent_break:int) (parent_continue:int) ::
       (rest:(cm_acursor)list)`, THM_LIST(same_program, repeat));
  thm proved = specl_rule(TERM_LIST(
      `p:cm_program`, `q:cm_program`, `fid:int`, `control:cm_control`,
      `st:cm_src_state`,
      `cm_restore_scope (st:cm_src_state) ${env:int->int->cm_value}
        ${regions:(cm_region)list}`,
      `cm_phase_frame ${old_phase:cm_aphase} :: (ks:(cm_frame)list)`,
      `CMWhileGuardK ${guard:cm_expr} ${loop_body:cm_stmt} ::
        (ks:(cm_frame)list)`,
      old_phase, new_phase, guard, `pc:int`, `temp:int`,
      `breakpc:int`, `continuepc:int`, `parent_temp:int`,
      `parent_break:int`, `parent_continue:int`,
      `rest:(cm_acursor)list`, `spills:(cm_spill)list`,
      `saved:(cm_spill_frame)list`, `calls:(cm_call_sim_frame)list`,
      next_ann), cm_c_replace_r_task_ready);
  thm_list premises = THM_LIST(ready, conjunct1_rule(bounds),
      conjunct2_rule(bounds), old_next, guard_wf, guard_scalar,
      new_static, new_parent, new_result, new_next, new_input,
      new_expr, cursor_equal);
  for (size_t i = 0; i < vector_size(premises); ++i) {
    proved = mp_rule(proved, premises[i]);
  }
  return proved;
}

PROOF static thm cm_prove_c_struct_type_ready_step(void) {
  term phase = `phase:cm_aphase`;
  term ann = cm_tvs_annotation(phase);
  term task = cm_tcs_task(phase);
  term body = imp_chain(TERM_LIST(
      `cm_phase_is_halt (phase:cm_aphase) ||
       (0i <= (fid:int) &&
        fid < ilength (cm_program_functions (p:cm_program)))`,
      `cm_task_type_ready p ${task:cm_task} ${ann:cm_annotation}`,
      `cm_c_phase_family (phase:cm_aphase) == 1i ||
       cm_c_phase_family phase == 2i`),
      `cm_task_type_ready (p:cm_program)
        (cm_step ${task:cm_task})
        (cm_update_annotation
          (cm_annotation_step ${task:cm_task}
            ${ann:cm_annotation}))`);
  gnode root = gnode_new_with_ccl(list_mk_forall(free_vars(body), body));
  gnode introduced = cm_tcs_nonexit_branch(AUTO_INTROS_TAC(root));
  thm generic_ready = assume_rule(
      `cm_task_type_ready (p:cm_program) ${task:cm_task}
        ${ann:cm_annotation}`);
  thm family = assume_rule(
      `cm_c_phase_family (phase:cm_aphase) == 1i ||
       cm_c_phase_family phase == 2i`);
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
    if (i != 16 && i != 19) {
      thm impossible = conv_rule(reduce_rewrite_conv(THM_LIST(
          shape, get_cm_c_phase_family_def())), family);
      CONTR_TAC(cases[i], impossible);
      continue;
    }
    thm ready = conv_rule(rewrite_conv(THM_LIST(shape)), generic_ready);
    thm components = cm_tcs_components(concrete_phase, ready);
    thm same_program = cm_tvs_pick_conjunct(components,
        `(q:cm_program) == (p:cm_program)`);
    thm old_control = cm_tvs_pick_conjunct(components,
        `cm_control_type_ready (p:cm_program) (fid:int)
          (control:cm_control)`);
    thm old_next = cm_tvs_trivial(
        `cm_phase_next_fid (fid:int) ${concrete_phase:cm_aphase} == fid`,
        THM_LIST(cm_phase_next_fid_def));
    thm next_control_view = beta_norm(ap_term_rule(
        `\next_fid:int.
           cm_control_type_ready (p:cm_program) next_fid
             (control:cm_control)`, old_next));
    thm next_control = eq_mp_rule(sym_rule(next_control_view),
        old_control);
    thm bounds = conv_rule(reduce_rewrite_conv(THM_LIST(
        shape, cm_phase_is_halt_def)), assume_rule(
        `cm_phase_is_halt (phase:cm_aphase) ||
         (0i <= (fid:int) &&
          fid < ilength (cm_program_functions (p:cm_program)))`));
    if (i == 16) {
      term second = cm_tvs_phase_arg(concrete_phase, 1, 0);
      term normal_condition =
          `cm_control_kind (control:cm_control) == 0i`;
      gnode_list control_cases = BOOL_CASES_TAC(
          cases[i], normal_condition, "Hnormal");
      {
        thm normal = assume_rule(normal_condition);
        thm proved = cm_tcstruct_seq_normal(concrete_phase, second,
            ready, components, bounds, same_program, normal);
        cm_tcs_accept(control_cases[0], proved, shape,
            THM_LIST(same_program, normal));
      }
      {
        thm not_normal = assume_rule(mk_not(normal_condition));
        thm proved = cm_tcs_pop_control(concrete_phase,
            `control:cm_control`, `st:cm_src_state`, ready,
            next_control, THM_LIST(same_program, not_normal));
        cm_tcs_accept(control_cases[1], proved, shape,
            THM_LIST(same_program, not_normal));
      }
      continue;
    }
    term guard = cm_tvs_phase_arg(concrete_phase, 6, 0);
    term loop_body = cm_tvs_phase_arg(concrete_phase, 6, 1);
    term env = cm_tvs_phase_arg(concrete_phase, 6, 2);
    term regions = cm_tvs_phase_arg(concrete_phase, 6, 3);
    term loop_start = cm_tvs_phase_arg(concrete_phase, 6, 4);
    term loop_end = cm_tvs_phase_arg(concrete_phase, 6, 5);
    term repeat_condition =
        `cm_control_kind (control:cm_control) == 0i ||
         cm_control_kind control == 2i`;
    term loop_normal = `cm_control_kind (control:cm_control) == 0i`;
    gnode_list normal_cases = BOOL_CASES_TAC(
        cases[i], loop_normal, "Hloop_normal");
    {
      thm is_normal = assume_rule(loop_normal);
      thm repeat = mp_rule(taut_rule(
          mk_imp(concl(is_normal), repeat_condition)), is_normal);
      thm proved = cm_tcstruct_while_repeat(concrete_phase,
          guard, loop_body, env, regions, loop_start, loop_end,
          ready, components, bounds, same_program, repeat);
      cm_tcs_accept(normal_cases[0], proved, shape,
          THM_LIST(same_program, is_normal, repeat));
    }
    {
      thm not_normal = assume_rule(mk_not(loop_normal));
      term loop_continue =
          `cm_control_kind (control:cm_control) == 2i`;
      gnode_list continue_cases = BOOL_CASES_TAC(
          normal_cases[1], loop_continue, "Hloop_continue");
      {
        thm is_continue = assume_rule(loop_continue);
        thm repeat = mp_rule(taut_rule(
            mk_imp(concl(is_continue), repeat_condition)), is_continue);
        thm proved = cm_tcstruct_while_repeat(concrete_phase,
            guard, loop_body, env, regions, loop_start, loop_end,
            ready, components, bounds, same_program, repeat);
        cm_tcs_accept(continue_cases[0], proved, shape,
            THM_LIST(same_program, not_normal, is_continue, repeat));
      }
      {
        thm not_continue = assume_rule(mk_not(loop_continue));
        thm not_repeat = taut_rule(imp_chain(TERM_LIST(
            concl(not_normal), concl(not_continue)),
            mk_not(repeat_condition)));
        not_repeat = mp_rule(not_repeat, not_normal);
        not_repeat = mp_rule(not_repeat, not_continue);
        term break_condition =
            `cm_control_kind (control:cm_control) == 1i`;
        gnode_list break_cases = BOOL_CASES_TAC(
            continue_cases[1], break_condition, "Hbreak");
        {
          thm is_break = assume_rule(break_condition);
          thm normal_ready = cm_tvs_trivial(
              `cm_control_type_ready (p:cm_program)
                (cm_phase_next_fid (fid:int)
                  ${concrete_phase:cm_aphase}) CMNormal`,
              THM_LIST(get_cm_control_type_ready_def(),
                cm_phase_next_fid_def));
          thm proved = cm_tcs_pop_control(concrete_phase, `CMNormal`,
              `cm_restore_scope (st:cm_src_state)
                ${env:int->int->cm_value} ${regions:(cm_region)list}`,
              ready, normal_ready,
              THM_LIST(same_program, not_repeat, is_break));
          cm_tcs_accept(break_cases[0], proved, shape,
              THM_LIST(same_program, not_normal, not_continue,
                not_repeat, is_break));
        }
        {
          thm not_break = assume_rule(mk_not(break_condition));
          thm proved = cm_tcs_pop_control(concrete_phase,
              `control:cm_control`,
              `cm_restore_scope (st:cm_src_state)
                ${env:int->int->cm_value} ${regions:(cm_region)list}`,
              ready, next_control,
              THM_LIST(same_program, not_repeat, not_break));
          cm_tcs_accept(break_cases[1], proved, shape,
              THM_LIST(same_program, not_normal, not_continue,
                not_repeat, not_break));
        }
      }
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_c_struct_type_ready_step =
    cm_prove_c_struct_type_ready_step();

PROOF static int cmc_preservation_type_source_c_struct_final_checks(void) {
  ENSURE_COND(vector_size(hyp(cm_c_struct_type_ready_step)) == 0,
      "structured control type theorem has assumptions");
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_type_source_c_struct_axioms_before,
      "structured control type proof introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_type_source_c_struct_checks =
    cmc_preservation_type_source_c_struct_final_checks();
