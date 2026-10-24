#include "proof/proof.h"
#include "userlib/proof.h"
#include "cmc_annotate_model.h"
#include "cmc_preservation_code_value_call.h"

#require "cmc_preservation_code_value_call.c"

PROOF size_t _cmc_preservation_code_value_total_axioms_before =
    vector_size(get_all_axioms());

PROOF static term cm_v_phase_annotation_term(void) {
  return `CMAnnotation (pc:int) (temp:int) (breakpc:int)
      (continuepc:int)
      (CMACursor (phase:cm_aphase) (owner:int)
        (saved_break:int) (saved_continue:int) ::
       (rest:(cm_acursor)list))
      (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
      (calls:(cm_call_sim_frame)list)`;
}

PROOF static term cm_v_phase_task_term(void) {
  return `CMVTask (p:cm_program) (fid:int) (v:cm_value)
      (st:cm_src_state)
      (cm_phase_frame (phase:cm_aphase) ::
       cm_cursor_frames (rest:(cm_acursor)list))`;
}

PROOF static thm_list cm_v_phase_shape_rules(const thm shape) {
  return THM_LIST(shape, cm_phase_frame_def,
      cm_cursor_phase_def, cm_cursor_temp_def,
      cm_cursor_break_def, cm_cursor_continue_def,
      cm_cursor_frames_def,
      get_theorem_by_name("HD"), get_theorem_by_name("TL"),
      get_theorem_by_name("NOT_CONS_NIL"));
}

PROOF static thm cm_v_open_phase_ready(
    const thm ready, const thm shape,
    const thm_list extra_rules) {
  thm_list rules = THM_LIST(shape, cm_v_phase_ready_def,
      cm_ann_temp_def, cm_ann_cursors_def,
      cm_cursor_phase_def, cm_cursor_temp_def,
      get_theorem_by_name("HD"), get_theorem_by_name("TL"),
      get_theorem_by_name("NOT_CONS_NIL"));
  for (size_t i = 0; i < vector_size(extra_rules); ++i) {
    vector_add(&rules, extra_rules[i]);
  }
  return conv_rule(reduce_rewrite_conv(rules), ready);
}

PROOF static thm cm_v_open_temp_ready(
    const thm ready, const thm shape) {
  return conv_rule(reduce_rewrite_conv(THM_LIST(
      shape, cm_v_temp_ready_def, cm_phase_child_temp_def,
      cm_ann_temp_def, cm_ann_cursors_def,
      cm_cursor_phase_def, cm_cursor_temp_def,
      get_theorem_by_name("HD"), get_theorem_by_name("TL"),
      get_theorem_by_name("NOT_CONS_NIL"))), ready);
}

PROOF static void cm_accept_v_phase_case(
    const gnode branch, const thm shape,
    thm result, const thm_list extra_rules) {
  thm_list rules = cm_v_phase_shape_rules(shape);
  for (size_t i = 0; i < vector_size(extra_rules); ++i) {
    vector_add(&rules, extra_rules[i]);
  }
  result = conv_rule(reduce_rewrite_conv(rules), result);
  gnode reduced = CONV_TAC(branch, reduce_rewrite_conv(rules));
  ACCEPT_TAC(reduced, result);
}

PROOF static thm cm_prove_v_phase_layout_step(void) {
  term task = cm_v_phase_task_term();
  term annotation = cm_v_phase_annotation_term();
  term ready =
      `cm_v_phase_ready (p:cm_program) (v:cm_value)
        (st:cm_src_state) ${annotation:cm_annotation}
        (phase:cm_aphase)`;
  term temp_ready =
      `cm_v_temp_ready ${annotation:cm_annotation} (phase:cm_aphase)`;
  term old_layout =
      `cm_task_layout (p:cm_program) ${task:cm_task}
        ${annotation:cm_annotation}`;
  term target =
      `cm_task_layout (p:cm_program) (cm_step ${task:cm_task})
        (cm_update_annotation
          (cm_annotation_step ${task:cm_task}
            ${annotation:cm_annotation}))`;
  term body = imp_chain(
      TERM_LIST(ready, temp_ready, old_layout), target);
  gnode root = gnode_new_with_ccl(
      list_mk_forall(free_vars(body), body));
  gnode introduced = AUTO_INTROS_TAC(root);
  thm phase_cases = ispec_rule(
      `phase:cm_aphase`, get_datatype_cases("cm_aphase"));
  gnode_list cases =
      DISJ_CASES_TAC(introduced, phase_cases, "Hphase");

  for (size_t i = 0; i < vector_size(cases); ++i) {
    while (true) {
      labeled_term_list assumptions = goal_lasmps(cases[i]->g);
      int index = labeled_term_list_index(assumptions, "Hphase");
      if (!is_exists(assumptions[index].tm)) break;
      cases[i] = ASMP_EXISTS_TAC(cases[i], "Hphase", NULL);
    }
    labeled_term_list assumptions = goal_lasmps(cases[i]->g);
    thm shape = assume_rule(
        assumptions[
          labeled_term_list_index(assumptions, "Hphase")].tm);
    thm ready_fact = assume_rule(ready);
    thm aligned_fact =
        cm_v_open_temp_ready(assume_rule(temp_ready), shape);
    thm layout_fact = assume_rule(old_layout);
    layout_fact = conv_rule(
        reduce_rewrite_conv(cm_v_phase_shape_rules(shape)),
        layout_fact);

    if (i == 15 || i == 16 || i == 19 || i == 22) {
      thm impossible = cm_v_open_phase_ready(
          ready_fact, shape, THM_LIST());
      CONTR_TAC(cases[i], impossible);
      continue;
    }

    thm opened_ready = cm_v_open_phase_ready(
        ready_fact, shape, THM_LIST());
    thm result = empty_theorem;
    switch (i) {
      case 0: {
        thm tail_nil = opened_ready;
        thm_list tail_rules =
            THM_LIST(tail_nil, cm_cursor_frames_def);
        layout_fact = conv_rule(
            reduce_rewrite_conv(tail_rules), layout_fact);
        result = match_mp_rule(cm_v_halt_layout_step, layout_fact);
        cm_accept_v_phase_case(
            cases[i], shape, result, tail_rules);
        continue;
      }
      case 1:
        result = match_mp_rule(cm_v_load_layout_step, opened_ready);
        break;
      case 2:
        result = match_mp_rule(
            cm_v_assign_l_layout_step, aligned_fact);
        break;
      case 3:
        result = match_mp_rule(
            cm_v_assign_r_layout_step, opened_ready);
        break;
      case 4:
        result = match_mp_rule(
            cm_v_bin_l_layout_step, aligned_fact);
        break;
      case 5:
        result = match_mp_rule(
            cm_v_bin_r_layout_step, opened_ready);
        break;
      case 6:
        result = cm_v_unary_layout_step;
        break;
      case 7:
        result = match_mp_rule(
            cm_v_index_l_layout_step, aligned_fact);
        break;
      case 8:
        result = match_mp_rule(
            cm_v_index_r_layout_step, opened_ready);
        break;
      case 9:
        result = match_mp_rule(
            cm_v_member_layout_step, opened_ready);
        break;
      case 10:
        result = cm_v_putc_layout_step;
        break;
      case 11:
        result = cm_v_puti_layout_step;
        break;
      case 12:
        result = cm_v_exit_layout_step;
        break;
      case 13:
        result = cm_v_expr_stmt_layout_step;
        break;
      case 14:
        result = cm_v_init_layout_step;
        break;
      case 17:
        result = match_mp_rule(
            cm_v_if_layout_step, aligned_fact);
        break;
      case 18:
        result = match_mp_rule(
            cm_v_while_layout_step, aligned_fact);
        break;
      case 20:
        result = cm_v_return_layout_step;
        break;
      case 21: {
        gnode_list arg_shapes = DISJ_CASES_TAC(
            cases[i],
            ispec_rule(`a1:(cm_expr)list`,
              get_theorem_by_name("list_CASES")),
            "Hargs");
        thm args_nil = assume_rule(
            goal_lasmps(arg_shapes[0]->g)[
              labeled_term_list_index(
                goal_lasmps(arg_shapes[0]->g), "Hargs")].tm);
        thm nil_ready = cm_v_open_phase_ready(
            ready_fact, shape, THM_LIST(args_nil));
        thm nil_layout = conv_rule(
            reduce_rewrite_conv(THM_LIST(args_nil)), layout_fact);
        thm nil_result = match_mp_rule(
            cm_v_arg_nil_layout_step, aligned_fact);
        nil_result = match_mp_rule(
            nil_result, conjunct1_rule(nil_ready));
        nil_result = match_mp_rule(
            nil_result, conjunct2_rule(nil_ready));
        nil_result = match_mp_rule(nil_result, nil_layout);
        cm_accept_v_phase_case(arg_shapes[0], shape, nil_result,
            THM_LIST(args_nil));

        gnode cons = ASMP_EXISTS_TAC(
            arg_shapes[1], "Hargs", NULL);
        cons = ASMP_EXISTS_TAC(cons, "Hargs", NULL);
        thm args_cons = assume_rule(
            goal_lasmps(cons->g)[
              labeled_term_list_index(
                goal_lasmps(cons->g), "Hargs")].tm);
        thm cons_layout = conv_rule(
            reduce_rewrite_conv(THM_LIST(args_cons)), layout_fact);
        thm cons_result = match_mp_rule(
            cm_v_arg_cons_layout_step, aligned_fact);
        cons_result = match_mp_rule(cons_result, cons_layout);
        cm_accept_v_phase_case(cons, shape, cons_result,
            THM_LIST(args_cons));
        continue;
      }
      default:
        CONTR_TAC(cases[i], opened_ready);
        continue;
    }
    result = match_mp_rule(result, layout_fact);
    cm_accept_v_phase_case(cases[i], shape, result, THM_LIST());
  }
  return gnode_prove(root);
}
PROOF thm cm_v_phase_layout_step =
    cm_prove_v_phase_layout_step();

PROOF static thm cm_prove_v_cons_annotation_layout_step(void) {
  term task =
      `CMVTask (p:cm_program) (fid:int) (v:cm_value)
        (st:cm_src_state) (ks:(cm_frame)list)`;
  term annotation = cm_v_phase_annotation_term();
  term erases =
      `cm_annotation_erases ${task:cm_task}
        ${annotation:cm_annotation}`;
  term ready =
      `cm_v_layout_ready (p:cm_program) (v:cm_value)
        (st:cm_src_state) ${annotation:cm_annotation}`;
  term old_layout =
      `cm_task_layout (p:cm_program) ${task:cm_task}
        ${annotation:cm_annotation}`;
  term target =
      `cm_task_layout (p:cm_program) (cm_step ${task:cm_task})
        (cm_update_annotation
          (cm_annotation_step ${task:cm_task}
            ${annotation:cm_annotation}))`;
  term body = imp_chain(
      TERM_LIST(erases, ready, old_layout), target);
  gnode root = gnode_new_with_ccl(
      list_mk_forall(free_vars(body), body));
  gnode leaf = AUTO_INTROS_TAC(root);
  thm frames_eq = conv_rule(
      reduce_rewrite_conv(THM_LIST(
        cm_annotation_erases_def,
        cm_ann_cursors_def, cm_cursor_frames_def,
        cm_cursor_phase_def)),
      assume_rule(erases));
  thm opened_ready = conv_rule(
      reduce_rewrite_conv(THM_LIST(
        cm_v_layout_ready_def, cm_ann_cursors_def,
        cm_ann_temp_def, cm_cursor_temp_def,
        cm_cursor_phase_def,
        get_theorem_by_name("HD"),
        get_theorem_by_name("NOT_CONS_NIL"))),
      assume_rule(ready));
  thm rewritten_layout = conv_rule(
      rewrite_conv(THM_LIST(gsym_rule(frames_eq))),
      assume_rule(old_layout));
  thm result = match_mp_rule(
      cm_v_phase_layout_step, conjunct2_rule(opened_ready));
  result = match_mp_rule(result, conjunct1_rule(opened_ready));
  result = match_mp_rule(result, rewritten_layout);
  result = conv_rule(
      rewrite_conv(THM_LIST(frames_eq)), result);
  ACCEPT_TAC(leaf, result);
  return gnode_prove(root);
}
PROOF thm cm_v_cons_annotation_layout_step =
    cm_prove_v_cons_annotation_layout_step();

PROOF static thm cm_prove_v_nil_annotation_layout_step(void) {
  term task =
      `CMVTask (p:cm_program) (fid:int) (v:cm_value)
        (st:cm_src_state) (ks:(cm_frame)list)`;
  term annotation =
      `CMAnnotation (pc:int) (temp:int) (breakpc:int)
        (continuepc:int) ([]:(cm_acursor)list)
        (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
        (calls:(cm_call_sim_frame)list)`;
  term erases =
      `cm_annotation_erases ${task:cm_task}
        ${annotation:cm_annotation}`;
  term ready =
      `cm_v_layout_ready (p:cm_program) (v:cm_value)
        (st:cm_src_state) ${annotation:cm_annotation}`;
  term old_layout =
      `cm_task_layout (p:cm_program) ${task:cm_task}
        ${annotation:cm_annotation}`;
  term target =
      `cm_task_layout (p:cm_program) (cm_step ${task:cm_task})
        (cm_update_annotation
          (cm_annotation_step ${task:cm_task}
            ${annotation:cm_annotation}))`;
  term body = imp_chain(
      TERM_LIST(erases, ready, old_layout), target);
  gnode root = gnode_new_with_ccl(
      list_mk_forall(free_vars(body), body));
  gnode leaf = AUTO_INTROS_TAC(root);
  thm frames_eq = conv_rule(
      reduce_rewrite_conv(THM_LIST(
        cm_annotation_erases_def, cm_ann_cursors_def,
        cm_cursor_frames_def)),
      assume_rule(erases));
  thm rewritten_layout = conv_rule(
      rewrite_conv(THM_LIST(gsym_rule(frames_eq))),
      assume_rule(old_layout));
  thm_list rules = cm_v_layout_rules();
  vector_add(&rules, gsym_rule(frames_eq));
  thm result = conv_rule(
      reduce_rewrite_conv(rules), rewritten_layout);
  gnode reduced = CONV_TAC(leaf, reduce_rewrite_conv(rules));
  if (IS_NULL(reduced->solved)) {
    ACCEPT_TAC(reduced, result);
  }
  return gnode_prove(root);
}
PROOF thm cm_v_nil_annotation_layout_step =
    cm_prove_v_nil_annotation_layout_step();

PROOF static term cm_v_app_arg_from_right(
    term application, size_t offset) {
  for (size_t i = 0; i < offset; ++i) {
    application = dest_comb(application).tm1;
  }
  return dest_comb(application).tm2;
}

PROOF static thm cm_prove_v_task_layout_step(void) {
  term task =
      `CMVTask (p:cm_program) (fid:int) (v:cm_value)
        (st:cm_src_state) (ks:(cm_frame)list)`;
  term erases =
      `cm_annotation_erases ${task:cm_task}
        (ann:cm_annotation)`;
  term ready =
      `cm_v_layout_ready (p:cm_program) (v:cm_value)
        (st:cm_src_state) (ann:cm_annotation)`;
  term old_layout =
      `cm_task_layout (p:cm_program) ${task:cm_task}
        (ann:cm_annotation)`;
  term target =
      `cm_task_layout (p:cm_program) (cm_step ${task:cm_task})
        (cm_update_annotation
          (cm_annotation_step ${task:cm_task}
            (ann:cm_annotation)))`;
  term body = imp_chain(
      TERM_LIST(erases, ready, old_layout), target);
  gnode root = gnode_new_with_ccl(
      list_mk_forall(free_vars(body), body));
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list annotation_cases = DISJ_CASES_TAC(
      introduced,
      ispec_rule(`ann:cm_annotation`,
        get_datatype_cases("cm_annotation")),
      "Hannotation");

  for (size_t i = 0; i < vector_size(annotation_cases); ++i) {
    gnode branch = annotation_cases[i];
    while (true) {
      labeled_term_list assumptions = goal_lasmps(branch->g);
      int index =
          labeled_term_list_index(assumptions, "Hannotation");
      if (!is_exists(assumptions[index].tm)) break;
      branch = ASMP_EXISTS_TAC(branch, "Hannotation", NULL);
    }
    labeled_term_list assumptions = goal_lasmps(branch->g);
    thm annotation_shape = assume_rule(
        assumptions[labeled_term_list_index(
          assumptions, "Hannotation")].tm);
    term cursors = cm_v_app_arg_from_right(
        rhs_of(annotation_shape), 3);
    gnode_list cursor_cases = DISJ_CASES_TAC(
        branch,
        ispec_rule(cursors, get_theorem_by_name("list_CASES")),
        "Hcursors");

    thm cursors_nil = assume_rule(
        goal_lasmps(cursor_cases[0]->g)[
          labeled_term_list_index(
            goal_lasmps(cursor_cases[0]->g), "Hcursors")].tm);
    thm_list nil_shapes =
        THM_LIST(annotation_shape, cursors_nil);
    thm nil_erases = conv_rule(
        rewrite_conv(nil_shapes), assume_rule(erases));
    thm nil_ready = conv_rule(
        rewrite_conv(nil_shapes), assume_rule(ready));
    thm nil_layout = conv_rule(
        rewrite_conv(nil_shapes), assume_rule(old_layout));
    thm nil_result = match_mp_rule(
        cm_v_nil_annotation_layout_step, nil_erases);
    nil_result = match_mp_rule(nil_result, nil_ready);
    nil_result = match_mp_rule(nil_result, nil_layout);
    nil_result = conv_rule(
        rewrite_conv(nil_shapes), nil_result);
    gnode nil_goal = CONV_TAC(
        cursor_cases[0], rewrite_conv(nil_shapes));
    ACCEPT_TAC(nil_goal, nil_result);

    gnode cons = ASMP_EXISTS_TAC(
        cursor_cases[1], "Hcursors", NULL);
    cons = ASMP_EXISTS_TAC(cons, "Hcursors", NULL);
    thm cursors_cons = assume_rule(
        goal_lasmps(cons->g)[
          labeled_term_list_index(
            goal_lasmps(cons->g), "Hcursors")].tm);
    term cursor = cm_v_app_arg_from_right(
        rhs_of(cursors_cons), 1);
    gnode_list cursor_shapes = DISJ_CASES_TAC(
        cons,
        ispec_rule(cursor, get_datatype_cases("cm_acursor")),
        "Hcursor");
    for (size_t j = 0; j < vector_size(cursor_shapes); ++j) {
      gnode cursor_branch = cursor_shapes[j];
      while (true) {
        labeled_term_list cursor_assumptions =
            goal_lasmps(cursor_branch->g);
        int index = labeled_term_list_index(
            cursor_assumptions, "Hcursor");
        if (!is_exists(cursor_assumptions[index].tm)) break;
        cursor_branch =
            ASMP_EXISTS_TAC(cursor_branch, "Hcursor", NULL);
      }
      thm cursor_shape = assume_rule(
          goal_lasmps(cursor_branch->g)[
            labeled_term_list_index(
              goal_lasmps(cursor_branch->g), "Hcursor")].tm);
      thm_list cons_shapes = THM_LIST(
          annotation_shape, cursors_cons, cursor_shape);
      thm cons_erases = conv_rule(
          rewrite_conv(cons_shapes), assume_rule(erases));
      thm cons_ready = conv_rule(
          rewrite_conv(cons_shapes), assume_rule(ready));
      thm cons_layout = conv_rule(
          rewrite_conv(cons_shapes), assume_rule(old_layout));
      thm cons_result = match_mp_rule(
          cm_v_cons_annotation_layout_step, cons_erases);
      cons_result = match_mp_rule(cons_result, cons_ready);
      cons_result = match_mp_rule(cons_result, cons_layout);
      cons_result = conv_rule(
          rewrite_conv(cons_shapes), cons_result);
      gnode cons_goal = CONV_TAC(
          cursor_branch, rewrite_conv(cons_shapes));
      ACCEPT_TAC(cons_goal, cons_result);
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_v_task_layout_step =
    cm_prove_v_task_layout_step();

PROOF thm get_cm_v_task_layout_step(void) {
  return cm_v_task_layout_step;
}

PROOF static int cmc_preservation_code_value_total_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_code_value_total_axioms_before,
      "cmc_preservation_code_value_total introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_code_value_total_checks =
    cmc_preservation_code_value_total_final_checks();
