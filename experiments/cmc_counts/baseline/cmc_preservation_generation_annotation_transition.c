#include "proof/proof.h"
#include "userlib/proof.h"
#include "cmc_preservation_generation_annotation_transition.h"
#include "cmc_preservation_generation_annotation_step.h"
#include "cmc_preservation_generation_limit.h"
#include "cmc_preservation_generation.h"
#include "cmc_preservation_generation_task.h"
#include "cmc_preservation_generation_step_task.h"
#include "cmc_preservation_spill_semantic.h"
#include "cmc_preservation_state.h"
#include "cmc_preservation_source.h"

#require "cmc_preservation_generation_annotation_step.c"
#require "cmc_preservation_generation_limit.c"
#require "cmc_preservation_generation_step_task.c"

PROOF static size_t _cmc_preservation_generation_annotation_transition_axioms_before =
    vector_size(get_all_axioms());

PROOF static term cm_gat_app_arg_from_right(
    term application, size_t offset) {
  for (size_t i = 0; i < offset; ++i) {
    application = dest_comb(application).tm1;
  }
  return dest_comb(application).tm2;
}

PROOF static term cm_gat_constructor_arg(
    term constructor, size_t arity, size_t index) {
  return cm_gat_app_arg_from_right(
      constructor, arity - index - 1);
}

PROOF static thm cm_gat_payload_update_cond = beta_norm(ispecl_rule(
    TERM_LIST(`condition:bool`,
      `\update:cm_aupdate.
         cm_annotation_payload_generation_below (limit:int)
           (cm_update_annotation update)`,
      `yes_update:cm_aupdate`, `no_update:cm_aupdate`),
    get_theorem_by_name("COND_RAND")));

PROOF static thm cm_prove_gat_head_call_saved(void) {
  gnode root = gnode_new_with_ccl(
      `!(phase:cm_aphase) (owner:int) (owner_break:int)
         (owner_continue:int) (rest:(cm_acursor)list)
         (pc:int) (temp:int) (breakpc:int) (continuepc:int)
         (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
         (calls:(cm_call_sim_frame)list).
         cm_annotation_spill_consistent
           (CMAnnotation pc temp breakpc continuepc
             (CMACursor phase owner owner_break owner_continue :: rest)
             spills saved calls) ==>
         cm_phase_is_call phase ==>
         ~(saved == [])`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm consistent = assume_rule(
      `cm_annotation_spill_consistent
        (CMAnnotation (pc:int) (temp:int) (breakpc:int)
          (continuepc:int)
          (CMACursor (phase:cm_aphase) (owner:int)
            (owner_break:int) (owner_continue:int) ::
            (rest:(cm_acursor)list))
          (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
          (calls:(cm_call_sim_frame)list))`);
  thm call_phase = assume_rule(`cm_phase_is_call (phase:cm_aphase)`);
  thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_annotation_spill_consistent_def,
      cm_ann_temp_def, cm_ann_cursors_def, cm_ann_spills_def,
      cm_ann_saved_def, cm_cursor_temp_def, cm_cursor_phase_def,
      cm_cursors_spill_consistent_def,
      eqt_intro_rule(call_phase),
      get_theorem_by_name("HD"), get_theorem_by_name("TL"),
      get_theorem_by_name("NOT_CONS_NIL"))), consistent);
  thm nonempty = conjunct1_rule(conjunct2_rule(opened));
  CONTR_TAC(leaf, contra(nonempty, assume_rule(
      `(saved:(cm_spill_frame)list) == []`)));
  return gnode_prove(root);
}
PROOF static thm cm_gat_head_call_saved =
    cm_prove_gat_head_call_saved();

PROOF static thm cm_prove_gat_update_c_payload(void) {
  gnode root = gnode_new_with_ccl(
      `!(limit:int) (p:cm_program) (fid:int) (ctl:cm_control)
         (st:cm_src_state) (ann:cm_annotation).
         cm_annotation_payload_generation_below limit ann ==>
         cm_annotation_spill_consistent ann ==>
         ~(cm_ann_cursors ann == []) ==>
         cm_annotation_payload_generation_below limit
           (cm_update_annotation
             (cm_update_c p fid ctl st ann
               (cm_cursor_phase (HD (cm_ann_cursors ann)))))`);
  gnode introduced = AUTO_INTROS_TAC(root);
  thm old_payload = assume_rule(
      `cm_annotation_payload_generation_below (limit:int)
        (ann:cm_annotation)`);
  thm old_consistent = assume_rule(
      `cm_annotation_spill_consistent (ann:cm_annotation)`);
  thm cursors_nonempty = assume_rule(
      `~(cm_ann_cursors (ann:cm_annotation) == [])`);
  gnode_list ann_cases = DISJ_CASES_TAC(introduced,
      ispec_rule(`ann:cm_annotation`,
        get_datatype_cases("cm_annotation")), "Hann");
  gnode branch = ann_cases[0];
  while (true) {
    labeled_term_list assumptions = goal_lasmps(branch->g);
    int index = labeled_term_list_index(assumptions, "Hann");
    if (!is_exists(assumptions[index].tm)) break;
    branch = ASMP_EXISTS_TAC(branch, "Hann", NULL);
  }
  thm ann_shape = assume_rule(
      goal_lasmps(branch->g)[labeled_term_list_index(
        goal_lasmps(branch->g), "Hann")].tm);
  term shaped_ann = rhs_of(ann_shape);
  term cursors = cm_gat_constructor_arg(shaped_ann, 8, 4);
  gnode_list cursor_cases = DISJ_CASES_TAC(branch,
      ispec_rule(cursors, get_theorem_by_name("list_CASES")),
      "Hcursors");
  {
    thm cursors_nil = assume_rule(
        goal_lasmps(cursor_cases[0]->g)[labeled_term_list_index(
          goal_lasmps(cursor_cases[0]->g), "Hcursors")].tm);
    thm impossible = conv_rule(reduce_rewrite_conv(THM_LIST(
        ann_shape, cursors_nil, cm_ann_cursors_def)),
        cursors_nonempty);
    CONTR_TAC(cursor_cases[0], impossible);
  }
  gnode cons = ASMP_EXISTS_TAC(cursor_cases[1], "Hcursors", NULL);
  cons = ASMP_EXISTS_TAC(cons, "Hcursors", NULL);
  thm cursors_cons = assume_rule(
      goal_lasmps(cons->g)[labeled_term_list_index(
        goal_lasmps(cons->g), "Hcursors")].tm);
  term cursor = cm_gat_app_arg_from_right(rhs_of(cursors_cons), 1);
  gnode_list cursor_shapes = DISJ_CASES_TAC(cons,
      ispec_rule(cursor, get_datatype_cases("cm_acursor")),
      "Hcursor");
  gnode cursor_branch = cursor_shapes[0];
  while (true) {
    labeled_term_list assumptions = goal_lasmps(cursor_branch->g);
    int index = labeled_term_list_index(assumptions, "Hcursor");
    if (!is_exists(assumptions[index].tm)) break;
    cursor_branch = ASMP_EXISTS_TAC(cursor_branch, "Hcursor", NULL);
  }
  thm cursor_shape = assume_rule(
      goal_lasmps(cursor_branch->g)[labeled_term_list_index(
        goal_lasmps(cursor_branch->g), "Hcursor")].tm);
  thm full_shape = conv_rule(rewrite_conv(THM_LIST(
      cursors_cons, cursor_shape)), ann_shape);
  shaped_ann = rhs_of(full_shape);
  term pc = cm_gat_constructor_arg(shaped_ann, 8, 0);
  term temp = cm_gat_constructor_arg(shaped_ann, 8, 1);
  term breakpc = cm_gat_constructor_arg(shaped_ann, 8, 2);
  term continuepc = cm_gat_constructor_arg(shaped_ann, 8, 3);
  term spills = cm_gat_constructor_arg(shaped_ann, 8, 5);
  term saved = cm_gat_constructor_arg(shaped_ann, 8, 6);
  term calls = cm_gat_constructor_arg(shaped_ann, 8, 7);
  term shaped_cursor = rhs_of(cursor_shape);
  term phase = cm_gat_constructor_arg(shaped_cursor, 4, 0);
  term owner = cm_gat_constructor_arg(shaped_cursor, 4, 1);
  term owner_break = cm_gat_constructor_arg(shaped_cursor, 4, 2);
  term owner_continue = cm_gat_constructor_arg(shaped_cursor, 4, 3);
  term rest = cm_gat_app_arg_from_right(rhs_of(cursors_cons), 0);
  thm shaped_payload = conv_rule(rewrite_conv(THM_LIST(full_shape)),
      old_payload);
  thm shaped_consistent = conv_rule(
      rewrite_conv(THM_LIST(full_shape)), old_consistent);
  thm call_saved = specl_rule(TERM_LIST(
      phase, owner, owner_break, owner_continue, rest,
      pc, temp, breakpc, continuepc, spills, saved, calls),
      cm_gat_head_call_saved);
  call_saved = match_mp_rule(call_saved, shaped_consistent);
  thm result = specl_rule(TERM_LIST(
      `limit:int`, `p:cm_program`, `fid:int`, `ctl:cm_control`,
      `st:cm_src_state`, phase, pc, temp, breakpc, continuepc,
      owner, owner_break, owner_continue, rest, spills, saved, calls),
      cm_update_c_payload_generation);
  result = match_mp_rule(result, call_saved);
  result = match_mp_rule(result, shaped_payload);
  thm target_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
      full_shape, cm_ann_cursors_def, cm_cursor_phase_def,
      get_theorem_by_name("HD"),
      get_theorem_by_name("NOT_CONS_NIL"))),
      goal_ccl(cursor_branch->g));
  ACCEPT_TAC(cursor_branch,
      eq_mp_rule(sym_rule(target_view), result));
  return gnode_prove(root);
}
PROOF static thm cm_gat_update_c_payload =
    cm_prove_gat_update_c_payload();

PROOF static thm cm_prove_annotation_step_payload_generation(void) {
  gnode root = gnode_new_with_ccl(
      `!(root_program:cm_program) (task:cm_task)
         (ann:cm_annotation).
         cm_task_generation_below root_program task ==>
         cm_annotation_generation_below task ann ==>
         cm_annotation_spill_consistent ann ==>
         ~(cm_task_done task) ==>
         cm_annotation_payload_generation_below
           (cm_task_generation_limit task)
           (cm_update_annotation
             (cm_annotation_step task ann))`);
  gnode introduced = AUTO_INTROS_TAC(root);
  thm task_generation = assume_rule(
      `cm_task_generation_below (root_program:cm_program)
        (task:cm_task)`);
  thm annotation_generation = assume_rule(
      `cm_annotation_generation_below (task:cm_task)
        (ann:cm_annotation)`);
  thm annotation_consistent = assume_rule(
      `cm_annotation_spill_consistent (ann:cm_annotation)`);
  thm not_done = assume_rule(`~(cm_task_done (task:cm_task))`);
  gnode_list cases = DISJ_CASES_TAC(introduced,
      ispec_rule(`task:cm_task`,
        get_datatype_cases("cm_task")), "Htask");
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
    term concrete = rhs_of(task_shape);
    if (i == 6) {
      thm impossible = conv_rule(reduce_rewrite_conv(THM_LIST(
          task_shape, get_cm_task_done_def())), not_done);
      CONTR_TAC(branch, impossible);
      continue;
    }
    if (i == 0) {
      term program = cm_gat_constructor_arg(concrete, 2, 0);
      term input = cm_gat_constructor_arg(concrete, 2, 1);
      term condition =
          `cm_call_ok ${program:cm_program}
             (cm_program_main ${program:cm_program}) []
             (cm_initial_state ${program:cm_program}
               ${input:(int)list}) &&
           cm_call_depth [CMHaltK] < 65536i`;
      gnode_list start_cases = BOOL_CASES_TAC(
          branch, condition, "Hstart");
      for (size_t j = 0; j < vector_size(start_cases); ++j) {
        thm start_case = assume_rule(
            goal_lasmps(start_cases[j]->g)[labeled_term_list_index(
              goal_lasmps(start_cases[j]->g), "Hstart")].tm);
        thm start_rule = j == 0
            ? eqt_intro_rule(start_case)
            : eqf_intro_rule(start_case);
        ACCEPT_TAC(start_cases[j], eqt_elim_rule(apply_conversion(
            reduce_rewrite_conv(THM_LIST(
              task_shape, cm_task_generation_limit_def,
              cm_annotation_step_def, cm_update_annotation_def,
              start_rule,
              cm_annotation_payload_generation_below_def,
              cm_ann_enter_call_def,
              cm_ann_spills_def, cm_ann_saved_def,
              cm_spills_generation_below_def,
              cm_spill_frames_generation_below_def,
              cm_spill_frame_spills_def)),
            goal_ccl(start_cases[j]->g))));
      }
      continue;
    }
    term program = cm_gat_constructor_arg(concrete, 5, 0);
    term fid = cm_gat_constructor_arg(concrete, 5, 1);
    term payload = cm_gat_constructor_arg(concrete, 5, 2);
    term state = cm_gat_constructor_arg(concrete, 5, 3);
    term old_payload_goal =
        `cm_annotation_payload_generation_below
          (cm_state_nextgen ${state:cm_src_state})
          (ann:cm_annotation)`;
    thm annotation_normal = conv_rule(
        reduce_rewrite_conv(THM_LIST(
          task_shape, cm_annotation_generation_below_def,
          cm_active_spill_frames_def,
          cm_spill_frames_generation_below_def,
          cm_spill_frame_spills_def)),
        annotation_generation);
    thm payload_view = apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          cm_annotation_payload_generation_below_def,
          cm_ann_spills_def, cm_ann_saved_def)),
        old_payload_goal);
    thm old_payload =
        eq_mp_rule(sym_rule(payload_view), annotation_normal);
    thm result = empty_theorem;
    if (i == 1) {
      result = specl_rule(TERM_LIST(
          `cm_state_nextgen ${state:cm_src_state}`,
          program, fid, state, `ann:cm_annotation`, payload),
          cm_update_r_payload_generation);
      result = match_mp_rule(result, old_payload);
    } else if (i == 2) {
      result = specl_rule(TERM_LIST(
          `cm_state_nextgen ${state:cm_src_state}`,
          program, fid, state, `ann:cm_annotation`, payload),
          cm_update_l_payload_generation);
      result = match_mp_rule(result, old_payload);
    } else if (i == 3) {
      result = specl_rule(TERM_LIST(
          `cm_state_nextgen ${state:cm_src_state}`,
          program, fid, state, `ann:cm_annotation`, payload),
          cm_update_s_payload_generation);
      result = match_mp_rule(result, old_payload);
    }
    if (i >= 1 && i <= 3) {
      thm target_view = apply_conversion(
          rewrite_conv(THM_LIST(
            task_shape, cm_task_generation_limit_def,
            cm_annotation_step_def)),
          goal_ccl(branch->g));
      ACCEPT_TAC(branch,
          eq_mp_rule(sym_rule(target_view), result));
      continue;
    }
    thm not_exit = empty_theorem;
    if (i == 5) {
      gnode_list exit_cases = BOOL_CASES_TAC(
          branch, `cm_control_kind ${payload:cm_control} == 4i`,
          "Hexit_payload");
      thm is_exit = assume_rule(
          goal_lasmps(exit_cases[0]->g)[labeled_term_list_index(
            goal_lasmps(exit_cases[0]->g), "Hexit_payload")].tm);
      thm_list exit_rules = THM_LIST(
          task_shape, cm_task_generation_limit_def,
          cm_annotation_step_def, cm_update_annotation_def,
          cm_ann_done_def, cm_annotation_payload_generation_below_def,
          cm_ann_spills_def, cm_ann_saved_def, is_exit);
      thm normalized = conv_rule(
          reduce_rewrite_conv(exit_rules), old_payload);
      thm target_view = apply_conversion(
          reduce_rewrite_conv(exit_rules),
          goal_ccl(exit_cases[0]->g));
      ACCEPT_TAC(exit_cases[0],
          eq_mp_rule(sym_rule(target_view), normalized));
      branch = exit_cases[1];
      not_exit = assume_rule(
          goal_lasmps(branch->g)[labeled_term_list_index(
            goal_lasmps(branch->g), "Hexit_payload")].tm);
    }
    gnode_list cursor_empty_cases = BOOL_CASES_TAC(
        branch, `cm_ann_cursors (ann:cm_annotation) == []`,
        "Hcursors_empty");
    for (size_t j = 0;
         j < vector_size(cursor_empty_cases); ++j) {
      gnode cursor_branch = cursor_empty_cases[j];
      thm cursor_case = assume_rule(
          goal_lasmps(cursor_branch->g)[labeled_term_list_index(
            goal_lasmps(cursor_branch->g),
            "Hcursors_empty")].tm);
      if (j == 0) {
        result = old_payload;
      } else if (i == 4) {
        thm generation_open = conv_rule(
            reduce_rewrite_conv(THM_LIST(
              task_shape, cm_task_generation_below_def)),
            task_generation);
        thm value_below = conjunct1_rule(
            conjunct2_rule(conjunct2_rule(generation_open)));
        result = specl_rule(TERM_LIST(
            `cm_state_nextgen ${state:cm_src_state}`,
            program, fid, payload, state, `ann:cm_annotation`,
            `cm_cursor_phase
              (HD (cm_ann_cursors (ann:cm_annotation)))`),
            cm_update_v_payload_generation);
        result = match_mp_rule(result, value_below);
        result = match_mp_rule(result, old_payload);
      } else {
        result = specl_rule(TERM_LIST(
            `cm_state_nextgen ${state:cm_src_state}`,
            program, fid, payload, state, `ann:cm_annotation`),
            cm_gat_update_c_payload);
        result = match_mp_rule(result, old_payload);
        result = match_mp_rule(result, annotation_consistent);
        result = match_mp_rule(result, cursor_case);
      }
      thm cursor_rule = j == 0
          ? eqt_intro_rule(cursor_case)
          : eqf_intro_rule(cursor_case);
      thm_list target_rules = THM_LIST(
          task_shape, cm_task_generation_limit_def,
          cm_annotation_step_def, cm_update_annotation_def,
          cursor_rule);
      if (i == 5) vector_add(&target_rules, not_exit);
      thm target_view = apply_conversion(
          reduce_rewrite_conv(target_rules),
          goal_ccl(cursor_branch->g));
      ACCEPT_TAC(cursor_branch,
          eq_mp_rule(sym_rule(target_view), result));
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_annotation_step_payload_generation =
    cm_prove_annotation_step_payload_generation();

PROOF static thm cm_prove_annotation_generation_below_step(void) {
  gnode root = gnode_new_with_ccl(
      `!(root_program:cm_program) (task:cm_task)
         (ann:cm_annotation).
         cm_task_generation_below root_program task ==>
         cm_annotation_generation_below task ann ==>
         cm_annotation_spill_consistent ann ==>
         cm_annotation_generation_below (cm_step task)
           (cm_update_annotation
             (cm_annotation_step task ann))`);
  gnode introduced = AUTO_INTROS_TAC(root);
  thm task_generation = assume_rule(
      `cm_task_generation_below (root_program:cm_program)
        (task:cm_task)`);
  thm annotation_generation = assume_rule(
      `cm_annotation_generation_below (task:cm_task)
        (ann:cm_annotation)`);
  thm annotation_consistent = assume_rule(
      `cm_annotation_spill_consistent (ann:cm_annotation)`);
  gnode_list cases = DISJ_CASES_TAC(introduced,
      ispec_rule(`task:cm_task`,
        get_datatype_cases("cm_task")), "Htask");
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
    if (i == 6) {
      thm_list done_rules = THM_LIST(
          task_shape, get_cm_step_def(),
          cm_annotation_step_def, cm_update_annotation_def);
      thm unchanged = conv_rule(rewrite_conv(done_rules),
          annotation_generation);
      thm target_view = apply_conversion(
          rewrite_conv(done_rules), goal_ccl(branch->g));
      ACCEPT_TAC(branch,
          eq_mp_rule(sym_rule(target_view), unchanged));
      continue;
    }
    thm not_done = eqt_elim_rule(apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          task_shape, get_cm_task_done_def())),
        `~(cm_task_done (task:cm_task))`));
    thm payload_old = specl_rule(TERM_LIST(
        `root_program:cm_program`, `task:cm_task`,
        `ann:cm_annotation`),
        cm_annotation_step_payload_generation);
    payload_old = match_mp_rule(payload_old, task_generation);
    payload_old = match_mp_rule(payload_old, annotation_generation);
    payload_old = match_mp_rule(payload_old, annotation_consistent);
    payload_old = match_mp_rule(payload_old, not_done);
    thm payload_new = specl_rule(TERM_LIST(
        `cm_update_annotation
          (cm_annotation_step (task:cm_task) (ann:cm_annotation))`,
        `cm_task_generation_limit (task:cm_task)`,
        `cm_task_generation_limit (cm_step (task:cm_task))`),
        cm_annotation_payload_generation_below_mono);
    payload_new = match_mp_rule(payload_new,
        spec_rule(`task:cm_task`,
          cm_task_generation_limit_step_mono));
    payload_new = match_mp_rule(payload_new, payload_old);
    thm result = specl_rule(TERM_LIST(
        `cm_step (task:cm_task)`,
        `cm_update_annotation
          (cm_annotation_step task (ann:cm_annotation))`),
        cm_annotation_payload_implies_task_generation);
    result = match_mp_rule(result, payload_new);
    ACCEPT_TAC(branch, result);
  }
  return gnode_prove(root);
}
PROOF thm cm_annotation_generation_below_step =
    cm_prove_annotation_generation_below_step();

PROOF static thm cm_prove_task_generation_safe_step(void) {
  gnode root = gnode_new_with_ccl(
      `!(root_program:cm_program) (task:cm_task)
         (ann:cm_annotation).
         cm_task_static_valid task ==>
         cm_task_generation_safe root_program task ann ==>
         cm_annotation_spill_consistent ann ==>
         cm_task_succeeds task ==>
         cm_task_generation_safe root_program (cm_step task)
           (cm_update_annotation
             (cm_annotation_step task ann))`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm old_safe = conv_rule(rewrite_conv(THM_LIST(
      cm_task_generation_safe_def)), assume_rule(
        `cm_task_generation_safe (root_program:cm_program)
          (task:cm_task) (ann:cm_annotation)`));
  thm task_generation = conjunct1_rule(old_safe);
  thm annotation_generation = conjunct2_rule(old_safe);
  thm next_task = specl_rule(TERM_LIST(
      `root_program:cm_program`, `task:cm_task`),
      cm_task_generation_below_step);
  next_task = match_mp_rule(next_task,
      assume_rule(`cm_task_static_valid (task:cm_task)`));
  next_task = match_mp_rule(next_task, task_generation);
  next_task = match_mp_rule(next_task,
      assume_rule(`cm_task_succeeds (task:cm_task)`));
  thm next_annotation = specl_rule(TERM_LIST(
      `root_program:cm_program`, `task:cm_task`,
      `ann:cm_annotation`),
      cm_annotation_generation_below_step);
  next_annotation =
      match_mp_rule(next_annotation, task_generation);
  next_annotation =
      match_mp_rule(next_annotation, annotation_generation);
  next_annotation = match_mp_rule(next_annotation,
      assume_rule(
        `cm_annotation_spill_consistent (ann:cm_annotation)`));
  thm target_view = apply_conversion(rewrite_conv(THM_LIST(
      cm_task_generation_safe_def)), goal_ccl(leaf->g));
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view),
      conj_rule(next_task, next_annotation)));
  return gnode_prove(root);
}
PROOF thm cm_task_generation_safe_step =
    cm_prove_task_generation_safe_step();


PROOF static int cmc_preservation_generation_annotation_transition_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_generation_annotation_transition_axioms_before,
      "cmc_preservation_generation_annotation_transition introduced an axiom");
  ENSURE_COND(vector_size(hyp(
      cm_annotation_step_payload_generation)) == 0,
      "annotation-step payload generation theorem is not closed");
  ENSURE_COND(vector_size(hyp(
      cm_annotation_generation_below_step)) == 0,
      "annotation generation-step theorem is not closed");
  ENSURE_COND(vector_size(hyp(
      cm_task_generation_safe_step)) == 0,
      "task generation-safety theorem is not closed");
  return 0;
err:
  return -1;
}

PROOF static int _cmc_preservation_generation_annotation_transition_checks =
    cmc_preservation_generation_annotation_transition_final_checks();
