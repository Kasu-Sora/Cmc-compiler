#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_type_step.h"
#include "cmc_preservation_type_facts.h"
#include "cmc_preservation_code_task.h"
#include "cmc_preservation_type_source_r_total.h"
#include "cmc_preservation_type_source_l.h"
#include "cmc_preservation_type_source_s.h"
#include "cmc_preservation_ready_coordinate.h"
#include "cmc_preservation_fid.h"

#require "cmc_preservation_type_source_r_total.c"
#require "cmc_preservation_type_source_l.c"
#require "cmc_preservation_type_source_s.c"
#require "cmc_preservation_type_source_c_total.c"
#require "cmc_preservation_fid.c"

PROOF static size_t _cmc_preservation_type_step_axioms_before =
    vector_size(get_all_axioms());


PROOF static term cm_tstep_app_arg_from_right(
    term application, size_t offset) {
  for (size_t i = 0; i < offset; ++i) {
    application = dest_comb(application).tm1;
  }
  return dest_comb(application).tm2;
}

PROOF static term cm_tstep_constructor_arg(
    term constructor, size_t arity, size_t index) {
  return cm_tstep_app_arg_from_right(
      constructor, arity - index - 1);
}

PROOF static thm cm_tstep_pick_conjunct(thm fact, term wanted) {
  if (alpha_compare(concl(fact), wanted) == 0) return fact;
  if (!is_conj(concl(fact))) return empty_theorem;
  thm left = cm_tstep_pick_conjunct(conjunct1_rule(fact), wanted);
  if (!IS_NULL(left)) return left;
  return cm_tstep_pick_conjunct(conjunct2_rule(fact), wanted);
}

PROOF static void cm_tstep_accept(
    gnode branch, thm_list rules, thm result) {
  thm normalized = conv_rule(rewrite_conv(rules), result);
  thm target_view = apply_conversion(
      rewrite_conv(rules), goal_ccl(branch->g));
  ACCEPT_TAC(branch, eq_mp_rule(sym_rule(target_view), normalized));
}

PROOF static thm cm_prove_start_type_ready_step(void) {
  term task = `CMStartTask (q:cm_program) (input:(int)list)`;
  term next = `cm_step ${task:cm_task}`;
  term next_ann =
      `cm_update_annotation
         (cm_annotation_step ${task:cm_task} (ann:cm_annotation))`;
  term typed_term = `cm_typed_program (p:cm_program)`;
  term layout_term =
      `cm_task_layout_ready (p:cm_program) ${task:cm_task}
        (ann:cm_annotation)`;
  term target =
      `cm_task_type_ready (p:cm_program) ${next:cm_task}
        ${next_ann:cm_annotation}`;
  term body = imp_chain(TERM_LIST(typed_term, layout_term), target);
  gnode root = gnode_new_with_ccl(
      list_mk_forall(free_vars(body), body));
  gnode leaf = AUTO_INTROS_TAC(root);
  thm typed = assume_rule(typed_term);
  thm typed_open = conv_rule(rewrite_conv(THM_LIST(
      get_cm_typed_program_def())), typed);
  thm layout_open = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_task_layout_ready_def)), assume_rule(layout_term));
  thm same_program = cm_tstep_pick_conjunct(
      layout_open, `(q:cm_program) == (p:cm_program)`);
  thm same_annotation = cm_tstep_pick_conjunct(
      layout_open, `(ann:cm_annotation) == cm_initial_annotation`);
  thm call_ok = cm_tstep_pick_conjunct(layout_open,
      `cm_call_ok (p:cm_program) (cm_program_main p) []
        (cm_initial_state p (input:(int)list))`);
  thm main_low = cm_tstep_pick_conjunct(typed_open,
      `0i <= cm_program_main (p:cm_program)`);
  thm main_high = cm_tstep_pick_conjunct(typed_open,
      `cm_program_main (p:cm_program) <
       ilength (cm_program_functions p)`);
  thm main_ret = cm_tstep_pick_conjunct(typed_open,
      `cm_function_ret
         (inth (cm_program_main (p:cm_program))
           (cm_program_functions p)) == CMIntTy`);
  thm function_wf = specl_rule(TERM_LIST(
      `p:cm_program`, `cm_program_main (p:cm_program)`),
      cm_typed_function_at);
  function_wf = match_mp_rule(
      match_mp_rule(match_mp_rule(function_wf, typed), main_low),
      main_high);
  thm function_open = conv_rule(rewrite_conv(THM_LIST(
      get_cm_function_wf_def())), function_wf);
  term main_function =
      `inth (cm_program_main (p:cm_program))
        (cm_program_functions p)`;
  thm body_wf_false = cm_tstep_pick_conjunct(function_open,
      `cm_stmt_wf (p:cm_program) ${main_function:cm_function_d} F
        (cm_function_body ${main_function:cm_function_d})`);
  thm body_wf = match_mp_rule(specl_rule(TERM_LIST(
      `cm_function_body ${main_function:cm_function_d}`,
      `p:cm_program`, main_function, `F`),
      cm_stmt_wf_loop_mono), body_wf_false);
  thm depth = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(THM_LIST(
        get_cm_call_depth_def(), get_cm_is_call_frame_def(),
        get_theorem_by_name("ILENGTH_DEF"))),
      `cm_call_depth [CMHaltK] < 65536i`));
  thm_list rules = THM_LIST(
      same_program, same_annotation, call_ok, depth,
      main_low, main_high, main_ret, body_wf,
      get_cm_step_def(), get_cm_begin_call_def(),
      cm_annotation_step_def, cm_update_annotation_def,
      cm_ann_enter_call_def, cm_ann_cursors_def,
      get_cm_task_type_ready_def(), get_cm_cursors_type_ready_def(),
      get_cm_phase_static_type_ready_def(),
      get_cm_phase_parent_type_ready_def(),
      get_cm_phase_result_type_ready_def(),
      get_cm_cursor_head_input_type_ready_def(),
      get_cm_phase_input_type_ready_def(),
      get_cm_phase_result_type_def(),
      get_cm_cursor_head_value_type_ready_def(),
      get_cm_phase_value_type_ready_def(),
      cm_phase_next_fid_def, cm_cursor_phase_def,
      get_theorem_by_name("HD"), get_theorem_by_name("TL"),
      get_theorem_by_name("NOT_CONS_NIL"));
  thm proved = eqt_elim_rule(apply_conversion(
      reduce_rewrite_conv(rules), goal_ccl(leaf->g)));
  proved = disch_rule(layout_term, proved);
  proved = disch_rule(typed_term, proved);
  proved = mp_rule(proved, assume_rule(typed_term));
  proved = mp_rule(proved, assume_rule(layout_term));
  ACCEPT_TAC(leaf, proved);
  return gnode_prove(root);
}
PROOF static thm cm_start_type_ready_step =
    cm_prove_start_type_ready_step();

PROOF static thm cm_prove_v_type_ready_step(void) {
  term task =
      `CMVTask (q:cm_program) (fid:int) (incoming:cm_value)
        (st:cm_src_state) (ks:(cm_frame)list)`;
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (q:cm_program) (fid:int)
         (incoming:cm_value) (st:cm_src_state) (ks:(cm_frame)list)
         (ann:cm_annotation).
         cm_typed_program p ==>
         cm_annotation_erases ${task:cm_task} ann ==>
         cm_task_type_ready p ${task:cm_task} ann ==>
         cm_task_phase_fid_ready p ${task:cm_task} ann ==>
         cm_task_type_ready p (cm_step ${task:cm_task})
           (cm_update_annotation
             (cm_annotation_step ${task:cm_task} ann))`);
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list ann_cases = DISJ_CASES_TAC(introduced,
      ispec_rule(`ann:cm_annotation`,
        get_datatype_cases("cm_annotation")), "Hann");
  gnode branch = ann_cases[0];
  while (is_exists(goal_lasmps(branch->g)[
      labeled_term_list_index(goal_lasmps(branch->g), "Hann")].tm)) {
    branch = ASMP_EXISTS_TAC(branch, "Hann", NULL);
  }
  thm ann_shape = assume_rule(goal_lasmps(branch->g)[
      labeled_term_list_index(goal_lasmps(branch->g), "Hann")].tm);
  term cursors = cm_tstep_constructor_arg(rhs_of(ann_shape), 8, 4);
  gnode_list cursor_cases = DISJ_CASES_TAC(branch,
      ispec_rule(cursors, get_theorem_by_name("list_CASES")),
      "Hcursors");
  {
    thm cursors_nil = assume_rule(goal_lasmps(cursor_cases[0]->g)[
        labeled_term_list_index(
          goal_lasmps(cursor_cases[0]->g), "Hcursors")].tm);
    thm ready = conv_rule(rewrite_conv(THM_LIST(
        ann_shape, cursors_nil)), assume_rule(
          `cm_task_type_ready (p:cm_program) ${task:cm_task}
            (ann:cm_annotation)`));
    thm impossible = conv_rule(reduce_rewrite_conv(THM_LIST(
        get_cm_task_type_ready_def(), cm_ann_cursors_def,
        get_cm_cursor_head_value_type_ready_def())), ready);
    CONTR_TAC(cursor_cases[0], impossible);
  }
  gnode cons = ASMP_EXISTS_TAC(cursor_cases[1], "Hcursors", NULL);
  cons = ASMP_EXISTS_TAC(cons, "Hcursors", NULL);
  thm cursors_cons = assume_rule(goal_lasmps(cons->g)[
      labeled_term_list_index(goal_lasmps(cons->g), "Hcursors")].tm);
  term cursor = cm_tstep_app_arg_from_right(rhs_of(cursors_cons), 1);
  gnode_list cursor_shapes = DISJ_CASES_TAC(cons,
      ispec_rule(cursor, get_datatype_cases("cm_acursor")), "Hcursor");
  gnode cursor_branch = cursor_shapes[0];
  while (is_exists(goal_lasmps(cursor_branch->g)[
      labeled_term_list_index(
        goal_lasmps(cursor_branch->g), "Hcursor")].tm)) {
    cursor_branch = ASMP_EXISTS_TAC(cursor_branch, "Hcursor", NULL);
  }
  thm cursor_shape = assume_rule(goal_lasmps(cursor_branch->g)[
      labeled_term_list_index(
        goal_lasmps(cursor_branch->g), "Hcursor")].tm);
  thm full_shape = conv_rule(rewrite_conv(THM_LIST(
      cursors_cons, cursor_shape)), ann_shape);
  term shaped_ann = rhs_of(full_shape);
  term phase = cm_tstep_constructor_arg(rhs_of(cursor_shape), 4, 0);
  term pc = cm_tstep_constructor_arg(shaped_ann, 8, 0);
  term temp = cm_tstep_constructor_arg(shaped_ann, 8, 1);
  term breakpc = cm_tstep_constructor_arg(shaped_ann, 8, 2);
  term continuepc = cm_tstep_constructor_arg(shaped_ann, 8, 3);
  term owner = cm_tstep_constructor_arg(rhs_of(cursor_shape), 4, 1);
  term owner_break = cm_tstep_constructor_arg(rhs_of(cursor_shape), 4, 2);
  term owner_continue = cm_tstep_constructor_arg(rhs_of(cursor_shape), 4, 3);
  term rest = cm_tstep_app_arg_from_right(rhs_of(cursors_cons), 0);
  term spills = cm_tstep_constructor_arg(shaped_ann, 8, 5);
  term saved = cm_tstep_constructor_arg(shaped_ann, 8, 6);
  term calls = cm_tstep_constructor_arg(shaped_ann, 8, 7);
  thm shaped_erases = conv_rule(rewrite_conv(THM_LIST(
      full_shape)), assume_rule(
        `cm_annotation_erases ${task:cm_task} (ann:cm_annotation)`));
  thm frames_equal = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_annotation_erases_def, cm_ann_cursors_def,
      cm_cursor_frames_def, cm_cursor_phase_def)),
      shaped_erases);
  thm frames_rewrite = gsym_rule(frames_equal);
  thm_list task_shape_rules = THM_LIST(full_shape, frames_rewrite);
  thm cursor_fid_ready = conv_rule(reduce_rewrite_conv(THM_LIST(
      full_shape, cm_task_phase_fid_ready_def,
      cm_cursors_fid_ready_def, cm_ann_cursors_def,
      cm_cursor_frames_def, cm_frames_fid_ready_def)),
      assume_rule(
        `cm_task_phase_fid_ready (p:cm_program) ${task:cm_task}
          (ann:cm_annotation)`));
  thm fid_ready = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_cursor_phase_def)), match_mp_rule(
        get_cm_phase_frame_fid_ready(),
        conjunct1_rule(cursor_fid_ready)));
  thm result = specl_rule(TERM_LIST(
      `p:cm_program`, `q:cm_program`, `fid:int`,
      `incoming:cm_value`, `st:cm_src_state`,
      `cm_cursor_frames ${rest:(cm_acursor)list}`,
      pc, temp, breakpc, continuepc, phase, owner, owner_break,
      owner_continue, rest, spills, saved, calls),
      cm_v_type_ready_step_at);
  result = match_mp_rule(result,
      assume_rule(`cm_typed_program (p:cm_program)`));
  result = match_mp_rule(result, fid_ready);
  result = match_mp_rule(result, conv_rule(
      rewrite_conv(THM_LIST(frames_rewrite)), shaped_erases));
  result = match_mp_rule(result, conv_rule(rewrite_conv(task_shape_rules),
      assume_rule(
        `cm_task_type_ready (p:cm_program) ${task:cm_task}
          (ann:cm_annotation)`)));
  cm_tstep_accept(cursor_branch, task_shape_rules, result);
  return gnode_prove(root);
}
PROOF static thm cm_v_type_ready_step =
    cm_prove_v_type_ready_step();

PROOF static thm cm_prove_c_type_ready_step(void) {
  term task =
      `CMCTask (q:cm_program) (fid:int) (control:cm_control)
        (st:cm_src_state) (ks:(cm_frame)list)`;
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (q:cm_program) (fid:int)
         (control:cm_control) (st:cm_src_state) (ks:(cm_frame)list)
         (ann:cm_annotation).
         cm_typed_program p ==>
         cm_annotation_erases ${task:cm_task} ann ==>
         cm_task_type_ready p ${task:cm_task} ann ==>
         cm_task_phase_fid_ready p ${task:cm_task} ann ==>
         cm_task_type_ready p (cm_step ${task:cm_task})
           (cm_update_annotation
             (cm_annotation_step ${task:cm_task} ann))`);
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list ann_cases = DISJ_CASES_TAC(introduced,
      ispec_rule(`ann:cm_annotation`,
        get_datatype_cases("cm_annotation")), "Hann");
  gnode branch = ann_cases[0];
  while (is_exists(goal_lasmps(branch->g)[
      labeled_term_list_index(goal_lasmps(branch->g), "Hann")].tm)) {
    branch = ASMP_EXISTS_TAC(branch, "Hann", NULL);
  }
  thm ann_shape = assume_rule(goal_lasmps(branch->g)[
      labeled_term_list_index(goal_lasmps(branch->g), "Hann")].tm);
  term cursors = cm_tstep_constructor_arg(rhs_of(ann_shape), 8, 4);
  gnode_list cursor_cases = DISJ_CASES_TAC(branch,
      ispec_rule(cursors, get_theorem_by_name("list_CASES")),
      "Hcursors");
  {
    thm cursors_nil = assume_rule(goal_lasmps(cursor_cases[0]->g)[
        labeled_term_list_index(
          goal_lasmps(cursor_cases[0]->g), "Hcursors")].tm);
    thm erases = conv_rule(rewrite_conv(THM_LIST(
        ann_shape, cursors_nil)), assume_rule(
          `cm_annotation_erases ${task:cm_task} (ann:cm_annotation)`));
    thm frames_nil = conv_rule(reduce_rewrite_conv(THM_LIST(
        cm_annotation_erases_def, cm_ann_cursors_def,
        cm_cursor_frames_def)), erases);
    thm_list rules = THM_LIST(
        ann_shape, cursors_nil, frames_nil,
        get_cm_step_def(), cm_annotation_step_def,
        cm_update_annotation_def, get_cm_task_type_ready_def(),
        cm_ann_cursors_def);
    vector_add(&rules, beta_norm(ispecl_rule(TERM_LIST(
        `condition:bool`,
        `\at:cm_task. cm_task_type_ready (p:cm_program) at
          (result_ann:cm_annotation)`,
        `yes_task:cm_task`, `no_task:cm_task`),
        get_theorem_by_name("COND_RAND"))));
    vector_add(&rules, get_theorem_by_name("COND_ID"));
    thm target_view = apply_conversion(
        reduce_rewrite_conv(rules), goal_ccl(cursor_cases[0]->g));
    ACCEPT_TAC(cursor_cases[0], eqt_elim_rule(target_view));
  }
  gnode cons = ASMP_EXISTS_TAC(cursor_cases[1], "Hcursors", NULL);
  cons = ASMP_EXISTS_TAC(cons, "Hcursors", NULL);
  thm cursors_cons = assume_rule(goal_lasmps(cons->g)[
      labeled_term_list_index(goal_lasmps(cons->g), "Hcursors")].tm);
  term cursor = cm_tstep_app_arg_from_right(rhs_of(cursors_cons), 1);
  gnode_list cursor_shapes = DISJ_CASES_TAC(cons,
      ispec_rule(cursor, get_datatype_cases("cm_acursor")), "Hcursor");
  gnode cursor_branch = cursor_shapes[0];
  while (is_exists(goal_lasmps(cursor_branch->g)[
      labeled_term_list_index(
        goal_lasmps(cursor_branch->g), "Hcursor")].tm)) {
    cursor_branch = ASMP_EXISTS_TAC(cursor_branch, "Hcursor", NULL);
  }
  thm cursor_shape = assume_rule(goal_lasmps(cursor_branch->g)[
      labeled_term_list_index(
        goal_lasmps(cursor_branch->g), "Hcursor")].tm);
  thm full_shape = conv_rule(rewrite_conv(THM_LIST(
      cursors_cons, cursor_shape)), ann_shape);
  term shaped_ann = rhs_of(full_shape);
  term phase = cm_tstep_constructor_arg(rhs_of(cursor_shape), 4, 0);
  term pc = cm_tstep_constructor_arg(shaped_ann, 8, 0);
  term temp = cm_tstep_constructor_arg(shaped_ann, 8, 1);
  term breakpc = cm_tstep_constructor_arg(shaped_ann, 8, 2);
  term continuepc = cm_tstep_constructor_arg(shaped_ann, 8, 3);
  term owner = cm_tstep_constructor_arg(rhs_of(cursor_shape), 4, 1);
  term owner_break = cm_tstep_constructor_arg(rhs_of(cursor_shape), 4, 2);
  term owner_continue = cm_tstep_constructor_arg(rhs_of(cursor_shape), 4, 3);
  term rest = cm_tstep_app_arg_from_right(rhs_of(cursors_cons), 0);
  term spills = cm_tstep_constructor_arg(shaped_ann, 8, 5);
  term saved = cm_tstep_constructor_arg(shaped_ann, 8, 6);
  term calls = cm_tstep_constructor_arg(shaped_ann, 8, 7);
  thm shaped_erases = conv_rule(rewrite_conv(THM_LIST(
      full_shape)), assume_rule(
        `cm_annotation_erases ${task:cm_task} (ann:cm_annotation)`));
  thm frames_equal = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_annotation_erases_def, cm_ann_cursors_def,
      cm_cursor_frames_def, cm_cursor_phase_def)),
      shaped_erases);
  thm frames_rewrite = gsym_rule(frames_equal);
  thm_list task_shape_rules = THM_LIST(full_shape, frames_rewrite);
  thm cursor_fid_ready = conv_rule(reduce_rewrite_conv(THM_LIST(
      full_shape, cm_task_phase_fid_ready_def,
      cm_cursors_fid_ready_def, cm_ann_cursors_def,
      cm_cursor_frames_def, cm_frames_fid_ready_def)),
      assume_rule(
        `cm_task_phase_fid_ready (p:cm_program) ${task:cm_task}
          (ann:cm_annotation)`));
  thm fid_ready = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_cursor_phase_def)), match_mp_rule(
        get_cm_phase_frame_fid_ready(),
        conjunct1_rule(cursor_fid_ready)));
  thm result = specl_rule(TERM_LIST(
      `p:cm_program`, `q:cm_program`, `fid:int`,
      `control:cm_control`, `st:cm_src_state`,
      `cm_cursor_frames ${rest:(cm_acursor)list}`,
      pc, temp, breakpc, continuepc, phase, owner, owner_break,
      owner_continue, rest, spills, saved, calls),
      cm_c_type_ready_step_at);
  result = match_mp_rule(result,
      assume_rule(`cm_typed_program (p:cm_program)`));
  result = match_mp_rule(result, fid_ready);
  result = match_mp_rule(result, conv_rule(rewrite_conv(task_shape_rules),
      assume_rule(
        `cm_task_type_ready (p:cm_program) ${task:cm_task}
          (ann:cm_annotation)`)));
  cm_tstep_accept(cursor_branch, task_shape_rules, result);
  return gnode_prove(root);
}
PROOF static thm cm_c_type_ready_step =
    cm_prove_c_type_ready_step();

PROOF static thm cm_prove_task_type_ready_step(void) {
  term typed = `cm_typed_program (p:cm_program)`;
  term erases = `cm_annotation_erases
      (task:cm_task) (ann:cm_annotation)`;
  term layout = `cm_task_layout_ready
      (p:cm_program) (task:cm_task) (ann:cm_annotation)`;
  term ready = `cm_task_type_ready
      (p:cm_program) (task:cm_task) (ann:cm_annotation)`;
  term source_fid_ready = `cm_task_fid_ready
      (p:cm_program) (task:cm_task)`;
  term succeeds = `cm_task_succeeds (task:cm_task)`;
  term target = `cm_task_type_ready (p:cm_program)
      (cm_step (task:cm_task))
      (cm_update_annotation
        (cm_annotation_step task (ann:cm_annotation)))`;
  term body = imp_chain(TERM_LIST(
      typed, erases, layout, ready, source_fid_ready, succeeds), target);
  gnode root = gnode_new_with_ccl(
      list_mk_forall(free_vars(body), body));
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list cases = DISJ_CASES_TAC(introduced,
      ispec_rule(`task:cm_task`, get_datatype_cases("cm_task")),
      "Htask");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode branch = cases[i];
    while (is_exists(goal_lasmps(branch->g)[
        labeled_term_list_index(goal_lasmps(branch->g), "Htask")].tm)) {
      branch = ASMP_EXISTS_TAC(branch, "Htask", NULL);
    }
    thm shape = assume_rule(goal_lasmps(branch->g)[
        labeled_term_list_index(goal_lasmps(branch->g), "Htask")].tm);
    term concrete = rhs_of(shape);
    thm shaped_erases = conv_rule(rewrite_conv(THM_LIST(shape)),
        assume_rule(erases));
    thm shaped_layout = conv_rule(rewrite_conv(THM_LIST(shape)),
        assume_rule(layout));
    thm shaped_ready = conv_rule(rewrite_conv(THM_LIST(shape)),
        assume_rule(ready));
    thm phase_fid_ready = match_mp_rule(match_mp_rule(
        get_cm_task_phase_fid_ready_from_source(),
        assume_rule(erases)), assume_rule(source_fid_ready));
    thm shaped_fid = conv_rule(rewrite_conv(THM_LIST(shape)),
        phase_fid_ready);
    thm shaped_succeeds = conv_rule(rewrite_conv(THM_LIST(shape)),
        assume_rule(succeeds));
    thm result = empty_theorem;
    if (i == 0) {
      term q = cm_tstep_constructor_arg(concrete, 2, 0);
      term input = cm_tstep_constructor_arg(concrete, 2, 1);
      result = specl_rule(TERM_LIST(
          `p:cm_program`, q, input, `ann:cm_annotation`),
          cm_start_type_ready_step);
      result = match_mp_rule(result, assume_rule(typed));
      result = match_mp_rule(result, shaped_layout);
    } else if (i == 1) {
      term q = cm_tstep_constructor_arg(concrete, 5, 0);
      term fid = cm_tstep_constructor_arg(concrete, 5, 1);
      term expr = cm_tstep_constructor_arg(concrete, 5, 2);
      term st = cm_tstep_constructor_arg(concrete, 5, 3);
      term ks = cm_tstep_constructor_arg(concrete, 5, 4);
      result = specl_rule(TERM_LIST(
          `p:cm_program`, q, fid, expr, st, ks, `ann:cm_annotation`),
          cm_r_type_ready_step);
      result = match_mp_rule(result, assume_rule(typed));
      result = match_mp_rule(result, shaped_succeeds);
      result = match_mp_rule(result, shaped_erases);
      result = match_mp_rule(result, shaped_ready);
    } else if (i == 2) {
      term q = cm_tstep_constructor_arg(concrete, 5, 0);
      term fid = cm_tstep_constructor_arg(concrete, 5, 1);
      term expr = cm_tstep_constructor_arg(concrete, 5, 2);
      term st = cm_tstep_constructor_arg(concrete, 5, 3);
      term ks = cm_tstep_constructor_arg(concrete, 5, 4);
      result = specl_rule(TERM_LIST(
          expr, `p:cm_program`, q, fid, st, ks, `ann:cm_annotation`),
          cm_l_type_ready_step);
      result = match_mp_rule(result, assume_rule(typed));
      result = match_mp_rule(result, shaped_succeeds);
      result = match_mp_rule(result, shaped_ready);
    } else if (i == 3) {
      term q = cm_tstep_constructor_arg(concrete, 5, 0);
      term fid = cm_tstep_constructor_arg(concrete, 5, 1);
      term stmt = cm_tstep_constructor_arg(concrete, 5, 2);
      term st = cm_tstep_constructor_arg(concrete, 5, 3);
      term ks = cm_tstep_constructor_arg(concrete, 5, 4);
      result = specl_rule(TERM_LIST(
          `p:cm_program`, q, fid, stmt, st, ks, `ann:cm_annotation`),
          cm_s_type_ready_step);
      result = match_mp_rule(result, assume_rule(typed));
      result = match_mp_rule(result, shaped_succeeds);
      result = match_mp_rule(result, shaped_erases);
      result = match_mp_rule(result, shaped_ready);
    } else if (i == 4) {
      term q = cm_tstep_constructor_arg(concrete, 5, 0);
      term fid = cm_tstep_constructor_arg(concrete, 5, 1);
      term incoming = cm_tstep_constructor_arg(concrete, 5, 2);
      term st = cm_tstep_constructor_arg(concrete, 5, 3);
      term ks = cm_tstep_constructor_arg(concrete, 5, 4);
      result = specl_rule(TERM_LIST(
          `p:cm_program`, q, fid, incoming, st, ks,
          `ann:cm_annotation`), cm_v_type_ready_step);
      result = match_mp_rule(result, assume_rule(typed));
      result = match_mp_rule(result, shaped_erases);
      result = match_mp_rule(result, shaped_ready);
      result = match_mp_rule(result, shaped_fid);
    } else if (i == 5) {
      term q = cm_tstep_constructor_arg(concrete, 5, 0);
      term fid = cm_tstep_constructor_arg(concrete, 5, 1);
      term control = cm_tstep_constructor_arg(concrete, 5, 2);
      term st = cm_tstep_constructor_arg(concrete, 5, 3);
      term ks = cm_tstep_constructor_arg(concrete, 5, 4);
      result = specl_rule(TERM_LIST(
          `p:cm_program`, q, fid, control, st, ks,
          `ann:cm_annotation`), cm_c_type_ready_step);
      result = match_mp_rule(result, assume_rule(typed));
      result = match_mp_rule(result, shaped_erases);
      result = match_mp_rule(result, shaped_ready);
      result = match_mp_rule(result, shaped_fid);
    } else {
      thm_list rules = THM_LIST(
          shape, get_cm_step_def(), cm_annotation_step_def,
          cm_update_annotation_def, get_cm_task_type_ready_def());
      thm target_view = apply_conversion(
          reduce_rewrite_conv(rules), goal_ccl(branch->g));
      ACCEPT_TAC(branch, eqt_elim_rule(target_view));
      continue;
    }
    cm_tstep_accept(branch, THM_LIST(shape), result);
  }
  return gnode_prove(root);
}
PROOF thm cm_task_type_ready_step =
    cm_prove_task_type_ready_step();

PROOF thm get_cm_task_type_ready_step(void) {
  return cm_task_type_ready_step;
}

PROOF static int cmc_preservation_type_step_final_checks(void) {
  ENSURE_COND(vector_size(hyp(cm_start_type_ready_step)) == 0 &&
      vector_size(hyp(cm_v_type_ready_step)) == 0 &&
      vector_size(hyp(cm_c_type_ready_step)) == 0 &&
      vector_size(hyp(cm_task_type_ready_step)) == 0,
      "aggregate type-step theorem has assumptions");
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_type_step_axioms_before,
      "cmc_preservation_type_step introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_type_step_checks =
    cmc_preservation_type_step_final_checks();
