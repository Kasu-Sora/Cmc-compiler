#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_runtime_ready.h"
#include "cmc_preservation_fid.h"
#include "cmc_preservation_budget_defs.h"
#include "cmc_preservation_budget_ready.h"
#include "cmc_preservation_source_ready.h"
#include "cmc_preservation_type_ready.h"
#include "cmc_preservation_code_task.h"
#include "cmc_preservation_invariant_transition.h"

#require "cmc_preservation_source_ready.c"
#require "cmc_preservation_budget_ready.c"
#require "cmc_preservation_fid.c"
#require "cmc_preservation_type_ready.c"
#require "cmc_preservation_code_task.c"

PROOF static size_t _cmc_preservation_runtime_ready_axioms_before =
    vector_size(get_all_axioms());

PROOF static term cm_rr_app_arg_from_right(
    term application, size_t offset) {
  for (size_t i = 0; i < offset; ++i) {
    application = dest_comb(application).tm1;
  }
  return dest_comb(application).tm2;
}

PROOF static term cm_rr_constructor_arg(
    term constructor, size_t arity, size_t index) {
  return cm_rr_app_arg_from_right(
      constructor, arity - index - 1);
}

PROOF static thm cm_rr_named_shape(
    gnode *node, const char *label) {
  while (true) {
    labeled_term_list assumptions = goal_lasmps((*node)->g);
    int index = labeled_term_list_index(assumptions, label);
    if (!is_exists(assumptions[index].tm)) {
      return assume_rule(assumptions[index].tm);
    }
    *node = ASMP_EXISTS_TAC(*node, label, NULL);
  }
}

PROOF static thm cm_rr_pick_conjunct(thm source, term wanted) {
  if (alpha_compare(concl(source), wanted) == 0) return source;
  if (!is_conj(concl(source))) return empty_theorem;
  thm left = cm_rr_pick_conjunct(conjunct1_rule(source), wanted);
  if (!IS_NULL(left)) return left;
  return cm_rr_pick_conjunct(conjunct2_rule(source), wanted);
}

PROOF static thm cm_prove_cursors_fid_head_ready(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (cursors:(cm_acursor)list).
         cm_cursors_fid_ready p fid cursors ==>
         ~(cursors == []) ==>
         cm_phase_is_halt (cm_cursor_phase (HD cursors)) ||
         0i <= fid`);
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list cases = DISJ_CASES_TAC(introduced,
      ispec_rule(`cursors:(cm_acursor)list`,
        get_theorem_by_name("list_CASES")),
      "Hrr_cursors");
  {
    gnode nil = cases[0];
    thm nil_shape = cm_rr_named_shape(&nil, "Hrr_cursors");
    thm impossible = conv_rule(reduce_rewrite_conv(THM_LIST(
        nil_shape)), assume_rule(
          `~((cursors:(cm_acursor)list) == [])`));
    CONTR_TAC(nil, impossible);
  }
  gnode cons = cases[1];
  thm cons_shape = cm_rr_named_shape(&cons, "Hrr_cursors");
  term cursor = cm_rr_app_arg_from_right(rhs_of(cons_shape), 1);
  thm opened = conv_rule(reduce_rewrite_conv(THM_LIST(
      cons_shape, cm_cursors_fid_ready_def,
      cm_cursor_frames_def, cm_frames_fid_ready_def)),
      assume_rule(
        `cm_cursors_fid_ready (p:cm_program) (fid:int)
          (cursors:(cm_acursor)list)`));
  thm frame_ready = conjunct1_rule(opened);
  thm phase_ready = match_mp_rule(specl_rule(TERM_LIST(
      `cm_cursor_phase ${cursor:cm_acursor}`,
      `fid:int`, `p:cm_program`),
      cm_phase_frame_fid_ready), frame_ready);
  thm weakened = mp_rule(taut_rule(mk_imp(concl(phase_ready),
      `cm_phase_is_halt
         (cm_cursor_phase ${cursor:cm_acursor}) ||
       0i <= (fid:int)`)), phase_ready);
  gnode reduced = CONV_TAC(cons,
      reduce_rewrite_conv(THM_LIST(
        cons_shape, get_theorem_by_name("HD"))));
  ACCEPT_TAC(reduced, weakened);
  return gnode_prove(root);
}
PROOF static thm cm_cursors_fid_head_ready =
    cm_prove_cursors_fid_head_ready();

PROOF static thm cm_prove_task_v_fid_condition(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (q:cm_program) (fid:int) (v:cm_value)
         (st:cm_src_state) (ks:(cm_frame)list)
         (ann:cm_annotation).
         cm_task_fid_ready p (CMVTask q fid v st ks) ==>
         cm_annotation_erases (CMVTask q fid v st ks) ann ==>
         (~(cm_ann_cursors ann == []) ==>
          cm_phase_is_halt
            (cm_cursor_phase (HD (cm_ann_cursors ann))) ||
          0i <= fid)`);
  gnode introduced = AUTO_INTROS_TAC(root);
  term task = `CMVTask (q:cm_program) (fid:int) (v:cm_value)
      (st:cm_src_state) (ks:(cm_frame)list)`;
  thm phase_ready = match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(
        `p:cm_program`, task, `ann:cm_annotation`),
        cm_task_phase_fid_ready_from_source),
      assume_rule(
        `cm_annotation_erases ${task:cm_task}
          (ann:cm_annotation)`)),
      assume_rule(
        `cm_task_fid_ready (p:cm_program) ${task:cm_task}`));
  thm cursors_ready = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_task_phase_fid_ready_def)), phase_ready);
  thm result = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`,
      `cm_ann_cursors (ann:cm_annotation)`),
      cm_cursors_fid_head_ready);
  result = match_mp_rule(result, cursors_ready);
  ACCEPT_TAC(introduced, mp_rule(result,
      assume_rule(`~(cm_ann_cursors (ann:cm_annotation) == [])`)));
  return gnode_prove(root);
}
PROOF static thm cm_task_v_fid_condition =
    cm_prove_task_v_fid_condition();

PROOF static void cm_rr_accept(
    gnode branch, thm result, thm_list shapes) {
  thm normalized = conv_rule(rewrite_conv(shapes), result);
  thm target_view = apply_conversion(
      rewrite_conv(shapes), goal_ccl(branch->g));
  ACCEPT_TAC(branch, eq_mp_rule(sym_rule(target_view), normalized));
}

PROOF static thm cm_prove_invariants_runtime_step_ready(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (task:cm_task) (ann:cm_annotation).
         cm_typed_program p ==>
         cm_task_type_ready p task ann ==>
         cm_task_coordinate_ready p task ann ==>
         cm_task_layout_ready p task ann ==>
         cm_task_budget p task ann ==>
         cm_task_fid_ready p task ==>
         cm_task_succeeds task ==>
         cm_annotation_erases task ann ==>
         cm_task_short_ready task ==>
         cm_runtime_step_ready p task ann`);
  gnode introduced = AUTO_INTROS_TAC(root);
  thm typed = assume_rule(`cm_typed_program (p:cm_program)`);
  thm layout = assume_rule(
      `cm_task_layout_ready (p:cm_program)
        (task:cm_task) (ann:cm_annotation)`);
  gnode_list cases = DISJ_CASES_TAC(introduced,
      ispec_rule(`task:cm_task`, get_datatype_cases("cm_task")),
      "Hrr_task");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode branch = cases[i];
    thm task_shape = cm_rr_named_shape(&branch, "Hrr_task");
    term concrete_task = rhs_of(task_shape);
    thm_list shapes = THM_LIST(task_shape);
    thm shaped_layout = conv_rule(
        rewrite_conv(THM_LIST(task_shape)), layout);
    thm opened_layout = conv_rule(reduce_rewrite_conv(THM_LIST(
        cm_task_layout_ready_def)), shaped_layout);
    if (i == 6) {
      thm target_view = apply_conversion(
          reduce_rewrite_conv(THM_LIST(
            task_shape, cm_runtime_step_ready_def)),
          goal_ccl(branch->g));
      ACCEPT_TAC(branch, eqt_elim_rule(target_view));
      continue;
    }
    thm program_eq = conjunct1_rule(opened_layout);
    vector_add(&shapes, program_eq);
    thm rooted_layout = conv_rule(rewrite_conv(THM_LIST(program_eq)),
        shaped_layout);
    if (i == 0) {
      thm body = conj_rule(typed, rooted_layout);
      cm_rr_accept(branch, body, THM_LIST(
          task_shape, program_eq, cm_runtime_step_ready_def));
      continue;
    }
    term fid = cm_rr_constructor_arg(concrete_task, 5, 1);
    thm shaped_type = conv_rule(reduce_rewrite_conv(THM_LIST(
        task_shape, program_eq, get_cm_task_type_ready_def())),
        assume_rule(
          `cm_task_type_ready (p:cm_program)
            (task:cm_task) (ann:cm_annotation)`));
    if (i == 1 || i == 2 || i == 3) {
      thm fid_low = cm_rr_pick_conjunct(shaped_type,
          `0i <= ${fid:int}`);
      thm body = i == 3
          ? conj_rule(typed, conj_rule(fid_low, rooted_layout))
          : conj_rule(fid_low, rooted_layout);
      cm_rr_accept(branch, body, THM_LIST(
          task_shape, program_eq, cm_runtime_step_ready_def));
      continue;
    }
    if (i == 5) {
      cm_rr_accept(branch, rooted_layout, THM_LIST(
          task_shape, program_eq, cm_runtime_step_ready_def));
      continue;
    }
    term val = cm_rr_constructor_arg(concrete_task, 5, 2);
    term st = cm_rr_constructor_arg(concrete_task, 5, 3);
    term ks = cm_rr_constructor_arg(concrete_task, 5, 4);
    thm rooted_coordinate = conv_rule(rewrite_conv(shapes),
        assume_rule(
          `cm_task_coordinate_ready (p:cm_program)
            (task:cm_task) (ann:cm_annotation)`));
    thm rooted_budget = conv_rule(rewrite_conv(shapes),
        assume_rule(
          `cm_task_budget (p:cm_program)
            (task:cm_task) (ann:cm_annotation)`));
    thm rooted_fid = conv_rule(rewrite_conv(shapes),
        assume_rule(
          `cm_task_fid_ready (p:cm_program) (task:cm_task)`));
    thm rooted_succeeds = conv_rule(rewrite_conv(shapes),
        assume_rule(`cm_task_succeeds (task:cm_task)`));
    thm rooted_erases = conv_rule(rewrite_conv(shapes),
        assume_rule(
          `cm_annotation_erases (task:cm_task)
            (ann:cm_annotation)`));
    thm rooted_short = conv_rule(rewrite_conv(shapes),
        assume_rule(`cm_task_short_ready (task:cm_task)`));
    thm fid_condition = specl_rule(TERM_LIST(
        `p:cm_program`, `p:cm_program`, fid, val, st, ks,
        `ann:cm_annotation`), cm_task_v_fid_condition);
    fid_condition = match_mp_rule(fid_condition, rooted_fid);
    fid_condition = match_mp_rule(fid_condition, rooted_erases);
    thm spill_condition = specl_rule(TERM_LIST(
        `p:cm_program`, fid, val, st, ks,
        `ann:cm_annotation`), cm_task_budget_v_spill_ready);
    spill_condition = match_mp_rule(
        match_mp_rule(spill_condition, rooted_coordinate),
        rooted_budget);
    thm source_condition = specl_rule(TERM_LIST(
        `p:cm_program`, fid, val, st, ks,
        `ann:cm_annotation`), cm_task_v_source_ready);
    source_condition = match_mp_rule(source_condition, rooted_succeeds);
    source_condition = match_mp_rule(source_condition, rooted_erases);
    source_condition = match_mp_rule(source_condition, rooted_short);
    thm body = conj_rule(rooted_layout,
        conj_rule(fid_condition,
          conj_rule(spill_condition, source_condition)));
    cm_rr_accept(branch, body, THM_LIST(
        task_shape, program_eq, cm_runtime_step_ready_def));
  }
  return gnode_prove(root);
}
PROOF thm cm_invariants_runtime_step_ready =
    cm_prove_invariants_runtime_step_ready();

PROOF static int cmc_preservation_runtime_ready_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_runtime_ready_axioms_before,
      "cmc_preservation_runtime_ready introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_runtime_ready_checks =
    cmc_preservation_runtime_ready_final_checks();
