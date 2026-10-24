#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_source_ready.h"
#include "cmc_preservation_short_defs.h"
#include "cmc_preservation_source_conditions.h"
#include "cmc_preservation_invariant_transition.h"

#require "cmc_preservation_short_step.c"
#require "cmc_preservation_source_conditions.c"

PROOF static size_t _cmc_preservation_source_ready_axioms_before =
    vector_size(get_all_axioms());

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

PROOF static thm cm_sr_named_shape(
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

PROOF static thm cm_sr_consequence(thm given, term wanted) {
  return mp_rule(taut_rule(mk_imp(concl(given), wanted)), given);
}

PROOF static term cm_sr_runtime_annotation(term phase) {
  return `CMAnnotation (pc:int) (temp:int) (breakpc:int)
    (continuepc:int)
    (CMACursor ${phase:cm_aphase} (owner:int)
       (saved_break:int) (saved_continue:int) ::
     (rest:(cm_acursor)list))
    (spills:(cm_spill)list) (saved:(cm_spill_frame)list)
    (calls:(cm_call_sim_frame)list)`;
}

PROOF static thm cm_prove_task_v_source_ready_phase(void) {
  term phase = `phase:cm_aphase`;
  term ann = cm_sr_runtime_annotation(phase);
  term task =
      `CMVTask (p:cm_program) (fid:int) (v:cm_value)
        (st:cm_src_state) (ks:(cm_frame)list)`;
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (v:cm_value)
         (st:cm_src_state) (ks:(cm_frame)list)
         (pc:int) (temp:int) (breakpc:int) (continuepc:int)
         (phase:cm_aphase) (owner:int)
         (saved_break:int) (saved_continue:int)
         (rest:(cm_acursor)list) (spills:(cm_spill)list)
         (saved:(cm_spill_frame)list)
         (calls:(cm_call_sim_frame)list).
         cm_task_succeeds (CMVTask p fid v st ks) ==>
         cm_annotation_erases
           (CMVTask p fid v st ks)
           (CMAnnotation pc temp breakpc continuepc
             (CMACursor phase owner saved_break saved_continue :: rest)
             spills saved calls) ==>
         cm_task_short_ready (CMVTask p fid v st ks) ==>
         cm_v_source_ready p fid st phase`);
  gnode introduced = AUTO_INTROS_TAC(root);
  thm succeeds = assume_rule(
      `cm_task_succeeds ${task:cm_task}`);
  thm erases = assume_rule(
      `cm_annotation_erases ${task:cm_task} ${ann:cm_annotation}`);
  thm frames_eq = conv_rule(reduce_rewrite_conv(THM_LIST(
      cm_annotation_erases_def, cm_ann_cursors_def,
      cm_cursor_frames_def, cm_cursor_phase_def)), erases);
  thm old_ready = assume_rule(
      `cm_task_short_ready ${task:cm_task}`);
  gnode opened = CONV_TAC(introduced,
      rewrite_conv(THM_LIST(cm_v_source_ready_def)));
  gnode_list properties = CONJ_TAC(opened);
  {
    gnode init_case = GEN_TAC(properties[0], "slot");
    init_case = DISCH_TAC(init_case, "Hsr_init_phase");
    thm phase_eq = assume_rule(
        `(phase:cm_aphase) == CAInitP (slot:int)`);
    thm shaped_succeeds = conv_rule(rewrite_conv(THM_LIST(
        sym_rule(frames_eq), phase_eq, cm_phase_frame_def)),
        succeeds);
    thm result = specl_rule(TERM_LIST(
        `p:cm_program`, `fid:int`, `v:cm_value`,
        `st:cm_src_state`, `slot:int`,
        `cm_cursor_frames (rest:(cm_acursor)list)`),
        cm_v_init_succeeds_store);
    ACCEPT_TAC(init_case, match_mp_rule(result, shaped_succeeds));
  }
  {
    gnode binary_case = GEN_TAC(properties[1], "op");
    binary_case = GEN_TAC(binary_case, "left");
    binary_case = GEN_TAC(binary_case, "right");
    binary_case = GEN_TAC(binary_case, "left_value");
    binary_case = GEN_TAC(binary_case, "ty");
    binary_case = DISCH_TAC(binary_case, "Hsr_binary_phase");
    thm phase_eq = assume_rule(
        `(phase:cm_aphase) ==
         CABinRP (op:int) (left:cm_expr) (right:cm_expr)
           (left_value:cm_value) (ty:cm_type)`);
    thm shaped_ready = conv_rule(reduce_rewrite_conv(THM_LIST(
        sym_rule(frames_eq), phase_eq,
        cm_task_short_ready_def, cm_frames_short_ready_def,
        cm_frame_short_ready_def, cm_phase_frame_def)),
        old_ready);
    ACCEPT_TAC(binary_case, cm_sr_consequence(shaped_ready,
        `(op == 0i ==> ~cm_truth (st:cm_src_state)
             (left_value:cm_value)) &&
         (op == 1i ==> cm_truth st left_value)`));
  }
  return gnode_prove(root);
}
PROOF static thm cm_task_v_source_ready_phase =
    cm_prove_task_v_source_ready_phase();

PROOF static thm cm_prove_task_v_source_ready(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (v:cm_value)
         (st:cm_src_state) (ks:(cm_frame)list)
         (ann:cm_annotation).
         cm_task_succeeds (CMVTask p fid v st ks) ==>
         cm_annotation_erases (CMVTask p fid v st ks) ann ==>
         cm_task_short_ready (CMVTask p fid v st ks) ==>
         ~(cm_ann_cursors ann == []) ==>
         cm_v_source_ready p fid st
           (cm_cursor_phase (HD (cm_ann_cursors ann)))`);
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list ann_cases = DISJ_CASES_TAC(introduced,
      ispec_rule(`ann:cm_annotation`,
        get_datatype_cases("cm_annotation")),
      "Hsr_ann");
  gnode branch = ann_cases[0];
  thm ann_shape = cm_sr_named_shape(&branch, "Hsr_ann");
  term cursors = cm_sr_constructor_arg(rhs_of(ann_shape), 8, 4);
  gnode_list cursor_cases = DISJ_CASES_TAC(branch,
      ispec_rule(cursors, get_theorem_by_name("list_CASES")),
      "Hsr_cursors");
  {
    gnode nil = cursor_cases[0];
    thm cursors_nil = cm_sr_named_shape(&nil, "Hsr_cursors");
    thm impossible = conv_rule(reduce_rewrite_conv(THM_LIST(
        ann_shape, cursors_nil, cm_ann_cursors_def)),
        assume_rule(`~(cm_ann_cursors (ann:cm_annotation) == [])`));
    CONTR_TAC(nil, impossible);
  }
  gnode cons = cursor_cases[1];
  thm cursors_cons = cm_sr_named_shape(&cons, "Hsr_cursors");
  term cursor = cm_sr_app_arg_from_right(rhs_of(cursors_cons), 1);
  gnode_list cursor_shapes = DISJ_CASES_TAC(cons,
      ispec_rule(cursor, get_datatype_cases("cm_acursor")),
      "Hsr_cursor");
  gnode cursor_branch = cursor_shapes[0];
  thm cursor_shape = cm_sr_named_shape(&cursor_branch, "Hsr_cursor");
  thm full_shape = conv_rule(rewrite_conv(THM_LIST(
      cursors_cons, cursor_shape)), ann_shape);
  term shaped_ann = rhs_of(full_shape);
  term pc_value = cm_sr_constructor_arg(shaped_ann, 8, 0);
  term temp_value = cm_sr_constructor_arg(shaped_ann, 8, 1);
  term break_value = cm_sr_constructor_arg(shaped_ann, 8, 2);
  term continue_value = cm_sr_constructor_arg(shaped_ann, 8, 3);
  term spills_value = cm_sr_constructor_arg(shaped_ann, 8, 5);
  term saved_value = cm_sr_constructor_arg(shaped_ann, 8, 6);
  term calls_value = cm_sr_constructor_arg(shaped_ann, 8, 7);
  term shaped_cursor = rhs_of(cursor_shape);
  term phase_value = cm_sr_constructor_arg(shaped_cursor, 4, 0);
  term owner_value = cm_sr_constructor_arg(shaped_cursor, 4, 1);
  term owner_break_value = cm_sr_constructor_arg(shaped_cursor, 4, 2);
  term owner_continue_value = cm_sr_constructor_arg(shaped_cursor, 4, 3);
  term rest_value = cm_sr_app_arg_from_right(
      rhs_of(cursors_cons), 0);
  thm result = specl_rule(TERM_LIST(
      `p:cm_program`, `fid:int`, `v:cm_value`,
      `st:cm_src_state`, `ks:(cm_frame)list`,
      pc_value, temp_value, break_value, continue_value,
      phase_value, owner_value, owner_break_value,
      owner_continue_value, rest_value, spills_value,
      saved_value, calls_value), cm_task_v_source_ready_phase);
  thm_list premises = THM_LIST(
      assume_rule(
        `cm_task_succeeds
          (CMVTask (p:cm_program) (fid:int) (v:cm_value)
            (st:cm_src_state) (ks:(cm_frame)list))`),
      assume_rule(
        `cm_annotation_erases
          (CMVTask (p:cm_program) (fid:int) (v:cm_value)
            (st:cm_src_state) (ks:(cm_frame)list))
          (ann:cm_annotation)`),
      assume_rule(
        `cm_task_short_ready
          (CMVTask (p:cm_program) (fid:int) (v:cm_value)
            (st:cm_src_state) (ks:(cm_frame)list))`));
  for (size_t i = 0; i < vector_size(premises); ++i) {
    result = match_mp_rule(result, conv_rule(
        rewrite_conv(THM_LIST(full_shape)), premises[i]));
  }
  gnode reduced = CONV_TAC(cursor_branch,
      reduce_rewrite_conv(THM_LIST(
        full_shape, cm_ann_cursors_def, cm_cursor_phase_def,
        get_theorem_by_name("HD"))));
  ACCEPT_TAC(reduced, result);
  return gnode_prove(root);
}
PROOF thm cm_task_v_source_ready =
    cm_prove_task_v_source_ready();

PROOF static int cmc_preservation_source_ready_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_source_ready_axioms_before,
      "cmc_preservation_source_ready introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_source_ready_checks =
    cmc_preservation_source_ready_final_checks();
