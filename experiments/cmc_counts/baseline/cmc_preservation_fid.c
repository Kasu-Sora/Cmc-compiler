#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_fid.h"
#include "cmc_annotate_model.h"

#require "cmc_preservation_generation.c"

PROOF static size_t _cmc_preservation_fid_axioms_before =
    vector_size(get_all_axioms());

PROOF thm cm_frame_fid_ready_def = new_fun_definition(
    `cm_frame_fid_ready (p:cm_program) (fid:int) (frame:cm_frame) : bool =
       (if frame == CMHaltK
        then fid == --1i
        else 0i <= fid &&
             fid < ilength (cm_program_functions p))`);
PROOF static int _c_cm_frame_fid_ready =
    cst_add_const_to_header(`cm_frame_fid_ready`);

PROOF thm cm_frames_fid_ready_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(!p fid.
        cm_frames_fid_ready (p:cm_program) (fid:int)
          ([]:(cm_frame)list) = (fid == --1i)) &&
     (!p fid frame rest.
        cm_frames_fid_ready p fid
          ((frame:cm_frame) :: (rest:(cm_frame)list)) =
        (cm_frame_fid_ready p fid frame &&
         cm_frames_fid_ready p
           (cm_frame_parent_fid frame fid) rest))`);
PROOF static int _c_cm_frames_fid_ready =
    cst_add_const_to_header(`cm_frames_fid_ready`);

PROOF thm cm_task_fid_ready_def = new_rec_definition(
    get_cm_task_recursion(),
    `(!p q input.
        cm_task_fid_ready (p:cm_program)
          (CMStartTask (q:cm_program) (input:(int)list)) = T) &&
     (!p q fid expr st ks.
        cm_task_fid_ready p
          (CMRTask (q:cm_program) (fid:int) (expr:cm_expr)
            (st:cm_src_state) (ks:(cm_frame)list)) =
        cm_frames_fid_ready p fid ks) &&
     (!p q fid expr st ks.
        cm_task_fid_ready p
          (CMLTask (q:cm_program) (fid:int) (expr:cm_expr)
            (st:cm_src_state) (ks:(cm_frame)list)) =
        cm_frames_fid_ready p fid ks) &&
     (!p q fid stmt st ks.
        cm_task_fid_ready p
          (CMSTask (q:cm_program) (fid:int) (stmt:cm_stmt)
            (st:cm_src_state) (ks:(cm_frame)list)) =
        cm_frames_fid_ready p fid ks) &&
     (!p q fid incoming st ks.
        cm_task_fid_ready p
          (CMVTask (q:cm_program) (fid:int) (incoming:cm_value)
            (st:cm_src_state) (ks:(cm_frame)list)) =
        cm_frames_fid_ready p fid ks) &&
     (!p q fid control st ks.
        cm_task_fid_ready p
          (CMCTask (q:cm_program) (fid:int) (control:cm_control)
            (st:cm_src_state) (ks:(cm_frame)list)) =
        cm_frames_fid_ready p fid ks) &&
     (!p st control status.
        cm_task_fid_ready p
          (CMDoneTask (st:cm_src_state) (control:cm_control)
            (status:int)) = T)`);
PROOF static int _c_cm_task_fid_ready =
    cst_add_const_to_header(`cm_task_fid_ready`);

PROOF thm cm_cursors_fid_ready_def = new_fun_definition(
    `cm_cursors_fid_ready (p:cm_program) (fid:int)
       (cursors:(cm_acursor)list) : bool =
       cm_frames_fid_ready p fid (cm_cursor_frames cursors)`);
PROOF static int _c_cm_cursors_fid_ready =
    cst_add_const_to_header(`cm_cursors_fid_ready`);

PROOF thm cm_task_phase_fid_ready_def = new_rec_definition(
    get_cm_task_recursion(),
    `(!p q input ann.
        cm_task_phase_fid_ready (p:cm_program)
          (CMStartTask (q:cm_program) (input:(int)list))
          (ann:cm_annotation) =
        cm_cursors_fid_ready p (--1i) (cm_ann_cursors ann)) &&
     (!p q fid expr st ks ann.
        cm_task_phase_fid_ready p
          (CMRTask (q:cm_program) (fid:int) (expr:cm_expr)
            (st:cm_src_state) (ks:(cm_frame)list)) ann =
        cm_cursors_fid_ready p fid (cm_ann_cursors ann)) &&
     (!p q fid expr st ks ann.
        cm_task_phase_fid_ready p
          (CMLTask (q:cm_program) (fid:int) (expr:cm_expr)
            (st:cm_src_state) (ks:(cm_frame)list)) ann =
        cm_cursors_fid_ready p fid (cm_ann_cursors ann)) &&
     (!p q fid stmt st ks ann.
        cm_task_phase_fid_ready p
          (CMSTask (q:cm_program) (fid:int) (stmt:cm_stmt)
            (st:cm_src_state) (ks:(cm_frame)list)) ann =
        cm_cursors_fid_ready p fid (cm_ann_cursors ann)) &&
     (!p q fid incoming st ks ann.
        cm_task_phase_fid_ready p
          (CMVTask (q:cm_program) (fid:int) (incoming:cm_value)
            (st:cm_src_state) (ks:(cm_frame)list)) ann =
        cm_cursors_fid_ready p fid (cm_ann_cursors ann)) &&
     (!p q fid control st ks ann.
        cm_task_phase_fid_ready p
          (CMCTask (q:cm_program) (fid:int) (control:cm_control)
            (st:cm_src_state) (ks:(cm_frame)list)) ann =
        cm_cursors_fid_ready p fid (cm_ann_cursors ann)) &&
     (!p st control status ann.
        cm_task_phase_fid_ready p
          (CMDoneTask (st:cm_src_state) (control:cm_control)
            (status:int)) (ann:cm_annotation) =
        cm_cursors_fid_ready p (--1i) (cm_ann_cursors ann))`);
PROOF static int _c_cm_task_phase_fid_ready =
    cst_add_const_to_header(`cm_task_phase_fid_ready`);

PROOF static thm cm_prove_phase_frame_fid_ready(void) {
  term body =
      `cm_frame_fid_ready (p:cm_program) (fid:int)
         (cm_phase_frame (phase:cm_aphase)) ==>
       (cm_phase_is_halt phase ||
        (0i <= fid && fid < ilength (cm_program_functions p)))`;
  gnode root = gnode_new_with_ccl(
      list_mk_forall(free_vars(body), body));
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list cases = DISJ_CASES_TAC(introduced,
      ispec_rule(`phase:cm_aphase`, get_datatype_cases("cm_aphase")),
      "Hphase");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode branch = cases[i];
    while (is_exists(goal_lasmps(branch->g)[
        labeled_term_list_index(
          goal_lasmps(branch->g), "Hphase")].tm)) {
      branch = ASMP_EXISTS_TAC(branch, "Hphase", NULL);
    }
    thm shape = assume_rule(goal_lasmps(branch->g)[
        labeled_term_list_index(
          goal_lasmps(branch->g), "Hphase")].tm);
    thm premise = conv_rule(reduce_rewrite_conv(THM_LIST(
        shape, cm_frame_fid_ready_def, cm_phase_frame_def,
        get_datatype_distinctness("cm_frame"))),
        assume_rule(
          `cm_frame_fid_ready (p:cm_program) (fid:int)
            (cm_phase_frame (phase:cm_aphase))`));
    thm target_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
        shape, cm_phase_is_halt_def)), goal_ccl(branch->g));
    if (i == 0) {
      ACCEPT_TAC(branch, eqt_elim_rule(target_view));
    } else {
      ACCEPT_TAC(branch, eq_mp_rule(sym_rule(target_view), premise));
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_phase_frame_fid_ready =
    cm_prove_phase_frame_fid_ready();

PROOF static thm cm_prove_task_phase_fid_ready_from_source(void) {
  term erases =
      `cm_annotation_erases (task:cm_task) (ann:cm_annotation)`;
  term source =
      `cm_task_fid_ready (p:cm_program) (task:cm_task)`;
  term target =
      `cm_task_phase_fid_ready (p:cm_program)
        (task:cm_task) (ann:cm_annotation)`;
  term body = imp_chain(TERM_LIST(erases, source), target);
  gnode root = gnode_new_with_ccl(
      list_mk_forall(free_vars(body), body));
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list cases = DISJ_CASES_TAC(introduced,
      ispec_rule(`task:cm_task`, get_datatype_cases("cm_task")),
      "Htask");
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode branch = cases[i];
    while (is_exists(goal_lasmps(branch->g)[
        labeled_term_list_index(
          goal_lasmps(branch->g), "Htask")].tm)) {
      branch = ASMP_EXISTS_TAC(branch, "Htask", NULL);
    }
    thm shape = assume_rule(goal_lasmps(branch->g)[
        labeled_term_list_index(
          goal_lasmps(branch->g), "Htask")].tm);
    thm erases_fact = conv_rule(reduce_rewrite_conv(THM_LIST(
        shape, cm_annotation_erases_def)), assume_rule(erases));
    thm source_fact = conv_rule(reduce_rewrite_conv(THM_LIST(
        shape, cm_task_fid_ready_def)), assume_rule(source));
    thm target_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
        shape, cm_task_phase_fid_ready_def,
        cm_cursors_fid_ready_def, cm_ann_cursors_def,
        cm_cursor_frames_def, cm_frames_fid_ready_def,
        erases_fact)), goal_ccl(branch->g));
    if (i == 0 || i == 6) {
      ACCEPT_TAC(branch, eqt_elim_rule(target_view));
    } else {
      ACCEPT_TAC(branch,
          eq_mp_rule(sym_rule(target_view), source_fact));
    }
  }
  return gnode_prove(root);
}
PROOF thm cm_task_phase_fid_ready_from_source =
    cm_prove_task_phase_fid_ready_from_source();

PROOF thm get_cm_frame_fid_ready_def(void) {
  return cm_frame_fid_ready_def;
}
PROOF thm get_cm_frames_fid_ready_def(void) {
  return cm_frames_fid_ready_def;
}
PROOF thm get_cm_task_fid_ready_def(void) {
  return cm_task_fid_ready_def;
}
PROOF thm get_cm_cursors_fid_ready_def(void) {
  return cm_cursors_fid_ready_def;
}
PROOF thm get_cm_task_phase_fid_ready_def(void) {
  return cm_task_phase_fid_ready_def;
}
PROOF thm get_cm_phase_frame_fid_ready(void) {
  return cm_phase_frame_fid_ready;
}
PROOF thm get_cm_task_phase_fid_ready_from_source(void) {
  return cm_task_phase_fid_ready_from_source;
}

PROOF static int cmc_preservation_fid_final_checks(void) {
  ENSURE_COND(vector_size(hyp(cm_phase_frame_fid_ready)) == 0 &&
      vector_size(hyp(cm_task_phase_fid_ready_from_source)) == 0,
      "function-context theorem has assumptions");
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_fid_axioms_before,
      "cmc_preservation_fid introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_fid_checks =
    cmc_preservation_fid_final_checks();
