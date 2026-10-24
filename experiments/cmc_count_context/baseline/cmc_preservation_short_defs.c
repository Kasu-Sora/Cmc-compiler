#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "userlib/proof_patterns.h"
#include "cmc_preservation_short_defs.h"
#include "cmc_preservation_generation.h"
#include "cmc_preservation_call_value.h"

#require "userlib/proof_patterns.c"
#require "cmc_preservation_generation.c"
#require "cmc_preservation_call_value.c"

PROOF static size_t _cmc_preservation_short_defs_axioms_before =
    vector_size(get_all_axioms());

PROOF thm cm_frame_short_ready_def = new_rec_definition(
    get_cm_frame_recursion(),
    `(cm_frame_short_ready (st:cm_src_state) CMHaltK = T) &&
     (!st ty. cm_frame_short_ready st (CMLoadK (ty:cm_type)) = T) &&
     (!st src ty. cm_frame_short_ready st
        (CMAssignLK (src:cm_expr) (ty:cm_type)) = T) &&
     (!st ptr ty. cm_frame_short_ready st
        (CMAssignRK (ptr:cm_value) (ty:cm_type)) = T) &&
     (!st op right ty. cm_frame_short_ready st
        (CMBinLK (op:int) (right:cm_expr) (ty:cm_type)) = T) &&
     (!st op left_value ty. cm_frame_short_ready st
        (CMBinRK (op:int) (left_value:cm_value) (ty:cm_type)) =
        ((op == 0i ==> ~cm_truth st left_value) &&
         (op == 1i ==> cm_truth st left_value))) &&
     (!st op. cm_frame_short_ready st (CMUnaryK (op:int)) = T) &&
     (!st index ty. cm_frame_short_ready st
        (CMIndexLK (index:cm_expr) (ty:cm_type)) = T) &&
     (!st base ty. cm_frame_short_ready st
        (CMIndexRK (base:cm_value) (ty:cm_type)) = T) &&
     (!st mid. cm_frame_short_ready st (CMMemberK (mid:int)) = T) &&
     (!st. cm_frame_short_ready st CMPutcK = T) &&
     (!st. cm_frame_short_ready st CMPutiK = T) &&
     (!st. cm_frame_short_ready st CMExitK = T) &&
     (!st. cm_frame_short_ready st CMExprStmtK = T) &&
     (!st slot. cm_frame_short_ready st (CMInitK (slot:int)) = T) &&
     (!st env regions. cm_frame_short_ready st
        (CMBlockK (env:int->int->cm_value)
          (regions:(cm_region)list)) = T) &&
     (!st second. cm_frame_short_ready st
        (CMSeqK (second:cm_stmt)) = T) &&
     (!st yes no. cm_frame_short_ready st
        (CMIfK (yes:cm_stmt) (no:cm_stmt)) = T) &&
     (!st guard body. cm_frame_short_ready st
        (CMWhileGuardK (guard:cm_expr) (body:cm_stmt)) = T) &&
     (!st guard body env regions. cm_frame_short_ready st
        (CMWhileBodyK (guard:cm_expr) (body:cm_stmt)
          (env:int->int->cm_value) (regions:(cm_region)list)) = T) &&
     (!st. cm_frame_short_ready st CMReturnK = T) &&
     (!st callee rest values ret. cm_frame_short_ready st
        (CMArgK (callee:int) (rest:(cm_expr)list)
          (values:(cm_value)list) (ret:cm_type)) = T) &&
     (!st caller env fp regions ret. cm_frame_short_ready st
        (CMCallK (caller:int) (env:int->int->cm_value) (fp:int)
          (regions:(cm_region)list) (ret:cm_type)) = T)`);
PROOF static int _c_cm_frame_short_ready =
    cst_add_const_to_header(`cm_frame_short_ready`);

PROOF thm cm_frames_short_ready_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(!st. cm_frames_short_ready (st:cm_src_state)
        ([]:(cm_frame)list) = T) &&
     (!st frame rest. cm_frames_short_ready st
        ((frame:cm_frame) :: (rest:(cm_frame)list)) =
        (cm_frame_short_ready st frame &&
         cm_frames_short_ready st rest))`);
PROOF static int _c_cm_frames_short_ready =
    cst_add_const_to_header(`cm_frames_short_ready`);

PROOF thm cm_task_short_ready_def = new_rec_definition(
    get_cm_task_recursion(),
    `(!p input. cm_task_short_ready
        (CMStartTask (p:cm_program) (input:(int)list)) = T) &&
     (!p fid expr st ks. cm_task_short_ready
        (CMRTask (p:cm_program) (fid:int) (expr:cm_expr)
          (st:cm_src_state) (ks:(cm_frame)list)) =
        cm_frames_short_ready st ks) &&
     (!p fid expr st ks. cm_task_short_ready
        (CMLTask (p:cm_program) (fid:int) (expr:cm_expr)
          (st:cm_src_state) (ks:(cm_frame)list)) =
        cm_frames_short_ready st ks) &&
     (!p fid stmt st ks. cm_task_short_ready
        (CMSTask (p:cm_program) (fid:int) (stmt:cm_stmt)
          (st:cm_src_state) (ks:(cm_frame)list)) =
        cm_frames_short_ready st ks) &&
     (!p fid value st ks. cm_task_short_ready
        (CMVTask (p:cm_program) (fid:int) (value:cm_value)
          (st:cm_src_state) (ks:(cm_frame)list)) =
        cm_frames_short_ready st ks) &&
     (!p fid ctl st ks. cm_task_short_ready
        (CMCTask (p:cm_program) (fid:int) (ctl:cm_control)
          (st:cm_src_state) (ks:(cm_frame)list)) =
        cm_frames_short_ready st ks) &&
     (!st ctl status. cm_task_short_ready
        (CMDoneTask (st:cm_src_state) (ctl:cm_control)
          (status:int)) = T)`);
PROOF static int _c_cm_task_short_ready =
    cst_add_const_to_header(`cm_task_short_ready`);

PROOF static term cm_sd_app_arg_from_right(
    term application, size_t offset) {
  for (size_t i = 0; i < offset; ++i) {
    application = dest_comb(application).tm1;
  }
  return dest_comb(application).tm2;
}

PROOF static term cm_sd_constructor_arg(
    term constructor, size_t arity, size_t index) {
  return cm_sd_app_arg_from_right(
      constructor, arity - index - 1);
}

PROOF static thm cm_sd_named_shape(
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

PROOF static thm cm_prove_truth_bases(void) {
  gnode root = gnode_new_with_ccl(
      `!(old_state:cm_src_state) (new_state:cm_src_state)
         (limit:int) (v:cm_value).
         cm_region_bases_below_equal
           (cm_state_regions new_state)
           (cm_state_regions old_state) limit ==>
         cm_value_generation_below limit v ==>
         (cm_truth new_state v <=> cm_truth old_state v)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm number = match_mp_rule(match_mp_rule(
      specl_rule(TERM_LIST(
        `v:cm_value`, `old_state:cm_src_state`,
        `new_state:cm_src_state`, `limit:int`),
        cm_value_number_bases),
      assume_rule(
        `cm_region_bases_below_equal
          (cm_state_regions (new_state:cm_src_state))
          (cm_state_regions (old_state:cm_src_state)) (limit:int)`)),
      assume_rule(
        `cm_value_generation_below (limit:int) (v:cm_value)`));
  CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
      get_cm_truth_def(), number)));
  return gnode_prove(root);
}
PROOF thm cm_truth_bases = cm_prove_truth_bases();

PROOF static thm cm_prove_frame_short_ready_bases(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (fid:int) (old_state:cm_src_state)
         (new_state:cm_src_state) (limit:int) (frame:cm_frame).
         cm_region_bases_below_equal
           (cm_state_regions new_state)
           (cm_state_regions old_state) limit ==>
         cm_frame_generation_below p fid limit frame ==>
         cm_frame_short_ready old_state frame ==>
         cm_frame_short_ready new_state frame`);
  gnode introduced = AUTO_INTROS_TAC(root);
  gnode_list cases = DISJ_CASES_TAC(introduced,
      ispec_rule(`frame:cm_frame`, get_datatype_cases("cm_frame")),
      "Hshort_frame");
  size_t arities[23] = {
      0, 1, 2, 2, 3, 3, 1, 2, 2, 1, 0, 0,
      0, 0, 1, 2, 1, 2, 2, 4, 0, 4, 5};
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode branch = cases[i];
    thm shape = cm_sd_named_shape(&branch, "Hshort_frame");
    if (i != 5) {
      CONV_TAC(branch, reduce_rewrite_conv(THM_LIST(
          shape, cm_frame_short_ready_def)));
      continue;
    }
    term concrete = rhs_of(shape);
    term left_value = cm_sd_constructor_arg(
        concrete, arities[i], 1);
    thm value_below = conv_rule(reduce_rewrite_conv(THM_LIST(
        shape, cm_frame_generation_below_def)), assume_rule(
          `cm_frame_generation_below (p:cm_program) (fid:int)
            (limit:int) (frame:cm_frame)`));
    thm old_ready = conv_rule(reduce_rewrite_conv(THM_LIST(
        shape, cm_frame_short_ready_def)), assume_rule(
          `cm_frame_short_ready (old_state:cm_src_state)
            (frame:cm_frame)`));
    thm truth = match_mp_rule(match_mp_rule(
        specl_rule(TERM_LIST(
          `old_state:cm_src_state`, `new_state:cm_src_state`,
          `limit:int`, left_value), cm_truth_bases),
        assume_rule(
          `cm_region_bases_below_equal
            (cm_state_regions (new_state:cm_src_state))
            (cm_state_regions (old_state:cm_src_state))
            (limit:int)`)), value_below);
    thm target_view = apply_conversion(reduce_rewrite_conv(THM_LIST(
        shape, cm_frame_short_ready_def, truth)),
        goal_ccl(branch->g));
    ACCEPT_TAC(branch, eq_mp_rule(sym_rule(target_view), old_ready));
  }
  return gnode_prove(root);
}
PROOF thm cm_frame_short_ready_bases =
    cm_prove_frame_short_ready_bases();

PROOF static thm cm_prove_frames_short_ready_bases(void) {
  gnode root = gnode_new_with_ccl(
      `!(ks:(cm_frame)list).
         !(p:cm_program) (fid:int) (old_state:cm_src_state)
           (new_state:cm_src_state) (limit:int).
           cm_region_bases_below_equal
             (cm_state_regions new_state)
             (cm_state_regions old_state) limit ==>
           cm_frames_generation_below p fid limit ks ==>
           cm_frames_short_ready old_state ks ==>
           cm_frames_short_ready new_state ks`);
  gnode_list cases = INDUCT_TAC(root, `ks:(cm_frame)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        cm_frames_short_ready_def)));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm bases = assume_rule(
        `cm_region_bases_below_equal
          (cm_state_regions (new_state:cm_src_state))
          (cm_state_regions (old_state:cm_src_state)) (limit:int)`);
    thm generation = conv_rule(rewrite_conv(THM_LIST(
        cm_frames_generation_below_def)), assume_rule(
          `cm_frames_generation_below (p:cm_program) (fid:int)
            (limit:int) ((a0:cm_frame) :: (a1:(cm_frame)list))`));
    thm old_ready = conv_rule(rewrite_conv(THM_LIST(
        cm_frames_short_ready_def)), assume_rule(
          `cm_frames_short_ready (old_state:cm_src_state)
            ((a0:cm_frame) :: (a1:(cm_frame)list))`));
    thm head = match_mp_rule(match_mp_rule(match_mp_rule(
        specl_rule(TERM_LIST(
          `p:cm_program`, `fid:int`, `old_state:cm_src_state`,
          `new_state:cm_src_state`, `limit:int`, `a0:cm_frame`),
          cm_frame_short_ready_bases), bases),
        conjunct1_rule(generation)), conjunct1_rule(old_ready));
    thm ih = assume_rule(
        `!(p:cm_program) (fid:int) (old_state:cm_src_state)
           (new_state:cm_src_state) (limit:int).
           cm_region_bases_below_equal
             (cm_state_regions new_state)
             (cm_state_regions old_state) limit ==>
           cm_frames_generation_below p fid limit
             (a1:(cm_frame)list) ==>
           cm_frames_short_ready old_state a1 ==>
           cm_frames_short_ready new_state a1`);
    thm tail = match_mp_rule(match_mp_rule(match_mp_rule(
        specl_rule(TERM_LIST(
          `p:cm_program`,
          `cm_frame_parent_fid (a0:cm_frame) (fid:int)`,
          `old_state:cm_src_state`, `new_state:cm_src_state`,
          `limit:int`), ih), bases),
        conjunct2_rule(generation)), conjunct2_rule(old_ready));
    thm result = conj_rule(head, tail);
    thm target_view = apply_conversion(rewrite_conv(THM_LIST(
        cm_frames_short_ready_def)), goal_ccl(leaf->g));
    ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), result));
  }
  return gnode_prove(root);
}
PROOF thm cm_frames_short_ready_bases =
    cm_prove_frames_short_ready_bases();

PROOF static thm cm_prove_task_short_ready_initial(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (input:(int)list).
         cm_task_short_ready (CMStartTask p input)`);
  CONV_TAC(root, reduce_rewrite_conv(THM_LIST(
      cm_task_short_ready_def)));
  return gnode_prove(root);
}
PROOF thm cm_task_short_ready_initial =
    cm_prove_task_short_ready_initial();

PROOF static int cmc_preservation_short_defs_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_short_defs_axioms_before,
      "cmc_preservation_short_defs introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_short_defs_checks =
    cmc_preservation_short_defs_final_checks();
