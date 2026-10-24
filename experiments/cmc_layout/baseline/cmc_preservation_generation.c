#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_generation.h"

#require "cmc_preservation_call_transport.c"
#require "cmc_preservation_spill_semantic.c"
#require "cmc_preservation_state.c"

PROOF static size_t _cmc_preservation_generation_axioms_before =
    vector_size(get_all_axioms());

PROOF thm cm_env_generation_below_def = new_fun_definition(
    `cm_env_generation_below (p:cm_program) (fid:int) (limit:int)
       (env:int->int->cm_value) : bool =
       ((!slot.
          0i <= slot && slot < ilength (cm_program_globals p) ==>
          cm_value_generation_below limit (env 0i slot)) &&
        (!slot.
          0i <= slot &&
          slot < ilength
            (cm_function_locals
              (inth fid (cm_program_functions p))) ==>
          cm_value_generation_below limit (env 1i slot)) &&
        (!slot.
          0i <= slot &&
          slot < ilength
            (cm_function_params
              (inth fid (cm_program_functions p))) ==>
          cm_value_generation_below limit (env 2i slot)))`);
PROOF static int _e_cm_env_generation_below =
    cst_add_const_to_header(`cm_env_generation_below`);

PROOF thm cm_tags_generation_below_def = new_fun_definition(
    `cm_tags_generation_below (limit:int)
       (tags:int->cm_value) : bool =
       !addr. cm_value_generation_below limit (tags addr)`);
PROOF static int _e_cm_tags_generation_below =
    cst_add_const_to_header(`cm_tags_generation_below`);

PROOF thm cm_control_generation_below_def = new_rec_definition(
    get_cm_control_recursion(),
    `(cm_control_generation_below (limit:int) CMNormal = T) &&
     (cm_control_generation_below limit CMBreak = T) &&
     (cm_control_generation_below limit CMContinue = T) &&
     (!v. cm_control_generation_below limit (CMReturn (v:cm_value)) =
        cm_value_generation_below limit v) &&
     (!status. cm_control_generation_below limit (CMExit (status:int)) = T) &&
     (!code. cm_control_generation_below limit (CMError (code:int)) = T)`);
PROOF static int _e_cm_control_generation_below =
    cst_add_const_to_header(`cm_control_generation_below`);

PROOF thm cm_frame_generation_below_def = new_rec_definition(
    get_cm_frame_recursion(),
    `(cm_frame_generation_below (p:cm_program) (fid:int) (limit:int)
        CMHaltK = (fid == --1i)) &&
     (!ty. cm_frame_generation_below p fid limit (CMLoadK (ty:cm_type)) = T) &&
     (!expr ty. cm_frame_generation_below p fid limit
        (CMAssignLK (expr:cm_expr) (ty:cm_type)) = T) &&
     (!v ty. cm_frame_generation_below p fid limit
        (CMAssignRK (v:cm_value) (ty:cm_type)) =
        cm_value_generation_below limit v) &&
     (!op expr ty. cm_frame_generation_below p fid limit
        (CMBinLK (op:int) (expr:cm_expr) (ty:cm_type)) = T) &&
     (!op v ty. cm_frame_generation_below p fid limit
        (CMBinRK (op:int) (v:cm_value) (ty:cm_type)) =
        cm_value_generation_below limit v) &&
     (!op. cm_frame_generation_below p fid limit
        (CMUnaryK (op:int)) = T) &&
     (!expr ty. cm_frame_generation_below p fid limit
        (CMIndexLK (expr:cm_expr) (ty:cm_type)) = T) &&
     (!v ty. cm_frame_generation_below p fid limit
        (CMIndexRK (v:cm_value) (ty:cm_type)) =
        cm_value_generation_below limit v) &&
     (!mid. cm_frame_generation_below p fid limit
        (CMMemberK (mid:int)) = T) &&
     (cm_frame_generation_below p fid limit CMPutcK = T) &&
     (cm_frame_generation_below p fid limit CMPutiK = T) &&
     (cm_frame_generation_below p fid limit CMExitK = T) &&
     (cm_frame_generation_below p fid limit CMExprStmtK = T) &&
     (!slot. cm_frame_generation_below p fid limit
        (CMInitK (slot:int)) = T) &&
     (!env regions. cm_frame_generation_below p fid limit
        (CMBlockK (env:int->int->cm_value)
          (regions:(cm_region)list)) =
        cm_env_generation_below p fid limit env) &&
     (!stmt. cm_frame_generation_below p fid limit
        (CMSeqK (stmt:cm_stmt)) = T) &&
     (!yes no. cm_frame_generation_below p fid limit
        (CMIfK (yes:cm_stmt) (no:cm_stmt)) = T) &&
     (!guard body. cm_frame_generation_below p fid limit
        (CMWhileGuardK (guard:cm_expr) (body:cm_stmt)) = T) &&
     (!guard body env regions. cm_frame_generation_below p fid limit
        (CMWhileBodyK (guard:cm_expr) (body:cm_stmt)
          (env:int->int->cm_value) (regions:(cm_region)list)) =
        cm_env_generation_below p fid limit env) &&
     (cm_frame_generation_below p fid limit CMReturnK = T) &&
     (!callee rest values ret. cm_frame_generation_below p fid limit
        (CMArgK (callee:int) (rest:(cm_expr)list)
          (values:(cm_value)list) (ret:cm_type)) =
        cm_values_generation_below limit values) &&
     (!caller env fp regions ret. cm_frame_generation_below p fid limit
        (CMCallK (caller:int) (env:int->int->cm_value) (fp:int)
          (regions:(cm_region)list) (ret:cm_type)) =
        cm_env_generation_below p caller limit env)`);
PROOF static int _e_cm_frame_generation_below =
    cst_add_const_to_header(`cm_frame_generation_below`);

PROOF thm cm_frame_parent_fid_def = new_rec_definition(
    get_cm_frame_recursion(),
    `(cm_frame_parent_fid CMHaltK (fid:int) = fid) &&
     (!ty. cm_frame_parent_fid (CMLoadK (ty:cm_type)) fid = fid) &&
     (!expr ty. cm_frame_parent_fid
        (CMAssignLK (expr:cm_expr) (ty:cm_type)) fid = fid) &&
     (!v ty. cm_frame_parent_fid
        (CMAssignRK (v:cm_value) (ty:cm_type)) fid = fid) &&
     (!op expr ty. cm_frame_parent_fid
        (CMBinLK (op:int) (expr:cm_expr) (ty:cm_type)) fid = fid) &&
     (!op v ty. cm_frame_parent_fid
        (CMBinRK (op:int) (v:cm_value) (ty:cm_type)) fid = fid) &&
     (!op. cm_frame_parent_fid (CMUnaryK (op:int)) fid = fid) &&
     (!expr ty. cm_frame_parent_fid
        (CMIndexLK (expr:cm_expr) (ty:cm_type)) fid = fid) &&
     (!v ty. cm_frame_parent_fid
        (CMIndexRK (v:cm_value) (ty:cm_type)) fid = fid) &&
     (!mid. cm_frame_parent_fid (CMMemberK (mid:int)) fid = fid) &&
     (cm_frame_parent_fid CMPutcK fid = fid) &&
     (cm_frame_parent_fid CMPutiK fid = fid) &&
     (cm_frame_parent_fid CMExitK fid = fid) &&
     (cm_frame_parent_fid CMExprStmtK fid = fid) &&
     (!slot. cm_frame_parent_fid (CMInitK (slot:int)) fid = fid) &&
     (!env regions. cm_frame_parent_fid
        (CMBlockK (env:int->int->cm_value)
          (regions:(cm_region)list)) fid = fid) &&
     (!stmt. cm_frame_parent_fid (CMSeqK (stmt:cm_stmt)) fid = fid) &&
     (!yes no. cm_frame_parent_fid
        (CMIfK (yes:cm_stmt) (no:cm_stmt)) fid = fid) &&
     (!guard body. cm_frame_parent_fid
        (CMWhileGuardK (guard:cm_expr) (body:cm_stmt)) fid = fid) &&
     (!guard body env regions. cm_frame_parent_fid
        (CMWhileBodyK (guard:cm_expr) (body:cm_stmt)
          (env:int->int->cm_value) (regions:(cm_region)list)) fid = fid) &&
     (cm_frame_parent_fid CMReturnK fid = fid) &&
     (!callee rest values ret. cm_frame_parent_fid
        (CMArgK (callee:int) (rest:(cm_expr)list)
          (values:(cm_value)list) (ret:cm_type)) fid = fid) &&
     (!caller env fp regions ret. cm_frame_parent_fid
        (CMCallK (caller:int) (env:int->int->cm_value) (fp:int)
          (regions:(cm_region)list) (ret:cm_type)) fid = caller)`);
PROOF static int _e_cm_frame_parent_fid =
    cst_add_const_to_header(`cm_frame_parent_fid`);

PROOF thm cm_frames_generation_below_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(!p fid limit.
        cm_frames_generation_below (p:cm_program) (fid:int) (limit:int)
          ([]:(cm_frame)list) = (fid == --1i)) &&
     (!p fid limit frame rest.
        cm_frames_generation_below p fid limit
          ((frame:cm_frame) :: (rest:(cm_frame)list)) =
        (cm_frame_generation_below p fid limit frame &&
         cm_frames_generation_below p (cm_frame_parent_fid frame fid)
           limit rest))`);
PROOF static int _e_cm_frames_generation_below =
    cst_add_const_to_header(`cm_frames_generation_below`);

PROOF thm cm_state_generation_below_def = new_fun_definition(
    `cm_state_generation_below (p:cm_program) (fid:int)
       (st:cm_src_state) : bool =
       (cm_first_dynamic_generation p <= cm_state_nextgen st &&
        cm_env_generation_below p fid (cm_state_nextgen st)
          (cm_state_env st) &&
        cm_tags_generation_below (cm_state_nextgen st)
          (cm_state_tags st))`);
PROOF static int _e_cm_state_generation_below =
    cst_add_const_to_header(`cm_state_generation_below`);

PROOF thm cm_task_generation_below_def = new_rec_definition(
    get_cm_task_recursion(),
    `(!p q input.
        cm_task_generation_below (p:cm_program)
          (CMStartTask (q:cm_program) (input:(int)list)) = (q == p)) &&
     (!p q fid expr st ks.
        cm_task_generation_below p
          (CMRTask (q:cm_program) (fid:int) (expr:cm_expr)
            (st:cm_src_state) (ks:(cm_frame)list)) =
        (q == p && cm_state_generation_below p fid st &&
         cm_frames_generation_below p fid (cm_state_nextgen st) ks)) &&
     (!p q fid expr st ks.
        cm_task_generation_below p
          (CMLTask (q:cm_program) (fid:int) (expr:cm_expr)
            (st:cm_src_state) (ks:(cm_frame)list)) =
        (q == p && cm_state_generation_below p fid st &&
         cm_frames_generation_below p fid (cm_state_nextgen st) ks)) &&
     (!p q fid stmt st ks.
        cm_task_generation_below p
          (CMSTask (q:cm_program) (fid:int) (stmt:cm_stmt)
            (st:cm_src_state) (ks:(cm_frame)list)) =
        (q == p && cm_state_generation_below p fid st &&
         cm_frames_generation_below p fid (cm_state_nextgen st) ks)) &&
     (!p q fid v st ks.
        cm_task_generation_below p
          (CMVTask (q:cm_program) (fid:int) (v:cm_value)
            (st:cm_src_state) (ks:(cm_frame)list)) =
        (q == p && cm_state_generation_below p fid st &&
         cm_value_generation_below (cm_state_nextgen st) v &&
         cm_frames_generation_below p fid (cm_state_nextgen st) ks)) &&
     (!p q fid ctl st ks.
        cm_task_generation_below p
          (CMCTask (q:cm_program) (fid:int) (ctl:cm_control)
            (st:cm_src_state) (ks:(cm_frame)list)) =
        (q == p && cm_state_generation_below p fid st &&
         cm_control_generation_below (cm_state_nextgen st) ctl &&
         cm_frames_generation_below p fid (cm_state_nextgen st) ks)) &&
     (!p st ctl status.
        cm_task_generation_below (p:cm_program)
          (CMDoneTask (st:cm_src_state) (ctl:cm_control) (status:int)) =
        (cm_first_dynamic_generation p <= cm_state_nextgen st &&
         cm_tags_generation_below (cm_state_nextgen st)
           (cm_state_tags st) &&
         cm_control_generation_below (cm_state_nextgen st) ctl))`);
PROOF static int _e_cm_task_generation_below =
    cst_add_const_to_header(`cm_task_generation_below`);

PROOF thm cm_annotation_generation_below_def = new_rec_definition(
    get_cm_task_recursion(),
    `(!p input ann.
        cm_annotation_generation_below
          (CMStartTask (p:cm_program) (input:(int)list))
          (ann:cm_annotation) =
        cm_spill_frames_generation_below
          (cm_first_dynamic_generation p) (cm_ann_saved ann)) &&
     (!p fid expr st ks ann.
        cm_annotation_generation_below
          (CMRTask (p:cm_program) (fid:int) (expr:cm_expr)
            (st:cm_src_state) (ks:(cm_frame)list)) ann =
        cm_spill_frames_generation_below (cm_state_nextgen st)
          (cm_active_spill_frames fid st ann)) &&
     (!p fid expr st ks ann.
        cm_annotation_generation_below
          (CMLTask (p:cm_program) (fid:int) (expr:cm_expr)
            (st:cm_src_state) (ks:(cm_frame)list)) ann =
        cm_spill_frames_generation_below (cm_state_nextgen st)
          (cm_active_spill_frames fid st ann)) &&
     (!p fid stmt st ks ann.
        cm_annotation_generation_below
          (CMSTask (p:cm_program) (fid:int) (stmt:cm_stmt)
            (st:cm_src_state) (ks:(cm_frame)list)) ann =
        cm_spill_frames_generation_below (cm_state_nextgen st)
          (cm_active_spill_frames fid st ann)) &&
     (!p fid v st ks ann.
        cm_annotation_generation_below
          (CMVTask (p:cm_program) (fid:int) (v:cm_value)
            (st:cm_src_state) (ks:(cm_frame)list)) ann =
        cm_spill_frames_generation_below (cm_state_nextgen st)
          (cm_active_spill_frames fid st ann)) &&
     (!p fid ctl st ks ann.
        cm_annotation_generation_below
          (CMCTask (p:cm_program) (fid:int) (ctl:cm_control)
            (st:cm_src_state) (ks:(cm_frame)list)) ann =
        cm_spill_frames_generation_below (cm_state_nextgen st)
          (cm_active_spill_frames fid st ann)) &&
     (!st ctl status ann.
        cm_annotation_generation_below
          (CMDoneTask (st:cm_src_state) (ctl:cm_control) (status:int))
          (ann:cm_annotation) =
        cm_spill_frames_generation_below (cm_state_nextgen st)
          (cm_ann_saved ann))`);
PROOF static int _e_cm_annotation_generation_below =
    cst_add_const_to_header(`cm_annotation_generation_below`);

PROOF thm cm_task_generation_safe_def = new_fun_definition(
    `cm_task_generation_safe (p:cm_program) (task:cm_task)
       (ann:cm_annotation) : bool =
       (cm_task_generation_below p task &&
        cm_annotation_generation_below task ann)`);
PROOF static int _e_cm_task_generation_safe =
    cst_add_const_to_header(`cm_task_generation_safe`);

PROOF static thm cm_prove_value_generation_below_mono(void) {
  gnode root = gnode_new_with_ccl(
      `!(v:cm_value) (old:int) (new:int).
         old <= new ==>
         cm_value_generation_below old v ==>
         cm_value_generation_below new v`);
  gnode_list cases = INDUCT_TAC(root, `v:cm_value`);
  for (size_t i = 0; i < 3; ++i) {
    gnode leaf = AUTO_INTROS_TAC(cases[i]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        cm_value_generation_below_def)));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[3]);
    thm old_le_new = assume_rule(`(old:int) <= (new:int)`);
    thm gen_old = conv_rule(rewrite_conv(THM_LIST(
        cm_value_generation_below_def)), assume_rule(
          `cm_value_generation_below (old:int)
            (CMPtrV (a0:int) (a1:int) (a2:int) (a3:int)
              (a4:cm_type))`));
    thm result = mp_rule(int_arith_rule(
        `(a0:int) < (old:int) ==> old <= (new:int) ==> a0 < new`),
        gen_old);
    gnode reduced = CONV_TAC(leaf, rewrite_conv(THM_LIST(
        cm_value_generation_below_def)));
    ACCEPT_TAC(reduced, mp_rule(result, old_le_new));
  }
  return gnode_prove(root);
}
PROOF thm cm_value_generation_below_mono =
    cm_prove_value_generation_below_mono();

PROOF static thm cm_prove_values_generation_below_mono(void) {
  gnode root = gnode_new_with_ccl(
      `!(values:(cm_value)list) (old:int) (new:int).
         old <= new ==>
         cm_values_generation_below old values ==>
         cm_values_generation_below new values`);
  gnode_list cases = INDUCT_TAC(root, `values:(cm_value)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        cm_values_generation_below_def)));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm old_le_new = assume_rule(`(old:int) <= (new:int)`);
    thm opened = conv_rule(rewrite_conv(THM_LIST(
        cm_values_generation_below_def)), assume_rule(
          `cm_values_generation_below (old:int)
            ((a0:cm_value) :: (a1:(cm_value)list))`));
    thm first = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
        `a0:cm_value`, `old:int`, `new:int`),
        cm_value_generation_below_mono), old_le_new),
        conjunct1_rule(opened));
    thm rest = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
        `old:int`, `new:int`),
        assume_rule(goal_lasmps(leaf->g)[0].tm)), old_le_new),
        conjunct2_rule(opened));
    thm combined = conj_rule(first, rest);
    thm target_view = apply_conversion(rewrite_conv(THM_LIST(
        cm_values_generation_below_def)), goal_ccl(leaf->g));
    ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), combined));
  }
  return gnode_prove(root);
}
PROOF thm cm_values_generation_below_mono =
    cm_prove_values_generation_below_mono();

PROOF static thm cm_prove_spills_generation_below_mono(void) {
  gnode root = gnode_new_with_ccl(
      `!(spills:(cm_spill)list) (old:int) (new:int).
         old <= new ==>
         cm_spills_generation_below old spills ==>
         cm_spills_generation_below new spills`);
  gnode_list cases = INDUCT_TAC(root, `spills:(cm_spill)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        cm_spills_generation_below_def)));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm old_le_new = assume_rule(`(old:int) <= (new:int)`);
    thm opened = conv_rule(rewrite_conv(THM_LIST(
        cm_spills_generation_below_def)), assume_rule(
          `cm_spills_generation_below (old:int)
            ((a0:cm_spill) :: (a1:(cm_spill)list))`));
    thm first = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
        `cm_spill_value (a0:cm_spill)`, `old:int`, `new:int`),
        cm_value_generation_below_mono), old_le_new),
        conjunct1_rule(opened));
    thm rest = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
        `old:int`, `new:int`),
        assume_rule(goal_lasmps(leaf->g)[0].tm)), old_le_new),
        conjunct2_rule(opened));
    thm combined = conj_rule(first, rest);
    thm target_view = apply_conversion(rewrite_conv(THM_LIST(
        cm_spills_generation_below_def)), goal_ccl(leaf->g));
    ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), combined));
  }
  return gnode_prove(root);
}
PROOF thm cm_spills_generation_below_mono =
    cm_prove_spills_generation_below_mono();

PROOF static thm cm_prove_spill_frames_generation_below_mono(void) {
  gnode root = gnode_new_with_ccl(
      `!(frames:(cm_spill_frame)list) (old:int) (new:int).
         old <= new ==>
         cm_spill_frames_generation_below old frames ==>
         cm_spill_frames_generation_below new frames`);
  gnode_list cases = INDUCT_TAC(root, `frames:(cm_spill_frame)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        cm_spill_frames_generation_below_def)));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm old_le_new = assume_rule(`(old:int) <= (new:int)`);
    thm opened = conv_rule(rewrite_conv(THM_LIST(
        cm_spill_frames_generation_below_def)), assume_rule(
          `cm_spill_frames_generation_below (old:int)
            ((a0:cm_spill_frame) :: (a1:(cm_spill_frame)list))`));
    thm first = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
        `cm_spill_frame_spills (a0:cm_spill_frame)`,
        `old:int`, `new:int`), cm_spills_generation_below_mono),
        old_le_new), conjunct1_rule(opened));
    thm rest = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
        `old:int`, `new:int`),
        assume_rule(goal_lasmps(leaf->g)[0].tm)), old_le_new),
        conjunct2_rule(opened));
    thm combined = conj_rule(first, rest);
    thm target_view = apply_conversion(rewrite_conv(THM_LIST(
        cm_spill_frames_generation_below_def)), goal_ccl(leaf->g));
    ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), combined));
  }
  return gnode_prove(root);
}
PROOF thm cm_spill_frames_generation_below_mono =
    cm_prove_spill_frames_generation_below_mono();

PROOF static thm cm_prove_values_generation_below_append(void) {
  gnode root = gnode_new_with_ccl(
      `!(left:(cm_value)list) (right:(cm_value)list) (limit:int).
         cm_values_generation_below limit left ==>
         cm_values_generation_below limit right ==>
         cm_values_generation_below limit (left ++ right)`);
  gnode_list cases = INDUCT_TAC(root, `left:(cm_value)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm right = assume_rule(
        `cm_values_generation_below (limit:int)
          (right:(cm_value)list)`);
    gnode reduced = CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("APPEND"))));
    ACCEPT_TAC(reduced, right);
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm left = conv_rule(rewrite_conv(THM_LIST(
        cm_values_generation_below_def)), assume_rule(
          `cm_values_generation_below (limit:int)
            ((a0:cm_value) :: (a1:(cm_value)list))`));
    thm tail = match_mp_rule(match_mp_rule(
        spec_rule(`right:(cm_value)list`,
          assume_rule(goal_lasmps(leaf->g)[0].tm)),
        conjunct2_rule(left)), assume_rule(
          `cm_values_generation_below (limit:int)
            (right:(cm_value)list)`));
    thm combined = conj_rule(conjunct1_rule(left), tail);
    gnode reduced = CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("APPEND"),
        cm_values_generation_below_def)));
    ACCEPT_TAC(reduced, combined);
  }
  return gnode_prove(root);
}
PROOF static thm cm_values_generation_below_append =
    cm_prove_values_generation_below_append();

PROOF static thm cm_prove_values_generation_below_reverse(void) {
  gnode root = gnode_new_with_ccl(
      `!(values:(cm_value)list) (limit:int).
         cm_values_generation_below limit values ==>
         cm_values_generation_below limit (REVERSE values)`);
  gnode_list cases = INDUCT_TAC(root, `values:(cm_value)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        get_theorem_by_name("REVERSE"), cm_values_generation_below_def)));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm opened = conv_rule(rewrite_conv(THM_LIST(
        cm_values_generation_below_def)), assume_rule(
          `cm_values_generation_below (limit:int)
            ((a0:cm_value) :: (a1:(cm_value)list))`));
    thm ih = match_mp_rule(spec_rule(`limit:int`,
        assume_rule(goal_lasmps(leaf->g)[0].tm)),
        conjunct2_rule(opened));
    thm singleton_view = apply_conversion(
        rewrite_conv(THM_LIST(cm_values_generation_below_def)),
        `cm_values_generation_below (limit:int) [a0:cm_value]`);
    thm singleton = eq_mp_rule(
        sym_rule(singleton_view), conjunct1_rule(opened));
    thm appended = match_mp_rule(match_mp_rule(
        specl_rule(TERM_LIST(
          `REVERSE (a1:(cm_value)list)`, `[a0:cm_value]`,
          `limit:int`), cm_values_generation_below_append),
        ih), singleton);
    thm target_view = apply_conversion(
        rewrite_conv(THM_LIST(get_theorem_by_name("REVERSE"))),
        goal_ccl(leaf->g));
    ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), appended));
  }
  return gnode_prove(root);
}
PROOF thm cm_values_generation_below_reverse =
    cm_prove_values_generation_below_reverse();

PROOF static thm cm_prove_spill_holds_generation_below(void) {
  gnode root = gnode_new_with_ccl(
      `!(spills:(cm_spill)list) (limit:int) (slot:int) (v:cm_value).
         cm_spills_generation_below limit spills ==>
         cm_spill_holds slot v spills ==>
         cm_value_generation_below limit v`);
  gnode_list cases = INDUCT_TAC(root, `spills:(cm_spill)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    thm impossible = conv_rule(reduce_rewrite_conv(THM_LIST(
        cm_spill_holds_def)), assume_rule(
          `cm_spill_holds (slot:int) (v:cm_value) ([]:(cm_spill)list)`));
    CONTR_TAC(leaf, impossible);
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm below = conv_rule(rewrite_conv(THM_LIST(
        cm_spills_generation_below_def)), assume_rule(
          `cm_spills_generation_below (limit:int)
            ((a0:cm_spill) :: (a1:(cm_spill)list))`));
    thm holds = conv_rule(rewrite_conv(THM_LIST(
        cm_spill_holds_def)), assume_rule(
          `cm_spill_holds (slot:int) (v:cm_value)
            ((a0:cm_spill) :: (a1:(cm_spill)list))`));
    gnode_list equal_cases = BOOL_CASES_TAC(
        leaf, `cm_spill_slot (a0:cm_spill) == (slot:int)`, "Hslot");
    {
      thm equal = assume_rule(`cm_spill_slot (a0:cm_spill) == (slot:int)`);
      thm value_equal = conv_rule(reduce_rewrite_conv(THM_LIST(equal)), holds);
      thm lifted = beta_norm(ap_term_rule(
          `\x:cm_value. cm_value_generation_below (limit:int) x`,
          value_equal));
      ACCEPT_TAC(equal_cases[0],
          eq_mp_rule(lifted, conjunct1_rule(below)));
    }
    {
      thm unequal = assume_rule(`~(cm_spill_slot (a0:cm_spill) == (slot:int))`);
      thm tail_holds = conv_rule(reduce_rewrite_conv(THM_LIST(unequal)), holds);
      thm result = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
          `limit:int`, `slot:int`, `v:cm_value`),
          assume_rule(goal_lasmps(leaf->g)[0].tm)),
          conjunct2_rule(below)), tail_holds);
      ACCEPT_TAC(equal_cases[1], result);
    }
  }
  return gnode_prove(root);
}
PROOF static thm cm_spill_holds_generation_below =
    cm_prove_spill_holds_generation_below();

PROOF static thm cm_prove_staged_spills_generation_below(void) {
  gnode root = gnode_new_with_ccl(
      `!(values:(cm_value)list) (base:int)
         (spills:(cm_spill)list) (limit:int).
         cm_staged_spills base values spills ==>
         cm_spills_generation_below limit spills ==>
         cm_values_generation_below limit values`);
  gnode_list cases = INDUCT_TAC(root, `values:(cm_value)list`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    CONV_TAC(leaf, reduce_rewrite_conv(THM_LIST(
        cm_values_generation_below_def)));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    thm staged = conv_rule(rewrite_conv(THM_LIST(
        cm_staged_spills_def)), assume_rule(
          `cm_staged_spills (base:int)
            ((a0:cm_value) :: (a1:(cm_value)list))
            (spills:(cm_spill)list)`));
    thm spill_below = assume_rule(
        `cm_spills_generation_below (limit:int)
          (spills:(cm_spill)list)`);
    thm first = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
        `spills:(cm_spill)list`, `limit:int`,
        `(base:int) + ilength (a1:(cm_value)list)`, `a0:cm_value`),
        cm_spill_holds_generation_below), spill_below),
        conjunct1_rule(staged));
    thm rest = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
        `base:int`, `spills:(cm_spill)list`, `limit:int`),
        assume_rule(goal_lasmps(leaf->g)[0].tm)),
        conjunct2_rule(staged)), spill_below);
    thm combined = conj_rule(first, rest);
    thm target_view = apply_conversion(rewrite_conv(THM_LIST(
        cm_values_generation_below_def)), goal_ccl(leaf->g));
    ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), combined));
  }
  return gnode_prove(root);
}
PROOF thm cm_staged_spills_generation_below =
    cm_prove_staged_spills_generation_below();

PROOF static thm cm_prove_state_tags_generation_from_all(void) {
  gnode root = gnode_new_with_ccl(
      `!(st:cm_src_state) (limit:int).
         cm_tags_generation_below limit (cm_state_tags st) ==>
         cm_state_tags_generation_below st limit`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm all_tags = conv_rule(rewrite_conv(THM_LIST(
      cm_tags_generation_below_def)), assume_rule(
        `cm_tags_generation_below (limit:int)
          (cm_state_tags (st:cm_src_state))`));
  gnode opened = CONV_TAC(leaf, rewrite_conv(THM_LIST(
      cm_state_tags_generation_below_def)));
  gnode point = AUTO_INTROS_TAC(opened);
  ACCEPT_TAC(point, spec_rule(`addr:int`, all_tags));
  return gnode_prove(root);
}
PROOF thm cm_state_tags_generation_from_all =
    cm_prove_state_tags_generation_from_all();

PROOF static thm cm_prove_pointer_retype_generation_below(void) {
  gnode root = gnode_new_with_ccl(
      `!(v:cm_value) (limit:int) (ty:cm_type).
         cm_value_generation_below limit v ==>
         cm_value_generation_below limit (cm_pointer_retype ty v)`);
  gnode_list cases = INDUCT_TAC(root, `v:cm_value`);
  {
    gnode leaf = AUTO_INTROS_TAC(cases[0]);
    gnode_list zero_cases = BOOL_CASES_TAC(
        leaf, `tower_wrap64 (a:int) == 0i`, "Hzero");
    for (size_t i = 0; i < vector_size(zero_cases); ++i) {
      thm branch = i == 0
          ? eqt_intro_rule(assume_rule(
              `tower_wrap64 (a:int) == 0i`))
          : eqf_intro_rule(assume_rule(
              `~(tower_wrap64 (a:int) == 0i)`));
      conv normalize = pure_rewrite_conv(THM_LIST(
          get_cm_pointer_retype_def(), branch,
          get_theorem_by_name("COND_CLAUSES"),
          cm_value_generation_below_def));
      thm solved = eqt_elim_rule(apply_conversion(
          normalize, goal_ccl(zero_cases[i]->g)));
      ACCEPT_TAC(zero_cases[i], solved);
    }
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[1]);
    gnode_list zero_cases = BOOL_CASES_TAC(
        leaf, `tower_u8 (a:int) == 0i`, "Hzero");
    for (size_t i = 0; i < vector_size(zero_cases); ++i) {
      thm branch = i == 0
          ? eqt_intro_rule(assume_rule(
              `tower_u8 (a:int) == 0i`))
          : eqf_intro_rule(assume_rule(
              `~(tower_u8 (a:int) == 0i)`));
      conv normalize = pure_rewrite_conv(THM_LIST(
          get_cm_pointer_retype_def(), branch,
          get_theorem_by_name("COND_CLAUSES"),
          cm_value_generation_below_def));
      thm solved = eqt_elim_rule(apply_conversion(
          normalize, goal_ccl(zero_cases[i]->g)));
      ACCEPT_TAC(zero_cases[i], solved);
    }
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[2]);
    thm solved = eqt_elim_rule(apply_conversion(
        then_conv(
          rewrite_conv(THM_LIST(get_cm_pointer_retype_def())),
          reduce_rewrite_conv(THM_LIST(
            cm_value_generation_below_def))),
        goal_ccl(leaf->g)));
    ACCEPT_TAC(leaf, solved);
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[3]);
    thm below = conv_rule(rewrite_conv(THM_LIST(
        cm_value_generation_below_def)), assume_rule(
          `cm_value_generation_below (limit:int)
            (CMPtrV (a0:int) (a1:int) (a2:int) (a3:int)
              (a4:cm_type))`));
    thm target_view = apply_conversion(
        then_conv(
          rewrite_conv(THM_LIST(get_cm_pointer_retype_def())),
          reduce_rewrite_conv(THM_LIST(
            cm_value_generation_below_def))),
        goal_ccl(leaf->g));
    ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), below));
  }
  return gnode_prove(root);
}
PROOF thm cm_pointer_retype_generation_below =
    cm_prove_pointer_retype_generation_below();

PROOF static thm cm_prove_convert_generation_below(void) {
  gnode root = gnode_new_with_ccl(
      `!(st:cm_src_state) (ty:cm_type) (v:cm_value) (limit:int).
         cm_value_generation_below limit v ==>
         cm_value_generation_below limit (cm_convert_value st ty v)`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm value = assume_rule(
      `cm_value_generation_below (limit:int) (v:cm_value)`);
  gnode_list int_cases = BOOL_CASES_TAC(leaf, `(ty:cm_type) == CMIntTy`, "Hint");
  CONV_TAC(int_cases[0], reduce_rewrite_conv(THM_LIST(
      assume_rule(`(ty:cm_type) == CMIntTy`), get_cm_convert_value_def(),
      cm_value_generation_below_def)));
  gnode_list char_cases = BOOL_CASES_TAC(
      int_cases[1], `(ty:cm_type) == CMCharTy`, "Hchar");
  CONV_TAC(char_cases[0], reduce_rewrite_conv(THM_LIST(
      assume_rule(`~((ty:cm_type) == CMIntTy)`),
      assume_rule(`(ty:cm_type) == CMCharTy`),
      get_cm_convert_value_def(), cm_value_generation_below_def)));
  {
    thm result = match_mp_rule(specl_rule(TERM_LIST(
        `v:cm_value`, `limit:int`, `ty:cm_type`),
        cm_pointer_retype_generation_below), value);
    gnode reduced = CONV_TAC(char_cases[1], reduce_rewrite_conv(THM_LIST(
        assume_rule(`~((ty:cm_type) == CMIntTy)`),
        assume_rule(`~((ty:cm_type) == CMCharTy)`),
        get_cm_convert_value_def())));
    ACCEPT_TAC(reduced, result);
  }
  return gnode_prove(root);
}
PROOF thm cm_convert_generation_below =
    cm_prove_convert_generation_below();

PROOF static thm cm_prove_ptr_add_generation_below(void) {
  gnode root = gnode_new_with_ccl(
      `!(structs:(cm_struct_d)list) (ptr:cm_value)
         (index:int) (limit:int).
         0i < limit ==> cm_value_generation_below limit ptr ==>
         cm_value_generation_below limit (cm_ptr_add structs ptr index)`);
  gnode with_structs = GEN_TAC(root, "structs");
  gnode_list cases = INDUCT_TAC(with_structs, `ptr:cm_value`);
  for (size_t i = 0; i < 3; ++i) {
    gnode leaf = AUTO_INTROS_TAC(cases[i]);
    thm default_below = mp_rule(
        int_arith_rule(`(0i:int) < limit ==> -- 1i < limit`),
        assume_rule(`(0i:int) < limit`));
    CONV_WITH_ASMP_TAC(
        leaf, reduce_rewrite_conv, THM_LIST(
          get_cm_ptr_add_def(), get_cm_ptr_gen_def(),
          cm_value_generation_below_def, default_below));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[3]);
    thm below = conv_rule(rewrite_conv(THM_LIST(
        cm_value_generation_below_def)), assume_rule(
          `cm_value_generation_below (limit:int)
            (CMPtrV (a0:int) (a1:int) (a2:int) (a3:int)
              (a4:cm_type))`));
    thm target_view = apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          get_cm_ptr_add_def(), get_cm_ptr_gen_def(),
          cm_value_generation_below_def)),
        goal_ccl(leaf->g));
    ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), below));
  }
  return gnode_prove(root);
}
PROOF thm cm_ptr_add_generation_below =
    cm_prove_ptr_add_generation_below();

PROOF static thm cm_prove_ptr_member_generation_below(void) {
  gnode root = gnode_new_with_ccl(
      `!(p:cm_program) (ptr:cm_value) (mid:int) (limit:int).
         0i < limit ==> cm_value_generation_below limit ptr ==>
         cm_value_generation_below limit (cm_ptr_member p ptr mid)`);
  gnode with_program = GEN_TAC(root, "p");
  gnode_list cases = INDUCT_TAC(with_program, `ptr:cm_value`);
  for (size_t i = 0; i < 3; ++i) {
    gnode leaf = AUTO_INTROS_TAC(cases[i]);
    thm default_below = mp_rule(
        int_arith_rule(`(0i:int) < limit ==> -- 1i < limit`),
        assume_rule(`(0i:int) < limit`));
    CONV_WITH_ASMP_TAC(
        leaf, reduce_rewrite_conv, THM_LIST(
          get_cm_ptr_member_def(), get_cm_ptr_gen_def(),
          cm_value_generation_below_def, default_below));
  }
  {
    gnode leaf = AUTO_INTROS_TAC(cases[3]);
    thm below = conv_rule(rewrite_conv(THM_LIST(
        cm_value_generation_below_def)), assume_rule(
          `cm_value_generation_below (limit:int)
            (CMPtrV (a0:int) (a1:int) (a2:int) (a3:int)
              (a4:cm_type))`));
    thm target_view = apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          get_cm_ptr_member_def(), get_cm_ptr_gen_def(),
          cm_value_generation_below_def)),
        goal_ccl(leaf->g));
    ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), below));
  }
  return gnode_prove(root);
}
PROOF thm cm_ptr_member_generation_below =
    cm_prove_ptr_member_generation_below();

PROOF thm get_cm_task_generation_safe_def(void) {
  return cm_task_generation_safe_def;
}
PROOF thm get_cm_value_generation_below_mono(void) {
  return cm_value_generation_below_mono;
}
PROOF thm get_cm_values_generation_below_mono(void) {
  return cm_values_generation_below_mono;
}
PROOF thm get_cm_spill_frames_generation_below_mono(void) {
  return cm_spill_frames_generation_below_mono;
}
PROOF thm get_cm_values_generation_below_reverse(void) {
  return cm_values_generation_below_reverse;
}
PROOF thm get_cm_staged_spills_generation_below(void) {
  return cm_staged_spills_generation_below;
}
PROOF thm get_cm_state_tags_generation_from_all(void) {
  return cm_state_tags_generation_from_all;
}
PROOF thm get_cm_convert_generation_below(void) {
  return cm_convert_generation_below;
}

PROOF static int cmc_preservation_generation_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_generation_axioms_before,
      "cmc_preservation_generation introduced an axiom");
  ENSURE_COND(vector_size(hyp(cm_task_generation_safe_def)) == 0,
      "cm_task_generation_safe_def has hypotheses");
  ENSURE_COND(vector_size(hyp(cm_staged_spills_generation_below)) == 0,
      "cm_staged_spills_generation_below has hypotheses");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_generation_checks =
    cmc_preservation_generation_final_checks();
