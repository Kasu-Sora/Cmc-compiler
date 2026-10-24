#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_generation_task.h"

#require "cmc_preservation_generation_state.c"

PROOF static size_t _cmc_preservation_generation_task_axioms_before =
    vector_size(get_all_axioms());

PROOF thm cm_expr_static_valid_def = new_rec_definition(
    get_cm_expr_recursion(),
    `(!p f n ty.
        cm_expr_static_valid (p:cm_program) (f:cm_function_d)
          (CMConstE (n:int) (ty:cm_type)) = T) &&
     (!p f sid ty.
        cm_expr_static_valid p f (CMStringE (sid:int) (ty:cm_type)) =
          (0i <= sid && sid < ilength (cm_program_strings p))) &&
     (!p f scope slot ty.
        cm_expr_static_valid p f
          (CMVarE (scope:int) (slot:int) (ty:cm_type)) =
          cm_binding_valid p f scope slot) &&
     (!p f dst src ty.
        cm_expr_static_valid p f
          (CMAssignE (dst:cm_expr) (src:cm_expr) (ty:cm_type)) =
          (cm_expr_static_valid p f dst &&
           cm_expr_static_valid p f src)) &&
     (!p f op left right ty.
        cm_expr_static_valid p f
          (CMBinaryE (op:int) (left:cm_expr) (right:cm_expr)
            (ty:cm_type)) =
          (cm_expr_static_valid p f left &&
           cm_expr_static_valid p f right)) &&
     (!p f op arg ty.
        cm_expr_static_valid p f
          (CMUnaryE (op:int) (arg:cm_expr) (ty:cm_type)) =
          cm_expr_static_valid p f arg) &&
     (!p f base sub ty.
        cm_expr_static_valid p f
          (CMIndexE (base:cm_expr) (sub:cm_expr) (ty:cm_type)) =
          (cm_expr_static_valid p f base &&
           cm_expr_static_valid p f sub)) &&
     (!p f base mid ty.
        cm_expr_static_valid p f
          (CMMemberE (base:cm_expr) (mid:int) (ty:cm_type)) =
          cm_expr_static_valid p f base) &&
     (!p f callee args ty.
        cm_expr_static_valid p f
          (CMCallE (callee:int) (args:(cm_expr)list) (ty:cm_type)) =
          (0i <= callee &&
           callee < ilength (cm_program_functions p) &&
           cm_args_static_valid p f args)) &&
     (!p f asked ty.
        cm_expr_static_valid p f
          (CMSizeofE (asked:cm_type) (ty:cm_type)) = T) &&
     (!p f ty.
        cm_expr_static_valid p f (CMGetcE (ty:cm_type)) = T) &&
     (!p f arg ty.
        cm_expr_static_valid p f
          (CMPutcE (arg:cm_expr) (ty:cm_type)) =
          cm_expr_static_valid p f arg) &&
     (!p f arg ty.
        cm_expr_static_valid p f
          (CMPutiE (arg:cm_expr) (ty:cm_type)) =
          cm_expr_static_valid p f arg) &&
     (!p f arg ty.
        cm_expr_static_valid p f
          (CMExitE (arg:cm_expr) (ty:cm_type)) =
          cm_expr_static_valid p f arg) &&
     (!p f.
        cm_args_static_valid (p:cm_program) (f:cm_function_d)
          ([]:(cm_expr)list) = T) &&
     (!p f arg args.
        cm_args_static_valid p f
          ((arg:cm_expr) :: (args:(cm_expr)list)) =
          (cm_expr_static_valid p f arg &&
           cm_args_static_valid p f args))`);
PROOF thm cm_args_static_valid_def = cm_expr_static_valid_def;

PROOF thm cm_stmt_static_valid_def = new_rec_definition(
    get_cm_stmt_recursion(),
    `(!p f. cm_stmt_static_valid
        (p:cm_program) (f:cm_function_d) CMSkipS = T) &&
     (!p f expr.
        cm_stmt_static_valid p f (CMExprS (expr:cm_expr)) =
          cm_expr_static_valid p f expr) &&
     (!p f slot.
        cm_stmt_static_valid p f (CMDeclS (slot:int)) = T) &&
     (!p f slot expr.
        cm_stmt_static_valid p f
          (CMInitS (slot:int) (expr:cm_expr)) =
          cm_expr_static_valid p f expr) &&
     (!p f first second.
        cm_stmt_static_valid p f
          (CMSeqS (first:cm_stmt) (second:cm_stmt)) =
          (cm_stmt_static_valid p f first &&
           cm_stmt_static_valid p f second)) &&
     (!p f body.
        cm_stmt_static_valid p f (CMBlockS (body:cm_stmt)) =
          cm_stmt_static_valid p f body) &&
     (!p f guard yes no.
        cm_stmt_static_valid p f
          (CMIfS (guard:cm_expr) (yes:cm_stmt) (no:cm_stmt)) =
          (cm_expr_static_valid p f guard &&
           cm_stmt_static_valid p f yes &&
           cm_stmt_static_valid p f no)) &&
     (!p f guard body.
        cm_stmt_static_valid p f
          (CMWhileS (guard:cm_expr) (body:cm_stmt)) =
          (cm_expr_static_valid p f guard &&
           cm_stmt_static_valid p f body)) &&
     (!p f. cm_stmt_static_valid
        (p:cm_program) (f:cm_function_d) CMBreakS = T) &&
     (!p f. cm_stmt_static_valid
        (p:cm_program) (f:cm_function_d) CMContinueS = T) &&
     (!p f expr.
        cm_stmt_static_valid p f (CMReturnS (expr:cm_expr)) =
          cm_expr_static_valid p f expr)`);

PROOF thm cm_frame_static_valid_def = new_rec_definition(
    get_cm_frame_recursion(),
    `(!p fid. cm_frame_static_valid
        (p:cm_program) (fid:int) CMHaltK = T) &&
     (!p fid ty.
        cm_frame_static_valid p fid (CMLoadK (ty:cm_type)) = T) &&
     (!p fid expr ty.
        cm_frame_static_valid p fid
          (CMAssignLK (expr:cm_expr) (ty:cm_type)) =
          cm_expr_static_valid p
            (inth fid (cm_program_functions p)) expr) &&
     (!p fid v ty.
        cm_frame_static_valid p fid
          (CMAssignRK (v:cm_value) (ty:cm_type)) = T) &&
     (!p fid op expr ty.
        cm_frame_static_valid p fid
          (CMBinLK (op:int) (expr:cm_expr) (ty:cm_type)) =
          cm_expr_static_valid p
            (inth fid (cm_program_functions p)) expr) &&
     (!p fid op v ty.
        cm_frame_static_valid p fid
          (CMBinRK (op:int) (v:cm_value) (ty:cm_type)) = T) &&
     (!p fid op.
        cm_frame_static_valid p fid (CMUnaryK (op:int)) = T) &&
     (!p fid expr ty.
        cm_frame_static_valid p fid
          (CMIndexLK (expr:cm_expr) (ty:cm_type)) =
          cm_expr_static_valid p
            (inth fid (cm_program_functions p)) expr) &&
     (!p fid v ty.
        cm_frame_static_valid p fid
          (CMIndexRK (v:cm_value) (ty:cm_type)) = T) &&
     (!p fid mid.
        cm_frame_static_valid p fid (CMMemberK (mid:int)) = T) &&
     (!p fid. cm_frame_static_valid p fid CMPutcK = T) &&
     (!p fid. cm_frame_static_valid p fid CMPutiK = T) &&
     (!p fid. cm_frame_static_valid p fid CMExitK = T) &&
     (!p fid. cm_frame_static_valid p fid CMExprStmtK = T) &&
     (!p fid slot.
        cm_frame_static_valid p fid (CMInitK (slot:int)) = T) &&
     (!p fid env regions.
        cm_frame_static_valid p fid
          (CMBlockK (env:int->int->cm_value)
            (regions:(cm_region)list)) = T) &&
     (!p fid stmt.
        cm_frame_static_valid p fid (CMSeqK (stmt:cm_stmt)) =
          cm_stmt_static_valid p
            (inth fid (cm_program_functions p)) stmt) &&
     (!p fid yes no.
        cm_frame_static_valid p fid
          (CMIfK (yes:cm_stmt) (no:cm_stmt)) =
          (cm_stmt_static_valid p
             (inth fid (cm_program_functions p)) yes &&
           cm_stmt_static_valid p
             (inth fid (cm_program_functions p)) no)) &&
     (!p fid guard body.
        cm_frame_static_valid p fid
          (CMWhileGuardK (guard:cm_expr) (body:cm_stmt)) =
          (cm_expr_static_valid p
             (inth fid (cm_program_functions p)) guard &&
           cm_stmt_static_valid p
             (inth fid (cm_program_functions p)) body)) &&
     (!p fid guard body env regions.
        cm_frame_static_valid p fid
          (CMWhileBodyK (guard:cm_expr) (body:cm_stmt)
            (env:int->int->cm_value) (regions:(cm_region)list)) =
          (cm_expr_static_valid p
             (inth fid (cm_program_functions p)) guard &&
           cm_stmt_static_valid p
             (inth fid (cm_program_functions p)) body)) &&
     (!p fid. cm_frame_static_valid p fid CMReturnK = T) &&
     (!p fid callee rest values ret.
        cm_frame_static_valid p fid
          (CMArgK (callee:int) (rest:(cm_expr)list)
            (values:(cm_value)list) (ret:cm_type)) =
          (0i <= callee &&
           callee < ilength (cm_program_functions p) &&
           cm_args_static_valid p
             (inth fid (cm_program_functions p)) rest)) &&
     (!p fid caller env fp regions ret.
        cm_frame_static_valid p fid
          (CMCallK (caller:int) (env:int->int->cm_value) (fp:int)
            (regions:(cm_region)list) (ret:cm_type)) = T)`);

PROOF thm cm_frames_static_valid_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(!p fid. cm_frames_static_valid
        (p:cm_program) (fid:int) ([]:(cm_frame)list) = T) &&
     (!p fid frame rest.
        cm_frames_static_valid p fid
          ((frame:cm_frame) :: (rest:(cm_frame)list)) =
          (cm_frame_static_valid p fid frame &&
           cm_frames_static_valid p
             (cm_frame_parent_fid frame fid) rest))`);

PROOF thm cm_task_static_valid_def = new_rec_definition(
    get_cm_task_recursion(),
    `(!p input. cm_task_static_valid
        (CMStartTask (p:cm_program) (input:(int)list)) = T) &&
     (!p fid expr st ks.
        cm_task_static_valid
          (CMRTask (p:cm_program) (fid:int) (expr:cm_expr)
            (st:cm_src_state) (ks:(cm_frame)list)) =
          (cm_expr_static_valid p
             (inth fid (cm_program_functions p)) expr &&
           cm_frames_static_valid p fid ks)) &&
     (!p fid expr st ks.
        cm_task_static_valid
          (CMLTask (p:cm_program) (fid:int) (expr:cm_expr)
            (st:cm_src_state) (ks:(cm_frame)list)) =
          (cm_expr_static_valid p
             (inth fid (cm_program_functions p)) expr &&
           cm_frames_static_valid p fid ks)) &&
     (!p fid stmt st ks.
        cm_task_static_valid
          (CMSTask (p:cm_program) (fid:int) (stmt:cm_stmt)
            (st:cm_src_state) (ks:(cm_frame)list)) =
          (cm_stmt_static_valid p
             (inth fid (cm_program_functions p)) stmt &&
           cm_frames_static_valid p fid ks)) &&
     (!p fid v st ks.
        cm_task_static_valid
          (CMVTask (p:cm_program) (fid:int) (v:cm_value)
            (st:cm_src_state) (ks:(cm_frame)list)) =
          cm_frames_static_valid p fid ks) &&
     (!p fid ctl st ks.
        cm_task_static_valid
          (CMCTask (p:cm_program) (fid:int) (ctl:cm_control)
            (st:cm_src_state) (ks:(cm_frame)list)) =
          cm_frames_static_valid p fid ks) &&
     (!st ctl status.
        cm_task_static_valid
          (CMDoneTask (st:cm_src_state) (ctl:cm_control)
            (status:int)) = T)`);

PROOF thm cm_task_generation_limit_def = new_rec_definition(
    get_cm_task_recursion(),
    `(!p input.
        cm_task_generation_limit
          (CMStartTask (p:cm_program) (input:(int)list)) =
          cm_first_dynamic_generation p) &&
     (!p fid expr st ks.
        cm_task_generation_limit
          (CMRTask (p:cm_program) (fid:int) (expr:cm_expr)
            (st:cm_src_state) (ks:(cm_frame)list)) =
          cm_state_nextgen st) &&
     (!p fid expr st ks.
        cm_task_generation_limit
          (CMLTask (p:cm_program) (fid:int) (expr:cm_expr)
            (st:cm_src_state) (ks:(cm_frame)list)) =
          cm_state_nextgen st) &&
     (!p fid stmt st ks.
        cm_task_generation_limit
          (CMSTask (p:cm_program) (fid:int) (stmt:cm_stmt)
            (st:cm_src_state) (ks:(cm_frame)list)) =
          cm_state_nextgen st) &&
     (!p fid v st ks.
        cm_task_generation_limit
          (CMVTask (p:cm_program) (fid:int) (v:cm_value)
            (st:cm_src_state) (ks:(cm_frame)list)) =
          cm_state_nextgen st) &&
     (!p fid ctl st ks.
        cm_task_generation_limit
          (CMCTask (p:cm_program) (fid:int) (ctl:cm_control)
            (st:cm_src_state) (ks:(cm_frame)list)) =
          cm_state_nextgen st) &&
     (!st ctl status.
        cm_task_generation_limit
          (CMDoneTask (st:cm_src_state) (ctl:cm_control)
            (status:int)) = cm_state_nextgen st)`);

PROOF thm cm_annotation_payload_generation_below_def =
    new_fun_definition(
      `cm_annotation_payload_generation_below (limit:int)
         (ann:cm_annotation) : bool =
         (cm_spills_generation_below limit (cm_ann_spills ann) &&
          cm_spill_frames_generation_below limit (cm_ann_saved ann))`);

PROOF static thm cm_prove_annotation_payload_implies_task_generation(void) {
  gnode root = gnode_new_with_ccl(
      `!(task:cm_task) (ann:cm_annotation).
         cm_annotation_payload_generation_below
           (cm_task_generation_limit task) ann ==>
         cm_annotation_generation_below task ann`);
  gnode_list cases = INDUCT_TAC(root, `task:cm_task`);
  for (size_t i = 0; i < vector_size(cases); ++i) {
    gnode leaf = AUTO_INTROS_TAC(cases[i]);
    thm payload = conv_rule(reduce_rewrite_conv(THM_LIST(
        cm_annotation_payload_generation_below_def,
        cm_task_generation_limit_def)), assume_rule(
          goal_lasmps(leaf->g)[0].tm));
    thm body = (i == 0 || i == 6)
        ? conjunct2_rule(payload)
        : conj_rule(conjunct1_rule(payload), conjunct2_rule(payload));
    thm target_view = apply_conversion(
        reduce_rewrite_conv(THM_LIST(
          cm_annotation_generation_below_def,
          cm_active_spill_frames_def,
          cm_spill_frames_generation_below_def,
          cm_spill_frame_spills_def)),
        goal_ccl(leaf->g));
    ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view), body));
  }
  return gnode_prove(root);
}
PROOF thm cm_annotation_payload_implies_task_generation =
    cm_prove_annotation_payload_implies_task_generation();

PROOF static thm cm_prove_annotation_payload_generation_below_mono(void) {
  gnode root = gnode_new_with_ccl(
      `!(ann:cm_annotation) (old:int) (new:int).
         old <= new ==>
         cm_annotation_payload_generation_below old ann ==>
         cm_annotation_payload_generation_below new ann`);
  gnode leaf = AUTO_INTROS_TAC(root);
  thm opened = conv_rule(rewrite_conv(THM_LIST(
      cm_annotation_payload_generation_below_def)), assume_rule(
        `cm_annotation_payload_generation_below (old:int)
          (ann:cm_annotation)`));
  thm spills = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
      `cm_ann_spills (ann:cm_annotation)`, `old:int`, `new:int`),
      cm_spills_generation_below_mono), assume_rule(
        `(old:int) <= (new:int)`)), conjunct1_rule(opened));
  thm saved = match_mp_rule(match_mp_rule(specl_rule(TERM_LIST(
      `cm_ann_saved (ann:cm_annotation)`, `old:int`, `new:int`),
      cm_spill_frames_generation_below_mono), assume_rule(
        `(old:int) <= (new:int)`)), conjunct2_rule(opened));
  thm target_view = apply_conversion(rewrite_conv(THM_LIST(
      cm_annotation_payload_generation_below_def)), goal_ccl(leaf->g));
  ACCEPT_TAC(leaf, eq_mp_rule(sym_rule(target_view),
      conj_rule(spills, saved)));
  return gnode_prove(root);
}
PROOF thm cm_annotation_payload_generation_below_mono =
    cm_prove_annotation_payload_generation_below_mono();

PROOF thm get_cm_task_static_valid_def(void) {
  return cm_task_static_valid_def;
}
PROOF thm get_cm_task_generation_limit_def(void) {
  return cm_task_generation_limit_def;
}
PROOF thm get_cm_annotation_payload_generation_below_def(void) {
  return cm_annotation_payload_generation_below_def;
}

PROOF static int cmc_preservation_generation_task_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_generation_task_axioms_before,
      "cmc_preservation_generation_task introduced an axiom");
  ENSURE_COND(vector_size(hyp(cm_annotation_payload_implies_task_generation)) == 0,
      "payload-to-task generation theorem is not closed");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_generation_task_checks =
    cmc_preservation_generation_task_final_checks();
