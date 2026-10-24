#include "proof/proof.h"
#include "userlib/renderers.h"
#include "cmc_annotate_model.h"
#include "cmc_preservation_generation.h"
#include "cmc_temp_algebra.h"
#require "cmc_preservation_generation.c"
#require "cmc_temp_algebra.c"
#include "userlib/proof.h"
#include "cmc_preservation_budget_defs.h"

PROOF static size_t _cmc_preservation_budget_defs_axioms_before =
    vector_size(get_all_axioms());

PROOF thm cm_phase_budget_def = new_rec_definition(
    get_cm_aphase_recursion(),
    `(!p fid owner.
        cm_phase_budget (p:cm_program) (fid:int) CAHaltP (owner:int) = T) &&
     (!p fid owner ty.
        cm_phase_budget p fid (CALoadP (ty:cm_type)) owner = T) &&
     (!p fid owner src ty.
        cm_phase_budget p fid
          (CAAssignLP (src:cm_expr) (ty:cm_type)) owner =
        (0i <= owner &&
         owner + 1i + cm_rtemps src <=
           cm_temp_slots (inth fid (cm_program_functions p)))) &&
     (!p fid owner ptr ty.
        cm_phase_budget p fid
          (CAAssignRP (ptr:cm_value) (ty:cm_type)) owner = T) &&
     (!p fid owner op left right ty.
        cm_phase_budget p fid
          (CABinLP (op:int) (left:cm_expr) (right:cm_expr)
             (ty:cm_type)) owner =
        (0i <= owner &&
         owner +
           (if op == 0i || op == 1i
            then cm_rtemps right
            else 1i + cm_rtemps right) <=
           cm_temp_slots (inth fid (cm_program_functions p)))) &&
     (!p fid owner op left right left_value ty.
        cm_phase_budget p fid
          (CABinRP (op:int) (left:cm_expr) (right:cm_expr)
             (left_value:cm_value) (ty:cm_type)) owner = T) &&
     (!p fid owner op.
        cm_phase_budget p fid (CAUnaryP (op:int)) owner = T) &&
     (!p fid owner index ty.
        cm_phase_budget p fid
          (CAIndexLP (index:cm_expr) (ty:cm_type)) owner =
        (0i <= owner &&
         owner + 1i + cm_rtemps index <=
           cm_temp_slots (inth fid (cm_program_functions p)))) &&
     (!p fid owner base ty.
        cm_phase_budget p fid
          (CAIndexRP (base:cm_value) (ty:cm_type)) owner = T) &&
     (!p fid owner mid base_ty.
        cm_phase_budget p fid
          (CAMemberP (mid:int) (base_ty:cm_type)) owner = T) &&
     (!p fid owner. cm_phase_budget p fid CAPutcP owner = T) &&
     (!p fid owner. cm_phase_budget p fid CAPutiP owner = T) &&
     (!p fid owner. cm_phase_budget p fid CAExitP owner = T) &&
     (!p fid owner. cm_phase_budget p fid CAExprStmtP owner = T) &&
     (!p fid owner slot.
        cm_phase_budget p fid (CAInitP (slot:int)) owner = T) &&
     (!p fid owner env regions jump target.
        cm_phase_budget p fid
          (CABlockP (env:int->int->cm_value)
             (regions:(cm_region)list) (jump:bool) (target:int))
          owner = T) &&
     (!p fid owner second.
        cm_phase_budget p fid (CASeqP (second:cm_stmt)) owner =
        (0i <= owner &&
         owner + cm_stemps second <=
           cm_temp_slots (inth fid (cm_program_functions p)))) &&
     (!p fid owner yes no.
        cm_phase_budget p fid
          (CAIfP (yes:cm_stmt) (no:cm_stmt)) owner =
        (0i <= owner &&
         owner + cm_stemps yes <=
           cm_temp_slots (inth fid (cm_program_functions p)) &&
         owner + cm_stemps no <=
           cm_temp_slots (inth fid (cm_program_functions p)))) &&
     (!p fid owner guard body loop_start loop_end.
        cm_phase_budget p fid
          (CAWhileGuardP (guard:cm_expr) (body:cm_stmt)
             (loop_start:int) (loop_end:int)) owner =
        (0i <= owner &&
         owner + cm_rtemps guard <=
           cm_temp_slots (inth fid (cm_program_functions p)) &&
         owner + cm_stemps body <=
           cm_temp_slots (inth fid (cm_program_functions p)))) &&
     (!p fid owner guard body env regions loop_start loop_end.
        cm_phase_budget p fid
          (CAWhileBodyP (guard:cm_expr) (body:cm_stmt)
             (env:int->int->cm_value) (regions:(cm_region)list)
             (loop_start:int) (loop_end:int)) owner =
        (0i <= owner &&
         owner + cm_rtemps guard <=
           cm_temp_slots (inth fid (cm_program_functions p)) &&
         owner + cm_stemps body <=
           cm_temp_slots (inth fid (cm_program_functions p)))) &&
     (!p fid owner. cm_phase_budget p fid CAReturnP owner = T) &&
     (!p fid owner callee rest values ret all_args base_slot
         current_slot scratch.
        cm_phase_budget p fid
          (CAArgP (callee:int) (rest:(cm_expr)list)
             (values:(cm_value)list) (ret:cm_type)
             (all_args:(cm_expr)list) (base_slot:int)
             (current_slot:int) (scratch:int)) owner =
        (0i <= base_slot &&
         0i <= current_slot &&
         0i <= scratch &&
         current_slot <
           cm_temp_slots (inth fid (cm_program_functions p)) &&
         current_slot + 1i + ilength rest == scratch &&
         scratch + cm_adepth (cm_args_apair rest) <=
           cm_temp_slots (inth fid (cm_program_functions p)))) &&
     (!p fid owner caller env fp regions ret.
        cm_phase_budget p fid
          (CACallP (caller:int) (env:int->int->cm_value) (fp:int)
             (regions:(cm_region)list) (ret:cm_type)) owner = T)`);
PROOF static int _c_cm_phase_budget =
    cst_add_const_to_header(`cm_phase_budget`);

PROOF thm cm_cursors_budget_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(!p fid.
        cm_cursors_budget (p:cm_program) (fid:int)
          ([]:(cm_acursor)list) = T) &&
     (!p fid cursor rest.
        cm_cursors_budget p fid
          ((cursor:cm_acursor) :: (rest:(cm_acursor)list)) =
        (cm_phase_budget p fid (cm_cursor_phase cursor)
           (cm_cursor_temp cursor) &&
         cm_cursors_budget p
           (cm_frame_parent_fid
             (cm_phase_frame (cm_cursor_phase cursor)) fid)
           rest))`);
PROOF static int _c_cm_cursors_budget =
    cst_add_const_to_header(`cm_cursors_budget`);

PROOF thm cm_task_budget_def = new_rec_definition(
    get_cm_task_recursion(),
    `(!root p input ann.
        cm_task_budget (root:cm_program)
          (CMStartTask (p:cm_program) (input:(int)list))
          (ann:cm_annotation) =
        cm_cursors_budget root (--1i) (cm_ann_cursors ann)) &&
     (!root p fid expr st ks ann.
        cm_task_budget root
          (CMRTask (p:cm_program) (fid:int) (expr:cm_expr)
             (st:cm_src_state) (ks:(cm_frame)list)) ann =
        (0i <= cm_ann_temp ann &&
         cm_ann_temp ann + cm_rtemps expr <=
           cm_temp_slots
             (inth fid (cm_program_functions root)) &&
         cm_cursors_budget root fid (cm_ann_cursors ann))) &&
     (!root p fid expr st ks ann.
        cm_task_budget root
          (CMLTask (p:cm_program) (fid:int) (expr:cm_expr)
             (st:cm_src_state) (ks:(cm_frame)list)) ann =
        (0i <= cm_ann_temp ann &&
         cm_ann_temp ann + cm_ltemps expr <=
           cm_temp_slots
             (inth fid (cm_program_functions root)) &&
         cm_cursors_budget root fid (cm_ann_cursors ann))) &&
     (!root p fid stmt st ks ann.
        cm_task_budget root
          (CMSTask (p:cm_program) (fid:int) (stmt:cm_stmt)
             (st:cm_src_state) (ks:(cm_frame)list)) ann =
        (0i <= cm_ann_temp ann &&
         cm_ann_temp ann + cm_stemps stmt <=
           cm_temp_slots
             (inth fid (cm_program_functions root)) &&
         cm_cursors_budget root fid (cm_ann_cursors ann))) &&
     (!root p fid value st ks ann.
        cm_task_budget root
          (CMVTask (p:cm_program) (fid:int) (value:cm_value)
             (st:cm_src_state) (ks:(cm_frame)list)) ann =
        cm_cursors_budget root fid (cm_ann_cursors ann)) &&
     (!root p fid control st ks ann.
        cm_task_budget root
          (CMCTask (p:cm_program) (fid:int) (control:cm_control)
             (st:cm_src_state) (ks:(cm_frame)list)) ann =
        cm_cursors_budget root fid (cm_ann_cursors ann)) &&
     (!root st control status ann.
        cm_task_budget (root:cm_program)
          (CMDoneTask (st:cm_src_state) (control:cm_control)
             (status:int)) (ann:cm_annotation) = T)`);
PROOF static int _c_cm_task_budget =
    cst_add_const_to_header(`cm_task_budget`);

PROOF thm get_cm_phase_budget_def(void) {
  return cm_phase_budget_def;
}
PROOF thm get_cm_cursors_budget_def(void) {
  return cm_cursors_budget_def;
}
PROOF thm get_cm_task_budget_def(void) {
  return cm_task_budget_def;
}

PROOF static int cmc_preservation_budget_defs_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_budget_defs_axioms_before,
      "cmc_preservation_budget_defs introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_budget_defs_checks =
    cmc_preservation_budget_defs_final_checks();
