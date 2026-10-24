#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_sim.h"
#require "cmc_sim.c"
#include "cmc_annotate_model.h"


/* Static cursor phases parallel cm_frame while retaining only the compile
 * coordinates erased by the source CEK machine. */
PROOF indtype cm_aphase_ty = new_datatype_definition(
    "cm_aphase = CAHaltP"
    " | CALoadP cm_type"
    " | CAAssignLP cm_expr cm_type"
    " | CAAssignRP cm_value cm_type"
    " | CABinLP int cm_expr cm_expr cm_type"
    " | CABinRP int cm_expr cm_expr cm_value cm_type"
    " | CAUnaryP int"
    " | CAIndexLP cm_expr cm_type"
    " | CAIndexRP cm_value cm_type"
    " | CAMemberP int cm_type"
    " | CAPutcP | CAPutiP | CAExitP | CAExprStmtP"
    " | CAInitP int"
    " | CABlockP (int->int->cm_value) (cm_region)list bool int"
    " | CASeqP cm_stmt"
    " | CAIfP cm_stmt cm_stmt"
    " | CAWhileGuardP cm_expr cm_stmt int int"
    " | CAWhileBodyP cm_expr cm_stmt (int->int->cm_value)"
    "   (cm_region)list int int"
    " | CAReturnP"
    " | CAArgP int (cm_expr)list (cm_value)list cm_type"
    "   (cm_expr)list int int int"
    " | CACallP int (int->int->cm_value) int (cm_region)list cm_type");
PROOF static int _t_cm_aphase = cst_add_type_to_header("cm_aphase", 0);

PROOF indtype cm_acursor_ty = new_datatype_definition(
    "cm_acursor = CMACursor cm_aphase int int int");
PROOF static int _t_cm_acursor = cst_add_type_to_header("cm_acursor", 0);

PROOF indtype cm_annotation_ty = new_datatype_definition(
    "cm_annotation = CMAnnotation int int int int (cm_acursor)list"
    " (cm_spill)list (cm_spill_frame)list (cm_call_sim_frame)list");
PROOF static int _t_cm_annotation =
    cst_add_type_to_header("cm_annotation", 0);

PROOF indtype cm_aupdate_ty = new_datatype_definition(
    "cm_aupdate = CMAUpdate num cm_annotation");
PROOF static int _t_cm_aupdate = cst_add_type_to_header("cm_aupdate", 0);

PROOF indtype cm_astate_ty = new_datatype_definition(
    "cm_astate = CMAState cm_task tvm_task cm_annotation");
PROOF static int _t_cm_astate = cst_add_type_to_header("cm_astate", 0);

PROOF static int _c_CAHaltP =
    cst_add_const_to_header(`CAHaltP:cm_aphase`);
PROOF static int _c_CALoadP =
    cst_add_const_to_header(`CALoadP:cm_type->cm_aphase`);
PROOF static int _c_CAAssignLP = cst_add_const_to_header(
    `CAAssignLP:cm_expr->cm_type->cm_aphase`);
PROOF static int _c_CAAssignRP = cst_add_const_to_header(
    `CAAssignRP:cm_value->cm_type->cm_aphase`);
PROOF static int _c_CABinLP = cst_add_const_to_header(
    `CABinLP:int->cm_expr->cm_expr->cm_type->cm_aphase`);
PROOF static int _c_CABinRP = cst_add_const_to_header(
    `CABinRP:int->cm_expr->cm_expr->cm_value->cm_type->cm_aphase`);
PROOF static int _c_CAUnaryP =
    cst_add_const_to_header(`CAUnaryP:int->cm_aphase`);
PROOF static int _c_CAIndexLP = cst_add_const_to_header(
    `CAIndexLP:cm_expr->cm_type->cm_aphase`);
PROOF static int _c_CAIndexRP = cst_add_const_to_header(
    `CAIndexRP:cm_value->cm_type->cm_aphase`);
PROOF static int _c_CAMemberP = cst_add_const_to_header(
    `CAMemberP:int->cm_type->cm_aphase`);
PROOF static int _c_CAPutcP =
    cst_add_const_to_header(`CAPutcP:cm_aphase`);
PROOF static int _c_CAPutiP =
    cst_add_const_to_header(`CAPutiP:cm_aphase`);
PROOF static int _c_CAExitP =
    cst_add_const_to_header(`CAExitP:cm_aphase`);
PROOF static int _c_CAExprStmtP =
    cst_add_const_to_header(`CAExprStmtP:cm_aphase`);
PROOF static int _c_CAInitP =
    cst_add_const_to_header(`CAInitP:int->cm_aphase`);
PROOF static int _c_CABlockP = cst_add_const_to_header(
    `CABlockP:(int->int->cm_value)->(cm_region)list->bool->int->cm_aphase`);
PROOF static int _c_CASeqP =
    cst_add_const_to_header(`CASeqP:cm_stmt->cm_aphase`);
PROOF static int _c_CAIfP = cst_add_const_to_header(
    `CAIfP:cm_stmt->cm_stmt->cm_aphase`);
PROOF static int _c_CAWhileGuardP = cst_add_const_to_header(
    `CAWhileGuardP:cm_expr->cm_stmt->int->int->cm_aphase`);
PROOF static int _c_CAWhileBodyP = cst_add_const_to_header(
    `CAWhileBodyP:cm_expr->cm_stmt->(int->int->cm_value)->(cm_region)list->int->int->cm_aphase`);
PROOF static int _c_CAReturnP =
    cst_add_const_to_header(`CAReturnP:cm_aphase`);
PROOF static int _c_CAArgP = cst_add_const_to_header(
    `CAArgP:int->(cm_expr)list->(cm_value)list->cm_type->(cm_expr)list->int->int->int->cm_aphase`);
PROOF static int _c_CACallP = cst_add_const_to_header(
    `CACallP:int->(int->int->cm_value)->int->(cm_region)list->cm_type->cm_aphase`);
PROOF static int _c_CMACursor = cst_add_const_to_header(
    `CMACursor:cm_aphase->int->int->int->cm_acursor`);
PROOF static int _c_CMAnnotation = cst_add_const_to_header(
    `CMAnnotation:int->int->int->int->(cm_acursor)list->(cm_spill)list->(cm_spill_frame)list->(cm_call_sim_frame)list->cm_annotation`);
PROOF static int _c_CMAUpdate = cst_add_const_to_header(
    `CMAUpdate:num->cm_annotation->cm_aupdate`);
PROOF static int _c_CMAState = cst_add_const_to_header(
    `CMAState:cm_task->tvm_task->cm_annotation->cm_astate`);

PROOF thm cm_phase_frame_def = new_rec_definition(
    cm_aphase_ty.rec,
    `(cm_phase_frame CAHaltP = CMHaltK) &&
     (!ty. cm_phase_frame (CALoadP (ty:cm_type)) = CMLoadK ty) &&
     (!src ty. cm_phase_frame (CAAssignLP (src:cm_expr) (ty:cm_type)) =
        CMAssignLK src ty) &&
     (!ptr ty. cm_phase_frame (CAAssignRP (ptr:cm_value) (ty:cm_type)) =
        CMAssignRK ptr ty) &&
     (!op left right ty.
        cm_phase_frame
          (CABinLP (op:int) (left:cm_expr) (right:cm_expr) (ty:cm_type)) =
        CMBinLK op right ty) &&
     (!op left right value ty.
        cm_phase_frame
          (CABinRP (op:int) (left:cm_expr) (right:cm_expr)
            (value:cm_value) (ty:cm_type)) =
        CMBinRK op value ty) &&
     (!op. cm_phase_frame (CAUnaryP (op:int)) = CMUnaryK op) &&
     (!index ty.
        cm_phase_frame (CAIndexLP (index:cm_expr) (ty:cm_type)) =
        CMIndexLK index ty) &&
     (!base ty.
        cm_phase_frame (CAIndexRP (base:cm_value) (ty:cm_type)) =
        CMIndexRK base ty) &&
     (!mid base_ty.
        cm_phase_frame (CAMemberP (mid:int) (base_ty:cm_type)) =
        CMMemberK mid) &&
     (cm_phase_frame CAPutcP = CMPutcK) &&
     (cm_phase_frame CAPutiP = CMPutiK) &&
     (cm_phase_frame CAExitP = CMExitK) &&
     (cm_phase_frame CAExprStmtP = CMExprStmtK) &&
     (!slot. cm_phase_frame (CAInitP (slot:int)) = CMInitK slot) &&
     (!env regions jump target.
        cm_phase_frame
          (CABlockP (env:int->int->cm_value) (regions:(cm_region)list)
             (jump:bool) (target:int)) =
        CMBlockK env regions) &&
     (!second. cm_phase_frame (CASeqP (second:cm_stmt)) = CMSeqK second) &&
     (!yes no.
        cm_phase_frame (CAIfP (yes:cm_stmt) (no:cm_stmt)) =
        CMIfK yes no) &&
     (!guard body loop_start loop_end.
        cm_phase_frame
          (CAWhileGuardP (guard:cm_expr) (body:cm_stmt)
             (loop_start:int) (loop_end:int)) =
        CMWhileGuardK guard body) &&
     (!guard body env regions loop_start loop_end.
        cm_phase_frame
          (CAWhileBodyP (guard:cm_expr) (body:cm_stmt)
             (env:int->int->cm_value) (regions:(cm_region)list)
             (loop_start:int) (loop_end:int)) =
        CMWhileBodyK guard body env regions) &&
     (cm_phase_frame CAReturnP = CMReturnK) &&
     (!callee rest values ret all_args base_slot current_slot scratch.
        cm_phase_frame
          (CAArgP (callee:int) (rest:(cm_expr)list)
             (values:(cm_value)list) (ret:cm_type)
             (all_args:(cm_expr)list) (base_slot:int)
             (current_slot:int) (scratch:int)) =
        CMArgK callee rest values ret) &&
     (!caller env fp regions ret.
        cm_phase_frame
          (CACallP (caller:int) (env:int->int->cm_value) (fp:int)
             (regions:(cm_region)list) (ret:cm_type)) =
        CMCallK caller env fp regions ret)`);
PROOF int _e_cm_phase_frame = cst_add_const_to_header(`cm_phase_frame`);

PROOF thm cm_cursor_phase_def = new_rec_definition(
    cm_acursor_ty.rec,
    `cm_cursor_phase
       (CMACursor (phase:cm_aphase) (temp:int)
          (breakpc:int) (continuepc:int)) = phase`);
PROOF thm cm_cursor_temp_def = new_rec_definition(
    cm_acursor_ty.rec,
    `cm_cursor_temp
       (CMACursor (phase:cm_aphase) (temp:int)
          (breakpc:int) (continuepc:int)) = temp`);
PROOF thm cm_cursor_break_def = new_rec_definition(
    cm_acursor_ty.rec,
    `cm_cursor_break
       (CMACursor (phase:cm_aphase) (temp:int)
          (breakpc:int) (continuepc:int)) = breakpc`);
PROOF thm cm_cursor_continue_def = new_rec_definition(
    cm_acursor_ty.rec,
    `cm_cursor_continue
       (CMACursor (phase:cm_aphase) (temp:int)
          (breakpc:int) (continuepc:int)) = continuepc`);

PROOF thm cm_cursor_frames_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(cm_cursor_frames ([]:(cm_acursor)list) = ([]:(cm_frame)list)) &&
     (!cursor rest.
        cm_cursor_frames
          ((cursor:cm_acursor) :: (rest:(cm_acursor)list)) =
        cm_phase_frame (cm_cursor_phase cursor) ::
          cm_cursor_frames rest)`);
PROOF int _e_cm_cursor_frames = cst_add_const_to_header(`cm_cursor_frames`);

PROOF thm cm_ann_pc_def = new_rec_definition(cm_annotation_ty.rec,
    `cm_ann_pc
       (CMAnnotation (pc:int) (temp:int) (breakpc:int) (continuepc:int)
          (cursors:(cm_acursor)list) (spills:(cm_spill)list)
          (saved:(cm_spill_frame)list)
          (calls:(cm_call_sim_frame)list)) = pc`);
PROOF thm cm_ann_temp_def = new_rec_definition(cm_annotation_ty.rec,
    `cm_ann_temp
       (CMAnnotation (pc:int) (temp:int) (breakpc:int) (continuepc:int)
          (cursors:(cm_acursor)list) (spills:(cm_spill)list)
          (saved:(cm_spill_frame)list)
          (calls:(cm_call_sim_frame)list)) = temp`);
PROOF thm cm_ann_break_def = new_rec_definition(cm_annotation_ty.rec,
    `cm_ann_break
       (CMAnnotation (pc:int) (temp:int) (breakpc:int) (continuepc:int)
          (cursors:(cm_acursor)list) (spills:(cm_spill)list)
          (saved:(cm_spill_frame)list)
          (calls:(cm_call_sim_frame)list)) = breakpc`);
PROOF thm cm_ann_continue_def = new_rec_definition(cm_annotation_ty.rec,
    `cm_ann_continue
       (CMAnnotation (pc:int) (temp:int) (breakpc:int) (continuepc:int)
          (cursors:(cm_acursor)list) (spills:(cm_spill)list)
          (saved:(cm_spill_frame)list)
          (calls:(cm_call_sim_frame)list)) = continuepc`);
PROOF thm cm_ann_cursors_def = new_rec_definition(cm_annotation_ty.rec,
    `cm_ann_cursors
       (CMAnnotation (pc:int) (temp:int) (breakpc:int) (continuepc:int)
          (cursors:(cm_acursor)list) (spills:(cm_spill)list)
          (saved:(cm_spill_frame)list)
          (calls:(cm_call_sim_frame)list)) = cursors`);
PROOF thm cm_ann_spills_def = new_rec_definition(cm_annotation_ty.rec,
    `cm_ann_spills
       (CMAnnotation (pc:int) (temp:int) (breakpc:int) (continuepc:int)
          (cursors:(cm_acursor)list) (spills:(cm_spill)list)
          (saved:(cm_spill_frame)list)
          (calls:(cm_call_sim_frame)list)) = spills`);
PROOF thm cm_ann_saved_def = new_rec_definition(cm_annotation_ty.rec,
    `cm_ann_saved
       (CMAnnotation (pc:int) (temp:int) (breakpc:int) (continuepc:int)
          (cursors:(cm_acursor)list) (spills:(cm_spill)list)
          (saved:(cm_spill_frame)list)
          (calls:(cm_call_sim_frame)list)) = saved`);
PROOF thm cm_ann_calls_def = new_rec_definition(cm_annotation_ty.rec,
    `cm_ann_calls
       (CMAnnotation (pc:int) (temp:int) (breakpc:int) (continuepc:int)
          (cursors:(cm_acursor)list) (spills:(cm_spill)list)
          (saved:(cm_spill_frame)list)
          (calls:(cm_call_sim_frame)list)) = calls`);

PROOF thm cm_update_steps_def = new_rec_definition(cm_aupdate_ty.rec,
    `cm_update_steps
       (CMAUpdate (steps:num) (annotation:cm_annotation)) = steps`);
PROOF thm cm_update_annotation_def = new_rec_definition(cm_aupdate_ty.rec,
    `cm_update_annotation
       (CMAUpdate (steps:num) (annotation:cm_annotation)) = annotation`);

PROOF thm cm_astate_task_def = new_rec_definition(cm_astate_ty.rec,
    `cm_astate_task
       (CMAState (task:cm_task) (target:tvm_task)
          (annotation:cm_annotation)) = task`);
PROOF thm cm_astate_target_def = new_rec_definition(cm_astate_ty.rec,
    `cm_astate_target
       (CMAState (task:cm_task) (target:tvm_task)
          (annotation:cm_annotation)) = target`);
PROOF thm cm_astate_annotation_def = new_rec_definition(cm_astate_ty.rec,
    `cm_astate_annotation
       (CMAState (task:cm_task) (target:tvm_task)
          (annotation:cm_annotation)) = annotation`);

/* Update helpers are defined in the next block. */

PROOF thm cm_code_steps_def = new_fun_definition(
    `cm_code_steps (code:(tvm_inst)list) : num =
       num_of_int (ilength code)`);

PROOF thm cm_ann_plain_def = new_fun_definition(
    `cm_ann_plain (pc:int) (temp:int) (breakpc:int) (continuepc:int)
       (ann:cm_annotation) : cm_annotation =
       CMAnnotation pc temp breakpc continuepc
         (cm_ann_cursors ann) (cm_ann_spills ann)
         (cm_ann_saved ann) (cm_ann_calls ann)`);

PROOF thm cm_ann_done_def = new_fun_definition(
    `cm_ann_done (ann:cm_annotation) : cm_annotation =
       CMAnnotation (cm_ann_pc ann) (cm_ann_temp ann)
         (cm_ann_break ann) (cm_ann_continue ann)
         [] (cm_ann_spills ann) (cm_ann_saved ann)
         (cm_ann_calls ann)`);

PROOF thm cm_ann_linear_def = new_fun_definition(
    `cm_ann_linear (code:(tvm_inst)list)
       (ann:cm_annotation) : cm_annotation =
       cm_ann_plain (cm_ann_pc ann + ilength code)
         (cm_ann_temp ann) (cm_ann_break ann)
         (cm_ann_continue ann) ann`);

PROOF thm cm_ann_push_def = new_fun_definition(
    `cm_ann_push (phase:cm_aphase) (pc:int) (temp:int)
       (breakpc:int) (continuepc:int)
       (ann:cm_annotation) : cm_annotation =
       CMAnnotation pc temp breakpc continuepc
         (CMACursor phase (cm_ann_temp ann) (cm_ann_break ann)
            (cm_ann_continue ann) :: cm_ann_cursors ann)
         (cm_ann_spills ann) (cm_ann_saved ann) (cm_ann_calls ann)`);

PROOF thm cm_ann_replace_def = new_fun_definition(
    `cm_ann_replace (phase:cm_aphase) (pc:int) (temp:int)
       (breakpc:int) (continuepc:int)
       (ann:cm_annotation) : cm_annotation =
       CMAnnotation pc temp breakpc continuepc
         (CMACursor phase
            (cm_cursor_temp (HD (cm_ann_cursors ann)))
            (cm_cursor_break (HD (cm_ann_cursors ann)))
            (cm_cursor_continue (HD (cm_ann_cursors ann))) ::
          TL (cm_ann_cursors ann))
         (cm_ann_spills ann) (cm_ann_saved ann) (cm_ann_calls ann)`);

PROOF thm cm_ann_pop_def = new_fun_definition(
    `cm_ann_pop (pc:int) (ann:cm_annotation) : cm_annotation =
       CMAnnotation pc
         (cm_cursor_temp (HD (cm_ann_cursors ann)))
         (cm_cursor_break (HD (cm_ann_cursors ann)))
         (cm_cursor_continue (HD (cm_ann_cursors ann)))
         (TL (cm_ann_cursors ann))
         (cm_ann_spills ann) (cm_ann_saved ann) (cm_ann_calls ann)`);

PROOF thm cm_ann_spills_set_def = new_fun_definition(
    `cm_ann_spills_set (spills:(cm_spill)list)
       (ann:cm_annotation) : cm_annotation =
       CMAnnotation (cm_ann_pc ann) (cm_ann_temp ann)
         (cm_ann_break ann) (cm_ann_continue ann)
         (cm_ann_cursors ann) spills (cm_ann_saved ann)
         (cm_ann_calls ann)`);

PROOF thm cm_spill_remove_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(cm_spill_remove (slot:int) ([]:(cm_spill)list) = []) &&
     (!spill rest.
        cm_spill_remove slot
          ((spill:cm_spill) :: (rest:(cm_spill)list)) =
        (if cm_spill_slot spill == slot
         then cm_spill_remove slot rest
         else spill :: cm_spill_remove slot rest))`);
PROOF thm cm_spill_put_def = new_fun_definition(
    `cm_spill_put (slot:int) (spill_value:cm_value)
       (spills:(cm_spill)list) : (cm_spill)list =
       CMSpill slot spill_value :: cm_spill_remove slot spills`);

PROOF thm cm_call_body_pc_def = new_fun_definition(
    `cm_call_body_pc (p:cm_program) (fid:int) : int =
       cm_function_pc p fid +
       cm_function_prologue_count
         (inth fid (cm_program_functions p))`);

PROOF thm cm_ann_enter_call_def = new_fun_definition(
    `cm_ann_enter_call (p:cm_program) (caller:int) (callee:int)
       (st:cm_src_state) (ret:cm_type) (returnpc:int)
       (parent_temp:int) (parent_break:int) (parent_continue:int)
       (tail:(cm_acursor)list) (caller_spills:(cm_spill)list)
       (saved:(cm_spill_frame)list)
       (calls:(cm_call_sim_frame)list) : cm_annotation =
       CMAnnotation (cm_call_body_pc p callee) 0i 0i 0i
         (CMACursor
            (CACallP caller (cm_state_env st) (cm_state_fp st)
              (cm_state_regions st) ret)
            parent_temp parent_break parent_continue :: tail)
         []
         (CMSpillFrame caller (cm_state_fp st) caller_spills :: saved)
         (CMCallSimFrame
            (cm_state_fp st -
             cm_frame_size (cm_program_structs p)
               (inth callee (cm_program_functions p)))
            (cm_state_fp st) returnpc :: calls)`);

PROOF int _e_cm_call_body_pc =
    cst_add_const_to_header(`cm_call_body_pc`);


PROOF thm cm_update_r_def = new_rec_definition(
    get_cm_expr_recursion(),
    `(!p fid st ann n ty.
        cm_update_r (p:cm_program) (fid:int) (st:cm_src_state)
          (ann:cm_annotation) (CMConstE (n:int) (ty:cm_type)) =
        CMAUpdate 1
          (cm_ann_linear
            (cm_push_code (cm_const_immediate ty n)) ann)) &&
     (!p fid st ann sid ty.
        cm_update_r p fid st ann
          (CMStringE (sid:int) (ty:cm_type)) =
        CMAUpdate 1
          (cm_ann_linear
            (cm_push_code (cm_string_address p sid)) ann)) &&
     (!p fid st ann scope slot ty.
        cm_update_r p fid st ann
          (CMVarE (scope:int) (slot:int) (ty:cm_type)) =
        (if cm_binding_array p fid scope slot
         then CMAUpdate
           (cm_code_steps
             (cm_binding_address_code p fid scope slot))
           (cm_ann_linear
             (cm_binding_address_code p fid scope slot) ann)
         else CMAUpdate 0
           (cm_ann_push (CALoadP ty) (cm_ann_pc ann)
             (cm_ann_temp ann) (cm_ann_break ann)
             (cm_ann_continue ann) ann))) &&
     (!p fid st ann dst src ty.
        cm_update_r p fid st ann
          (CMAssignE (dst:cm_expr) (src:cm_expr) (ty:cm_type)) =
        CMAUpdate 0
          (cm_ann_push (CAAssignLP src ty) (cm_ann_pc ann)
            (cm_ann_temp ann) (cm_ann_break ann)
            (cm_ann_continue ann) ann)) &&
     (!p fid st ann op left right ty.
        cm_update_r p fid st ann
          (CMBinaryE (op:int) (left:cm_expr) (right:cm_expr)
             (ty:cm_type)) =
        CMAUpdate 0
          (cm_ann_push (CABinLP op left right ty) (cm_ann_pc ann)
            (cm_ann_temp ann) (cm_ann_break ann)
            (cm_ann_continue ann) ann)) &&
     (!p fid st ann op arg ty.
        cm_update_r p fid st ann
          (CMUnaryE (op:int) (arg:cm_expr) (ty:cm_type)) =
        (if op == 2i
         then CMAUpdate 0
           (cm_ann_push (CALoadP ty) (cm_ann_pc ann)
             (cm_ann_temp ann) (cm_ann_break ann)
             (cm_ann_continue ann) ann)
         else if op == 3i
              then CMAUpdate 0 ann
              else CMAUpdate 0
                (cm_ann_push (CAUnaryP op) (cm_ann_pc ann)
                  (cm_ann_temp ann) (cm_ann_break ann)
                  (cm_ann_continue ann) ann))) &&
     (!p fid st ann base index ty.
        cm_update_r p fid st ann
          (CMIndexE (base:cm_expr) (index:cm_expr) (ty:cm_type)) =
        CMAUpdate 0
          (cm_ann_push (CALoadP ty) (cm_ann_pc ann)
            (cm_ann_temp ann) (cm_ann_break ann)
            (cm_ann_continue ann) ann)) &&
     (!p fid st ann base mid ty.
        cm_update_r p fid st ann
          (CMMemberE (base:cm_expr) (mid:int) (ty:cm_type)) =
        (if cm_member_array p (cm_expr_type base) mid
         then CMAUpdate 0 ann
         else CMAUpdate 0
           (cm_ann_push (CALoadP ty) (cm_ann_pc ann)
             (cm_ann_temp ann) (cm_ann_break ann)
             (cm_ann_continue ann) ann))) &&
     (!p fid st ann callee args ty.
        cm_update_r p fid st ann
          (CMCallE (callee:int) (args:(cm_expr)list) (ty:cm_type)) =
        (if args == []
         then if cm_call_ok p callee [] st &&
                 cm_call_depth
                   (cm_cursor_frames (cm_ann_cursors ann)) < 65536i
              then CMAUpdate
                (SUC (cm_code_steps (cm_emit_prologue p callee)))
                (cm_ann_enter_call p fid callee st ty
                  (cm_ann_pc ann + 1i)
                  (cm_ann_temp ann) (cm_ann_break ann)
                  (cm_ann_continue ann) (cm_ann_cursors ann)
                  (cm_ann_spills ann) (cm_ann_saved ann)
                  (cm_ann_calls ann))
              else CMAUpdate 0 ann
         else CMAUpdate 0
           (cm_ann_push
             (CAArgP callee (TL args) [] ty args
               (cm_ann_temp ann) (cm_ann_temp ann)
               (cm_ann_temp ann + ilength args))
             (cm_ann_pc ann)
             (cm_ann_temp ann + ilength args)
             (cm_ann_break ann) (cm_ann_continue ann) ann))) &&
     (!p fid st ann asked ty.
        cm_update_r p fid st ann
          (CMSizeofE (asked:cm_type) (ty:cm_type)) =
        CMAUpdate 1
          (cm_ann_linear
            (cm_push_code
              (cm_type_size (cm_program_structs p) asked)) ann)) &&
     (!p fid st ann ty.
        cm_update_r p fid st ann (CMGetcE (ty:cm_type)) =
        CMAUpdate 1
          (cm_ann_plain (cm_ann_pc ann + 1i)
            (cm_ann_temp ann) (cm_ann_break ann)
            (cm_ann_continue ann) ann)) &&
     (!p fid st ann arg ty.
        cm_update_r p fid st ann
          (CMPutcE (arg:cm_expr) (ty:cm_type)) =
        CMAUpdate 0
          (cm_ann_push CAPutcP (cm_ann_pc ann)
            (cm_ann_temp ann) (cm_ann_break ann)
            (cm_ann_continue ann) ann)) &&
     (!p fid st ann arg ty.
        cm_update_r p fid st ann
          (CMPutiE (arg:cm_expr) (ty:cm_type)) =
        CMAUpdate 0
          (cm_ann_push CAPutiP (cm_ann_pc ann)
            (cm_ann_temp ann) (cm_ann_break ann)
            (cm_ann_continue ann) ann)) &&
     (!p fid st ann arg ty.
        cm_update_r p fid st ann
          (CMExitE (arg:cm_expr) (ty:cm_type)) =
        CMAUpdate 0
          (cm_ann_push CAExitP (cm_ann_pc ann)
            (cm_ann_temp ann) (cm_ann_break ann)
            (cm_ann_continue ann) ann)) &&
     (!p fid st ann.
        cm_update_r_list (p:cm_program) (fid:int)
          (st:cm_src_state) (ann:cm_annotation)
          ([]:(cm_expr)list) = CMAUpdate 0 ann) &&
     (!p fid st ann arg args.
        cm_update_r_list p fid st ann
          ((arg:cm_expr) :: (args:(cm_expr)list)) =
        CMAUpdate 0 ann)`);


PROOF thm cm_update_l_def = new_rec_definition(
    get_cm_expr_recursion(),
    `(!p fid st ann n ty.
        cm_update_l (p:cm_program) (fid:int) (st:cm_src_state)
          (ann:cm_annotation) (CMConstE (n:int) (ty:cm_type)) =
        CMAUpdate 0 ann) &&
     (!p fid st ann sid ty.
        cm_update_l p fid st ann
          (CMStringE (sid:int) (ty:cm_type)) =
        CMAUpdate 0 ann) &&
     (!p fid st ann scope slot ty.
        cm_update_l p fid st ann
          (CMVarE (scope:int) (slot:int) (ty:cm_type)) =
        CMAUpdate
          (cm_code_steps
            (cm_binding_address_code p fid scope slot))
          (cm_ann_linear
            (cm_binding_address_code p fid scope slot) ann)) &&
     (!p fid st ann dst src ty.
        cm_update_l p fid st ann
          (CMAssignE (dst:cm_expr) (src:cm_expr) (ty:cm_type)) =
        CMAUpdate 0 ann) &&
     (!p fid st ann op left right ty.
        cm_update_l p fid st ann
          (CMBinaryE (op:int) (left:cm_expr) (right:cm_expr)
             (ty:cm_type)) =
        CMAUpdate 0 ann) &&
     (!p fid st ann op arg ty.
        cm_update_l p fid st ann
          (CMUnaryE (op:int) (arg:cm_expr) (ty:cm_type)) =
        CMAUpdate 0 ann) &&
     (!p fid st ann base index ty.
        cm_update_l p fid st ann
          (CMIndexE (base:cm_expr) (index:cm_expr) (ty:cm_type)) =
        CMAUpdate 0
          (cm_ann_push (CAIndexLP index ty) (cm_ann_pc ann)
            (cm_ann_temp ann) (cm_ann_break ann)
            (cm_ann_continue ann) ann)) &&
     (!p fid st ann base mid ty.
        cm_update_l p fid st ann
          (CMMemberE (base:cm_expr) (mid:int) (ty:cm_type)) =
        CMAUpdate 0
          (cm_ann_push (CAMemberP mid (cm_expr_type base))
            (cm_ann_pc ann) (cm_ann_temp ann)
            (cm_ann_break ann) (cm_ann_continue ann) ann)) &&
     (!p fid st ann callee args ty.
        cm_update_l p fid st ann
          (CMCallE (callee:int) (args:(cm_expr)list) (ty:cm_type)) =
        CMAUpdate 0 ann) &&
     (!p fid st ann asked ty.
        cm_update_l p fid st ann
          (CMSizeofE (asked:cm_type) (ty:cm_type)) =
        CMAUpdate 0 ann) &&
     (!p fid st ann ty.
        cm_update_l p fid st ann (CMGetcE (ty:cm_type)) =
        CMAUpdate 0 ann) &&
     (!p fid st ann arg ty.
        cm_update_l p fid st ann
          (CMPutcE (arg:cm_expr) (ty:cm_type)) =
        CMAUpdate 0 ann) &&
     (!p fid st ann arg ty.
        cm_update_l p fid st ann
          (CMPutiE (arg:cm_expr) (ty:cm_type)) =
        CMAUpdate 0 ann) &&
     (!p fid st ann arg ty.
        cm_update_l p fid st ann
          (CMExitE (arg:cm_expr) (ty:cm_type)) =
        CMAUpdate 0 ann) &&
     (!p fid st ann.
        cm_update_l_list (p:cm_program) (fid:int)
          (st:cm_src_state) (ann:cm_annotation)
          ([]:(cm_expr)list) = CMAUpdate 0 ann) &&
     (!p fid st ann arg args.
        cm_update_l_list p fid st ann
          ((arg:cm_expr) :: (args:(cm_expr)list)) =
        CMAUpdate 0 ann)`);


PROOF thm cm_update_s_def = new_rec_definition(
    get_cm_stmt_recursion(),
    `(!p fid st ann.
        cm_update_s (p:cm_program) (fid:int) (st:cm_src_state)
          (ann:cm_annotation) CMSkipS =
        CMAUpdate 0 ann) &&
     (!p fid st ann expr.
        cm_update_s p fid st ann (CMExprS (expr:cm_expr)) =
        CMAUpdate 0
          (cm_ann_push CAExprStmtP (cm_ann_pc ann)
            (cm_ann_temp ann) (cm_ann_break ann)
            (cm_ann_continue ann) ann)) &&
     (!p fid st ann slot.
        cm_update_s p fid st ann (CMDeclS (slot:int)) =
        CMAUpdate 0 ann) &&
     (!p fid st ann slot expr.
        cm_update_s p fid st ann
          (CMInitS (slot:int) (expr:cm_expr)) =
        (if cm_local_slot_ok p fid slot
         then CMAUpdate 0
                (cm_ann_push (CAInitP slot) (cm_ann_pc ann)
                  (cm_ann_temp ann) (cm_ann_break ann)
                  (cm_ann_continue ann) ann)
         else CMAUpdate 0 ann)) &&
     (!p fid st ann first second.
        cm_update_s p fid st ann
          (CMSeqS (first:cm_stmt) (second:cm_stmt)) =
        CMAUpdate 0
          (cm_ann_push (CASeqP second) (cm_ann_pc ann)
            (cm_ann_temp ann) (cm_ann_break ann)
            (cm_ann_continue ann) ann)) &&
     (!p fid st ann body.
        cm_update_s p fid st ann (CMBlockS (body:cm_stmt)) =
        CMAUpdate 0
          (cm_ann_push
            (CABlockP (cm_state_env st) (cm_state_regions st)
              F 0i)
            (cm_ann_pc ann) (cm_ann_temp ann)
            (cm_ann_break ann) (cm_ann_continue ann) ann)) &&
     (!p fid st ann guard yes no.
        cm_update_s p fid st ann
          (CMIfS (guard:cm_expr) (yes:cm_stmt) (no:cm_stmt)) =
        CMAUpdate 0
          (cm_ann_push (CAIfP yes no) (cm_ann_pc ann)
            (cm_ann_temp ann) (cm_ann_break ann)
            (cm_ann_continue ann) ann)) &&
     (!p fid st ann guard body.
        cm_update_s p fid st ann
          (CMWhileS (guard:cm_expr) (body:cm_stmt)) =
        CMAUpdate 0
          (cm_ann_push
            (CAWhileGuardP guard body (cm_ann_pc ann)
              (cm_ann_pc ann +
               cm_stmt_code_count p fid (CMWhileS guard body)))
            (cm_ann_pc ann) (cm_ann_temp ann)
            (cm_ann_break ann) (cm_ann_continue ann) ann)) &&
     (!p fid st ann.
        cm_update_s p fid st ann CMBreakS =
        CMAUpdate 0 ann) &&
     (!p fid st ann.
        cm_update_s p fid st ann CMContinueS =
        CMAUpdate 0 ann) &&
     (!p fid st ann expr.
        cm_update_s p fid st ann (CMReturnS (expr:cm_expr)) =
        CMAUpdate 0
          (cm_ann_push CAReturnP (cm_ann_pc ann)
            (cm_ann_temp ann) (cm_ann_break ann)
            (cm_ann_continue ann) ann))`);


PROOF thm cm_assign_tail_code_def = new_fun_definition(
    `cm_assign_tail_code (p:cm_program) (fid:int)
       (ty:cm_type) (temp:int) : (tvm_inst)list =
       cm_char_normalize_code ty ++
       cm_temp_load_code p fid temp ++
       cm_store_code ty ++
       cm_temp_load_code p fid temp ++
       cm_load_code ty`);

PROOF thm cm_index_tail_code_def = new_fun_definition(
    `cm_index_tail_code (p:cm_program) (fid:int)
       (ty:cm_type) (temp:int) : (tvm_inst)list =
       [TVMInst TVMPushOp
          (cm_type_size (cm_program_structs p) ty);
        TVMInst TVMMulOp 0i] ++
       cm_temp_load_code p fid temp ++
       [TVMInst TVMAddOp 0i]`);

PROOF thm cm_member_tail_code_def = new_fun_definition(
    `cm_member_tail_code (p:cm_program) (base_ty:cm_type)
       (mid:int) : (tvm_inst)list =
       [TVMInst TVMPushOp
          (cm_member_offset (cm_program_structs p)
            (cm_struct_id (cm_pointee base_ty)) mid);
        TVMInst TVMAddOp 0i]`);

PROOF thm cm_init_tail_code_def = new_fun_definition(
    `cm_init_tail_code (p:cm_program) (fid:int)
       (slot:int) : (tvm_inst)list =
       cm_char_normalize_code
         (cm_slot_ty
           (inth slot (cm_function_locals
             (inth fid (cm_program_functions p))))) ++
       cm_fp_relative_address_code (cm_local_offset p fid slot) ++
       cm_store_code
         (cm_slot_ty
           (inth slot (cm_function_locals
             (inth fid (cm_program_functions p)))))`);

PROOF thm cm_status_tail_code_def = new_fun_definition(
    `cm_status_tail_code : (tvm_inst)list =
       cm_char_normalize_code CMCharTy ++
       [TVMInst TVMHaltOp 0i]`);

PROOF thm cm_return_tail_code_def = new_fun_definition(
    `cm_return_tail_code (p:cm_program) (fid:int) :
       (tvm_inst)list =
       cm_char_normalize_code
         (cm_function_ret
           (inth fid (cm_program_functions p))) ++
       cm_return_epilogue`);

PROOF thm cm_fallthrough_tail_code_def = new_fun_definition(
    `cm_fallthrough_tail_code : (tvm_inst)list =
       [TVMInst TVMPushOp 0i] ++ cm_return_epilogue`);

PROOF thm cm_arg_final_code_def = new_fun_definition(
    `cm_arg_final_code (p:cm_program) (caller:int)
       (callee:int) (all_args:(cm_expr)list)
       (base_slot:int) (current_slot:int) : (tvm_inst)list =
       cm_temp_store_code p caller current_slot ++
       cm_emit_args_reload p caller base_slot all_args ++
       [TVMInst TVMCallOp (cm_function_pc p callee)] ++
       cm_emit_prologue p callee`);

PROOF thm cm_ann_put_spill_def = new_fun_definition(
    `cm_ann_put_spill (slot:int) (spill_value:cm_value)
       (ann:cm_annotation) : cm_annotation =
       cm_ann_spills_set
         (cm_spill_put slot spill_value (cm_ann_spills ann)) ann`);

PROOF thm cm_ann_leave_call_def = new_fun_definition(
    `cm_ann_leave_call (returnpc:int)
       (ann:cm_annotation) : cm_annotation =
       CMAnnotation returnpc
         (cm_cursor_temp (HD (cm_ann_cursors ann)))
         (cm_cursor_break (HD (cm_ann_cursors ann)))
         (cm_cursor_continue (HD (cm_ann_cursors ann)))
         (TL (cm_ann_cursors ann))
         (cm_spill_frame_spills (HD (cm_ann_saved ann)))
         (TL (cm_ann_saved ann)) (TL (cm_ann_calls ann))`);

PROOF thm cm_update_v_def = new_rec_definition(
    cm_aphase_ty.rec,
    `(!p fid v st ann.
        cm_update_v (p:cm_program) (fid:int) (v:cm_value)
          (st:cm_src_state) (ann:cm_annotation) CAHaltP =
        CMAUpdate (cm_code_steps cm_status_tail_code)
          (cm_ann_pop
            (cm_ann_pc ann +
             ilength (cm_char_normalize_code CMCharTy)) ann)) &&
     (!p fid v st ann ty.
        cm_update_v p fid v st ann (CALoadP (ty:cm_type)) =
        CMAUpdate (cm_code_steps (cm_load_code ty))
          (cm_ann_pop
            (cm_ann_pc ann + ilength (cm_load_code ty)) ann)) &&
     (!p fid v st ann src ty.
        cm_update_v p fid v st ann
          (CAAssignLP (src:cm_expr) (ty:cm_type)) =
        CMAUpdate
          (cm_code_steps
            (cm_temp_store_code p fid (cm_ann_temp ann)))
          (cm_ann_put_spill (cm_ann_temp ann) v
            (cm_ann_replace (CAAssignRP v ty)
              (cm_ann_pc ann +
               ilength (cm_temp_store_code p fid
                 (cm_ann_temp ann)))
              (cm_ann_temp ann + 1i)
              (cm_ann_break ann) (cm_ann_continue ann) ann))) &&
     (!p fid v st ann ptr ty.
        cm_update_v p fid v st ann
          (CAAssignRP (ptr:cm_value) (ty:cm_type)) =
        CMAUpdate
          (cm_code_steps
            (cm_assign_tail_code p fid ty
              (cm_cursor_temp (HD (cm_ann_cursors ann)))))
          (cm_ann_pop
            (cm_ann_pc ann +
             ilength
               (cm_assign_tail_code p fid ty
                 (cm_cursor_temp (HD (cm_ann_cursors ann))))) ann)) &&
     (!p fid v st ann op left right ty.
        cm_update_v p fid v st ann
          (CABinLP (op:int) (left:cm_expr) (right:cm_expr)
             (ty:cm_type)) =
        (if (op == 0i && cm_truth st v) ||
            (op == 1i && ~(cm_truth st v))
         then CMAUpdate 2
           (cm_ann_pop
             (cm_ann_pc ann +
              cm_rvalue_code_count p fid right + 5i) ann)
         else if op == 0i || op == 1i
              then CMAUpdate 1
                (cm_ann_replace
                  (CABinRP op left right v ty)
                  (cm_ann_pc ann + 1i) (cm_ann_temp ann)
                  (cm_ann_break ann) (cm_ann_continue ann) ann)
              else CMAUpdate
                (cm_code_steps
                  (cm_temp_store_code p fid (cm_ann_temp ann)))
                (cm_ann_put_spill (cm_ann_temp ann) v
                  (cm_ann_replace
                    (CABinRP op left right v ty)
                    (cm_ann_pc ann +
                     ilength (cm_temp_store_code p fid
                       (cm_ann_temp ann)))
                    (cm_ann_temp ann + 1i)
                    (cm_ann_break ann) (cm_ann_continue ann) ann)))) &&
     (!p fid v st ann op left right left_value ty.
        cm_update_v p fid v st ann
          (CABinRP (op:int) (left:cm_expr) (right:cm_expr)
             (left_value:cm_value) (ty:cm_type)) =
        (if op == 0i || op == 1i
         then CMAUpdate 3
           (cm_ann_pop (cm_ann_pc ann + 4i) ann)
         else CMAUpdate
           (cm_code_steps
             (cm_binary_finish_code p fid op left right
               (cm_cursor_temp (HD (cm_ann_cursors ann)))))
           (cm_ann_pop
             (cm_ann_pc ann +
              ilength
                (cm_binary_finish_code p fid op left right
                  (cm_cursor_temp (HD (cm_ann_cursors ann))))) ann))) &&
     (!p fid v st ann op.
        cm_update_v p fid v st ann (CAUnaryP (op:int)) =
        CMAUpdate 2 (cm_ann_pop (cm_ann_pc ann + 2i) ann)) &&
     (!p fid v st ann index ty.
        cm_update_v p fid v st ann
          (CAIndexLP (index:cm_expr) (ty:cm_type)) =
        CMAUpdate
          (cm_code_steps
            (cm_temp_store_code p fid (cm_ann_temp ann)))
          (cm_ann_put_spill (cm_ann_temp ann) v
            (cm_ann_replace (CAIndexRP v ty)
              (cm_ann_pc ann +
               ilength (cm_temp_store_code p fid
                 (cm_ann_temp ann)))
              (cm_ann_temp ann + 1i)
              (cm_ann_break ann) (cm_ann_continue ann) ann))) &&
     (!p fid v st ann base ty.
        cm_update_v p fid v st ann
          (CAIndexRP (base:cm_value) (ty:cm_type)) =
        CMAUpdate
          (cm_code_steps
            (cm_index_tail_code p fid ty
              (cm_cursor_temp (HD (cm_ann_cursors ann)))))
          (cm_ann_pop
            (cm_ann_pc ann +
             ilength
               (cm_index_tail_code p fid ty
                 (cm_cursor_temp (HD (cm_ann_cursors ann))))) ann)) &&
     (!p fid v st ann mid base_ty.
        cm_update_v p fid v st ann
          (CAMemberP (mid:int) (base_ty:cm_type)) =
        CMAUpdate
          (cm_code_steps (cm_member_tail_code p base_ty mid))
          (cm_ann_pop
            (cm_ann_pc ann +
             ilength (cm_member_tail_code p base_ty mid)) ann)) &&
     (!p fid v st ann.
        cm_update_v p fid v st ann CAPutcP =
        CMAUpdate 2 (cm_ann_pop (cm_ann_pc ann + 2i) ann)) &&
     (!p fid v st ann.
        cm_update_v p fid v st ann CAPutiP =
        CMAUpdate 2 (cm_ann_pop (cm_ann_pc ann + 2i) ann)) &&
     (!p fid v st ann.
        cm_update_v p fid v st ann CAExitP =
        CMAUpdate (cm_code_steps cm_status_tail_code)
          (cm_ann_pop
            (cm_ann_pc ann +
             ilength (cm_char_normalize_code CMCharTy)) ann)) &&
     (!p fid v st ann.
        cm_update_v p fid v st ann CAExprStmtP =
        CMAUpdate 1 (cm_ann_pop (cm_ann_pc ann + 1i) ann)) &&
     (!p fid v st ann slot.
        cm_update_v p fid v st ann (CAInitP (slot:int)) =
        CMAUpdate (cm_code_steps (cm_init_tail_code p fid slot))
          (cm_ann_pop
            (cm_ann_pc ann +
             ilength (cm_init_tail_code p fid slot)) ann)) &&
     (!p fid v st ann env regions jump target.
        cm_update_v p fid v st ann
          (CABlockP (env:int->int->cm_value)
             (regions:(cm_region)list) (jump:bool) (target:int)) =
        CMAUpdate 0 (cm_ann_pop (cm_ann_pc ann) ann)) &&
     (!p fid v st ann second.
        cm_update_v p fid v st ann (CASeqP (second:cm_stmt)) =
        CMAUpdate 0 (cm_ann_pop (cm_ann_pc ann) ann)) &&
     (!p fid v st ann yes no.
        cm_update_v p fid v st ann
          (CAIfP (yes:cm_stmt) (no:cm_stmt)) =
        (if cm_truth st v
         then CMAUpdate 1
           (cm_ann_replace
             (CABlockP (cm_state_env st) (cm_state_regions st)
               T
               (cm_ann_pc ann + 2i +
                cm_stmt_code_count p fid yes +
                cm_stmt_code_count p fid no))
             (cm_ann_pc ann + 1i)
             (cm_cursor_temp (HD (cm_ann_cursors ann)))
             (cm_cursor_break (HD (cm_ann_cursors ann)))
             (cm_cursor_continue (HD (cm_ann_cursors ann))) ann)
         else CMAUpdate 1
           (cm_ann_replace
             (CABlockP (cm_state_env st) (cm_state_regions st)
               F
               (cm_ann_pc ann + 2i +
                cm_stmt_code_count p fid yes +
                cm_stmt_code_count p fid no))
             (cm_ann_pc ann + 2i +
              cm_stmt_code_count p fid yes)
             (cm_cursor_temp (HD (cm_ann_cursors ann)))
             (cm_cursor_break (HD (cm_ann_cursors ann)))
             (cm_cursor_continue (HD (cm_ann_cursors ann))) ann))) &&
     (!p fid v st ann guard body loop_start loop_end.
        cm_update_v p fid v st ann
          (CAWhileGuardP (guard:cm_expr) (body:cm_stmt)
             (loop_start:int) (loop_end:int)) =
        (if cm_truth st v
         then CMAUpdate 1
           (cm_ann_replace
             (CAWhileBodyP guard body (cm_state_env st)
               (cm_state_regions st) loop_start loop_end)
             (cm_ann_pc ann + 1i)
             (cm_cursor_temp (HD (cm_ann_cursors ann)))
             loop_end loop_start ann)
         else CMAUpdate 1 (cm_ann_pop loop_end ann))) &&
     (!p fid v st ann guard body env regions loop_start loop_end.
        cm_update_v p fid v st ann
          (CAWhileBodyP (guard:cm_expr) (body:cm_stmt)
             (env:int->int->cm_value) (regions:(cm_region)list)
             (loop_start:int) (loop_end:int)) =
        CMAUpdate 0 (cm_ann_pop (cm_ann_pc ann) ann)) &&
     (!p fid v st ann.
        cm_update_v p fid v st ann CAReturnP =
        CMAUpdate 0 (cm_ann_pop (cm_ann_pc ann) ann)) &&
     (!p fid v st ann callee rest values ret all_args
         base_slot current_slot scratch.
        cm_update_v p fid v st ann
          (CAArgP (callee:int) (rest:(cm_expr)list)
             (values:(cm_value)list) (ret:cm_type)
             (all_args:(cm_expr)list) (base_slot:int)
             (current_slot:int) (scratch:int)) =
        (if rest == []
         then if cm_call_ok p callee (REVERSE (v :: values)) st &&
                 cm_call_depth
                   (cm_cursor_frames (TL (cm_ann_cursors ann))) <
                   65536i
              then CMAUpdate
                (cm_code_steps
                  (cm_arg_final_code p fid callee all_args
                    base_slot current_slot))
                (cm_ann_enter_call p fid callee st ret
                  (cm_ann_pc ann +
                   ilength (cm_temp_store_code p fid current_slot) +
                   ilength
                     (cm_emit_args_reload p fid base_slot all_args) +
                   1i)
                  (cm_cursor_temp (HD (cm_ann_cursors ann)))
                  (cm_cursor_break (HD (cm_ann_cursors ann)))
                  (cm_cursor_continue (HD (cm_ann_cursors ann)))
                  (TL (cm_ann_cursors ann))
                  (cm_spill_put current_slot v
                    (cm_ann_spills ann))
                  (cm_ann_saved ann) (cm_ann_calls ann))
              else CMAUpdate 0
                (cm_ann_pop (cm_ann_pc ann) ann)
         else CMAUpdate
           (cm_code_steps
             (cm_temp_store_code p fid current_slot))
           (cm_ann_put_spill current_slot v
             (cm_ann_replace
               (CAArgP callee (TL rest) (v :: values) ret
                 all_args base_slot (current_slot + 1i) scratch)
               (cm_ann_pc ann +
                ilength (cm_temp_store_code p fid current_slot))
               scratch (cm_ann_break ann)
               (cm_ann_continue ann) ann)))) &&
     (!p fid v st ann caller env fp regions ret.
        cm_update_v p fid v st ann
          (CACallP (caller:int) (env:int->int->cm_value) (fp:int)
             (regions:(cm_region)list) (ret:cm_type)) =
        CMAUpdate 0 (cm_ann_pop (cm_ann_pc ann) ann))`);


PROOF thm cm_update_c_def = new_rec_definition(
    cm_aphase_ty.rec,
    `(!p fid ctl st ann.
        cm_update_c (p:cm_program) (fid:int) (ctl:cm_control)
          (st:cm_src_state) (ann:cm_annotation) CAHaltP =
        CMAUpdate 0 (cm_ann_pop (cm_ann_pc ann) ann)) &&
     (!p fid ctl st ann ty.
        cm_update_c p fid ctl st ann (CALoadP (ty:cm_type)) =
        CMAUpdate 0 (cm_ann_pop (cm_ann_pc ann) ann)) &&
     (!p fid ctl st ann src ty.
        cm_update_c p fid ctl st ann
          (CAAssignLP (src:cm_expr) (ty:cm_type)) =
        CMAUpdate 0 (cm_ann_pop (cm_ann_pc ann) ann)) &&
     (!p fid ctl st ann ptr ty.
        cm_update_c p fid ctl st ann
          (CAAssignRP (ptr:cm_value) (ty:cm_type)) =
        CMAUpdate 0 (cm_ann_pop (cm_ann_pc ann) ann)) &&
     (!p fid ctl st ann op left right ty.
        cm_update_c p fid ctl st ann
          (CABinLP (op:int) (left:cm_expr) (right:cm_expr)
             (ty:cm_type)) =
        CMAUpdate 0 (cm_ann_pop (cm_ann_pc ann) ann)) &&
     (!p fid ctl st ann op left right left_value ty.
        cm_update_c p fid ctl st ann
          (CABinRP (op:int) (left:cm_expr) (right:cm_expr)
             (left_value:cm_value) (ty:cm_type)) =
        CMAUpdate 0 (cm_ann_pop (cm_ann_pc ann) ann)) &&
     (!p fid ctl st ann op.
        cm_update_c p fid ctl st ann (CAUnaryP (op:int)) =
        CMAUpdate 0 (cm_ann_pop (cm_ann_pc ann) ann)) &&
     (!p fid ctl st ann index ty.
        cm_update_c p fid ctl st ann
          (CAIndexLP (index:cm_expr) (ty:cm_type)) =
        CMAUpdate 0 (cm_ann_pop (cm_ann_pc ann) ann)) &&
     (!p fid ctl st ann base ty.
        cm_update_c p fid ctl st ann
          (CAIndexRP (base:cm_value) (ty:cm_type)) =
        CMAUpdate 0 (cm_ann_pop (cm_ann_pc ann) ann)) &&
     (!p fid ctl st ann mid base_ty.
        cm_update_c p fid ctl st ann
          (CAMemberP (mid:int) (base_ty:cm_type)) =
        CMAUpdate 0 (cm_ann_pop (cm_ann_pc ann) ann)) &&
     (!p fid ctl st ann.
        cm_update_c p fid ctl st ann CAPutcP =
        CMAUpdate 0 (cm_ann_pop (cm_ann_pc ann) ann)) &&
     (!p fid ctl st ann.
        cm_update_c p fid ctl st ann CAPutiP =
        CMAUpdate 0 (cm_ann_pop (cm_ann_pc ann) ann)) &&
     (!p fid ctl st ann.
        cm_update_c p fid ctl st ann CAExitP =
        CMAUpdate 0 (cm_ann_pop (cm_ann_pc ann) ann)) &&
     (!p fid ctl st ann.
        cm_update_c p fid ctl st ann CAExprStmtP =
        CMAUpdate 0 (cm_ann_pop (cm_ann_pc ann) ann)) &&
     (!p fid ctl st ann slot.
        cm_update_c p fid ctl st ann (CAInitP (slot:int)) =
        CMAUpdate 0 (cm_ann_pop (cm_ann_pc ann) ann)) &&
     (!p fid ctl st ann env regions jump target.
        cm_update_c p fid ctl st ann
          (CABlockP (env:int->int->cm_value)
             (regions:(cm_region)list) (jump:bool) (target:int)) =
        (if cm_control_kind ctl == 0i && jump
         then CMAUpdate 1 (cm_ann_pop target ann)
         else CMAUpdate 0 (cm_ann_pop (cm_ann_pc ann) ann))) &&
     (!p fid ctl st ann second.
        cm_update_c p fid ctl st ann (CASeqP (second:cm_stmt)) =
        CMAUpdate 0 (cm_ann_pop (cm_ann_pc ann) ann)) &&
     (!p fid ctl st ann yes no.
        cm_update_c p fid ctl st ann
          (CAIfP (yes:cm_stmt) (no:cm_stmt)) =
        CMAUpdate 0 (cm_ann_pop (cm_ann_pc ann) ann)) &&
     (!p fid ctl st ann guard body loop_start loop_end.
        cm_update_c p fid ctl st ann
          (CAWhileGuardP (guard:cm_expr) (body:cm_stmt)
             (loop_start:int) (loop_end:int)) =
        CMAUpdate 0 (cm_ann_pop (cm_ann_pc ann) ann)) &&
     (!p fid ctl st ann guard body env regions loop_start loop_end.
        cm_update_c p fid ctl st ann
          (CAWhileBodyP (guard:cm_expr) (body:cm_stmt)
             (env:int->int->cm_value) (regions:(cm_region)list)
             (loop_start:int) (loop_end:int)) =
        (if cm_control_kind ctl == 0i ||
            cm_control_kind ctl == 2i
         then CMAUpdate 1
           (cm_ann_replace
             (CAWhileGuardP guard body loop_start loop_end)
             loop_start
             (cm_cursor_temp (HD (cm_ann_cursors ann)))
             loop_end loop_start ann)
         else if cm_control_kind ctl == 1i
              then CMAUpdate 1 (cm_ann_pop loop_end ann)
              else CMAUpdate 0
                (cm_ann_pop (cm_ann_pc ann) ann))) &&
     (!p fid ctl st ann.
        cm_update_c p fid ctl st ann CAReturnP =
        CMAUpdate 0 (cm_ann_pop (cm_ann_pc ann) ann)) &&
     (!p fid ctl st ann callee rest values ret all_args
         base_slot current_slot scratch.
        cm_update_c p fid ctl st ann
          (CAArgP (callee:int) (rest:(cm_expr)list)
             (values:(cm_value)list) (ret:cm_type)
             (all_args:(cm_expr)list) (base_slot:int)
             (current_slot:int) (scratch:int)) =
        CMAUpdate 0 (cm_ann_pop (cm_ann_pc ann) ann)) &&
     (!p fid ctl st ann caller env fp regions ret.
        cm_update_c p fid ctl st ann
          (CACallP (caller:int) (env:int->int->cm_value) (fp:int)
             (regions:(cm_region)list) (ret:cm_type)) =
        (if cm_control_kind ctl == 3i
         then CMAUpdate
           (cm_code_steps (cm_return_tail_code p fid))
           (cm_ann_leave_call
             (cm_call_sim_return (HD (cm_ann_calls ann))) ann)
         else if cm_control_kind ctl == 0i
              then CMAUpdate
                (cm_code_steps cm_fallthrough_tail_code)
                (cm_ann_leave_call
                  (cm_call_sim_return
                    (HD (cm_ann_calls ann))) ann)
              else CMAUpdate 0
                (cm_ann_leave_call (cm_ann_pc ann) ann)))`);


PROOF thm cm_initial_annotation_def = new_fun_definition(
    `cm_initial_annotation : cm_annotation =
       CMAnnotation 0i 0i 0i 0i [] [] [] []`);

PROOF thm cm_entry_steps_def = new_fun_definition(
    `cm_entry_steps (p:cm_program) : num =
       SUC (4 + cm_code_steps
         (cm_emit_prologue p (cm_program_main p)))`);

PROOF thm cm_annotation_step_def = new_rec_definition(
    get_cm_task_recursion(),
    `(!p input ann.
        cm_annotation_step
          (CMStartTask (p:cm_program) (input:(int)list))
          (ann:cm_annotation) =
        (if cm_call_ok p (cm_program_main p) []
              (cm_initial_state p input) &&
            cm_call_depth [CMHaltK] < 65536i
         then CMAUpdate (cm_entry_steps p)
           (cm_ann_enter_call p (--1i) (cm_program_main p)
             (cm_initial_state p input) CMIntTy 4i
             0i 0i 0i
             [CMACursor CAHaltP 0i 0i 0i]
             [] [] [])
         else CMAUpdate 0
           (CMAnnotation 0i 0i 0i 0i
             [CMACursor CAHaltP 0i 0i 0i] [] [] []))) &&
     (!p fid expr st ks ann.
        cm_annotation_step
          (CMRTask (p:cm_program) (fid:int) (expr:cm_expr)
             (st:cm_src_state) (ks:(cm_frame)list))
          (ann:cm_annotation) =
        cm_update_r p fid st ann expr) &&
     (!p fid expr st ks ann.
        cm_annotation_step
          (CMLTask (p:cm_program) (fid:int) (expr:cm_expr)
             (st:cm_src_state) (ks:(cm_frame)list))
          (ann:cm_annotation) =
        cm_update_l p fid st ann expr) &&
     (!p fid stmt st ks ann.
        cm_annotation_step
          (CMSTask (p:cm_program) (fid:int) (stmt:cm_stmt)
             (st:cm_src_state) (ks:(cm_frame)list))
          (ann:cm_annotation) =
        cm_update_s p fid st ann stmt) &&
     (!p fid v st ks ann.
        cm_annotation_step
          (CMVTask (p:cm_program) (fid:int) (v:cm_value)
             (st:cm_src_state) (ks:(cm_frame)list))
          (ann:cm_annotation) =
        (if cm_ann_cursors ann == []
         then CMAUpdate 0 ann
         else cm_update_v p fid v st ann
                (cm_cursor_phase (HD (cm_ann_cursors ann))))) &&
     (!p fid ctl st ks ann.
        cm_annotation_step
          (CMCTask (p:cm_program) (fid:int) (ctl:cm_control)
             (st:cm_src_state) (ks:(cm_frame)list))
          (ann:cm_annotation) =
        (if cm_control_kind ctl == 4i
         then CMAUpdate 0 (cm_ann_done ann)
         else if cm_ann_cursors ann == []
         then CMAUpdate 0 ann
         else cm_update_c p fid ctl st ann
                (cm_cursor_phase (HD (cm_ann_cursors ann))))) &&
     (!st ctl status ann.
        cm_annotation_step
          (CMDoneTask (st:cm_src_state) (ctl:cm_control)
             (status:int))
          (ann:cm_annotation) =
        CMAUpdate 0 ann)`);

PROOF thm cm_annotated_start_def = new_fun_definition(
    `cm_annotated_start (p:cm_program) (input:(int)list) :
       cm_astate =
       CMAState (CMStartTask p input)
         (TVMBoot (cm_compile_model p) input)
         cm_initial_annotation`);

PROOF thm cm_annotated_step_def = new_fun_definition(
    `cm_annotated_step (ast:cm_astate) : cm_astate =
       (let update =
          cm_annotation_step (cm_astate_task ast)
            (cm_astate_annotation ast) in
        CMAState
          (cm_step (cm_astate_task ast))
          (tvm_iter (cm_update_steps update)
            (cm_astate_target ast))
          (cm_update_annotation update))`);

PROOF thm cm_annotated_iter_def = new_rec_definition(
    get_theorem_by_name("num_RECURSION"),
    `(cm_annotated_iter 0 (ast:cm_astate) = ast) &&
     (!n ast.
        cm_annotated_iter (SUC n) ast =
        cm_annotated_iter n (cm_annotated_step ast))`);

PROOF thm cm_annotation_erases_def = new_rec_definition(
    get_cm_task_recursion(),
    `(!p input ann.
        cm_annotation_erases
          (CMStartTask (p:cm_program) (input:(int)list))
          (ann:cm_annotation) =
        (cm_ann_cursors ann == [])) &&
     (!p fid expr st ks ann.
        cm_annotation_erases
          (CMRTask (p:cm_program) (fid:int) (expr:cm_expr)
             (st:cm_src_state) (ks:(cm_frame)list))
          (ann:cm_annotation) =
        (cm_cursor_frames (cm_ann_cursors ann) == ks)) &&
     (!p fid expr st ks ann.
        cm_annotation_erases
          (CMLTask (p:cm_program) (fid:int) (expr:cm_expr)
             (st:cm_src_state) (ks:(cm_frame)list))
          (ann:cm_annotation) =
        (cm_cursor_frames (cm_ann_cursors ann) == ks)) &&
     (!p fid stmt st ks ann.
        cm_annotation_erases
          (CMSTask (p:cm_program) (fid:int) (stmt:cm_stmt)
             (st:cm_src_state) (ks:(cm_frame)list))
          (ann:cm_annotation) =
        (cm_cursor_frames (cm_ann_cursors ann) == ks)) &&
     (!p fid v st ks ann.
        cm_annotation_erases
          (CMVTask (p:cm_program) (fid:int) (v:cm_value)
             (st:cm_src_state) (ks:(cm_frame)list))
          (ann:cm_annotation) =
        (cm_cursor_frames (cm_ann_cursors ann) == ks)) &&
     (!p fid ctl st ks ann.
        cm_annotation_erases
          (CMCTask (p:cm_program) (fid:int) (ctl:cm_control)
             (st:cm_src_state) (ks:(cm_frame)list))
          (ann:cm_annotation) =
        (cm_cursor_frames (cm_ann_cursors ann) == ks)) &&
     (!st ctl status ann.
        cm_annotation_erases
          (CMDoneTask (st:cm_src_state) (ctl:cm_control)
             (status:int))
          (ann:cm_annotation) =
        (cm_ann_cursors ann == []))`);

PROOF thm cm_cursors_rooted_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(cm_cursors_rooted ([]:(cm_acursor)list) = T) &&
     (!cursor rest.
        cm_cursors_rooted
          ((cursor:cm_acursor) :: (rest:(cm_acursor)list)) =
        (((cm_cursor_phase cursor == CAHaltP) ==>
          rest == []) &&
         cm_cursors_rooted rest))`);

PROOF thm cm_annotation_rooted_def = new_fun_definition(
    `cm_annotation_rooted (ann:cm_annotation) : bool =
       cm_cursors_rooted (cm_ann_cursors ann)`);
PROOF int _e_cm_annotation_step =
    cst_add_const_to_header(`cm_annotation_step`);
PROOF int _e_cm_annotated_start =
    cst_add_const_to_header(`cm_annotated_start`);
PROOF int _e_cm_annotated_step =
    cst_add_const_to_header(`cm_annotated_step`);
PROOF int _e_cm_annotated_iter =
    cst_add_const_to_header(`cm_annotated_iter`);
PROOF int _e_cm_annotation_erases =
    cst_add_const_to_header(`cm_annotation_erases`);
PROOF int _e_cm_annotation_rooted =
    cst_add_const_to_header(`cm_annotation_rooted`);
PROOF int _e_cm_cursors_rooted =
    cst_add_const_to_header(`cm_cursors_rooted`);
PROOF int _e_cm_astate_task =
    cst_add_const_to_header(`cm_astate_task`);
PROOF int _e_cm_astate_target =
    cst_add_const_to_header(`cm_astate_target`);
PROOF int _e_cm_astate_annotation =
    cst_add_const_to_header(`cm_astate_annotation`);
PROOF int _e_cm_update_steps =
    cst_add_const_to_header(`cm_update_steps`);
PROOF int _e_cm_update_annotation =
    cst_add_const_to_header(`cm_update_annotation`);
PROOF int _e_cm_update_c = cst_add_const_to_header(`cm_update_c`);
PROOF int _e_cm_update_v = cst_add_const_to_header(`cm_update_v`);
PROOF int _e_cm_update_s = cst_add_const_to_header(`cm_update_s`);
PROOF int _e_cm_update_l = cst_add_const_to_header(`cm_update_l`);
PROOF int _e_cm_update_r = cst_add_const_to_header(`cm_update_r`);
PROOF int _e_cm_code_steps = cst_add_const_to_header(`cm_code_steps`);
PROOF int _e_cm_spill_remove = cst_add_const_to_header(`cm_spill_remove`);
PROOF int _e_cm_spill_put = cst_add_const_to_header(`cm_spill_put`);

PROOF thm get_cm_aphase_recursion(void) {
  return cm_aphase_ty.rec;
}
