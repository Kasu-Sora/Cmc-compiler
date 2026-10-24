#include "proof/proof.h"
#include "userlib/renderers.h"
#include "userlib/proof.h"
#include "cmc_preservation_type_ready.h"
#include "cmc_preservation_ready_coordinate.h"

#require "cmc_preservation_ready_coordinate.c"

PROOF static size_t _cmc_preservation_type_ready_axioms_before =
    vector_size(get_all_axioms());

PROOF thm cm_member_lvalue_type_def = new_fun_definition(
    `cm_member_lvalue_type (p:cm_program) (base_ty:cm_type)
       (mid:int) : cm_type =
       CMPtrTy
         (cm_slot_ty
           (inth mid
             (cm_struct_members
               (inth (cm_struct_id (cm_pointee base_ty))
                 (cm_program_structs p)))))`);
PROOF static int _e_cm_member_lvalue_type =
    cst_add_const_to_header(`cm_member_lvalue_type`);

PROOF thm cm_lvalue_output_type_def = new_rec_definition(
    get_cm_expr_recursion(),
    `(!p f n ty.
        cm_lvalue_output_type (p:cm_program) (f:cm_function_d)
          (CMConstE (n:int) (ty:cm_type)) = CMPtrTy ty) &&
     (!p f sid ty.
        cm_lvalue_output_type p f
          (CMStringE (sid:int) (ty:cm_type)) = CMPtrTy ty) &&
     (!p f scope slot ty.
        cm_lvalue_output_type p f
          (CMVarE (scope:int) (slot:int) (ty:cm_type)) =
        CMPtrTy
          (if scope == 0i
           then cm_global_ty (inth slot (cm_program_globals p))
           else if scope == 1i
                then cm_slot_ty
                  (inth slot (cm_function_locals f))
                else cm_slot_ty
                  (inth slot (cm_function_params f)))) &&
     (!p f dst src ty.
        cm_lvalue_output_type p f
          (CMAssignE (dst:cm_expr) (src:cm_expr) (ty:cm_type)) =
        CMPtrTy ty) &&
     (!p f op left right ty.
        cm_lvalue_output_type p f
          (CMBinaryE (op:int) (left:cm_expr) (right:cm_expr)
            (ty:cm_type)) = CMPtrTy ty) &&
     (!p f op arg ty.
        cm_lvalue_output_type p f
          (CMUnaryE (op:int) (arg:cm_expr) (ty:cm_type)) =
        CMPtrTy ty) &&
     (!p f base index ty.
        cm_lvalue_output_type p f
          (CMIndexE (base:cm_expr) (index:cm_expr) (ty:cm_type)) =
        CMPtrTy ty) &&
     (!p f base mid ty.
        cm_lvalue_output_type p f
          (CMMemberE (base:cm_expr) (mid:int) (ty:cm_type)) =
        cm_member_lvalue_type p (cm_expr_type base) mid) &&
     (!p f callee args ty.
        cm_lvalue_output_type p f
          (CMCallE (callee:int) (args:(cm_expr)list) (ty:cm_type)) =
        CMPtrTy ty) &&
     (!p f asked ty.
        cm_lvalue_output_type p f
          (CMSizeofE (asked:cm_type) (ty:cm_type)) = CMPtrTy ty) &&
     (!p f ty.
        cm_lvalue_output_type p f (CMGetcE (ty:cm_type)) =
        CMPtrTy ty) &&
     (!p f arg ty.
        cm_lvalue_output_type p f
          (CMPutcE (arg:cm_expr) (ty:cm_type)) = CMPtrTy ty) &&
     (!p f arg ty.
        cm_lvalue_output_type p f
          (CMPutiE (arg:cm_expr) (ty:cm_type)) = CMPtrTy ty) &&
     (!p f arg ty.
        cm_lvalue_output_type p f
          (CMExitE (arg:cm_expr) (ty:cm_type)) = CMPtrTy ty)`);
PROOF static int _e_cm_lvalue_output_type =
    cst_add_const_to_header(`cm_lvalue_output_type`);

PROOF thm cm_exprs_type_ready_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(!p f. cm_exprs_type_ready (p:cm_program) (f:cm_function_d)
        ([]:(cm_expr)list) = T) &&
     (!p f expr rest.
        cm_exprs_type_ready p f
          ((expr:cm_expr) :: (rest:(cm_expr)list)) =
        (cm_expr_wf p f expr &&
         cm_scalar_expr_type (cm_expr_type expr) &&
         cm_exprs_type_ready p f rest))`);
PROOF static int _e_cm_exprs_type_ready =
    cst_add_const_to_header(`cm_exprs_type_ready`);

PROOF thm cm_value_type_compatible_def = new_fun_definition(
    `cm_value_type_compatible (v:cm_value) (ty:cm_type) : bool =
       (cm_value_type v == ty ||
        (v == CMNullV && cm_is_pointer ty))`);
PROOF static int _e_cm_value_type_compatible =
    cst_add_const_to_header(`cm_value_type_compatible`);

PROOF thm cm_expr_value_type_ready_def = new_fun_definition(
    `cm_expr_value_type_ready (expr:cm_expr) (v:cm_value) : bool =
       (cm_value_type_compatible v (cm_expr_type expr) &&
        (cm_zero_literal expr ==> v == CMIntV 0i))`);
PROOF static int _e_cm_expr_value_type_ready =
    cst_add_const_to_header(`cm_expr_value_type_ready`);

PROOF thm cm_value_convertible_to_def = new_fun_definition(
    `cm_value_convertible_to (v:cm_value) (ty:cm_type) : bool =
       (cm_convertible (cm_value_type v) ty ||
        (v == CMIntV 0i && cm_is_pointer ty))`);
PROOF static int _e_cm_value_convertible_to =
    cst_add_const_to_header(`cm_value_convertible_to`);

PROOF thm cm_arg_next_type_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(!slots.
        cm_arg_next_type (slots:(cm_slot_d)list)
          ([]:(cm_value)list) = cm_slot_ty (HD slots)) &&
     (!slots v done.
        cm_arg_next_type (slots:(cm_slot_d)list)
          ((v:cm_value) :: (done:(cm_value)list)) =
        cm_arg_next_type (TL slots) done)`);
PROOF static int _e_cm_arg_next_type =
    cst_add_const_to_header(`cm_arg_next_type`);

PROOF thm cm_arg_progress_type_ready_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(!all_args slots rest.
        cm_arg_progress_type_ready
          (all_args:(cm_expr)list) (slots:(cm_slot_d)list)
          ([]:(cm_value)list) (rest:(cm_expr)list) =
        (~(all_args == []) && ~(slots == []) && TL all_args == rest)) &&
     (!all_args slots v done rest.
        cm_arg_progress_type_ready
          (all_args:(cm_expr)list) (slots:(cm_slot_d)list)
          ((v:cm_value) :: (done:(cm_value)list))
          (rest:(cm_expr)list) =
        (~(all_args == []) && ~(slots == []) &&
         cm_value_convertible_to v (cm_slot_ty (HD slots)) &&
         cm_arg_progress_type_ready
           (TL all_args) (TL slots) done rest))`);
PROOF static int _e_cm_arg_progress_type_ready =
    cst_add_const_to_header(`cm_arg_progress_type_ready`);


PROOF thm cm_phase_input_type_ready_def = new_rec_definition(
    get_cm_aphase_recursion(),
    `(!p fid incoming.
        cm_phase_input_type_ready (p:cm_program) (fid:int)
          CAHaltP (incoming:cm_type) = T) &&
     (!p fid incoming ty.
        cm_phase_input_type_ready p fid (CALoadP (ty:cm_type))
          (incoming:cm_type) = (incoming == CMPtrTy ty)) &&
     (!p fid incoming src ty.
        cm_phase_input_type_ready p fid
          (CAAssignLP (src:cm_expr) (ty:cm_type)) (incoming:cm_type) =
        (incoming == CMPtrTy ty)) &&
     (!p fid incoming ptr ty.
        cm_phase_input_type_ready p fid
          (CAAssignRP (ptr:cm_value) (ty:cm_type)) (incoming:cm_type) =
        T) &&
     (!p fid incoming op left right ty.
        cm_phase_input_type_ready p fid
          (CABinLP (op:int) (left:cm_expr) (right:cm_expr)
            (ty:cm_type)) (incoming:cm_type) =
        (incoming == cm_expr_type left)) &&
     (!p fid incoming op left right value ty.
        cm_phase_input_type_ready p fid
          (CABinRP (op:int) (left:cm_expr) (right:cm_expr)
            (value:cm_value) (ty:cm_type)) (incoming:cm_type) =
        (incoming == cm_expr_type right)) &&
     (!p fid incoming op.
        cm_phase_input_type_ready p fid (CAUnaryP (op:int))
          (incoming:cm_type) = cm_integer_type incoming) &&
     (!p fid incoming index ty.
        cm_phase_input_type_ready p fid
          (CAIndexLP (index:cm_expr) (ty:cm_type)) (incoming:cm_type) =
        (incoming == CMPtrTy ty)) &&
     (!p fid incoming base ty.
        cm_phase_input_type_ready p fid
          (CAIndexRP (base:cm_value) (ty:cm_type)) (incoming:cm_type) =
        cm_integer_type incoming) &&
     (!p fid incoming mid base_ty.
        cm_phase_input_type_ready p fid
          (CAMemberP (mid:int) (base_ty:cm_type)) (incoming:cm_type) =
        (incoming == base_ty)) &&
     (!p fid incoming.
        cm_phase_input_type_ready p fid CAPutcP (incoming:cm_type) =
        cm_scalar_expr_type incoming) &&
     (!p fid incoming.
        cm_phase_input_type_ready p fid CAPutiP (incoming:cm_type) =
        cm_integer_type incoming) &&
     (!p fid incoming.
        cm_phase_input_type_ready p fid CAExitP (incoming:cm_type) =
        cm_integer_type incoming) &&
     (!p fid incoming.
        cm_phase_input_type_ready p fid CAExprStmtP (incoming:cm_type) =
        cm_scalar_expr_type incoming) &&
     (!p fid incoming slot.
        cm_phase_input_type_ready p fid (CAInitP (slot:int))
          (incoming:cm_type) = T) &&
     (!p fid incoming env regions jump target.
        cm_phase_input_type_ready p fid
          (CABlockP (env:int->int->cm_value) (regions:(cm_region)list)
            (jump:bool) (target:int)) (incoming:cm_type) = F) &&
     (!p fid incoming second.
        cm_phase_input_type_ready p fid (CASeqP (second:cm_stmt))
          (incoming:cm_type) = F) &&
     (!p fid incoming yes no.
        cm_phase_input_type_ready p fid
          (CAIfP (yes:cm_stmt) (no:cm_stmt)) (incoming:cm_type) =
        cm_scalar_expr_type incoming) &&
     (!p fid incoming guard body loop_start loop_end.
        cm_phase_input_type_ready p fid
          (CAWhileGuardP (guard:cm_expr) (body:cm_stmt)
            (loop_start:int) (loop_end:int)) (incoming:cm_type) =
        cm_scalar_expr_type incoming) &&
     (!p fid incoming guard body env regions loop_start loop_end.
        cm_phase_input_type_ready p fid
          (CAWhileBodyP (guard:cm_expr) (body:cm_stmt)
            (env:int->int->cm_value) (regions:(cm_region)list)
            (loop_start:int) (loop_end:int)) (incoming:cm_type) = F) &&
     (!p fid incoming.
        cm_phase_input_type_ready p fid CAReturnP (incoming:cm_type) = T) &&
     (!p fid incoming callee rest values ret all_args base_slot
         current_slot scratch.
        cm_phase_input_type_ready p fid
          (CAArgP (callee:int) (rest:(cm_expr)list)
            (values:(cm_value)list) (ret:cm_type)
            (all_args:(cm_expr)list) (base_slot:int)
            (current_slot:int) (scratch:int)) (incoming:cm_type) = T) &&
     (!p fid incoming caller env fp regions ret.
        cm_phase_input_type_ready p fid
          (CACallP (caller:int) (env:int->int->cm_value) (fp:int)
            (regions:(cm_region)list) (ret:cm_type))
          (incoming:cm_type) = F)`);
PROOF static int _e_cm_phase_input_type_ready =
    cst_add_const_to_header(`cm_phase_input_type_ready`);

PROOF thm cm_cursor_head_input_type_ready_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(!p fid incoming.
        cm_cursor_head_input_type_ready (p:cm_program) (fid:int)
          (incoming:cm_type) ([]:(cm_acursor)list) = F) &&
     (!p fid incoming cursor rest.
        cm_cursor_head_input_type_ready p fid (incoming:cm_type)
          ((cursor:cm_acursor) :: (rest:(cm_acursor)list)) =
        cm_phase_input_type_ready p fid
          (cm_cursor_phase cursor) incoming)`);
PROOF static int _e_cm_cursor_head_input_type_ready =
    cst_add_const_to_header(`cm_cursor_head_input_type_ready`);

PROOF thm cm_phase_value_type_ready_def = new_rec_definition(
    get_cm_aphase_recursion(),
    `(!p fid v.
        cm_phase_value_type_ready (p:cm_program) (fid:int)
          CAHaltP (v:cm_value) = T) &&
     (!p fid v ty.
        cm_phase_value_type_ready p fid (CALoadP (ty:cm_type))
          (v:cm_value) =
        cm_value_type_compatible v (CMPtrTy ty)) &&
     (!p fid v src ty.
        cm_phase_value_type_ready p fid
          (CAAssignLP (src:cm_expr) (ty:cm_type)) (v:cm_value) =
        cm_value_type_compatible v (CMPtrTy ty)) &&
     (!p fid v ptr ty.
        cm_phase_value_type_ready p fid
          (CAAssignRP (ptr:cm_value) (ty:cm_type)) (v:cm_value) =
        cm_value_convertible_to v ty) &&
     (!p fid v op left right ty.
        cm_phase_value_type_ready p fid
          (CABinLP (op:int) (left:cm_expr) (right:cm_expr)
            (ty:cm_type)) (v:cm_value) =
        cm_value_type_compatible v (cm_expr_type left)) &&
     (!p fid v op left right saved ty.
        cm_phase_value_type_ready p fid
          (CABinRP (op:int) (left:cm_expr) (right:cm_expr)
            (saved:cm_value) (ty:cm_type)) (v:cm_value) =
        cm_value_type_compatible v (cm_expr_type right)) &&
     (!p fid v op.
        cm_phase_value_type_ready p fid (CAUnaryP (op:int))
          (v:cm_value) = cm_integer_type (cm_value_type v)) &&
     (!p fid v index ty.
        cm_phase_value_type_ready p fid
          (CAIndexLP (index:cm_expr) (ty:cm_type)) (v:cm_value) =
        cm_value_type_compatible v (CMPtrTy ty)) &&
     (!p fid v base ty.
        cm_phase_value_type_ready p fid
          (CAIndexRP (base:cm_value) (ty:cm_type)) (v:cm_value) =
        cm_integer_type (cm_value_type v)) &&
     (!p fid v mid base_ty.
        cm_phase_value_type_ready p fid
          (CAMemberP (mid:int) (base_ty:cm_type)) (v:cm_value) =
        cm_value_type_compatible v base_ty) &&
     (!p fid v.
        cm_phase_value_type_ready p fid CAPutcP (v:cm_value) =
        cm_scalar_expr_type (cm_value_type v)) &&
     (!p fid v.
        cm_phase_value_type_ready p fid CAPutiP (v:cm_value) =
        cm_integer_type (cm_value_type v)) &&
     (!p fid v.
        cm_phase_value_type_ready p fid CAExitP (v:cm_value) =
        cm_integer_type (cm_value_type v)) &&
     (!p fid v.
        cm_phase_value_type_ready p fid CAExprStmtP (v:cm_value) =
        cm_scalar_expr_type (cm_value_type v)) &&
     (!p fid v slot.
        cm_phase_value_type_ready p fid (CAInitP (slot:int))
          (v:cm_value) =
        cm_value_convertible_to v
          (cm_slot_ty
            (inth slot
              (cm_function_locals
                (inth fid (cm_program_functions p)))))) &&
     (!p fid v env regions jump target.
        cm_phase_value_type_ready p fid
          (CABlockP (env:int->int->cm_value) (regions:(cm_region)list)
            (jump:bool) (target:int)) (v:cm_value) = F) &&
     (!p fid v second.
        cm_phase_value_type_ready p fid (CASeqP (second:cm_stmt))
          (v:cm_value) = F) &&
     (!p fid v yes no.
        cm_phase_value_type_ready p fid
          (CAIfP (yes:cm_stmt) (no:cm_stmt)) (v:cm_value) =
        cm_scalar_expr_type (cm_value_type v)) &&
     (!p fid v guard body loop_start loop_end.
        cm_phase_value_type_ready p fid
          (CAWhileGuardP (guard:cm_expr) (body:cm_stmt)
            (loop_start:int) (loop_end:int)) (v:cm_value) =
        cm_scalar_expr_type (cm_value_type v)) &&
     (!p fid v guard body env regions loop_start loop_end.
        cm_phase_value_type_ready p fid
          (CAWhileBodyP (guard:cm_expr) (body:cm_stmt)
            (env:int->int->cm_value) (regions:(cm_region)list)
            (loop_start:int) (loop_end:int)) (v:cm_value) = F) &&
     (!p fid v.
        cm_phase_value_type_ready p fid CAReturnP (v:cm_value) =
        cm_value_convertible_to v
          (cm_function_ret (inth fid (cm_program_functions p)))) &&
     (!p fid v callee rest values ret all_args base_slot
         current_slot scratch.
        cm_phase_value_type_ready p fid
          (CAArgP (callee:int) (rest:(cm_expr)list)
            (values:(cm_value)list) (ret:cm_type)
            (all_args:(cm_expr)list) (base_slot:int)
            (current_slot:int) (scratch:int)) (v:cm_value) =
        cm_value_convertible_to v
          (cm_arg_next_type
            (cm_function_params
              (inth callee (cm_program_functions p)))
            (REVERSE values))) &&
     (!p fid v caller env fp regions ret.
        cm_phase_value_type_ready p fid
          (CACallP (caller:int) (env:int->int->cm_value) (fp:int)
            (regions:(cm_region)list) (ret:cm_type))
          (v:cm_value) = F)`);
PROOF static int _e_cm_phase_value_type_ready =
    cst_add_const_to_header(`cm_phase_value_type_ready`);

PROOF thm cm_control_type_ready_def = new_rec_definition(
    get_cm_control_recursion(),
    `(cm_control_type_ready (p:cm_program) (fid:int) CMNormal = T) &&
     (cm_control_type_ready p fid CMBreak = T) &&
     (cm_control_type_ready p fid CMContinue = T) &&
     (!v. cm_control_type_ready p fid (CMReturn (v:cm_value)) =
        cm_value_convertible_to v
          (cm_function_ret (inth fid (cm_program_functions p)))) &&
     (!status.
        cm_control_type_ready p fid (CMExit (status:int)) = T) &&
     (!code.
        cm_control_type_ready p fid (CMError (code:int)) = T)`);
PROOF static int _e_cm_control_type_ready =
    cst_add_const_to_header(`cm_control_type_ready`);

PROOF thm cm_cursor_head_value_type_ready_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(!p fid v.
        cm_cursor_head_value_type_ready (p:cm_program) (fid:int)
          (v:cm_value) ([]:(cm_acursor)list) = F) &&
     (!p fid v cursor rest.
        cm_cursor_head_value_type_ready p fid (v:cm_value)
          ((cursor:cm_acursor) :: (rest:(cm_acursor)list)) =
        cm_phase_value_type_ready p fid
          (cm_cursor_phase cursor) v)`);
PROOF static int _e_cm_cursor_head_value_type_ready =
    cst_add_const_to_header(`cm_cursor_head_value_type_ready`);

PROOF thm cm_phase_result_type_def = new_rec_definition(
    get_cm_aphase_recursion(),
    `(!p fid result.
        cm_phase_result_type (p:cm_program) (fid:int)
          CAHaltP (result:cm_type) = F) &&
     (!p fid result ty.
        cm_phase_result_type p fid (CALoadP (ty:cm_type))
          (result:cm_type) = (result == ty)) &&
     (!p fid result src ty.
        cm_phase_result_type p fid
          (CAAssignLP (src:cm_expr) (ty:cm_type))
          (result:cm_type) = (result == ty)) &&
     (!p fid result ptr ty.
        cm_phase_result_type p fid
          (CAAssignRP (ptr:cm_value) (ty:cm_type))
          (result:cm_type) = (result == ty)) &&
     (!p fid result op left right ty.
        cm_phase_result_type p fid
          (CABinLP (op:int) (left:cm_expr) (right:cm_expr)
            (ty:cm_type)) (result:cm_type) = (result == ty)) &&
     (!p fid result op left right saved ty.
        cm_phase_result_type p fid
          (CABinRP (op:int) (left:cm_expr) (right:cm_expr)
            (saved:cm_value) (ty:cm_type))
          (result:cm_type) = (result == ty)) &&
     (!p fid result op.
        cm_phase_result_type p fid (CAUnaryP (op:int))
          (result:cm_type) = (result == CMIntTy)) &&
     (!p fid result index ty.
        cm_phase_result_type p fid
          (CAIndexLP (index:cm_expr) (ty:cm_type))
          (result:cm_type) = (result == CMPtrTy ty)) &&
     (!p fid result base ty.
        cm_phase_result_type p fid
          (CAIndexRP (base:cm_value) (ty:cm_type))
          (result:cm_type) = (result == CMPtrTy ty)) &&
     (!p fid result mid base_ty.
        cm_phase_result_type p fid
          (CAMemberP (mid:int) (base_ty:cm_type))
          (result:cm_type) =
        (result == cm_member_lvalue_type p base_ty mid)) &&
     (!p fid result.
        cm_phase_result_type p fid CAPutcP (result:cm_type) =
        (result == CMIntTy)) &&
     (!p fid result.
        cm_phase_result_type p fid CAPutiP (result:cm_type) =
        (result == CMIntTy)) &&
     (!p fid result.
        cm_phase_result_type p fid CAExitP (result:cm_type) = F) &&
     (!p fid result.
        cm_phase_result_type p fid CAExprStmtP (result:cm_type) = F) &&
     (!p fid result slot.
        cm_phase_result_type p fid (CAInitP (slot:int))
          (result:cm_type) = F) &&
     (!p fid result env regions jump target.
        cm_phase_result_type p fid
          (CABlockP (env:int->int->cm_value) (regions:(cm_region)list)
            (jump:bool) (target:int)) (result:cm_type) = F) &&
     (!p fid result second.
        cm_phase_result_type p fid (CASeqP (second:cm_stmt))
          (result:cm_type) = F) &&
     (!p fid result yes no.
        cm_phase_result_type p fid
          (CAIfP (yes:cm_stmt) (no:cm_stmt))
          (result:cm_type) = F) &&
     (!p fid result guard body loop_start loop_end.
        cm_phase_result_type p fid
          (CAWhileGuardP (guard:cm_expr) (body:cm_stmt)
            (loop_start:int) (loop_end:int))
          (result:cm_type) = F) &&
     (!p fid result guard body env regions loop_start loop_end.
        cm_phase_result_type p fid
          (CAWhileBodyP (guard:cm_expr) (body:cm_stmt)
            (env:int->int->cm_value) (regions:(cm_region)list)
            (loop_start:int) (loop_end:int))
          (result:cm_type) = F) &&
     (!p fid result.
        cm_phase_result_type p fid CAReturnP (result:cm_type) = F) &&
     (!p fid result callee exprs values ret all_args base_slot
         current_slot scratch.
        cm_phase_result_type p fid
          (CAArgP (callee:int) (exprs:(cm_expr)list)
            (values:(cm_value)list) (ret:cm_type)
            (all_args:(cm_expr)list) (base_slot:int)
            (current_slot:int) (scratch:int))
          (result:cm_type) = (result == ret)) &&
     (!p fid result caller env fp regions ret.
        cm_phase_result_type p fid
          (CACallP (caller:int) (env:int->int->cm_value) (fp:int)
            (regions:(cm_region)list) (ret:cm_type))
          (result:cm_type) = (result == ret))`);
PROOF static int _e_cm_phase_result_type =
    cst_add_const_to_header(`cm_phase_result_type`);

PROOF thm cm_phase_result_type_ready_def = new_fun_definition(
    `cm_phase_result_type_ready (p:cm_program) (fid:int)
       (phase:cm_aphase) (rest:(cm_acursor)list) : bool =
       !(result:cm_type) (v:cm_value).
         cm_phase_result_type p fid phase result ==>
         cm_value_type_compatible v result ==>
         cm_cursor_head_value_type_ready p
           (cm_phase_next_fid fid phase) v rest`);
PROOF static int _e_cm_phase_result_type_ready =
    cst_add_const_to_header(`cm_phase_result_type_ready`);

PROOF thm cm_phase_expr_type_ready_def = new_rec_definition(
    get_cm_aphase_recursion(),
    `(!p fid expr.
        cm_phase_expr_type_ready (p:cm_program) (fid:int)
          CAHaltP (expr:cm_expr) = T) &&
     (!p fid expr ty.
        cm_phase_expr_type_ready p fid (CALoadP (ty:cm_type))
          (expr:cm_expr) =
        (cm_expr_type expr == CMPtrTy ty)) &&
     (!p fid expr src ty.
        cm_phase_expr_type_ready p fid
          (CAAssignLP (src:cm_expr) (ty:cm_type)) (expr:cm_expr) =
        (cm_expr_type expr == CMPtrTy ty)) &&
     (!p fid expr ptr ty.
        cm_phase_expr_type_ready p fid
          (CAAssignRP (ptr:cm_value) (ty:cm_type)) (expr:cm_expr) =
        cm_expr_convertible expr ty) &&
     (!p fid expr op left right ty.
        cm_phase_expr_type_ready p fid
          (CABinLP (op:int) (left:cm_expr) (right:cm_expr)
            (ty:cm_type)) (expr:cm_expr) =
        (cm_expr_type expr == cm_expr_type left)) &&
     (!p fid expr op left right saved ty.
        cm_phase_expr_type_ready p fid
          (CABinRP (op:int) (left:cm_expr) (right:cm_expr)
            (saved:cm_value) (ty:cm_type)) (expr:cm_expr) =
        (cm_expr_type expr == cm_expr_type right)) &&
     (!p fid expr op.
        cm_phase_expr_type_ready p fid (CAUnaryP (op:int))
          (expr:cm_expr) = cm_integer_type (cm_expr_type expr)) &&
     (!p fid expr index ty.
        cm_phase_expr_type_ready p fid
          (CAIndexLP (index:cm_expr) (ty:cm_type)) (expr:cm_expr) =
        (cm_expr_type expr == CMPtrTy ty)) &&
     (!p fid expr base ty.
        cm_phase_expr_type_ready p fid
          (CAIndexRP (base:cm_value) (ty:cm_type)) (expr:cm_expr) =
        cm_integer_type (cm_expr_type expr)) &&
     (!p fid expr mid base_ty.
        cm_phase_expr_type_ready p fid
          (CAMemberP (mid:int) (base_ty:cm_type)) (expr:cm_expr) =
        (cm_expr_type expr == base_ty)) &&
     (!p fid expr.
        cm_phase_expr_type_ready p fid CAPutcP (expr:cm_expr) =
        cm_scalar_expr_type (cm_expr_type expr)) &&
     (!p fid expr.
        cm_phase_expr_type_ready p fid CAPutiP (expr:cm_expr) =
        cm_integer_type (cm_expr_type expr)) &&
     (!p fid expr.
        cm_phase_expr_type_ready p fid CAExitP (expr:cm_expr) =
        cm_integer_type (cm_expr_type expr)) &&
     (!p fid expr.
        cm_phase_expr_type_ready p fid CAExprStmtP (expr:cm_expr) =
        cm_scalar_expr_type (cm_expr_type expr)) &&
     (!p fid expr slot.
        cm_phase_expr_type_ready p fid (CAInitP (slot:int))
          (expr:cm_expr) =
        cm_expr_convertible expr
          (cm_slot_ty
            (inth slot
              (cm_function_locals
                (inth fid (cm_program_functions p)))))) &&
     (!p fid expr env regions jump target.
        cm_phase_expr_type_ready p fid
          (CABlockP (env:int->int->cm_value) (regions:(cm_region)list)
            (jump:bool) (target:int)) (expr:cm_expr) = F) &&
     (!p fid expr second.
        cm_phase_expr_type_ready p fid (CASeqP (second:cm_stmt))
          (expr:cm_expr) = F) &&
     (!p fid expr yes no.
        cm_phase_expr_type_ready p fid
          (CAIfP (yes:cm_stmt) (no:cm_stmt)) (expr:cm_expr) =
        cm_scalar_expr_type (cm_expr_type expr)) &&
     (!p fid expr guard body loop_start loop_end.
        cm_phase_expr_type_ready p fid
          (CAWhileGuardP (guard:cm_expr) (body:cm_stmt)
            (loop_start:int) (loop_end:int)) (expr:cm_expr) =
        cm_scalar_expr_type (cm_expr_type expr)) &&
     (!p fid expr guard body env regions loop_start loop_end.
        cm_phase_expr_type_ready p fid
          (CAWhileBodyP (guard:cm_expr) (body:cm_stmt)
            (env:int->int->cm_value) (regions:(cm_region)list)
            (loop_start:int) (loop_end:int)) (expr:cm_expr) = F) &&
     (!p fid expr.
        cm_phase_expr_type_ready p fid CAReturnP (expr:cm_expr) =
        cm_expr_convertible expr
          (cm_function_ret (inth fid (cm_program_functions p)))) &&
     (!p fid expr callee rest values ret all_args base_slot
         current_slot scratch.
        cm_phase_expr_type_ready p fid
          (CAArgP (callee:int) (rest:(cm_expr)list)
            (values:(cm_value)list) (ret:cm_type)
            (all_args:(cm_expr)list) (base_slot:int)
            (current_slot:int) (scratch:int)) (expr:cm_expr) =
        cm_expr_convertible expr
          (cm_arg_next_type
            (cm_function_params
              (inth callee (cm_program_functions p)))
            (REVERSE values))) &&
     (!p fid expr caller env fp regions ret.
        cm_phase_expr_type_ready p fid
          (CACallP (caller:int) (env:int->int->cm_value) (fp:int)
            (regions:(cm_region)list) (ret:cm_type))
          (expr:cm_expr) = F)`);
PROOF static int _e_cm_phase_expr_type_ready =
    cst_add_const_to_header(`cm_phase_expr_type_ready`);

PROOF thm cm_cursor_head_expr_type_ready_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(!p fid expr.
        cm_cursor_head_expr_type_ready (p:cm_program) (fid:int)
          (expr:cm_expr) ([]:(cm_acursor)list) = F) &&
     (!p fid expr cursor rest.
        cm_cursor_head_expr_type_ready p fid (expr:cm_expr)
          ((cursor:cm_acursor) :: (rest:(cm_acursor)list)) =
        cm_phase_expr_type_ready p fid
          (cm_cursor_phase cursor) expr)`);
PROOF static int _e_cm_cursor_head_expr_type_ready =
    cst_add_const_to_header(`cm_cursor_head_expr_type_ready`);

PROOF thm cm_cursor_expr_values_type_ready_def = new_fun_definition(
    `cm_cursor_expr_values_type_ready (p:cm_program) (fid:int)
       (expr:cm_expr) (cursors:(cm_acursor)list) : bool =
       !(v:cm_value).
         cm_expr_value_type_ready expr v ==>
         cm_cursor_head_value_type_ready p fid v cursors`);
PROOF static int _e_cm_cursor_expr_values_type_ready =
    cst_add_const_to_header(`cm_cursor_expr_values_type_ready`);

PROOF thm cm_phase_lvalue_type_ready_def = new_fun_definition(
    `cm_phase_lvalue_type_ready (p:cm_program) (fid:int)
       (phase:cm_aphase) (output:cm_type) : bool =
       !(v:cm_value).
         cm_value_type_compatible v output ==>
         cm_phase_value_type_ready p fid phase v`);
PROOF static int _e_cm_phase_lvalue_type_ready =
    cst_add_const_to_header(`cm_phase_lvalue_type_ready`);

PROOF thm cm_cursor_head_lvalue_type_ready_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(!p fid output.
        cm_cursor_head_lvalue_type_ready (p:cm_program) (fid:int)
          (output:cm_type) ([]:(cm_acursor)list) = F) &&
     (!p fid output cursor rest.
        cm_cursor_head_lvalue_type_ready p fid (output:cm_type)
          ((cursor:cm_acursor) :: (rest:(cm_acursor)list)) =
        cm_phase_lvalue_type_ready p fid
          (cm_cursor_phase cursor) output)`);
PROOF static int _e_cm_cursor_head_lvalue_type_ready =
    cst_add_const_to_header(`cm_cursor_head_lvalue_type_ready`);

PROOF thm cm_phase_static_type_ready_def = new_rec_definition(
    get_cm_aphase_recursion(),
    `(!p fid. cm_phase_static_type_ready (p:cm_program) (fid:int)
        CAHaltP = T) &&
     (!p fid ty. cm_phase_static_type_ready p fid
        (CALoadP (ty:cm_type)) =
        cm_scalar_expr_type ty) &&
     (!p fid src ty. cm_phase_static_type_ready p fid
        (CAAssignLP (src:cm_expr) (ty:cm_type)) =
        (cm_expr_wf p (inth fid (cm_program_functions p)) src &&
         cm_expr_convertible src ty &&
         cm_scalar_expr_type ty)) &&
     (!p fid ptr ty. cm_phase_static_type_ready p fid
        (CAAssignRP (ptr:cm_value) (ty:cm_type)) =
        (cm_value_type_compatible ptr (CMPtrTy ty) &&
         cm_scalar_expr_type ty)) &&
     (!p fid op left right ty. cm_phase_static_type_ready p fid
        (CABinLP (op:int) (left:cm_expr) (right:cm_expr)
          (ty:cm_type)) =
        cm_expr_wf p (inth fid (cm_program_functions p))
          (CMBinaryE op left right ty)) &&
     (!p fid op left right value ty. cm_phase_static_type_ready p fid
        (CABinRP (op:int) (left:cm_expr) (right:cm_expr)
          (value:cm_value) (ty:cm_type)) =
        (cm_expr_wf p (inth fid (cm_program_functions p))
           (CMBinaryE op left right ty) &&
         cm_value_type_compatible value (cm_expr_type left))) &&
     (!p fid op. cm_phase_static_type_ready p fid
        (CAUnaryP (op:int)) = (op == 0i || op == 1i)) &&
     (!p fid index ty. cm_phase_static_type_ready p fid
        (CAIndexLP (index:cm_expr) (ty:cm_type)) =
        (cm_expr_wf p (inth fid (cm_program_functions p)) index &&
         cm_integer_type (cm_expr_type index) &&
         cm_type_refs (cm_program_structs p) ty)) &&
     (!p fid base ty. cm_phase_static_type_ready p fid
        (CAIndexRP (base:cm_value) (ty:cm_type)) =
        (cm_value_type_compatible base (CMPtrTy ty) &&
         cm_type_refs (cm_program_structs p) ty)) &&
     (!p fid mid base_ty. cm_phase_static_type_ready p fid
        (CAMemberP (mid:int) (base_ty:cm_type)) =
        cm_member_valid p base_ty mid) &&
     (!p fid. cm_phase_static_type_ready p fid CAPutcP = T) &&
     (!p fid. cm_phase_static_type_ready p fid CAPutiP = T) &&
     (!p fid. cm_phase_static_type_ready p fid CAExitP = T) &&
     (!p fid. cm_phase_static_type_ready p fid CAExprStmtP = T) &&
     (!p fid slot. cm_phase_static_type_ready p fid
        (CAInitP (slot:int)) =
        (0i <= slot &&
         slot < ilength
           (cm_function_locals (inth fid (cm_program_functions p))) &&
         cm_slot_count
           (inth slot
             (cm_function_locals
               (inth fid (cm_program_functions p)))) == 0i &&
         cm_scalar_type (cm_program_structs p)
           (cm_slot_ty
             (inth slot
               (cm_function_locals
                 (inth fid (cm_program_functions p))))))) &&
     (!p fid env regions jump target. cm_phase_static_type_ready p fid
        (CABlockP (env:int->int->cm_value) (regions:(cm_region)list)
          (jump:bool) (target:int)) = T) &&
     (!p fid second. cm_phase_static_type_ready p fid
        (CASeqP (second:cm_stmt)) =
        cm_stmt_wf p (inth fid (cm_program_functions p)) T second) &&
     (!p fid yes no. cm_phase_static_type_ready p fid
        (CAIfP (yes:cm_stmt) (no:cm_stmt)) =
        (cm_stmt_wf p (inth fid (cm_program_functions p)) T yes &&
         cm_stmt_wf p (inth fid (cm_program_functions p)) T no)) &&
     (!p fid guard body loop_start loop_end.
        cm_phase_static_type_ready p fid
          (CAWhileGuardP (guard:cm_expr) (body:cm_stmt)
            (loop_start:int) (loop_end:int)) =
        (cm_expr_wf p (inth fid (cm_program_functions p)) guard &&
         cm_scalar_expr_type (cm_expr_type guard) &&
         cm_stmt_wf p (inth fid (cm_program_functions p)) T body)) &&
     (!p fid guard body env regions loop_start loop_end.
        cm_phase_static_type_ready p fid
          (CAWhileBodyP (guard:cm_expr) (body:cm_stmt)
            (env:int->int->cm_value) (regions:(cm_region)list)
            (loop_start:int) (loop_end:int)) =
        (cm_expr_wf p (inth fid (cm_program_functions p)) guard &&
         cm_scalar_expr_type (cm_expr_type guard) &&
         cm_stmt_wf p (inth fid (cm_program_functions p)) T body)) &&
     (!p fid. cm_phase_static_type_ready p fid CAReturnP = T) &&
     (!p fid callee rest values ret all_args base_slot current_slot scratch.
        cm_phase_static_type_ready p fid
          (CAArgP (callee:int) (rest:(cm_expr)list)
            (values:(cm_value)list) (ret:cm_type)
            (all_args:(cm_expr)list) (base_slot:int)
            (current_slot:int) (scratch:int)) =
        (0i <= callee && callee < ilength (cm_program_functions p) &&
         cm_exprs_type_ready p
           (inth fid (cm_program_functions p)) rest &&
         cm_args_wf p (inth fid (cm_program_functions p)) all_args
           (cm_function_params
             (inth callee (cm_program_functions p))) &&
         cm_arg_progress_type_ready all_args
           (cm_function_params
             (inth callee (cm_program_functions p)))
           (REVERSE values) rest &&
         ret == cm_function_ret
           (inth callee (cm_program_functions p)))) &&
     (!p fid caller env fp regions ret.
        cm_phase_static_type_ready p fid
          (CACallP (caller:int) (env:int->int->cm_value) (fp:int)
            (regions:(cm_region)list) (ret:cm_type)) =
        (0i <= fid && fid < ilength (cm_program_functions p) &&
         (caller == --1i ||
          (0i <= caller && caller < ilength (cm_program_functions p))) &&
         ret == cm_function_ret
           (inth fid (cm_program_functions p))))`);
PROOF static int _e_cm_phase_static_type_ready =
    cst_add_const_to_header(`cm_phase_static_type_ready`);

PROOF thm cm_phase_parent_type_ready_def = new_rec_definition(
    get_cm_aphase_recursion(),
    `(!p fid rest. cm_phase_parent_type_ready (p:cm_program) (fid:int)
        CAHaltP (rest:(cm_acursor)list) = (rest == [])) &&
     (!p fid ty rest. cm_phase_parent_type_ready p fid
        (CALoadP (ty:cm_type)) (rest:(cm_acursor)list) =
        cm_cursor_head_input_type_ready p fid ty rest) &&
     (!p fid src ty rest. cm_phase_parent_type_ready p fid
        (CAAssignLP (src:cm_expr) (ty:cm_type))
          (rest:(cm_acursor)list) =
        cm_cursor_head_input_type_ready p fid ty rest) &&
     (!p fid ptr ty rest. cm_phase_parent_type_ready p fid
        (CAAssignRP (ptr:cm_value) (ty:cm_type))
          (rest:(cm_acursor)list) =
        cm_cursor_head_input_type_ready p fid ty rest) &&
     (!p fid op left right ty rest. cm_phase_parent_type_ready p fid
        (CABinLP (op:int) (left:cm_expr) (right:cm_expr)
          (ty:cm_type)) (rest:(cm_acursor)list) =
        cm_cursor_head_input_type_ready p fid ty rest) &&
     (!p fid op left right value ty rest.
        cm_phase_parent_type_ready p fid
          (CABinRP (op:int) (left:cm_expr) (right:cm_expr)
            (value:cm_value) (ty:cm_type)) (rest:(cm_acursor)list) =
        cm_cursor_head_input_type_ready p fid ty rest) &&
     (!p fid op rest. cm_phase_parent_type_ready p fid
        (CAUnaryP (op:int)) (rest:(cm_acursor)list) =
        cm_cursor_head_input_type_ready p fid CMIntTy rest) &&
     (!p fid index ty rest. cm_phase_parent_type_ready p fid
        (CAIndexLP (index:cm_expr) (ty:cm_type))
          (rest:(cm_acursor)list) =
        cm_cursor_head_input_type_ready p fid (CMPtrTy ty) rest) &&
     (!p fid base ty rest. cm_phase_parent_type_ready p fid
        (CAIndexRP (base:cm_value) (ty:cm_type))
          (rest:(cm_acursor)list) =
        cm_cursor_head_input_type_ready p fid (CMPtrTy ty) rest) &&
     (!p fid mid base_ty rest. cm_phase_parent_type_ready p fid
        (CAMemberP (mid:int) (base_ty:cm_type))
          (rest:(cm_acursor)list) =
        cm_cursor_head_input_type_ready p fid
          (cm_member_lvalue_type p base_ty mid) rest) &&
     (!p fid rest. cm_phase_parent_type_ready p fid CAPutcP
        (rest:(cm_acursor)list) =
        cm_cursor_head_input_type_ready p fid CMIntTy rest) &&
     (!p fid rest. cm_phase_parent_type_ready p fid CAPutiP
        (rest:(cm_acursor)list) =
        cm_cursor_head_input_type_ready p fid CMIntTy rest) &&
     (!p fid rest. cm_phase_parent_type_ready p fid CAExitP
        (rest:(cm_acursor)list) = T) &&
     (!p fid rest. cm_phase_parent_type_ready p fid CAExprStmtP
        (rest:(cm_acursor)list) = T) &&
     (!p fid slot rest. cm_phase_parent_type_ready p fid
        (CAInitP (slot:int)) (rest:(cm_acursor)list) = T) &&
     (!p fid env regions jump target rest.
        cm_phase_parent_type_ready p fid
          (CABlockP (env:int->int->cm_value) (regions:(cm_region)list)
            (jump:bool) (target:int)) (rest:(cm_acursor)list) = T) &&
     (!p fid second rest. cm_phase_parent_type_ready p fid
        (CASeqP (second:cm_stmt)) (rest:(cm_acursor)list) = T) &&
     (!p fid yes no rest. cm_phase_parent_type_ready p fid
        (CAIfP (yes:cm_stmt) (no:cm_stmt))
          (rest:(cm_acursor)list) = T) &&
     (!p fid guard body loop_start loop_end rest.
        cm_phase_parent_type_ready p fid
          (CAWhileGuardP (guard:cm_expr) (body:cm_stmt)
            (loop_start:int) (loop_end:int))
          (rest:(cm_acursor)list) = T) &&
     (!p fid guard body env regions loop_start loop_end rest.
        cm_phase_parent_type_ready p fid
          (CAWhileBodyP (guard:cm_expr) (body:cm_stmt)
            (env:int->int->cm_value) (regions:(cm_region)list)
            (loop_start:int) (loop_end:int))
          (rest:(cm_acursor)list) = T) &&
     (!p fid rest. cm_phase_parent_type_ready p fid CAReturnP
        (rest:(cm_acursor)list) = T) &&
     (!p fid callee exprs values ret all_args base_slot current_slot
         scratch rest.
        cm_phase_parent_type_ready p fid
          (CAArgP (callee:int) (exprs:(cm_expr)list)
            (values:(cm_value)list) (ret:cm_type)
            (all_args:(cm_expr)list) (base_slot:int)
            (current_slot:int) (scratch:int))
          (rest:(cm_acursor)list) =
        cm_cursor_head_input_type_ready p fid ret rest) &&
     (!p fid caller env fp regions ret rest.
        cm_phase_parent_type_ready p fid
          (CACallP (caller:int) (env:int->int->cm_value) (fp:int)
            (regions:(cm_region)list) (ret:cm_type))
          (rest:(cm_acursor)list) =
        cm_cursor_head_input_type_ready p caller ret rest)`);
PROOF static int _e_cm_phase_parent_type_ready =
    cst_add_const_to_header(`cm_phase_parent_type_ready`);

PROOF thm cm_cursors_type_ready_def = new_rec_definition(
    get_theorem_by_name("list_RECURSION"),
    `(!p fid. cm_cursors_type_ready (p:cm_program) (fid:int)
        ([]:(cm_acursor)list) = T) &&
     (!p fid cursor rest.
        cm_cursors_type_ready p fid
          ((cursor:cm_acursor) :: (rest:(cm_acursor)list)) =
        (cm_phase_static_type_ready p fid (cm_cursor_phase cursor) &&
         cm_phase_parent_type_ready p fid (cm_cursor_phase cursor) rest &&
         cm_phase_result_type_ready p fid (cm_cursor_phase cursor) rest &&
         cm_cursors_type_ready p
           (cm_phase_next_fid fid (cm_cursor_phase cursor)) rest))`);
PROOF static int _e_cm_cursors_type_ready =
    cst_add_const_to_header(`cm_cursors_type_ready`);

PROOF thm cm_task_type_ready_def = new_rec_definition(
    get_cm_task_recursion(),
    `(!p q input ann.
        cm_task_type_ready (p:cm_program)
          (CMStartTask (q:cm_program) (input:(int)list))
          (ann:cm_annotation) = (q == p)) &&
     (!p q fid expr st ks ann.
        cm_task_type_ready (p:cm_program)
          (CMRTask (q:cm_program) (fid:int) (expr:cm_expr)
            (st:cm_src_state) (ks:(cm_frame)list))
          (ann:cm_annotation) =
        (q == p &&
         0i <= fid && fid < ilength (cm_program_functions p) &&
         cm_expr_wf p (inth fid (cm_program_functions p)) expr &&
         cm_scalar_expr_type (cm_expr_type expr) &&
         cm_cursors_type_ready p fid (cm_ann_cursors ann) &&
         cm_cursor_head_input_type_ready p fid (cm_expr_type expr)
           (cm_ann_cursors ann) &&
         cm_cursor_expr_values_type_ready p fid expr
           (cm_ann_cursors ann))) &&
     (!p q fid expr st ks ann.
        cm_task_type_ready (p:cm_program)
          (CMLTask (q:cm_program) (fid:int) (expr:cm_expr)
            (st:cm_src_state) (ks:(cm_frame)list))
          (ann:cm_annotation) =
        (q == p &&
         0i <= fid && fid < ilength (cm_program_functions p) &&
         cm_expr_wf p (inth fid (cm_program_functions p)) expr &&
         cm_lvalue expr &&
         cm_cursors_type_ready p fid (cm_ann_cursors ann) &&
         cm_cursor_head_input_type_ready p fid
           (cm_lvalue_output_type p
             (inth fid (cm_program_functions p)) expr)
           (cm_ann_cursors ann) &&
         cm_cursor_head_lvalue_type_ready p fid
           (cm_lvalue_output_type p
             (inth fid (cm_program_functions p)) expr)
           (cm_ann_cursors ann))) &&
     (!p q fid stmt st ks ann.
        cm_task_type_ready (p:cm_program)
          (CMSTask (q:cm_program) (fid:int) (stmt:cm_stmt)
            (st:cm_src_state) (ks:(cm_frame)list))
          (ann:cm_annotation) =
        (q == p &&
         0i <= fid && fid < ilength (cm_program_functions p) &&
         cm_stmt_wf p (inth fid (cm_program_functions p)) T stmt &&
         cm_cursors_type_ready p fid (cm_ann_cursors ann))) &&
     (!p q fid value st ks ann.
        cm_task_type_ready (p:cm_program)
          (CMVTask (q:cm_program) (fid:int) (value:cm_value)
            (st:cm_src_state) (ks:(cm_frame)list))
          (ann:cm_annotation) =
        (q == p &&
         cm_cursors_type_ready p fid (cm_ann_cursors ann) &&
         cm_cursor_head_value_type_ready p fid value
           (cm_ann_cursors ann))) &&
     (!p q fid control st ks ann.
        cm_task_type_ready (p:cm_program)
          (CMCTask (q:cm_program) (fid:int) (control:cm_control)
            (st:cm_src_state) (ks:(cm_frame)list))
          (ann:cm_annotation) =
        (q == p &&
         cm_control_type_ready p fid control &&
         cm_cursors_type_ready p fid (cm_ann_cursors ann))) &&
     (!p st control status ann.
        cm_task_type_ready (p:cm_program)
          (CMDoneTask (st:cm_src_state) (control:cm_control)
            (status:int)) (ann:cm_annotation) = T)`);
PROOF static int _e_cm_task_type_ready =
    cst_add_const_to_header(`cm_task_type_ready`);

PROOF thm get_cm_exprs_type_ready_def(void) {
  return cm_exprs_type_ready_def;
}
PROOF thm get_cm_phase_expr_type_ready_def(void) {
  return cm_phase_expr_type_ready_def;
}
PROOF thm get_cm_cursor_head_expr_type_ready_def(void) {
  return cm_cursor_head_expr_type_ready_def;
}
PROOF thm get_cm_cursor_expr_values_type_ready_def(void) {
  return cm_cursor_expr_values_type_ready_def;
}
PROOF thm get_cm_phase_lvalue_type_ready_def(void) {
  return cm_phase_lvalue_type_ready_def;
}
PROOF thm get_cm_cursor_head_lvalue_type_ready_def(void) {
  return cm_cursor_head_lvalue_type_ready_def;
}
PROOF thm get_cm_cursor_head_input_type_ready_def(void) {
  return cm_cursor_head_input_type_ready_def;
}
PROOF thm get_cm_lvalue_output_type_def(void) {
  return cm_lvalue_output_type_def;
}
PROOF thm get_cm_value_type_compatible_def(void) {
  return cm_value_type_compatible_def;
}
PROOF thm get_cm_member_lvalue_type_def(void) {
  return cm_member_lvalue_type_def;
}
PROOF thm get_cm_expr_value_type_ready_def(void) {
  return cm_expr_value_type_ready_def;
}
PROOF thm get_cm_value_convertible_to_def(void) {
  return cm_value_convertible_to_def;
}
PROOF thm get_cm_arg_next_type_def(void) {
  return cm_arg_next_type_def;
}
PROOF thm get_cm_arg_progress_type_ready_def(void) {
  return cm_arg_progress_type_ready_def;
}
PROOF thm get_cm_phase_value_type_ready_def(void) {
  return cm_phase_value_type_ready_def;
}
PROOF thm get_cm_control_type_ready_def(void) {
  return cm_control_type_ready_def;
}
PROOF thm get_cm_cursor_head_value_type_ready_def(void) {
  return cm_cursor_head_value_type_ready_def;
}
PROOF thm get_cm_phase_result_type_def(void) {
  return cm_phase_result_type_def;
}
PROOF thm get_cm_phase_result_type_ready_def(void) {
  return cm_phase_result_type_ready_def;
}
PROOF thm get_cm_phase_input_type_ready_def(void) {
  return cm_phase_input_type_ready_def;
}
PROOF thm get_cm_phase_static_type_ready_def(void) {
  return cm_phase_static_type_ready_def;
}
PROOF thm get_cm_phase_parent_type_ready_def(void) {
  return cm_phase_parent_type_ready_def;
}
PROOF thm get_cm_cursors_type_ready_def(void) {
  return cm_cursors_type_ready_def;
}
PROOF thm get_cm_task_type_ready_def(void) {
  return cm_task_type_ready_def;
}

PROOF static int cmc_preservation_type_ready_final_checks(void) {
  ENSURE_COND(vector_size(get_all_axioms()) ==
      _cmc_preservation_type_ready_axioms_before,
      "cmc_preservation_type_ready introduced an axiom");
  return 0;
err:
  return -1;
}
PROOF static int _cmc_preservation_type_ready_checks =
    cmc_preservation_type_ready_final_checks();
